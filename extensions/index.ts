/**
 * figma-labor extension for pi
 *
 * Registers write (and read) tools that talk to the figma-labor bridge server,
 * which relays commands to the Figma plugin via WebSocket → Plugin API.
 *
 * Requires:
 *   1. Bridge server running at http://127.0.0.1:3846  (start with /figma-labor-start)
 *   2. figma-labor plugin open inside Figma desktop app
 *
 * Tools registered:
 *   labor_get_selection       Get currently selected nodes
 *   labor_get_node            Get a node by ID
 *   labor_get_node_full       Get a node with all layout/constraint properties
 *   labor_get_children        List children of a node
 *   labor_get_component_props Get component property definitions
 *   labor_get_component_set_summary Get a component set summary
 *   labor_reorder_variant_options Reorder variant property options in a component set
 *   labor_create_component_set Combine components into a component set
 *   labor_update_properties   Update position, size, name, opacity, etc.
 *   labor_resize_node         Resize a node
 *   labor_scale_node          Scale a node proportionally like Figma Scale tool
 *   labor_clone_node          Clone a node
 *   labor_update_fills        Change fill colors
 *   labor_update_text         Change text content and font size
 *   labor_set_layout          Set auto-layout alignment, sizing, padding, spacing
 *   labor_create_node         Create a new primitive node
 *   labor_create_instance     Create an instance of a component
 *   labor_delete_node         Delete a node
 *   labor_move_node           Move a node to a different parent
 *   labor_select_node         Select a node and zoom to it
 *   labor_zoom_to_node        Zoom the viewport to a node without selecting it
 *   labor_detach_instance     Detach an instance, converting it to a plain frame
 *   labor_run_script          Run arbitrary JS in the Figma plugin context
 *   labor_get_annotations     List annotations on the page, selection, a node, or the document
 *   labor_update_annotations  Add, update, remove, or reply to one annotation
 *   labor_undo                Undo the last operation
 *   labor_list_files          List connected Figma files and this agent's target
 *   labor_use_file            Point this agent's tools at one connected file
 */

import { StringEnum } from "@mariozechner/pi-ai";
import type { ExtensionAPI } from "@mariozechner/pi-coding-agent";
import { Type, type TSchema } from "@sinclair/typebox";
import { spawn, type ChildProcess } from "node:child_process";
import { createWriteStream, readFileSync, realpathSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { setTimeout as delay } from "node:timers/promises";
import { fileURLToPath } from "node:url";

const __dirname = dirname(realpathSync(fileURLToPath(import.meta.url)));
const PROMPT_PATH = join(__dirname, "prompt.md");
const PROMPT_TEMPLATE = readFileSync(PROMPT_PATH, "utf8");
const DISCONNECTED_PROMPT = `## Figma labor

- figma-labor plugin: not connected. Labor tools fail until the user opens the plugin in Figma (Plugins → Development → figma-labor).
- If the task involves Figma, call \`labor_list_files\` to recheck the connection before asking the user for screenshots or exports.
- Once connected, read ${PROMPT_PATH} for Labor rules before the first canvas read or write. It is injected automatically from the next prompt on.`;

const BRIDGE_URL = "http://127.0.0.1:3846";
const BRIDGE_BIN = join(__dirname, "bridge.js");
const MCP_URL = `http://127.0.0.1:${process.env.FIGMA_MCP_PORT ?? "3845"}/mcp`;
const MAX_OUTPUT_BYTES = 50 * 1024;
/** The CLI running this extension; the annotation watch starts its agent with it. */
const HOST_CLI = process.argv[1]?.includes("@oh-my-pi/") ? "omp" : "pi";
/** Output of the annotation watch's background agent runs. */
const WATCH_LOG = join(tmpdir(), "figma-labor-watch.log");

// ## MCP STATE

let mcpSessionId: string | undefined;
let mcpRequestId = 1;
let mcpConnected = false;
let mcpAvailableTools: Array<{ name: string; description: string }> = [];

// ## STATES

type EditorType = "figma" | "figjam" | "slides" | "dev" | "buzz";

interface PluginContext {
  editorType: EditorType;
  page: { id: string; name: string };
  selectionCount: number;
  focusedSlide?: { id: string; name: string } | null;
  slidesMode?: "grid" | "single-slide";
}

/** One Figma file with the plugin open, as reported by the bridge. */
interface BridgeFile {
  id: string;
  file: string | null;
  editorType: EditorType | null;
  page: { id: string; name: string } | null;
  selectionCount: number | null;
}

interface BridgeStatus {
  bridge: string;
  plugin: string;
  /** Only set when exactly one file is connected. */
  context: PluginContext | null;
  /** Missing on bridges that predate multi-file support. */
  files?: BridgeFile[];
}

let bridgeProc: ChildProcess | null = null;
let bridgeStartedByUs = false;
let cachedStatus: BridgeStatus | null = null;

function footerSymbols(fileCount: number, mcpReady: boolean): string {
  const plugin =
    fileCount === 0 ? "◌" : fileCount === 1 ? "P" : `P${fileCount}`;
  const mcp = mcpReady ? "M" : "◌";
  return `${plugin} ${mcp}`;
}

function connectedFileCount(status: BridgeStatus): number {
  if (status.plugin !== "connected") return 0;
  return status.files?.length || 1;
}

function isStaleSessionContextError(error: unknown): boolean {
  return (
    error instanceof Error &&
    error.message.includes("stale after session replacement or reload")
  );
}

/** The part of a pi context that sets footer status entries. */
interface StatusContext {
  ui: {
    setStatus: (key: string, value: string | undefined) => void;
  };
}

function updateFooterStatus(ctx: StatusContext): boolean {
  try {
    if (cachedStatus?.bridge !== "running") {
      ctx.ui.setStatus("labor", undefined);
      return true;
    }
    ctx.ui.setStatus(
      "labor",
      `labor ${footerSymbols(connectedFileCount(cachedStatus), mcpConnected)}`,
    );
    return true;
  } catch (error) {
    if (isStaleSessionContextError(error)) return false;
    throw error;
  }
}

// ## BRIDGE HTTP

async function bridgeStatus(timeout = 2000): Promise<BridgeStatus | null> {
  try {
    const res = await fetch(`${BRIDGE_URL}/status`, {
      signal: AbortSignal.timeout(timeout),
    });
    return (await res.json()) as BridgeStatus;
  } catch {
    return null;
  }
}

function fileLabel(file: BridgeFile): string {
  const name = file.file === null ? "unidentified file" : `"${file.file}"`;
  return `${name} (${file.id})`;
}

function pluginStatusLabel(status: BridgeStatus | null): string {
  if (!status) return "disconnected";
  const files = status.files ?? [];
  if (files.length > 1) {
    return `${status.plugin} (${files.length} files: ${files.map(fileLabel).join(", ")})`;
  }
  const editor = status.context?.editorType;
  return editor ? `${status.plugin} (${editor})` : status.plugin;
}

// ## BRIDGE COMMAND HELPERS

interface BridgeCommandResult {
  result: unknown;
  /** The file that ran the command. */
  file: BridgeFile | null;
}

// Send a command to the bridge server. `target` is a file name or connection
// id; null lets the bridge use the only connected file.
async function bridgeCommand(
  command: string,
  params: Record<string, unknown>,
  opts?: { timeout?: number; signal?: AbortSignal; target?: string | null },
): Promise<BridgeCommandResult> {
  const timeoutMs = opts?.timeout ?? 35_000;
  const httpTimeoutSignal = AbortSignal.timeout(timeoutMs + 5_000); // HTTP timeout > bridge timeout
  const signal = opts?.signal
    ? AbortSignal.any([opts.signal, httpTimeoutSignal])
    : httpTimeoutSignal;
  const res = await fetch(`${BRIDGE_URL}/command`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({
      command,
      params,
      timeout: opts?.timeout,
      target: opts?.target ?? undefined,
    }),
    signal,
  });
  const json = (await res.json()) as {
    result?: unknown;
    error?: string;
    file?: BridgeFile;
  };
  if (json.error) throw new Error(json.error);
  return { result: json.result, file: json.file ?? null };
}

// Send an undo command to the bridge server
async function bridgeUndo(target: string | null): Promise<void> {
  const res = await fetch(`${BRIDGE_URL}/undo`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ target: target ?? undefined }),
    signal: AbortSignal.timeout(5000),
  });
  const json = (await res.json()) as { error?: string };
  if (json.error) throw new Error(json.error);
}

// Start the bridge server
async function startBridge(signal?: AbortSignal): Promise<boolean> {
  // Already running?
  const status = await bridgeStatus();
  if (status) return true;
  if (signal?.aborted) return false;

  bridgeProc = spawn("node", [BRIDGE_BIN], {
    detached: false,
    stdio: ["ignore", "pipe", "pipe"],
  });

  let spawnFailed = false;
  bridgeProc.on("error", (err) => {
    console.error("[figma-labor] Bridge process error:", err.message);
    spawnFailed = true;
  });

  // Wait up to 3s for it to start to avoid blocking the main thread
  for (let i = 0; i < 15; i++) {
    if (signal?.aborted) {
      stopBridge();
      return false;
    }
    if (spawnFailed) return false;
    await new Promise((r) => setTimeout(r, 200));
    const s = await bridgeStatus(300);
    if (s) {
      bridgeStartedByUs = true;
      return true;
    }
  }

  return false;
}

// Stop the bridge server
function stopBridge() {
  if (bridgeProc) {
    bridgeProc.kill("SIGTERM");
    bridgeProc = null;
  }
  bridgeStartedByUs = false;
}

// Plugins reconnect to a restarted bridge within a few seconds.
const PLUGIN_RECONNECT_WAIT_MS = 10_000;

function hasTargetFile(status: BridgeStatus, target: string | null): boolean {
  if (status.plugin !== "connected") return false;
  if (target === null) return true;
  return (status.files ?? []).some(
    (file) => file.file === target || file.id === target,
  );
}

// After restarting the bridge, wait for the target file's plugin to reconnect.
async function waitForPlugin(
  target: string | null,
  signal?: AbortSignal,
): Promise<BridgeStatus | null> {
  const deadline = Date.now() + PLUGIN_RECONNECT_WAIT_MS;
  let status = await bridgeStatus();
  while (
    status &&
    !hasTargetFile(status, target) &&
    Date.now() < deadline &&
    !signal?.aborted
  ) {
    await delay(500);
    status = await bridgeStatus();
  }
  return status;
}

// ## TOOL HELPERS

function formatToolOutput(output: unknown): string {
  return JSON.stringify(output, null, 2) ?? "No result returned by Figma.";
}

interface BridgeToolOptions {
  timeout?: number;
  signal?: AbortSignal;
  includeContext?: boolean;
  /** File name or connection id; null lets the bridge use the only connected file. */
  target?: string | null;
  /** Called with the file that ran the command. */
  onFile?: (file: BridgeFile) => void;
  /** Amends a successful result before it's shown. Must not throw. */
  after?: (result: unknown, file: BridgeFile | null) => Promise<unknown>;
}

async function runBridgeTool(
  command: string,
  params: Record<string, unknown>,
  opts?: BridgeToolOptions,
) {
  let status = await bridgeStatus();

  // The bridge exits with the session that started it. Restart it so other
  // sessions keep working, and give the plugins time to reconnect to it.
  if (!status && (await startBridge(opts?.signal))) {
    status = await waitForPlugin(opts?.target ?? null, opts?.signal);
  }

  // Handle connection errors
  if (!status) {
    return {
      content: [
        {
          type: "text" as const,
          text: "figma-labor bridge is not running and could not be started. Run /figma-labor-start.",
        },
      ],
      isError: true,
    };
  }

  if (status.plugin !== "connected") {
    return {
      content: [
        {
          type: "text" as const,
          text: "Figma plugin is not connected. Open the figma-labor plugin in Figma (Menu → Plugins → Development → figma-labor).",
        },
      ],
      isError: true,
    };
  }

  cachedStatus = status;

  // Execute command
  try {
    const { result, file } = await bridgeCommand(command, params, opts);
    if (file) opts?.onFile?.(file);
    const errorMessage =
      typeof result === "string" && result.startsWith("figma-labor error:")
        ? result
        : result &&
            typeof result === "object" &&
            "error" in result &&
            typeof result.error === "string"
          ? `figma-labor error: ${result.error}`
          : null;
    if (errorMessage) {
      return {
        content: [{ type: "text" as const, text: errorMessage }],
        isError: true,
      };
    }
    const amended = opts?.after ? await opts.after(result, file) : result;
    const output = opts?.includeContext
      ? {
          file: file?.file ?? null,
          editorType: file?.editorType ?? status.context?.editorType ?? null,
          page: file?.page ?? status.context?.page ?? null,
          selection: amended,
        }
      : amended;
    return {
      content: [{ type: "text" as const, text: formatToolOutput(output) }],
    };
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    return {
      content: [{ type: "text" as const, text: `figma-labor error: ${msg}` }],
      isError: true,
    };
  }
}

// ## ANNOTATIONS

// The plugin has no annotation commands, so the annotation tools and the
// watch send fixed scripts through run_script. Arguments travel as JSON.

/** Annotations in this category are requests for the agent. */
const AGENT_CATEGORY = "Agent";
/** Starts the agent's reply paragraph inside an annotation. */
const AGENT_REPLY_MARK = "■";

const ANNOTATION_PROPERTY_TYPES = [
  "width",
  "height",
  "maxWidth",
  "minWidth",
  "maxHeight",
  "minHeight",
  "fills",
  "strokes",
  "effects",
  "strokeWeight",
  "cornerRadius",
  "textStyleId",
  "textAlignHorizontal",
  "fontFamily",
  "fontStyle",
  "fontSize",
  "fontWeight",
  "lineHeight",
  "letterSpacing",
  "itemSpacing",
  "padding",
  "layoutMode",
  "alignItems",
  "opacity",
  "mainComponent",
  "gridRowGap",
  "gridColumnGap",
  "gridRowCount",
  "gridColumnCount",
  "gridRowAnchorIndex",
  "gridColumnAnchorIndex",
  "gridRowSpan",
  "gridColumnSpan",
] as const;

// Shared by every annotation script; `args` is defined by annotationScript.
// Node lookups catch: getNodeByIdAsync throws after ~10 s for unknown ids.
const ANNOTATION_SCRIPT_HELPERS = `
if (!figma.annotations) return { error: "Annotations are only available in Figma Design and Dev Mode." };
const AGENT = ${JSON.stringify(AGENT_CATEGORY)};
const REPLY_MARK = ${JSON.stringify(AGENT_REPLY_MARK)};
const categories = (await figma.annotations.getAnnotationCategoriesAsync()).map((c) => ({ id: c.id, label: c.label }));
const categoryLabel = (id) => categories.find((c) => c.id === id)?.label;
const isAgentCategory = (id) => categoryLabel(id)?.trim().toLowerCase() === AGENT.toLowerCase();
const findCategory = (key) => categories.find((c) => c.id === key || c.label.trim().toLowerCase() === key.trim().toLowerCase());
async function ensureAgentCategory() {
  const found = findCategory(AGENT);
  if (found) return { category: found, created: false };
  const added = await figma.annotations.addAnnotationCategoryAsync({ label: AGENT, color: "violet" });
  const category = { id: added.id, label: added.label };
  categories.push(category);
  return { category, created: true };
}
const labelOf = (a) => a.labelMarkdown || a.label || "";
// A request is pending until its last paragraph is the agent's reply.
function isPending(a) {
  const paragraphs = labelOf(a).split(/\\n+/).map((p) => p.trim()).filter(Boolean);
  return paragraphs.length > 0 && !paragraphs[paragraphs.length - 1].startsWith(REPLY_MARK);
}
// "agent: …" opening an annotation in any category, or none, is a request
// too. The watch, or the agent's reply, files it under Agent without the prefix.
const AGENT_PREFIX = /^\\s*agent\\s*:\\s*(?=\\S)/i;
const hasAgentPrefix = (a) => AGENT_PREFIX.test(labelOf(a));
const isRequest = (a) => isAgentCategory(a.categoryId) || hasAgentPrefix(a);
// A plain copy to write back. Figma rejects annotations that set both label
// and labelMarkdown, which is how it reports them, so copy one of the two.
function copyAnnotation(a) {
  const copy = {};
  if (a.labelMarkdown) copy.labelMarkdown = a.labelMarkdown;
  else if (a.label) copy.label = a.label;
  if (a.properties?.length) copy.properties = a.properties.map((p) => ({ type: p.type }));
  if (a.categoryId) copy.categoryId = a.categoryId;
  return copy;
}
// File an "agent:" request, given as a copy, under Agent without the prefix.
function categorize(copy, agentId) {
  copy.labelMarkdown = labelOf(copy).replace(AGENT_PREFIX, "");
  delete copy.label;
  copy.categoryId = agentId;
  return copy;
}
function describeAnnotation(a, index) {
  const out = { index };
  const label = labelOf(a);
  if (label) out.label = label;
  if (a.categoryId) {
    const name = categoryLabel(a.categoryId);
    if (name) out.category = name;
    else out.categoryId = a.categoryId;
  }
  if (isRequest(a)) out.status = isPending(a) ? "pending" : "replied";
  if (a.properties?.length) out.properties = a.properties.map((p) => p.type);
  return out;
}
function pageOf(node) {
  let p = node;
  while (p && p.type !== "PAGE") p = p.parent;
  return p;
}
function pathOf(node) {
  const names = [];
  for (let p = node.parent; p && p.type !== "PAGE"; p = p.parent) names.push(p.name);
  if (names.length <= 2) return names.reverse().join(" › ");
  return names[names.length - 1] + " › … › " + names[0];
}
async function nodeById(id) {
  try {
    return await figma.getNodeByIdAsync(id);
  } catch {
    return null;
  }
}
const hasAnnotations = (n) => "annotations" in n && n.annotations.length > 0;
// The node and its descendants that have annotations.
const annotatedIn = (node) => [
  ...(hasAnnotations(node) ? [node] : []),
  ...("findAll" in node ? node.findAll(hasAnnotations) : []),
];
// Rewrite node.annotations without the ones drop picks; returns how many went.
function dropAnnotations(node, drop) {
  const kept = node.annotations.filter((a) => !drop(a));
  const dropped = node.annotations.length - kept.length;
  if (dropped) node.annotations = kept.map(copyAnnotation);
  return dropped;
}
`;

function annotationScript(body: string, args: Record<string, unknown>): string {
  return `const args = ${JSON.stringify(args)};\n${ANNOTATION_SCRIPT_HELPERS}\n${body}`;
}

const GET_ANNOTATIONS_SCRIPT = `
const wanted = args.category?.trim().toLowerCase();
// "agent:" requests count as Agent whatever their category.
const wantsAgent = wanted === AGENT.toLowerCase() || isAgentCategory(args.category);
const matches = (a) =>
  !wanted ||
  a.categoryId === args.category ||
  categoryLabel(a.categoryId)?.trim().toLowerCase() === wanted ||
  (wantsAgent && hasAgentPrefix(a));
let scope;
let nodes = [];
const collect = (root) => nodes.push(...annotatedIn(root));
if (args.nodeId) {
  const root = await nodeById(args.nodeId);
  if (!root) return { error: "Node " + args.nodeId + " not found." };
  scope = "node " + root.id;
  collect(root);
} else if (args.scope === "selection") {
  const selection = figma.currentPage.selection;
  if (!selection.length) return { error: "Nothing is selected." };
  scope = "selection";
  selection.forEach(collect);
} else if (args.scope === "document") {
  await figma.loadAllPagesAsync();
  scope = "document";
  nodes = figma.root.findAll(hasAnnotations);
} else {
  scope = 'page "' + figma.currentPage.name + '"';
  nodes = figma.currentPage.findAll(hasAnnotations);
}
const seen = new Set();
const shown = [];
let nodeCount = 0;
let annotationCount = 0;
for (const node of nodes) {
  if (seen.has(node.id)) continue;
  seen.add(node.id);
  const annotations = node.annotations.flatMap((a, i) => (matches(a) ? [describeAnnotation(a, i)] : []));
  if (!annotations.length) continue;
  nodeCount++;
  annotationCount += annotations.length;
  if (shown.length >= args.limit) continue;
  const entry = { nodeId: node.id, name: node.name, type: node.type };
  const path = pathOf(node);
  if (path) entry.path = path;
  if (scope === "document") entry.page = pageOf(node)?.name;
  entry.annotations = annotations;
  shown.push(entry);
}
const result = { scope, categories, nodeCount, annotationCount, nodes: shown };
if (nodeCount > shown.length) result.truncated = "Showing " + shown.length + " of " + nodeCount + " nodes; narrow with nodeId or category, or raise limit.";
return result;
`;

const UPDATE_ANNOTATIONS_SCRIPT = `
const node = await nodeById(args.nodeId);
if (!node) return { error: "Node " + args.nodeId + " not found." };
if (!("annotations" in node)) return { error: node.type + " nodes can't have annotations." };
const list = node.annotations.map(copyAnnotation);
const index = args.index;
if (args.action !== "add" && (index === undefined || !list[index])) {
  return { error: "Annotation index " + index + " is out of range; the node has " + list.length + " annotation(s)." };
}
let categoryId;
let createdCategory = false;
if (args.category) {
  let category = findCategory(args.category);
  if (!category && args.category.trim().toLowerCase() === AGENT.toLowerCase()) {
    const ensured = await ensureAgentCategory();
    category = ensured.category;
    createdCategory = ensured.created;
  }
  if (!category) return { error: 'No annotation category "' + args.category + '". Categories: ' + categories.map((c) => c.label).join(", ") + "." };
  categoryId = category.id;
}
const properties = args.properties?.map((type) => ({ type }));
if (args.action === "add") {
  const added = {};
  if (args.label) added.labelMarkdown = args.label;
  if (properties?.length) added.properties = properties;
  if (categoryId) added.categoryId = categoryId;
  if (!added.labelMarkdown && !added.properties) return { error: "add needs a label or properties." };
  list.push(added);
} else if (args.action === "update") {
  const a = list[index];
  if (args.label !== undefined) {
    delete a.label;
    delete a.labelMarkdown;
    if (args.label) a.labelMarkdown = args.label;
  }
  if (args.category !== undefined) {
    delete a.categoryId;
    if (categoryId) a.categoryId = categoryId;
  }
  if (properties !== undefined) {
    delete a.properties;
    if (properties.length) a.properties = properties;
  }
  if (!a.labelMarkdown && !a.label && !a.properties) return { error: "That would leave the annotation empty; use remove." };
} else if (args.action === "reply") {
  const text = args.label?.trim().replace(/\\s*\\n+\\s*/g, " ");
  if (!text) return { error: "reply needs a label: the reply text." };
  const a = list[index];
  if (hasAgentPrefix(a)) {
    const ensured = await ensureAgentCategory();
    if (ensured.created) createdCategory = true;
    categorize(a, ensured.category.id);
  }
  const previous = a.labelMarkdown ?? a.label ?? "";
  delete a.label;
  a.labelMarkdown = (previous ? previous + "\\n\\n" : "") + REPLY_MARK + " " + text;
} else {
  list.splice(index, 1);
}
node.annotations = list;
const result = { nodeId: node.id, name: node.name, annotations: node.annotations.map(describeAnnotation) };
if (createdCategory) result.createdCategory = AGENT;
return result;
`;

// One listener per plugin instance records nodes whose annotations change,
// keeping at most 1000; each poll reads the ones changed since its last poll.
// A watcher's first poll, and any poll after the plugin restarted, scans the
// whole document instead. The listener carries a version so a newer extension
// replaces the one an older one installed.
// Figma reports annotation changes on groups but gives plugins no annotations
// property on them, so a poll can't read those. It names each such group once
// per watch (args.warned holds the ones named) in a Figma toast and returns it.
const WATCH_ANNOTATIONS_SCRIPT = `
let createdCategory = args.ensureCategory ? (await ensureAgentCategory()).created : false;
let state = globalThis.__laborAnnotationWatch;
let full = args.since === null;
if (state?.version !== 2) {
  if (state?.listener) figma.off("documentchange", state.listener);
  await figma.loadAllPagesAsync();
  const changed = new Map();
  const listener = (event) => {
    const at = Date.now();
    for (const change of event.documentChanges) {
      if (change.type === "DELETE") {
        changed.delete(change.id);
        continue;
      }
      // A copy (duplicate, paste, clone) is one CREATE for its root, with
      // annotations anywhere in its subtree.
      const created = change.type === "CREATE";
      const annotated = created
        ? annotatedIn(change.node).length > 0
        : change.type === "PROPERTY_CHANGE" && change.properties.includes("annotations");
      if (!annotated) continue;
      const prior = changed.get(change.id);
      changed.delete(change.id);
      changed.set(change.id, { node: change.node, at, created: created || Boolean(prior?.created) });
      if (changed.size > 1000) changed.delete(changed.keys().next().value);
    }
  };
  figma.on("documentchange", listener);
  state = globalThis.__laborAnnotationWatch = { version: 2, listener, changed };
  full = true;
}
const now = Date.now();
for (const [id, entry] of state.changed) if (now - entry.at > 600000) state.changed.delete(id);
let nodes = [];
const unreadable = [];
const copies = [];
if (full) {
  nodes = figma.root.findAll(hasAnnotations);
} else {
  for (const entry of state.changed.values()) {
    if (entry.at < args.since || entry.node.removed) continue;
    if (!("annotations" in entry.node)) {
      if (!args.warned.includes(entry.node.id)) unreadable.push({ nodeId: entry.node.id, name: entry.node.name });
      continue;
    }
    if (!entry.created) {
      nodes.push(entry.node);
      continue;
    }
    entry.created = false;
    const annotated = annotatedIn(entry.node);
    nodes.push(...annotated);
    copies.push(...annotated);
  }
}
// A copy keeps its source's annotations. Drop the Agent requests whose source
// is still in the file: the copy shouldn't repeat them, but a cut-and-paste
// or an undone delete keeps its request. Other annotations stay.
const copiedRequests = copies.filter((node) => node.annotations.some(isRequest));
if (copiedRequests.length) {
  const copyIds = new Set(copies.map((node) => node.id));
  const sources = new Set();
  for (const node of figma.root.findAll(hasAnnotations)) {
    if (copyIds.has(node.id)) continue;
    for (const a of node.annotations) if (isRequest(a)) sources.add(labelOf(a));
  }
  for (const node of copiedRequests) dropAnnotations(node, (a) => isRequest(a) && sources.has(labelOf(a)));
}
let agentId = null;
const seen = new Set();
const requests = [];
for (const node of nodes) {
  if (seen.has(node.id) || node.removed || !("annotations" in node)) continue;
  seen.add(node.id);
  if (node.annotations.some(hasAgentPrefix)) {
    if (!agentId) {
      const ensured = await ensureAgentCategory();
      agentId = ensured.category.id;
      if (ensured.created) createdCategory = true;
    }
    node.annotations = node.annotations.map((a) => (hasAgentPrefix(a) ? categorize(copyAnnotation(a), agentId) : copyAnnotation(a)));
  }
  node.annotations.forEach((a, index) => {
    if (isAgentCategory(a.categoryId) && isPending(a)) {
      requests.push({ nodeId: node.id, name: node.name, index, label: labelOf(a), page: pageOf(node)?.name });
    }
  });
}
if (unreadable.length) {
  const names = unreadable.map((n) => '"' + n.name + '"').join(", ");
  figma.notify("Labor can't read annotations on groups (" + names + "). Annotate a frame or layer instead.", { timeout: 10000 });
}
return { since: now, requests, unreadable, createdCategory };
`;

// labor_clone_node: a clone keeps its source's annotations. Drop the Agent
// requests among them; other annotations stay.
const DROP_COPIED_REQUESTS_SCRIPT = `
const node = await nodeById(args.nodeId);
if (!node) return { error: "Node " + args.nodeId + " not found." };
let dropped = 0;
for (const n of annotatedIn(node)) dropped += dropAnnotations(n, isRequest);
return { dropped };
`;

/** Drop the Agent requests a clone copied so they don't reach the agent again. */
async function dropCopiedRequests(
  clone: unknown,
  file: BridgeFile | null,
  signal?: AbortSignal,
): Promise<unknown> {
  const id = (clone as { id?: unknown } | null)?.id;
  // Only Figma Design and Dev Mode have annotations.
  const editor = file?.editorType;
  if (
    typeof id !== "string" ||
    (file && editor !== "figma" && editor !== "dev")
  )
    return clone;
  try {
    const { result } = await bridgeCommand(
      "run_script",
      { code: annotationScript(DROP_COPIED_REQUESTS_SCRIPT, { nodeId: id }) },
      { target: file?.id ?? null, signal },
    );
    const { dropped, error } = (result ?? {}) as {
      dropped?: number;
      error?: string;
    };
    if (error) throw new Error(error);
    return dropped
      ? { ...(clone as object), droppedAgentRequests: dropped }
      : clone;
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    return {
      ...(clone as object),
      warning: `Couldn't drop the Agent requests copied onto the clone: ${msg}`,
    };
  }
}

interface AnnotationRequest {
  nodeId: string;
  name: string;
  index: number;
  label: string;
  page?: string;
}

function watchMessage(file: string, requests: AnnotationRequest[]): string {
  const lines = requests.map(
    (r) =>
      `- node ${r.nodeId} "${r.name}"${r.page ? ` on page "${r.page}"` : ""}, annotation ${r.index}:\n  ${r.label.replace(/\n+/g, "\n  ")}`,
  );
  const count =
    requests.length === 1 ? "1 new request" : `${requests.length} new requests`;
  return [
    `Figma annotation watch: ${count} in the "${AGENT_CATEGORY}" category of "${file}". Labor tools already target that file. You run in the background, so your replies on the annotations are the only report the designer sees.`,
    ...lines,
    `Handle each on its node and verify, then reply on that annotation with labor_update_annotations (action "reply"): one line starting "Done:" with what changed, or "Question:" with what you need. Skip any whose last paragraph is already a ${AGENT_REPLY_MARK} reply.`,
  ].join("\n");
}

/** Match a connected file by connection id or unique file name. */
function resolveFile(
  files: BridgeFile[],
  query: string,
): { file: BridgeFile; target: string } | { error: string } {
  const sameName = files.filter((file) => file.file === query);
  const match =
    files.find((file) => file.id === query) ??
    (sameName.length === 1 ? sameName[0] : undefined);
  if (!match) {
    const reason =
      sameName.length > 1
        ? `Several connected files are named "${query}"; use a connection id.`
        : `No connected Figma file matches "${query}".`;
    const connected = files.length ? files.map(fileLabel).join(", ") : "none";
    return { error: `${reason} Connected: ${connected}.` };
  }
  // Prefer the name: it survives plugin reconnects, which change the id.
  const nameIsUnique =
    match.file !== null &&
    files.filter((file) => file.file === match.file).length === 1;
  return { file: match, target: nameIsUnique ? match.file! : match.id };
}

// ## MCP HELPERS

async function mcpPost(
  method: string,
  params?: Record<string, unknown>,
  signal?: AbortSignal,
): Promise<unknown> {
  const id = mcpRequestId++;
  const headers: Record<string, string> = {
    "Content-Type": "application/json",
    Accept: "application/json, text/event-stream",
  };
  if (mcpSessionId) headers["mcp-session-id"] = mcpSessionId;

  const response = await fetch(MCP_URL, {
    method: "POST",
    headers,
    body: JSON.stringify({ jsonrpc: "2.0", id, method, params }),
    signal,
  });

  const newSessionId = response.headers.get("mcp-session-id");
  if (newSessionId) mcpSessionId = newSessionId;

  if (!response.ok) {
    throw new Error(`MCP HTTP ${response.status}: ${response.statusText}`);
  }

  const contentType = response.headers.get("content-type") ?? "";
  const text = await response.text();
  let json: { result?: unknown; error?: { message: string } };

  if (contentType.includes("text/event-stream")) {
    const dataLine = text.split("\n").find((line) => line.startsWith("data: "));
    if (!dataLine) throw new Error("No data in SSE response");
    json = JSON.parse(dataLine.slice(6));
  } else {
    json = JSON.parse(text);
  }

  if (json.error) throw new Error(json.error.message);
  return json.result;
}

async function initializeMcpSession(signal?: AbortSignal): Promise<boolean> {
  try {
    mcpSessionId = undefined;
    await mcpPost(
      "initialize",
      {
        protocolVersion: "2024-11-05",
        capabilities: {},
        clientInfo: { name: "pi-figma-labor", version: "2.0" },
      },
      signal,
    );
    return true;
  } catch {
    return false;
  }
}

interface McpTool {
  name: string;
  description: string;
  inputSchema: {
    type: string;
    properties?: Record<
      string,
      {
        type: string;
        description?: string;
        enum?: string[];
        items?: unknown;
        default?: unknown;
      }
    >;
    required?: string[];
  };
}

interface McpContent {
  type: "text" | "image" | "resource";
  text?: string;
  data?: string;
  mimeType?: string;
  uri?: string;
}

interface McpToolResult {
  content: McpContent[];
  isError?: boolean;
}

async function listMcpTools(signal?: AbortSignal): Promise<McpTool[]> {
  const result = (await mcpPost("tools/list", undefined, signal)) as {
    tools: McpTool[];
  };
  return result.tools ?? [];
}

async function callMcpTool(
  name: string,
  args: Record<string, unknown>,
  signal?: AbortSignal,
): Promise<McpToolResult> {
  return (await mcpPost(
    "tools/call",
    { name, arguments: args },
    signal,
  )) as McpToolResult;
}

function truncateMcpText(text: string): string {
  if (Buffer.byteLength(text, "utf8") <= MAX_OUTPUT_BYTES) return text;
  return (
    Buffer.from(text, "utf8").slice(0, MAX_OUTPUT_BYTES).toString("utf8") +
    "\n\n[Output truncated — use a more specific nodeId or break the design into smaller sections.]"
  );
}

function convertMcpContent(
  mcpContent: McpContent[],
): Array<
  | { type: "text"; text: string }
  | { type: "image"; mimeType: string; data: string }
> {
  const out: ReturnType<typeof convertMcpContent> = [];
  for (const content of mcpContent) {
    if (content.type === "text" && content.text) {
      out.push({ type: "text", text: truncateMcpText(content.text) });
    } else if (content.type === "image" && content.data && content.mimeType) {
      out.push({
        type: "image",
        mimeType: content.mimeType,
        data: content.data,
      });
    } else if (content.type === "resource" && content.uri) {
      out.push({ type: "text", text: `[Resource: ${content.uri}]` });
    }
  }
  return out;
}

function buildMcpSchema(inputSchema: McpTool["inputSchema"]): TSchema {
  const props = inputSchema.properties ?? {};
  const required = new Set(inputSchema.required ?? []);
  const fields: Record<string, TSchema> = {};

  for (const [key, prop] of Object.entries(props)) {
    let schema: TSchema;

    if (prop.enum) {
      schema = Type.Union(prop.enum.map((value) => Type.Literal(value)));
    } else if (prop.type === "boolean") {
      schema = Type.Boolean();
    } else if (prop.type === "number" || prop.type === "integer") {
      schema = Type.Number();
    } else if (prop.type === "array") {
      schema = Type.Array(Type.Any());
    } else {
      schema = Type.String();
    }

    const description = prop.description ?? "";
    const withDescription = description ? { ...schema, description } : schema;
    fields[key] = required.has(key)
      ? withDescription
      : Type.Optional(withDescription);
  }

  return Type.Object(fields);
}

function formatMcpLabel(name: string): string {
  return name
    .split("_")
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
}

function normalizeMcpNodeId(value: string): string {
  const squashed = value.replace(/\s+/g, "").trim();
  if (!squashed) return squashed;

  try {
    const url = new URL(squashed);
    const fromQuery =
      url.searchParams.get("node-id") ?? url.searchParams.get("nodeId");
    if (fromQuery) return normalizeMcpNodeId(fromQuery);
  } catch {}

  const queryMatch = squashed.match(/[?&]node-id=([0-9]+(?:[:-][0-9]+)?)/i);
  if (queryMatch?.[1]) return normalizeMcpNodeId(queryMatch[1]);

  const plainMatch = squashed.match(/\b([0-9]+[:-][0-9]+)\b/);
  if (!plainMatch) return squashed;

  return plainMatch[1].replace(/-/g, ":");
}

const MCP_EDITOR_ROUTES: Partial<
  Record<
    string,
    {
      editors: readonly EditorType[];
      fallback: string;
    }
  >
> = {
  get_design_context: {
    editors: ["figma", "dev"],
    fallback: "Use get_figjam in FigJam or Labor reads in Slides.",
  },
  get_metadata: {
    editors: ["figma", "dev"],
    fallback: "Use Labor reads outside Figma Design.",
  },
  get_variable_defs: {
    editors: ["figma", "dev"],
    fallback: "Variables are only supported in Figma Design.",
  },
  get_figjam: {
    editors: ["figjam"],
    fallback: "Use get_design_context in Design or Labor reads in Slides.",
  },
};

function mcpEditorRoutingError(name: string): string | null {
  const route = MCP_EDITOR_ROUTES[name];
  const editor = cachedStatus?.context?.editorType;
  if (!route || !editor || route.editors.includes(editor)) return null;
  return `${name} does not support the current ${editor} editor. ${route.fallback}`;
}

function normalizeMcpArgs(
  name: string,
  args: Record<string, unknown>,
): Record<string, unknown> {
  const next = { ...args };
  if (
    typeof next.nodeId === "string" &&
    [
      "get_design_context",
      "get_screenshot",
      "get_metadata",
      "get_variable_defs",
      "get_code_connect_map",
      "add_code_connect_map",
      "get_code_connect_suggestions",
      "send_code_connect_mappings",
      "get_figjam",
    ].includes(name)
  ) {
    next.nodeId = normalizeMcpNodeId(next.nodeId);
  }
  return next;
}

async function callMcpToolWithRetry(
  name: string,
  args: Record<string, unknown>,
  signal?: AbortSignal,
): Promise<McpToolResult> {
  try {
    return await callMcpTool(name, args, signal);
  } catch (error: unknown) {
    const message = error instanceof Error ? error.message : String(error);
    const lower = message.toLowerCase();
    const shouldRetry =
      lower.includes("aborted") ||
      message.includes("404") ||
      lower.includes("session");
    if (!shouldRetry) throw error;

    mcpSessionId = undefined;
    const ok = await initializeMcpSession(signal);
    if (!ok) throw error;
    return await callMcpTool(name, args, signal);
  }
}

function registerFigmaMcp(pi: ExtensionAPI) {
  const registeredToolNames = new Set<string>();
  let pollTimer: ReturnType<typeof setTimeout> | null = null;
  let pollingActive = false;
  let refreshInFlight = false;

  function registerMcpTools(tools: McpTool[]) {
    mcpAvailableTools = tools.map((tool) => ({
      name: tool.name,
      description: tool.description,
    }));

    for (const tool of tools) {
      if (registeredToolNames.has(tool.name)) continue;
      registeredToolNames.add(tool.name);
      pi.registerTool({
        name: tool.name,
        label: formatMcpLabel(tool.name),
        description: tool.description,
        parameters: buildMcpSchema(tool.inputSchema),
        async execute(_id, params, signal, _onUpdate, ctx) {
          const routingError = mcpEditorRoutingError(tool.name);
          if (routingError) {
            return {
              content: [{ type: "text", text: routingError }],
              isError: true,
            };
          }

          if (!mcpSessionId) {
            const ok = await initializeMcpSession(signal);
            if (!ok) {
              markMcpDisconnected(ctx);
              return {
                content: [
                  {
                    type: "text",
                    text: "Figma MCP server is not reachable. Make sure the Figma desktop app is open and the MCP server is enabled.",
                  },
                ],
                isError: true,
              };
            }
          }

          try {
            const normalizedParams = normalizeMcpArgs(
              tool.name,
              params as Record<string, unknown>,
            );
            const result = await callMcpToolWithRetry(
              tool.name,
              normalizedParams,
              signal,
            );
            return {
              content: convertMcpContent(result.content),
              isError: result.isError ?? false,
            };
          } catch (error: unknown) {
            const message =
              error instanceof Error ? error.message : String(error);
            if (isMcpConnectionError(message)) markMcpDisconnected(ctx);
            return {
              content: [{ type: "text", text: `Figma MCP error: ${message}` }],
              isError: true,
            };
          }
        },
      });
    }
  }

  function scheduleMcpPoll(ctx: Parameters<Parameters<typeof pi.on>[1]>[1]) {
    if (!pollingActive) return;
    if (pollTimer) clearTimeout(pollTimer);
    const delay = mcpConnected ? 30_000 : 5_000;
    pollTimer = setTimeout(async () => {
      pollTimer = null;
      await refreshMcpStatus(ctx);
      scheduleMcpPoll(ctx);
    }, delay);
  }

  function markMcpDisconnected(
    ctx: Parameters<Parameters<typeof pi.on>[1]>[1],
  ) {
    mcpConnected = false;
    mcpSessionId = undefined;
    updateFooterStatus(ctx);
    scheduleMcpPoll(ctx);
  }

  function isMcpConnectionError(message: string): boolean {
    const lower = message.toLowerCase();
    return (
      lower.includes("fetch failed") ||
      lower.includes("econnrefused") ||
      lower.includes("aborted") ||
      lower.includes("404") ||
      lower.includes("session")
    );
  }

  async function refreshMcpStatus(
    ctx: Parameters<Parameters<typeof pi.on>[1]>[1],
  ) {
    if (refreshInFlight) return;
    refreshInFlight = true;
    const signal = AbortSignal.timeout(3000);
    try {
      if (!mcpSessionId) {
        const ok = await initializeMcpSession(signal);
        if (!ok) throw new Error("MCP initialization failed");
      }

      let tools: McpTool[];
      try {
        tools = await listMcpTools(signal);
      } catch {
        mcpSessionId = undefined;
        const ok = await initializeMcpSession(signal);
        if (!ok) throw new Error("MCP reconnection failed");
        tools = await listMcpTools(signal);
      }

      mcpConnected = true;
      registerMcpTools(tools);
    } catch {
      mcpConnected = false;
      mcpSessionId = undefined;
    } finally {
      refreshInFlight = false;
      updateFooterStatus(ctx);
    }
  }

  pi.on("session_start", async (_event, ctx) => {
    pollingActive = true;
    void (async () => {
      await refreshMcpStatus(ctx);
      scheduleMcpPoll(ctx);
    })();
  });

  pi.on("session_shutdown", async (_event, ctx) => {
    pollingActive = false;
    if (pollTimer) {
      clearTimeout(pollTimer);
      pollTimer = null;
    }
    mcpConnected = false;
    mcpSessionId = undefined;
    updateFooterStatus(ctx);
  });

  pi.registerCommand("figma-mcp", {
    description: "Show Figma MCP server connection status and available tools",
    handler: async (_args, ctx) => {
      if (!mcpConnected) {
        ctx.ui.notify(
          "Figma MCP server is not connected.\n\nTo enable:\n1. Open Figma desktop app\n2. Open a Design file\n3. Switch to Dev Mode (Shift+D)\n4. In the Inspect panel → MCP server → Enable desktop MCP server",
          "error",
        );
        return;
      }
      ctx.ui.notify(
        `Figma MCP server connected ✓\nURL: ${MCP_URL}\n\nAvailable tools (${mcpAvailableTools.length}):\n${mcpAvailableTools.map((tool) => `  • ${tool.name}`).join("\n")}`,
        "success",
      );
    },
  });
}

// ## EXTENSION

export default function (pi: ExtensionAPI) {
  registerFigmaMcp(pi);

  // Lifecycle
  let pollTimer: ReturnType<typeof setInterval> | null = null;
  let bridgeSessionRun = 0;
  let bridgeStartupAbort: AbortController | null = null;

  // File this agent's Labor tools target: a file name, or a connection id when
  // the name is ambiguous. Each agent (subagents included) gets its own. The
  // first command that runs with a single connected file pins it, so a file
  // connecting later can't redirect this agent's writes. FIGMA_LABOR_FILE
  // presets it, which is how the annotation watch's agent gets its file.
  let targetFile: string | null = null;

  function runTool(
    command: string,
    params: Record<string, unknown>,
    opts?: Omit<BridgeToolOptions, "target" | "onFile">,
  ) {
    return runBridgeTool(command, params, {
      ...opts,
      target: targetFile,
      onFile: (file) => {
        targetFile ??= file.file ?? file.id;
      },
    });
  }

  // Annotation watch: off until /figma-labor-watch turns it on for one file,
  // this session's target. Polls that file and hands new Agent requests to a
  // background agent: a headless run of this CLI, which loads this extension
  // too, with FIGMA_LABOR_FILE set to the watched file. One run at a time;
  // requests that arrive meanwhile wait for the next. The session only shows
  // a footer status, a notification when a run ends, and a warning when an
  // annotation changes on a group, which plugins can't read.
  interface AnnotationWatch {
    file: string;
    ctx: {
      ui: {
        setStatus(key: string, value: string | undefined): void;
        notify(message: string, type?: "info" | "warning" | "error"): void;
      };
    };
    since: number | null;
    /** nodeId + label of every request already handed to the agent. */
    sent: Set<string>;
    /** Groups whose annotation changes the watch has said it can't read. */
    warned: Set<string>;
    /** Requests waiting for the running agent to finish. */
    queue: AnnotationRequest[];
    agent: ChildProcess | null;
    timer?: ReturnType<typeof setInterval>;
    polling: boolean;
  }
  let annotationWatch: AnnotationWatch | null = null;

  /** Update the watch's UI, ignoring a context gone stale with its session. */
  function watchUi(
    watch: AnnotationWatch,
    update: (ui: AnnotationWatch["ctx"]["ui"]) => void,
  ) {
    try {
      update(watch.ctx.ui);
    } catch (error) {
      if (!isStaleSessionContextError(error)) throw error;
    }
  }

  function showWatchStatus(watch: AnnotationWatch) {
    const working = watch.agent ? " · agent working" : "";
    watchUi(watch, (ui) =>
      ui.setStatus("labor-watch", `watching "${watch.file}"${working}`),
    );
  }

  /** Start the background agent on the queued requests unless it's running. */
  function runAnnotationAgent(watch: AnnotationWatch) {
    if (watch.agent || !watch.queue.length) return;
    const requests = watch.queue.splice(0);
    const count =
      requests.length === 1 ? "1 request" : `${requests.length} requests`;
    const log = createWriteStream(WATCH_LOG, { flags: "a" });
    log.write(`\n== ${new Date().toISOString()} "${watch.file}", ${count}\n`);
    // omp gives its shells and kernels the session's file and artifacts dir;
    // the agent runs without a session, so it mustn't inherit them.
    const env = { ...process.env, FIGMA_LABOR_FILE: watch.file };
    delete env.PI_SESSION_FILE;
    delete env.PI_SESSION_ID;
    delete env.PI_ARTIFACTS_DIR;
    const agent = spawn(
      HOST_CLI,
      ["-p", "--no-session", watchMessage(watch.file, requests)],
      { env, stdio: ["ignore", "pipe", "pipe"] },
    );
    watch.agent = agent;
    agent.stdout.pipe(log, { end: false });
    agent.stderr.pipe(log, { end: false });
    let finished = false;
    // "error" (it couldn't start) can be followed by "close"; handle one.
    const finish = (failure: string | null) => {
      if (finished) return;
      finished = true;
      log.end();
      // Stopped with the watch, which killed it.
      if (annotationWatch !== watch || watch.agent !== agent) return;
      watch.agent = null;
      const message = failure
        ? `The annotation agent stopped on ${count} in "${watch.file}" (${failure}). Log: ${WATCH_LOG}. Rerun /figma-labor-watch to retry.`
        : `The annotation agent handled ${count} in "${watch.file}".`;
      watchUi(watch, (ui) => ui.notify(message, failure ? "error" : "info"));
      showWatchStatus(watch);
      runAnnotationAgent(watch);
    };
    agent.on("error", (err) => finish(err.message));
    agent.on("close", (code, signal) => {
      if (code === 0) finish(null);
      else finish(signal ? `killed by ${signal}` : `exit code ${code}`);
    });
    showWatchStatus(watch);
  }

  async function pollAnnotationWatch(
    watch: AnnotationWatch,
    ensureCategory: boolean,
  ): Promise<{ sent: number; createdCategory: boolean }> {
    const { result } = await bridgeCommand(
      "run_script",
      {
        code: annotationScript(WATCH_ANNOTATIONS_SCRIPT, {
          since: watch.since,
          ensureCategory,
          warned: [...watch.warned],
        }),
      },
      { target: watch.file, timeout: 60_000 },
    );
    if (!result || typeof result !== "object" || "error" in result) {
      throw new Error(
        (result as { error?: string } | null)?.error ??
          "The annotation scan returned nothing.",
      );
    }
    const { since, requests, unreadable, createdCategory } = result as {
      since: number;
      requests: AnnotationRequest[];
      unreadable: { nodeId: string; name: string }[];
      createdCategory: boolean;
    };
    watch.since = since;
    if (unreadable.length && annotationWatch === watch) {
      for (const node of unreadable) watch.warned.add(node.nodeId);
      const names = unreadable.map((n) => `"${n.name}" (${n.nodeId})`);
      watchUi(watch, (ui) =>
        ui.notify(
          `Figma gives plugins no annotations on groups, so the watch can't read the one on ${names.join(", ")} in "${watch.file}". Annotate a frame or layer instead.`,
          "warning",
        ),
      );
    }
    const fresh = requests.filter((request) => {
      const key = `${request.nodeId}\n${request.label}`;
      if (watch.sent.has(key)) return false;
      watch.sent.add(key);
      return true;
    });
    if (fresh.length && annotationWatch === watch) {
      watch.queue.push(...fresh);
      runAnnotationAgent(watch);
    }
    return { sent: fresh.length, createdCategory };
  }

  /** Stop the watch, if any, and return the file it watched. */
  function stopAnnotationWatch(): string | null {
    const watch = annotationWatch;
    if (!watch) return null;
    annotationWatch = null;
    clearInterval(watch.timer);
    watch.agent?.kill("SIGTERM");
    watch.agent = null;
    watchUi(watch, (ui) => ui.setStatus("labor-watch", undefined));
    return watch.file;
  }

  function isCurrentBridgeSession(run: number, signal: AbortSignal): boolean {
    return run === bridgeSessionRun && !signal.aborted;
  }

  function startPolling(
    ctx: Parameters<Parameters<typeof pi.on>[1]>[1],
    run: number,
    signal: AbortSignal,
  ) {
    if (pollTimer) return;
    pollTimer = setInterval(async () => {
      if (!isCurrentBridgeSession(run, signal)) {
        stopPolling();
        return;
      }
      const s = await bridgeStatus();
      if (!isCurrentBridgeSession(run, signal)) {
        stopPolling();
        return;
      }
      cachedStatus = s;
      if (!updateFooterStatus(ctx)) stopPolling();
    }, 3000);
  }

  function stopPolling() {
    if (pollTimer) {
      clearInterval(pollTimer);
      pollTimer = null;
    }
  }

  function currentBridgeSessionSignal(): AbortSignal {
    if (!bridgeStartupAbort || bridgeStartupAbort.signal.aborted) {
      bridgeStartupAbort = new AbortController();
    }
    return bridgeStartupAbort.signal;
  }

  pi.on("session_start", async (_event, ctx) => {
    stopAnnotationWatch();
    targetFile = process.env.FIGMA_LABOR_FILE || null;
    bridgeStartupAbort?.abort();
    const run = ++bridgeSessionRun;
    const controller = new AbortController();
    bridgeStartupAbort = controller;

    void (async () => {
      let s = await bridgeStatus();
      if (!isCurrentBridgeSession(run, controller.signal)) return;
      if (!s) {
        await startBridge(controller.signal);
        if (!isCurrentBridgeSession(run, controller.signal)) return;
        s = await bridgeStatus();
        if (!isCurrentBridgeSession(run, controller.signal)) return;
      }
      cachedStatus = s;
      if (!updateFooterStatus(ctx)) return;
      if (s) startPolling(ctx, run, controller.signal);
    })();
  });

  pi.on("session_shutdown", async (_event, ctx) => {
    stopAnnotationWatch();
    bridgeStartupAbort?.abort();
    bridgeStartupAbort = null;
    bridgeSessionRun++;
    stopPolling();
    stopBridge();
    cachedStatus = null;
    updateFooterStatus(ctx);
  });

  // System prompt injection. The full Labor guide is ~10 KB; inject it only
  // while the plugin is connected, and a pointer to it otherwise.
  pi.on("before_agent_start", async (event) => {
    // The first prompt of a session can arrive before session_start's async
    // status probe lands; ask the bridge directly instead of guessing.
    const status = cachedStatus ?? (await bridgeStatus(500));
    if (status?.plugin !== "connected") {
      return {
        systemPrompt: event.systemPrompt + "\n\n" + DISCONNECTED_PROMPT,
      };
    }
    const mcpAvailable = pi
      .getActiveTools()
      .some((toolName) =>
        [
          "get_screenshot",
          "get_design_context",
          "get_metadata",
          "get_variable_defs",
          "search_design_system",
        ].includes(toolName),
      );
    const prompt = PROMPT_TEMPLATE.replace(
      "{{plugin_status}}",
      pluginStatusLabel(status),
    )
      .replace(
        "{{target_file}}",
        targetFile === null ? "none yet" : `"${targetFile}"`,
      )
      .replace("{{mcp_status}}", mcpAvailable ? "available" : "unavailable");
    return {
      systemPrompt: event.systemPrompt + "\n\n" + prompt,
    };
  });

  // Slash commands

  pi.registerCommand("figma-labor-start", {
    description: "Start the figma-labor bridge server",
    handler: async (_args, ctx) => {
      const already = await bridgeStatus();
      if (already) {
        cachedStatus = already;
        updateFooterStatus(ctx);
        ctx.ui.notify(
          `figma-labor bridge is already running.\nPlugin: ${pluginStatusLabel(already)}`,
          "info",
        );
        startPolling(ctx, bridgeSessionRun, currentBridgeSessionSignal());
        return;
      }
      ctx.ui.notify("Starting figma-labor bridge...", "info");
      const ok = await startBridge(currentBridgeSessionSignal());
      if (!ok) {
        cachedStatus = null;
        updateFooterStatus(ctx);
        ctx.ui.notify(
          "Failed to start figma-labor bridge.\n\nMake sure bridge.js exists at:\n" +
            BRIDGE_BIN,
          "error",
        );
        return;
      }
      const status = await bridgeStatus();
      cachedStatus = status;
      updateFooterStatus(ctx);
      ctx.ui.notify(
        `figma-labor bridge started.\nPlugin: ${pluginStatusLabel(status)}`,
        "success",
      );
      startPolling(ctx, bridgeSessionRun, currentBridgeSessionSignal());
    },
  });

  pi.registerCommand("figma-labor-stop", {
    description: "Stop the figma-labor bridge server",
    handler: async (_args, ctx) => {
      stopPolling();
      stopBridge();
      cachedStatus = null;
      updateFooterStatus(ctx);
      ctx.ui.notify("figma-labor bridge stopped.", "info");
    },
  });

  pi.registerCommand("figma-labor", {
    description: "Show Figma bridge server connection status",
    handler: async (_args, ctx) => {
      const status = await bridgeStatus();
      if (!status) {
        ctx.ui.notify(
          "figma-labor bridge is not running.\n\nRun /figma-labor-start to launch it.",
          "error",
        );
        return;
      }
      const files = status.files ?? [];
      const context = status.context;
      const details =
        files.length > 1
          ? `\nFiles:\n${files
              .map(
                (file) =>
                  `  • ${fileLabel(file)}, page "${file.page?.name ?? "?"}"${file.file === targetFile || file.id === targetFile ? " ← this session" : ""}`,
              )
              .join("\n")}`
          : context
            ? `\nEditor: ${context.editorType}\nPage: ${context.page.name}\nSelection: ${context.selectionCount}`
            : "";
      ctx.ui.notify(
        `figma-labor bridge: ${status.bridge}\nFigma plugin: ${status.plugin}${details}`,
        status.plugin === "connected" ? "success" : "info",
      );
    },
  });

  pi.registerCommand("figma-labor-watch", {
    description: `Watch this session's Figma file for "${AGENT_CATEGORY}" annotations and hand new ones to a background agent. /figma-labor-watch <file> picks the file; /figma-labor-watch off stops`,
    handler: async (args, ctx) => {
      const arg = args.trim();
      if (arg === "off") {
        const file = stopAnnotationWatch();
        ctx.ui.notify(
          file
            ? `Stopped watching annotations in "${file}".`
            : "Not watching annotations.",
          "info",
        );
        return;
      }
      if (annotationWatch && !arg) {
        ctx.ui.notify(
          `Watching "${annotationWatch.file}" for "${AGENT_CATEGORY}" annotations. /figma-labor-watch off stops.`,
          "info",
        );
        return;
      }
      const files = (await bridgeStatus())?.files ?? [];
      if (!files.length) {
        ctx.ui.notify("No Figma file has the Labor plugin open.", "error");
        return;
      }
      const query =
        arg || targetFile || (files.length === 1 ? files[0].id : null);
      if (!query) {
        ctx.ui.notify(
          `Several files are connected; name one: /figma-labor-watch <file>. Connected: ${files.map(fileLabel).join(", ")}.`,
          "error",
        );
        return;
      }
      const resolved = resolveFile(files, query);
      if ("error" in resolved) {
        ctx.ui.notify(resolved.error, "error");
        return;
      }
      const editor = resolved.file.editorType;
      if (editor !== "figma" && editor !== "dev") {
        ctx.ui.notify(
          `Annotations exist only in Figma Design and Dev Mode; ${fileLabel(resolved.file)} is open in ${editor ?? "an unknown editor"}.`,
          "error",
        );
        return;
      }

      stopAnnotationWatch();
      targetFile = resolved.target;
      const watch: AnnotationWatch = {
        file: resolved.target,
        ctx,
        since: null,
        sent: new Set(),
        warned: new Set(),
        queue: [],
        agent: null,
        polling: true,
      };
      annotationWatch = watch;
      let first: { sent: number; createdCategory: boolean };
      try {
        first = await pollAnnotationWatch(watch, true);
      } catch (err) {
        if (annotationWatch === watch) annotationWatch = null;
        const msg = err instanceof Error ? err.message : String(err);
        ctx.ui.notify(
          `Couldn't read annotations in "${watch.file}": ${msg}`,
          "error",
        );
        return;
      } finally {
        watch.polling = false;
      }
      // Stopped, or replaced by another watch, during the first scan.
      if (annotationWatch !== watch) return;

      watch.timer = setInterval(async () => {
        if (watch.polling) return;
        watch.polling = true;
        try {
          await pollAnnotationWatch(watch, false);
        } catch {
          // The plugin or bridge is away; the next tick retries.
        } finally {
          watch.polling = false;
        }
      }, 3000);
      showWatchStatus(watch);
      const created = first.createdCategory
        ? ` Added the "${AGENT_CATEGORY}" annotation category to the file.`
        : "";
      const sent = first.sent
        ? ` Handed ${first.sent} pending request${first.sent === 1 ? "" : "s"} to a background agent.`
        : " No pending requests yet.";
      ctx.ui.notify(
        `Watching "${watch.file}" for "${AGENT_CATEGORY}" annotations.${created}${sent}`,
        "success",
      );
    },
  });

  // Tools

  // ## Files

  pi.registerTool({
    name: "labor_list_files",
    label: "List Files",
    description:
      "List the Figma files that have the Labor plugin open, and which one this agent's Labor tools target.",
    parameters: Type.Object({}),
    async execute() {
      const status = await bridgeStatus();
      if (!status) {
        return {
          content: [
            {
              type: "text" as const,
              text: "figma-labor bridge is not running.",
            },
          ],
          isError: true,
        };
      }
      if (!status.files) {
        return {
          content: [
            {
              type: "text" as const,
              text: "The running figma-labor bridge predates multi-file support. Stop its bridge.js process so the extension can start the current one.",
            },
          ],
          isError: true,
        };
      }
      return {
        content: [
          {
            type: "text" as const,
            text: JSON.stringify(
              { target: targetFile, files: status.files },
              null,
              2,
            ),
          },
        ],
      };
    },
  });

  pi.registerTool({
    name: "labor_use_file",
    label: "Use File",
    description:
      "Point this agent's Labor tools at one connected Figma file, by file name or connection id from labor_list_files. Required when several files are connected.",
    parameters: Type.Object({
      file: Type.String({
        description: "Exact file name, or connection id from labor_list_files",
      }),
    }),
    async execute(_id, params) {
      const files = (await bridgeStatus())?.files ?? [];
      const resolved = resolveFile(files, params.file);
      if ("error" in resolved) {
        return {
          content: [{ type: "text" as const, text: resolved.error }],
          isError: true,
        };
      }
      const { file: match, target } = resolved;
      targetFile = target;
      // The watch follows this session's file; it never runs against another.
      const stoppedWatch =
        annotationWatch && annotationWatch.file !== target
          ? stopAnnotationWatch()
          : null;
      const watchNote = stoppedWatch
        ? ` Stopped the annotation watch on "${stoppedWatch}"; tell the user, who can restart it with /figma-labor-watch.`
        : "";
      return {
        content: [
          {
            type: "text" as const,
            text: `Labor tools now target ${fileLabel(match)}: ${match.editorType ?? "unknown"} editor, page "${match.page?.name ?? "?"}".${watchNote}`,
          },
        ],
      };
    },
  });

  // ## Selection & navigation

  pi.registerTool({
    name: "labor_get_selection",
    label: "Get Selection",
    description:
      "Lightweight discovery: get the active editor, page, and currently selected nodes. Always call this first before editor-specific tools.",
    parameters: Type.Object({}),
    async execute(_id, _params, signal) {
      return runTool("get_selection", {}, { signal, includeContext: true });
    },
  });

  pi.registerTool({
    name: "labor_select_node",
    label: "Select Node",
    description: "Select a node in Figma and zoom the viewport to it.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID to select" }),
    }),
    async execute(_id, params, signal) {
      return runTool("select_node", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_zoom_to_node",
    label: "Zoom To Node",
    description: "Zoom the viewport to a node without changing selection.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID to zoom to" }),
    }),
    async execute(_id, params, signal) {
      return runTool("zoom_to_node", params, { signal });
    },
  });

  // ## Reading & inspection

  pi.registerTool({
    name: "labor_get_node",
    label: "Get Node",
    description: "Get a Figma node by ID, including its properties.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID, e.g. '123:456'" }),
    }),
    async execute(_id, params, signal) {
      return runTool("get_node", { nodeId: params.nodeId }, { signal });
    },
  });

  pi.registerTool({
    name: "labor_get_node_full",
    label: "Get Node Full",
    description:
      "Get a Figma node with ALL properties including auto-layout, constraints, padding, sizing modes, min/max sizes, clipsContent, and locked state. Use this instead of labor_get_node when you need to diagnose layout issues or read/set alignment.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID, e.g. '123:456'" }),
    }),
    async execute(_id, params, signal) {
      return runTool("get_node_full", { nodeId: params.nodeId }, { signal });
    },
  });

  pi.registerTool({
    name: "labor_get_children",
    label: "Get Children",
    description:
      "List children of a node. Omit nodeId to list children of the current page.",
    parameters: Type.Object({
      nodeId: Type.Optional(
        Type.String({ description: "Parent node ID. Omit for current page." }),
      ),
    }),
    async execute(_id, params, signal) {
      return runTool("get_children", { nodeId: params.nodeId }, { signal });
    },
  });

  pi.registerTool({
    name: "labor_run_script",
    label: "Run Script",
    description:
      "Run arbitrary JavaScript in the Figma plugin context. The script has full access to the `figma` Plugin API. Use `return` to return a value. Async is supported. Example: `return figma.currentPage.findAll(n => n.type === 'COMPONENT').length`",
    parameters: Type.Object({
      code: Type.String({
        description:
          "JS code to execute. Has access to `figma`. Use return to return a value.",
      }),
    }),
    async execute(_id, params, signal) {
      return runTool(
        "run_script",
        { code: params.code },
        { timeout: 60_000, signal },
      );
    },
  });

  // ## Annotations

  pi.registerTool({
    name: "labor_get_annotations",
    label: "Get Annotations",
    description: `List annotations, the notes and pinned properties attached to nodes in Figma Design and Dev Mode. Searches the current page by default, or the selection, one node and its descendants, or the whole document. Annotations in the "${AGENT_CATEGORY}" category, or whose text starts with "agent:", are requests for you and carry a status: pending or replied. Each annotation's index is what labor_update_annotations takes. Figma gives plugins no annotations on groups, so those never appear.`,
    parameters: Type.Object({
      nodeId: Type.Optional(
        Type.String({ description: "Search this node and its descendants" }),
      ),
      scope: Type.Optional(
        StringEnum(["page", "selection", "document"] as const, {
          description:
            "Where to search when nodeId is omitted. Default: page (the current page)",
        }),
      ),
      category: Type.Optional(
        Type.String({
          description: `Only annotations in this category, by label or id, e.g. "${AGENT_CATEGORY}"`,
        }),
      ),
      limit: Type.Optional(
        Type.Integer({
          minimum: 1,
          maximum: 200,
          description: "Most nodes to return. Default 50",
        }),
      ),
    }),
    async execute(_id, params, signal) {
      const code = annotationScript(GET_ANNOTATIONS_SCRIPT, {
        ...params,
        limit: params.limit ?? 50,
      });
      return runTool("run_script", { code }, { timeout: 60_000, signal });
    },
  });

  pi.registerTool({
    name: "labor_update_annotations",
    label: "Update Annotations",
    description: `Add, update, remove, or reply to one annotation on a node, leaving its other annotations as they are. "reply" appends a ${AGENT_REPLY_MARK} paragraph to an existing annotation: use it to answer "${AGENT_CATEGORY}" requests; replying to an "agent:" request also files it under "${AGENT_CATEGORY}" and drops the prefix. Use this tool instead of assigning node.annotations in a script, which replaces every annotation on the node.`,
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID" }),
      action: StringEnum(["add", "update", "remove", "reply"] as const),
      index: Type.Optional(
        Type.Integer({
          minimum: 0,
          description:
            "Annotation index from labor_get_annotations. Required except for add",
        }),
      ),
      label: Type.Optional(
        Type.String({
          description:
            "Markdown text. reply: the one-line reply. update: replaces the text; an empty string removes it",
        }),
      ),
      category: Type.Optional(
        Type.String({
          description: `Category label or id. update: an empty string removes it. "${AGENT_CATEGORY}" is added to the file if it's missing`,
        }),
      ),
      properties: Type.Optional(
        Type.Array(StringEnum(ANNOTATION_PROPERTY_TYPES), {
          description:
            "Properties to pin, e.g. width or fills. update: replaces them; an empty array removes them",
        }),
      ),
    }),
    async execute(_id, params, signal) {
      const code = annotationScript(UPDATE_ANNOTATIONS_SCRIPT, params);
      return runTool("run_script", { code }, { timeout: 60_000, signal });
    },
  });

  // ## Components & variants

  pi.registerTool({
    name: "labor_get_component_props",
    label: "Get Component Props",
    description:
      "Get component property definitions for a COMPONENT_SET node, including variant options.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "COMPONENT_SET node ID" }),
    }),
    async execute(_id, params, signal) {
      return runTool(
        "get_component_properties",
        { nodeId: params.nodeId },
        { signal },
      );
    },
  });

  pi.registerTool({
    name: "labor_get_component_set_summary",
    label: "Get Component Set Summary",
    description:
      "Get a COMPONENT_SET summary including layout, variant groups, component property definitions, and child variant names/sizes.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "COMPONENT_SET node ID" }),
    }),
    async execute(_id, params, signal) {
      return runTool(
        "get_component_set_summary",
        { nodeId: params.nodeId },
        { signal },
      );
    },
  });

  pi.registerTool({
    name: "labor_reorder_variant_options",
    label: "Reorder Variant Options",
    description:
      "Reorder the options of a VARIANT property on a component or component set.",
    parameters: Type.Object({
      nodeId: Type.String({
        description: "COMPONENT or COMPONENT_SET node ID",
      }),
      property: Type.String({
        description: "Variant property name, e.g. 'size'",
      }),
      order: Type.Array(Type.String(), {
        description:
          "New variant option order, e.g. ['small', 'medium', 'large']",
      }),
    }),
    async execute(_id, params, signal) {
      return runTool("reorder_variant_options", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_create_component_set",
    label: "Create Component Set",
    description:
      "Combine existing COMPONENT nodes into a COMPONENT_SET. Optionally set the new set name, parent, and position.",
    parameters: Type.Object({
      componentIds: Type.Array(Type.String(), {
        description: "COMPONENT node IDs to combine as variants",
      }),
      name: Type.Optional(
        Type.String({ description: "New component set name" }),
      ),
      parentId: Type.Optional(
        Type.String({ description: "Parent node ID for the new set" }),
      ),
      x: Type.Optional(
        Type.Number({ description: "X position for the new set" }),
      ),
      y: Type.Optional(
        Type.Number({ description: "Y position for the new set" }),
      ),
    }),
    async execute(_id, params, signal) {
      return runTool(
        "create_component_set",
        params as Record<string, unknown>,
        { signal },
      );
    },
  });

  pi.registerTool({
    name: "labor_create_instance",
    label: "Create Instance",
    description:
      "Create an instance of a COMPONENT node and place it on the canvas or inside a parent. The componentId must point to a COMPONENT (not a COMPONENT_SET) — call labor_get_children on the set to find the specific variant you want. Optionally pass properties to set variant or text overrides.",
    parameters: Type.Object({
      componentId: Type.String({
        description:
          "ID of the COMPONENT node to instantiate (not COMPONENT_SET)",
      }),
      parentId: Type.Optional(
        Type.String({
          description:
            "Parent node ID to append the instance into. Omit to place on current page.",
        }),
      ),
      x: Type.Optional(Type.Number({ description: "X position" })),
      y: Type.Optional(Type.Number({ description: "Y position" })),
      name: Type.Optional(
        Type.String({ description: "Override the instance name" }),
      ),
      properties: Type.Optional(
        Type.Record(Type.String(), Type.Unknown(), {
          description:
            "Component property overrides, e.g. { 'size': 'medium', 'label': 'Click me' }",
        }),
      ),
    }),
    async execute(_id, params, signal) {
      return runTool("create_instance", params as Record<string, unknown>, {
        signal,
      });
    },
  });

  pi.registerTool({
    name: "labor_detach_instance",
    label: "Detach Instance",
    description:
      "Detach a component instance, converting it into a plain frame whose children can be freely repositioned. Call this when you need to reorder or reposition children that are locked inside an instance.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "INSTANCE node ID to detach" }),
    }),
    async execute(_id, params, signal) {
      return runTool("detach_instance", params, { signal });
    },
  });

  // ## Create & structure

  pi.registerTool({
    name: "labor_create_node",
    label: "Create Node",
    description:
      "Create a primitive or native product node. Supports standard nodes; FigJam stickies, shapes, connectors, code blocks, tables, and sections; and Slides slides and rows. In Slides, ordinary content defaults to the focused slide.",
    parameters: Type.Object({
      type: StringEnum([
        "RECTANGLE",
        "ELLIPSE",
        "FRAME",
        "TEXT",
        "STICKY",
        "SHAPE_WITH_TEXT",
        "CONNECTOR",
        "CODE_BLOCK",
        "TABLE",
        "SECTION",
        "SLIDE",
        "SLIDE_ROW",
      ] as const),
      parentId: Type.Optional(
        Type.String({
          description: "Parent node ID. Omit to add to current page.",
        }),
      ),
      name: Type.Optional(Type.String({ description: "Node name" })),
      x: Type.Optional(Type.Number()),
      y: Type.Optional(Type.Number()),
      width: Type.Optional(Type.Number()),
      height: Type.Optional(Type.Number()),
      text: Type.Optional(
        Type.String({ description: "Initial text for text-bearing nodes" }),
      ),
      shapeType: Type.Optional(
        Type.String({
          description: "FigJam SHAPE_WITH_TEXT shape type",
        }),
      ),
      connectorLineType: Type.Optional(
        StringEnum(["ELBOWED", "STRAIGHT", "CURVED"] as const),
      ),
      startNodeId: Type.Optional(
        Type.String({ description: "CONNECTOR start node ID" }),
      ),
      endNodeId: Type.Optional(
        Type.String({ description: "CONNECTOR end node ID" }),
      ),
      code: Type.Optional(Type.String({ description: "CODE_BLOCK contents" })),
      codeLanguage: Type.Optional(
        Type.String({
          description: "CODE_BLOCK language, such as TYPESCRIPT or PLAINTEXT",
        }),
      ),
      rows: Type.Optional(Type.Number({ description: "TABLE row count" })),
      columns: Type.Optional(
        Type.Number({ description: "TABLE column count" }),
      ),
      row: Type.Optional(
        Type.Number({ description: "SLIDE or SLIDE_ROW grid row" }),
      ),
      column: Type.Optional(Type.Number({ description: "SLIDE grid column" })),
    }),
    async execute(_id, params, signal) {
      return runTool("create_node", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_clone_node",
    label: "Clone Node",
    description: `Clone a node. Optionally rename it, move it to another parent, and position it. "${AGENT_CATEGORY}" requests copied onto the clone are dropped; other annotations stay.`,
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID to clone" }),
      parentId: Type.Optional(
        Type.String({ description: "Target parent node ID" }),
      ),
      name: Type.Optional(
        Type.String({ description: "Override the cloned node name" }),
      ),
      x: Type.Optional(Type.Number({ description: "X position" })),
      y: Type.Optional(Type.Number({ description: "Y position" })),
    }),
    async execute(_id, params, signal) {
      return runTool("clone_node", params, {
        signal,
        after: (clone, file) => dropCopiedRequests(clone, file, signal),
      });
    },
  });

  pi.registerTool({
    name: "labor_move_node",
    label: "Move Node",
    description:
      "Move a node to a different parent, optionally at a specific index.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID to move" }),
      parentId: Type.String({ description: "Target parent node ID" }),
      index: Type.Optional(
        Type.Number({ description: "Insert at this child index (0 = first)" }),
      ),
    }),
    async execute(_id, params, signal) {
      return runTool("move_node", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_delete_node",
    label: "Delete Node",
    description:
      "Delete a node. This is destructive — call labor_undo immediately if it was a mistake.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID to delete" }),
    }),
    async execute(_id, params, signal) {
      return runTool("delete_node", params, { signal });
    },
  });

  // ## Layout, styling & text

  pi.registerTool({
    name: "labor_update_properties",
    label: "Update Properties",
    description:
      "Update generic node properties plus supported FigJam-native properties for stickies, sections, code blocks, and connectors.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID" }),
      name: Type.Optional(Type.String({ description: "New name" })),
      x: Type.Optional(Type.Number({ description: "X position" })),
      y: Type.Optional(Type.Number({ description: "Y position" })),
      width: Type.Optional(Type.Number({ description: "Width in px" })),
      height: Type.Optional(Type.Number({ description: "Height in px" })),
      opacity: Type.Optional(Type.Number({ description: "Opacity 0–1" })),
      visible: Type.Optional(Type.Boolean({ description: "Visibility" })),
      rotation: Type.Optional(
        Type.Number({ description: "Rotation in degrees" }),
      ),
      authorVisible: Type.Optional(
        Type.Boolean({ description: "STICKY author visibility" }),
      ),
      isWideWidth: Type.Optional(
        Type.Boolean({ description: "Whether a STICKY uses wide format" }),
      ),
      sectionContentsHidden: Type.Optional(
        Type.Boolean({ description: "Whether SECTION contents are hidden" }),
      ),
      codeLanguage: Type.Optional(
        StringEnum(
          [
            "TYPESCRIPT",
            "CPP",
            "RUBY",
            "CSS",
            "JAVASCRIPT",
            "HTML",
            "JSON",
            "GRAPHQL",
            "PYTHON",
            "GO",
            "SQL",
            "SWIFT",
            "KOTLIN",
            "RUST",
            "BASH",
            "PLAINTEXT",
            "DART",
          ] as const,
          { description: "CODE_BLOCK language" },
        ),
      ),
      connectorLineType: Type.Optional(
        StringEnum(["ELBOWED", "STRAIGHT", "CURVED"] as const, {
          description: "CONNECTOR line type",
        }),
      ),
      connectorStartNodeId: Type.Optional(
        Type.String({
          description: "Node ID for the CONNECTOR start endpoint",
        }),
      ),
      connectorEndNodeId: Type.Optional(
        Type.String({ description: "Node ID for the CONNECTOR end endpoint" }),
      ),
      connectorStartMagnet: Type.Optional(
        StringEnum([
          "NONE",
          "AUTO",
          "TOP",
          "LEFT",
          "BOTTOM",
          "RIGHT",
          "CENTER",
        ] as const),
      ),
      connectorEndMagnet: Type.Optional(
        StringEnum([
          "NONE",
          "AUTO",
          "TOP",
          "LEFT",
          "BOTTOM",
          "RIGHT",
          "CENTER",
        ] as const),
      ),
      connectorStartStrokeCap: Type.Optional(
        StringEnum([
          "NONE",
          "ARROW_EQUILATERAL",
          "ARROW_LINES",
          "TRIANGLE_FILLED",
          "DIAMOND_FILLED",
          "CIRCLE_FILLED",
          "ERD_ZERO_OR_ONE",
          "ERD_EXACTLY_ONE",
          "ERD_ZERO_OR_MORE",
          "ERD_ONE_OR_MORE",
          "ERD_ONE",
          "ERD_MANY",
        ] as const),
      ),
      connectorEndStrokeCap: Type.Optional(
        StringEnum([
          "NONE",
          "ARROW_EQUILATERAL",
          "ARROW_LINES",
          "TRIANGLE_FILLED",
          "DIAMOND_FILLED",
          "CIRCLE_FILLED",
          "ERD_ZERO_OR_ONE",
          "ERD_EXACTLY_ONE",
          "ERD_ZERO_OR_MORE",
          "ERD_ONE_OR_MORE",
          "ERD_ONE",
          "ERD_MANY",
        ] as const),
      ),
    }),
    async execute(_id, params, signal) {
      const { nodeId, ...properties } = params;
      return runTool("update_properties", { nodeId, properties }, { signal });
    },
  });

  pi.registerTool({
    name: "labor_update_table",
    label: "Update Table",
    description:
      "Insert, remove, move, or resize rows and columns on a FigJam TABLE node.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "TABLE node ID" }),
      action: StringEnum([
        "INSERT_ROW",
        "INSERT_COLUMN",
        "REMOVE_ROW",
        "REMOVE_COLUMN",
        "MOVE_ROW",
        "MOVE_COLUMN",
        "RESIZE_ROW",
        "RESIZE_COLUMN",
      ] as const),
      rowIndex: Type.Optional(Type.Integer({ minimum: 0 })),
      columnIndex: Type.Optional(Type.Integer({ minimum: 0 })),
      fromIndex: Type.Optional(Type.Integer({ minimum: 0 })),
      toIndex: Type.Optional(Type.Integer({ minimum: 0 })),
      width: Type.Optional(Type.Number({ minimum: 0.01 })),
      height: Type.Optional(Type.Number({ minimum: 0.01 })),
    }),
    async execute(_id, params, signal) {
      return runTool("update_table", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_resize_node",
    label: "Resize Node",
    description:
      "Resize a node to specific dimensions. Zooms the viewport to it.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID" }),
      width: Type.Number({ description: "New width in px" }),
      height: Type.Number({ description: "New height in px" }),
    }),
    async execute(_id, params, signal) {
      return runTool("resize_node", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_scale_node",
    label: "Scale Node",
    description:
      "Scale a node proportionally like Figma's Scale tool, using a scale factor from the top-left corner.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID" }),
      scale: Type.Number({ description: "Scale factor, e.g. 0.5 or 1.5" }),
    }),
    async execute(_id, params, signal) {
      return runTool("scale_node", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_set_layout",
    label: "Set Layout",
    description:
      "Set auto-layout properties on a frame or component. Use layoutMode to enable auto-layout, then set alignment, sizing modes, padding and spacing. primaryAxisAlignItems/counterAxisAlignItems require layoutMode to be HORIZONTAL or VERTICAL.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Frame or component node ID" }),
      layoutMode: Type.Optional(
        StringEnum(["NONE", "HORIZONTAL", "VERTICAL"] as const, {
          description: "Auto-layout direction. NONE disables auto-layout.",
        }),
      ),
      primaryAxisAlignItems: Type.Optional(
        StringEnum(["MIN", "CENTER", "MAX", "SPACE_BETWEEN"] as const, {
          description:
            "Main axis alignment (requires layoutMode HORIZONTAL or VERTICAL)",
        }),
      ),
      counterAxisAlignItems: Type.Optional(
        StringEnum(["MIN", "CENTER", "MAX", "BASELINE"] as const, {
          description:
            "Cross axis alignment (requires layoutMode HORIZONTAL or VERTICAL)",
        }),
      ),
      primaryAxisSizingMode: Type.Optional(
        StringEnum(["FIXED", "AUTO"] as const, {
          description: "Whether the frame hugs content on the main axis",
        }),
      ),
      counterAxisSizingMode: Type.Optional(
        StringEnum(["FIXED", "AUTO"] as const, {
          description: "Whether the frame hugs content on the cross axis",
        }),
      ),
      paddingTop: Type.Optional(
        Type.Number({ description: "Top padding in px" }),
      ),
      paddingRight: Type.Optional(
        Type.Number({ description: "Right padding in px" }),
      ),
      paddingBottom: Type.Optional(
        Type.Number({ description: "Bottom padding in px" }),
      ),
      paddingLeft: Type.Optional(
        Type.Number({ description: "Left padding in px" }),
      ),
      itemSpacing: Type.Optional(
        Type.Number({ description: "Gap between children in px" }),
      ),
    }),
    async execute(_id, params, signal) {
      const { nodeId, ...layoutProps } = params;
      return runTool("set_layout", { nodeId, ...layoutProps }, { signal });
    },
  });

  pi.registerTool({
    name: "labor_update_fills",
    label: "Update Fills",
    description:
      "Replace the fill colors of a node. Colors use 0–1 range for r/g/b/a.",
    parameters: Type.Object({
      nodeId: Type.String({ description: "Node ID" }),
      fills: Type.Array(
        Type.Object({
          r: Type.Number({ description: "Red 0–1" }),
          g: Type.Number({ description: "Green 0–1" }),
          b: Type.Number({ description: "Blue 0–1" }),
          a: Type.Optional(
            Type.Number({ description: "Alpha 0–1, defaults to 1" }),
          ),
        }),
        { description: "Array of solid fills" },
      ),
    }),
    async execute(_id, params, signal) {
      return runTool("update_fills", params, { signal });
    },
  });

  pi.registerTool({
    name: "labor_update_text",
    label: "Update Text",
    description:
      "Change text content and/or font size on a TEXT node or a native FigJam node with an editable text sublayer, such as a sticky, shape, or connector.",
    parameters: Type.Object({
      nodeId: Type.String({
        description: "TEXT or text-bearing FigJam node ID",
      }),
      text: Type.Optional(Type.String({ description: "New text content" })),
      fontSize: Type.Optional(Type.Number({ description: "Font size in px" })),
    }),
    async execute(_id, params, signal) {
      return runTool("update_text", params, { signal });
    },
  });

  // ## Safety

  pi.registerTool({
    name: "labor_undo",
    label: "Undo",
    description:
      "Undo the last Figma operation. Call this immediately if a change was wrong.",
    parameters: Type.Object({}),
    async execute(_id, _params, signal) {
      const status = await bridgeStatus();
      if (!status || status.plugin !== "connected") {
        return {
          content: [
            {
              type: "text" as const,
              text: "Plugin not connected — cannot undo.",
            },
          ],
          isError: true,
        };
      }
      try {
        await bridgeUndo(targetFile);
        return { content: [{ type: "text" as const, text: "Undo applied." }] };
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        return {
          content: [{ type: "text" as const, text: `Undo failed: ${msg}` }],
          isError: true,
        };
      }
    },
  });
}
