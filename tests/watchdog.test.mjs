#!/usr/bin/env node
/**
 * Unit tests for the p2m-agent-bench watchdog.
 *
 * Every rule is driven by synthetic jsonl lines in the exact shape the harness
 * sees (`opencode run --format json` for agent.jsonl, the guard plugin's jsonl
 * for guard.log), so no real session, model call or filesystem is needed.
 *
 *   node --test tests/
 */

import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import test from "node:test"

import {
  WATCHDOG_DEFAULTS,
  createWatchdog,
  dirMaxMtime,
  errorSignature,
  parseWatchdogLine,
  resourceKey,
  tailJsonl,
  watchdogConfig,
} from "../core.mjs"

// ---------------------------------------------------------------------------
// Synthetic transcript helpers — same shapes as a real agent.jsonl
// ---------------------------------------------------------------------------

const stepStart = (i = 0) => ({ type: "step_start", timestamp: 1000 + i, part: { messageID: `msg_${i}` } })

const stepFinish = (out, i = 0) => ({
  type: "step_finish",
  timestamp: 1100 + i,
  part: { messageID: `msg_${i}`, tokens: { input: 100, output: out } },
})

const toolUse = (tool, input, { status = "completed", output = "", error = "" } = {}) => ({
  type: "tool_use",
  part: { tool, state: { status, input, output, error } },
})

const deniedTool = (tool, input, message = "Permission denied: external_directory") =>
  toolUse(tool, input, { status: "error", error: message })

const guardDeny = (tool, resource) => ({ type: "guard", hook: "permission.evaluate", tool, action: "shell", resource, decision: "deny" })

function feedAll(events, opts = {}) {
  const wd = createWatchdog({ taskDir: null, statMtime: () => 1000, ...opts })
  let stop = null
  for (const ev of events) {
    stop = wd.feed(ev, ev?.__src)
    if (stop) break
  }
  return { wd, stop }
}

// ---------------------------------------------------------------------------
// Rule 1 — 5 consecutive identical tool calls (same tool + normalized input)
// ---------------------------------------------------------------------------

test("rule 1: 5 identical tool calls stop the session", () => {
  const call = () => toolUse("shell", { command: "grep -rn constantsTower ~ --include=*.lean" })
  const { stop, wd } = feedAll([stepStart(0), call(), call(), call(), call(), call()])
  assert.ok(stop, "expected an early stop")
  assert.equal(stop.reason, "repeated_tool_call")
  assert.equal(stop.turn, 1)
  assert.equal(typeof stop.elapsed, "number")
  assert.deepEqual(Object.keys(stop).sort(), ["elapsed", "reason", "turn"])
  assert.equal(wd.state.tool_streak, 5)
})

test("rule 1: different inputs / different tools never accumulate", () => {
  const events = [stepStart(0)]
  for (let i = 0; i < 10; i++) events.push(toolUse("shell", { command: `ls dir${i}` }))
  for (let i = 0; i < 10; i++) events.push(toolUse(i % 2 ? "read" : "grep", { path: "Problem.lean" }))
  const { stop } = feedAll(events)
  assert.equal(stop, null, "no rule may fire on a non-repeating transcript")
})

test("rule 1: 4 identical calls are below the default threshold", () => {
  const call = () => toolUse("read", { path: "Problem.lean" })
  const { stop } = feedAll([stepStart(0), call(), call(), call(), call()])
  assert.equal(stop, null)
})

test("rule 1: input key is normalized (whitespace, key order)", () => {
  const a = () => toolUse("shell", { command: "lake  env   lean Problem.lean", timeout: 9 })
  const b = () => toolUse("shell", { timeout: 9, command: "lake env lean Problem.lean" })
  const { stop } = feedAll([stepStart(0), a(), b(), a(), b(), a()])
  assert.equal(stop?.reason, "repeated_tool_call")
})

test("rule 1: threshold is configurable (WATCHDOG_REPEAT_TOOL)", () => {
  const cfg = watchdogConfig({ WATCHDOG_REPEAT_TOOL: "3" })
  assert.equal(cfg.repeatTool, 3)
  const call = () => toolUse("grep", { pattern: "foo" })
  const { stop } = feedAll([stepStart(0), call(), call(), call()], { config: cfg })
  assert.equal(stop?.reason, "repeated_tool_call")
})

// ---------------------------------------------------------------------------
// Rule 2 — 3 consecutive guard denies on the same resource
// ---------------------------------------------------------------------------

test("rule 2: 3 guard denials on the same resource stop the session", () => {
  const resource = "grep -rn constantsTower ~/lean-4.28-reap/mathlib4-0df444a/Mathlib"
  const { stop, wd } = feedAll([stepStart(0), guardDeny("shell", resource), guardDeny("shell", resource), guardDeny("shell", resource)])
  assert.equal(stop?.reason, "guard_denied_same_resource")
  assert.equal(wd.state.deny_streak, 3)
})

test("rule 2: same resource through different tools still counts", () => {
  const p = "~/lean-4.28-reap/formalpedia/envs/0df444a/Solutions/Sol_x.lean"
  const { stop } = feedAll([
    stepStart(0),
    guardDeny("read", p),
    guardDeny("shell", `cat ${p}`),
    guardDeny("grep", p),
  ])
  assert.equal(stop?.reason, "guard_denied_same_resource")
})

test("rule 2: denials of different resources do not accumulate", () => {
  const { stop } = feedAll([
    stepStart(0),
    guardDeny("shell", "cat ~/lean-4.28-reap/a.lean"),
    guardDeny("shell", "cat ./data/bank_local/T5.jsonl"),
    guardDeny("shell", "cat /tmp/opencode/x.lean"),
  ])
  assert.equal(stop, null)
})

test("rule 2: a successful call resets the deny streak", () => {
  const r = "cat ~/lean-4.28-reap/formalpedia/x"
  const { stop } = feedAll([
    stepStart(0),
    guardDeny("shell", r),
    guardDeny("shell", r),
    toolUse("read", { path: "Problem.lean" }),
    guardDeny("shell", r),
    guardDeny("shell", r),
  ])
  assert.equal(stop, null, "2 denies, a success, then 2 more is not 3 in a row")
})

test("rule 2: agent.jsonl denials and guard.log denials are not double counted", () => {
  const r = "cat ~/lean-4.28-reap/formalpedia/x"
  const { stop, wd } = feedAll([
    stepStart(0),
    { ...guardDeny("shell", r), __src: "guard.log" },
    { ...deniedTool("shell", { command: r }), __src: "agent.jsonl" }, // same denial, other source
    { ...guardDeny("shell", r), __src: "guard.log" },
    { ...deniedTool("shell", { command: r }), __src: "agent.jsonl" },
  ])
  assert.equal(stop, null, "two physical denials must not look like four")
  assert.equal(wd.state.deny_streak, 2)
})

test("rule 2: threshold is configurable (WATCHDOG_GUARD_DENY)", () => {
  const cfg = watchdogConfig({ WATCHDOG_GUARD_DENY: "2" })
  const r = "cat ~/lean-4.28-reap/bank/T1.jsonl"
  const { stop } = feedAll([stepStart(0), guardDeny("shell", r), guardDeny("shell", r)], { config: cfg })
  assert.equal(stop?.reason, "guard_denied_same_resource")
})

// ---------------------------------------------------------------------------
// Rule 3 — 8 turns with no file mtime change AND no new assistant tokens
// ---------------------------------------------------------------------------

test("rule 3: 8 turns without mtime change or new tokens stop the session", () => {
  const events = []
  for (let i = 0; i < 12; i++) events.push(stepStart(i), stepFinish(0, i))
  const { stop, wd } = feedAll(events, { statMtime: () => 1000 })
  assert.equal(stop?.reason, "idle_no_progress")
  assert.equal(stop?.turn, 8)
  assert.equal(wd.state.turn, 8)
})

test("rule 3: new assistant tokens reset the idle window", () => {
  const events = []
  // 7 productive turns (each generates tokens) …
  for (let i = 0; i < 7; i++) events.push(stepStart(i), stepFinish(400, i))
  // … then 7 silent turns: 8 + 8 = 16 is the first turn that may fire.
  for (let i = 7; i < 14; i++) events.push(stepStart(i), stepFinish(0, i))
  const { stop, wd } = feedAll(events, { statMtime: () => 1000 })
  assert.equal(stop, null, "tokens at every turn must reset the window")
  assert.equal(wd.state.turn, 14)
  assert.equal(wd.state.idle.turn, 8)
})

test("rule 3: a file mtime change resets the idle window", () => {
  let mtime = 1000
  const wd = createWatchdog({ taskDir: null, statMtime: () => mtime })
  let stop = null
  for (let i = 0; i < 7; i++) {
    stop = wd.feed(stepStart(i)) ?? stop
    wd.feed(stepFinish(0, i))
  }
  assert.equal(stop, null)
  mtime = 2000 // the agent writes a file just before turn 8 starts
  for (let i = 7; i < 14 && !stop; i++) {
    stop = wd.feed(stepStart(i)) ?? stop
    wd.feed(stepFinish(0, i))
  }
  assert.equal(stop, null, "a write must reset the idle window")
  assert.equal(wd.state.idle.turn, 8)
  assert.equal(wd.state.idle.mtime, 2000)
  // … and 8 silent turns after that write do stop it.
  for (let i = 14; i < 18 && !stop; i++) {
    stop = wd.feed(stepStart(i)) ?? stop
    wd.feed(stepFinish(0, i))
  }
  assert.equal(stop?.reason, "idle_no_progress")
  assert.equal(stop?.turn, 16)
})

test("rule 3: threshold is configurable (WATCHDOG_IDLE_TURNS)", () => {
  const cfg = watchdogConfig({ WATCHDOG_IDLE_TURNS: "3" })
  const events = []
  for (let i = 0; i < 5; i++) events.push(stepStart(i), stepFinish(0, i))
  const { stop } = feedAll(events, { config: cfg, statMtime: () => 1000 })
  assert.equal(stop?.reason, "idle_no_progress")
  assert.equal(stop?.turn, 3)
})

// ---------------------------------------------------------------------------
// Rule 4 — the same compiler error 4 times in a row
// ---------------------------------------------------------------------------

const compile = (err, n = 0) =>
  toolUse(
    "shell",
    { command: `lake env lean Problem${n ? n : ""}.lean` },
    { error: "", output: err ? `Problem.lean:12:4: error: ${err}` : "" },
  )

test("rule 4: the same compiler error 4 times stops the session", () => {
  const e = "unknown identifier 'maximalIdeal'"
  const { stop, wd } = feedAll([stepStart(0), compile(e), compile(e), compile(e), compile(e)])
  assert.equal(stop?.reason, "repeated_compiler_error")
  assert.equal(wd.state.error_streak, 4)
})

test("rule 4: line/column numbers do not defeat the match", () => {
  const ev = (line) => toolUse("shell", { command: "lake env lean Problem.lean" }, { output: `Problem.lean:${line}:9: error: unsolved goals` })
  const { stop } = feedAll([stepStart(0), ev(10), ev(99), ev(3), ev(41)])
  assert.equal(stop?.reason, "repeated_compiler_error")
})

test("rule 4: different errors, or a clean compile in between, do not accumulate", () => {
  const e1 = "unknown identifier 'foo'"
  const e2 = "type mismatch"
  assert.equal(feedAll([stepStart(0), compile(e1, 1), compile(e2, 2), compile(e1, 3), compile(e2, 4)]).stop, null)
  assert.equal(
    feedAll([stepStart(0), compile(e1, 1), compile(e1, 2), compile(null, 3), compile(e1, 4), compile(e1, 5)]).stop,
    null,
    "a clean compile resets the error streak",
  )
})

test("rule 4: threshold is configurable (WATCHDOG_REPEAT_ERROR)", () => {
  const cfg = watchdogConfig({ WATCHDOG_REPEAT_ERROR: "2" })
  const { stop } = feedAll([stepStart(0), compile("boom"), compile("boom")], { config: cfg })
  assert.equal(stop?.reason, "repeated_compiler_error")
})

// ---------------------------------------------------------------------------
// Plumbing: config, normalizers, tailer, stop record
// ---------------------------------------------------------------------------

test("config: defaults are the documented thresholds", () => {
  const cfg = watchdogConfig({})
  assert.deepEqual(
    { repeatTool: cfg.repeatTool, guardDeny: cfg.guardDeny, idleTurns: cfg.idleTurns, repeatError: cfg.repeatError },
    { repeatTool: 5, guardDeny: 3, idleTurns: 8, repeatError: 4 },
  )
  assert.equal(WATCHDOG_DEFAULTS.enabled, true)
  assert.equal(cfg.killGraceMs, 10_000)
})

test("config: WATCHDOG=off disables it, nonsense values fall back to defaults", () => {
  assert.equal(watchdogConfig({ WATCHDOG: "off" }).enabled, false)
  assert.equal(watchdogConfig({}, { enabled: false }).enabled, false)
  assert.equal(watchdogConfig({ WATCHDOG_REPEAT_TOOL: "zero" }).repeatTool, 5)
  assert.equal(watchdogConfig({ WATCHDOG_REPEAT_TOOL: "-3" }).repeatTool, 5)
})

test("errorSignature is path- and position-insensitive", () => {
  assert.equal(
    errorSignature("Problem.lean:12:4: error: unknown identifier 'x'"),
    "error: unknown identifier 'x'",
  )
  assert.equal(errorSignature("no errors here, just prose about error handling"), null)
  assert.equal(errorSignature(""), null)
})

test("resourceKey collapses to the path root, falling back to the tool", () => {
  assert.equal(resourceKey(`${os.homedir()}/lean-4.28-reap/formalpedia/x.lean`, "shell"), "~/lean-4.28-reap/formalpedia")
  assert.equal(resourceKey("cat ./data/T5.jsonl", "shell"), "/data/WSP")
  assert.equal(resourceKey("ls -la", "shell"), "shell")
})

test("tailJsonl reads appended lines once and survives truncation", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pab-wd-"))
  const file = path.join(dir, "agent.jsonl")
  fs.writeFileSync(file, "", "utf8")
  const seen = []
  const t = tailJsonl({ files: [file], onEvent: (ev) => seen.push(ev.type) })
  t.poll()
  fs.appendFileSync(file, `${JSON.stringify(stepStart(0))}\n${JSON.stringify(toolUse("read", { path: "a" }))}\n`)
  t.poll()
  t.poll() // idempotent: nothing new
  assert.deepEqual(seen, ["step_start", "tool_use"])
  fs.writeFileSync(file, `${JSON.stringify(stepFinish(7, 0))}\n`, "utf8") // truncated + rewritten
  t.poll()
  assert.deepEqual(seen, ["step_start", "tool_use", "step_finish"])
  fs.rmSync(dir, { recursive: true, force: true })
})

test("tailJsonl maps guard.log lines to deny events", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pab-wd-"))
  const file = path.join(dir, "guard.log")
  fs.writeFileSync(file, `${JSON.stringify({ hook: "permission.evaluate", tool: "shell", resource: "/x", decision: "deny" })}\n`, "utf8")
  const seen = []
  const t = tailJsonl({ files: [file], onEvent: (ev) => seen.push(ev) })
  t.poll()
  assert.equal(seen[0].type, "guard")
  assert.equal(seen[0].decision, "deny")
  assert.equal(parseWatchdogLine("{not json"), null)
  fs.rmSync(dir, { recursive: true, force: true })
})

test("stop record is frozen after the first decision and carries reason/turn/elapsed", () => {
  const wd = createWatchdog({ taskDir: null, statMtime: () => 0 })
  const call = () => toolUse("read", { path: "Problem.lean" })
  let stop = null
  for (let i = 0; i < 9; i++) stop = wd.feed(call()) ?? stop
  assert.equal(stop.reason, "repeated_tool_call")
  assert.deepEqual(wd.feed(stepStart(0)), stop, "later events must not rewrite the stop record")
  assert.equal(wd.snapshot().stopped, true)
})

test("dirMaxMtime ignores build/vcs trees", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pab-mtime-"))
  fs.writeFileSync(path.join(dir, "Problem.lean"), "x")
  fs.mkdirSync(path.join(dir, ".lake"))
  fs.writeFileSync(path.join(dir, ".lake", "junk"), "x")
  const base = dirMaxMtime(dir)
  assert.ok(base > 0)
  const future = new Date(Date.now() + 60_000)
  fs.utimesSync(path.join(dir, ".lake", "junk"), future, future)
  assert.equal(dirMaxMtime(dir), base, ".lake must not count as progress")
  fs.rmSync(dir, { recursive: true, force: true })
})
