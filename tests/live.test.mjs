#!/usr/bin/env node
/**
 * Live watchdog test: a real subprocess, a real SIGTERM, a real launch.json.
 *
 * The stub below stands in for `opencode run --format json`: it emits five
 * identical tool calls and then hangs. `launchTask` must notice, kill the
 * process group, record `early_stop: {reason, turn, elapsed}` and leave the run
 * directory intact.
 */

import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import test from "node:test"

import { PATHS, launchTask } from "../core.mjs"

const STUB = `#!/bin/bash
for i in 1 2 3 4 5 6; do
  printf '%s\\n' '{"type":"step_start","timestamp":1,"part":{"messageID":"m1"}}'
  printf '%s\\n' '{"type":"tool_use","part":{"tool":"shell","state":{"status":"completed","input":{"command":"grep -rn constantsTower ~"},"output":""}}}'
done
exec sleep 60
`

test("watchdog kills a live session on rule 1 and keeps the run dir", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "pab-live-"))
  const runDir = path.join(root, "pab-live")
  const id = "t5-stub"
  const envDir = path.join(runDir, id)
  fs.mkdirSync(path.join(envDir, "repo"), { recursive: true })
  fs.writeFileSync(path.join(envDir, "repo", "Problem.lean"), "theorem solution : True := by\n  trivial\n")

  const stub = path.join(root, "fake-opencode")
  fs.writeFileSync(stub, STUB, { mode: 0o755 })
  const realOpencode = PATHS.opencode
  PATHS.opencode = stub

  const started = Date.now()
  let res
  try {
    res = await launchTask({
      runDir,
      task: { id, tier: "T5", imports: ["Mathlib"] },
      timeoutS: 40, // the watchdog must beat the wall clock by a wide margin
      briefMode: "default",
      watchdog: { repeatTool: 5, pollMs: 50, killGraceMs: 500 },
    })
  } finally {
    PATHS.opencode = realOpencode
  }
  const took = (Date.now() - started) / 1000

  assert.equal(res.early_stop?.reason, "repeated_tool_call", `got ${JSON.stringify(res.early_stop)}`)
  // the tailer drains the whole buffer, so the turn counter is at least 1
  assert.ok(res.early_stop.turn >= 1 && res.early_stop.turn <= 6, `turn=${res.early_stop.turn}`)
  assert.equal(typeof res.early_stop.elapsed, "number")
  assert.deepEqual(Object.keys(res.early_stop).sort(), ["elapsed", "reason", "turn"])
  assert.equal(res.timed_out, false, "the watchdog, not the wall clock, ended the run")
  assert.ok(took < 20, `expected an early kill, took ${took}s`)

  // the run dir survives: transcript, launch record, project, watchdog log
  assert.ok(fs.existsSync(path.join(envDir, "agent.jsonl")))
  assert.ok(fs.readFileSync(path.join(envDir, "agent.jsonl"), "utf8").includes('"tool_use"'))
  assert.ok(fs.existsSync(path.join(envDir, "repo", "Problem.lean")))
  const launch = JSON.parse(fs.readFileSync(path.join(envDir, "launch.json"), "utf8"))
  assert.equal(launch.early_stop.reason, "repeated_tool_call")
  assert.equal(launch.watchdog.repeatTool, 5)
  const wdLog = fs.readFileSync(path.join(envDir, "watchdog.jsonl"), "utf8").trim().split("\n")
  assert.equal(JSON.parse(wdLog[0]).event, "early_stop")

  fs.rmSync(root, { recursive: true, force: true })
})

test("watchdog off: the same stub runs to the wall clock", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "pab-live-"))
  const runDir = path.join(root, "pab-live")
  const id = "t5-stub"
  const envDir = path.join(runDir, id)
  fs.mkdirSync(path.join(envDir, "repo"), { recursive: true })
  const stub = path.join(root, "fake-opencode")
  fs.writeFileSync(stub, "#!/bin/bash\nexit 0\n", { mode: 0o755 })
  const realOpencode = PATHS.opencode
  PATHS.opencode = stub
  let res
  try {
    res = await launchTask({
      runDir,
      task: { id, tier: "T5", imports: ["Mathlib"] },
      timeoutS: 10,
      watchdog: { enabled: false },
    })
  } finally {
    PATHS.opencode = realOpencode
  }
  assert.equal(res.early_stop, null)
  assert.equal(res.code, 0)
  assert.equal(res.watchdog.enabled, false)
  fs.rmSync(root, { recursive: true, force: true })
})
