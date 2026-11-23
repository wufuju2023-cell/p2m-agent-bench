#!/usr/bin/env node
/**
 * Unit tests for the p2m-agent-bench sub-mission contract.
 *
 * A child mission that says "locate the original source/proof" is unprovable and
 * used to die on guard-denied reads, so `pab_split` now requires four fields and
 * returns a ready-to-paste `subagent` prompt for each accepted mission.
 *
 *   node --test tests/
 */

import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import test from "node:test"

import {
  MISSION_FIELDS,
  MISSION_FORBIDDEN,
  childPrompt,
  dispatchFor,
  findSourceHunt,
  missionMarkdown,
  missionObjective,
  scrubProhibitions,
  validateMissionContract,
  writeMissions,
} from "../core.mjs"

const PROJECT = "./eval/runs/pab-x/t5-problem/repo"

function goodMission(overrides = {}) {
  return {
    goal_statement:
      "{n : ℕ} (xs fs : Fin (n + 1) → ℝ) → Function.Injective xs → ∃ p : Polynomial ℝ, p.degree ≤ n ∧ ∀ i, p.eval (xs i) = fs i",
    lean_context:
      "section · variable {n : ℕ} · xs fs : Fin (n+1) → ℝ · h : Function.Injective xs · open Polynomial Finset · imports Mathlib",
    imports: ["Mathlib"],
    acceptance: `cd ${PROJECT} && lake env lean missions/01-existence.lean`,
    ...overrides,
  }
}

// ---------------------------------------------------------------------------
// Accepting a well-formed mission
// ---------------------------------------------------------------------------

test("contract: accepts a mission carrying all four fields", () => {
  const v = validateMissionContract(goodMission())
  assert.equal(v.ok, true, v.errors.join("; "))
  assert.deepEqual(MISSION_FIELDS, ["goal_statement", "lean_context", "imports", "acceptance"])
  assert.deepEqual(v.normalized.forbidden, MISSION_FORBIDDEN, "forbidden is stamped when absent")
})

test("contract: accepts a goal that only uses → (no colon)", () => {
  const v = validateMissionContract(goodMission({ goal_statement: "Nat.Prime n → n ≥ 2" }))
  assert.equal(v.ok, true, v.errors.join("; "))
})

test("contract: keeps an explicit forbidden list", () => {
  const v = validateMissionContract(goodMission({ forbidden: ["read Solutions/", "ask the parent"] }))
  assert.equal(v.ok, true)
  assert.deepEqual(v.normalized.forbidden, ["read Solutions/", "ask the parent"])
})

test("contract: accepts a hint and normalizes whitespace", () => {
  const v = validateMissionContract(
    goodMission({ hint: "  use Lagrange.interpolate  ", goal_statement: "{n : ℕ} : n + 0 = n" }),
  )
  assert.equal(v.ok, true, v.errors.join("; "))
  assert.equal(v.normalized.hint, "use Lagrange.interpolate")
})

// ---------------------------------------------------------------------------
// Rejecting an incomplete mission (one test per hard-required field)
// ---------------------------------------------------------------------------

for (const field of MISSION_FIELDS) {
  test(`contract: rejects a mission missing ${field}`, () => {
    const m = goodMission()
    delete m[field]
    const v = validateMissionContract(m)
    assert.equal(v.ok, false)
    assert.ok(
      v.errors.some((e) => e.includes(field)),
      `expected an error mentioning ${field}, got: ${v.errors.join(" | ")}`,
    )
  })
}

test("contract: rejects an empty imports array", () => {
  const v = validateMissionContract(goodMission({ imports: [] }))
  assert.equal(v.ok, false)
  assert.ok(v.errors.some((e) => /imports is empty/.test(e)))
})

test("contract: rejects imports outside the parent's Problem.lean", () => {
  const v = validateMissionContract(goodMission({ imports: ["Mathlib", "Mathlib.RingTheory.Foo"] }), {
    allowedImports: ["Mathlib"],
  })
  assert.equal(v.ok, false)
  assert.ok(v.errors.some((e) => /not allowed/.test(e)))
})

test("contract: rejects a goal that is prose, not a Lean type", () => {
  const v = validateMissionContract(goodMission({ goal_statement: "Understand what the theorem needs" }))
  assert.equal(v.ok, false)
  assert.ok(v.errors.some((e) => /does not look like a Lean type/.test(e)))
})

test("contract: rejects an acceptance that is not `cd … && lake env lean …`", () => {
  for (const acceptance of [
    "lake env lean Problem.lean",
    "cd repo; lake env lean Problem.lean",
    "lake build",
    "cd /tmp/x && lake build",
    "cd /tmp/x && lean Problem.lean",
    "",
  ]) {
    const v = validateMissionContract(goodMission({ acceptance }))
    assert.equal(v.ok, false, `should reject acceptance ${JSON.stringify(acceptance)}`)
  }
})

test("contract: rejects a short lean_context", () => {
  const v = validateMissionContract(goodMission({ lean_context: "Mathlib" }))
  assert.equal(v.ok, false)
  assert.ok(v.errors.some((e) => /lean_context too short/.test(e)))
})

// ---------------------------------------------------------------------------
// Rejecting "go find the source" instructions
// ---------------------------------------------------------------------------

const HUNTS = [
  { field: "goal_statement", text: "Locate the original source/proof of `exists_constantsTower_of_totallyRamified_of_isIntegral` and report file:line." },
  { field: "goal_statement", text: "Find the reference proof for this theorem: `foo : True`" },
  { field: "lean_context", text: "Variables as in Mathlib · search prove2me/formalpedia for the statement · open Foo" },
  { field: "lean_context", text: "grep -rn constantsTower ~/lean-4.28-reap/formalpedia/envs · h : P" },
  { field: "hint", text: "just read Solutions/Sol_0001.lean and copy it" },
  { field: "hint", text: "find any equivalent lemma in the bank and restate it" },
  { field: "note", text: "the theorem likely comes from a newer Mathlib — where does this theorem come from?" },
]

for (const { field, text } of HUNTS) {
  test(`contract: rejects a source hunt in ${field}: ${text.slice(0, 42)}…`, () => {
    const v = validateMissionContract(goodMission({ [field]: text }))
    assert.equal(v.ok, false)
    assert.ok(
      v.errors.some((e) => /source hunt/.test(e)),
      `expected a source-hunt error, got: ${v.errors.join(" | ")}`,
    )
  })
}

test("contract: the forbidden stamp itself is not a source hunt (no false positive)", () => {
  assert.deepEqual(findSourceHunt(`forbidden: [${MISSION_FORBIDDEN.map((f) => JSON.stringify(f)).join(", ")}]`), [])
  assert.ok(findSourceHunt("forbidden: []\nplease locate the source proof").length > 0)
  assert.equal(validateMissionContract(goodMission()).ok, true)
})

test("contract: a clean mission has no source hunt", () => {
  assert.deepEqual(findSourceHunt(goodMission().lean_context), [])
})

// ---------------------------------------------------------------------------
// Child dispatch: prompt + objective
// ---------------------------------------------------------------------------

test("dispatch: objective is exactly `prove <mission_id>: <goal_statement>`", () => {
  const m = validateMissionContract(goodMission()).normalized
  const objective = missionObjective("problem/01-existence", m)
  assert.equal(objective, `prove problem/01-existence: ${m.goal_statement.replace(/\s+/g, " ")}`)
})

test("dispatch: the subagent prompt embeds all four fields verbatim", () => {
  const m = validateMissionContract(goodMission()).normalized
  const prompt = childPrompt({ missionId: "problem/01-existence", mission: m, projectDir: PROJECT })
  assert.ok(prompt.includes(m.goal_statement), "goal_statement verbatim")
  assert.ok(prompt.includes(m.lean_context), "lean_context verbatim")
  assert.ok(prompt.includes("imports: [Mathlib]"), "imports verbatim")
  assert.ok(prompt.includes(m.acceptance), "acceptance verbatim")
  assert.ok(prompt.includes('"locate the source proof"'), "forbidden stamp present")
  assert.ok(prompt.includes(`goal({action: "set", objective: "prove problem/01-existence: ${m.goal_statement}`), "goal objective")
  assert.ok(prompt.includes("missions/01-existence.lean"), "target file derived from acceptance")
  assert.ok(/Do not look for, grep for, or read the original source/.test(prompt))
})

test("dispatch: every field the validator requires is also required in the prompt", () => {
  const m = validateMissionContract(goodMission()).normalized
  const prompt = childPrompt({ missionId: "p/01", mission: m, projectDir: PROJECT })
  for (const field of MISSION_FIELDS) {
    assert.ok(new RegExp(`^${field}\\s*:`, "m").test(prompt), `prompt carries a ${field}: line`)
  }
})

test("dispatch: the dispatch object carries a ready-to-use subagent call", () => {
  const m = validateMissionContract(goodMission()).normalized
  const d = dispatchFor("problem/01-existence", m, PROJECT)
  assert.equal(d.objective, missionObjective("problem/01-existence", m))
  assert.equal(d.subagent.agent, "general")
  assert.ok(d.subagent.description.length <= 60)
  assert.equal(d.subagent.prompt, childPrompt({ missionId: "problem/01-existence", mission: m, projectDir: PROJECT }))
  assert.equal(d.team_send.to, "children")
})

// ---------------------------------------------------------------------------
// writeMissions: end-to-end on a fake run dir (no env build, no lake)
// ---------------------------------------------------------------------------

function fakeRun() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "pab-contract-"))
  const runId = "pab-test"
  const id = "t5-problem"
  const dir = path.join(root, runId) // loadRun resolves <runRoot>/<runId>/run.json
  const repo = path.join(dir, id, "repo")
  fs.mkdirSync(repo, { recursive: true })
  fs.writeFileSync(path.join(repo, "Problem.lean"), "import Mathlib\n\ntheorem solution : True := by\n  -- TODO\n  trivial\n")
  fs.writeFileSync(
    path.join(dir, "run.json"),
    JSON.stringify({
      run_id: runId,
      model: "opencode-go/deepseek-v4.1-flash#max",
      tasks: [{ id, tier: "T5", imports: ["Mathlib"], status: "running", repo }],
    }),
  )
  return { root, dir, runId, id, repo }
}

test("writeMissions: accepts a good mission, writes it, and returns a dispatch prompt", () => {
  const { root, runId, id, repo } = fakeRun()
  const res = writeMissions({ runId, id, subtasks: [goodMission()], runRoot: root })
  assert.equal(res.ok, true)
  assert.equal(res.count, 1)
  assert.deepEqual(res.rejected, [])
  const mission = res.dispatch[0]
  assert.ok(mission.mission_id.startsWith(`${id}/01-`))
  assert.ok(mission.subagent.prompt.includes(goodMission().goal_statement))
  assert.ok(mission.subagent.prompt.includes(goodMission().acceptance))
  assert.ok(fs.existsSync(path.join(repo, res.written[0])), "mission file exists")
  const md = fs.readFileSync(path.join(repo, res.written[0]), "utf8")
  assert.ok(/goal_statement\s*:/.test(md) && /acceptance\s*:/.test(md), "mission file carries the contract")
  assert.deepEqual(res.required_fields, MISSION_FIELDS)
  fs.rmSync(root, { recursive: true, force: true })
})

test("writeMissions: rejects a missing field and a source hunt, writing nothing", () => {
  const { root, runId, id, repo } = fakeRun()
  const bad1 = goodMission()
  delete bad1.lean_context
  const bad2 = goodMission({ goal_statement: "Locate the original source proof of `solution` : True" })
  const res = writeMissions({ runId, id, subtasks: [bad1, bad2], runRoot: root })
  assert.equal(res.ok, false)
  assert.equal(res.count, 0)
  assert.equal(res.rejected.length, 2)
  assert.ok(res.rejected[0].errors.some((e) => e.includes("lean_context")))
  assert.ok(res.rejected[1].errors.some((e) => /source hunt/.test(e)))
  assert.equal(fs.readdirSync(path.join(repo, "missions")).length, 0, "nothing is written for rejected missions")
  assert.match(res.next_step, /rejected/i)
  fs.rmSync(root, { recursive: true, force: true })
})

test("writeMissions: a mixed batch keeps the good mission and reports the bad one", () => {
  const { root, runId, id, repo } = fakeRun()
  const res = writeMissions({
    runId,
    id,
    subtasks: [goodMission(), goodMission({ imports: ["Mathlib.RingTheory.Foo"] })],
    runRoot: root,
  })
  assert.equal(res.ok, false)
  assert.equal(res.count, 1)
  assert.equal(res.rejected.length, 1)
  assert.equal(fs.readdirSync(path.join(repo, "missions")).length, 1)
  fs.rmSync(root, { recursive: true, force: true })
})

test("missionMarkdown: renders the contract block and the objective", () => {
  const m = validateMissionContract(goodMission()).normalized
  const md = missionMarkdown({ missionId: "p/01", mission: m })
  for (const field of MISSION_FIELDS) assert.ok(new RegExp(`${field}\\s*:`).test(md), `${field} in markdown`)
  assert.ok(md.includes(`prove p/01: ${m.goal_statement.replace(/\s+/g, " ")}`))
})

test("audit: a prohibition section is not a source hunt", () => {
  const m = validateMissionContract(goodMission()).normalized
  const prompt = childPrompt({ missionId: "p/01", mission: m, projectDir: PROJECT })
  assert.deepEqual(findSourceHunt(prompt), [], "the generated prompt must audit clean")
})

test("audit: a parent-authored prohibition is forgiven, an instruction is not", () => {
  assert.deepEqual(findSourceHunt("## Forbidden\nDo not look for, grep for, or read the original source/proof.\n## Next"), [])
  assert.deepEqual(findSourceHunt("Please grep for the original proof in the oracle"), ["search the original proof"])
})

test("leaks: the harness's own forbidden stamp is not contamination", () => {
  const splitInput = {
    subtasks: [
      {
        goal_statement: "∀ x, f x = x",
        lean_context: "f : ℝ → ℝ",
        imports: ["Mathlib"],
        acceptance: `cd ${PROJECT} && lake env lean missions/01.lean`,
        forbidden: MISSION_FORBIDDEN,
      },
    ],
  }
  const scrubbed = JSON.stringify(scrubProhibitions(splitInput))
  assert.ok(!/formalpedia|Solutions\//.test(scrubbed), "the stamp must be scrubbed")
  // …while a real read of the oracle survives the scrub and stays a leak.
  const real = JSON.stringify(scrubProhibitions({ command: `head -c 3000 ${PROJECT}/../../../formalpedia/envs/0df444a/Solutions/Sol_x.lean` }))
  assert.ok(/formalpedia/.test(real) && /Solutions\//.test(real))
})
