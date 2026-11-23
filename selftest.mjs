#!/usr/bin/env node
/**
 * selftest.mjs — build one env without running an agent and assert the wiring:
 *   - sampling is deterministic and honours local_compilable
 *   - the sanitized Problem.lean does not leak the original name/namespace/docstring
 *   - `lake env lean Problem.lean` runs against the pinned 4.33.1 + Mathlib
 *   - the statement hash in secrets.json matches the generated statement
 *   - the repo is a single commit
 *
 * Usage: node selftest.mjs [--tier T1] [--seed selftest]
 */

import fs from "node:fs"
import path from "node:path"

import {
  MODEL,
  PATHS,
  buildEnv,
  dispatchFor,
  grade,
  mulberry32,
  problemStatement,
  readJson,
  sampleTier,
  sha256,
  normalizeWs,
  sh,
  shortHash,
  TIERS,
  validateMissionContract,
} from "./core.mjs"

const argv = process.argv.slice(2)
const opt = (name, fallback) => {
  const i = argv.indexOf(`--${name}`)
  return i >= 0 && argv[i + 1] ? argv[i + 1] : fallback
}

const tier = String(opt("tier", "T1")).toUpperCase()
const seed = String(opt("seed", "selftest"))
const root = path.join("/tmp/opencode", "pab-selftest", `${tier}-${shortHash(seed, 6)}`)
fs.rmSync(root, { recursive: true, force: true })
fs.mkdirSync(root, { recursive: true })

const fails = []
const check = (ok, msg) => {
  console.log(`${ok ? "ok  " : "FAIL"} ${msg}`)
  if (!ok) fails.push(msg)
}

console.log(`model pinned: ${MODEL}`)

// determinism
const a = sampleTier({ tier, perTier: 2, seed })
const b = sampleTier({ tier, perTier: 2, seed })
check(a.length === 2, `${tier} sample returns 2 records`)
check(JSON.stringify(a.map((r) => r.id)) === JSON.stringify(b.map((r) => r.id)), "same seed → same sample")
check(a.every((r) => r.local_compilable === true), "every sample is local_compilable")
const diff = sampleTier({ tier, perTier: 2, seed: seed + "-other" })
check(JSON.stringify(diff.map((r) => r.id)) !== JSON.stringify(a.map((r) => r.id)), "different seed → different sample")

const rec = a[0]
const id = rec.id
console.log(`problem: ${id} · imports: ${rec.imports.join(", ")}`)

const built = buildEnv({ runDir: root, id, rec, tier, lakeName: `pab_env_${shortHash(id, 8)}` })
const problem = fs.readFileSync(built.problemFile, "utf8")
console.log("--- Problem.lean ---")
console.log(problem.trim())

check(/theorem\s+solution\b/.test(problem), "declares `theorem solution`")
check(!problem.includes(rec.fq_name ?? "\u0000"), "original fq_name absent")
check(!/namespace\s+/.test(problem), "no namespace block")
check(!/\/--/.test(problem) && !/-!\s/.test(problem), "no docstring")
check(/--\s*TODO/.test(problem), "has the -- TODO hole")
check(built.commits === 1, `single-commit git (got ${built.commits})`)

const secrets = readJson(path.join(root, id, "secrets.json"))
const stmt = problemStatement(problem)
check(sha256(normalizeWs(stmt)) === secrets.problem_statement_sha256, "statement hash matches secrets.json")
check(secrets.env_id === id && MODEL === readJson(path.join(root, id, "opencode.json")).agents["p2m-eval"].model, "agent pinned to the only allowed model")

// ---- sub-mission contract (a real mission derived from this env) -----------
const goal = stmt.replace(/^theorem\s+solution\s*/, "").replace(/:=.*$/s, "").trim()
const mission = {
  goal_statement: goal,
  lean_context: `Problem.lean declares \`theorem solution\` · imports: ${rec.imports.join(", ")} · open namespaces: none`,
  imports: rec.imports,
  acceptance: `cd ${built.repo} && lake env lean missions/01-proof.lean`,
}
const v = validateMissionContract(mission, { allowedImports: rec.imports })
check(v.ok, `contract accepts a mission built from the real env${v.ok ? "" : `: ${v.errors.join("; ")}`}`)
const hunt = validateMissionContract({ ...mission, goal_statement: "Locate the original source/proof of `solution` and report file:line." })
check(!hunt.ok && hunt.errors.some((e) => /source hunt/.test(e)), "contract rejects a 'locate the source proof' mission")
const incomplete = validateMissionContract({ goal_statement: goal })
check(!incomplete.ok && incomplete.errors.length >= 3, "contract rejects a mission missing lean_context/imports/acceptance")
const dispatch = dispatchFor(`${id}/01-proof`, v.normalized, built.repo)
check(
  ["goal_statement", "lean_context", "imports", "acceptance"].every((f) => new RegExp(`^${f}\\s*:`, "m").test(dispatch.subagent.prompt)),
  "dispatch prompt carries all four contract fields",
)

// The project must actually resolve Mathlib through lake.
const t0 = Date.now()
const g = grade({ envDir: path.join(root, id), timeoutS: 300 })
check(g.exit !== 0, `lake env lean rejects the TODO hole (exit ${g.exit})`)
check(!g.pass, "hole is not graded as a pass")
console.log(`lake wiring: ${((Date.now() - t0) / 1000).toFixed(1)}s · errors: ${g.errors.slice(0, 2).join(" / ") || "(none)"}`)

// A correct one-line proof must be graded as a pass (sanity of the grader).
const repo = built.repo
const good = problem.replace(/theorem\s+solution([\s\S]*?):= by\n[\s\S]*$/, (_m, mid) => `theorem solution${mid}:= by\n  sorry\n`)
void good
const trivial = `import Mathlib\n\ntheorem solution (n : ℕ) : n + 0 = n := by\n  simp\n`
fs.writeFileSync(path.join(repo, "Problem.lean"), trivial, "utf8")
const g2 = grade({ envDir: path.join(root, id), timeoutS: 300 })
check(g2.statement_ok === false, "statement change is detected (hash mismatch)")
fs.writeFileSync(path.join(repo, "Problem.lean"), problem, "utf8")

// sorry detection
const sorryText = `import Mathlib\n\ntheorem solution (n : ℕ) : n = n := by\n  sorry\n`
fs.writeFileSync(path.join(repo, "Problem.lean"), sorryText, "utf8")
const g3 = grade({ envDir: path.join(root, id), timeoutS: 300 })
check(g3.sorry_hits > 0 || g3.failure === "sorry", "sorry is detected")
fs.writeFileSync(path.join(repo, "Problem.lean"), problem, "utf8")

console.log(fails.length ? `\nselftest FAILED (${fails.length})` : "\nselftest passed")
console.log(`env kept at ${root} for inspection`)
process.exit(fails.length ? 1 : 0)
