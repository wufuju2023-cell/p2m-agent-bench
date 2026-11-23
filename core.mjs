/**
 * p2m-agent-bench — core engine (plain ESM, node stdlib only).
 *
 * The "agent-vs-prove2me" harness: sample blind Lean problems from the local
 * bank, materialise one sandboxed OpenCode project per problem, launch a
 * free-form agent (no MCTS / no value head), then grade the result with
 * `lake env lean Problem.lean` + no-`sorry` + statement-unchanged.
 *
 * Everything is deterministic given (bank, seed, run_id): the same seed samples
 * the same problems. No network calls are made here; the only subprocesses are
 * python3 (reusing guard/l0l1/make_env.py), git, lake and opencode.
 */

import crypto from "node:crypto"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { createRequire } from "node:module"
import { spawn, spawnSync } from "node:child_process"

// ---------------------------------------------------------------------------
// Constants / defaults
// ---------------------------------------------------------------------------

/** The ONLY model this harness may invoke. Asserted on every launch. */
export const MODEL = "opencode-go/deepseek-v4.1-flash#max"

export const PATHS = {
  bank: "./data/bank_local",
  runRoot: "./eval/runs",
  guard: "./guard/guard.json",
  makeEnv: "./guard/l0l1/make_env.py",
  perms: "./guard/l0l1/permissions.json",
  leanProject: "~/lean-4.28-reap/env-0df444a",
  mathlib: "~/lean-4.28-reap/mathlib4-0df444a",
  opencode: "~/.opencode2/bin/opencode",
  elan: "~/.elan/bin",
  // OpenCode v2 session store (child sessions live here, not in agent.jsonl).
  db: path.join(os.homedir(), ".opencode2", "share", "opencode", "opencode.db"),
}

export const TIERS = ["T1", "T2", "T3", "T4", "T5"]
export const DEFAULT_TIMEOUT_S = 600
export const AGENT_ID = "p2m-eval"

// ---------------------------------------------------------------------------
// Small utilities
// ---------------------------------------------------------------------------

export function sha256(text) {
  return crypto.createHash("sha256").update(text, "utf8").digest("hex")
}

export function shortHash(text, n = 8) {
  return sha256(text).slice(0, n)
}

export function normalizeWs(text) {
  return String(text ?? "").replace(/\s+/g, " ").trim()
}

export function readJson(file) {
  return JSON.parse(fs.readFileSync(file, "utf8"))
}

export function writeJson(file, obj, mode = 0o644) {
  fs.mkdirSync(path.dirname(file), { recursive: true })
  fs.writeFileSync(file, JSON.stringify(obj, null, 2) + "\n", "utf8")
  fs.chmodSync(file, mode)
}

export function appendJsonl(file, obj) {
  fs.mkdirSync(path.dirname(file), { recursive: true })
  fs.appendFileSync(file, JSON.stringify(obj) + "\n", "utf8")
}

export function exists(file) {
  try {
    fs.accessSync(file)
    return true
  } catch {
    return false
  }
}

export function safeName(value) {
  return String(value ?? "")
    .replace(/[^A-Za-z0-9._-]+/g, "_")
    .replace(/^[._]+/, "_")
    .slice(0, 80)
}

/** Deterministic PRNG (mulberry32). */
export function mulberry32(seed) {
  let a = seed >>> 0
  return function next() {
    a = (a + 0x6d2b79f5) | 0
    let t = Math.imul(a ^ (a >>> 15), 1 | a)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

export function seedFrom(seed, tier) {
  const text = `${seed}:${tier}`
  return parseInt(sha256(text).slice(0, 8), 16) >>> 0
}

/** Fixed git identity/dates so every env is byte-stable and one-commit. */
const GIT_DATE = "2026-01-01T00:00:00+0000"
export const GIT_ENV = {
  GIT_AUTHOR_NAME: "p2m",
  GIT_AUTHOR_EMAIL: "p2m@localhost",
  GIT_COMMITTER_NAME: "p2m",
  GIT_COMMITTER_EMAIL: "p2m@localhost",
  GIT_AUTHOR_DATE: GIT_DATE,
  GIT_COMMITTER_DATE: GIT_DATE,
  GIT_CONFIG_NOSYSTEM: "1",
}

export function sh(cmd, args, opts = {}) {
  const res = spawnSync(cmd, args, {
    encoding: "utf8",
    maxBuffer: 256 * 1024 * 1024,
    ...opts,
    env: { ...process.env, ...(opts.env ?? {}) },
  })
  return {
    code: res.status ?? -1,
    signal: res.signal ?? null,
    stdout: res.stdout ?? "",
    stderr: res.stderr ?? "",
  }
}

// ---------------------------------------------------------------------------
// Bank sampling
// ---------------------------------------------------------------------------

/** A record is usable iff it claims local compilability and has a declaration. */
export function usable(rec) {
  if (!rec || rec.local_compilable !== true) return false
  const stmt = String(rec.statement_formal ?? "")
  if (!stmt.trim()) return false
  if (!/\b(theorem|lemma)\s+[^\s(\[{:]+/.test(stmt)) return false
  if (!Array.isArray(rec.imports) || rec.imports.length === 0) return false
  if (!stmt.includes(":")) return false
  return true
}

/**
 * Seeded reservoir sample of `perTier` records from one tier shard.
 * Deterministic: the same (seed, tier) yields the same set.
 */
export function sampleTier({ tier, perTier = 2, seed = "pab-1", bankDir = PATHS.bank }) {
  const shard = path.join(bankDir, `${tier}.jsonl`)
  if (!exists(shard)) throw new Error(`missing bank shard: ${shard}`)
  const rnd = mulberry32(seedFrom(seed, tier))
  const picked = []
  let seen = 0
  const fd = fs.openSync(shard, "r")
  try {
    // Stream line by line without loading the 61 MB T1 shard as one string.
    const buf = Buffer.alloc(4 * 1024 * 1024)
    let rest = ""
    let carry = ""
    while (true) {
      const n = fs.readSync(fd, buf, 0, buf.length, null)
      if (n <= 0) break
      const chunk = carry + buf.toString("utf8", 0, n)
      const lines = chunk.split("\n")
      carry = lines.pop() ?? ""
      for (const line of lines) {
        if (!line) continue
        if (!line.includes('"local_compilable": true')) continue
        let rec
        try {
          rec = JSON.parse(line)
        } catch {
          continue
        }
        if (!usable(rec)) continue
        seen += 1
        if (picked.length < perTier) picked.push(rec)
        else {
          const j = Math.floor(rnd() * seen)
          if (j < perTier) picked[j] = rec
        }
      }
      rest = carry
    }
    if (carry && carry.includes('"local_compilable": true')) {
      try {
        const rec = JSON.parse(carry)
        if (usable(rec)) {
          seen += 1
          if (picked.length < perTier) picked.push(rec)
          else {
            const j = Math.floor(rnd() * seen)
            if (j < perTier) picked[j] = rec
          }
        }
      } catch {
        /* ignore trailing partial line */
      }
    }
    void rest
  } finally {
    fs.closeSync(fd)
  }
  return picked
}

// ---------------------------------------------------------------------------
// Env materialisation (reuses guard/l0l1/make_env.py — read, do not fork)
// ---------------------------------------------------------------------------

/**
 * Build one blind env:
 *   <run>/<id>/repo/{Problem.lean,README.md,.git}
 *   <run>/<id>/{opencode.json,.opencode.json,secrets.json,env.json}
 * plus the lake wiring needed to compile in place (lakefile + toolchain +
 * manifest + .lake/packages symlinks to the prebuilt mathlib checkout).
 */
export function buildEnv({ runDir, id, rec, tier, lakeName }) {
  const envDir = path.join(runDir, id)
  const shimDir = path.join(runDir, ".shim", id)
  fs.mkdirSync(shimDir, { recursive: true })

  // make_env.py looks records up by `bench_id`; the raw bank has `id`/`fq_name`
  // instead, so hand it a one-record shard with a stable, opaque bench_id.
  const benchId = `pab-${shortHash(rec.id ?? rec.theorem_id ?? id)}`
  const shim = {
    bench_id: benchId,
    tier,
    statement_formal: rec.statement_formal,
    statement_nl: rec.statement_nl ?? "",
    imports: rec.imports,
  }
  const shard = path.join(shimDir, `${tier}.jsonl`)
  fs.writeFileSync(shard, JSON.stringify(shim) + "\n", "utf8")

  const res = sh(PATHS.makeEnv === "" ? "python3" : "python3", [
    PATHS.makeEnv,
    "--bench-id", benchId,
    "--out", envDir,
    "--tier", tier,
    "--bank-dir", shimDir,
    "--project", PATHS.leanProject,
    "--force",
  ], { env: { P2M_AGENT_MODEL: MODEL } })
  fs.rmSync(shimDir, { recursive: true, force: true })
  if (res.code !== 0) {
    throw new Error(`make_env failed for ${id}: ${res.stderr.trim() || res.stdout.trim()}`)
  }

  const repo = path.join(envDir, "repo")
  const problemFile = path.join(repo, "Problem.lean")
  const problem = fs.readFileSync(problemFile, "utf8")

  // ---- lake wiring: a private project that path-requires the shared mathlib --
  fs.writeFileSync(path.join(repo, "lean-toolchain"), "leanprover/lean4:v4.33.1\n", "utf8")
  fs.writeFileSync(
    path.join(repo, "lakefile.toml"),
    `name = "${lakeName}"\nversion = "0.1.0"\n\n[[require]]\nname = "mathlib"\npath = "${PATHS.mathlib}"\n`,
    "utf8",
  )
  const manifest = readJson(path.join(PATHS.leanProject, "lake-manifest.json"))
  for (const pkg of manifest.packages ?? []) {
    if (pkg?.name === "mathlib") pkg.dir = PATHS.mathlib
  }
  writeJson(path.join(repo, "lake-manifest.json"), manifest)

  // Point lake at the already-built dependency trees: no clone, no rebuild.
  const pkgSrc = path.join(PATHS.leanProject, ".lake", "packages")
  const pkgDst = path.join(repo, ".lake", "packages")
  fs.mkdirSync(pkgDst, { recursive: true })
  for (const name of fs.readdirSync(pkgSrc)) {
    const link = path.join(pkgDst, name)
    if (!exists(link)) fs.symlinkSync(path.join(pkgSrc, name), link)
  }
  fs.writeFileSync(path.join(repo, ".gitignore"), ".lake/\ntoolchains/\nsettings.toml\nknown-projects/\ntmp/\n", "utf8")

  patchEnvConfig(envDir)


  // ---- grading fingerprint: hash of the sanitized statement -----------------
  const stmt = problemStatement(problem)
  if (!stmt) throw new Error(`could not extract the statement from ${problemFile}`)
  const secretsFile = path.join(envDir, "secrets.json")
  const secrets = readJson(secretsFile)
  secrets.env_id = id
  secrets.bank_id = rec.id ?? null
  secrets.problem_statement_sha256 = sha256(normalizeWs(stmt))
  secrets.problem_theorem_name = "solution"
  secrets.imports = rec.imports
  writeJson(secretsFile, secrets, 0o600)

  const envJson = readJson(path.join(envDir, "env.json"))
  envJson.env_id = id
  envJson.bank_id = rec.id ?? null
  envJson.fq_name = rec.fq_name ?? rec.id ?? null
  envJson.lean_project = repo
  envJson.model = MODEL
  envJson.timeout_s = DEFAULT_TIMEOUT_S
  writeJson(path.join(envDir, "env.json"), envJson)

  // ---- one commit, including the lake wiring --------------------------------
  const git = (...args) =>
    sh("git", ["-c", "commit.gpgsign=false", ...args], { cwd: repo, env: GIT_ENV })
  git("add", "-A")
  git("commit", "-q", "--amend", "--no-edit")
  const head = git("rev-list", "--count", "HEAD").stdout.trim()

  return {
    envDir,
    repo,
    problemFile,
    imports: rec.imports,
    statement_sha256: secrets.problem_statement_sha256,
    commits: Number(head),
  }
}

/** The theorem-as-written (from `theorem solution` to the `:=` separator). */
export function problemStatement(text) {
  const src = String(text ?? "")
  const i = src.indexOf("theorem solution")
  if (i < 0) return ""
  let tail = src.slice(i)
  const j = tail.indexOf(":=")
  if (j >= 0) tail = tail.slice(0, j)
  return tail.trim()
}

export function agentPolicy() {
  return `You are a Lean 4 proof agent. The project's Problem.lean declares exactly one
theorem, \`solution\`, with a \`-- TODO\` hole. Replace the hole with a complete proof.

Definition of done: \`lake env lean Problem.lean\` exits 0 from the project root,
the file contains no \`sorry\`/\`admit\`, and the statement (name, binders,
hypotheses, conclusion) is unchanged.

Policy, in order:
1. Direct first. Read Problem.lean, compile it, look at the goal, and attack it
   with the usual tactics (\`simp\`, \`omega\`, \`nlinarith\`, \`gcongr\`,
   \`positivity\`, \`field_simp\`/\`ring\`, \`linarith\`, \`aesop\`, \`exact?\`,
   \`apply?\`, \`#check\`). Iterate until it compiles.
2. Local pool first. Prefer an existing Mathlib lemma over re-proving it: probe
   locally with \`#check\`, \`#exact?\`, \`#apply?\`, \`simp?\`, \`#loogle\`-style
   guesses inside Problem.lean (or the lean-lsp MCP tools when they are
   available). Web search is a last resort, not a first move.
3. If stuck, or the problem looks big, split it: write child missions with
   \`pab_split({subtasks:[{goal,hint}]})\` (or \`missions/*.md\` by hand) and
   dispatch them with the \`subagent\` tool (or \`team_send\`). One concrete
   subgoal per child, then assemble the pieces yourself.
4. Web search is allowed as a last resort (Mathlib docs, Lean Zulip). The
   sandbox guard blocks prove2me / formalpedia / github.com/prove2me / arxiv /
   huggingface: do not try to reach them.
5. Never change the statement or the imports, never use \`sorry\`/\`admit\`,
   never touch files outside this project, never rewrite git history.
6. Stop as soon as the file compiles cleanly. Do not keep polishing.
`
}

/** The per-problem task brief handed to the agent (prompt of `opencode run`). */
/** Extra paragraph for the forced-decomposition arm (mechanism validation). */
export function forcedDecompositionBrief() {
  return `
## Mandatory decomposition (overrides the strategy above)

An external estimator says this mission needs **more than 500 steps** — far more
than one agent turn can do. You MUST, before attempting any proof yourself:

1. call \`pab_split({subtasks:[...]})\` with **at least 2** child missions.
   Every subtask is a CONTRACT and all four fields are required:

       goal_statement : <the exact Lean goal/type to prove>
       lean_context   : <variables, hypotheses, open namespaces, imports>
       imports        : ["Mathlib", ...]      # allowed imports only
       acceptance     : cd <project> && lake env lean <file>.lean
       forbidden      : ["locate the source proof", "search prove2me/formalpedia", "read Solutions/"]

   \`pab_split\` **rejects** a subtask that is missing any of those fields, whose
   \`imports\` are not a subset of the imports already in Problem.lean, whose
   \`acceptance\` is not the exact \`cd … && lake env lean …\` command, or whose
   text asks anyone to locate/search for the original source or proof.

2. dispatch each child with the \`subagent\` tool, passing
   \`dispatch[i].subagent.prompt\` **verbatim** — that text already embeds
   goal_statement, lean_context, imports and acceptance, so do not paraphrase
   it, shorten it, or re-derive the task. A child that is told "find the source"
   instead of "prove this goal" is a failed child.

Only after both children have reported may you touch Problem.lean yourself.
If the \`subagent\`/\`team_send\` tool is unavailable, say so explicitly in one
line and then proceed directly — but still write the child missions first.
`
}

export function taskBrief({ tier, imports, forced = false }) {
  const im = (imports ?? []).join(", ")
  return `# Prove \`solution\` in Problem.lean

Lean 4.33.1 + Mathlib (pinned and prebuilt). Project root is this directory.
Imports already in the file: ${im || "Mathlib"}.
Tier hint: ${tier} (T1 = short textbook lemma, T5 = long multi-step argument).

Fill the \`-- TODO\` hole in ./Problem.lean. Verify with:

    lake env lean Problem.lean

Definition of done: that command exits 0, no \`sorry\`/\`admit\` in the file, and
the statement of \`solution\` is byte-for-byte unchanged.

Strategy (follow in order):
1. Direct first: read Problem.lean, compile it, inspect the goal, attack with
   \`simp\` / \`omega\` / \`nlinarith\` / \`gcongr\` / \`positivity\` /
   \`field_simp\`+\`ring\` / \`aesop\` / \`exact?\` / \`apply?\`.
2. Local pool first: look for an existing Mathlib lemma locally (\`#check\`,
   \`exact?\`, \`apply?\`, \`simp?\`, lean-lsp MCP tools). Do not re-prove what
   Mathlib already has.
3. If stuck or the problem is big: split. \`pab_split({subtasks:[...]})\` writes
   child mission files; dispatch them with the \`subagent\` tool (or
   \`team_send\`), then assemble. Each subtask needs \`goal_statement\`,
   \`lean_context\`, \`imports\` and \`acceptance\` (see "Child mission contract"
   below); pass \`dispatch[i].subagent.prompt\` to the child verbatim.
4. Web search only as a last resort. prove2me / formalpedia / github.com/prove2me
   / arxiv / huggingface are blocked by the guard.
5. No \`sorry\`/\`admit\`, no statement or import changes, no writes outside this
   project. Stop as soon as it compiles.

Child mission contract (\`pab_split\` rejects anything else):

    goal_statement : <the exact Lean goal/type to prove>
    lean_context   : <variables, hypotheses, open namespaces, imports>
    imports        : ["Mathlib", ...]      # subset of the imports above
    acceptance     : cd <project> && lake env lean <file>.lean
    forbidden      : ["locate the source proof", "search prove2me/formalpedia", "read Solutions/"]

A child is told *what to prove*, never *where to find it*: a mission that asks
to locate or search for the original proof is rejected, and its \`dispatch\` entry
is what you paste into \`subagent\` (verbatim).

Work autonomously. Do not ask questions: nobody will answer.
` + (forced ? forcedDecompositionBrief() : "")
}

// ---------------------------------------------------------------------------
// Sub-mission contract (`pab_split`) — a child gets a goal, not a scavenger hunt
// ---------------------------------------------------------------------------

/**
 * The four fields every child mission MUST carry. A mission without any of them
 * is rejected: the previous arm's child #1 was literally "locate the original
 * source/proof", which cannot be proved and died on guard-denied reads.
 */
export const MISSION_FIELDS = ["goal_statement", "lean_context", "imports", "acceptance"]

/** Stamp applied to every mission (and repeated in the child's prompt). */
export const MISSION_FORBIDDEN = [
  "locate the source proof",
  "search prove2me/formalpedia",
  "read Solutions/",
]

/** Text that means "go find the answer instead of proving it". */
const SOURCE_HUNT_PATTERNS = [
  [/locate\s+(?:the\s+)?(?:original\s+|reference\s+|existing\s+|real\s+)?(?:source|proof|solution)\b/i, "locate the source proof"],
  [/\b(?:find|search|look\s+up|grep|hunt\s+for)\b[^\n]{0,60}\b(?:original|reference|existing)\s+(?:proof|solution|source)\b/i, "search the original proof"],
  [/\b(?:search|grep|scan|look\s+in|browse|recall)\b[^\n]{0,80}(?:prove2me|formalpedia|hot_papers|p2m\/data|bank_local)/i, "search prove2me/formalpedia"],
  [/\b(?:read|open|cat|inspect|list)\b[^\n]{0,60}(?:\/Solutions\/|\bSolutions\/|Thm_\w+\.lean)/i, "read Solutions/"],
  [/\b(?:prove2me|formalpedia|bank_local|\/p2m\/data\/)\b/i, "mentions the oracle/bank"],
  [/\bwhere\s+(?:does|is)\s+(?:this|the)\s+(?:theorem|lemma)\s+come\s+from\b/i, "provenance hunt"],
  [/\banywhere\s+on\s+this\s+machine\b/i, "machine-wide source hunt"],
  [/\b(?:find|locate)\s+(?:any\s+)?equivalent\s+(?:lemma|theorem|statement)\b/i, "equivalent-lemma hunt"],
]

const ACCEPTANCE_RE = /^cd\s+\S.*&&\s*lake\s+env\s+lean\s+\S+\.lean\s*$/
const IMPORT_RE = /^[A-Za-z0-9_][A-Za-z0-9_.']*$/

/** All free text of a mission, excluding the fields that legitimately name the
 * forbidden actions (`forbidden` repeats "locate the source proof" by design). */
export function missionText(mission) {
  const skip = new Set(["forbidden", "imports"])
  const out = []
  for (const [k, v] of Object.entries(mission ?? {})) {
    if (skip.has(k)) continue
    if (typeof v === "string") out.push(v)
    else if (Array.isArray(v)) out.push(v.filter((x) => typeof x === "string").join("\n"))
  }
  return out.join("\n")
}

/** Drop prohibition text: `forbidden:` lines and whole `## Forbidden` sections.
 * A prohibition ("do not read Solutions/") is the opposite of an instruction,
 * so it must not be reported as a source hunt. */
export function stripForbiddenLines(text) {
  const out = []
  let inForbidden = false
  for (const line of String(text ?? "").split("\n")) {
    if (/^#{1,6}\s*forbidden\b/i.test(line.trim())) {
      inForbidden = true
      continue
    }
    if (inForbidden && /^#{1,6}\s+\S/.test(line.trim())) inForbidden = false
    if (inForbidden) continue
    if (/^\s*forbidden\s*:/.test(line)) continue
    out.push(line)
  }
  return out.join("\n")
}

/** Which source-hunt instructions a text contains (empty array = clean). */
export function findSourceHunt(text) {
  const t = stripForbiddenLines(text)
  const hits = []
  for (const [re, label] of SOURCE_HUNT_PATTERNS) if (re.test(t) && !hits.includes(label)) hits.push(label)
  return hits
}

/**
 * Validate one child mission against the contract.
 * Hard-required: goal_statement, lean_context, imports, acceptance.
 * `forbidden` is defaulted to MISSION_FORBIDDEN when absent.
 */
export function validateMissionContract(mission, { allowedImports = null } = {}) {
  const errors = []
  const m = mission && typeof mission === "object" ? mission : {}
  const s = (v) => (typeof v === "string" ? v.trim() : "")

  const goal = s(m.goal_statement)
  if (!goal) errors.push("missing goal_statement (the exact Lean goal/type to prove)")
  else if (goal.length < 4) errors.push("goal_statement too short to be a Lean goal")
  else if (!/[:⊢→∀∃]/.test(goal)) {
    errors.push("goal_statement does not look like a Lean type (no ':', '⊢', '→', '∀' or '∃')")
  }

  const ctx = s(m.lean_context)
  if (!ctx) errors.push("missing lean_context (variables, hypotheses, open namespaces, imports)")
  else if (ctx.length < 20) errors.push("lean_context too short — give the variables/hypotheses/namespaces the goal lives in")

  let importsOk = false
  if (!Array.isArray(m.imports)) errors.push("missing imports (array of module names)")
  else if (m.imports.length === 0) errors.push("imports is empty — list the modules the child may import")
  else {
    importsOk = true
    for (const im of m.imports) {
      if (typeof im !== "string" || !IMPORT_RE.test(im.trim())) {
        errors.push(`bad import: ${JSON.stringify(im)}`)
        importsOk = false
        break
      }
    }
    if (importsOk && Array.isArray(allowedImports)) {
      const allowed = new Set(allowedImports.map((x) => String(x).trim()))
      const extra = m.imports.map((x) => String(x).trim()).filter((x) => !allowed.has(x))
      if (extra.length) errors.push(`imports not allowed by the parent's Problem.lean: ${extra.join(", ")}`)
    }
  }

  const acc = s(m.acceptance)
  if (!acc) errors.push("missing acceptance (the exact verification command)")
  else if (!ACCEPTANCE_RE.test(acc)) {
    errors.push(`acceptance must be exactly \`cd <project> && lake env lean <file>.lean\` (got ${JSON.stringify(acc)})`)
  }

  if (m.forbidden !== undefined && !Array.isArray(m.forbidden)) errors.push("forbidden must be an array of strings")

  for (const h of findSourceHunt(missionText(m))) errors.push(`source hunt in the mission text: "${h}"`)

  const forbidden =
    Array.isArray(m.forbidden) && m.forbidden.length ? m.forbidden.map(String) : [...MISSION_FORBIDDEN]

  return {
    ok: errors.length === 0,
    errors,
    normalized: {
      goal_statement: goal,
      lean_context: ctx,
      imports: Array.isArray(m.imports) ? m.imports.map((x) => String(x).trim()) : [],
      acceptance: acc,
      forbidden,
      ...(typeof m.hint === "string" && m.hint.trim() ? { hint: m.hint.trim() } : {}),
    },
  }
}

/** The objective a child should set: `prove <mission_id>: <goal_statement>`. */
export function missionObjective(missionId, mission) {
  const one = String(mission?.goal_statement ?? "").replace(/\s+/g, " ").trim()
  return `prove ${missionId}: ${one}`
}

/** The file an `acceptance` command compiles (best effort). */
export function acceptanceFile(acceptance) {
  const m = String(acceptance ?? "").match(/lake\s+env\s+lean\s+(\S+\.lean)\s*$/)
  return m ? m[1] : "missions/Mission.lean"
}

/**
 * The exact prompt the parent must hand to `subagent` for one mission: it
 * embeds goal_statement / lean_context / imports / acceptance verbatim, plus the
 * objective for the child's `goal` tool.
 */
export function childPrompt({ missionId, mission, projectDir }) {
  const file = acceptanceFile(mission.acceptance)
  const objective = missionObjective(missionId, mission)
  const imports = (mission.imports ?? []).map(String)
  const forbidden = Array.isArray(mission.forbidden) && mission.forbidden.length ? mission.forbidden : MISSION_FORBIDDEN
  return `# Child mission ${missionId}

You are a child mission of a decomposition. Prove exactly ONE Lean goal and
make it compile. Do not re-plan the parent's proof; do not widen the goal.

## Contract (fixed — copy it, do not rewrite it)

goal_statement:
${mission.goal_statement}

lean_context:
${mission.lean_context}

imports: [${imports.join(", ")}]
acceptance: ${mission.acceptance}
forbidden: [${forbidden.map((f) => JSON.stringify(f)).join(", ")}]

## What to do

1. Work inside ${projectDir} (Lean 4.33.1 + pinned, prebuilt Mathlib — already
   wired; nothing to install).
2. Put the lemma in \`${file}\` (create it if needed). Its statement must be
   exactly the goal above, modulo notation. You may add helper lemmas in the
   same file.
3. Make this command exit 0 with no \`sorry\`/\`admit\`:

       ${mission.acceptance}

   That is the only acceptance criterion. It is also the only thing the parent
   will re-run.
4. Do not modify \`Problem.lean\` and do not touch files outside the project.

## Forbidden

- Do not look for, grep for, or read the original source/proof of this theorem
  or any equivalent lemma. The question bank and the formalpedia oracle are
  denied by the sandbox guard, so such attempts return denials, not information,
  and the run is killed early.
- Do not import anything outside the \`imports\` list above.

## Report back

status (proved | partial | blocked) · the file · the exact final Lean statement ·
if partial, the one subgoal that remains (as a Lean goal, with context).

## First action

If a \`goal\` tool is available in this session, call it before anything else:

    goal({action: "set", objective: ${JSON.stringify(objective)}})

Then start on the lemma.`
}

/** Everything the parent needs to dispatch one mission, verbatim. */
export function dispatchFor(missionId, mission, projectDir) {
  const prompt = childPrompt({ missionId, mission, projectDir })
  const description = `Prove ${missionId}`.slice(0, 60)
  return {
    mission_id: missionId,
    objective: missionObjective(missionId, mission),
    goal_statement: mission.goal_statement,
    acceptance: mission.acceptance,
    subagent: { agent: "general", description, prompt },
    team_send: { to: "children", mode: "queue", text: prompt },
  }
}

/** Recursively drop prohibition text from a tool input before leak scanning.
 * The harness's own `forbidden` stamp names the oracle, so a naive scan would
 * mark every decomposed run as contaminated. */
export function scrubProhibitions(value) {
  if (typeof value === "string") return stripForbiddenLines(value)
  if (Array.isArray(value)) return value.map(scrubProhibitions)
  if (value && typeof value === "object") {
    const out = {}
    for (const [k, v] of Object.entries(value)) {
      if (/^forbidden(_stamp)?$/i.test(k)) continue
      out[k] = scrubProhibitions(v)
    }
    return out
  }
  return value
}

// ---------------------------------------------------------------------------
// Grading
// ---------------------------------------------------------------------------

const SORRY_RE = /\b(sorry|admit|sorryAx)\b/

/** Drop Lean comments and string literals before scanning for `sorry`. */
export function stripLean(text) {
  let out = ""
  let i = 0
  const src = String(text ?? "")
  let depth = 0
  while (i < src.length) {
    const two = src.slice(i, i + 2)
    if (depth === 0 && two === "/-") {
      depth = 1
      i += 2
      continue
    }
    if (depth > 0) {
      if (two === "/-") {
        depth += 1
        i += 2
        continue
      }
      if (two === "-/") {
        depth -= 1
        i += 2
        continue
      }
      i += 1
      continue
    }
    if (two === "--") {
      while (i < src.length && src[i] !== "\n") i += 1
      continue
    }
    if (src[i] === '"') {
      i += 1
      while (i < src.length) {
        if (src[i] === "\\") {
          i += 2
          continue
        }
        if (src[i] === '"') {
          i += 1
          break
        }
        i += 1
      }
      out += '""'
      continue
    }
    out += src[i]
    i += 1
  }
  return out
}

/**
 * Grade one finished task.
 * pass ⇔ compiles ∧ no sorry ∧ statement unchanged.
 */
export function grade({ envDir, timeoutS = 300 }) {
  const repo = path.join(envDir, "repo")
  const problemFile = path.join(repo, "Problem.lean")
  const secrets = readJson(path.join(envDir, "secrets.json"))
  const started = Date.now()

  if (!exists(problemFile)) {
    return { pass: false, failure: "gave_up", detail: "Problem.lean is missing", elapsed_s: 0 }
  }
  const text = fs.readFileSync(problemFile, "utf8")
  const clean = stripLean(text)
  const stmt = problemStatement(clean)
  const stmtHash = sha256(normalizeWs(stmt))
  const statement_ok = stmtHash === secrets.problem_statement_sha256
  const sorry_hits = (clean.match(new RegExp(SORRY_RE, "g")) ?? []).length

  const lakeEnv = {
    PATH: `${PATHS.elan}:${process.env.PATH ?? "/usr/local/bin:/usr/bin:/bin"}`,
    HOME: process.env.HOME ?? os.homedir(),
  }
  // Never pass an empty ELAN_HOME: elan would then resolve a *relative* toolchain
  // dir under the project and download Lean into the run directory.
  if (process.env.ELAN_HOME) lakeEnv.ELAN_HOME = process.env.ELAN_HOME
  const res = sh("lake", ["env", "lean", "Problem.lean"], {
    cwd: repo,
    timeout: timeoutS * 1000,
    env: lakeEnv,
  })
  const elapsed = (Date.now() - started) / 1000
  const out = `${res.stdout}\n${res.stderr}`
  const errors = out
    .split("\n")
    .filter((l) => /:\s*(error|Error)\b/.test(l) || /^error:/.test(l))
    .map((l) => l.trim())
    .slice(0, 12)
  const timedOut = res.signal === "SIGTERM" || /timed out|timeout/i.test(res.stderr ?? "")
  const compiles = res.code === 0

  let failure = null
  if (!compiles) failure = timedOut ? "grade_timeout" : "compile_error"
  else if (!statement_ok) failure = "wrong_statement"
  else if (sorry_hits > 0) failure = "sorry"
  else if (/declaration uses 'sorry'|uses 'sorry'/.test(out)) failure = "sorry"

  return {
    pass: failure === null,
    failure,
    elapsed_s: Number(elapsed.toFixed(2)),
    statement_ok,
    sorry_hits,
    statement_sha256: stmtHash,
    exit: res.code,
    errors,
    output_tail: out.trim().split("\n").slice(-25).join("\n"),
  }
}

// ---------------------------------------------------------------------------
// Agent run + transcript analysis
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Watchdog — kill a session early when it is provably not making progress
// ---------------------------------------------------------------------------

/**
 * Defaults for the four early-stop rules. All are overridable per run via
 * `WATCHDOG_<NAME>` in the environment or via the plugin options
 * (`WATCHDOG_REPEAT_TOOL`, `WATCHDOG_GUARD_DENY`, `WATCHDOG_IDLE_TURNS`,
 * `WATCHDOG_REPEAT_ERROR`, `WATCHDOG_POLL_MS`, `WATCHDOG_KILL_GRACE_MS`,
 * `WATCHDOG=off` to disable).
 */
export const WATCHDOG_DEFAULTS = {
  repeatTool: 5,
  guardDeny: 3,
  idleTurns: 8,
  repeatError: 4,
  pollMs: 500,
  killGraceMs: 10_000,
  enabled: true,
}

const WATCHDOG_ENV = {
  repeatTool: "WATCHDOG_REPEAT_TOOL",
  guardDeny: "WATCHDOG_GUARD_DENY",
  idleTurns: "WATCHDOG_IDLE_TURNS",
  repeatError: "WATCHDOG_REPEAT_ERROR",
  pollMs: "WATCHDOG_POLL_MS",
  killGraceMs: "WATCHDOG_KILL_GRACE_MS",
}

export function watchdogConfig(env = process.env, overrides = {}) {
  const cfg = { ...WATCHDOG_DEFAULTS }
  for (const [key, name] of Object.entries(WATCHDOG_ENV)) {
    const raw = overrides?.[key] ?? env?.[name]
    if (raw === undefined || raw === null || raw === "") continue
    const n = Number(raw)
    if (Number.isFinite(n) && n > 0) cfg[key] = n
  }
  const off = String(overrides?.enabled ?? env?.WATCHDOG ?? "").toLowerCase()
  if (off === "off" || off === "0" || off === "false") cfg.enabled = false
  if (overrides?.enabled === false) cfg.enabled = false
  return cfg
}

/** Deterministic JSON (sorted keys) for comparing tool inputs. */
export function stableStringify(value) {
  if (value === null || typeof value !== "object") return JSON.stringify(value) ?? "null"
  if (Array.isArray(value)) return `[${value.map(stableStringify).join(",")}]`
  return `{${Object.keys(value)
    .sort()
    .map((k) => `${JSON.stringify(k)}:${stableStringify(value[k])}`)
    .join(",")}}`
}

/** Identity of a tool call: tool name + normalized input (rule 1). */
export function toolCallKey(tool, input) {
  const norm = stableStringify(input ?? {}).replace(/\s+/g, " ").slice(0, 600)
  return `${tool}::${norm}`
}

/**
 * The first path a command mentions, truncated to its root (3 segments), is the
 * "resource" of a denial. `~/lean-4.28-reap/formalpedia/x` →
 * `~/lean-4.28-reap`; a command with no path falls back to the tool name, so
 * three identical bare denials still count.
 */
export function resourceKey(text, fallback = "?") {
  const src = String(text ?? "")
  const home = os.homedir()
  const m = src.match(/(?:^|[\s"'`=(])((?:~\/|\/)[^\s"'`;,)|>]+)/)
  if (!m) return fallback
  let p = m[1].replace(/\/+$/, "")
  const prefix = home && p.startsWith(home) ? "~" : ""
  if (prefix) p = p.slice(home.length)
  const seg = p.split("/").filter(Boolean)
  if (!seg.length) return fallback
  const take = seg.slice(0, prefix ? 2 : 3).join("/")
  return prefix ? `~/${take}` : `/${take}`
}

/** The Lean/lake error signature of a tool result, path- and line-insensitive. */
export function errorSignature(text) {
  for (const raw of String(text ?? "").split("\n")) {
    const i = raw.search(/\berror\b/i)
    if (i < 0) continue
    const tail = raw.slice(i)
    if (!/^error\s*[:(]|^error\b.*:/i.test(tail)) continue
    return tail.replace(/\b\d+:\d+\b/g, "L:C").replace(/\s+/g, " ").trim().slice(0, 240)
  }
  return null
}

/** Does this tool call try to compile something? (rule 4 only tracks those) */
export function isCompileAttempt(tool, input) {
  if (/^lean_|^lean-/.test(String(tool ?? ""))) return true
  const s = stableStringify(input ?? {})
  return /lake\s+env\s+lean|lake\s+build|\.lean\b/.test(s)
}

/** True when a tool result is a guard/permission denial. */
export function isDenial(status, message) {
  if (String(status ?? "").toLowerCase() === "denied") return true
  return /permission denied|denied by (?:the )?(?:guard|policy)|not allowed|guard denied/i.test(String(message ?? ""))
}

const MTIME_SKIP = new Set([".git", ".lake", "node_modules", "toolchains", ".cache", "target"])

/**
 * Newest mtime under a directory (skipping build/vcs trees). This is rule 3's
 * progress signal: an agent that neither writes a file nor emits tokens for 8
 * turns is stuck.
 */
export function dirMaxMtime(dir, budget = 4000) {
  if (!dir) return 0
  let max = 0
  let seen = 0
  const walk = (d) => {
    if (seen > budget) return
    let ents
    try {
      ents = fs.readdirSync(d, { withFileTypes: true })
    } catch {
      return
    }
    for (const e of ents) {
      if (MTIME_SKIP.has(e.name)) continue
      const p = path.join(d, e.name)
      if (e.isDirectory()) walk(p)
      else {
        seen += 1
        try {
          const st = fs.statSync(p)
          if (st.mtimeMs > max) max = st.mtimeMs
        } catch {
          /* vanished */
        }
      }
    }
  }
  walk(dir)
  return max
}

/**
 * Create a watchdog state machine. Pure: `feed(event)` consumes already-parsed
 * transcript/guard events and returns a stop record on the first violation.
 *
 * Rules (thresholds from `config`):
 *   1. `repeatTool` (5)   — N consecutive identical tool calls (tool + input).
 *   2. `guardDeny` (3)    — N consecutive guard denials on the same resource.
 *   3. `idleTurns` (8)    — N turns with no file mtime change AND no new tokens.
 *   4. `repeatError` (4)  — the same compiler error N compile attempts in a row.
 */
export function createWatchdog({
  config = watchdogConfig(),
  taskDir = null,
  statMtime = () => dirMaxMtime(taskDir),
  now = () => Date.now(),
} = {}) {
  const cfg = { ...WATCHDOG_DEFAULTS, ...(config ?? {}) }
  const startedAt = now()
  const state = {
    turn: 0,
    tokens: 0,
    tool_streak: 0,
    last_tool: null,
    deny_streak: 0,
    last_deny: null,
    last_deny_turn: -1,
    last_deny_source: null,
    error_streak: 0,
    last_error: null,
    idle: { turn: 0, mtime: 0, tokens: 0 },
    stopped: false,
    reason: null,
  }
  try {
    state.idle = { turn: 0, mtime: statMtime(), tokens: 0 }
  } catch {
    state.idle = { turn: 0, mtime: 0, tokens: 0 }
  }
  let result = null

  const finish = (reason) => {
    if (result) return result
    state.stopped = true
    state.reason = reason
    result = {
      reason,
      turn: state.turn,
      elapsed: Math.round(((now() - startedAt) / 1000) * 10) / 10,
    }
    return result
  }

  const idleCheck = () => {
    let mtime = 0
    try {
      mtime = statMtime()
    } catch {
      mtime = 0
    }
    if (mtime > state.idle.mtime || state.tokens > state.idle.tokens) {
      state.idle = { turn: state.turn, mtime, tokens: state.tokens }
      return null
    }
    if (state.turn - state.idle.turn >= cfg.idleTurns) return finish("idle_no_progress")
    return null
  }

  const denySeen = new Map() // `${turn}|${key}` -> source that owns this physical denial
  let denySeenTurn = -1
  const denyEvent = (tool, resource, turn, source) => {
    const key = resourceKey(resource, `tool:${tool}`)
    const src = String(source ?? "unknown")
    if (turn !== denySeenTurn) {
      denySeen.clear()
      denySeenTurn = turn
    }
    const slot = `${turn}|${key}`
    const owner = denySeen.get(slot)
    if (owner !== undefined && owner !== src) return null // agent.jsonl + guard.log echo of the same denial
    denySeen.set(slot, src)
    if (state.last_deny === key) state.deny_streak += 1
    else {
      state.last_deny = key
      state.deny_streak = 1
    }
    state.last_deny_turn = turn
    state.last_deny_source = src
    if (state.deny_streak >= cfg.guardDeny) return finish("guard_denied_same_resource")
    return null
  }

  function feed(ev, source) {
    if (result) return result
    const type = String(ev?.type ?? "")
    const part = ev?.part ?? ev?.message?.part ?? ev ?? {}

    if (type === "step_start") {
      state.turn += 1
      return idleCheck()
    }
    if (type === "step_finish") {
      state.tokens += Number(part?.tokens?.output ?? 0)
      return null
    }
    if (type === "guard") {
      // guard.log line: {hook, tool, action, resource, decision}
      if (String(ev.decision ?? "").toLowerCase() === "deny") {
        return denyEvent(String(ev.tool ?? "unknown"), String(ev.resource ?? ""), state.turn, source ?? "guard.log")
      }
      return null
    }
    if (type !== "tool_use" && type !== "tool") return null

    const tool = String(part.tool ?? part.name ?? "unknown")
    const input = part.state?.input ?? part.input ?? {}
    const status = part.state?.status ?? part.status
    const message = part.state?.error ?? part.error ?? ""

    // rule 2 first: a denial is a denial even when the input repeats
    if (isDenial(status, message)) {
      const hit = denyEvent(
        tool,
        `${String(input.command ?? input.path ?? input.pattern ?? "")}`,
        state.turn,
        source ?? "agent.jsonl",
      )
      if (hit) return hit
    } else {
      state.deny_streak = 0
      state.last_deny = null
    }

    // rule 1
    const key = toolCallKey(tool, input)
    if (key === state.last_tool) state.tool_streak += 1
    else {
      state.last_tool = key
      state.tool_streak = 1
    }
    if (state.tool_streak >= cfg.repeatTool) return finish("repeated_tool_call")

    // rule 4
    const output = `${part.state?.output ?? part.output ?? ""}\n${message}`
    const sig = errorSignature(output)
    if (sig) {
      if (sig === state.last_error) state.error_streak += 1
      else {
        state.last_error = sig
        state.error_streak = 1
      }
      if (state.error_streak >= cfg.repeatError) return finish("repeated_compiler_error")
    } else if (isCompileAttempt(tool, input)) {
      state.last_error = null
      state.error_streak = 0
    }
    return null
  }

  return {
    cfg,
    state,
    feed,
    finish,
    snapshot: () => ({ ...state, idle: { ...state.idle }, stop: result }),
  }
}

/** Parse one jsonl line (agent.jsonl or guard.log) into a watchdog event. */
export function parseWatchdogLine(line) {
  const text = String(line ?? "").trim()
  if (!text) return null
  let ev
  try {
    ev = JSON.parse(text)
  } catch {
    return null
  }
  if (ev && ev.decision !== undefined && ev.type === undefined) return { ...ev, type: "guard" }
  return ev
}

/**
 * Incremental jsonl tailer. Keeps a byte offset per file, tolerates partial
 * lines and truncation, and calls `onEvent` for every complete line.
 */
export function tailJsonl({ files = [], pollMs = 500, onEvent = () => {}, fsImpl = fs } = {}) {
  const state = new Map()
  for (const f of files) state.set(f, { offset: 0, carry: "" })
  let timer = null

  const poll = () => {
    for (const [file, s] of state) {
      let st
      try {
        st = fsImpl.statSync(file)
      } catch {
        continue
      }
      if (st.size < s.offset) {
        s.offset = 0
        s.carry = ""
      }
      if (st.size === s.offset) continue
      let buf
      try {
        const fd = fsImpl.openSync(file, "r")
        try {
          buf = Buffer.alloc(st.size - s.offset)
          fsImpl.readSync(fd, buf, 0, buf.length, s.offset)
        } finally {
          fsImpl.closeSync(fd)
        }
      } catch {
        continue
      }
      s.offset = st.size
      const chunk = s.carry + buf.toString("utf8")
      const lines = chunk.split("\n")
      s.carry = lines.pop() ?? ""
      for (const line of lines) {
        const ev = parseWatchdogLine(line)
        if (ev) onEvent(ev, file)
      }
    }
  }

  return {
    poll,
    start() {
      if (timer) return this
      timer = setInterval(poll, pollMs)
      timer.unref?.()
      return this
    },
    stop() {
      if (timer) clearInterval(timer)
      timer = null
      return this
    },
    offsets: () => Object.fromEntries([...state].map(([f, s]) => [f, s.offset])),
  }
}


/** Signal the whole process group of a detached child (SIGTERM, then SIGKILL). */
function killTree(child, sig) {
  try {
    process.kill(-child.pid, sig)
  } catch {
    try {
      child.kill(sig)
    } catch {
      /* already gone */
    }
  }
}

/**
 * Launch one agent run and resolve when it exits, the wall clock expires, or the
 * watchdog fires (4 rules — see createWatchdog).
 * Writes <env>/agent.jsonl, agent.err.log, launch.json, watchdog.jsonl.
 */
export function launchTask({ runDir, task, timeoutS = DEFAULT_TIMEOUT_S, briefMode = "default", watchdog = undefined }) {
  const envDir = path.join(runDir, task.id)
  const repo = path.join(envDir, "repo")
  const jsonl = path.join(envDir, "agent.jsonl")
  const errlog = path.join(envDir, "agent.err.log")
  const guardLog = path.join(envDir, "guard.log")
  const brief = taskBrief({ tier: task.tier, imports: task.imports, forced: briefMode === "forced" })
  const wcfg = watchdogConfig(process.env, watchdog ?? {})
  // Rule 3 watches the project, never the append-only transcript.
  const wd = wcfg.enabled ? createWatchdog({ config: wcfg, taskDir: repo }) : null
  let earlyStop = null
  let tail = null

  const out = fs.openSync(jsonl, "w")
  const err = fs.openSync(errlog, "w")
  const started = Date.now()
  const child = spawn(
    PATHS.opencode,
    ["run", "--standalone", "--auto", "--agent", AGENT_ID, "--model", MODEL, "--format", "json", brief],
    {
      cwd: repo,
      detached: true,
      stdio: ["ignore", out, err],
      env: {
        ...process.env,
        PWD: repo,
        PATH: `${PATHS.elan}:${process.env.PATH ?? "/usr/local/bin:/usr/bin:/bin"}`,
        P2M_GUARD: "on",
        P2M_GUARD_CONFIG: PATHS.guard,
        P2M_GUARD_LOG: guardLog,
        PAB_RUN: path.basename(runDir),
        PAB_ID: task.id,
        PAB_ENV_DIR: envDir,
      },
    },
  )
  fs.closeSync(out)
  fs.closeSync(err)

  // ---- early-stop watchdog ------------------------------------------------
  // Tails the parent transcript and the guard log (children share the guard
  // log, so a child that hunts the oracle still trips rule 2). On a decision the
  // whole process group gets SIGTERM, then SIGKILL after `killGraceMs`.
  if (wd) {
    const stopNow = (decision) => {
      if (earlyStop) return
      earlyStop = decision
      appendJsonl(path.join(envDir, "watchdog.jsonl"), { ts: new Date().toISOString(), event: "early_stop", ...decision })
      killTree(child, "SIGTERM")
      setTimeout(() => killTree(child, "SIGKILL"), wcfg.killGraceMs).unref?.()
    }
    tail = tailJsonl({
      files: [jsonl, guardLog],
      pollMs: wcfg.pollMs,
      onEvent: (ev, source) => {
        if (earlyStop) return
        const d = wd.feed(ev, source === guardLog ? "guard.log" : "agent.jsonl")
        if (d) stopNow(d)
      },
    }).start()
  }

  let timedOut = false
  const timer = setTimeout(() => {
    timedOut = true
    killTree(child, "SIGTERM")
    setTimeout(() => killTree(child, "SIGKILL"), 10_000).unref?.()
  }, timeoutS * 1000)

  const base = () => ({
    id: task.id,
    agent_jsonl: jsonl,
    guard_log: guardLog,
    early_stop: earlyStop,
    watchdog: wcfg.enabled ? wcfg : { enabled: false },
  })

  return new Promise((resolve) => {
    child.on("exit", (code, signal) => {
      clearTimeout(timer)
      tail?.stop()
      const elapsed = (Date.now() - started) / 1000
      const result = {
        ...base(),
        code,
        signal,
        timed_out: timedOut,
        elapsed_s: Number(elapsed.toFixed(1)),
      }
      writeJson(path.join(envDir, "launch.json"), { ...result, model: MODEL, timeout_s: timeoutS, brief_mode: briefMode, brief })
      resolve(result)
    })
    child.on("error", (e) => {
      clearTimeout(timer)
      tail?.stop()
      resolve({
        ...base(),
        code: -1,
        signal: null,
        timed_out: false,
        elapsed_s: Number(((Date.now() - started) / 1000).toFixed(1)),
        error: String(e?.message ?? e),
      })
    })
  })
}

const DECOMP_TOOLS = new Set(["subagent", "task", "pab_split", "team_send"])
const WEB_TOOLS = new Set(["websearch", "webfetch"])

/** Parse the `--format json` transcript: tool calls, decomposition, search. */
export function analyzeTranscript(jsonlFile) {
  const tools = {}
  let calls = 0
  let decomp = 0
  let web = 0
  let leanTools = 0
  let identitySearch = 0
  let lastText = ""
  let cost = 0
  let tokens = { input: 0, output: 0 }
  const decompEvents = []
  const webQueries = []
  if (!exists(jsonlFile)) {
    return { calls, tools, decomp, decomp_events: [], web, web_queries: [], lean_tools: 0, identity_search: 0, last_text: "", cost, tokens }
  }
  const lines = fs.readFileSync(jsonlFile, "utf8").split("\n")
  for (const line of lines) {
    if (!line.trim()) continue
    let ev
    try {
      ev = JSON.parse(line)
    } catch {
      continue
    }
    const part = ev.part ?? {}
    if (ev.type === "text" && typeof part.text === "string") lastText = part.text
    if (ev.type === "step_finish") {
      cost += Number(part.cost ?? 0)
      tokens.input += Number(part.tokens?.input ?? 0)
      tokens.output += Number(part.tokens?.output ?? 0)
    }
    if (ev.type !== "tool_use") continue
    const name = String(part.tool ?? "unknown")
    calls += 1
    tools[name] = (tools[name] ?? 0) + 1
    const input = part.state?.input ?? {}
    if (DECOMP_TOOLS.has(name)) {
      decomp += 1
      const summary =
        name === "pab_split"
          ? (Array.isArray(input.subtasks) ? input.subtasks.map((s) => String(s?.goal ?? "")).join(" | ") : "")
          : String(input.description ?? input.text ?? input.prompt ?? input.goal ?? "").slice(0, 200)
      decompEvents.push({ tool: name, summary })
    }
    if (WEB_TOOLS.has(name)) {
      web += 1
      const q = String(input.query ?? input.url ?? "")
      webQueries.push(q.slice(0, 160))
      if (/prove2me|formalpedia|arxiv|huggingface|AMPUniversality/i.test(q)) identitySearch += 1
    }
    if (name.startsWith("lean_") || name.startsWith("lean-lsp_") || name.startsWith("lean_lsp")) leanTools += 1
  }
  return {
    calls,
    tools,
    decomp,
    decomp_events: decompEvents,
    web,
    web_queries: webQueries,
    lean_tools: leanTools,
    identity_search: identitySearch,
    last_text: lastText.slice(-1200),
    cost: Number(cost.toFixed(4)),
    tokens,
  }
}

/**
 * Compile every extra `.lean` file the run left in the repo (child-session
 * output, scratch proofs). Used by the forced-decomposition arm: a child that
 * cannot finish the parent may still leave a valid lemma.
 */
export function gradeChildFiles(envDir, limit = 6, timeoutS = 120) {
  const repo = path.join(envDir, "repo")
  if (!exists(repo)) return []
  const found = []
  const walk = (dir, depth) => {
    if (depth > 2) return
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      if (e.name === ".git" || e.name === ".lake" || e.name === "toolchains") continue
      const p = path.join(dir, e.name)
      if (e.isDirectory()) walk(p, depth + 1)
      else if (e.name.endsWith(".lean") && e.name !== "Problem.lean") found.push(p)
    }
  }
  walk(repo, 0)
  const results = []
  const lakeEnv = { PATH: `${PATHS.elan}:${process.env.PATH ?? "/usr/local/bin:/usr/bin:/bin"}`, HOME: process.env.HOME ?? os.homedir() }
  if (process.env.ELAN_HOME) lakeEnv.ELAN_HOME = process.env.ELAN_HOME
  for (const file of found.slice(0, limit)) {
    const rel = path.relative(repo, file)
    const res = sh("lake", ["env", "lean", rel], { cwd: repo, timeout: timeoutS * 1000, env: lakeEnv })
    const out = `${res.stdout}\n${res.stderr}`
    results.push({
      file: rel,
      ok: res.code === 0,
      sorry: SORRY_RE.test(stripLean(fs.readFileSync(file, "utf8"))),
      errors: out.split("\n").filter((l) => /:\s*error\b|^error:/.test(l)).slice(0, 3),
    })
  }
  return results
}

/** Tool calls recorded by the guard log slice for one env (denials etc.). */
export function analyzeGuard(guardLog) {
  if (!exists(guardLog)) return { lines: 0, denials: 0, events: [] }
  let lines = 0
  let denials = 0
  const events = []
  for (const line of fs.readFileSync(guardLog, "utf8").split("\n")) {
    if (!line.trim()) continue
    lines += 1
    let ev
    try {
      ev = JSON.parse(line)
    } catch {
      continue
    }
    if (ev.decision === "deny") {
      denials += 1
      if (events.length < 20) events.push(ev)
    }
  }
  return { lines, denials, events }
}

// ---------------------------------------------------------------------------
// Child-session audit: did each dispatched child actually receive the contract?
// ---------------------------------------------------------------------------

/** node:sqlite is experimental; never let its absence break a run. */
function openSessionDb(dbPath) {
  try {
    const req = createRequire(import.meta.url)
    const { DatabaseSync } = req("node:sqlite")
    const db = new DatabaseSync(dbPath, { readOnly: true })
    // A live session may hold the write lock; never block the driver on it.
    try {
      db.exec("PRAGMA busy_timeout = 3000")
    } catch {
      /* older builds */
    }
    return db
  } catch {
    return null
  }
}

/** The session id of a `--format json` transcript (first line carries it). */
export function transcriptSessionId(jsonlFile) {
  if (!exists(jsonlFile)) return null
  for (const line of fs.readFileSync(jsonlFile, "utf8").split("\n")) {
    if (!line.trim()) continue
    try {
      const ev = JSON.parse(line)
      if (ev?.sessionID) return String(ev.sessionID)
    } catch {
      continue
    }
  }
  return null
}

const CONTRACT_PROMPT_MARKERS = {
  goal_statement: /^\s*goal_statement\s*:/m,
  lean_context: /^\s*lean_context\s*:/m,
  imports: /^\s*imports\s*:/m,
  acceptance: /^\s*acceptance\s*:/m,
}

/**
 * Read every child session of a parent session out of the OpenCode store and
 * check that the child's FIRST user message carries the full contract.
 *
 * Returns `{ ok, source, children: [{session, title, contract, missing,
 * source_hunt, denials, prompt_head}] }`; `ok` is null when the store is
 * unreadable (never a failure of the run).
 */
export function auditChildContracts(envDir, { dbPath = PATHS.db, parentSessionId = null } = {}) {
  const jsonl = path.join(envDir, "agent.jsonl")
  const parent = parentSessionId ?? transcriptSessionId(jsonl)
  if (!parent) return { ok: null, source: "none", parent: null, children: [], reason: "no parent session id" }
  const db = openSessionDb(dbPath)
  if (!db) return { ok: null, source: "unavailable", parent, children: [], reason: `cannot open ${dbPath}` }
  try {
    const kids = db.prepare("select id, title from session_v2 where parent_id = ? order by time_created").all(parent)
    const children = kids.map((k) => {
      const first = db
        .prepare("select data from session_message where session_id = ? and type = 'user' order by seq limit 1")
        .get(k.id)
      let prompt = ""
      try {
        prompt = String(JSON.parse(first?.data ?? "{}").text ?? "")
      } catch {
        prompt = ""
      }
      const missing = Object.entries(CONTRACT_PROMPT_MARKERS)
        .filter(([, re]) => !re.test(prompt))
        .map(([name]) => name)
      // Tool inputs the child actually executed (denials included).
      let denials = 0
      let sourceAttempts = 0
      const rows = db.prepare("select data from session_message where session_id = ? and type = 'assistant'").all(k.id)
      for (const row of rows) {
        let msg
        try {
          msg = JSON.parse(row.data)
        } catch {
          continue
        }
        for (const c of msg.content ?? []) {
          if (c?.type !== "tool") continue
          const input = JSON.stringify(scrubProhibitions(c.state?.input ?? {}))
          if (c.state?.status === "error" && isDenial(c.state.status, c.state?.error)) denials += 1
          if (/formalpedia|Solutions\/|bank_local|\/p2m\/data\//.test(input)) sourceAttempts += 1
        }
      }
      return {
        session: k.id,
        title: String(k.title ?? ""),
        contract: missing.length === 0,
        missing,
        source_hunt: findSourceHunt(prompt).length > 0,
        source_attempts: sourceAttempts,
        denials,
        prompt_head: prompt.split("\n").slice(0, 12).join("\n"),
      }
    })
    const bad = children.filter((c) => !c.contract || c.source_hunt)
    return {
      ok: children.length === 0 ? null : bad.length === 0,
      source: dbPath,
      parent,
      children,
      reason: children.length === 0 ? "no child sessions" : bad.length ? "child contract violated" : "all children carry the contract",
    }
  } catch (e) {
    return { ok: null, source: "error", parent, children: [], reason: String(e?.message ?? e) }
  }
}



export function newRunId(seed) {
  const stamp = new Date().toISOString().replace(/[-:]/g, "").replace(/\..+/, "").replace("T", "-")
  return `pab-${stamp}-${shortHash(String(seed) + stamp, 4)}`
}

export function runPath(runId, runRoot = PATHS.runRoot) {
  return path.join(runRoot, runId)
}

export function loadRun(runId, runRoot = PATHS.runRoot) {
  const dir = runPath(runId, runRoot)
  const file = path.join(dir, "run.json")
  if (!exists(file)) throw new Error(`unknown run: ${runId} (${file})`)
  const run = readJson(file)
  run.dir = dir
  return run
}

export function saveRun(run) {
  writeJson(path.join(run.dir, "run.json"), run)
}

/**
 * Create a run: sample, materialise every blind env, write run.json.
 * Deterministic for a given (seed, tiers, perTier, bank).
 */
export function createRun(opts = {}) {
  const model = String(opts.model ?? MODEL)
  if (model !== MODEL) throw new Error(`refusing model ${model}: this harness may only use ${MODEL}`)
  const runRoot = opts.runRoot ?? PATHS.runRoot
  const bankDir = opts.bankDir ?? PATHS.bank
  const tiers = (Array.isArray(opts.tiers) && opts.tiers.length ? opts.tiers : TIERS).map((t) => String(t).toUpperCase())
  for (const t of tiers) if (!TIERS.includes(t)) throw new Error(`unknown tier ${t}`)
  const perTier = Math.max(1, Math.min(Number(opts.perTier ?? 2), 20))
  const seed = String(opts.seed ?? "pab-1")
  const timeoutS = Number(opts.timeoutS ?? DEFAULT_TIMEOUT_S)
  const runId = String(opts.runId ?? newRunId(seed))
  const dir = runPath(runId, runRoot)
  if (exists(path.join(dir, "run.json"))) throw new Error(`run already exists: ${runId}`)
  fs.mkdirSync(dir, { recursive: true })

  const tasks = []
  const used = new Set()
  const sampled = []
  for (const tier of tiers) {
    const recs = sampleTier({ tier, perTier, seed, bankDir })
    if (recs.length === 0) throw new Error(`no usable records in ${tier}`)
    for (const rec of recs) {
      let id = safeName(rec.id ?? rec.fq_name ?? rec.theorem_id ?? `${tier}-x`)
      if (used.has(id)) id = `${id}-${shortHash(String(rec.theorem_id ?? Math.random()), 4)}`
      used.add(id)
      sampled.push({ tier, id, rec })
    }
  }

  for (const { tier, id, rec } of sampled) {
    const built = buildEnv({ runDir: dir, id, rec, tier, lakeName: `pab_env_${shortHash(id, 8)}` })
    tasks.push({
      id,
      tier,
      bank_id: rec.id ?? null,
      fq_name: rec.fq_name ?? rec.id ?? null,
      theorem_id: rec.theorem_id ?? null,
      imports: rec.imports,
      status: "pending",
      pass: null,
      failure: null,
      env_dir: built.envDir,
      repo: built.repo,
      statement_sha256: built.statement_sha256,
      commits: built.commits,
      policy: "eval-blind+msa",
      brief_mode: String(opts.briefMode ?? "default"),
      created_at: new Date().toISOString(),
    })
  }

  const run = {
    run_id: runId,
    kind: "agent-vs-prove2me",
    plugin: "p2m-agent-bench",
    model,
    seed,
    tiers,
    per_tier: perTier,
    timeout_s: timeoutS,
    jobs: Number(opts.jobs ?? 1),
    bank_dir: bankDir,
    lean_project: PATHS.leanProject,
    created_at: new Date().toISOString(),
    tasks,
  }
  writeJson(path.join(dir, "run.json"), run)
  return { run_id: runId, dir, model, seed, ids: tasks.map((t) => t.id), tasks }
}

/** Claim one specific task (used by the pilot / explicit-id batch runs). */
export function claimTask(runId, id, runRoot = PATHS.runRoot) {
  const run = loadRun(runId, runRoot)
  const task = run.tasks.find((t) => t.id === id)
  if (!task) throw new Error(`unknown task ${id} in ${runId}`)
  const claimDir = path.join(run.dir, ".claims")
  fs.mkdirSync(claimDir, { recursive: true })
  const claim = path.join(claimDir, `${task.id}.claim`)
  try {
    const fd = fs.openSync(claim, "wx")
    fs.writeSync(fd, String(Date.now()))
    fs.closeSync(fd)
  } catch {
    if (task.status === "pending") throw new Error(`task ${id} is already claimed by another worker`)
  }
  if (task.status === "pending") {
    task.status = "running"
    task.started_at = new Date().toISOString()
    saveRun(run)
  }
  return { run, task }
}

/**
 * Rewrite `<env>/opencode.json` (+ `.opencode.json`) so it always carries the
 * full eval policy: the eval-blind L1 rules, MSA enablement, harness-only tool
 * denials, and shell-level denials for the paths that would leak the answer
 * (the question bank, the formalpedia oracle checkout, sibling run dirs).
 *
 * Idempotent: safe to re-run on an existing env.
 */
export function patchEnvConfig(envDir) {
  const cfgFile = path.join(envDir, "opencode.json")
  const cfg = readJson(cfgFile)
  const injected = new Set([
    "subagent", "task", "team_send", "team_list", "team_status", "team_space_post", "team_space_read",
    "pab_split", "pab_run", "pab_next", "pab_finish", "pab_status", "pab_report",
    "p2m_next", "p2m_get", "p2m_check", "p2m_submit", "p2m_split", "p2m_status", "p2m_export",
  ])
  const rules = (cfg.permissions ?? []).filter(
    (r) => r && !injected.has(String(r.action)) && !String(r.resource ?? "").includes("formalpedia"),
  )

  // Shell-level read protection. L1 `shell` rules match the whole command
  // string, so these catch `cat /…/formalpedia/…/Solutions/…`, `grep … bank_local`
  // and friend. Not a sandbox (L3 is), but it closes the accidental leak.
  const denyPath = (glob) => ({ action: "shell", resource: glob, effect: "deny" })
  const leakRules = [
    denyPath("*formalpedia*"),
    denyPath("*/p2m/data/bank*"),
    denyPath("*/p2m/data/*.jsonl*"),
    denyPath("*/eval/runs/*"),
    denyPath("*secrets.json*"),
    denyPath("*/guard.json*"),
    denyPath("*/lean-4.28-reap/env-*"),
    denyPath("*/lean-4.28-reap/reap*"),
  ]

  const extra = [
    // multi-agent capability (the eval-blind profile denies it by default)
    { action: "subagent", resource: "*", effect: "allow" },
    { action: "task", resource: "*", effect: "allow" },
    { action: "team_send", resource: "*", effect: "allow" },
    { action: "team_list", resource: "*", effect: "allow" },
    { action: "team_status", resource: "*", effect: "allow" },
    { action: "team_space_post", resource: "*", effect: "allow" },
    { action: "team_space_read", resource: "*", effect: "allow" },
    // blind-safe decomposition recorder (harness tool, no bank access)
    { action: "pab_split", resource: "*", effect: "allow" },
    // harness-only tools: never available to the graded agent
    { action: "pab_run", resource: "*", effect: "deny" },
    { action: "pab_next", resource: "*", effect: "deny" },
    { action: "pab_finish", resource: "*", effect: "deny" },
    { action: "pab_status", resource: "*", effect: "deny" },
    { action: "pab_report", resource: "*", effect: "deny" },
    // the question bank would leak reference proofs (and the statement_nl hints)
    { action: "p2m_next", resource: "*", effect: "deny" },
    { action: "p2m_get", resource: "*", effect: "deny" },
    { action: "p2m_check", resource: "*", effect: "deny" },
    { action: "p2m_submit", resource: "*", effect: "deny" },
    { action: "p2m_split", resource: "*", effect: "deny" },
    { action: "p2m_status", resource: "*", effect: "deny" },
    { action: "p2m_export", resource: "*", effect: "deny" },
    ...leakRules,
  ]

  cfg.permissions = [...rules, ...extra]
  cfg.default_agent = AGENT_ID
  cfg.agents = cfg.agents ?? {}
  fs.writeFileSync(path.join(envDir, "AGENT_POLICY.md"), agentPolicy(), "utf8")
  cfg.agents[AGENT_ID] = {
    description: "Blind prove2me eval agent (agent-vs-prove2me, no MCTS)",
    mode: "primary",
    model: MODEL,
    temperature: 0.2,
    prompt: agentPolicy(),
    permissions: cfg.permissions,
  }
  writeJson(cfgFile, cfg)
  writeJson(path.join(envDir, ".opencode.json"), cfg)
  return cfg
}

/** Restore a task's repo to its pristine one-commit state (undo the agent). */
export function restoreRepo(envDir) {
  const repo = path.join(envDir, "repo")
  sh("git", ["checkout", "--", "."], { cwd: repo, env: GIT_ENV })
  // -d (not -x): keeps the ignored .lake/ build tree
  sh("git", ["clean", "-fdq"], { cwd: repo, env: GIT_ENV })
  return repo
}

/**
 * Evidence that the agent reached for the answer instead of proving it.
 * Only *successful* accesses count as contamination; blocked ones are recorded
 * separately as attempts (they are a capability signal, not a leak).
 */
export function detectLeaks(envDir) {
  const jsonl = path.join(envDir, "agent.jsonl")
  const confirmed = []
  const blocked = []
  if (!exists(jsonl)) return { confirmed, blocked }
  const patterns = [
    [/formalpedia/, "formalpedia oracle checkout"],
    [/p2m\/data\/bank|bank_local/, "question bank"],
    [/\/Solutions\/|Theorems\/Thm_/, "reference solution file"],
    [/secrets\.json/, "secrets.json"],
  ]
  for (const line of fs.readFileSync(jsonl, "utf8").split("\n")) {
    if (!line.trim()) continue
    let ev
    try {
      ev = JSON.parse(line)
    } catch {
      continue
    }
    if (ev.type !== "tool_use") continue
    const input = JSON.stringify(scrubProhibitions(ev.part?.state?.input ?? {}))
    const status = ev.part?.state?.status
    for (const [re, label] of patterns) {
      if (!re.test(input)) continue
      const bucket = status === "error" || status === "denied" ? blocked : confirmed
      if (!bucket.includes(label)) bucket.push(label)
    }
  }
  return { confirmed, blocked }
}

/** Claim the next pending task atomically (exclusive-create claim file). */
export function claimNext(runId, runRoot = PATHS.runRoot) {
  const run = loadRun(runId, runRoot)
  const claimDir = path.join(run.dir, ".claims")
  fs.mkdirSync(claimDir, { recursive: true })
  for (const task of run.tasks) {
    if (task.status !== "pending") continue
    const claim = path.join(claimDir, `${task.id}.claim`)
    try {
      const fd = fs.openSync(claim, "wx")
      fs.writeSync(fd, String(Date.now()))
      fs.closeSync(fd)
    } catch {
      continue
    }
    task.status = "running"
    task.started_at = new Date().toISOString()
    saveRun(run)
    return { run, task }
  }
  return { run, task: null }
}

export function finishTask({ runId, id, evidence, runRoot = PATHS.runRoot, gradeTimeoutS = 300 }) {
  const run = loadRun(runId, runRoot)
  const task = run.tasks.find((t) => t.id === id)
  if (!task) throw new Error(`unknown task ${id} in ${runId}`)
  const envDir = path.join(run.dir, id)

  const g = grade({ envDir, timeoutS: gradeTimeoutS })
  const tr = analyzeTranscript(path.join(envDir, "agent.jsonl"))
  const guard = analyzeGuard(path.join(envDir, "guard.log"))
  const launchFile = path.join(envDir, "launch.json")
  const launch = exists(launchFile) ? readJson(launchFile) : {}
  const elapsed = Number(launch.elapsed_s ?? task.elapsed_s ?? g.elapsed_s)

  let failure = g.failure
  let pass = g.pass
  if (launch.timed_out) {
    pass = false
    failure = "timeout"
  }
  if (!pass && !failure) failure = "gave_up"
  // The watchdog killed the session: that is the failure class, not a compiler
  // error the model never got to see.
  if (!pass && launch.early_stop) {
    pass = false
    failure = "early_stop"
  }
  if (!pass && failure === "compile_error" && tr.calls === 0) failure = "gave_up"
  if (!pass && failure === "compile_error" && /--\s*TODO/.test(fs.readFileSync(path.join(envDir, "repo", "Problem.lean"), "utf8"))) {
    failure = tr.decomp > 0 ? "decomposed_unfinished" : "gave_up"
  }
  if (!pass && failure !== "timeout" && tr.decomp > 0 && (failure === "gave_up" || failure === "decomposed_unfinished")) {
    failure = "decomposed_unfinished"
  }

  task.status = pass ? "passed" : "failed"
  task.finished_at = new Date().toISOString()
  task.pass = pass
  task.failure = pass ? null : failure
  task.elapsed_s = elapsed
  task.tool_calls = tr.calls
  task.tools = tr.tools
  task.decomposed = tr.decomp > 0
  task.decomp_events = tr.decomp_events
  task.searched = tr.web > 0
  task.web_queries = tr.web_queries
  task.identity_search = tr.identity_search > 0
  task.lean_tools = tr.lean_tools
  task.guard_denials = guard.denials
  task.grade = {
    pass: g.pass,
    failure: g.failure,
    statement_ok: g.statement_ok,
    sorry_hits: g.sorry_hits,
    exit: g.exit,
    errors: g.errors,
    output_tail: g.output_tail,
  }
  task.cost_usd = tr.cost
  task.tokens = tr.tokens
  const timing = transcriptTiming(path.join(envDir, "agent.jsonl"))
  task.turns = timing?.turns ?? 0
  task.model_s = timing?.model_s ?? null
  task.tool_s = timing?.tool_s ?? null
  task.max_turn_s = timing?.max_turn_s ?? null
  task.child_files = gradeChildFiles(envDir)
  task.brief_mode = exists(launchFile) ? readJson(launchFile).brief_mode ?? "default" : "default"
  task.early_stop = launch.early_stop ?? null
  task.missions = listMissions(envDir)
  task.child_contracts = auditChildContracts(envDir)
  const leaks = detectLeaks(envDir)
  task.leak_evidence = leaks.confirmed
  task.leak_attempts = leaks.blocked
  task.contaminated = leaks.confirmed.length > 0
  if (evidence) task.evidence = evidence
  saveRun(run)
  appendJsonl(path.join(run.dir, "results.jsonl"), {
    ts: new Date().toISOString(),
    id,
    tier: task.tier,
    pass,
    failure: task.failure,
    elapsed_s: elapsed,
    tool_calls: tr.calls,
    decomposed: task.decomposed,
    searched: task.searched,
    contaminated: task.contaminated,
    cost_usd: tr.cost,
    early_stop: task.early_stop ?? null,
    child_contracts: task.child_contracts?.ok ?? null,
  })
  return task
}

export function listMissions(envDir) {
  const dir = path.join(envDir, "repo", "missions")
  if (!exists(dir)) return []
  try {
    return fs.readdirSync(dir).filter((f) => f.endsWith(".md")).sort()
  } catch {
    return []
  }
}

/**
 * `pab_split` implementation, also callable from inside the eval sandbox:
 * the run/task ids come from PAB_RUN / PAB_ID so the brief never leaks them.
 *
 * Every subtask is validated against the sub-mission contract. Rejected
 * subtasks are NOT written and are reported back with the exact errors, so the
 * parent can fix them and re-call. Accepted subtasks come back with a
 * ready-to-paste `subagent` prompt (goal_statement + lean_context + imports +
 * acceptance verbatim) — the parent must pass it verbatim.
 */
export function writeMissions({ runId, id, subtasks, runRoot = PATHS.runRoot }) {
  if (!runId || !id) throw new Error("no active task (PAB_RUN/PAB_ID unset)")
  const run = loadRun(runId, runRoot)
  const task = run.tasks.find((t) => t.id === id)
  if (!task) throw new Error(`unknown task ${id} in ${runId}`)
  const envDir = path.join(run.dir, id)
  const repo = path.join(envDir, "repo")
  const dir = path.join(repo, "missions")
  fs.mkdirSync(dir, { recursive: true })
  const written = []
  const missions = []
  const rejected = []
  const list = Array.isArray(subtasks) ? subtasks.slice(0, 16) : []
  list.forEach((sub, i) => {
    const v = validateMissionContract(sub, { allowedImports: task.imports })
    if (!v.ok) {
      rejected.push({
        index: i,
        errors: v.errors,
        goal_statement: String(sub?.goal_statement ?? sub?.goal ?? "").slice(0, 160),
      })
      return
    }
    const mission = v.normalized
    const slug = `${String(i + 1).padStart(2, "0")}-${safeName(mission.goal_statement.split(/[.\n:]/)[0]).slice(0, 40)}`
    const missionId = `${task.id}/${slug}`
    const file = path.join(dir, `${slug}.md`)
    const body = missionMarkdown({ missionId, mission })
    fs.writeFileSync(file, body, "utf8")
    written.push(`missions/${slug}.md`)
    missions.push({ missionId, slug, file: `missions/${slug}.md`, mission })
  })
  task.missions = listMissions(envDir)
  task.decomp_events = [
    ...(task.decomp_events ?? []),
    ...missions.map((m) => ({ tool: "pab_split", summary: `${m.missionId} :: ${m.mission.goal_statement.slice(0, 160)}` })),
    ...rejected.map((r) => ({ tool: "pab_split.rejected", summary: `#${r.index} ${r.errors.join("; ")}` })),
  ]
  task.mission_contract = {
    ok: rejected.length === 0 && written.length > 0,
    accepted: missions.length,
    rejected: rejected.length,
    fields: MISSION_FIELDS,
  }
  task.status = task.status === "pending" ? "running" : task.status
  saveRun(run)
  return {
    ok: rejected.length === 0 && written.length > 0,
    written,
    count: written.length,
    rejected,
    required_fields: MISSION_FIELDS,
    forbidden_stamp: MISSION_FORBIDDEN,
    imports_allowed: task.imports ?? [],
    acceptance_template: `cd ${repo} && lake env lean missions/<file>.lean`,
    dispatch: missions.map((m) => dispatchFor(m.missionId, m.mission, repo)),
    next_step:
      rejected.length > 0
        ? `Some subtasks were rejected. Fix the listed fields and call pab_split again. Use acceptance_template verbatim: ${`cd ${repo} && lake env lean missions/<file>.lean`}`
        : "For each entry in `dispatch`, call subagent(agent=dispatch[i].subagent.agent, description=..., prompt=dispatch[i].subagent.prompt) with the prompt VERBATIM.",
  }
}

/** Render one mission as the on-disk contract (missions/<slug>.md). */
export function missionMarkdown({ missionId, mission }) {
  const imports = (mission.imports ?? []).map(String).join(", ")
  const forbidden = (Array.isArray(mission.forbidden) ? mission.forbidden : MISSION_FORBIDDEN).map((f) => JSON.stringify(f)).join(", ")
  return `# Mission ${missionId}

## Contract

\`\`\`
goal_statement : ${String(mission.goal_statement).replace(/\n/g, "\n                 ")}
lean_context   : ${String(mission.lean_context).replace(/\n/g, "\n                 ")}
imports        : [${imports}]
acceptance     : ${mission.acceptance}
forbidden      : [${forbidden}]
\`\`\`

## Objective

prove ${missionId}: ${String(mission.goal_statement).replace(/\s+/g, " ").trim()}

## Hint

${String(mission.hint ?? "(none)")}

## Report

- status: open
- file:
- final statement:
- remaining subgoal:
`
}

// ---------------------------------------------------------------------------
// Invariants: one model, no statement/proof leaks, statements untouched
// ---------------------------------------------------------------------------

/**
 * Audit a run against the hard constraints:
 *   1. only `MODEL` may appear in any config/launch/transcript
 *   2. no reference proof from the bank may appear in any env
 *   3. the statement hash in every graded task matches secrets.json
 */
export function verifyRun(runId, runRoot = PATHS.runRoot) {
  const run = loadRun(runId, runRoot)
  const problems = []
  const modelIds = new Set()
  const MODEL_RE = /\b(?:[a-z0-9][a-z0-9_-]*)\/[A-Za-z0-9][A-Za-z0-9._-]*(?:#[A-Za-z0-9._-]+)?/g

  const scanFile = (file) => {
    let text
    try {
      text = fs.readFileSync(file, "utf8")
    } catch {
      return
    }
    for (const m of text.match(MODEL_RE) ?? []) {
      // ignore paths/urls, keep provider/model shaped tokens
      if (m.startsWith("http") || m.includes("github.com")) continue
      if (!/^(opencode-go|local08b|local4b|local27b|anthropic|openai|google|deepseek|qwen|moonshot|zhipu|xai|mistral|meta)\//.test(m)) continue
      modelIds.add(m)
    }
  }

  scanFile(path.join(run.dir, "run.json"))
  for (const task of run.tasks) {
    const envDir = path.join(run.dir, task.id)
    for (const f of ["opencode.json", ".opencode.json", "launch.json", "agent.jsonl", "env.json"]) {
      scanFile(path.join(envDir, f))
    }
    // Statements are legal only inside repo/ (Problem.lean and the agent's own
    // scratch files). Anything at env level or in run.json would be a harness leak.
    for (const f of ["env.json", "opencode.json", ".opencode.json", "secrets.json", "launch.json", "AGENT_POLICY.md"]) {
      const p2 = path.join(envDir, f)
      if (!exists(p2)) continue
      if (/theorem\s+solution/.test(fs.readFileSync(p2, "utf8"))) problems.push(`task ${task.id}: statement text in ${f}`)
    }
    const secrets = exists(path.join(envDir, "secrets.json")) ? readJson(path.join(envDir, "secrets.json")) : null
    if (secrets && (task.statement_sha256 ?? secrets.problem_statement_sha256) !== secrets.problem_statement_sha256) {
      problems.push(`task ${task.id}: statement hash drifted from build time`)
    }
    if (task.status === "passed" || task.status === "failed") {
      const file = path.join(envDir, "repo", "Problem.lean")
      const stmt = problemStatement(stripLean(fs.readFileSync(file, "utf8")))
      if (sha256(normalizeWs(stmt)) !== secrets.problem_statement_sha256) {
        problems.push(`task ${task.id}: final statement differs from secrets.json`)
      }
      if (task.commits !== 1) problems.push(`task ${task.id}: ${task.commits} commits (expected 1)`)
    }
  }

  const bad = [...modelIds].filter((m) => m !== MODEL && !m.startsWith("opencode-go/deepseek-v4.1-flash"))
  if (bad.length) problems.push(`unexpected model ids in run: ${bad.join(", ")}`)

  return {
    ok: problems.length === 0,
    run_id: run.run_id,
    model: run.model,
    model_ids_seen: [...modelIds].sort(),
    problems,
    tasks_checked: run.tasks.length,
  }
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

export function status(runId, runRoot = PATHS.runRoot) {
  const run = loadRun(runId, runRoot)
  const by = {}
  for (const t of run.tasks) {
    by[t.status] = (by[t.status] ?? 0) + 1
  }
  return {
    run_id: run.run_id,
    model: run.model,
    dir: run.dir,
    counts: by,
    total: run.tasks.length,
    passed: run.tasks.filter((t) => t.status === "passed").length,
    failed: run.tasks.filter((t) => t.status === "failed").length,
    pending: run.tasks.filter((t) => t.status === "pending").length,
    running: run.tasks.filter((t) => t.status === "running").length,
    tasks: run.tasks.map((t) => ({
      id: t.id,
      tier: t.tier,
      status: t.status,
      pass: t.pass ?? null,
      elapsed_s: t.elapsed_s ?? null,
      tool_calls: t.tool_calls ?? null,
      decomposed: t.decomposed ?? null,
      searched: t.searched ?? null,
      failure: t.failure ?? null,
    })),
  }
}

function fmt(v) {
  if (v === null || v === undefined) return "—"
  if (typeof v === "boolean") return v ? "yes" : "no"
  return String(v)
}

/** Wall-clock attribution: how much of the budget was model latency vs tools. */
export function transcriptTiming(jsonlFile) {
  if (!exists(jsonlFile)) return null
  const evs = fs
    .readFileSync(jsonlFile, "utf8")
    .split("\n")
    .filter(Boolean)
    .map((l) => {
      try {
        return JSON.parse(l)
      } catch {
        return null
      }
    })
    .filter(Boolean)
  const steps = evs.filter((e) => e.type === "step_start")
  const gaps = []
  for (const s of steps) {
    const fin = evs.find((e) => e.type === "step_finish" && e.part?.messageID === s.part?.messageID)
    if (fin) gaps.push((fin.timestamp - s.timestamp) / 1000)
  }
  const toolTimes = []
  for (const tu of evs.filter((e) => e.type === "tool_use")) {
    const st = tu.part?.state?.time
    if (st?.start && st?.end) toolTimes.push((st.end - st.start) / 1000)
  }
  const sum = (a) => a.reduce((x, y) => x + y, 0)
  return {
    turns: steps.length,
    model_s: Math.round(sum(gaps)),
    tool_s: Math.round(sum(toolTimes)),
    max_turn_s: gaps.length ? Math.round(Math.max(...gaps)) : 0,
  }
}

export function report(runId, runRoot = PATHS.runRoot) {
  const run = loadRun(runId, runRoot)
  const done = run.tasks.filter((t) => t.status === "passed" || t.status === "failed")
  const passed = done.filter((t) => t.pass)
  const rate = done.length ? ((passed.length / done.length) * 100).toFixed(0) : "0"
  const failures = {}
  for (const t of done) if (!t.pass) failures[t.failure ?? "unknown"] = (failures[t.failure ?? "unknown"] ?? 0) + 1
  const perTier = {}
  for (const t of done) {
    perTier[t.tier] = perTier[t.tier] ?? { done: 0, pass: 0 }
    perTier[t.tier].done += 1
    if (t.pass) perTier[t.tier].pass += 1
  }

  const lines = []
  lines.push(`# p2m-agent-bench report — ${run.run_id}`)
  lines.push("")
  lines.push(`- model: \`${run.model}\` (only model invoked)`)
  lines.push(`- seed: \`${run.seed}\` · sampled: ${run.tasks.length} (${run.per_tier} per tier, T1..T5)`)
  lines.push(`- timeout: ${run.timeout_s}s per problem · parallelism: ${run.jobs ?? 1}`)
  lines.push(`- pass rate: **${passed.length}/${done.length} (${rate}%)**`)
  lines.push(`- run dir: \`${run.dir}\``)
  lines.push("")
  lines.push("| id | tier | pass | elapsed_s | tool_calls | decomposed | searched | failure | early_stop |")
  lines.push("|---|---|---|---|---|---|---|---|---|")
  for (const t of run.tasks) {
    lines.push(
      `| ${t.id} | ${t.tier} | ${t.status === "pending" || t.status === "running" ? t.status : t.pass ? "PASS" : "fail"} | ` +
        `${fmt(t.elapsed_s)} | ${fmt(t.tool_calls)} | ${fmt(t.decomposed)} | ${fmt(t.searched)} | ${fmt(t.failure)} | ` +
        `${t.early_stop ? `${t.early_stop.reason}@${t.early_stop.turn}` : "—"} |`,
    )
  }
  lines.push("")
  lines.push("## Per tier")
  lines.push("")
  lines.push("| tier | done | pass |")
  lines.push("|---|---|---|")
  for (const tier of Object.keys(perTier).sort()) lines.push(`| ${tier} | ${perTier[tier].done} | ${perTier[tier].pass} |`)
  lines.push("")
  lines.push("## Failure classes")
  lines.push("")
  for (const [k, v] of Object.entries(failures).sort((a, b) => b[1] - a[1])) lines.push(`- ${k}: ${v}`)
  if (Object.keys(failures).length === 0) lines.push("- none")
  lines.push("")
  lines.push("## Notes")
  lines.push("")
  const searched = run.tasks.filter((t) => t.searched).length
  const decomp = run.tasks.filter((t) => t.decomposed).length
  const idSearch = run.tasks.filter((t) => t.identity_search).length
  const denials = run.tasks.reduce((a, t) => a + (t.guard_denials ?? 0), 0)
  const contaminated = run.tasks.filter((t) => t.contaminated)
  lines.push(`- agents that searched the web: ${searched}/${run.tasks.length} (identity-ish queries: ${idSearch})`)
  lines.push(`- agents that decomposed: ${decomp}/${run.tasks.length}`)
  lines.push(`- guard denials: ${denials}`)
  lines.push(
    `- contaminated (agent reached for the answer): ${contaminated.length}` +
      (contaminated.length ? ` — ${contaminated.map((t) => `${t.id} [${t.leak_evidence.join(", ")}]`).join("; ")}` : ""),
  )
  lines.push(`- total cost: $${run.tasks.reduce((a, t) => a + (t.cost_usd ?? 0), 0).toFixed(4)}`)
  lines.push("")
  // ---- wall clock vs generation vs tools (the starvation question) ----------
  const timed = run.tasks.filter((t) => t.model_s !== null && t.model_s !== undefined)
  if (timed.length) {
    lines.push("## Wall clock: generation vs tools")
    lines.push("")
    lines.push("| id | tier | wall_s | model_s | tool_s | turns | max_turn_s | calls | prompt_tok | completion_tok |")
    lines.push("|---|---|---|---|---|---|---|---|---|---|")
    for (const t of timed) {
      const modelPct = t.elapsed_s ? Math.round((100 * (t.model_s ?? 0)) / t.elapsed_s) : 0
      lines.push(
        `| ${t.id} | ${t.tier} | ${fmt(t.elapsed_s)} | ${fmt(t.model_s)} (${modelPct}%) | ${fmt(t.tool_s)} | ${fmt(t.turns)} | ${fmt(t.max_turn_s)} | ` +
          `${fmt(t.tool_calls)} | ${fmt(t.tokens?.input)} | ${fmt(t.tokens?.output)} |`,
      )
    }
    const tot = (k) => timed.reduce((a, t) => a + (Number(t[k]) || 0), 0)
    lines.push("")
    lines.push(
      `Totals: wall ${Math.round(tot("elapsed_s"))}s · model ${Math.round(tot("model_s"))}s (${Math.round(
        (100 * tot("model_s")) / Math.max(1, tot("elapsed_s")),
      )}%) · tools ${Math.round(tot("tool_s"))}s · turns ${tot("turns")} · calls ${tot("tool_calls")}`,
    )
    lines.push("")
  }

  // ---- watchdog + child-contract audit ------------------------------------
  const stopped = run.tasks.filter((t) => t.early_stop)
  const audited = run.tasks.filter((t) => t.child_contracts?.children?.length)
  if (stopped.length || audited.length) {
    lines.push("## Watchdog & child-mission contract")
    lines.push("")
    if (stopped.length) {
      lines.push("| id | reason | turn | elapsed_s |")
      lines.push("|---|---|---|---|")
      for (const t of stopped) lines.push(`| ${t.id} | ${t.early_stop.reason} | ${t.early_stop.turn} | ${t.early_stop.elapsed} |`)
      lines.push("")
    } else {
      lines.push("- early stops: none")
      lines.push("")
    }
    for (const t of audited) {
      const cc = t.child_contracts
      lines.push(`- **${t.id}** child contract: ${cc.ok ? "ok" : "VIOLATED"} — ${cc.reason}`)
      for (const c of cc.children) {
        lines.push(
          `  - \`${c.session}\` "${c.title}": contract=${c.contract ? "yes" : `no (missing ${c.missing.join(", ")})`}, ` +
            `source_hunt=${c.source_hunt}, source_attempts=${c.source_attempts}, denials=${c.denials}`,
        )
      }
    }
    lines.push("")
  }

  // ---- forced decomposition trace -----------------------------------------
  const forced = run.tasks.filter((t) => t.brief_mode === "forced")
  if (forced.length) {
    lines.push("## Forced decomposition (mechanism check)")
    lines.push("")
    lines.push("| id | split_calls | subagent | team_send | missions | child .lean | child compiles |")
    lines.push("|---|---|---|---|---|---|---|")
    for (const t of forced) {
      const c = t.tools ?? {}
      const kids = t.child_files ?? []
      lines.push(
        `| ${t.id} | ${c.pab_split ?? 0} | ${c.subagent ?? c.task ?? 0} | ${c.team_send ?? 0} | ${(t.missions ?? []).length} | ` +
          `${kids.length} | ${kids.filter((k) => k.ok).length}/${kids.length} |`,
      )
    }
    lines.push("")
    for (const t of forced) {
      lines.push(`### ${t.id} — brief=${t.brief_mode}, ${t.pass ? "PASS" : t.failure ?? t.status}`)
      lines.push("")
      if (t.decomp_events?.length) {
        lines.push(`- decomposition events: ${t.decomp_events.map((e) => `${e.tool}(${e.summary.slice(0, 70)})`).join("; ")}`)
      } else lines.push("- decomposition events: none")
      if (t.missions?.length) lines.push(`- missions written: ${t.missions.join(", ")}`)
      for (const k of t.child_files ?? []) {
        lines.push(`- child file \`${k.file}\`: ${k.ok ? "compiles" : "does not compile"}${k.sorry ? " (sorry)" : ""}`)
        if (!k.ok && k.errors?.length) lines.push(`  - ${k.errors[0]}`)
      }
      lines.push("")
    }
  }

  lines.push("## Per problem detail")
  lines.push("")
  for (const t of run.tasks) {
    lines.push(`### ${t.id} (${t.tier}) — ${t.pass ? "PASS" : (t.failure ?? t.status)}`)
    lines.push("")
    lines.push(`- transcript: \`${path.join(run.dir, t.id, "agent.jsonl")}\``)
    lines.push(`- guard log: \`${path.join(run.dir, t.id, "guard.log")}\``)
    const timing = transcriptTiming(path.join(run.dir, t.id, "agent.jsonl"))
    if (timing) {
      lines.push(
        `- wall clock: agent ${fmt(t.elapsed_s)}s = model ${timing.model_s}s (${timing.turns} turns, max ${timing.max_turn_s}s) + tools ${timing.tool_s}s`,
      )
    }
    if (t.tools) lines.push(`- tools: ${Object.entries(t.tools).map(([k, v]) => `${k}×${v}`).join(", ")}`)
    if (t.early_stop) lines.push(`- EARLY STOP: ${t.early_stop.reason} at turn ${t.early_stop.turn} (${t.early_stop.elapsed}s)`)
    if (t.missions?.length) lines.push(`- missions: ${t.missions.join(", ")}`)
    if (t.contaminated) lines.push(`- CONTAMINATED: ${t.leak_evidence.join(", ")}`)
    if (t.web_queries?.length) lines.push(`- web queries: ${t.web_queries.map((q) => `"${q}"`).join(", ")}`)
    if (t.grade?.errors?.length) lines.push(`- last errors: ${t.grade.errors.map((e) => `\`${e}\``).join(" ")}`)
    lines.push("")
  }
  const md = lines.join("\n") + "\n"
  const file = path.join(run.dir, "report.md")
  fs.writeFileSync(file, md, "utf8")
  return { file, markdown: md, summary: { run_id: run.run_id, passed: passed.length, done: done.length, rate: `${rate}%`, failures } }
}
