#!/usr/bin/env node
/**
 * p2m-agent-bench CLI — the out-of-process driver for the same core the plugin
 * tools call. Used when the harness session cannot hot-load a new plugin.
 *
 *   core.mjs  : sampling, env build, launch, grade, report
 *   index.ts  : pab_* tools (pab_run, pab_next, pab_finish, pab_status, pab_report, pab_split)
 *   cli.mjs   : this file — run | next | launch | finish | exec | status | report | split
 *
 *   node cli.mjs run    --tiers T1 --per-tier 1 --seed pilot-1
 *   node cli.mjs next   --run <run>
 *   node cli.mjs launch --run <run> --id <id> --timeout 600
 *   node cli.mjs finish --run <run> --id <id>
 *   node cli.mjs exec   --run <run> --jobs 3 --timeout 600
 *   node cli.mjs status --run <run>
 *   node cli.mjs report --run <run>
 *   node cli.mjs split  --run <run> --id <id> --goal "..." [--goal "..."]
 */

import fs from "node:fs"
import path from "node:path"

import {
  MODEL,
  PATHS,
  analyzeTranscript,
  auditChildContracts,
  claimNext,
  claimTask,
  createRun,
  createWatchdog,
  finishTask,
  launchTask,
  loadRun,
  parseWatchdogLine,
  report,
  patchEnvConfig,
  restoreRepo,
  saveRun,
  status,
  taskBrief,
  verifyRun,
  watchdogConfig,
  writeMissions,
} from "./core.mjs"

function args(argv) {
  const out = { _: [] }
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    if (a.startsWith("--")) {
      const key = a.slice(2)
      const next = argv[i + 1]
      if (next === undefined || next.startsWith("--")) out[key] = true
      else {
        if (out[key] === undefined) out[key] = next
        else out[key] = [].concat(out[key], next)
        i++
      }
    } else out._.push(a)
  }
  return out
}

function print(obj) {
  process.stdout.write(JSON.stringify(obj, null, 2) + "\n")
}

function die(msg) {
  process.stderr.write(`pab: ${msg}\n`)
  process.exit(2)
}

function mustModel(model) {
  const resolved = String(model ?? MODEL)
  if (resolved !== MODEL) die(`refusing model "${resolved}": only ${MODEL} is allowed`)
  return resolved
}

/** `--no-watchdog` / `--repeat-tool 5` / `--idle-turns 8` → watchdogConfig overrides. */
function watchdogOverrides(cmd) {
  const off = cmd["no-watchdog"] === true || String(cmd.watchdog ?? "") === "off"
  const out = off ? { enabled: false } : {}
  const num = (flag, key) => {
    if (cmd[flag] === undefined || cmd[flag] === true) return
    const n = Number(cmd[flag])
    if (Number.isFinite(n) && n > 0) out[key] = n
  }
  num("repeat-tool", "repeatTool")
  num("guard-deny", "guardDeny")
  num("idle-turns", "idleTurns")
  num("repeat-error", "repeatError")
  num("poll-ms", "pollMs")
  num("kill-grace-ms", "killGraceMs")
  return out
}

const cmd = args(process.argv.slice(2))
const sub = cmd._[0]

async function main() {
  switch (sub) {
    case "run": {
      const model = mustModel(cmd.model)
      const out = createRun({
        tiers: cmd.tiers ? String(cmd.tiers).split(",") : undefined,
        perTier: cmd["per-tier"] ? Number(cmd["per-tier"]) : 2,
        seed: cmd.seed ? String(cmd.seed) : "pab-1",
        model,
        timeoutS: cmd.timeout ? Number(cmd.timeout) : undefined,
        runId: cmd.run ? String(cmd.run) : undefined,
        jobs: cmd.jobs ? Number(cmd.jobs) : 1,
        briefMode: cmd.brief ? String(cmd.brief) : "default",
      })
      print({
        ok: true,
        run_id: out.run_id,
        dir: out.dir,
        model: out.model,
        seed: out.seed,
        ids: out.ids,
        tasks: out.tasks.map((t) => ({ id: t.id, tier: t.tier, imports: t.imports, commits: t.commits })),
      })
      return
    }

    case "next": {
      const runId = String(cmd.run ?? "")
      if (!runId) die("--run is required")
      const { run, task } = claimNext(runId)
      if (!task) {
        print({ ok: true, run_id: runId, task: null, reason: "no pending task" })
        return
      }
      print({
        ok: true,
        run_id: runId,
        task: {
          id: task.id,
          tier: task.tier,
          imports: task.imports,
          env_dir: task.env_dir,
          repo: task.repo,
          timeout_s: run.timeout_s,
          model: run.model,
        },
        brief: taskBrief({ tier: task.tier, imports: task.imports }),
      })
      return
    }

    case "launch": {
      const runId = String(cmd.run ?? "")
      const id = String(cmd.id ?? "")
      if (!runId || !id) die("--run and --id are required")
      mustModel(cmd.model)
      const run = loadRun(runId)
      claimTask(runId, id)
      const task = run.tasks.find((t) => t.id === id)
      const timeoutS = Number(cmd.timeout ?? run.timeout_s)
      const res = await launchTask({
        runDir: run.dir,
        task,
        timeoutS,
        briefMode: cmd.brief ? String(cmd.brief) : "default",
        watchdog: watchdogOverrides(cmd),
      })
      print({ ok: true, ...res, analysis: analyzeTranscript(res.agent_jsonl), early_stop: res.early_stop })
      return
    }

    case "finish": {
      const runId = String(cmd.run ?? "")
      const id = String(cmd.id ?? "")
      if (!runId || !id) die("--run and --id are required")
      const task = finishTask({ runId, id, evidence: cmd.evidence ? String(cmd.evidence) : undefined })
      print({
        ok: true,
        id: task.id,
        tier: task.tier,
        pass: task.pass,
        failure: task.failure,
        elapsed_s: task.elapsed_s,
        tool_calls: task.tool_calls,
        decomposed: task.decomposed,
        searched: task.searched,
        grade: task.grade,
      })
      return
    }

    case "exec": {
      const runId = String(cmd.run ?? "")
      if (!runId) die("--run is required")
      mustModel(cmd.model)
      const run = loadRun(runId)
      const jobs = Math.max(1, Number(cmd.jobs ?? 1))
      const timeoutS = Number(cmd.timeout ?? run.timeout_s)
      const briefMode = cmd.brief ? String(cmd.brief) : "default"
      const only = cmd.ids ? String(cmd.ids).split(",") : null

      let targets = []
      if (only) {
        for (const id of only) {
          claimTask(runId, id)
          targets.push(loadRun(runId).tasks.find((t) => t.id === id))
        }
      }
      // Otherwise every worker claims lazily (claimNext), so a crash leaves at
      // most `jobs` tasks stuck in "running" and everything else resumable.
      const lazy = !only

      const log = path.join(run.dir, "exec.log")
      const say = (o) => {
        const line = JSON.stringify(o)
        fs.appendFileSync(log, line + "\n")
        process.stdout.write(line + "\n")
      }
      say({ ts: new Date().toISOString(), event: "exec.start", run_id: runId, jobs, timeout_s: timeoutS, model: MODEL, count: lazy ? -1 : targets.length })

      let cursor = 0
      const worker = async (slot) => {
        for (;;) {
          let task
          if (lazy) {
            const got = claimNext(runId)
            task = got.task
            if (!task) return
          } else {
            const i = cursor++
            if (i >= targets.length) return
            task = targets[i]
          }
          say({ ts: new Date().toISOString(), event: "task.start", slot, id: task.id, tier: task.tier })
          const launched = await launchTask({
            runDir: run.dir,
            task,
            timeoutS,
            briefMode,
            watchdog: watchdogOverrides(cmd),
          })
          const fin = finishTask({ runId, id: task.id })
          say({
            ts: new Date().toISOString(),
            event: "task.done",
            slot,
            id: task.id,
            tier: task.tier,
            pass: fin.pass,
            failure: fin.failure,
            elapsed_s: fin.elapsed_s,
            tool_calls: fin.tool_calls,
            decomposed: fin.decomposed,
            searched: fin.searched,
            timed_out: launched.timed_out,
            early_stop: launched.early_stop ?? null,
            child_contracts: fin.child_contracts?.ok ?? null,
          })
        }
      }
      const workers = lazy ? jobs : Math.min(jobs, targets.length)
      await Promise.all(Array.from({ length: Math.max(1, workers) }, (_, s) => worker(s)))
      const st = status(runId)
      say({ ts: new Date().toISOString(), event: "exec.end", run_id: runId, ...st })
      print({ ok: true, run_id: runId, counts: st.counts, passed: st.passed, failed: st.failed })
      return
    }

    case "status": {
      print(status(String(cmd.run ?? "")))
      return
    }

    case "report": {
      const r = report(String(cmd.run ?? ""))
      print({ ok: true, file: r.file, summary: r.summary })
      process.stdout.write("\n" + r.markdown)
      return
    }

    case "split": {
      const runId = String(cmd.run ?? process.env.PAB_RUN ?? "")
      const id = String(cmd.id ?? process.env.PAB_ID ?? "")
      if (!runId || !id) die("--run/--id are required (or run inside a task)")
      // Two ways in: --mission <file.json> (array of full contracts) or the
      // legacy per-field flags (which must still satisfy the contract).
      let subtasks = []
      if (cmd.mission) {
        const file = String(cmd.mission)
        const parsed = JSON.parse(fs.readFileSync(file, "utf8"))
        subtasks = Array.isArray(parsed) ? parsed : Array.isArray(parsed.subtasks) ? parsed.subtasks : []
      } else if (cmd.goal) {
        subtasks = [].concat(cmd.goal).map((g) => ({ goal_statement: String(g) }))
      }
      const res = writeMissions({ runId, id, subtasks })
      print(res)
      if (!res.ok) process.exit(3)
      return
    }

    case "children": {
      // Audit the child sessions of a graded task against the mission contract.
      const runId = String(cmd.run ?? "")
      const id = String(cmd.id ?? "")
      if (!runId || !id) die("--run and --id are required")
      const run = loadRun(runId)
      const res = auditChildContracts(path.join(run.dir, id))
      print(res)
      if (res.ok === false) process.exit(3)
      return
    }

    case "watchdog": {
      // Dry-run the watchdog thresholds against an existing transcript, so a
      // threshold change can be evaluated without burning a real run. The two
      // sources are merged by timestamp, exactly like the live tailer sees them.
      const runId = String(cmd.run ?? "")
      const id = String(cmd.id ?? "")
      if (!runId || !id) die("--run and --id are required")
      const run = loadRun(runId)
      const envDir = path.join(run.dir, id)
      const cfg = watchdogConfig(process.env, {})
      const wd = createWatchdog({ config: cfg, taskDir: path.join(envDir, "repo") })
      const merged = []
      const agentFile = path.join(envDir, "agent.jsonl")
      if (fs.existsSync(agentFile)) {
        for (const line of fs.readFileSync(agentFile, "utf8").split("\n")) {
          const ev = parseWatchdogLine(line)
          if (!ev) continue
          merged.push({ t: Number(ev.timestamp ?? 0), ev, src: "agent.jsonl" })
        }
      }
      const guardFile = path.join(envDir, "guard.log")
      if (fs.existsSync(guardFile)) {
        for (const line of fs.readFileSync(guardFile, "utf8").split("\n")) {
          const ev = parseWatchdogLine(line)
          if (!ev) continue
          const t = Date.parse(String(ev.ts ?? "")) || 0
          merged.push({ t, ev, src: "guard.log" })
        }
      }
      merged.sort((a, b) => a.t - b.t)
      let stop = null
      for (const m of merged) {
        stop = wd.feed(m.ev, m.src)
        if (stop) break
      }
      print({ ok: true, run_id: runId, id, config: cfg, events: merged.length, snapshot: wd.snapshot(), would_stop: stop })
      return
    }

    case "reset": {
      // Unstick tasks left in "running" by a dead driver (crash recovery).
      const runId = String(cmd.run ?? "")
      if (!runId) die("--run is required")
      const run = loadRun(runId)
      const claimDir = path.join(run.dir, ".claims")
      const only = cmd.ids ? String(cmd.ids).split(",") : null
      let cleared = 0
      for (const t of run.tasks) {
        if (only ? !only.includes(t.id) : t.status !== "running") continue
        if (t.status === "pending") continue
        if (cmd["keep-passed"] && t.pass) continue
        t.status = "pending"
        t.started_at = null
        t.pass = null
        t.failure = null
        cleared += 1
        const claim = path.join(claimDir, `${t.id}.claim`)
        if (fs.existsSync(claim)) fs.rmSync(claim)
        if (cmd.restore) {
          patchEnvConfig(path.join(run.dir, t.id))
          restoreRepo(path.join(run.dir, t.id))
          for (const f of ["agent.jsonl", "agent.err.log", "guard.log", "launch.json"]) {
            const p2 = path.join(run.dir, t.id, f)
            if (fs.existsSync(p2)) fs.rmSync(p2)
          }
        }
      }
      saveRun(run)
      print({ ok: true, run_id: runId, cleared })
      return
    }

    case "recheck": {
      // Re-grade every task in place (no relaunch) — refreshes transcripts-derived
      // fields and the leak audit after a policy change.
      const runId = String(cmd.run ?? "")
      if (!runId) die("--run is required")
      const run = loadRun(runId)
      const out = []
      for (const t of run.tasks) {
        if (t.status === "pending" || t.status === "running") continue
        const fin = finishTask({ runId, id: t.id })
        out.push({ id: fin.id, pass: fin.pass, failure: fin.failure, contaminated: fin.contaminated })
      }
      print({ ok: true, run_id: runId, tasks: out })
      return
    }

    case "verify": {
      print(verifyRun(String(cmd.run ?? "")))
      return
    }

    case "paths": {
      print({ ok: true, model: MODEL, paths: PATHS })
      return
    }

    default:
      die(`unknown subcommand ${sub ?? "(none)"}`)
  }
}

main().catch((e) => {
  process.stderr.write(`pab: ${e?.stack ?? e}\n`)
  process.exit(1)
})
