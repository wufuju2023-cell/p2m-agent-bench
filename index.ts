import { Plugin } from "@opencode/plugin"

import {
  MODEL,
  PATHS,
  analyzeGuard,
  analyzeTranscript,
  claimNext,
  claimTask,
  createRun,
  finishTask,
  launchTask,
  loadRun,
  report,
  status,
  taskBrief,
  writeMissions,
} from "./core.mjs"

/**
 * p2m-agent-bench — the "agent-vs-prove2me" harness.
 *
 * Samples blind problems from the local bank, materialises one sandboxed Lean
 * project per problem, launches a free-form OpenCode agent (no MCTS, no value
 * head) and grades the result. Every tool returns compact JSON.
 *
 * The heavy lifting lives in `core.mjs` so the exact same code can be driven
 * out of process by `cli.mjs` (which is how batch runs are executed).
 */

type Options = {
  runRoot?: string
  bankDir?: string
  timeoutS?: number
  jobs?: number
}

function json(value: unknown): { content: string } {
  return { content: JSON.stringify(value) }
}

function fail(error: unknown): { content: string } {
  const message = error instanceof Error ? error.message : String(error)
  return json({ ok: false, error: message })
}

function str(value: unknown): string {
  return typeof value === "string" ? value : ""
}

export default Plugin.define({
  id: "p2m-agent-bench",
  async setup(ctx) {
    const options = (ctx.options ?? {}) as Options
    const runRoot = str(options.runRoot) || PATHS.runRoot
    const bankDir = str(options.bankDir) || PATHS.bank
    const defaultTimeout = Number(options.timeoutS ?? 600)
    void options.jobs

    await ctx.tool.transform((editor) => {
      editor.namespace({
        name: "pab",
        description: "p2m-agent-bench: sample blind Lean problems, run an agent, grade it (no MCTS/value head).",
      })

      editor.add({
        name: "run",
        description:
          "Create a benchmark run: seeded sample of `per_tier` problems from each requested tier (default 2 per T1..T5 = 10), " +
          "materialise one blind env per problem (theorem renamed to `solution`, no docstring/namespace, one-commit git, " +
          "secrets.json, project opencode.json with eval-blind permissions and the p2m-eval agent pinned to " +
          MODEL + "), and write run.json. Returns the run id and the sampled ids.",
        input: {
          type: "object",
          properties: {
            tiers: { type: "array", items: { type: "string" }, description: "Tiers to sample, e.g. [\"T1\",\"T2\"]." },
            per_tier: { type: "integer", description: "Problems per tier (default 2)." },
            seed: { type: "string", description: "Sampling seed (deterministic)." },
            model: { type: "string", description: `Must be ${MODEL}; anything else is refused.` },
            timeout_s: { type: "integer", description: "Per-problem wall clock in seconds (default 600)." },
          },
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_run", codemode: false },
        execute: async (input) => {
          try {
            const a = (input ?? {}) as Record<string, unknown>
            const res = createRun({
              ...(Array.isArray(a.tiers) ? { tiers: a.tiers.map(String) } : {}),
              ...(typeof a.per_tier === "number" ? { perTier: a.per_tier } : {}),
              ...(typeof a.seed === "string" ? { seed: a.seed } : {}),
              ...(typeof a.model === "string" ? { model: a.model } : {}),
              ...(typeof a.timeout_s === "number" ? { timeoutS: a.timeout_s } : {}),
              runRoot,
              bankDir,
            })
            return json({
              ok: true,
              run_id: res.run_id,
              dir: res.dir,
              model: res.model,
              seed: res.seed,
              count: res.ids.length,
              ids: res.ids,
              tiers: res.tasks.map((t: { id: string; tier: string }) => ({ id: t.id, tier: t.tier })),
            })
          } catch (error) {
            return fail(error)
          }
        },
      })

      editor.add({
        name: "next",
        description:
          "Claim the next pending problem of a run and return its env dir plus the exact task brief to hand to the agent. " +
          "Atomic under concurrent callers (exclusive-create claim file).",
        input: {
          type: "object",
          properties: { run: { type: "string", description: "Run id from pab_run." } },
          required: ["run"],
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_next", codemode: false },
        execute: async (input) => {
          try {
            const { run, task } = claimNext(str((input as { run?: unknown })?.run), runRoot)
            if (!task) return json({ ok: true, run_id: run.run_id, task: null, reason: "no pending task" })
            return json({
              ok: true,
              run_id: run.run_id,
              task: {
                id: task.id,
                tier: task.tier,
                imports: task.imports,
                env_dir: task.env_dir,
                repo: task.repo,
                model: run.model,
                timeout_s: run.timeout_s,
              },
              brief: taskBrief({ tier: task.tier, imports: task.imports }),
            })
          } catch (error) {
            return fail(error)
          }
        },
      })

      editor.add({
        name: "finish",
        description:
          "Grade one finished problem: `lake env lean Problem.lean` from the project root, no sorry/admit, statement unchanged " +
          "(sha256 against secrets.json). Records pass/fail, elapsed, tool-call count, decomposition events, web-search usage " +
          "and the guard denial count.",
        input: {
          type: "object",
          properties: {
            run: { type: "string", description: "Run id." },
            id: { type: "string", description: "Problem id inside the run." },
            evidence: { type: "string", description: "Optional free-form note stored with the result." },
          },
          required: ["run", "id"],
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_finish", codemode: false },
        execute: async (input) => {
          try {
            const a = (input ?? {}) as Record<string, unknown>
            const task = finishTask({
              runId: str(a.run),
              id: str(a.id),
              ...(typeof a.evidence === "string" ? { evidence: a.evidence } : {}),
              runRoot,
            })
            return json({
              ok: true,
              id: task.id,
              tier: task.tier,
              pass: task.pass,
              failure: task.failure,
              elapsed_s: task.elapsed_s,
              tool_calls: task.tool_calls,
              decomposed: task.decomposed,
              searched: task.searched,
              guard_denials: task.guard_denials,
              grade: task.grade,
            })
          } catch (error) {
            return fail(error)
          }
        },
      })

      editor.add({
        name: "status",
        description: "Counts by status, per-task progress and pass rate for one run. Compact JSON.",
        input: {
          type: "object",
          properties: { run: { type: "string", description: "Run id." } },
          required: ["run"],
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_status", codemode: false },
        execute: async (input) => {
          try {
            return json({ ok: true, ...status(str((input as { run?: unknown })?.run), runRoot) })
          } catch (error) {
            return fail(error)
          }
        },
      })

      editor.add({
        name: "report",
        description:
          "Write and return the Markdown capability table for a run (id, tier, pass, elapsed, tool calls, decomposed, searched, " +
          "failure class) plus per-tier and per-problem detail. Writes <run>/report.md.",
        input: {
          type: "object",
          properties: { run: { type: "string", description: "Run id." } },
          required: ["run"],
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_report", codemode: false },
        execute: async (input) => {
          try {
            const res = report(str((input as { run?: unknown })?.run), runRoot)
            return json({ ok: true, file: res.file, summary: res.summary, markdown: res.markdown })
          } catch (error) {
            return fail(error)
          }
        },
      })

      // Blind-safe recorder for the sandboxed agent. It writes mission files
      // under <env>/repo/missions/ and records the decomposition event; it has
      // no access to the bank, so it cannot leak a reference proof.
      // Every subtask is validated against the sub-mission contract; accepted
      // ones come back with a ready-to-paste `subagent` prompt.
      editor.add({
        name: "split",
        description:
          "Register child missions for the current problem. Each subtask is a CONTRACT and must carry ALL FOUR fields: " +
          "goal_statement (the exact Lean goal/type to prove), lean_context (variables, hypotheses, open namespaces, imports), " +
          "imports (array; subset of Problem.lean's imports), acceptance (exactly `cd <project> && lake env lean <file>.lean`). " +
          "Submissions are REJECTED if a field is missing or the text asks anyone to locate/search the original source, the " +
          "prove2me/formalpedia bank, or Solutions/. Accepted missions return `dispatch[i].subagent.prompt`, which embeds all " +
          "four fields verbatim — pass it to `subagent` VERBATIM. Takes run/id from the sandbox env (PAB_RUN/PAB_ID).",
        input: {
          type: "object",
          properties: {
            subtasks: {
              type: "array",
              maxItems: 16,
              items: {
                type: "object",
                properties: {
                  goal_statement: { type: "string", description: "EXACT Lean goal/type the child must prove, e.g. `∀ i, p.eval (xs i) = fs i`." },
                  lean_context: {
                    type: "string",
                    description: "Surrounding context: binders/variables, hypotheses, `open` namespaces, imports being used.",
                  },
                  imports: {
                    type: "array",
                    items: { type: "string" },
                    description: "Allowed imports only (must be a subset of the imports already in Problem.lean).",
                  },
                  acceptance: {
                    type: "string",
                    description: "Exact verification command: `cd <project> && lake env lean <file>.lean`.",
                  },
                  forbidden: {
                    type: "array",
                    items: { type: "string" },
                    description: "Forbidden instructions (default: locate the source proof / search prove2me/formalpedia / read Solutions/).",
                  },
                  hint: { type: "string", description: "Optional hint or plan fragment." },
                },
                required: ["goal_statement", "lean_context", "imports", "acceptance"],
                additionalProperties: false,
              },
            },
            run: { type: "string", description: "Optional run id (defaults to PAB_RUN)." },
            id: { type: "string", description: "Optional problem id (defaults to PAB_ID)." },
          },
          required: ["subtasks"],
          additionalProperties: false,
        },
        options: { namespace: "pab", permission: "pab_split", codemode: false },
        execute: async (input) => {
          try {
            const a = (input ?? {}) as Record<string, unknown>
            const raw = Array.isArray(a.subtasks) ? a.subtasks : []
            const res = writeMissions({
              runId: str(a.run) || String(process.env.PAB_RUN ?? ""),
              id: str(a.id) || String(process.env.PAB_ID ?? ""),
              subtasks: raw.map((s) => {
                const r = (s ?? {}) as Record<string, unknown>
                return {
                  goal_statement: str(r.goal_statement),
                  lean_context: str(r.lean_context),
                  imports: Array.isArray(r.imports) ? r.imports.map(String) : r.imports,
                  acceptance: str(r.acceptance),
                  ...(Array.isArray(r.forbidden) ? { forbidden: r.forbidden.map(String) } : {}),
                  ...(typeof r.hint === "string" ? { hint: r.hint } : {}),
                }
              }),
              runRoot,
            })
            return json(res)
          } catch (error) {
            return fail(error)
          }
        },
      })
    })

    // Convenience for the harness operator: launching and grading from inside
    // a session is possible, but batch runs use cli.mjs.
    void launchTask
    void loadRun
    void analyzeTranscript
    void analyzeGuard

    console.log(`[p2m-agent-bench] loaded · model=${MODEL} · runRoot=${runRoot} · bank=${bankDir} · timeout=${defaultTimeout}s`)
  },
})
