# p2m-agent-bench

The **agent-vs-prove2me** harness: sample blind Lean problems from the local
prove2me/formalpedia bank, materialise one sandboxed OpenCode project per
problem, let a free-form agent (`opencode-go/deepseek-v4.1-flash#max`) try to
prove it, then grade with `lake env lean Problem.lean` + no-`sorry` +
statement-unchanged.

No MCTS, no value head, no tactic-level oracle — this is the plain agentic
baseline that the later training plugin is measured against.

## Files

| file | role |
|---|---|
| `core.mjs` | sampling, env materialisation, launch, watchdog, contract, grade, reporting (node stdlib only) |
| `cli.mjs` | out-of-process driver — same code the tools call |
| `index.ts` | `pab_*` tools (`Plugin.define`, OpenCode V2) |
| `selftest.mjs` | builds one env without an agent and asserts the wiring + the mission contract |
| `tests/` | unit tests: `watchdog.test.mjs`, `contract.test.mjs` (`npm test`) |

## Layout of a run

```
./eval/runs/<run_id>/
  run.json                      # tasks, seed, model, timeout
  results.jsonl                 # one line per graded task
  exec.log                      # driver events (start/done, per slot)
  report.md                     # capability table (pab_report)
  .claims/<id>.claim            # atomic claim files
  <id>/                         # one blind env per problem
    repo/
      Problem.lean              # `theorem solution ... := by -- TODO`
      README.md
      lakefile.toml lean-toolchain lake-manifest.json .lake/  # 4.33.1 + pinned Mathlib
      .git                      # exactly one commit
      missions/                 # created by pab_split
    opencode.json .opencode.json # eval-blind permissions, p2m-eval agent, model pinned
    secrets.json                # statement sha256 + content-filter shingles (0600)
    env.json
    agent.jsonl                 # `opencode run --format json` transcript
    agent.err.log
    guard.log                   # p2m-guard L2 slice for this env
    launch.json                 # timing, timeout flag, exact brief
```

## Sub-mission contract (forced decomposition)

A free-form split used to produce children like *"locate the original
source/proof of X"* — unprovable, and it died on guard-denied reads. `pab_split`
now enforces a contract on every subtask:

```
goal_statement : <the exact Lean goal/type to prove>
lean_context   : <variables, hypotheses, open namespaces, imports>
imports        : [..]           # allowed imports only
acceptance     : cd <project> && lake env lean <file>   # exact command
forbidden      : ["locate the source proof", "search prove2me/formalpedia", "read Solutions/"]
```

- The four fields are **hard-required**; `forbidden` is stamped when omitted.
- `imports` must be a subset of the imports already in `Problem.lean`.
- `acceptance` must literally match `^cd … && lake env lean …\.lean$`.
- Any text that asks to locate/search the source, the prove2me/formalpedia
  bank, or `Solutions/` is rejected (`SOURCE_HUNT_PATTERNS`) — including
  "find any equivalent lemma" and "where does this theorem come from".
- Rejected subtasks are **not written**; `pab_split` returns
  `{ok:false, rejected:[{index, errors}]}` so the parent can fix and re-call.

Accepted missions come back as `dispatch[i]`:

```json
{"mission_id":"<id>/01-…","objective":"prove <mission_id>: <goal_statement>",
 "subagent":{"agent":"general","description":"…","prompt":"…"},"team_send":{…}}
```

`dispatch[i].subagent.prompt` embeds all four fields **verbatim** plus the
objective for the child's `goal` tool; the brief tells the parent to call
`subagent` with that prompt **verbatim** (no paraphrasing). `finish` re-reads the
child sessions from the OpenCode store (`~/.opencode2/share/opencode/opencode.db`)
and stores `task.child_contracts` = per child: which fields landed in its first
prompt, whether it hunted the source, how many denials it ate.

## Watchdog (early stop)

`launchTask` tails `<env>/agent.jsonl` + `<env>/guard.log` while the session
runs and kills the process group when the session is provably useless:

| rule | default | meaning |
|---|---|---|
| `WATCHDOG_REPEAT_TOOL` | 5 | consecutive identical tool calls (tool + normalized input) |
| `WATCHDOG_GUARD_DENY` | 3 | consecutive guard denials on the same resource (path root, or the tool when no path) |
| `WATCHDOG_IDLE_TURNS` | 8 | turns with no file mtime change in the project **and** no new assistant tokens |
| `WATCHDOG_REPEAT_ERROR` | 4 | the same compiler error (path/line-insensitive) N compile attempts in a row |

Also `WATCHDOG_POLL_MS` (500), `WATCHDOG_KILL_GRACE_MS` (10000), `WATCHDOG=off`.
Kill is graceful: SIGTERM to the process group, SIGKILL after the grace period;
nothing in the run dir is removed. The decision is written to
`<env>/watchdog.jsonl` and `launch.json`, and lands in the result as
`early_stop: {reason, turn, elapsed}` (failure class `early_stop`).

```bash
node cli.mjs exec   --run <run> --jobs 2 --brief forced      # watchdog on
node cli.mjs exec   --run <run> --no-watchdog                # off
node cli.mjs exec   --run <run> --idle-turns 4 --guard-deny 2
node cli.mjs watchdog --run <run> --id <id>                  # replay a transcript against the thresholds
node cli.mjs children --run <run> --id <id>                  # audit child prompts against the contract
```

## Grading

`pass ⇔ lake env lean Problem.lean` exits 0 **and** no `sorry`/`admit`
**and** the sha256 of the statement (normalised, comment/string-stripped)
equals `secrets.json:problem_statement_sha256`.

Failure classes: `timeout` · `compile_error` · `wrong_statement` · `sorry` ·
`gave_up` · `decomposed_unfinished` · `early_stop` · `grade_timeout`.

## Isolation

- the Lean project is **private to the run dir**; Mathlib is path-required from
  `~/lean-4.28-reap/mathlib4-0df444a` and `.lake/packages` is symlinked to
  that checkout's already-built trees, so nothing is written under
  `~/lean-4.28-reap` and nothing is rebuilt or downloaded per problem.
- `guard/l0l1/make_env.py` is reused unchanged for L0 sanitisation (theorem
  renamed to `solution`, docstring/namespace/`context_pre` stripped, leak
  guards, one-commit git, permissions + secrets).
- the agent runs under the `eval-blind` L1 profile plus explicit MSA
  enablement (`subagent`, `team_*`, blind-safe `pab_split`); the bank tools
  (`p2m_*`) stay denied because `p2m_get` can return a reference proof.
- **shell-read deny** (`patchEnvConfig`): `eval-blind` only scopes read/edit/
  glob/grep, so `shell` can read anything the user can. The generated config
  therefore denies shell commands matching `*formalpedia*`, `*/p2m/data/bank*`,
  `*/eval/runs/*`, `*secrets.json*`, `*/guard.json*`, `*/lean-4.28-reap/env-*`.
  Without it an agent found the reference proof for a T1 problem with
  `head -c 3000 …/formalpedia/envs/0df444a/Solutions/Sol_*.lean`.
- `finish` audits every transcript for that leak (`detectLeaks`): successful
  reads of the oracle/bank mark the task `contaminated`; blocked ones are kept
  as `leak_attempts`. Real isolation still needs L3 (`guard/l3/p2mrun.sh`).
- `p2m-guard` (L2) is enabled per process: `P2M_GUARD=on`,
  `P2M_GUARD_LOG=<env>/guard.log`.

## Usage

```bash
# 1. create a run (2 per tier = 10)
node cli.mjs run --tiers T1,T2,T3,T4,T5 --per-tier 2 --seed bench-1 --timeout 600 --jobs 3

# 2. drive it (claim → launch → grade), at most 3 in parallel
node cli.mjs exec --run <run_id> --jobs 3 --timeout 600

# 3. table + report
node cli.mjs status --run <run_id>
node cli.mjs report --run <run_id>

# housekeeping
node cli.mjs verify  --run <run_id>                        # one model id, no leaks, statements intact
node cli.mjs recheck --run <run_id>                        # re-grade in place, refresh audit fields
node cli.mjs reset   --run <run_id> --ids a,b --restore     # unstick + restore pristine repos
```

Pilot (one T1 problem, end to end):

```bash
node cli.mjs run    --tiers T1 --per-tier 1 --seed pilot-1 --timeout 600
node cli.mjs exec   --run <run_id> --jobs 1 --timeout 600
```

Or from an OpenCode session: `pab_run` → `pab_next` → (agent) → `pab_finish` →
`pab_report`.

## Install

```bash
rsync -a --delete ./plugin/p2m-agent-bench/ ~/.opencode2/plugins/p2m-agent-bench/
```

Registered in `~/.opencode2/config/opencode/opencode.json` under `plugins`.

## Tests

```bash
npm test                 # 62 unit tests: watchdog rules, contract validator, dispatch prompts, live kill
node selftest.mjs        # builds one real env and asserts lake wiring + the mission contract
```

- `tests/watchdog.test.mjs` — each of the 4 rules from synthetic jsonl, plus
  negatives (4 identical calls, different resources, a successful call in
  between, a clean compile), env-override thresholds, the jsonl tailer and the
  timestamp normalizers.
- `tests/contract.test.mjs` — accepts a good mission; rejects each missing field,
  out-of-parent imports, a prose goal, a non-`cd … && lake env lean` acceptance,
  and 7 flavours of "go find the source"; checks that the generated `subagent`
  prompt embeds all four fields verbatim, and runs `writeMissions` end to end on
  a fake run dir.
- `tests/live.test.mjs` — a stub binary emits 5 identical tool calls and hangs;
  `launchTask` must SIGTERM it, record `early_stop` and leave the run dir intact.

## Notes / limits

- `pab_run` is refused for any model other than
  `opencode-go/deepseek-v4.1-flash#max`; the launcher passes `--model` from the
  same constant, so a second model id cannot appear in a transcript.
- Blindness is by construction (statement, docstring, namespace stripped), not
  adversarial: the env directory is named after the bank id, so a determined
  agent could learn the theorem's name from `pwd`. Statements themselves never
  appear outside `Problem.lean`.
- `agent.jsonl` is the only source for tool-call/decomposition/search counts;
  `guard.log` is the only source for denials.
