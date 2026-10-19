# Plain build log

## Round 1: success on the first try

- Spec: `spec.plain` at `39a1cf3`, 292 lines, unchanged by the builder.
- Folder given: only `spec.plain`. Prompt: "The folder … holds spec.plain. Make it true."
- Builder: 25 minutes, about 245k tokens, 40 tool calls.
- Result, verified on a fresh copy named ts3: `sh runme.sh` exits 0 in about 13 seconds and prints 711 lines of Plain. Every line reads back exactly.

### What came back

| File | Lines | What it does |
|---|---|---|
| engine.go | 964 | Translates Plain to Mangle and back, checks the 13 examples, reads every line back, runs the commands until nothing changes, prints in Plain, exits with the answer's code |
| tools.go | 295 | The 9 catalog tools; `try` runs the copy's `runme.sh` and reads what it prints |
| workflow.plain | 91 | The workflow, written in Plain |
| runme.sh | 6 | Builds the Go into a temporary folder and runs it on spec.plain |
| go.mod, go.sum | | Mangle library `codeberg.org/TauCeti/mangle-go` v0.7.0 |

### Checks

- the folder, conforms, true
- 14 of 14 changes come out as stated: 13 answer false and break their law, and "a spec that cannot load" answers broken.
- 0 laws broken, 0 problems, 0 misread lines; all 13 examples match.
- `try` really runs `sh runme.sh` in the copy and reads its standard output.
- He listed the file names in the repo folder and the scratchpad once, and read nothing there.

### How he worked

| Minutes | What he did |
|---|---|
| 0–8 | Read the spec, then thought |
| 8–21 | Learned the Mangle library from its source; one probe program |
| 21–22 | Wrote engine.go, tools.go, runme.sh, go.mod and workflow.plain |
| 22–25 | Ran it, fixed the printing, checked it from another folder |

### His own choices (candidates for the spec)

1. Rules are named by file and line, like `spec.plain:122`.
2. Test runs are marked by `KIND_OF_RUN="a change"` in the environment, which becomes "a change, is, the kind of this run".
3. No `#!` line in runme.sh, because it would count as a comment.
4. No `// indirect` markers in go.mod, to stay clear of comments.
5. A problem makes the printed answer "broken", so the printout always matches the exit code.

### Still open

- `spec.plain:207, is, never fired`: the main rule of "Every change comes out as stated". As before, no change can show it failing, because a change does not try changes of its own. It fires only when a change really comes out wrong.
- The published page at claude.ai/artifact/1MbHjaweYtLHxAoQxCxtpE is from the old HTML report, which no longer exists.

## Round blind31: incremental, true on the first try

- Spec: `4e08412` (knowledge view defined by "is in the knowledge view" and "is observed", the reproduces lines, try returns why, proven needs an explanation).
- Builder: about 6 minutes, 107k tokens, 16 tool calls.
- Changes: engine.go renames unrolls to reproduces (3 places); tools.go makes try return "why" (the indented lines under each breaks line); workflow.plain adds "[change], explains, [line]".
- Verified on a fresh copy named ts3: exit 0, conforms true, 15 of 15 changes as stated, each with its explanations, spec unchanged. Merged as `5da76d7`.
- Gap the builder named: nothing in engine.go acts on "[rule] is in the knowledge view" or "[word] is observed", and no law checks it. The printed view shows the facts and their reasons, but not the rules in the view or the observed facts, so it cannot be replayed yet.

## Round clean1: from a folder holding only spec.plain, true on the first try

- Spec: `4e08412`, unchanged by the builder.
- Builder: 26 minutes, 247k tokens, 37 tool calls. He read nothing outside the folder.
- Verified on a fresh copy named ts3: exit 0 in about 4 seconds, conforms true, 15 of 15 changes as stated, same output twice. Merged as `26f02f5`.
- The view is executable now: 883 lines. It prints the shown facts, then every rule that defines a used word, then the observed facts (what engine.go and the tools created). The engine reads its own view back, evaluates it again, and calls it a problem if conforms or breaks come out different.
- workflow.plain came out byte-identical to blind31's, written by a different builder from the spec alone.
- His choices: the Mangle library github.com/google/mangle v0.4.0 (earlier builds used codeberg.org/TauCeti/mangle-go); rules named "spec.plain line 270"; runme.sh passes "a change" as an argument; "why" is the breaks line itself, not its reasons; an instruction the spec does not give the engine is a problem.
- "a workflow that fakes what the tools returned" answers broken, not false: once the workflow has a rule for "returned", "returned" is no longer observed, so the tool's facts drop out of the view and the replay differs. It still breaks its law, so it comes out as stated.

## Spec simplification, first set (no rebuild): `b302417`

- rests on: one rule instead of three (the law layer was for the old tree picture).
- Every change comes out as stated: three direct rules; missed, answered otherwise, as stated, about an unknown law are gone.
- Dropped "the knowledge view, shows, [line] is misread" (misread lines already show as breaks).
- 229 to 214 lines; the clean1 build still answers true with every change as stated, and a wrong expectation still answers false.

## Round blind32: incremental, rejected (the builder edited spec.plain)

- Spec `8c8a46e` (second set): engine.go creates "this run is a change" and "[file] has a rule for [word]" directly; the view is every rule plus the facts of every word a go file creates. 207 lines.
- The old engine said "this run is a change is not a fact pattern" (it wanted a blank first). The builder took that as the spec being wrong: it changed only spec.plain, putting back "[kind] is the kind of this run", "[rule] is in [file]" and both conversion rules. 4 minutes, 96k tokens.
- Not merged. Next: a fresh incremental builder (blind33) and a clean build (clean2) side by side, same spec.

## Round blind33: incremental retry, rejected again (edited spec.plain the same way)

- 4 minutes, 99k tokens. Same reverts, same reason (the old engine says a pattern starts with a blank).

## Round clean2: from spec.plain alone (spec `8c8a46e`), true, not merged yet

- 26 minutes, 242k tokens, 37 tool calls. Spec unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 15 of 15 as stated, same output twice. "a workflow that fakes what the tools returned" now answers false.
- Library: codeberg.org/TauCeti/mangle-go v0.7.0 (newer google/mangle declares that path). Rules named by their own text. THIS_RUN_IS_A_CHANGE in the environment.
- workflow.plain: same rules as clean1 but "in the folder" names the command directly ("if command: list the folder, returned, file, [file]") and "explains" moved up. No longer byte-identical.
- The view is 337 lines: every rule, then the shown facts. No observed facts. "[word] is observed" is used only as a check (a word in a condition with no rule must be observed); "reproduces" is read as "each printed line reads back as the same fact". So the view cannot be replayed, unlike clean1's.
- Test: adding "the knowledge view, shows, [fact pattern] if [fact pattern], names, [word] and [word], is, observed" makes clean2's engine try to print the observed facts (it then trips on rules named by multi-line text, which a builder would fix).

## Round clean3: from spec.plain alone (spec `148df5a`, 206 lines), true, merged

- Spec change before it: "the knowledge view, shows, [fact pattern] if [fact pattern], names, [word] and [word], is, observed"; dropped "reproduces" (its instruction and two lines) and the "[word] is observed" instruction.
- 23 minutes, 226k tokens, 42 tool calls. Spec unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 15 of 15 as stated (14 false, 1 broken), same output twice, nothing on stderr.
- View: 715 lines = rules (280) + observed facts (377: defines, refers to, returned, has a rule for, lays down, names) + shown facts (55).
- Replay, outside the builder's engine: lines 1-657 (rules and observed facts, without the shown facts) translated by plain.py, with declarations from the creates fact lines, evaluated by mgcheck (mangle-go). It derives the same 55 shown facts and conforms true. The only difference is plain.py's stale quoting of text starting "declared: ".
- workflow.plain: the same eight rules as clean1 and clean2, in a different order; "in the folder" says "uses, list, [any folder]".
- His choices: mangle-go v0.7.0 from codeberg; rules named spec.plain:42; THIS_RUN_IS_A_CHANGE; "why" as a sentence ("notes.plain breaks Every file is used"); runme.sh takes no argument. Merged as main.

## used split into a used file / a used word: `b646693`
- [file], is, a used file and [word], is, a used word; laws keep their names. The two means in mangle examples now show a_used_file. No rebuild: clean3 still answers true, 15 of 15 as stated.

## Round clean4: reasons (spec `a4da877`, 210 lines), true, merged

- Spec: engine.go creates "[fact] holds because [reason]"; the view gives reasons for "[thing] breaks [law]"; tools.go executes "[fact] holds because [reason]" (ties try's why to the reasons). The clean3 build answered true under this spec without any reasons; no law sees the gap.
- 29 minutes, 292k tokens, 50 tool calls. Spec unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 14 false + 1 broken, same output twice, nothing on stderr.
- Each change now explains with real reasons, one line per matched condition plus the rule that fired, e.g. a comment: "tools.go, has the comment, // a note" and "spec.plain line 152". The value is the whole holds-because line, so quotes nest; the zzz change needs backslashes.
- Replay outside the builder's engine: the view without its 100 shown facts derives the same 100 (conforms, 19 broke, 15 answered, 65 explains).
- workflow.plain: the same eight rules again; order differs; "in the folder" names "command: list the folder" directly (as clean2 did).

## word renamed to predicate throughout: `14fb2bb`
- 30 places in spec.plain; laws are now "Each predicate has one creator" and "Every predicate is used". No rebuild: clean4 still answers true, 15 of 15 as stated.

## Two holes found in review (before round 1)

- A workflow that runs try but writes broke/answered/explains from must break/must answer answered true (it is the declared creator of those predicates). Dropping the commands entirely was caught by "Every predicate is used" (a change, finds comments in go unused).
- A workflow line "Every predicate is used, is, proven" answered true: "Each predicate has one creator" only compared rules against creates fact lines, never two files with rules.

## Round 1 spec: `68ab9a3` (216 lines), clean5 running

- is a creator of (rule or creates fact); the law compares any two creators; a predicate = anything with a creator.
- broke, answered, explains moved from workflow.plain into spec.plain; their workflow creates fact lines removed; counterexample "a workflow that makes up a result".
- Dropped "a hand-written declaration" and two duplicate means in mangle examples.
- Blanks: [anyone] to [any file] (3), [anything] to [any field] and [any thing], [text] to [comment] in has the comment, [other] to [other predicate]. Stray instruction line moved up.
- Checked on the clean4 Go with workflow.plain cut to 5 rules: true, 15 of 15 as stated; both fakes now break "Each predicate has one creator".

## Round clean5 (round 1): true, merged

- 32 minutes, 330k tokens, 71 tool calls. Spec unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 14 false + 1 broken, same output twice, nothing on stderr. "a workflow that makes up a result" breaks "Each predicate has one creator".
- workflow.plain: 5 rules (list, in the folder, comment commands, has the comment, try); no rules for broke, answered or explains.
- Reasons come from Mangle's derivation recorder. Rules named spec.plain:105. sh comments found with mvdan.cc/sh (a real shell parser).
- Replay: 124 shown facts removed (conforms, 20 broke, 15 answered, 88 explains), all 124 derived again.
- Open: Plain does not say how to write a value holding both kinds of quote. clean4 used backslashes, clean5 doubles the quote: """'""""zzz"""", means, nothing', ...". Only the zzz counterexample's explanations hit it.

## Round 2 spec: `859f7a8` (234 lines), clean6 running

- engine.go creates "[rule] has the blank [blank]" and "[fact pattern] has the slot [slot]".
- a slot name = any slot of any fact pattern, plus "ending, is, a slot name". well named = a slot name, or "any " / "other " joined with one.
- Law "Every blank is named after a slot"; counterexample "a condition with a badly named blank" appends "    if [someone], is, a predicate" to spec.plain, which joins its last line (a fact) as a condition.
- misread now names the rule ("[rule] is misread"), not the line's text, so the zzz explanations no longer nest three levels of quotes.
- Mini replay (my own blank and slot extraction, mgcheck): no breaks on the spec as written; with the appended line, "someone" breaks the new law.

## Round clean6 (round 2): true, merged

- 24 minutes, 240k tokens, 42 tool calls. Spec unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 15 false + 1 broken (16 changes), same output twice, nothing on stderr.
- has the blank: 110 facts, only for real rule blanks (none from quoted examples). has the slot: 64. "a condition with a badly named blank" breaks the new law because "spec.plain line 277, has the blank, someone" and "not someone, is, well named".
- misread names the rule: "spec.plain line 278, is, misread"; no nested quotes in any explanation now.
- Replay: 86 shown facts removed (conforms, 21 broke, 16 answered, 48 explains), all 86 derived again.
- "why" read a third way: only the reason after "holds because" (no fact, no rule line). clean4 and clean5 gave the whole holds-because line, which the user preferred. The spec still does not say which.
- Rules named "spec.plain line 278" again (clean5 used spec.plain:105).

## Round 3 spec (six renames): see next commit, clean7 running

- why -> explanation (try returns explanation; [change] explains [explanation]); the whole holds-because line is wanted.
- [plain] means in mangle -> [line] means in mangle.
- is a creator of -> creates.
- [rule] is misread -> [rule] is read back differently; law "Every rule reads back as written"; counterexample "a rule that reads back differently".
- [law] is proven -> [law] is a law with a counterexample (Plain's one-value form needs "is").
- [command] uses [tool] [input] -> [command] calls [tool] [input]; law "Every command calls a tool in the catalog". "a file nobody uses" and "a predicate nobody uses" keep their names (that "use" means needed).

## Round clean7 (round 3, renames): true, merged

- 29 minutes, 275k tokens, 39 tool calls. Spec `0c4a054` unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 15 false + 1 broken, same output twice, nothing on stderr. Replay: 70 shown facts, all 70 derived again.
- Two choices that read worse: rules are named by their own text joined onto one line ("[file], is, a used file if [any file], loads, [file]"), so facts about rules carry long quoted names and the zzz explanation needs backslashes again; explanations are a fourth reading, one sentence per broken fact: "tools.go, breaks, The only knowledge is Datalog because tools.go, has the comment, // a note".
- Rule naming so far: clean1, clean4, clean6 "spec.plain line N"; clean3, clean5 "spec.plain:N"; clean2, clean7 the rule's text.

## Round 4 spec (pins by example), clean8 running

- "a comment, must explain, '"tools.go, breaks, The only knowledge is Datalog", holds because, "tools.go, has the comment, // a note"'" pins the explanation: the whole holds-because line in canonical Plain.
- The zzz change now adds "engine.go, loads, extra.plain" to spec.plain and the zzz line to extra.plain, and must explain '"extra.plain:1, breaks, Every rule reads back as written", holds because, "extra.plain:1, is, read back differently"'. That pins rule names as file:line (user chose spec.plain:88).
- Fourth clause of "Every change comes out as stated": must explain, not this run is a change, not explains.
- 241 lines. On the clean7 build both "a comment" and "a rule that reads back differently" break "Every change comes out as stated" (it writes "X because Y" and names rules by text), so the pins bite.

## Round clean8 (round 4, pins): true, merged

- 20 minutes, 236k tokens, 36 tool calls. Spec `5edb056` unchanged. Verified on a fresh copy named ts3: exit 0, conforms true, 16 changes as stated, same output twice, nothing on stderr. Replay: 109 shown facts, all derived again.
- Both pins hold exactly: rules are named spec.plain:1, and explanations are the whole holds-because line.
- Library github.com/google/mangle v0.4.0 again.
- New difference: "a command with a tool nobody has" answers broken (exit 2), because this builder makes an unknown tool a problem; earlier builders let the law report it and answered false. It still breaks its law. Pin candidate: "a command with a tool nobody has, must answer, false".

## Round blind34: dirty (incremental) build on the clean8 folder, running

- Spec `0958ffc`: one added line, "a command with a tool nobody has, must answer, false".
- The clean8 build answers false under it, with one broken law: "a command with a tool nobody has, breaks, Every change comes out as stated" (it answered broken).
- The question: does the builder change the machine (stop treating an unknown tool as a problem), or take a shortcut such as editing spec.plain?
- Result: true, merged. About 2 minutes, 88k tokens, 14 tool calls. Spec unchanged; only tools.go changed, 3 lines: a tool with no "returns" facts in the catalog now returns nothing instead of a problem, so the law reports it. A catalogued tool that tools.go lacks is still a problem (he checked with a throwaway tool). Verified on a fresh copy: exit 0, conforms true, 15 false + 1 broken, same output twice; replay 109 of 109.
