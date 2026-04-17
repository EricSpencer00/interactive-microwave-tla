# Interactive Microwave TLA+ — Browser Port & Stuttering Fix

**Date:** 2026-04-17
**Status:** Draft, awaiting user review

## Goal

Replace the Spring Boot + Vaadin deployment with a purely client-side build that runs on static hosting, and embed it as a blog post on [ai4fm.cs.luc.edu](https://ai4fm.cs.luc.edu). The browser build must mimic the Java microwave runtime and a small TLA+ checker faithful to the existing `Microwave.tla` spec. Fix the presentation bug that the current simulator never emits stuttering steps, violating standard TLA+ semantics (`Spec == Init /\ [][Next]_vars`, which admits `vars' = vars` stutters).

## Non-goals

- Shipping full TLC in the browser (considered and rejected: CheerpJ bundle is too heavy for a static Sphinx post).
- Changing the Java/Vaadin source tree beyond what is needed to extract the state machine logic. The Spring Boot app stays runnable for local development.
- New safety properties beyond what `Microwave.tla` already declares.
- Liveness / fairness reasoning. The current spec is safety-only and we keep it that way.

## Architecture

```
interactive-microwave-tla/
├── Microwave.tla               (unchanged — canonical spec)
├── web/                        (NEW — standalone client build)
│   ├── index.html              dev harness
│   ├── src/
│   │   ├── model/
│   │   │   ├── state.ts        MicrowaveState (TS port of model/MicrowaveState.java)
│   │   │   └── actions.ts      Next-relation actions (ports of MicrowaveService)
│   │   ├── checker/
│   │   │   ├── spec.ts         Init, Next, Safe — literal transcription of Microwave.tla
│   │   │   ├── stutter.ts      stuttering-step support + [Next]_vars closure
│   │   │   └── bfs.ts          bounded state-space enumeration for Safe checking
│   │   ├── ui/
│   │   │   ├── App.tsx         main shell (replaces MicrowaveView.java)
│   │   │   ├── Controls.tsx    buttons (start/cancel/+3s/door/power)
│   │   │   ├── TraceLog.tsx    TLA+ verification log pane
│   │   │   ├── Toggles.tsx     feature toggles (replaces FeatureTogglesPanel.java)
│   │   │   └── Cheatsheet.tsx  (replaces TlaCheatsheetPanel.java)
│   │   └── main.tsx
│   ├── vite.config.ts          outputs a single ESM bundle + CSS
│   └── package.json
└── docs/superpowers/specs/…    (this file)
```

Build output is a single hashed JS + CSS pair that gets copied into the ai4fm Sphinx site under `src/_static/demos/microwave/` and embedded via a `raw:: html` block in a new post.

### Why TS + React (not Vaadin-in-the-browser)

- Vaadin Flow requires a server round trip for every UI event — not an option on static hosting.
- Hilla (Vaadin's client-side variant) still expects a backend endpoint for business logic.
- A thin React shell + TS ports of `MicrowaveState` / `MicrowaveService` is the minimum viable port and keeps the state machine honest.

## The JS-native TLA+ runtime (option B)

Literal transcription of `Microwave.tla`, not an interpreter.

**`spec.ts`** exports:

```ts
type Vars = { door: 'OPEN'|'CLOSED'; time: number; radiation: 'ON'|'OFF'; power: 'ON'|'OFF' };

const Init = (v: Vars) => v.door==='CLOSED' && v.time===0 && v.radiation==='OFF' && v.power==='OFF';

type Action = { name: string; enabled(v: Vars): boolean; step(v: Vars): Vars };
const Actions: Action[] = [TogglePower, IncrementTime, Start, Tick, Cancel, CloseDoor, OpenDoor];

const Next = (v: Vars): {name: string; v2: Vars}[] =>
  Actions.filter(a => a.enabled(v)).map(a => ({ name: a.name, v2: a.step(v) }));

const Safe = (v: Vars) => !(v.radiation==='ON' && v.door==='OPEN');
```

Each `Action` body is the *direct* translation of the corresponding `Microwave.tla` disjunct, including `UNCHANGED` — e.g. `Tick` only mutates `time` and conditionally `radiation`.

**`bfs.ts`** does bounded reachability from `Init` over `Next` to precompute every reachable state and flag safety violations. The state space is tiny (`door×radiation×power×time≤60 ≈ 488` states), so an exhaustive check runs in <10 ms on page load.

**`stutter.ts`** — this is the fix for the presentation bug.

## Stuttering fix

### Diagnosis (post-paper)

After reading Laufer, Mertin, Thiruvathukal (arXiv:2407.21152, Sec. IV.C), stuttering in this spec is not a trace-display nicety — it's a **liveness hazard**. The paper introduces:

- A liveness property `HeatLiveness == (radiation = ON) ⇝ (radiation = OFF)` (Exercise 3a).
- A failure scenario (Figure 7) where `Spec == Init /\ [][Next]_vars` alone admits a behavior in which the radiating microwave stutters forever, never ticks, and radiation persists indefinitely — food catches fire.
- The fix (Exercise 3b): add weak fairness on `Tick`, so the spec becomes `Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)`.

The current web/Vaadin simulator does not model any of this: it neither admits stuttering nor declares the liveness property nor enforces fairness. It *accidentally* behaves correctly because its Java tick loop unconditionally ticks — but that behavior is not documented, not toggleable, and not pedagogically useful.

### Fix

Four complementary changes:

1. **`Microwave.tla`** grows two definitions: `HeatLiveness` and `Spec` is strengthened to include `WF_<<door,time,radiation,power>>(Tick)`.
2. **`web/src/checker/stutter.ts`** — explicit `Stutter` pseudo-action realizing `[Next]_vars = Next ∪ {Stutter}`. Used by the UI and engine, not by the reachability check (stuttering adds no new reachable states).
3. **`web/src/checker/liveness.ts`** — runtime detector for a "stutter trap": N consecutive stutter rows while `radiation = ON`. Flips a liveness-violated signal in the UI.
4. **`web/src/sim/engine.ts`** — tick loop has a `wfTick` flag. With fairness on (default, matching the paper's fixed spec), Tick fires whenever enabled. With fairness off, the tick loop may emit a stutter step instead, reproducing Figure 7. A UI toggle switches between modes so students can see the liveness failure and its fix side by side.

### Verification

Unit tests assert:

- `Safe` is closed under `Stutter` (sanity for safety properties).
- `[Next]_vars` always has at least the stutter step enabled.
- The liveness detector flips when 3+ consecutive stutter rows land while radiating, and resets when radiation turns off.

## Data flow

```
  user click ─▶ Action dispatch ─▶ enabled? ─yes─▶ step() ─▶ Vars'
                                     │                        │
                                     no                       ▼
                                     │                 Safe(Vars')? ──no──▶ violation banner
                                     ▼                        │
                              violation log                   yes
                                                              ▼
                                                         append to trace
  tick timer ─▶ if no enabled action fires ─▶ Stutter ─▶ append "(stutter)" to trace
```

## UI parity checklist

Everything the Vaadin UI does today, the React port must also do:

- [ ] Microwave graphic with door/radiation/power/time visual states
- [ ] Buttons: +3s, Start, Cancel, Open/Close Door, Power (toggleable)
- [ ] Feature toggles: `powerButtonEnabled`, `dangerousMode`
- [ ] TLA+ trace log (with stutter rows, per the fix above)
- [ ] "Verify with TLC" → replaced with "Verify invariant (JS checker)" that runs `bfs.ts` and reports reachable states + any `Safe` violations
- [ ] Tutorial + Cheatsheet tabs (port `TlaCheatsheetPanel` content verbatim)

## Sphinx / ai4fm integration

Deliverables in `~/GitHub/ai4fm`:

- `src/_static/demos/microwave/` ← built JS/CSS assets (copied from `web/dist/`).
- `src/posts/interactive-microwave-tla.rst` ← new blog post authored via ablog. Includes:
  - Context and a link to the source repo
  - Discussion of the stuttering issue and how the spec handles it
  - A `.. raw:: html` block with `<div id="microwave-root"></div><script type="module" src="../_static/demos/microwave/index.js"></script>` pointing at the static bundle
- `src/conf.py` — no change expected; `_static` copying is already configured.

## PR plan

1. New branch on the microwave repo: `feat/web-port-and-stutter`. Contains `web/`, the spec doc, and a `Makefile` target `make web` that builds into `web/dist/`.
2. New branch on ai4fm: `feat/microwave-demo-post`. Contains the copied `web/dist/` assets and the new `.rst` post.
3. Open two PRs; reference each from the other.

I will not push without explicit confirmation — both PRs are user-visible actions.

## Risks & open questions

- **Java code is left in place.** Some users may expect it removed; leaving it keeps the Spring Boot dev path working and avoids a risky, unrelated deletion.
- **Asset duplication** — the built bundle lives in two repos. Acceptable for a Sphinx post; re-run `make web && rsync …` on each microwave release.
- **Liveness check is a runtime heuristic, not a full temporal-logic model checker.** It detects a fixed window of stutter-while-radiating as a witness of `HeatLiveness` failure. A real check would explore infinite behaviors; TLC does this, we don't. Adequate for a teaching demo.
