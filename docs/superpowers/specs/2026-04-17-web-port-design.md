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

### Diagnosis

In standard TLA+ semantics, `Spec == Init /\ [][Next]_vars` unfolds to: at every step, either `Next` holds (a real action) **or** `vars' = vars` (a stutter). Safety properties are invariant under stuttering because `[Next]_vars` includes the identity step.

The current web/Vaadin simulator:

1. Never emits a stutter in its trace log — every logged row corresponds to an enabled action.
2. Treats "nothing happened this tick" as invisible rather than a legal TLA+ step.
3. Renders `[Next]_vars` cheatsheet content but does not actually realize stuttering in the animation.

This is the divergence from the paper's formal presentation: a faithful runtime must acknowledge stutter steps explicitly.

### Fix

Two complementary changes:

1. **`stutter.ts`** adds an explicit `Stutter` pseudo-action with `enabled = always`, `step(v) = v`, `name = "(stutter)"`. The enumerated `Next` used by the trace view is `[Next]_vars = Next ∪ {Stutter}`. The BFS checker uses plain `Next` (stuttering adds nothing reachable), but the interactive trace view and the logged `\* <Action>` comments include stutters.
2. **Timer stutter emission** — currently the backend's `@Scheduled` tick silently no-ops when radiation is OFF. The ported `tickLoop` emits an explicit `(stutter)` log entry on every tick where no action is taken, matching `[Next]_vars`. A UI toggle **"Show stutter steps"** (default on) lets users compress them if the log gets noisy.

### Verification

A unit test in `web/src/checker/__tests__/stutter.test.ts` asserts:

- `Safe` is closed under `Stutter` (`Safe(v) ⇒ Safe(Stutter.step(v))`).
- Every real `Next` successor of a safe state is safe (re-verifies `Microwave.tla`'s `Safe` invariant in TS).
- `[Next]_vars` always has at least the stutter step enabled (behaviors never deadlock in the TLA+ sense).

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

- **Arxiv 2407.21152 not fetched this session** (WebFetch deferred). If the paper defines stuttering more strictly (e.g., distinguishing finite vs infinite stuttering for termination), the `stutter.ts` design may need extension. Flagging for user to confirm after reading the draft.
- **Java code is left in place.** Some users may expect it removed; leaving it keeps the Spring Boot dev path working and avoids a risky, unrelated deletion.
- **Asset duplication** — the built bundle lives in two repos. Acceptable for a Sphinx post; re-run `make web && cp -r …` on each microwave release.
