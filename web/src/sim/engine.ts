// Engine: owns the current Vars, dispatches user actions, and runs a tick
// loop. The tick loop has two modes corresponding to the paper
// (Laufer/Mertin/Thiruvathukal, arXiv:2407.21152, Sec. IV.C):
//
//   wfTick = true  -> models Spec /\ WF_vars(Tick): whenever Tick is enabled
//                     it fires, so a radiating microwave cannot stall.
//   wfTick = false -> models Spec with no fairness: the tick loop is allowed
//                     to stutter even when Tick is enabled, demonstrating the
//                     liveness violation of HeatLiveness.
//
// Dispatches from user actions always fire (a user click is not subject to
// fairness; it is a voluntary step in the model).

import { Vars, Init } from '../model/state';
import { Actions } from '../checker/spec';
import { Stutter, STUTTER_NAME } from '../checker/stutter';

export interface TraceRow {
  t: number;
  name: string;
  from: Vars;
  to: Vars;
  safe: boolean;
  stutter: boolean;
}

type Listener = () => void;

const isSafe = (v: Vars) => !(v.radiation === 'ON' && v.door === 'OPEN');
const MAX_TRACE = 500;

export class Engine {
  private v: Vars = { ...Init };
  private trace: TraceRow[] = [];
  private listeners = new Set<Listener>();
  private tickHandle: ReturnType<typeof setInterval> | undefined;
  public showStutter = true;
  /** Weak fairness on Tick (WF_vars(Tick)). Default on, matching the paper's
   * final fixed specification. Toggle off to reproduce the stutter trap from
   * Figure 7. */
  public wfTick = true;
  /** When fairness is off, a random-ish fraction of ticks are suppressed as
   * stutters. 1.0 = always stutter (deterministic trap), 0 = never. */
  public stutterProbability = 1.0;

  getState(): Vars {
    return this.v;
  }
  getTrace(): readonly TraceRow[] {
    return this.trace;
  }
  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }
  private notify() {
    this.listeners.forEach(l => l());
  }

  /** Returns true iff the named action was enabled and fired. */
  dispatch(name: string): boolean {
    const action = Actions.find(a => a.name === name);
    if (!action || !action.enabled(this.v)) return false;
    const from = this.v;
    const to = action.step(this.v);
    this.v = to;
    this.push(name, from, to, false);
    this.notify();
    return true;
  }

  startTickLoop() {
    if (this.tickHandle !== undefined) return;
    this.tickHandle = setInterval(() => this.onTick(), 1000);
  }

  stopTickLoop() {
    if (this.tickHandle !== undefined) {
      clearInterval(this.tickHandle);
      this.tickHandle = undefined;
    }
  }

  /**
   * One tick of wall-clock time.
   *
   *   - If Tick is enabled AND weak fairness (wfTick) is on: fire Tick.
   *   - If Tick is enabled AND fairness is off AND we roll a stutter: emit a
   *     stutter step, leaving the state unchanged. This reproduces the
   *     liveness violation from Figure 7 of the paper.
   *   - Otherwise (Tick not enabled): emit a stutter step, because the TLA+
   *     model always permits vars' = vars.
   */
  private onTick() {
    const tick = Actions.find(a => a.name === 'Tick')!;
    const tickEnabled = tick.enabled(this.v);
    const wouldTick = tickEnabled && this.v.radiation === 'ON';
    const suppressed = wouldTick && !this.wfTick && Math.random() < this.stutterProbability;

    if (wouldTick && !suppressed) {
      const from = this.v;
      const to = tick.step(this.v);
      this.v = to;
      this.push('Tick', from, to, false);
    } else {
      const from = this.v;
      const to = Stutter.step(this.v);
      this.v = to;
      this.push(STUTTER_NAME, from, to, true);
    }
    this.notify();
  }

  private push(name: string, from: Vars, to: Vars, stutter: boolean) {
    this.trace.push({ t: Date.now(), name, from, to, safe: isSafe(to), stutter });
    if (this.trace.length > MAX_TRACE) {
      this.trace.splice(0, this.trace.length - MAX_TRACE);
    }
  }

  reset() {
    this.v = { ...Init };
    this.trace = [];
    this.notify();
  }

  setShowStutter(show: boolean) {
    this.showStutter = show;
    this.notify();
  }

  setWfTick(on: boolean) {
    this.wfTick = on;
    this.notify();
  }
}
