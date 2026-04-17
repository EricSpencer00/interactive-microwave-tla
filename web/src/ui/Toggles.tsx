import { Engine } from '../sim/engine';

export function Toggles({
  engine,
  showStutter,
  wfTick,
  violationsCount,
  reachableCount,
  livenessViolated,
}: {
  engine: Engine;
  showStutter: boolean;
  wfTick: boolean;
  violationsCount: number;
  reachableCount: number;
  livenessViolated: boolean;
}) {
  return (
    <div className="mw-toggles">
      <h3>Simulation</h3>
      <label className="mw-check">
        <input
          type="checkbox"
          checked={showStutter}
          onChange={e => engine.setShowStutter(e.target.checked)}
        />
        Show stutter steps <code>(vars′ = vars)</code>
      </label>
      <label className="mw-check">
        <input
          type="checkbox"
          checked={wfTick}
          onChange={e => engine.setWfTick(e.target.checked)}
        />
        Weak fairness on <code>Tick</code> <code>(WF_vars(Tick))</code>
      </label>
      <p className="mw-check-hint">
        Turn fairness off to reproduce Figure 7 of{' '}
        <a href="https://arxiv.org/abs/2407.21152" target="_blank" rel="noreferrer">
          Laufer/Mertin/Thiruvathukal
        </a>
        : a radiating microwave stutters forever, violating <code>HeatLiveness</code>.
      </p>
      <button className="mw-btn mw-btn-secondary" onClick={() => engine.reset()}>
        Reset state &amp; trace
      </button>

      <h3>JS-native TLA+ checker</h3>
      <p className="mw-check-result">
        Reachable states from <code>Init</code>: <strong>{reachableCount}</strong>
        <br />
        Safety (<code>DoorSafety</code>) violations:{' '}
        <strong className={violationsCount ? 'bad' : 'good'}>{violationsCount}</strong>
        <br />
        Liveness (<code>HeatLiveness</code>) status:{' '}
        <strong className={livenessViolated ? 'bad' : 'good'}>
          {livenessViolated ? 'violated (stutter trap)' : 'holding'}
        </strong>
      </p>
      <p className="mw-check-hint">
        The safety check enumerates every state reachable from <code>Init</code> via plain{' '}
        <code>Next</code>. The liveness signal flips when a radiating microwave sits in
        stuttering steps for too long — a runtime witness of the paper's Figure 7.
      </p>
    </div>
  );
}
