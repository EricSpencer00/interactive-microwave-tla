import { Engine } from '../sim/engine';

export function Toggles({
  engine,
  showStutter,
  violationsCount,
  reachableCount,
}: {
  engine: Engine;
  showStutter: boolean;
  violationsCount: number;
  reachableCount: number;
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
      <button className="mw-btn mw-btn-secondary" onClick={() => engine.reset()}>
        Reset state &amp; trace
      </button>

      <h3>JS-native TLA+ checker</h3>
      <p className="mw-check-result">
        Reachable states from <code>Init</code>: <strong>{reachableCount}</strong>
        <br />
        <code>Safe</code> violations: <strong className={violationsCount ? 'bad' : 'good'}>
          {violationsCount}
        </strong>
      </p>
      <p className="mw-check-hint">
        The checker enumerates every state reachable from <code>Init</code> via plain{' '}
        <code>Next</code> and flags any where radiation is on with the door open.
      </p>
    </div>
  );
}
