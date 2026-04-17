import { useEffect, useMemo, useState, useSyncExternalStore } from 'react';
import { Engine } from '../sim/engine';
import { Init } from '../model/state';
import { findViolations, reachable } from '../checker/bfs';
import { stutterTrapDetected } from '../checker/liveness';
import { Microwave } from './Microwave';
import { Controls } from './Controls';
import { TraceLog } from './TraceLog';
import { Toggles } from './Toggles';
import { Cheatsheet } from './Cheatsheet';

// One engine per mount. Could be singleton but this is simpler.
function useEngine(): Engine {
  const [engine] = useState(() => new Engine());
  useEffect(() => {
    engine.startTickLoop();
    return () => engine.stopTickLoop();
  }, [engine]);
  return engine;
}

export function App() {
  const engine = useEngine();

  // Subscribe the React tree to engine updates. The snapshot encodes enough
  // state (trace length, showStutter, wfTick) that any engine mutation
  // triggers a re-render.
  useSyncExternalStore(
    cb => engine.subscribe(cb),
    () =>
      engine.getTrace().length +
      (engine.showStutter ? 1_000_000 : 0) +
      (engine.wfTick ? 10_000_000 : 0),
  );

  const v = engine.getState();
  const trace = engine.getTrace();
  const livenessViolated = stutterTrapDetected(trace);

  // The model is tiny and the spec is immutable at runtime, so we can compute
  // the reachability check exactly once.
  const checker = useMemo(() => {
    const r = reachable(Init);
    const violations = findViolations(Init);
    return { reachableCount: r.size, violationsCount: violations.length };
  }, []);

  return (
    <div id="mw-app" className="mw-app">
      <header className="mw-header">
        <h1>Interactive Microwave</h1>
        <p>
          A browser port of the TLA+ microwave with a JS-native checker. Every
          tick where no action fires is recorded as a stuttering step, faithful
          to <code>[Next]_vars</code>.
        </p>
      </header>

      <div className="mw-layout">
        <aside className="mw-sidebar">
          <Toggles
            engine={engine}
            showStutter={engine.showStutter}
            wfTick={engine.wfTick}
            violationsCount={checker.violationsCount}
            reachableCount={checker.reachableCount}
            livenessViolated={livenessViolated}
          />
          <Cheatsheet />
        </aside>

        <main className="mw-main">
          <Microwave v={v} />
          {livenessViolated && (
            <div className="mw-violation" role="alert">
              🔥 <code>HeatLiveness</code> violated: radiation ON across many
              stutter steps with no Tick. Enable weak fairness on <code>Tick</code>{' '}
              to restore liveness.
            </div>
          )}
          <Controls engine={engine} v={v} />
        </main>

        <section className="mw-right">
          <TraceLog trace={trace} showStutter={engine.showStutter} />
        </section>
      </div>
    </div>
  );
}
