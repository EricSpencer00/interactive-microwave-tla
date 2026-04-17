import { useEffect, useMemo, useState, useSyncExternalStore } from 'react';
import { Engine } from '../sim/engine';
import { Init } from '../model/state';
import { findViolations, reachable } from '../checker/bfs';
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

  // Subscribe the React tree to engine updates.
  useSyncExternalStore(
    cb => engine.subscribe(cb),
    () => engine.getTrace().length + (engine.showStutter ? 1_000_000 : 0),
  );

  const v = engine.getState();
  const trace = engine.getTrace();

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
            violationsCount={checker.violationsCount}
            reachableCount={checker.reachableCount}
          />
          <Cheatsheet />
        </aside>

        <main className="mw-main">
          <Microwave v={v} />
          <Controls engine={engine} v={v} />
        </main>

        <section className="mw-right">
          <TraceLog trace={trace} showStutter={engine.showStutter} />
        </section>
      </div>
    </div>
  );
}
