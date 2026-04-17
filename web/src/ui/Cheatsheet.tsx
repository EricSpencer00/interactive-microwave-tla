export function Cheatsheet() {
  return (
    <details className="mw-cheatsheet">
      <summary>
        <code>Microwave.tla</code> cheatsheet
      </summary>
      <div className="mw-cheatsheet-body">
        <p>
          <strong>Variables:</strong>{' '}
          <code>door, time, radiation, power</code>.
        </p>
        <p>
          <strong>Init:</strong>{' '}
          <code>door = CLOSED ∧ time = 0 ∧ radiation = OFF ∧ power = OFF</code>
        </p>
        <p>
          <strong>Next</strong> is the disjunction of:{' '}
          <code>TogglePower, IncrementTime, Start, Tick, Cancel, CloseDoor, OpenDoor</code>.
        </p>
        <p>
          <strong>Safety:</strong>{' '}
          <code>Safe == ¬(radiation = ON ∧ door = OPEN)</code>
        </p>
        <p>
          <strong>Liveness:</strong>{' '}
          <code>HeatLiveness == (radiation = ON) ⇝ (radiation = OFF)</code>
        </p>
        <p>
          <strong>Spec:</strong>{' '}
          <code>Init ∧ □[Next]_vars ∧ WF_vars(Tick)</code>
        </p>
        <p>
          Without <code>WF_vars(Tick)</code>, the square-bracket form{' '}
          <code>[Next]_vars</code> admits an infinite suffix of stuttering steps
          where <code>vars′ = vars</code>. From a radiating state, that means the
          microwave never ticks and <code>HeatLiveness</code> fails — the failure
          mode introduced as Figure 7 / Exercise 3b in{' '}
          <a href="https://arxiv.org/abs/2407.21152" target="_blank" rel="noreferrer">
            Laufer, Mertin, Thiruvathukal (2024)
          </a>
          . Weak fairness on <code>Tick</code> forces the action to eventually
          fire whenever it is continuously enabled, breaking the trap.
        </p>
      </div>
    </details>
  );
}
