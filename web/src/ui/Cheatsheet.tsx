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
          <strong>Safe:</strong>{' '}
          <code>¬(radiation = ON ∧ door = OPEN)</code>
        </p>
        <p>
          <strong>Spec:</strong>{' '}
          <code>Init ∧ □[Next]_{'<<door,time,radiation,power>>'}</code>
        </p>
        <p>
          The <code>[Next]_vars</code> form admits <em>stuttering steps</em> where{' '}
          <code>vars′ = vars</code>, i.e. "nothing happens." This demo emits those
          explicitly on every tick where no user action fires. Toggle them off in
          the sidebar if they're noisy.
        </p>
      </div>
    </details>
  );
}
