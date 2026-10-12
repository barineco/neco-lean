import NecoLean.Tui.Types

set_option autoImplicit false

namespace NecoLean.Tui

structure Sampler (α : Type) where
  private mk ::
  latest : IO.Ref (Option (Except String α))
  stopped : IO.Ref Bool
  worker : Task (Except IO.Error Unit)

private partial def samplingLoop {α : Type} (loader : RuntimeLoader α) (intervalMs : Int)
    (latest : IO.Ref (Option (Except String α))) (stopped : IO.Ref Bool) : IO Unit := do
  if ← stopped.get then
    return
  latest.set (some (← loader))
  IO.sleep (UInt32.ofNat (max 1 intervalMs).toNat)
  samplingLoop loader intervalMs latest stopped

def startSampler {α : Type} (loader : RuntimeLoader α) (intervalMs : Int) : IO (Sampler α) := do
  let latest ← IO.mkRef none
  let stopped ← IO.mkRef false
  let worker ← IO.asTask (samplingLoop loader intervalMs latest stopped)
  return .mk latest stopped worker

/-- A stopped sampler returns `.stopped`. An active sampler returns
`RuntimeSample.unavailable` until a loader result arrives after the preceding read. -/
def takeLatest {α : Type} (sampler : Sampler α) : IO (Except RuntimeFailure (RuntimeSample α)) := do
  if ← sampler.stopped.get then
    return .error .stopped
  let latest ← sampler.latest.get
  sampler.latest.set none
  return .ok (match latest with | none => .unavailable | some value => .latest value)

/-- Stops the worker so subsequent reads return `RuntimeFailure.stopped`. -/
def stopSampler {α : Type} (sampler : Sampler α) : IO Unit := do
  sampler.stopped.set true

end NecoLean.Tui
