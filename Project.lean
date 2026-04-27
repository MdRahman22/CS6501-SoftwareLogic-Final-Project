/-
  CS6501 Software Logic Final Project

  Missile Chase in Lean 4

  Main idea:
  position(t) tells us where an object is at time t.
  velocity(t) tells us how position changes over time.
  acceleration(t) tells us how velocity changes over time.

  The HTML page is just the visual layer.
  Lean computes the motion data and proves small facts about it.
-/

structure Vec2 where
  x : Int
  y : Int
deriving Repr, DecidableEq

structure Point2 where
  x : Int
  y : Int
deriving Repr, DecidableEq

/-
  SimState is the full world state at one moment in time.
-/
structure SimState where
  tick : Nat
  targetPos : Point2
  targetVel : Vec2
  targetAcc : Vec2
  missilePos : Point2
  missileVel : Vec2
  missileAcc : Vec2
deriving Repr, DecidableEq

def zeroVec : Vec2 :=
  { x := 0, y := 0 }

/-
  New position = old position plus velocity.
-/
def addPointVec (p : Point2) (v : Vec2) : Point2 :=
  { x := p.x + v.x, y := p.y + v.y }

/-
  Change in position.
-/
def subPointPoint (p q : Point2) : Vec2 :=
  { x := p.x - q.x, y := p.y - q.y }

/-
  Change in velocity.
-/
def subVec (v w : Vec2) : Vec2 :=
  { x := v.x - w.x, y := v.y - w.y }

/-
  One-axis chase rule.

  The missile can move up to 2 units.
  If it is close, it moves exactly to the target instead of overshooting.
-/
def stepAxis (current target : Int) : Int :=
  if current < target then
    1
  else if target < current then
    -1
  else
    0

/-
  Missile velocity points from the missile toward the target.
-/
def chaseVelocity (missile target : Point2) : Vec2 :=
  {
    x := stepAxis missile.x target.x,
    y := stepAxis missile.y target.y
  }

/-
  One simulation step.
-/
def nextState (s : SimState) : SimState :=
  let newTargetPos := addPointVec s.targetPos s.targetVel
  let newMissileVel := chaseVelocity s.missilePos newTargetPos
  let newMissilePos := addPointVec s.missilePos newMissileVel
  let newMissileAcc := subVec newMissileVel s.missileVel
  {
    tick := s.tick + 1,
    targetPos := newTargetPos,
    targetVel := s.targetVel,
    targetAcc := zeroVec,
    missilePos := newMissilePos,
    missileVel := newMissileVel,
    missileAcc := newMissileAcc
  }

/-
  stateAt init t gives the world state at time t.
-/
def stateAt (init : SimState) : Nat -> SimState
| 0 => init
| n + 1 => nextState (stateAt init n)

/-
  Position, velocity, and acceleration as functions of time.
-/
def targetPositionAt (init : SimState) (t : Nat) : Point2 :=
  (stateAt init t).targetPos

def missilePositionAt (init : SimState) (t : Nat) : Point2 :=
  (stateAt init t).missilePos

def targetVelocityAt (init : SimState) (t : Nat) : Vec2 :=
  (stateAt init t).targetVel

def missileVelocityAt (init : SimState) (t : Nat) : Vec2 :=
  (stateAt init t).missileVel

/-
  Velocity as change in position.
-/
def velocityFromPositions (p1 p2 : Point2) : Vec2 :=
  {
    x := p2.x - p1.x,
    y := p2.y - p1.y
  }

/-
  Acceleration as change in velocity.
-/
def accelerationFromVelocities (v1 v2 : Vec2) : Vec2 :=
  {
    x := v2.x - v1.x,
    y := v2.y - v1.y
  }

def targetAccelerationAt (init : SimState) (t : Nat) : Vec2 :=
  accelerationFromVelocities
    (targetVelocityAt init t)
    (targetVelocityAt init (t + 1))

def missileAccelerationAt (init : SimState) (t : Nat) : Vec2 :=
  accelerationFromVelocities
    (missileVelocityAt init t)
    (missileVelocityAt init (t + 1))

/-
  Theorem 1:
  One update step keeps the target velocity the same.
-/
theorem nextState_keeps_target_velocity (s : SimState) :
    (nextState s).targetVel = s.targetVel := by
  rfl

/-
  Theorem 2:
  At every time t, the target velocity is still the original velocity.
-/
theorem target_velocity_constant (init : SimState) (t : Nat) :
    targetVelocityAt init t = init.targetVel := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      dsimp [targetVelocityAt] at ih
      change (nextState (stateAt init t)).targetVel = init.targetVel
      exact Eq.trans (nextState_keeps_target_velocity (stateAt init t)) ih

/-
  Theorem 3:
  The target acceleration is zero because target velocity never changes.
-/
theorem target_acceleration_zero (init : SimState) (t : Nat) :
    targetAccelerationAt init t = zeroVec := by
  unfold targetAccelerationAt accelerationFromVelocities zeroVec
  simp [target_velocity_constant]

/-
  Frame is a smaller version of SimState for simple visual frames.
-/
structure Frame where
  tick : Nat
  targetX : Int
  targetY : Int
  missileX : Int
  missileY : Int
deriving Repr, DecidableEq

def frameAt (init : SimState) (t : Nat) : Frame :=
  let s := stateAt init t
  {
    tick := s.tick,
    targetX := s.targetPos.x,
    targetY := s.targetPos.y,
    missileX := s.missilePos.x,
    missileY := s.missilePos.y
  }

def framesUpTo (init : SimState) (n : Nat) : List Frame :=
  (List.range (n + 1)).map (frameAt init)

/-
  Theorem 4:
  Frames from 0 through n have length n + 1.
-/
theorem framesUpTo_length (init : SimState) (n : Nat) :
    (framesUpTo init n).length = n + 1 := by
  simp [framesUpTo]

/-
  Demo starting state.
-/
def demoInit : SimState :=
  {
    tick := 0,
    targetPos := { x := 18, y := 6 },
    targetVel := { x := 1, y := 0 },
    targetAcc := zeroVec,
    missilePos := { x := 2, y := 2 },
    missileVel := zeroVec,
    missileAcc := zeroVec
  }

#eval stateAt demoInit 0
#eval stateAt demoInit 5
#eval (framesUpTo demoInit 10).length

/-
  Distance and caught status.
-/
def manhattanDistance (p q : Point2) : Nat :=
  Int.natAbs (p.x - q.x) + Int.natAbs (p.y - q.y)

def distanceToTarget (s : SimState) : Nat :=
  manhattanDistance s.missilePos s.targetPos

def caughtTarget (s : SimState) : Bool :=
  decide (s.missilePos = s.targetPos)

/-
  BigBang-medium section.

  World is the game state.
  onTick advances the world.
  onKey changes the world from input.
  stopWhen says when the game should stop.
-/
structure BigBang (World : Type) where
  onTick : World -> World
  onKey : World -> String -> World
  stopWhen : World -> Bool

/-
  Change the target velocity.
-/
def setTargetVelocity (s : SimState) (v : Vec2) : SimState :=
  { s with targetVel := v }

/-
  Input handler.

  This shows how the project could become interactive.
-/
def handleKey (s : SimState) (key : String) : SimState :=
  if key = "up" then
    setTargetVelocity s { x := 0, y := 1 }
  else if key = "down" then
    setTargetVelocity s { x := 0, y := -1 }
  else if key = "left" then
    setTargetVelocity s { x := -1, y := 0 }
  else if key = "right" then
    setTargetVelocity s { x := 1, y := 0 }
  else if key = "stop" then
    setTargetVelocity s zeroVec
  else
    s

/-
  BigBang instance for the missile chase project.
-/
def missileBigBang : BigBang SimState where
  onTick := nextState
  onKey := handleKey
  stopWhen := caughtTarget

/-
  Run a BigBang system forward by ticks.
-/
def stateAtByTick (bb : BigBang SimState) (init : SimState) : Nat -> SimState
| 0 => init
| n + 1 => bb.onTick (stateAtByTick bb init n)

/-
  BigBang theorem 1:
  The BigBang tick is exactly nextState.
-/
theorem missileBigBang_tick_is_nextState (s : SimState) :
    missileBigBang.onTick s = nextState s := by
  rfl

/-
  BigBang theorem 2:
  One BigBang tick keeps target velocity constant.
-/
theorem bigBang_tick_keeps_target_velocity (s : SimState) :
    (missileBigBang.onTick s).targetVel = s.targetVel := by
  rfl

/-
  BigBang theorem 3:
  One BigBang tick increases time by 1.
-/
theorem bigBang_tick_increments_time (s : SimState) :
    (missileBigBang.onTick s).tick = s.tick + 1 := by
  rfl

/-
  BigBang theorem 4:
  The stop condition is the caughtTarget function.
-/
theorem bigBang_stopWhen_means_caught (s : SimState) :
    missileBigBang.stopWhen s = caughtTarget s := by
  rfl

/-
  BigBang theorem 5:
  Running the BigBang tick model matches the original stateAt model.
-/
theorem stateAtByTick_matches_stateAt (init : SimState) (t : Nat) :
    stateAtByTick missileBigBang init t = stateAt init t := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      change
        missileBigBang.onTick (stateAtByTick missileBigBang init t)
          = nextState (stateAt init t)
      rw [missileBigBang_tick_is_nextState]
      rw [ih]

/-
  JSON export section.

  Lean writes frames.json.
  The HTML page reads frames.json.
-/
def joinWith (sep : String) : List String -> String
| [] => ""
| x :: [] => x
| x :: xs => x ++ sep ++ joinWith sep xs

def pointToJson (p : Point2) : String :=
  "{\"x\":" ++ toString p.x ++ ",\"y\":" ++ toString p.y ++ "}"

def vecToJson (v : Vec2) : String :=
  "{\"x\":" ++ toString v.x ++ ",\"y\":" ++ toString v.y ++ "}"

def stateToJson (s : SimState) : String :=
  "{"
  ++ "\"tick\":" ++ toString s.tick ++ ","
  ++ "\"targetPos\":" ++ pointToJson s.targetPos ++ ","
  ++ "\"targetVel\":" ++ vecToJson s.targetVel ++ ","
  ++ "\"targetAcc\":" ++ vecToJson s.targetAcc ++ ","
  ++ "\"missilePos\":" ++ pointToJson s.missilePos ++ ","
  ++ "\"missileVel\":" ++ vecToJson s.missileVel ++ ","
  ++ "\"missileAcc\":" ++ vecToJson s.missileAcc ++ ","
  ++ "\"distance\":" ++ toString (distanceToTarget s) ++ ","
  ++ "\"caught\":" ++ toString (caughtTarget s)
  ++ "}"

/-
  Export states from time 0 through n.

  This now uses the BigBang tick runner.
-/
def statesUpTo (init : SimState) (n : Nat) : List SimState :=
  (List.range (n + 1)).map (fun t => stateAtByTick missileBigBang init t)

/-
  Theorem 6:
  Exporting states from 0 through n gives n + 1 states.
-/
theorem statesUpTo_length (init : SimState) (n : Nat) :
    (statesUpTo init n).length = n + 1 := by
  simp [statesUpTo]

/-
  Theorem 7:
  The demo export has exactly 81 states.
-/
theorem demo_export_length :
    (statesUpTo demoInit 80).length = 81 := by
  simp [statesUpTo]

def gameDataJson (init : SimState) (n : Nat) : String :=
  "{\n"
  ++ "  \"frames\": [\n    "
  ++ joinWith ",\n    " ((statesUpTo init n).map stateToJson)
  ++ "\n  ]\n"
  ++ "}\n"

def main : IO Unit := do
  IO.FS.writeFile "frames.json" (gameDataJson demoInit 80)
  IO.println "Wrote frames.json with 81 frames."
