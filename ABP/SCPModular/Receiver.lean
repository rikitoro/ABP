import ABP.SCPModular.Wire

namespace SCPModular.Receiver

variable {α : Type}

@[grind]
structure State (α : Type) where
  expected : Bool
  output : List α
  deriving Repr, DecidableEq

@[simp, grind]
def initial : State α := ⟨false, []⟩

@[simp, grind]
def onData (s : State α) (p : Packet α) : State α :=
  if p.bit = s.expected then
    { expected := !s.expected, output := s.output ++ [p.payload] }
  else
    s

@[simp, grind]
def emitAck (s : State α) : Bool := s.expected

@[simp, grind =]
theorem onData_accept {s : State α} {p : Packet α}
  (h : p.bit = s.expected) :
  onData s p = ⟨!s.expected, s.output ++ [p.payload]⟩ := by
  grind

@[simp, grind =]
theorem onData_reject {s : State α} {p : Packet α}
  (h : p.bit ≠ s.expected) :
  onData s p = s := by
  grind

@[simp, grind =]
theorem onData_idempotent (s : State α) (p : Packet α) :
  onData (onData s p) p = onData s  p := by
  grind


/---/
@[simp, grind]
def Invariant (input : List α) (s : State α) : Prop :=
  ∃ rest, input = s.output ++ rest
@[simp, grind]
def DataAssumption (input : List α) (s : State α) (p : Packet α) : Prop :=
  p.bit = s.expected → ∃ rest, input = s.output ++ (p.payload :: rest)

@[simp, grind .]
theorem initial_invariant (input : List α) :
  Invariant input initial := by
  simp [Invariant, initial]

/-- 受信側の局所的契約 -/
theorem onData_preserves {input : List α} {s : State α} {p : Packet α}
  (hinb : Invariant input s) (hdata : DataAssumption input s p) :
  Invariant input (onData s p) := by
  by_cases h : p.bit = s.expected <;> simp_all



end SCPModular.Receiver
