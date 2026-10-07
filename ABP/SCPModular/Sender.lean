import ABP.SCPModular.Wire

namespace SCPModular.Sender

variable {α : Type}

@[grind]
structure State (α : Type) where
  pending : List  α
  bit : Bool
  deriving Repr, DecidableEq

@[simp, grind]
def initial (input : List α) : State α := ⟨input, false⟩

@[simp, grind]
def emit (s : State α) : Option (Packet α) :=
  match s.pending with
  | [] => none
  | x :: _ => some ⟨x, s.bit⟩

@[simp, grind]
def onAck (s : State α) (b : Bool) : State α :=
  match s.pending with
  | [] => s
  | _ :: xs =>
    if b = s.bit then s else { pending := xs, bit := !s.bit }

@[simp, grind .]
theorem emit_spec {s : State α} {p : Packet α}
  (h : emit s = some p) :
  p.bit = s.bit ∧ ∃ xs, s.pending = p.payload :: xs := by
  grind

@[simp, grind .]
theorem onAck_same (s : State α) : onAck s s.bit = s := by
  grind

@[simp, grind .]
theorem onAck_next {s : State α} {b : Bool} {x : α} {xs : List α}
  (hp : s.pending = x :: xs) (hb : b ≠ s.bit) :
  onAck s b = ⟨xs, !s.bit⟩ := by
  grind

/-- 同じ ACK を処理しても、さらに先には進まない -/
@[simp, grind =]
theorem onAck_idempotent (s : State α) (b : Bool) :
  onAck (onAck s b) b = onAck s b := by
  cases hb : s.pending with
  | nil => grind
  | cons =>
    by_cases hb : b = s.bit
    · grind
    · have heq : b = !s.bit := by
        cases b <;> cases hbit : s.bit <;> grind
      grind

@[simp, grind]
def Invariant (input confirmed delivered : List α) (s : State α) : Prop :=
  input = confirmed ++ s.pending ∧ ∃ rest, delivered = confirmed ++ rest

@[simp, grind]
def AckAssumption (confirmed derivered : List α) (s : State α) (b : Bool) : Prop :=
  ∀ x xs, s.pending = x :: xs → b ≠ s.bit →
  ∃ rest, derivered = (confirmed ++ [x]) ++ rest

@[simp, grind]
def recordAck (confirmed : List α) (s : State α) (b : Bool) : List α :=
  match s.pending with
  | [] => confirmed
  | x :: _ =>
    if b = s.bit then
      confirmed
    else
      confirmed ++ [x]

@[simp, grind .]
theorem initial_invariant (input : List α) :
  Invariant input [] [] (initial input) := by
  simp [Invariant]

/-- 送信側の局所的契約 -/

theorem onAck_preserves {input confirmed delivered : List α}
  {s : State α} {b : Bool}
  (hinv : Invariant input confirmed delivered s)
  (hack : AckAssumption confirmed delivered s b) :
  Invariant input (recordAck confirmed s b) delivered (onAck s b) := by
  grind

end SCPModular.Sender
