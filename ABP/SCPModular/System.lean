import ABP.SCPModular.Sender
import ABP.SCPModular.Receiver

namespace SCPModular.System

variable {α : Type}

@[grind]
structure Network (α : Type) where
  dataCell : Option (Packet α)
  ackCell : Option Bool
  deriving Repr, DecidableEq

/-- 大域的状態 -/
@[grind]
structure State (α : Type) where
  sender : Sender.State α
  receiver : Receiver.State α
  network : Network α
  deriving Repr, DecidableEq

@[simp, grind]
def initial (input : List α) : State α :=
  ⟨Sender.initial input, Receiver.initial, ⟨none, none⟩⟩

@[simp, grind]
def sendData (s : State α) (p : Packet α) : State α :=
  { s with network := { s.network with dataCell := some p } }

@[simp, grind]
def recvData (s : State α) (p : Packet α) : State α :=
  { s with
    receiver := Receiver.onData s.receiver p
    network := { s.network with dataCell :=none } }

@[simp, grind]
def sendAck (s : State α) : State α :=
  { s with network := { s.network with ackCell := some (Receiver.emitAck s.receiver) } }

@[simp, grind]
def recvAck (s : State α) (b : Bool) : State α :=
  { s with
    sender := Sender.onAck s.sender b
    network := { s.network with ackCell := none } }

@[simp, grind]
def dropData (s : State α) : State α :=
  { s with network := { s.network with dataCell := none } }

@[simp, grind]
def dropAck (s : State α) : State α :=
  { s with network := { s.network with ackCell := none } }

/-- sender, receiver の局所的な動作を通信路に接続する -/
@[grind]
inductive Step : State α → State α → Prop where
  | sendData {s : State α} {p : Packet α}
    (produced : Sender.emit s.sender = some p) : Step s (sendData s p)
  | recvData {s : State α} {p : Packet α}
    (present : s.network.dataCell = some p) : Step s (recvData s p)
  | sendAck (s : State α) : Step s (sendAck s)
  | recvAck {s : State α} {b : Bool}
    (present : s.network.ackCell = some b) : Step s (recvAck s b)
  | loseData {s : State α} {p : Packet α}
    (present : s.network.dataCell = some p) : Step s (dropData s)
  | loseAck {s : State α} {b : Bool}
    (present : s.network.ackCell = some b) : Step s (dropAck s)
  | idle (s : State α) : Step s s

@[grind]
inductive Reachable (input : List α) : State α → Prop where
  | init : Reachable input (initial input)
  | next {s t : State α} : Reachable input s → Step s t → Reachable input t


/-! 各端点の動作は、相手のローカル状態を書き換えない -/
@[simp, grind .]
theorem sendData_frame (s : State α) (p : Packet α) :
  (sendData s p).sender = s.sender ∧ (sendData s p).receiver = s.receiver :=
  ⟨rfl, rfl⟩

@[simp, grind .]
theorem recvAck_frame (s : State α) (b : Bool) :
  (recvAck s b).receiver = s.receiver :=
  rfl

@[simp, grind .]
theorem recvData_frame (s : State α) (p : Packet α) :
  (recvData s p).sender = s.sender :=
  rfl

@[simp, grind .]
theorem sendAck_frame (s : State α) :
  (sendAck s).sender = s.sender ∧ (sendAck s).receiver = s.receiver :=
  ⟨rfl, rfl⟩

@[simp, grind .]
theorem lossData_frame (s : State α) :
  (dropData s).sender = s.sender ∧ (dropData s).receiver = s.receiver :=
  ⟨rfl, rfl⟩

@[simp, grind .]
theorem loseAck_frame (s : State α) :
  (dropAck s).sender = s.sender ∧ (dropAck s).receiver = s.receiver :=
  ⟨rfl, rfl⟩


/-! 有限イベント列による実行 -/
@[grind]
inductive Event where
  | send | recvData | sendAck | recvAck | loseData | loseAck | idle
  deriving Repr, DecidableEq

@[simp, grind]
def tick (e : Event) (s : State α) : State α :=
  match e with
  | .send => match Sender.emit s.sender with
    | none => s
    | some p => sendData s p
  | .recvData => match s.network.dataCell with
    | none => s
    | some p => recvData s p
  | .sendAck => sendAck s
  | .recvAck => match s.network.ackCell with
    | none => s
    | some b => recvAck s b
  | .loseData => match s.network.dataCell with
    | none => s
    | some _ => dropData s
  | .loseAck => match s.network.ackCell with
    | none => s
    | some _ => dropAck s
  | .idle => s

@[simp, grind .]
theorem tick_step (e : Event) (s : State α) : Step s (tick e s) := by
  grind only [Step, tick]

@[simp, grind]
def run (events : List Event) (s : State α) : State α :=
  match events with
  | [] => s
  | e :: es => run es (tick e s)

@[simp, grind .]
theorem run_reachable {input : List α} {s : State α}
  (h : Reachable input s) (events : List Event) :
  Reachable input (run events s) := by
  induction events generalizing s with grind


def trace (events : List Event) (s : State α) : List (State α) :=
  match events with
  | [] => [s]
  | e :: es => s :: trace es (tick e s)


end SCPModular.System
