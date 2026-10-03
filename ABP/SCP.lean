import Std

/-!
# Simple Communication Protrol (SCP)
-/

namespace SCP

/-- 通信路を流れるパケット -/
structure Packet (α : Type) where
  payload : α
  bit     : Bool  -- 識別ビット
  deriving Repr, DecidableEq

/-- 送信側、受信側、データ通信路、ACK 通信路を合わせた全体の状態 -/
structure State (α : Type) where
  pending   : List α
  sendBit   : Bool
  expectBit : Bool  -- 受信側の期待ビット
  output    : List α
  dataCell  : Option (Packet α) -- データ通信路
  ackCell   : Option Bool       -- ACK 通信路
  deriving Repr, DecidableEq

/-- 初期状態 -/
def initial {α : Type} (input : List α) : State α where
  pending   := input
  sendBit   := false
  expectBit := false
  output    := []
  dataCell  := none
  ackCell   := none

/-- データ送信 (新規・再送も含む) -/
def transmitData {α : Type} (s : State α) (x : α) : State α :=
  { s with dataCell := some ⟨x, s.sendBit⟩ }

/-- データ受信 期待ビットに一致した場合のみデータを出力する -/
def receiveData {α : Type} (s : State α) (p : Packet α) : State α :=
  if p.bit = s.expectBit then
    { s with  dataCell := none, output := s.output ++ [p.payload],
              expectBit := !s.expectBit }
  else
    { s with dataCell := none }

/-- ACK 送信 -/
def transmitAck {α : Type} (s : State α) : State α :=
  { s with ackCell := some s.expectBit }

/-- ACK 受信 送信ビットと異なるときだけ、次のデータに進む -/
def receiveAck {α : Type} (s : State α) (b : Bool) : State α :=
  match s.pending with
  | [] => { s with ackCell := none }
  | _ :: xs =>
    if b = s.sendBit then
      { s with ackCell := none}
    else
      { s with pending := xs, sendBit := !s.sendBit, ackCell := none }


/-- 1 ステップの状態遷移 (いずれかが非決定的に起こるとする) -/
inductive Step {α : Type} : State α → State α → Prop where
  | send {s : State α} {x : α} {xs : List α}
    (head : s.pending = x :: xs) : Step s (transmitData s x)
  | recvData {s : State α} {p : Packet α}
    (present : s.dataCell = some p) : Step s (receiveData s p)
  | sendAck (s : State α) : Step s (transmitAck s)
  | recvAck {s : State α} {b : Bool}
    (present : s.ackCell = some b) : Step s (receiveAck s b)
  | loseData {s : State α} {p : Packet α}
    (present : s.dataCell = some p) : Step s { s with dataCell := none }
  | loseAck {s : State α} {b : Bool}
    (present : s.ackCell = some b) : Step s { s with ackCell := none }
  | idle (s : State α) : Step s s

/-- 初期状態から有限回の遷移で到達できる状態 -/
inductive Reachable {α : Type} (input : List α) : State α → Prop where
  | init : Reachable input (initial input)
  | next {s t : State α} : Reachable input s → Step s t → Reachable input t

end SCP
