import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

namespace Puyo1D

def canPuyoAt (s : List Nat) (i : Nat) : Bool := Id.run do {
  if h : i + 3 < s.length then
    let a := s[i]'(by grind)
    let b := s[i + 1]'(by grind)
    let c := s[i + 2]'(by grind)
    let d := s[i + 3]'(by grind)
    return a = b ∧ b = c ∧ c = d
  else return false
}

theorem canPuyoAt_length (s : List Nat) (i : Nat)
  (h : canPuyoAt s i) : i + 3 < s.length
:= by {
  unfold canPuyoAt at h
  simp at h
  split_ifs at h with hlen
  · exact hlen
  · contradiction
}

def puyo (s : List Nat) (i : Nat) (_ : canPuyoAt s i) := s.take i ++ s.drop (i + 4)

def Step (s t : List Nat) : Prop := ∃ i h, puyo s i h = t

theorem puyo_decreases_length {s i h}
: (puyo s i h).length = s.length - 4
:= by {
  unfold puyo
  have := canPuyoAt_length s i h
  grind
}

def Normal (s : List Nat) : Prop :=
  ∀ i : Nat, false = canPuyoAt s i

def Reaches (s t : List Nat) : Prop :=
  Relation.ReflTransGen Step s t

def TerminatesTo (s t : List Nat) : Prop :=
  Reaches s t ∧ Normal t

-- ABC 438 C - 1D puyopuyo (https://atcoder.jp/contests/abc438/tasks/abc438_c) について、解説の「まず、最終的な ∣A∣ の値は操作の順番によって変わりません。」を証明したい。
-- 問題設定は、項書き換え系とみなせる。
-- Newman's lemma より、停止性と局所合流性があれば、全体として合流性を持つ。つまり、長さどころかリストとしても、ある一意な正規形が存在する。
-- cf. Mathlib.Logic.Relation - church_rosser
