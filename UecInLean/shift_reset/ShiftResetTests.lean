import UecInLean.shift_reset.LambdaD

namespace LambdaD

/-- reset の「枠」を 1 つ持ったメタ継続（Nat 用） -/
abbrev FrameNat : MetaCont := .Cons Nat .Halt .Halt Nat .Halt .Halt

/-- いわゆる `reset` の最小ランナー。

`TypeD Nat .Halt FrameNat Nat .Halt .Halt Nat` を、
トップで用意したメタ継続（中身は最終継続）に渡して実行する。
-/
def runResetNat (e : TypeD Nat .Halt FrameNat Nat .Halt .Halt Nat) : Nat :=
  e (fun v _ ⟨k', m', s'⟩ => k' v m' s') () ()

/-- `shift (fun k => k n)` に相当する、`TShift` を使った最小例 -/
def shiftNat (n : Nat) : TypeD Nat .Halt FrameNat Nat .Halt .Halt Nat :=
  TShift (τ := Nat) (τ₁ := Nat) (τ₂ := Nat)
    (μ₁ := .Halt) (μ₂ := .Halt) (σ₁ := .Halt) (σ₂ := .Halt)
    (is_id := IdContType.refl Nat)
    (f := fun k => k n)

example (n : Nat) : runResetNat (shiftNat n) = n := by
  simp [runResetNat, shiftNat, TShift, IdContType.idk]

/-- 外側の継続（`reset` の外）で `Nat.succ` をかけるランナー。

`shift` が捕まえるのはこの外側継続も含むので、結果が `succ` されることをテストする。
-/
def runResetNat_succ (e : TypeD Nat .Halt FrameNat Nat .Halt .Halt Nat) : Nat :=
  e (fun v _ ⟨k', m', s'⟩ => k' (Nat.succ v) m' s') () ()

example : runResetNat_succ (shiftNat 5) = 6 := by
  simp [runResetNat_succ, shiftNat, TShift, IdContType.idk]

end LambdaD
