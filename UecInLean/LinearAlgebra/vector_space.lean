set_option autoImplicit true
universe u v w

abbrev Field := Lean.Grind.Field

instance [𝒦 : Field K] : @Std.Associative K 𝒦.add := ⟨𝒦.add_assoc⟩
instance [𝒦 : Field K] : @Std.Commutative K 𝒦.add := ⟨𝒦.add_comm⟩
instance [𝒦 : Field K] : @Std.Associative K 𝒦.mul := ⟨𝒦.mul_assoc⟩
instance [𝒦 : Field K] : @Std.Commutative K 𝒦.mul := ⟨𝒦.mul_comm⟩

class VectorSpace (K : Type u) [Field K] (V : Type v) extends Zero V, Add V, SMul K V where
  add_assoc (x y z : V) : x + y + z = x + (y + z)
  add_comm (x y : V) : x + y = y + x
  zero_add (x : V) : 0 + x = x
  add_zero (x : V) : x + 0 = x
  smul_add (k : K) (x y : V) : k • (x + y) = k • x + k • y
  add_smul (a b : K) (x : V) : (a + b) • x = a • x + b • x
  mul_smul (a b : K) (x : V) : (a * b) • x = a • (b • x)
  one_smul (x : V) : (1 : K) • x = x

example [Field K] : VectorSpace K Unit where
  add _ _ := ()
  smul _ _ := ()
  zero := ()
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  zero_add _ := rfl
  add_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul _ _ _ := rfl
  mul_smul _ _ _ := rfl
  one_smul _ := rfl

example {K : Type u} [𝒦 : Field K] : VectorSpace K K where
  add := (· + ·)
  smul := (· * ·)
  add_assoc _ _ _ := by rw [𝒦.add_assoc]
  add_comm _ _ := by rw [𝒦.add_comm]
  zero := 0
  zero_add _ := by rw [𝒦.add_comm, 𝒦.add_zero]
  add_zero _ := by rw [𝒦.add_zero]
  smul_add _ _ _ := by {
    simp only [HSMul.hSMul]
    rw [𝒦.left_distrib]
  }
  add_smul _ _ _ := by {
    simp only [HSMul.hSMul]
    rw [𝒦.right_distrib]
  }
  mul_smul _ _ _ := by {
    simp only [HSMul.hSMul]
    rw [𝒦.mul_assoc]
  }
  one_smul _ := by {
    simp only [HSMul.hSMul]
    rw [𝒦.one_mul]
  }

example {α : Type w} {K} [Field K] {V} [𝒱 : VectorSpace K V] : VectorSpace K (α → V) where
  add f g x := f x + g x
  smul c f x := c • f x
  zero x := 0
  add_assoc f g h := by {
    funext x
    have := 𝒱.add_assoc (f x) (g x) (h x)
    simp only [HAdd.hAdd]
    exact this
  }
  add_comm f g := by {
    funext x
    have := 𝒱.add_comm (f x) (g x)
    simp only [HAdd.hAdd]
    exact this
  }
  zero_add f := by {
    funext x
    have := 𝒱.zero_add (f x)
    simp only [HAdd.hAdd]
    exact this
  }
  add_zero f := by {
    funext x
    have := 𝒱.add_zero (f x)
    simp only [HAdd.hAdd]
    exact this
  }
  smul_add c f g := by {
    funext x
    have := 𝒱.smul_add c (f x) (g x)
    simp only [HAdd.hAdd, HSMul.hSMul]
    exact this
  }
  add_smul a b f := by {
    funext x
    have := 𝒱.add_smul a b (f x)
    simp only [HAdd.hAdd, HSMul.hSMul]
    exact this
  }
  mul_smul a b f := by {
    funext x
    have := 𝒱.mul_smul a b (f x)
    simp only [HSMul.hSMul]
    exact this
  }
  one_smul f := by {
    funext x
    have := 𝒱.one_smul (f x)
    simp only [HSMul.hSMul]
    exact this
  }
