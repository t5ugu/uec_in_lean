import UecInLean.LinearAlgebra.matrix
import UecInLean.LinearAlgebra.vector_space

example {n m R} [Field R] : VectorSpace R (Matrix n m R) where
  add_assoc := Matrix.add_assoc
  add_comm := Matrix.add_comm
  zero_add A := by {
    rw [Matrix.add_comm]
    exact Matrix.add_zero A
  }
  add_zero := Matrix.add_zero
  smul_add := Matrix.smul_add
  add_smul := Matrix.add_smul
  mul_smul := Matrix.mul_smul
  one_smul := Matrix.one_smul
