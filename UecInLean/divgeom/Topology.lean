import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.Use
import Mathlib.Tactic.Choose

namespace UecInLean.divgeom
open Set

universe u v w

theorem forall_proped_iff {α : Type u} {P : α → Prop} {Q : (x : α) → P x → Prop}
: (∀ x : α, ∀ h : P x, Q x h) ↔ (∀ x : {x // P x}, Q x.val x.property)
:= ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩

abbrev PowerSet (X : Type u) := Set (Set X)

theorem inter_eq_iInter₂ {X} (U V : Set X) : (U ∩ V) = (iInter fun i : Fin 2 => if i = 0 then U else V) := by {
  ext x
  constructor
  · intro hx
    rw [mem_iInter]
    intro ⟨n, h⟩
    cases n
    · exact hx.left
    · exact hx.right
  · intro hx
    rw [mem_iInter] at hx
    exact ⟨hx (Fin.mk 0 (by simp)), hx (Fin.mk 1 (by simp))⟩
}

theorem Fin.zero_union_range_succ {n} : {0} ∪ range (Fin.succ : Fin n → Fin (n + 1)) = univ := by {
  ext ⟨x, h⟩
  cases x
  · simp
  case succ x' =>
    suffices ∃ y : Fin n, y.succ = ⟨x' + 1, h⟩ by simp
    use ⟨x', by grind⟩
    simp
}

theorem inter_iInter_fin_succ {X : Type u} {n : Nat} (U : Fin (n + 1) → Set X) :
  (U 0) ∩ (⋂ i : Fin n, U i.succ) = (⋂ i : Fin (n + 1), U i) := by {
  nth_grw 2 [iInter]
  rw [← iInf_univ, ← Fin.zero_union_range_succ, iInf_union, iInf_singleton, iInf_range]
  rfl -- ⊓ は ∩ 、⨅ は ⋂ で解釈してくれる
}

/-- 有限の共通部分は、2つについて調べるので十分 -/
theorem finInter_of_inter {X : Type u} (P : Set X → Prop) (hu : P univ) (h : ∀ {A B}, P A ∧ P B → P (A ∩ B)) : ∀ {n} {U : Fin n → Set X}, (∀ i, P (U i)) → P (⋂ i, U i) := by {
  intro n
  induction n with
  | zero =>
    intro U hU
    rw [iInter_of_empty]
    exact hu
  | succ n ih =>
    intro U hU
    rw [← inter_iInter_fin_succ]
    apply h
    exact ⟨hU 0, ih (fun i => hU (Fin.succ i))⟩
}

/-- iUnion は sUnion で表せる -/
theorem Set.iUnion_of_sUnion {X : Type u} {𝒪} (sUnion_in : ∀ U ⊆ 𝒪, ⋃₀ U ∈ 𝒪)
  {I : Sort v} {U : I → Set X} (hU : ∀ i, U i ∈ 𝒪) : (⋃ i, U i) ∈ 𝒪 := by {
  apply sUnion_in
  intro x ⟨i, hi⟩
  rw [← hi]
  exact hU i
}

theorem Set.biUnion_of_sUnion {X : Type u} {𝒪} (sUnion_in : ∀ U ⊆ 𝒪, ⋃₀ U ∈ 𝒪)
  {I : Sort v} {P : I → Sort w} {U : (i : I) → (P i) → Set X} (hU : ∀ i j, U i j ∈ 𝒪) : (⋃ i, ⋃ j, U i j) ∈ 𝒪 := by {
  apply sUnion_in
  intro V ⟨i, hiV⟩
  rw [← hiV]
  simp only
  apply Set.iUnion_of_sUnion sUnion_in
  intro j
  exact hU i j
}

theorem Set.iUnion_eq_of_subset_of_in {X : Type u} {t : Set X} {s : {x // x ∈ t} → Set X} (h_sub : ∀ i, s i ⊆ t) (h_in : ∀ x : {x // x ∈ t}, ↑x ∈ s x) : ⋃ x, s x = t := by {
  apply Subset.antisymm
  · exact iUnion_subset h_sub
  · intro x hx
    rw [mem_iUnion]
    exact ⟨⟨x, hx⟩, h_in ⟨x, hx⟩⟩
}

class TopologicalSpace (X : Type u) (𝒪 : PowerSet X) where
  univ_in : univ ∈ 𝒪
  empty_in : ∅ ∈ 𝒪
  finInter_in {n : Nat} {U : Fin n → Set X} : (∀ i, U i ∈ 𝒪) → (⋂ i, U i) ∈ 𝒪
  sUnion_in : ∀ U ⊆ 𝒪, ⋃₀ U ∈ 𝒪

theorem TopologicalSpace.inter_in {X : Type u} {𝒪} [TopologicalSpace X 𝒪]
  {U V : Set X} (hU : U ∈ 𝒪) (hV : V ∈ 𝒪) : (U ∩ V) ∈ 𝒪 := by {
  rw [inter_eq_iInter₂]
  apply TopologicalSpace.finInter_in
  intro ⟨n, h⟩
  cases n
  · exact hU
  · exact hV
}

def IsOpenBase {X : Type u} {𝒪} [TopologicalSpace X 𝒪] (ℬ : PowerSet X) (_ : ℬ ⊆ 𝒪) : Prop
:= ∀ U ∈ 𝒪, ∃ V ⊆ ℬ, ⋃₀ V = U

theorem IsOpenBase.iff_exist_base {X : Type u} {𝒪} [TopologicalSpace X 𝒪] {ℬ} {hℬ : ℬ ⊆ 𝒪} :
  IsOpenBase ℬ hℬ ↔
  ∀ U ∈ 𝒪, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by {
  constructor
  {
    intro h U hU x hx
    have ⟨𝒱, hV, hVeq⟩ := h U hU
    rw [← hVeq, mem_sUnion] at hx
    obtain ⟨Vμ, hVμ, hx⟩ := hx
    use Vμ, hV hVμ, hx
    rw [← hVeq]
    exact subset_sUnion_of_mem hVμ
  }
  {
    intro h U hU
    specialize h U hU
    rw [forall_proped_iff] at h
    choose B hB hxB hBU using h
    use range B
    constructor
    · rw [range_subset_iff]; exact hB
    · exact Set.iUnion_eq_of_subset_of_in hBU hxB
  }
}

theorem IsOpenBase.union_cover {X : Type u} {𝒪} [TopologicalSpace X 𝒪]
  {ℬ : PowerSet X} (hℬ : ℬ ⊆ 𝒪) (h : IsOpenBase ℬ hℬ)
: ⋃₀ ℬ = univ
:= by {
  have h1 : ⋃₀ ℬ ⊆ univ := by {
    intro x hx
    exact mem_univ x
  }
  have h2 : univ ⊆ ⋃₀ ℬ := by {
    intro x hx
    rw [IsOpenBase.iff_exist_base] at h
    obtain ⟨B, hBℬ, hxB, hBsub⟩ := h univ TopologicalSpace.univ_in x hx
    exact mem_sUnion.mpr ⟨B, hBℬ, hxB⟩
  }
  exact Subset.antisymm h1 h2
}

theorem IsOpenBase.subset_inter {X : Type u} {𝒪} [TopologicalSpace X 𝒪]
  {ℬ : PowerSet X} (hℬ : ℬ ⊆ 𝒪) (h : IsOpenBase ℬ hℬ)
  : ∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, ∀ x ∈ B₁ ∩ B₂, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B₁ ∩ B₂ := by {
  intro B₁ hB₁ B₂ hB₂ x hx
  rw [IsOpenBase.iff_exist_base] at h
  exact h (B₁ ∩ B₂) (TopologicalSpace.inter_in (hℬ hB₁) (hℬ hB₂)) x hx
}

theorem IsOpenBase.sUnion_in {X : Type u} (ℬ : PowerSet X)
  : ∀ U ⊆ {x | ∃ B ⊆ ℬ, ⋃₀ B = x}, ⋃₀ U ∈ {x | ∃ B ⊆ ℬ, ⋃₀ B = x}
:= by {
  intro U hU
  use {b | ∃ x ∈ U, ∃ B ⊆ ℬ, x = ⋃₀ B ∧ b ∈ B}
  constructor
  · intro _ ⟨_, _, _, hBℬ, _, hbB⟩
    exact hBℬ hbB
  · ext y
    simp only [mem_sUnion]
    constructor
    {
      intro ⟨b, ⟨x, hxU, B, _, hxB, _⟩, _⟩
      rw [hxB] at hxU
      use ⋃₀ B, hxU, b
    }
    {
      intro ⟨x, hxU, hyx⟩
      obtain ⟨B, hBℬ, hBeq⟩ := hU hxU
      rw [← hBeq] at hyx
      obtain ⟨b, hbB, hyb⟩ := hyx
      exact ⟨b, ⟨x, hxU, B, hBℬ, hBeq.symm, hbB⟩, hyb⟩
    }
}

theorem TopologicalSpace.of_openBase_axioms {X : Type u} (ℬ : PowerSet X)
  (b1 : ⋃₀ ℬ = univ)
  (b2 : ∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, ∀ x ∈ B₁ ∩ B₂, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B₁ ∩ B₂)
  : TopologicalSpace X {⋃₀ B | B ⊆ ℬ}
  := {
  univ_in := ⟨ℬ, by simp, b1⟩
  empty_in := ⟨∅, by simp, by simp⟩
  finInter_in := by {
    apply finInter_of_inter
    · grind -- univ_in は先ほど示した

    intro U V ⟨⟨B₁, hB₁ℬ, hB₁U⟩, ⟨B₂, hB₂ℬ, hB₂V⟩⟩
    rw [← hB₁U, ← hB₂V, sUnion_inter_sUnion]

    apply Set.biUnion_of_sUnion (IsOpenBase.sUnion_in ℬ)
    intro ⟨Bi, Bj⟩ ⟨hBi, hBj⟩
    simp only at hBi hBj ⊢
    specialize b2 Bi (hB₁ℬ hBi) Bj (hB₂ℬ hBj)
    rw [forall_proped_iff] at b2
    choose B hBℬ hxB hBsub using b2

    use range B
    constructor
    · rw [range_subset_iff]; exact hBℬ
    · exact Set.iUnion_eq_of_subset_of_in hBsub hxB
  }
  sUnion_in := IsOpenBase.sUnion_in ℬ
}

class SecondCountableSpace (X : Type u) (𝒪 : PowerSet X) [TopologicalSpace X 𝒪] where
  base : PowerSet X
  base_countable : Countable base
  base_subset : base ⊆ 𝒪
  exists_countable_base : @IsOpenBase X 𝒪 _ base base_subset

/-- 近傍 -/
def IsNeighborhood {X} (𝒪) [TopologicalSpace X 𝒪] (V : Set X) (x : X) : Prop := ∃ U ∈ 𝒪, x ∈ U ∧ U ⊆ V

theorem IsNeighborhood.of_openNeighborhood {X 𝒪} [TopologicalSpace X 𝒪]
  {V : Set X} {x : X}
: V ∈ 𝒪 →  x ∈ V → IsNeighborhood 𝒪 V x := by {
  intro hVopen hxV
  use V, hVopen
}

variable {X} {𝒪} [TopologicalSpace X 𝒪]

theorem TopologicalSpace.open_of_neighborhood {U : Set X}
: U ∈ 𝒪 ↔ (∀ x ∈ U, ∃ N ⊆ U, IsNeighborhood 𝒪 N x)
:= by {
  constructor
  {
    intro h x hxU
    exact ⟨U, by rfl, IsNeighborhood.of_openNeighborhood h hxU⟩
  }
  {
    intro h
    simp only [IsNeighborhood, forall_proped_iff] at h
    choose V hV W hW𝒪 hxW hWV using h
    suffices h : ⋃ x, W x = U by {
      rw [← h]
      exact Set.iUnion_of_sUnion (TopologicalSpace.sUnion_in) hW𝒪
    }
    exact Set.iUnion_eq_of_subset_of_in (fun i => (hWV i).trans (hV i)) hxW
  }
}

def IsNeighborhoodBase {X} {𝒪} [TopologicalSpace X 𝒪] (x : X) (𝒱₀x : PowerSet X) (_ : 𝒱₀x ⊆ {V | IsNeighborhood 𝒪 V x}) := ∀ V, IsNeighborhood 𝒪 V x → ∃ V₀ ∈ 𝒱₀x, V₀ ⊆ V

class FirstCountableSpace (X : Type u) (𝒪 : PowerSet X) [TopologicalSpace X 𝒪] where
  base : X → PowerSet X
  base_subset : ∀ x : X, base x ⊆ {V | IsNeighborhood 𝒪 V x}
  base_countable : ∀ x : X, Countable (base x)
  exists_countable_base : ∀ x : X, IsNeighborhoodBase x (base x) (base_subset x)

