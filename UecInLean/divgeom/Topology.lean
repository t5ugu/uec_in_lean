
universe u

abbrev Set (X : Type u) := X → Prop
abbrev PowerSet (X : Type u) := Set X → Bool

instance {X} : Membership X (Set X) where
  mem U x := U x

instance {X} : Membership (Set X) (PowerSet X) where
  mem P U := P U

instance {X} : HasSubset (Set X) where
  Subset U V := ∀ x, U x → V x

instance {X} : HasSubset (PowerSet X) where
  Subset U V := ∀ P, U P → V P

theorem Set.eq_of_subset_supset {X : Type u} {U V : Set X}
  (h₁ : U ⊆ V) (h₂ : V ⊆ U)
  : U = V := by {
  ext x
  exact ⟨(h₁ x ·), (h₂ x ·)⟩
}

def univ {X : Type u} : Set X := fun _ => true
def empty {X : Type u} : Set X := fun _ => false

class TopologicalSpace (X : Type u) (𝒪 : PowerSet X) where
  univ_in : univ ∈ 𝒪
  empty_in : empty ∈ 𝒪
  inter_in {U V} : U ∈ 𝒪 → V ∈ 𝒪 → (fun x => U x ∧ V x) ∈ 𝒪
  union_in {Λ : Type u} {U : Λ → Set X} : (∀ i, U i ∈ 𝒪) → (fun x => ∃ i, U i x) ∈ 𝒪

def isOpenSpace {X : Type u} {𝒪} [TopologicalSpace X 𝒪] (ℬ : PowerSet X) (_ : ℬ ⊆ 𝒪) : Prop
:= ∀ U ∈ 𝒪, ∃ (Λ : Type u) (V : Λ → Set X), (∀ i, V i ∈ ℬ) ∧ (fun x => ∃ i, V i x) = U

theorem isOpenSpace_iff {X : Type u} {𝒪} [TopologicalSpace X 𝒪] (ℬ : PowerSet X) (hℬ : ℬ ⊆ 𝒪) :
  isOpenSpace ℬ hℬ ↔
  ∀ U ∈ 𝒪, ∀ x ∈ U, ∃ B ∈ ℬ, B ⊆ U ∧ x ∈ B := by {
  constructor
  · intro h U hU x hxU
    obtain ⟨Λ, V, hVℬ, hUeq⟩ := h U hU
    obtain ⟨μ, hxVμ⟩ := hUeq ▸ hxU

    have : V μ ⊆ U := by {
      intro y hyV
      rw [← hUeq]
      exact ⟨μ, hyV⟩
    }

    exact ⟨V μ, hVℬ μ, this, hxVμ⟩
  · intro h U hU
    exact ⟨{ B // B ∈ ℬ ∧ B ⊆ U }, fun ⟨v, _⟩ => v, fun ⟨_, h, _⟩ => h, by {
      apply Set.eq_of_subset_supset
      · intro x ⟨⟨_, _, hU⟩, h⟩
        exact hU x h
      · intro x hxU
        obtain ⟨B, hBℬ, hBU, hxB⟩ := h U hU x hxU
        exact ⟨⟨B, hBℬ, hBU⟩, hxB⟩
    }⟩
}


