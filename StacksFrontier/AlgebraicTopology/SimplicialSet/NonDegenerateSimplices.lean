module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

@[expose] public section

/-!
# Morphisms of simplicial sets detected on nondegenerate simplices

Let `f : U ⟶ V` be a morphism of simplicial sets sending every nondegenerate simplex of `U` to a
nondegenerate simplex of `V`. If moreover the induced map from the nondegenerate simplices of `U`
to those of `V` is injective, then `f.app ⦋n⦌ : U _⦋n⦌ → V _⦋n⦌` is injective for every `n`, and
the same holds with `injective` replaced by `surjective` or by `bijective`. Since a morphism of
simplicial sets preserves the dimension of a simplex, the hypotheses on the induced map and the
conclusions are all stated levelwise.

## Main definitions

* `SSet.PreservesNonDegenerate`: `f` sends nondegenerate `n`-simplices to nondegenerate
  `n`-simplices, for every `n`.
* `SSet.InjectiveOnNonDegenerate`: `f.app ⦋n⦌` is injective on the nondegenerate `n`-simplices of
  `U`, for every `n`.
* `SSet.SurjectiveOnNonDegenerate`: every nondegenerate `n`-simplex of `V` is the image under
  `f.app ⦋n⦌` of a nondegenerate `n`-simplex of `U`, for every `n`.

## Main results

* `SSet.injective_of_injective_on_nonDegenerate`: `f.app ⦋n⦌` is injective for every `n`.
* `SSet.surjective_of_surjective_on_nonDegenerate`: `f.app ⦋n⦌` is surjective for every `n`.
* `SSet.bijective_of_bijective_on_nonDegenerate`: `f.app ⦋n⦌` is bijective for every `n`.

## References

* [Stacks, Tag 017S](https://stacks.math.columbia.edu/tag/017S)
-/

open Simplicial CategoryTheory

namespace SSet

/-- The morphism `f` sends nondegenerate `n`-simplices to nondegenerate `n`-simplices, for every
`n`. -/
def PreservesNonDegenerate {U V : SSet} (f : U ⟶ V) : Prop :=
  ∀ (n : ℕ) (x : U _⦋n⦌), x ∈ U.nonDegenerate n → f.app _ x ∈ V.nonDegenerate n

/-- The map induced by `f` from the nondegenerate simplices of `U` to those of `V` is injective:
for every `n`, two nondegenerate `n`-simplices of `U` with the same image under `f.app ⦋n⦌` are
equal. -/
def InjectiveOnNonDegenerate {U V : SSet} (f : U ⟶ V) : Prop :=
  ∀ (n : ℕ) ⦃x y : U _⦋n⦌⦄, x ∈ U.nonDegenerate n → y ∈ U.nonDegenerate n →
    f.app _ x = f.app _ y → x = y

/-- The map induced by `f` from the nondegenerate simplices of `U` to those of `V` is surjective:
every nondegenerate `n`-simplex of `V` is the image under `f.app ⦋n⦌` of a nondegenerate
`n`-simplex of `U`. -/
def SurjectiveOnNonDegenerate {U V : SSet} (f : U ⟶ V) : Prop :=
  ∀ (n : ℕ) (z : V _⦋n⦌), z ∈ V.nonDegenerate n →
    ∃ x : U _⦋n⦌, x ∈ U.nonDegenerate n ∧ f.app _ x = z

/-- **Stacks 017S** (part 1).
Let `f : U ⟶ V` be a morphism of simplicial sets sending nondegenerate simplices to
nondegenerate simplices, whose induced map on nondegenerate simplices is injective. Then
`f.app ⦋n⦌` is injective for every `n`. -/
@[stacks 017S "(1)"]
theorem injective_of_injective_on_nonDegenerate
    {U V : SSet} (f : U ⟶ V)
    (ha : PreservesNonDegenerate f) (hb : InjectiveOnNonDegenerate f) :
    ∀ (n : ℕ), Function.Injective (f.app (Opposite.op ⦋n⦌)) := by
  intro n x x' hxx'
  obtain ⟨m₁, f₁, hf₁, y₁, hxeq⟩ := U.exists_nonDegenerate x
  obtain ⟨m₂, f₂, hf₂, y₂, hx'eq⟩ := U.exists_nonDegenerate x'
  have hgx : f.app _ x = V.map f₁.op (f.app _ (y₁ : U _⦋m₁⦌)) := by
    rw [hxeq]; exact (NatTrans.naturality_apply f f₁.op _).symm ▸ rfl
  have hgx' : f.app _ x' = V.map f₂.op (f.app _ (y₂ : U _⦋m₂⦌)) := by
    rw [hx'eq]; exact (NatTrans.naturality_apply f f₂.op _).symm ▸ rfl
  have hn₁ : f.app _ (y₁ : U _⦋m₁⦌) ∈ V.nonDegenerate m₁ := ha m₁ _ y₁.2
  have hn₂ : f.app _ (y₂ : U _⦋m₂⦌) ∈ V.nonDegenerate m₂ := ha m₂ _ y₂.2
  set z := f.app _ x with hz
  have hzeq : z = V.map f₁.op (f.app _ (y₁ : U _⦋m₁⦌)) := hgx
  have hzeq' : z = V.map f₂.op (f.app _ (y₂ : U _⦋m₂⦌)) := hxx'.trans hgx'
  have hmeq : m₁ = m₂ :=
    V.unique_nonDegenerate_dim z f₁ ⟨_, hn₁⟩ hzeq f₂ ⟨_, hn₂⟩ hzeq'
  subst hmeq
  have hyeq : (⟨_, hn₁⟩ : V.nonDegenerate m₁) = ⟨_, hn₂⟩ :=
    V.unique_nonDegenerate_simplex z f₁ ⟨_, hn₁⟩ hzeq f₂ ⟨_, hn₂⟩ hzeq'
  have hfeq : f₁ = f₂ :=
    V.unique_nonDegenerate_map z f₁ ⟨_, hn₁⟩ hzeq f₂ ⟨_, hn₂⟩ hzeq'
  have hgy : f.app _ (y₁ : U _⦋m₁⦌) = f.app _ (y₂ : U _⦋m₁⦌) := by
    have := congrArg Subtype.val hyeq
    simpa using this
  have hy : (y₁ : U _⦋m₁⦌) = (y₂ : U _⦋m₁⦌) := hb m₁ y₁.2 y₂.2 hgy
  rw [hxeq, hx'eq, hfeq, hy]

/-- **Stacks 017S** (part 2).
Let `f : U ⟶ V` be a morphism of simplicial sets whose induced map on nondegenerate simplices is
surjective. Then `f.app ⦋n⦌` is surjective for every `n`. -/
@[stacks 017S "(2)"]
theorem surjective_of_surjective_on_nonDegenerate
    {U V : SSet} (f : U ⟶ V)
    (hb : SurjectiveOnNonDegenerate f) :
    ∀ (n : ℕ), Function.Surjective (f.app (Opposite.op ⦋n⦌)) := by
  intro n w
  obtain ⟨m, φ, hφ, z, hweq⟩ := V.exists_nonDegenerate w
  obtain ⟨x, hx, hfx⟩ := hb m z z.2
  refine ⟨U.map φ.op x, ?_⟩
  rw [NatTrans.naturality_apply f φ.op x, hfx, ← hweq]

/-- **Stacks 017S** (part 3).
Let `f : U ⟶ V` be a morphism of simplicial sets sending nondegenerate simplices to
nondegenerate simplices, whose induced map on nondegenerate simplices is both injective and
surjective. Then `f.app ⦋n⦌` is bijective for every `n`. -/
@[stacks 017S "(3)"]
theorem bijective_of_bijective_on_nonDegenerate
    {U V : SSet} (f : U ⟶ V)
    (ha : PreservesNonDegenerate f)
    (hbinj : InjectiveOnNonDegenerate f) (hbsurj : SurjectiveOnNonDegenerate f) :
    ∀ (n : ℕ), Function.Bijective (f.app (Opposite.op ⦋n⦌)) := by
  intro n
  exact ⟨injective_of_injective_on_nonDegenerate f ha hbinj n,
    surjective_of_surjective_on_nonDegenerate f hbsurj n⟩

end SSet
