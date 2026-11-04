module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Derived limits in a pre-triangulated category

Let `D` be a pre-triangulated category and let `(Kₙ, fₙ)` be an inverse system of objects of `D`
indexed by `ℕ`, that is, a functor `F : ℕᵒᵖ ⥤ D`, with transition maps `fₙ₊₁ : Kₙ₊₁ ⟶ Kₙ`. An
object `K` of `D` is a *derived limit*, or *homotopy limit*, of the system when the product
`∏ Kₙ` exists and `K` sits in a distinguished triangle `K → ∏ Kₙ → ∏ Kₙ → K[1]` whose middle map
is the difference map `(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))`. One writes `K = R lim Kₙ` when this is so.

Such a `K` exists as soon as `∏ Kₙ` does: completing the difference map to a distinguished
triangle (TR1) and rotating it is `distinguished_cocone_triangle₁`. Any two derived limits of the
same system are isomorphic, by TR3 and the fact that a morphism of distinguished triangles which
is an isomorphism on two of the three objects is one on the third (`isIso₁_of_isIso₂₃`,
`isIso₃_of_isIso₁₂`). That isomorphism is not unique, which is why this is a predicate on `K`
rather than a construction of `K`.

## Main definitions

* `CategoryTheory.Pretriangulated.IsDerivedLimit`: the property that an object `K` is a derived
  limit (= homotopy limit) of an inverse system `F : ℕᵒᵖ ⥤ D` whose objects have a product.

## Main results

* `CategoryTheory.Pretriangulated.exists_isDerivedLimit`: an inverse system whose objects have a
  product has a derived limit.

## Implementation notes

`Kₙ` is `F.obj ⟨n⟩` and `fₙ₊₁` is `F.map (homOfLE (Nat.le_succ n)).op`; the source's data
`(Kₙ, fₙ)` gives such a functor by `CategoryTheory.Functor.ofOpSequence`, so nothing is lost by
taking the functorial form of an inverse system.

The clause "the product `∏ Kₙ` exists" is the instance hypothesis
`HasProduct fun n : ℕ => F.obj ⟨n⟩`, since the difference map cannot be written down without it.
The outer two maps of the triangle are existentially quantified, as in the source ("there is a
distinguished triangle"), while the difference map itself is pinned; quantifying over it too would
say only that `K` is the fibre of *some* endomorphism of `∏ Kₙ`, which is strictly weaker.

The source assumes `D` triangulated, but neither the definition nor the arguments for existence
and uniqueness above mention anything beyond the class `distTriang D` and the subtraction of
morphisms: `distinguished_cocone_triangle₁`, `isIso₁_of_isIso₂₃` and `isIso₃_of_isIso₁₂` are all
facts about a pre-triangulated category, so `Pretriangulated D` suffices.

## References

* [Stacks, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An object `K` of a pre-triangulated category `D` is a **derived limit**, or **homotopy
limit**, of an inverse system `F : ℕᵒᵖ ⥤ D` of objects of `D` whose objects have a product —
written `K = R lim Kₙ` — if there is a distinguished triangle
`K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧` in which the middle map is the difference map
`(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))`, where `Kₙ = F.obj ⟨n⟩` and `fₙ₊₁ = F.map (homOfLE (Nat.le_succ n)).op`
is the transition map `Kₙ₊₁ ⟶ Kₙ`. Such a `K` is unique only up to non-unique isomorphism, which
is why this is a predicate and not a construction. -/
@[stacks 08TC]
public def IsDerivedLimit (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩] (K : D) : Prop :=
  ∃ (p : K ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩) (δ : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧),
    Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang D

/-- An inverse system `F : ℕᵒᵖ ⥤ D` of objects of a pre-triangulated category whose objects have
a product has a derived limit. -/
theorem exists_isDerivedLimit (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩] :
    ∃ K : D, IsDerivedLimit F K :=
  distinguished_cocone_triangle₁ _

end CategoryTheory.Pretriangulated

end
