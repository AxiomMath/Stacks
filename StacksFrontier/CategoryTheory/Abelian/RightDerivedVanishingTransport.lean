module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Transporting the vanishing of a right derived functor across a natural isomorphism

If `F ≅ G` as additive functors out of an abelian category with injective resolutions, then
`F.rightDerived n` and `G.rightDerived n` agree on objects up to isomorphism, so one of them
vanishes at an object exactly when the other does.  This file states that transport.

## Main results

* `CategoryTheory.Functor.isZero_rightDerived_of_natIso`: **vanishing of a right derived
  functor at an object passes across a natural isomorphism of the functors.**
* `CategoryTheory.Functor.isZero_rightDerived_natIso_iff`: the same as an `Iff`.

## Implementation notes

The isomorphism of right derived functors itself is not new: it is
`CategoryTheory.Functor.rightDerivedIsoOfNatIso`
(`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean`), built from Mathlib's
`CategoryTheory.NatTrans.rightDerived` with its `_id` and `_comp` lemmas.  What is added here is
only the passage from it to the vanishing statement, which is the form the consumers ask for and
which was being written out at each use — `CategoryTheory.IsZero.of_iso` applied to the
component of that isomorphism, as in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineCohomologyVanishing.lean`.

The two `Functor.Additive` instance binders are *named*, so that a caller can pass one
explicitly.  That is not cosmetic: the categories a natural isomorphism of functors lives in are
fixed by the isomorphism, and when the same category has two `rfl`-equal spellings — as the
sheaves of modules on the small étale site of an algebraic space do — instance search keeps
them apart, the category being an indexed argument of `CategoryTheory.Functor.Additive`.  Since
that class is `Prop`-valued, passing the instance by name costs nothing: any proof will do.

Mathlib's `CategoryTheory.Functor.rightDerivedNatIso` is **not** applicable: it compares
*localization-theoretic* derived functors on the derived category, not the `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` built from chosen injective resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- **Vanishing of a right derived functor at an object passes across a natural isomorphism of
the functors.**  If `e : F ≅ G` are additive functors out of an abelian category with injective
resolutions and `(R^n F)(X) = 0`, then `(R^n G)(X) = 0`.

The comparison is `CategoryTheory.Functor.rightDerivedIsoOfNatIso` evaluated at `X`. -/
theorem isZero_rightDerived_of_natIso {F G : A ⥤ B} [hF : F.Additive] [hG : G.Additive]
    (e : F ≅ G) (n : ℕ) (X : A) (h : IsZero ((F.rightDerived n).obj X)) :
    IsZero ((G.rightDerived n).obj X) :=
  h.of_iso ((rightDerivedIsoOfNatIso e n).app X).symm

/-- The transport of `CategoryTheory.Functor.isZero_rightDerived_of_natIso` as an `Iff`: two
naturally isomorphic additive functors have the same objects of vanishing for each of their
right derived functors. -/
theorem isZero_rightDerived_natIso_iff {F G : A ⥤ B} [hF : F.Additive] [hG : G.Additive]
    (e : F ≅ G) (n : ℕ) (X : A) :
    IsZero ((F.rightDerived n).obj X) ↔ IsZero ((G.rightDerived n).obj X) :=
  ⟨isZero_rightDerived_of_natIso e n X, isZero_rightDerived_of_natIso e.symm n X⟩

end CategoryTheory.Functor

end
