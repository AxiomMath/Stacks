module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# A total left derived functor of a functor that already inverts `W` is triangulated

Let `L : C ⥤ H` be a localization functor for `W : MorphismProperty C`, let `F : C ⥤ D` be a
functor and let `α : L ⋙ LF ⟶ F` exhibit `LF : H ⥤ D` as the total left derived functor of `F`
along `L`. If `F` *already* inverts `W` — which is the situation of an exact functor of abelian
categories read on complexes, where no resolution is needed — then `α` is an isomorphism, and
`LF` is a triangulated functor as soon as `F` and `L` are.

This is the general statement behind the various "the derived pullback is an exact functor"
results of this library, each of which is instead proved by hand in its own setting from a
resolving class of complexes: see
`Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated` and
`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated`, whose resolving classes
are the K-flat complexes. When the functor inverts every morphism of `W` the resolving class can
be taken to be everything, and the only input left is that every morphism of `H` is, up to
isomorphism, the image of a morphism of `C` — that is, `L.mapArrow.EssSurj`, which holds for any
localization functor admitting a calculus of fractions and in particular for
`CategoryTheory.DerivedCategory.Qh`.

## Main results

* `CategoryTheory.Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts`: a total left
  derived functor of a triangulated functor which inverts `W` is triangulated.

## Implementation notes

The commutation of `LF` with the shift is *not* constructed here: it is already general, being
`StacksDraft.PseudoCoherence.leftDerivedCommShift`, and likewise the compatibility of `α` with
it is `CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift`. Both are therefore
instance arguments of the statement below, which keeps this file's imports to Mathlib and lets
it be used with any construction of the commutation isomorphisms.

The proof is Mathlib's `CategoryTheory.Functor.isTriangulated_of_rightExtension`, whose
hypothesis asks, for every morphism `f` of `H`, for a distinguished triangle of `C` whose first
morphism maps to `f` up to isomorphism and at whose three vertices `α` is invertible. Here `α`
is invertible everywhere by
`CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts`, so the triangle is obtained
by completing an arbitrary preimage of `f` under `L.mapArrow` to a distinguished triangle.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

open Limits Pretriangulated

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
  [LF.IsLeftDerivedFunctor α W]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject H]
  [Preadditive C] [Preadditive D] [Preadditive H]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor H n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated H]
  [F.CommShift ℤ] [L.CommShift ℤ] [LF.CommShift ℤ] [NatTrans.CommShift α ℤ]
  [F.IsTriangulated] [L.IsTriangulated] [L.mapArrow.EssSurj]

include α in
/-- **A total left derived functor of a functor that already inverts `W` is triangulated.**

If `F : C ⥤ D` inverts `W` then its comparison `α : L ⋙ LF ⟶ F` with its total left derived
functor is an isomorphism, so a distinguished triangle of `H` may be replaced by the image of a
distinguished triangle of `C`, of which `F` — and hence `LF` — takes a distinguished triangle.

The hypothesis `L.mapArrow.EssSurj` says that every morphism of `H` is, up to isomorphism, the
image of a morphism of `C`; it holds for `CategoryTheory.DerivedCategory.Qh`. -/
lemma isTriangulated_of_isLeftDerivedFunctor_of_inverts (hF : W.IsInvertedBy F) :
    LF.IsTriangulated := by
  have : IsIso α := isIso_of_isLeftDerivedFunctor_of_inverts LF α hF
  refine isTriangulated_of_rightExtension LF α (fun {X Y} f ↦ ?_)
  obtain ⟨Z, g, h, hT⟩ :=
    distinguished_cocone_triangle (L.mapArrow.objPreimage (Arrow.mk f)).hom
  exact ⟨_, hT, inferInstance, inferInstance, inferInstance,
    ⟨L.mapArrow.objObjPreimageIso (Arrow.mk f)⟩⟩

end CategoryTheory.Functor

end
