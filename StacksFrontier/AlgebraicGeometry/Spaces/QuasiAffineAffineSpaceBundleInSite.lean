module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.QuasiAffineAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The affine-space bundle of a quasi-affine scheme lies in the site

Stacks 0F82, `AlgebraicGeometry.exists_affine_pullback_iso_affineSpace`, produces for a
quasi-affine scheme `X` an integer `n`, an affine scheme `T` and a morphism `T ⟶ X` whose base
change along any morphism from an affine scheme is affine `n`-space over that scheme.

Membership of a big fppf site is the size bound `AlgebraicGeometry.BigFppfSite.Contains`, which
is not part of the conclusion of Stacks 0F82. This module shows that `T` can be chosen inside any
big fppf site containing `X`, and that `T ⟶ X` is locally of finite type.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_of_forall_isAffine_pullback_iso_affineSpace`: a
  morphism whose base change along every morphism from an affine scheme is affine `n`-space is
  locally of finite type.
* `AlgebraicGeometry.exists_contains_affine_pullback_iso_affineSpace`: **Stacks 0F82 inside a
  big fppf site.** For a quasi-affine scheme `X` contained in a big fppf site `B`, the bundle of
  Stacks 0F82 can be chosen with `T` contained in `B` as well, and with `T ⟶ X` locally of
  finite type.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A bundle that is affine `n`-space over every affine base change is locally of finite
type.** -/
theorem locallyOfFiniteType_of_forall_isAffine_pullback_iso_affineSpace
    {n : ℕ} {T X : Scheme.{u}} (f : T ⟶ X)
    (h : ∀ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
      Nonempty (Over.mk (pullback.fst g f) ≅
        Over.mk (AffineSpace.over (ULift.{u} (Fin n)) X').hom)) :
    LocallyOfFiniteType f := by
  have _ : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@LocallyOfFiniteType.{u})
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : X.affineOpens => (V : X.Opens)) (iSup_affineOpens_eq_top X) fun V => ?_
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨e⟩ := h (V.1 : Scheme.{u}) hVaff V.1.ι
  have hiso : IsIso e.hom.left := ((Over.forget (V.1 : Scheme.{u})).mapIso e).isIso_hom
  have hw : e.hom.left ≫ (𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u})) =
      pullback.fst V.1.ι f := Over.w e.hom
  have hfst : LocallyOfFiniteType (pullback.fst V.1.ι f) := by
    rw [← hw]
    infer_instance
  have hsnd : LocallyOfFiniteType (pullback.snd f V.1.ι) := by
    rw [← pullbackSymmetry_hom_comp_fst f V.1.ι]
    infer_instance
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V.1] at hsnd
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @LocallyOfFiniteType.{u}) (pullbackRestrictIsoRestrict f V.1).hom _).mp hsnd

/-- For a quasi-affine scheme `X` satisfying the size cutoff of a big fppf site `B`, the
affine-space bundle of Stacks 0F82 over `X` can be chosen with its total space satisfying the
cutoff too, and its structure morphism is locally of finite type. -/
@[stacks 0F82 "the bundle chosen inside a big fppf site"]
theorem exists_contains_affine_pullback_iso_affineSpace (B : BigFppfSite.{u})
    (X : Scheme.{u}) [X.IsQuasiAffine] (hX : B.Contains X) :
    ∃ (n : ℕ) (T : Scheme.{u}), IsAffine T ∧ B.Contains T ∧
      ∃ f : T ⟶ X, LocallyOfFiniteType f ∧
        ∀ (X' : Scheme.{u}) (_ : IsAffine X') (g : X' ⟶ X),
          Nonempty (Over.mk (pullback.fst g f) ≅
            Over.mk (AffineSpace.over (ULift.{u} (Fin n)) X').hom) := by
  obtain ⟨n, T, hTaff, f, hf⟩ := exists_affine_pullback_iso_affineSpace X
  have _ : IsAffine T := hTaff
  have hft : LocallyOfFiniteType f :=
    locallyOfFiniteType_of_forall_isAffine_pullback_iso_affineSpace f hf
  exact ⟨n, T, hTaff, (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hX, f, hft, hf⟩

end AlgebraicGeometry

end
