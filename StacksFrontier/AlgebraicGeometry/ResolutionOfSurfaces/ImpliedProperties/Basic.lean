module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Alteration
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# A dense regular open subscheme

An integral locally Noetherian scheme admitting an alteration by a regular scheme has a dense
open subscheme which is regular.

## Main results

* `AlgebraicGeometry.exists_dense_open_isRegular` produces the dense regular open subscheme.

## Implementation notes

The alteration is supplied together with its source scheme. An open subset carries its
canonical scheme structure, so its regularity is expressed by `AlgebraicGeometry.IsRegular V`.

## References

* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An integral locally Noetherian scheme admitting an alteration by a regular scheme has a
dense regular open subscheme. -/
@[stacks 0BGG "dense_regular_open"]
theorem exists_dense_open_isRegular
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [IsIntegral Y]
    (X : Scheme.{u}) (f : X ⟶ Y) (hf : IsAlteration f)
    (hX : IsRegular X) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsRegular V := by
  have : IsReduced Y := (isIntegral_iff_irreducibleSpace_and_isReduced Y).mp inferInstance |>.2
  have : IsProper f := hf.1
  have : LocallyOfFiniteType f := IsProper.toLocallyOfFiniteType
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : F.IsFiniteType := structureSheaf_isFiniteType X
  obtain ⟨U, hU, hflat, _, _⟩ := exists_dense_open_flat_finitePresentation f F
  refine ⟨U, hU, ?_⟩
  have : IsDominant f := hf.2.1
  apply ((isRegular_tfae U.toScheme).out 1 2 rfl rfl).mpr
  refine ⟨inferInstance, fun y ↦ ?_⟩
  obtain ⟨x, hfx⟩ := f.surjective (U.ι y)
  let xU : (f ⁻¹ᵁ U).toScheme := ⟨x, by
    change f x ∈ U
    rw [hfx]
    exact y.2⟩
  have hflatStalk : (f.stalkMap x).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (Scheme.Hom.resLEStalkMap f (U := U) (V := f ⁻¹ᵁ U) le_rfl xU)).mp
      ((Flat.iff_flat_stalkMap (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mp hflat xU)
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have : IsRegularLocalRing S := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mpr hflatStalk
  have : IsLocalHom (algebraMap R S) := f.toLRSHom.prop x
  have : IsRegularLocalRing (Y.presheaf.stalk y.1) := hfx.trans (U.ι_apply y) ▸
    IsRegularLocalRing.of_flat_of_isLocalHom S
  exact IsRegularLocalRing.of_ringEquiv
    (U.stalkIso y).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry
