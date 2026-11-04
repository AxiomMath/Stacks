module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.DerivedIsoLocality
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaOverAffineBase

/-!
# The projection formula over an arbitrary base

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, `E` an object of
`D_QCoh(𝒪_X)` and `K` an object of `D_QCoh(𝒪_Y)`.  [Stacks, Tag 08EU] asserts that the
projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is invertible.  Being an isomorphism is a local question on `Y`, which reduces the tag to the case
`Y = Spec A`, that is
`Stacks.Cohomology.ProjectionFormulaOverAffineBase.isIso_projectionFormulaMap_of_isQuasicoherent`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_derivedPullback_map_projectionFormulaMap`:
  for a Cartesian square of schemes whose base arrow `g` is an open immersion, invertibility of
  the projection-formula morphism for the base-changed morphism implies invertibility of the
  derived pullback along `g` of the projection-formula morphism itself.  Unconditional on `E`
  and `K`.
* `Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isAffine`:
  **[Stacks, Tag 08EU] over an arbitrary affine base.**
* `Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isQuasicoherent`:
  **[Stacks, Tag 08EU]**, with no hypothesis beyond the tag's own.

## Implementation notes

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, given a local instance priority
above the locally small model that the imports provide as a global instance.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.SupportedComplexes (quasicoherentDerivedProperty)
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.ProjectionFormulaGeneralBase

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-! ### The localization step -/

/-- **The projection-formula morphism of [Stacks, Tag 0B53] becomes invertible on an open of the
base as soon as it is invertible for the base-changed morphism.**  For a Cartesian square of
schemes whose base arrow `g` is an open immersion, `Lg^*` of the morphism for `f` is invertible
whenever the morphism for `f'` is.  No hypothesis on `E` and `K`. -/
theorem isIso_derivedPullback_map_projectionFormulaMap {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion g] (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (h : IsIso (projectionFormulaMap f'.toLRSHom.toShHom
      ((derivedPullback g'.toLRSHom.toShHom).obj E)
      ((derivedPullback g.toLRSHom.toShHom).obj K))) :
    IsIso ((derivedPullback g.toLRSHom.toShHom).map
      (projectionFormulaMap f.toLRSHom.toShHom E K)) := by
  have hsq := Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion
    g' f' f g sq
  have key := projectionFormulaMap_derivedBaseChangeMap g'.toLRSHom.toShHom
    f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom hsq.w E K
  unfold ProjectionFormulaBaseChangeSquare at key
  have hbcE := Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion
    g' f' f g sq E
  have hbc := Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion
    g' f' f g sq
    ((Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf)).obj
      (E, (derivedPullback f.toLRSHom.toShHom).obj K))
  refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ ?_ ?_ key.symm
  · refine IsIso.comp_isIso' hbc ?_
    exact ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      (Iso.app (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
          g'.toLRSHom.toShHom) (E, (derivedPullback f.toLRSHom.toShHom).obj K) ≪≫
        (Functor.uncurry.obj
          (derivedTensorProductFunctor X'.toRingedSpace.sheaf)).mapIso
          (Iso.prod (Iso.refl ((derivedPullback g'.toLRSHom.toShHom).obj E))
            (Iso.app (derivedPullbackSquareIso g'.toLRSHom.toShHom f'.toLRSHom.toShHom
              f.toLRSHom.toShHom g.toLRSHom.toShHom hsq.w) K).symm))).isIso_hom
  · refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ h)
    · exact (Iso.app (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        g.toLRSHom.toShHom) _).isIso_hom
    · exact ((Functor.uncurry.obj
        (derivedTensorProductFunctor Y'.toRingedSpace.sheaf)).mapIso
        (Iso.prod (@asIso _ _ _ _ _ hbcE)
          (Iso.refl ((derivedPullback g.toLRSHom.toShHom).obj K)))).isIso_hom

/-! ### [Stacks, Tag 08EU] over an arbitrary affine base -/

/-- The localization step for quasicoherent `E` and `K`: if the projection-formula morphism of
`f'` is invertible on quasicoherent objects, `Lg^*` of the one for `f` is invertible. -/
private theorem isIso_derivedPullback_map_projectionFormulaMap_of_quasicoherent
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion g] (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : quasicoherentDerivedProperty Y K)
    (h : ∀ (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))),
      quasicoherentDerivedProperty X' E' →
      ∀ (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))),
      quasicoherentDerivedProperty Y' K' → IsIso (projectionFormulaMap f'.toLRSHom.toShHom E' K')) :
    IsIso ((derivedPullback g.toLRSHom.toShHom).map
      (projectionFormulaMap f.toLRSHom.toShHom E K)) :=
  isIso_derivedPullback_map_projectionFormulaMap g' f' f g sq E K
    (h _ (fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g' E hE n) _
      (fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g K hK n))

/-- **[Stacks, Tag 08EU] over an arbitrary affine base.**  For a quasi-compact quasi-separated
morphism of schemes `f : X ⟶ Y` with `Y` affine, an `E` in `D_QCoh(𝒪_X)` and a `K` in
`D_QCoh(𝒪_Y)`, the projection-formula morphism of [Stacks, Tag 0B53] is invertible. -/
theorem isIso_projectionFormulaMap_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : quasicoherentDerivedProperty Y K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  have hsq : IsPullback (𝟙 X) (f ≫ Y.isoSpec.hom) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 := isIso_derivedPullback_map_projectionFormulaMap_of_quasicoherent (𝟙 X)
    (f ≫ Y.isoSpec.hom) f Y.isoSpec.inv hsq E hE K hK fun E' hE' K' hK' =>
    Stacks.Cohomology.ProjectionFormulaOverAffineBase.isIso_projectionFormulaMap_of_isQuasicoherent
      (f ≫ Y.isoSpec.hom) E' hE' K' hK'
  have hpush : Y.isoSpec.hom.toLRSHom.toShHom ≫ Y.isoSpec.inv.toLRSHom.toShHom =
      ((Y.isoSpec.hom ≫ Y.isoSpec.inv) : Y ⟶ Y).toLRSHom.toShHom := rfl
  have hone : ((𝟙 Y : Y ⟶ Y).toLRSHom) = 𝟙 Y.toLocallyRingedSpace := rfl
  have hid : Y.isoSpec.hom.toLRSHom.toShHom ≫ Y.isoSpec.inv.toLRSHom.toShHom =
      𝟙 Y.toRingedSpace := by
    rw [hpush, Y.isoSpec.hom_inv_id, hone, LocallyRingedSpace.id_toShHom']
  have eiso : derivedPullback Y.isoSpec.inv.toLRSHom.toShHom ⋙
      derivedPullback Y.isoSpec.hom.toLRSHom.toShHom ≅
        𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _ ≪≫
      eqToIso (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hid) ≪≫
      Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso Y.toRingedSpace
  exact (NatIso.isIso_map_iff eiso (projectionFormulaMap f.toLRSHom.toShHom E K)).1
    ((derivedPullback Y.isoSpec.hom.toLRSHom.toShHom).mapIso (@asIso _ _ _ _ _ h2)).isIso_hom

/-! ### [Stacks, Tag 08EU] -/

/-- **[Stacks, Tag 08EU].**  For a quasi-compact quasi-separated morphism of schemes
`f : X ⟶ Y`, an `E` in `D_QCoh(𝒪_X)` and a `K` in `D_QCoh(𝒪_Y)`, the projection-formula
morphism `Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` of [Stacks, Tag 0B53] is invertible. -/
@[stacks 08EU "the tag in full: for a quasi-compact quasi-separated morphism of schemes \
f : X ⟶ Y, an E in D_QCoh(𝒪_X) and a K in D_QCoh(𝒪_Y), the Tag 0B53 map \
Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K) is invertible, with no hypothesis beyond those. The source's \
first step, that invertibility is a local question on Y, is carried out here: over an affine \
open V ⊆ Y the square of Tag 0B6B identifies L((V).ι)^* of the map with the map for the \
base change f ∣_ V, every other arrow of that square being invertible because (V).ι is an open \
immersion; the map for f ∣_ V is the affine case; and invertibility in D(𝒪_Y) is local on the \
affine opens of Y"]
theorem isIso_projectionFormulaMap_of_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : quasicoherentDerivedProperty X E)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : quasicoherentDerivedProperty Y K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_derived_of_isIso_restrict_affineOpens
    (projectionFormulaMap f.toLRSHom.toShHom E K) fun V => ?_
  have _ : IsAffine (V : Y.Opens).toScheme := V.2
  have hsq : IsPullback ((f ⁻¹ᵁ (V : Y.Opens)).ι) (f ∣_ (V : Y.Opens)) f (V : Y.Opens).ι :=
    (AlgebraicGeometry.isPullback_morphismRestrict f (V : Y.Opens)).flip
  have h2 := isIso_derivedPullback_map_projectionFormulaMap_of_quasicoherent
    ((f ⁻¹ᵁ (V : Y.Opens)).ι) (f ∣_ (V : Y.Opens)) f (V : Y.Opens).ι hsq E hE K hK
    fun E' hE' K' hK' => isIso_projectionFormulaMap_of_isAffine (f ∣_ (V : Y.Opens)) E' hE' K' hK'
  exact (NatIso.isIso_map_iff
    (AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback (V : Y.Opens).ι)
    (projectionFormulaMap f.toLRSHom.toShHom E K)).2 h2

end Stacks.Cohomology.ProjectionFormulaGeneralBase

end
