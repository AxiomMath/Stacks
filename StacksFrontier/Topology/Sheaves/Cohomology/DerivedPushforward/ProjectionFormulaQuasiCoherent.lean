module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaLocalizationOnTheBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaOverSpec
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08EU]: the projection formula on `D_QCoh`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes.  For `E` in
`D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the projection-formula morphism of [Stacks, Tag 0B53]

`R f_* E ⊗^𝐋_{𝒪_Y} K ⟶ R f_*(E ⊗^𝐋_{𝒪_X} L f^* K)`

is an isomorphism.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isAffine`: the
  statement for an affine base.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent`:
  **[Stacks, Tag 08EU]**.
* `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`: the same, in the form the carried
  proposition `AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent` asks for.

## Implementation notes

The source's proof reduces to an affine base and then runs a dévissage in `K`; the dévissage is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_spec`, which is proved
for a base of the form `Spec R`.  This file supplies the two reductions.

*From `Spec R` to an arbitrary affine base.*  For `Y` affine, `Y.isoSpec` is an isomorphism
`Y ≅ Spec Γ(Y, ⊤)`, so its inverse `g` is an open immersion and the square with `g`, the identity
of `X`, `f` and `f ≫ Y.isoSpec.hom` is cartesian — a square two of whose parallel edges are
isomorphisms.  `isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion` then carries
the statement over `Spec Γ(Y, ⊤)` to invertibility of `L g^*` of the morphism over `Y`, and `L g^*`
reflects isomorphisms because `g` is an isomorphism, which is
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence`.

*From an affine base to an arbitrary one.*  Invertibility in `D(𝒪_Y)` is local on an open cover
of `Y` — `Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`, phrased with
restriction — and the affine opens cover `Y`.  Over an affine open `U` the restriction is the
derived pullback along the canonical inclusion,
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, and that inclusion is
`U.ι` read on ringed spaces; `isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion`
at the cartesian square of [Stacks, Tag 0B6B] for `U.ι` then reduces the statement to the affine
base `U`, where the previous paragraph applies.

Both reductions need the quasi-coherence of the restricted complexes, which is
[Stacks, Tag 08DW] part (1) in the form
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`; and the base-changed morphism
is again quasi-compact and quasi-separated, both properties being local on the target and stable
under composition with an isomorphism.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The underlying isomorphism of ringed spaces of an isomorphism of schemes -/

/-- An isomorphism of schemes, read as an isomorphism of the underlying ringed spaces. -/
def ringedSpaceIsoOfSchemeIso {X Y : Scheme.{u}} (s : X ≅ Y) :
    X.toRingedSpace ≅ Y.toRingedSpace :=
  (Scheme.forgetToLocallyRingedSpace ⋙
    AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace).mapIso s

/-- **The derived pullback along an isomorphism of schemes reflects isomorphisms**, being one
half of an equivalence of derived categories. -/
theorem isIso_of_isIso_derivedPullback_map_of_schemeIso {X Y : Scheme.{u}} (s : X ≅ Y)
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (φ : A ⟶ B)
    (h : IsIso ((derivedPullback s.hom.toLRSHom.toShHom).map φ)) : IsIso φ := by
  have : (derivedPullback (ringedSpaceIsoOfSchemeIso s).hom).IsEquivalence :=
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence
      (ringedSpaceIsoOfSchemeIso s)).isEquivalence_functor
  have : IsIso ((derivedPullback (ringedSpaceIsoOfSchemeIso s).hom).map φ) := h
  exact isIso_of_reflects_iso φ (derivedPullback (ringedSpaceIsoOfSchemeIso s).hom)

/-! ### An arbitrary affine base -/

section Affine

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
  (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)

include hE in
/-- **[Stacks, Tag 08EU] over an arbitrary affine base.**  For a quasi-compact and
quasi-separated morphism of schemes `f : X ⟶ Y` with `Y` affine, an object `E` of `D_QCoh(𝒪_X)`
and an object `K` of `D_QCoh(𝒪_Y)`, the projection-formula morphism of [Stacks, Tag 0B53] is an
isomorphism.

`Y.isoSpec` transports the statement to the base `Spec Γ(Y, ⊤)`, where it is
`isIso_projectionFormulaMap_of_spec`. -/
theorem isIso_projectionFormulaMap_of_isAffine
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj K).IsQuasicoherent) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  have sq : IsPullback (𝟙 X) (f ≫ Y.isoSpec.hom) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine isIso_of_isIso_derivedPullback_map_of_schemeIso Y.isoSpec.symm _ ?_
  exact isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion (𝟙 X)
    (f ≫ Y.isoSpec.hom) f Y.isoSpec.inv sq E K
    (isIso_projectionFormulaMap_of_spec (Γ(Y, ⊤)) (f ≫ Y.isoSpec.hom)
      ((derivedPullback (𝟙 X : X ⟶ X).toLRSHom.toShHom).obj E)
      (fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
        (𝟙 X : X ⟶ X) E hE j)
      ((derivedPullback Y.isoSpec.inv.toLRSHom.toShHom).obj K)
      (fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
        Y.isoSpec.inv K hK j))

end Affine

/-! ### An arbitrary base -/

section Main

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
  (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj E).IsQuasicoherent)

include hE

/-- **[Stacks, Tag 08EU] after restriction to an affine open of the base.** -/
theorem isIso_jStar_mapDerivedCategory_map_projectionFormulaMap_of_isAffineOpen
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj K).IsQuasicoherent)
    (U : Y.affineOpens) :
    IsIso ((jStar (U : Y.Opens) (structureSheafRing Y.toRingedSpace)).mapDerivedCategory.map
      (projectionFormulaMap f.toLRSHom.toShHom E K)) := by
  have : IsAffine (U : Y.Opens).toScheme := U.2
  have sq : IsPullback (f ⁻¹ᵁ (U : Y.Opens)).ι (f ∣_ (U : Y.Opens)) f (U : Y.Opens).ι :=
    (isPullback_morphismRestrict f (U : Y.Opens)).flip
  have hstep := isIso_derivedPullback_map_projectionFormulaMap_of_isOpenImmersion
    (f ⁻¹ᵁ (U : Y.Opens)).ι (f ∣_ (U : Y.Opens)) f (U : Y.Opens).ι sq E K
    (isIso_projectionFormulaMap_of_isAffine (f ∣_ (U : Y.Opens))
      ((derivedPullback (f ⁻¹ᵁ (U : Y.Opens)).ι.toLRSHom.toShHom).obj E)
      (fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
        (f ⁻¹ᵁ (U : Y.Opens)).ι E hE j)
      ((derivedPullback (U : Y.Opens).ι.toLRSHom.toShHom).obj K)
      (fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
        (U : Y.Opens).ι K hK j))
  exact (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
      Y.toRingedSpace (U : Y.Opens))
    (projectionFormulaMap f.toLRSHom.toShHom E K)).1 hstep

/-- **[Stacks, Tag 08EU].**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes.  For `E` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the projection-formula morphism of
[Stacks, Tag 0B53]

`R f_* E ⊗^𝐋_{𝒪_Y} K ⟶ R f_*(E ⊗^𝐋_{𝒪_X} L f^* K)`

is an isomorphism.

Invertibility is local on `Y`, the affine opens cover `Y`, and over an affine open the statement
is `isIso_projectionFormulaMap_of_isAffine`. -/
@[stacks 08EU]
theorem isIso_projectionFormulaMap_quasiCoherent
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj K).IsQuasicoherent) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) :=
  Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
    (structureSheafRing Y.toRingedSpace) (fun U : Y.affineOpens => (U : Y.Opens))
    (iSup_affineOpens_eq_top Y) (projectionFormulaMap f.toLRSHom.toShHom E K)
    (isIso_jStar_mapDerivedCategory_map_projectionFormulaMap_of_isAffineOpen f E hE K hK)

end Main

end Stacks.Cohomology.DerivedProjectionFormula

end
