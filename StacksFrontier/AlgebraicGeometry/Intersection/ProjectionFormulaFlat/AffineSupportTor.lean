module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic

/-!
# Pushing a Tor sheaf forward along a flat morphism, off an affine support

Let `f : X ⟶ Y` be a flat, quasi-compact and quasi-separated morphism of schemes, let
`j : Z ⟶ X` be a morphism such that `j` and `j ≫ f` are affine, let `ℱ` be a quasi-coherent
`𝒪_Z`-module and `𝒢` a quasi-coherent `𝒪_Y`-module. Then

`f_* Torᵢ^{𝒪_X}(j_*ℱ, f^*𝒢) ≅ Torᵢ^{𝒪_Y}(f_*j_*ℱ, 𝒢)`

for every `i`.

This is the comparison (43.22.1.1), Tag 0B11, in the proof of Stacks Tag 0B10. The source
obtains it at the generic point `ξ` of a component, where the support of the sheaf on `X` is
finite over `Y`; the content is the same, and the hypothesis that `j ≫ f` is affine is exactly
what the finiteness over a neighbourhood of `ξ` provides once `ℱ` is pushed forward from its
scheme-theoretic support.

## Main definitions

* `Stacks.Intersection.ProjectionFormula.pushforwardTorSheafIsoOfIsAffineHom` — the isomorphism
  above.

## Implementation notes

The argument is the source's, read in the derived category. Write `E = ℱ ⊗ᴸ Lj^*Lf^*𝒢` on `Z`.

* On `X`: `Lf^*𝒢 = f^*𝒢` because `f` is flat, `Rj_*ℱ = j_*ℱ` because `j` is affine, and the
  projection formula of Stacks 08EU for `j` gives `j_*ℱ ⊗ᴸ Lf^*𝒢 ≅ Rj_*E`. The cohomology of
  `Rj_*E` is `j_*` of that of `E` because `j` is affine, so `Torᵢ^{𝒪_X}(j_*ℱ, f^*𝒢) ≅ j_*Hⁱ(E)`
  and its direct image along `f` is `(j ≫ f)_*H^{-i}(E)`.
* On `Y`: `f_*j_*ℱ = R(j ≫ f)_*ℱ = Rf_*Rj_*ℱ` because `j ≫ f` is affine, and the projection
  formula of Stacks 08EU for `f` and then for `j` gives
  `Rf_*Rj_*ℱ ⊗ᴸ 𝒢 ≅ Rf_*(Rj_*ℱ ⊗ᴸ Lf^*𝒢) ≅ Rf_*Rj_*E = R(j ≫ f)_*E`, whose cohomology is
  `(j ≫ f)_*` of that of `E` because `j ≫ f` is affine.

No resolution and no boundedness is needed: the affine direct images are t-exact on complexes
with quasi-coherent cohomology without any bound
(`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso`).

## References

* [Stacks Project, Tag 0B10](https://stacks.math.columbia.edu/tag/0B10)
* [Stacks Project, Tag 0B11](https://stacks.math.columbia.edu/tag/0B11)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)

universe u

namespace Stacks.Intersection.ProjectionFormula

open AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The derived pullback along a flat morphism of a module placed in degree `0`** is the
ordinary pullback placed in degree `0`. -/
def singlePullbackIsoDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (G : Y.Modules) :
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
        ((Scheme.Modules.pullback f).obj G) ≅
      (derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G) :=
  let P := RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom
  (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app (P.obj G) ≪≫
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).app G)).symm ≪≫
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat f.toLRSHom.toShHom
      (fun x => Flat.stalkMap f x)
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)).symm ≪≫
    (derivedPullback f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).app G).symm


section

variable {Z X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [QuasiSeparated f]
  (j : Z ⟶ X) [IsAffineHom j] [IsAffineHom (j ≫ f)]
  (F : Z.Modules) (hF : F.IsQuasicoherent) (G : Y.Modules) (hG : G.IsQuasicoherent)

/-- The complex `ℱ ⊗ᴸ Lj^*Lf^*𝒢` on `Z` through which both sides of the comparison are
computed. -/
abbrev affineSupportTensor :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj F)).obj
    ((derivedPullback j.toLRSHom.toShHom).obj
      ((derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)))

omit [Flat f] [QuasiCompact f] [QuasiSeparated f] in
include hG in
/-- `Lf^*𝒢` has quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_derivedPullback_single (k : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) k).obj
      ((derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G))).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f _
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 G hG) k

omit [Flat f] [QuasiCompact f] [QuasiSeparated f] [IsAffineHom j] [IsAffineHom (j ≫ f)] in
include hF hG in
/-- `ℱ ⊗ᴸ Lj^*Lf^*𝒢` has quasi-coherent cohomology ([Stacks, Tag 08DX] part (1)). -/
theorem isQuasicoherent_homology_affineSupportTensor (k : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) k).obj
      (affineSupportTensor f j F G)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedTensor Z _ _
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 F hF)
    (fun l => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel j _
      (isQuasicoherent_homology_derivedPullback_single f G hG) l) k

/-- **The left side**: `Torᵢ^{𝒪_X}(j_*ℱ, f^*𝒢) ≅ j_*H^{-i}(ℱ ⊗ᴸ Lj^*Lf^*𝒢)`. -/
def torSheafPushforwardIso (p : ℕ) :
    torSheaf X ((Scheme.Modules.pushforward j).obj F) ((Scheme.Modules.pullback f).obj G) p ≅
      (Scheme.Modules.pushforward j).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (-(p : ℤ))).obj
          (affineSupportTensor f j F G)) :=
  have hj := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent j
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj F)
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 F hF)
    ((derivedPullback f.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G))
    (isQuasicoherent_homology_derivedPullback_single f G hG)
  (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (-(p : ℤ))).mapIso
      ((((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).mapIso
          (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
            j 0 F hF)).app _ ≪≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).mapIso
          (singlePullbackIsoDerivedPullback f G)) ≪≫
        @asIso _ _ _ _ _ hj) ≪≫
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso j
      (affineSupportTensor f j F G) (isQuasicoherent_homology_affineSupportTensor f j F hF G hG)
      (-(p : ℤ))

/-- **The right side**: `Torᵢ^{𝒪_Y}(f_*j_*ℱ, 𝒢) ≅ (j ≫ f)_*H^{-i}(ℱ ⊗ᴸ Lj^*Lf^*𝒢)`. -/
def torSheafPushforwardCompIso (p : ℕ) :
    torSheaf Y ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward j).obj F)) G p ≅
      (Scheme.Modules.pushforward (j ≫ f)).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (-(p : ℤ))).obj
          (affineSupportTensor f j F G)) :=
  have hj := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent j
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj F)
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 F hF)
    ((derivedPullback f.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G))
    (isQuasicoherent_homology_derivedPullback_single f G hG)
  have hf := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent f
    ((derivedPushforward j.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj F))
    (fun k => (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) k).mapIso
        (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
          j 0 F hF))
      (AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
        0 _ (AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward j F hF) k))
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 G hG)
  (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (-(p : ℤ))).mapIso
      ((((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).mapIso
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).mapIso
              ((Scheme.Modules.pushforwardComp j f).app F) ≪≫
            Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso
              (j ≫ f) 0 F hF ≪≫
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
              j.toLRSHom.toShHom f.toLRSHom.toShHom).app _).symm)).app _) ≪≫
        @asIso _ _ _ _ _ hf ≪≫
        (derivedPushforward f.toLRSHom.toShHom).mapIso
          (@asIso _ _ _ _ _ hj) ≪≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          j.toLRSHom.toShHom f.toLRSHom.toShHom).app _) ≪≫
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso (j ≫ f)
      (affineSupportTensor f j F G) (isQuasicoherent_homology_affineSupportTensor f j F hF G hG)
      (-(p : ℤ))

/-- **Stacks 0B11, the comparison in the proof of Tag 0B10.** For a flat, quasi-compact and
quasi-separated morphism `f : X ⟶ Y`, a morphism `j : Z ⟶ X` such that `j` and `j ≫ f` are affine,
a quasi-coherent `𝒪_Z`-module `ℱ` and a quasi-coherent `𝒪_Y`-module `𝒢`,

`f_* Torᵢ^{𝒪_X}(j_*ℱ, f^*𝒢) ≅ Torᵢ^{𝒪_Y}(f_*j_*ℱ, 𝒢)`. -/
def pushforwardTorSheafIsoOfIsAffineHom (p : ℕ) :
    (Scheme.Modules.pushforward f).obj
        (torSheaf X ((Scheme.Modules.pushforward j).obj F) ((Scheme.Modules.pullback f).obj G) p) ≅
      torSheaf Y ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward j).obj F)) G p :=
  (Scheme.Modules.pushforward f).mapIso (torSheafPushforwardIso f j F hF G hG p) ≪≫
    (Scheme.Modules.pushforwardComp j f).app _ ≪≫
    (torSheafPushforwardCompIso f j F hF G hG p).symm

end

end Stacks.Intersection.ProjectionFormula

end
