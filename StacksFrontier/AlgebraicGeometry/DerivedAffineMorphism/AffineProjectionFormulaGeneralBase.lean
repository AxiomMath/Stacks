module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaOpenCoverDescent
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.AffineProjectionFormulaDerived
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasicoherentKFlatModelAffine
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for an affine morphism over an arbitrary base

Let `f : X ⟶ S` be an affine morphism of schemes.  This file proves [Stacks, Tag 08I9] in full:
for every object `E` of `D_QCoh(𝒪_S)` the canonical morphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_S} E ⟶ Rf_*Lf^*E`

is an isomorphism, with the genuine derived pullback `Lf^*` and the genuine derived tensor
product `⊗^𝐋`, and with no boundedness, flatness or finiteness hypothesis on `E` and no
hypothesis on `S`.

The proof is the source's, and both of its halves were already in the library; what this file
does is compose them.

* *The question is local on `S`.*
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_of_openCover`
  reduces invertibility for `f` to invertibility for the restrictions `f|_{U_i} : f^{-1}U_i ⟶ U_i`
  over an open cover of `S`, at the restricted complexes, with nothing carried.  Taking `U_i` to
  run through the affine opens of `S` leaves a morphism over an affine base.
* *The affine case.*
  `AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_of_kFlatModel`
  proves invertibility for an affine morphism over an arbitrary base, at any `E` admitting a
  K-flat representative with quasi-coherent terms, and
  `AlgebraicGeometry.exists_kFlat_isQuasicoherent_model_of_isAffine` supplies such a
  representative over an affine scheme.

The only thing the composition needs beyond those two is that the restricted complex still has
quasi-coherent cohomology, which is [Stacks, Tag 08DW] part (1) along an open immersion:
derived pullback along an open immersion is the degreewise pullback
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`, because `j^*` is
exact), the degreewise pullback preserves quasi-coherence ([Stacks, Tag 01BG]) and an exact
functor commutes with cohomology.

## Main results

All three are in the namespace `AlgebraicGeometry.AffineProjectionFormula`.

* `isQuasicoherent_homology_derivedPullback_of_isOpenImmersion`: the derived pullback along an
  open immersion of schemes preserves quasi-coherence of the cohomology sheaves.
* `isIso_pullbackPushforwardTensorMap_of_isAffine`: **the affine case of [Stacks, Tag 08I9] over
  an arbitrary affine base.**
* `isIso_pullbackPushforwardTensorMap_unconditional`: **[Stacks, Tag 08I9].**

## Implementation notes

*`HasDerivedCategory.standard` is installed at priority `10000`*, as in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/AffineProjectionFormulaDerived.lean`.  Both
inputs of the composition are stated at the standard model: the affine case because its file
installs the attribute at that priority, and the localization half because the import closure of
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/ProjectionFormulaOpenCoverDescent.lean`
does not contain `StacksFrontier.Homology.DerivedCategory.LocallySmall`, so the default-priority
attribute there is already effective.

*The reducibility attributes* collapse the two spellings of the category of `𝒪_X`-modules, as in
the file of the affine case; the cover is indexed by `AlgebraicGeometry.Scheme.affineOpens`, so
the base of each restricted morphism is `U.toScheme` for an affine open `U` and the complexes
live in `SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedProjectionFormula (pullbackPushforwardTensorMap'
  isIso_pullbackPushforwardTensorMap_of_openCover)

universe u

namespace AlgebraicGeometry.AffineProjectionFormula

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules structureSheafRing
  TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **[Stacks, Tag 08DW] part (1) along an open immersion.**  If every cohomology sheaf of `E` in
`D(𝒪_Y)` is quasi-coherent then so is every cohomology sheaf of `Lg^*E` for `g : X ⟶ Y` an open
immersion of schemes.

Pullback along an open immersion is exact, so `Lg^* = D(g^*)`
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`); an exact functor
commutes with cohomology degreewise, and `g^*` preserves quasi-coherence by
[Stacks, Tag 01BG]. -/
theorem isQuasicoherent_homology_derivedPullback_of_isOpenImmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] (E : DerivedCategory Y.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((derivedPullback g.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  refine (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor X.Modules n).mapIso
        ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
          g.toLRSHom.toShHom).app E)) ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (modulePullback g.toLRSHom.toShHom) n).app E).symm ?_
  exact @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    g.toLRSHom.toShHom ((DerivedCategory.homologyFunctor Y.Modules n).obj E) (hE n)

/-- **The affine case of [Stacks, Tag 08I9] over an arbitrary affine base.**  Let `f : X ⟶ Y` be
an affine morphism of schemes with `Y` an affine *scheme* — not necessarily a spectrum — and let
`K` be an object of `D(𝒪_Y)` all of whose cohomology sheaves are quasi-coherent.  Then

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`

is invertible, with the genuine derived pullback and the genuine derived tensor product, and with
no boundedness, flatness or finiteness hypothesis.

This is `isIso_pullbackPushforwardTensorMap_of_kFlatModel` at the representative supplied by
`AlgebraicGeometry.exists_kFlat_isQuasicoherent_model_of_isAffine`; the latter is the spectrum
statement `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model` transported along
`AlgebraicGeometry.Scheme.isoSpec`. -/
theorem isIso_pullbackPushforwardTensorMap_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [IsAffine Y] (K : DerivedCategory Y.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsQuasicoherent) :
    IsIso (pullbackPushforwardTensorMap' f.toLRSHom.toShHom K) := by
  obtain ⟨C, hCq, hCk, ⟨e⟩⟩ := exists_kFlat_isQuasicoherent_model_of_isAffine Y K hK
  exact isIso_pullbackPushforwardTensorMap_of_kFlatModel f K C hCq hCk e

/-- **Stacks, Tag 08I9.**  Let `f : X ⟶ S` be an affine morphism of schemes and let `E` be an
object of `D_QCoh(𝒪_S)`, that is, an object of `D(𝒪_S)` all of whose cohomology sheaves are
quasi-coherent.  Then the canonical morphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_S} E ⟶ Rf_*Lf^*E`

is an isomorphism.  The derived pullback is the genuine `Lf^*` of [Stacks, Tag 06YJ], the tensor
product is the genuine `⊗^𝐋`, and there is no boundedness, flatness or finiteness hypothesis on
`E` and no hypothesis on `S`.

The proof is the source's.  The question is local on `S`, which is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_of_openCover` over
the cover of `S` by its affine opens; each restriction `f|_U` is an affine morphism over an affine
scheme, and the restricted complex still has quasi-coherent cohomology by
`isQuasicoherent_homology_derivedPullback_of_isOpenImmersion`, so
`isIso_pullbackPushforwardTensorMap_of_isAffine` applies to it. -/
@[stacks 08I9 "the canonical morphism Rf_*O_X ⊗^L E ⟶ Rf_*Lf^*E is invertible for every affine \
morphism of schemes f : X ⟶ S and every object E of D_QCoh(O_S), with the genuine derived \
pullback Lf^* and the genuine derived tensor product ⊗^L, no boundedness, flatness or finiteness \
hypothesis on E and no hypothesis on S"]
theorem isIso_pullbackPushforwardTensorMap_unconditional {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] (E : DerivedCategory S.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor S.Modules n).obj E).IsQuasicoherent) :
    IsIso (pullbackPushforwardTensorMap' f.toLRSHom.toShHom E) := by
  refine isIso_pullbackPushforwardTensorMap_of_openCover f (fun V : S.affineOpens => V.1)
    (fun y => ?_) E fun V => ?_
  · have hy : y ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
      rw [iSup_affineOpens_eq_top S]; trivial
    exact (TopologicalSpace.Opens.mem_iSup).1 hy
  · have : IsAffineHom (f ∣_ (V : S.Opens)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict f (V : S.Opens)).flip inferInstance
    exact isIso_pullbackPushforwardTensorMap_of_isAffine (f ∣_ (V : S.Opens)) _
      (isQuasicoherent_homology_derivedPullback_of_isOpenImmersion (V : S.Opens).ι E hE)

end AlgebraicGeometry.AffineProjectionFormula

end
