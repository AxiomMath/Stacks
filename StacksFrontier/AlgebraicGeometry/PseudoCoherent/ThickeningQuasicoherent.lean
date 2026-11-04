module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Descent.PushforwardQcohConjugate
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes

/-!
# Quasi-coherent cohomology along an affine finite-order thickening

Let `f : R ⟶ S` be a surjection of commutative rings whose kernel is nilpotent, so that
`i = Spec f : Spec S ⟶ Spec R` is a finite-order thickening, and let `A` be an object of
`D(𝒪_{Spec R})` whose derived pullback `Li^*A` is pseudo-coherent. This file proves that the
cohomology sheaves of `A` are all quasi-coherent, that is, that `A` lies in
`D_QCoh(𝒪_{Spec R})`.

That is the first paragraph of the source's proof of [Stacks, Tag 0DJX], and it is the one
hypothesis that
`Stacks.Thickenings.isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent` of
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningAffine` carries beyond the rest of the
development; with this file that hypothesis can be discharged, and the affine case of
[Stacks, Tag 0DJX] — hence, through
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.Thickening`, the tag itself — is unconditional.

## Main results

* `Stacks.Thickenings.isQuasicoherent_homology_specDerivedTensor` — **[Stacks, Tag 08DX]
  part (1) on an affine scheme, at the standard model of the derived category.** `D_QCoh` is
  closed under `⊗ᴸ` on `Spec R`.
* `Stacks.Thickenings.exists_iso_derivedPushforward_derivedTensor_of_isClosedEmbedding` and
  `Stacks.Thickenings.exists_iso_derivedPushforward_derivedTensor_obj` — **the projection
  formula for a closed embedding of ringed spaces at the level of objects of the derived
  category**, the content of [Stacks, Tag 0B55] that the dévissage needs.
* `Stacks.Thickenings.isQuasicoherent_homology_of_isPseudoCoherent_derivedPullback_specMap` —
  **the quasi-coherence half of the affine case of [Stacks, Tag 0DJX]**, the goal of the file.

## Supporting definitions

* `Stacks.Thickenings.specDerivedTensor` — `⊗ᴸ_{𝒪_{Spec R}}` at the standard model.
* `Stacks.Thickenings.derivedPushforwardQIsoOfIsClosedEmbedding` — `i_* = Ri_*` for a closed
  embedding: `Ri_*(QC) ≅ Q(i_*C)` for every complex `C`.
* `Stacks.Thickenings.derivedPushforwardSingleIso` — the same on a module placed in degree zero.
* `Stacks.Thickenings.specDerivedTensorUnitIso` — `𝒪_{Spec R}[0] ⊗ᴸ A ≅ A`.

## The three steps

**[Stacks, Tag 08DX] at the standard model.**
`Stacks.Duality.isQuasicoherent_homology_derivedTensor` is the tag for an arbitrary scheme, but
at the *locally small* model of the derived category. Its
file records that as forced by the essential surjectivity of derived sheafification,
[Stacks, Tag 06Z0], being available only there. That is no longer so — it is
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` — and since that is the only
locally small-pinned input of the affine case, the affine case runs verbatim at the standard
model. It is reproved here rather than transported, because transport would need an equivalence
of the two models identified with derived sheafification; every other input
(`AlgebraicGeometry.affineTensorComplexIso`, `AlgebraicGeometry.kFlat_tilde`,
`CochainComplex.KFlat.chosenResolution`) mentions no derived category or carries a free model
binder.

**The projection formula for a closed embedding.** For `i : X ⟶ Y` a morphism of ringed spaces
whose underlying map is a homeomorphism onto a closed subset, and arbitrary `F ∈ D(𝒪_X)` and
`E ∈ D(𝒪_Y)`, there is an object `D` of `D(𝒪_X)` with `D ≅ F ⊗ᴸ_{𝒪_X} Li^*E` and
`(Ri_*F) ⊗ᴸ_{𝒪_Y} E ≅ Ri_*D`. **What is not proved is that the second isomorphism is the
projection-formula morphism of [Stacks, Tag 0B53]**, and that is why no declaration here carries
the tag 0B55 for its conclusion: the mate computation identifying the two is still absent, and
is described in the module notes of
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso`. The
dévissage does not need it — only membership in a subcategory closed under isomorphism is
transported — so `D` is produced directly from a K-flat presentation: `E` is replaced by a K-flat
complex `B^•` and `F` by the class of an arbitrary complex `A^•`, and then the chain-level
isomorphism `Tot(i_*A^• ⊗ B^•) ≅ i_*Tot(A^• ⊗ i^*B^•)` of
`complexProjectionFormulaIso` is read on both sides through the one-sided K-flat comparison
`comparisonRight` of the two derived tensor products, through
`Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat` (so that `i^*B^•`
computes `Li^*E`, the pullback being K-flat by [Stacks, Tag 06YC]) and through
`derivedPushforwardQIsoOfIsClosedEmbedding` (so that `i_*` computes `Ri_*`). Only the *right*
one-sided comparison is used, so no flatness is imposed on `A^•`.

**The dévissage.** `Stacks.Thickenings.prop_of_isNilpotent_of_smul_eq_bot` reduces the property
`P N`, that `Ñ[0] ⊗ᴸ_{𝒪_{Spec R}} A` has quasi-coherent cohomology, from `N = R` — where the unit
`specDerivedTensorUnitIso` turns `P R` into the conclusion — to modules annihilated by
`I = ker f`, through extensions. Stability under extensions is the five-term weak Serre property
of the quasi-coherent modules ([Stacks, Tag 01LA]) applied to the distinguished triangle obtained
by tensoring with `A` the triangle of a short exact sequence of associated sheaves; `M ↦ M̃` is
exact by `AlgebraicGeometry.tilde.preservesFiniteLimits`, and `- ⊗ᴸ A` is exact by the
`exact_left` field of the derived tensor product. A module annihilated by `I` is restricted from
an `S`-module `M` by `Stacks.Thickenings.exists_restrictScalars_iso_of_smul_eq_bot`, so that
`Ñ ≅ i_*(M̃)` by `Stacks.Descent.restrictScalarsCompTildeIso`; the projection formula above then
writes `Ñ[0] ⊗ᴸ A` as `Ri_*D` with `D ≅ M̃[0] ⊗ᴸ_{𝒪_{Spec S}} Li^*A`, whose two factors are in
`D_QCoh(𝒪_{Spec S})` — the first because `M̃` is quasi-coherent, the second by
[Stacks, Tag 08E5] applied to the pseudo-coherence hypothesis. So `D` is in `D_QCoh` by the first
step and `Ri_*D` by [Stacks, Tag 08D5].

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of the pseudo-coherence
development, and the local instance carries a high priority because the import closure also
supplies the global locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which a default-priority local
attribute would not beat. No transport between models occurs: `complexProjectionFormulaIso` and
the chain-level K-flatness statements mention no derived category,
`Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat` and
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` carry free model binders, and
[Stacks, Tag 08D5] and the unit of the derived tensor product are themselves stated at the
standard model.

*The spellings of the category of modules.* `(Spec R).Modules`,
`StrictlyPerfect.OXMod (Spec R).toRingedSpace`,
`SheafOfModules (structureSheafRing (Spec R).toRingedSpace)` and
`Stacks.DerivedTensor.RingedSite.Modules (Spec R).sheaf` are one type with one set of instances
up to `rfl`, but `AlgebraicGeometry.Scheme.Modules` is not reducible, so instance search does not
cross between them. Every crossing below is therefore made by a type ascription in term position
— in particular the two `let`s giving `(- ⊗ᴸ A)` its `CommShift` and `IsTriangulated` instances
at the `specDerivedTensor` spelling, where searching for them at the ringed-site spelling
instead fails on the additivity of the shift functors.

*Why the unit isomorphism needs its instances reseated.* The unit of the derived tensor product
is stated over a `AlgebraicGeometry.RingedSite`, and `Stacks.Thickenings.specRingedSite` unfolds
to `Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace`, a plain `def`; so instance search
does not see that its sheaf of rings is the structure sheaf of `Spec R`, and the three instance
arguments of the ringed-site statement are supplied explicitly in
`specDerivedTensorUnitIso`. This is the same device, for the same reason, as the explicit
binders of `Stacks.Cohomology.PerfectPushforward.tensorStructureComplexIso`.

## References

* [Stacks Project, Tag 0DJX](https://stacks.math.columbia.edu/tag/0DJX)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StrictlyPerfect
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Thickenings

/-! ### The derived tensor product on an affine scheme, at the standard model -/

/-- Quasi-coherence of the `n`-th cohomology sheaf transfers backwards along an isomorphism. -/
private theorem isQuasicoherent_homology_of_iso {X : Scheme.{u}} {A B : DerivedCategory X.Modules}
    (e : A ≅ B) (n : ℤ)
    (h : ((DerivedCategory.homologyFunctor X.Modules n).obj B).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules n).mapIso e).symm h

/-- **`⊗ᴸ_{𝒪_{Spec R}}` at the standard model of the derived category.** This is the derived
tensor product of [Stacks, Tag 06YH] on the ringed space underlying `Spec R`, with the two
derived categories taken at `CategoryTheory.HasDerivedCategory.standard`.

It is not `Stacks.Duality.derivedTensor (Spec R)`, which is the same bifunctor at the locally
small model. -/
public abbrev specDerivedTensor (R : CommRingCat.{u}) :
    DerivedCategory (Spec R).Modules ⥤ DerivedCategory (Spec R).Modules ⥤
      DerivedCategory (Spec R).Modules :=
  (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor

/-- **On K-flat complexes, the derived tensor product of two derived sheafifications is the
derived sheafification of the ordinary total tensor complex**, at the standard model: for K-flat
complexes `P` and `P'` of `R`-modules,

`P̃ ⊗ᴸ_{𝒪_{Spec R}} P̃' ≅ (Tot(P ⊗_R P'))~`.

This is `Stacks.Duality.derivedTensorDerivedTildeIsoOfKFlat` at the standard model; the proof is
that one, and every input is model-free. Derived sheafification of the class of a complex is the
class of the degreewise sheafification, by `CategoryTheory.Functor.mapDerivedCategoryFactors`;
the sheafification of a K-flat complex is K-flat ([Stacks, Tag 08DV],
`AlgebraicGeometry.kFlat_tilde`), so the `comparison` field of the derived tensor product on
`Spec R` computes the left-hand side as the class of `Tot(P̃ ⊗_{𝒪_{Spec R}} P̃')`; and that
complex is the sheafification of `Tot(P ⊗_R P')`, by the totalised affine tensor comparison
`AlgebraicGeometry.affineTensorComplexIso` of [Stacks, Tag 08DX] part (2). -/
public def derivedTensorDerivedTildeIsoOfKFlatStandard (R : CommRingCat.{u})
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P') :
    ((specDerivedTensor R).obj
          ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P')) ≅
      (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj (P ⊗ P')) :=
  ((specDerivedTensor R).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P)).app _ ≪≫
    ((specDerivedTensor R).obj
        (DerivedCategory.Q.obj (tildeComplexMod P))).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P') ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).comparison _ _
      (kFlat_tilde P hP) (kFlat_tilde P' hP') ≪≫
    DerivedCategory.Q.mapIso (affineTensorComplexIso R P P').1.symm ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app (P ⊗ P')).symm

/-- **The derived tensor product of two derived sheafifications is a derived sheafification**, at
the standard model: for `M, N` in `D(R)` there is an object `W` of `D(R)` and an isomorphism
`M̃ ⊗ᴸ_{𝒪_{Spec R}} Ñ ≅ W̃`.

Replace `M` and `N` by K-flat representatives `P` and `P'`; then
`derivedTensorDerivedTildeIsoOfKFlatStandard` exhibits `W = Q(Tot(P ⊗_R P'))`. This is weaker
than [Stacks, Tag 08DX] part (2), which identifies the left-hand side with `(M ⊗ᴸ_R N)~`; it is
what the proof of part (1) consumes. -/
public theorem exists_iso_derivedTilde_derivedTensor_standard (R : CommRingCat.{u})
    (M N : DerivedCategory (ModuleCat.{u} R)) :
    ∃ W : DerivedCategory (ModuleCat.{u} R),
      Nonempty ((((specDerivedTensor R).obj ((tilde.functor R).mapDerivedCategory.obj M)).obj
        ((tilde.functor R).mapDerivedCategory.obj N)) ≅
          (tilde.functor R).mapDerivedCategory.obj W) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := Stacks.Duality.exists_kFlat_module_complex_iso R M
  obtain ⟨P', hP', ⟨eP'⟩⟩ := Stacks.Duality.exists_kFlat_module_complex_iso R N
  refine ⟨DerivedCategory.Q.obj (P ⊗ P'), ⟨?_⟩⟩
  exact ((specDerivedTensor R).mapIso
      ((tilde.functor R).mapDerivedCategory.mapIso eP.symm)).app _ ≪≫
    ((specDerivedTensor R).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))).mapIso
      ((tilde.functor R).mapDerivedCategory.mapIso eP'.symm) ≪≫
    derivedTensorDerivedTildeIsoOfKFlatStandard R P P' hP hP'

/-- **[Stacks, Tag 08DX] part (1) on an affine scheme, at the standard model.** If every
cohomology sheaf of `A` and of `B` is quasi-coherent, then so is every cohomology sheaf of
`A ⊗ᴸ_{𝒪_{Spec R}} B`.

This is `Stacks.Duality.isQuasicoherent_homology_derivedTensor_spec`, whose only locally
small-pinned input was essential surjectivity of derived sheafification, [Stacks, Tag 06Z0];
that is available at the standard model as
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, so the argument runs verbatim.
`A` and `B` are derived sheafifications of complexes of `R`-modules,
`exists_iso_derivedTilde_derivedTensor_standard` makes their derived tensor product one as well,
and the cohomology sheaves of a derived sheafification are quasi-coherent by construction. -/
@[stacks 08DX "part (1) on an affine scheme, at the standard model of the derived category"]
public theorem isQuasicoherent_homology_specDerivedTensor (R : CommRingCat.{u})
    (A B : DerivedCategory (Spec R).Modules)
    (hA : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj A).IsQuasicoherent)
    (hB : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj B).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      (((specDerivedTensor R).obj A).obj B)).IsQuasicoherent := by
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R A hA
  obtain ⟨N, ⟨eN⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R B hB
  obtain ⟨W, ⟨eW⟩⟩ := exists_iso_derivedTilde_derivedTensor_standard R M N
  have e : ((specDerivedTensor R).obj A).obj B ≅
      (tilde.functor R).mapDerivedCategory.obj W :=
    (((specDerivedTensor R).mapIso eM).app B).symm ≪≫
      ((specDerivedTensor R).obj
        ((tilde.functor R).mapDerivedCategory.obj M)).mapIso eN.symm ≪≫ eW
  exact isQuasicoherent_homology_of_iso e i
    (isQuasicoherent_homology_mapDerivedCategory_obj R W i)

/-! ### The derived pushforward along a closed embedding, computed termwise -/

section ClosedEmbedding

open RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (g : X ⟶ Y)

/-- **`Rg_*` is computed by applying `g_*` termwise**, for a morphism of ringed spaces whose
underlying continuous map is a homeomorphism onto a closed subset: for every complex `C` of
`𝒪_X`-modules, `Rg_*(QC) ≅ Q(g_*C)`.

Pushforward along such a `g` is exact ([Stacks, Tag 08KS],
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`), so the functor it induces on
derived categories is already a total right derived functor; the isomorphism of the two models is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, and
`CategoryTheory.Functor.mapDerivedCategoryFactors` evaluates the induced functor on the class of
a complex. -/
public def derivedPushforwardQIsoOfIsClosedEmbedding
    (hg : Topology.IsClosedEmbedding (ConcreteCategory.hom g.hom.base))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPushforward g).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (((modulePushforward g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C) :=
  letI := Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward g hg
  ((Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      (modulePushforward g)).app (DerivedCategory.Q.obj C)).symm ≪≫
    (modulePushforward g).mapDerivedCategoryFactors.app C

/-! ### The projection formula for a closed embedding, on objects -/

/-- **The projection formula for a closed embedding, at the level of objects of the derived
category** — the content of [Stacks, Tag 0B55] that the dévissage of [Stacks, Tag 0DJX] uses.

Let `g : X ⟶ Y` be a morphism of ringed spaces whose underlying map is a homeomorphism onto a
closed subset, let `A^•` be an arbitrary complex of `𝒪_X`-modules and let `E` be an arbitrary
object of `D(𝒪_Y)`. Then there is an object `D` of `D(𝒪_X)` with

`D ≅ (QA^•) ⊗ᴸ_{𝒪_X} Lg^*E` and `(Q(g_*A^•)) ⊗ᴸ_{𝒪_Y} E ≅ Rg_* D`.

What is *not* claimed is that the second isomorphism is the projection-formula morphism of
[Stacks, Tag 0B53]; only the existence of an isomorphism of the two objects is produced, which
is all that is needed to transport membership in a subcategory closed under isomorphism. The
route is the one recorded in the module notes of the file declaring
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso`:
represent `E` by a K-flat complex `B^•`, take
`D = Q(Tot(A^• ⊗_{𝒪_X} g^*B^•))`, and read the two sides off the chain-level isomorphism
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso`
through the one-sided K-flat comparisons of the two derived tensor products. The pullback
`g^*B^•` is K-flat by [Stacks, Tag 06YC]
(`Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional`) and computes `Lg^*E`
by `Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat`. -/
public theorem exists_iso_derivedPushforward_derivedTensor_of_isClosedEmbedding
    (hg : Topology.IsClosedEmbedding (ConcreteCategory.hom g.hom.base))
    (A : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) ℤ)
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)) :
    ∃ D : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf),
      Nonempty (D ≅ (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj
        (DerivedCategory.Q.obj A)).obj
          ((derivedPullback g).obj E))) ∧
      Nonempty ((((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.obj
        (DerivedCategory.Q.obj (((modulePushforward g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A))).obj E) ≅ (derivedPushforward g).obj D) := by
  obtain ⟨B, p, hB, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Y.sheaf
    (DerivedCategory.Q.objPreimage E)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := Stacks.DerivedTensor.RingedSite.Modules Y.sheaf) p).2 hp
  have eB : (DerivedCategory.Q.obj B :
      DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)) ≅ E :=
    @asIso _ _ _ _ (DerivedCategory.Q.map p) hiso ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hpull := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat g B hB
  have ePull : (DerivedCategory.Q.obj (((modulePullback g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj B) :
        DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)) ≅
      (derivedPullback g).obj E :=
    (@asIso _ _ _ _ ((Stacks.DerivedPullback.derivedPullbackComplexComparison g).app B)
      hpull).symm ≪≫ (derivedPullback g).mapIso eB
  refine ⟨DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj A).obj
    (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)), ⟨?_⟩, ⟨?_⟩⟩
  · exact ((Stacks.Cohomology.TorAmplitude.derTensor X).comparisonRight A _
      (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional g B hB)).symm ≪≫
        ((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj
          (DerivedCategory.Q.obj A)).mapIso ePull
  · exact (((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.obj
        (DerivedCategory.Q.obj (((modulePushforward g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A))).mapIso eB).symm ≪≫
      (Stacks.Cohomology.TorAmplitude.derTensor Y).comparisonRight _ B hB ≪≫
      DerivedCategory.Q.mapIso
        (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso
          g hg A B) ≪≫
      (derivedPushforwardQIsoOfIsClosedEmbedding g hg _).symm

/-- **The projection formula for a closed embedding, between objects of the two derived
categories** — [Stacks, Tag 0B55] in the form the dévissage of [Stacks, Tag 0DJX] consumes.

For a morphism of ringed spaces `g : X ⟶ Y` which is a homeomorphism onto a closed subset and
arbitrary objects `F` of `D(𝒪_X)` and `E` of `D(𝒪_Y)` there is an object `D` of `D(𝒪_X)` with

`D ≅ F ⊗ᴸ_{𝒪_X} Lg^*E` and `(Rg_*F) ⊗ᴸ_{𝒪_Y} E ≅ Rg_* D`.

As in `exists_iso_derivedPushforward_derivedTensor_of_isClosedEmbedding`, the second isomorphism
is *not* claimed to be the projection-formula morphism of [Stacks, Tag 0B53]; only the two
objects are identified, which is what transports membership in `D_QCoh`.

`F` is replaced by the class of an arbitrary complex `A^•`, on which `Rg_*` is computed termwise
by `derivedPushforwardQIsoOfIsClosedEmbedding`, and the complex-level statement is
`exists_iso_derivedPushforward_derivedTensor_of_isClosedEmbedding`. -/
public theorem exists_iso_derivedPushforward_derivedTensor_obj
    (hg : Topology.IsClosedEmbedding (ConcreteCategory.hom g.hom.base))
    (F : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf))
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)) :
    ∃ D : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf),
      Nonempty (D ≅ (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj F).obj
        ((derivedPullback g).obj E))) ∧
      Nonempty ((((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.obj
        ((derivedPushforward g).obj F)).obj E) ≅ (derivedPushforward g).obj D) := by
  have eA : (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage F) :
      DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)) ≅ F :=
    DerivedCategory.Q.objObjPreimageIso F
  obtain ⟨D, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_iso_derivedPushforward_derivedTensor_of_isClosedEmbedding g hg
    (DerivedCategory.Q.objPreimage F) E
  refine ⟨D, ⟨e₁ ≪≫ (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso eA).app _)⟩,
    ⟨?_⟩⟩
  exact ((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.mapIso
      (((derivedPushforward g).mapIso eA).symm ≪≫
        derivedPushforwardQIsoOfIsClosedEmbedding g hg _)).app E ≪≫ e₂

end ClosedEmbedding

/-! ### The thickening `Spec S ⟶ Spec R` of a surjection of rings -/

section Affine

open RingedSpaceModuleAdjunction

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- **A surjection of rings induces a closed embedding of spectra.** The morphism of ringed
spaces underlying `Spec f` is a homeomorphism onto a closed subset, which is the hypothesis the
projection formula for a closed embedding takes. -/
public theorem isClosedEmbedding_specMap (hf : Function.Surjective f.hom) :
    Topology.IsClosedEmbedding (ConcreteCategory.hom
      ((Spec.map f).toLRSHom.toShHom).hom.base) :=
  have := AlgebraicGeometry.IsClosedImmersion.spec_of_surjective f hf
  (Spec.map f).isClosedEmbedding

end Affine

/-! ### Two auxiliary identifications -/

/-- **A quasi-coherent module placed in degree zero lies in `D_QCoh(𝒪_X)`.** Its cohomology is
the module itself in degree zero and zero elsewhere, and the quasi-coherent modules are a weak
Serre subcategory ([Stacks, Tag 01LA]) and so contain the zero module. -/
public theorem isQuasicoherent_homology_singleFunctor_obj (X : Scheme.{u})
    (M : X.Modules) (hM : M.IsQuasicoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsQuasicoherent :=
  (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) M hM).2 n

section ClosedEmbeddingSingle

open RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (g : X ⟶ Y)

/-- **`Rg_*` of a module placed in degree zero is its pushforward placed in degree zero**, for a
morphism of ringed spaces whose underlying continuous map is a homeomorphism onto a closed
subset. This is `derivedPushforwardQIsoOfIsClosedEmbedding` read through
`CategoryTheory.HomologicalComplex.singleMapHomologicalComplex`, which says that applying `g_*`
termwise to a complex concentrated in degree zero gives a complex concentrated in degree
zero. -/
public def derivedPushforwardSingleIso
    (hg : Topology.IsClosedEmbedding (ConcreteCategory.hom g.hom.base))
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedPushforward g).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
        ((modulePushforward g).obj M) :=
  (derivedPushforward g).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (structureSheafRing X)) 0).app M) ≪≫
    derivedPushforwardQIsoOfIsClosedEmbedding g hg _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward g) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing Y)) 0).app
      ((modulePushforward g).obj M)).symm

end ClosedEmbeddingSingle

/-! ### The dévissage -/

section Devissage

open RingedSpaceModuleAdjunction

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The ringed site of the opens of `Spec R`. The unit of the derived tensor product of
[Stacks, Tag 06YU] is stated over a ringed site, and this is the one whose sheaf of rings is
`𝒪_{Spec R}`. -/
public abbrev specRingedSite (R : CommRingCat.{u}) : RingedSite.{u, u, u} :=
  Stacks.Cohomology.SpaceInverseSystems.ringedSiteOfSpace (Spec R).toRingedSpace

/-- **The unit of the derived tensor product on `Spec R`:** `𝒪_{Spec R}[0] ⊗ᴸ A ≅ A`, with the
structure sheaf spelled as the module associated to `R` itself.

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso` states this over a ringed
site with the unit sheaf of modules; `AlgebraicGeometry.tildeSelf` identifies `R̃` with that unit.
The three instance arguments that the ringed-site statement carries have to be reseated by hand:
`Stacks.Thickenings.specRingedSite` is a `def` behind the scenes, so instance search does not
see that its sheaf of rings is the structure sheaf of `Spec R`. -/
public def specDerivedTensorUnitIso (R : CommRingCat.{u})
    (A : DerivedCategory (Spec R).Modules) :
    ((specDerivedTensor R).obj ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        ((tilde.functor R).obj (ModuleCat.of R (R : Type u))))).obj A ≅ A :=
  letI : (Stacks.SheafOfModules.Tensor.sheafTensor (specRingedSite R).O).Additive :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive
      (Spec R).toRingedSpace
  letI : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor (specRingedSite R).O).obj M).Additive :=
    fun M => AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive
      (Spec R).toRingedSpace M
  letI : ∀ K L : CochainComplex
      (Stacks.DerivedTensor.RingedSite.Modules (specRingedSite R).O) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (specRingedSite R).O) (ComplexShape.up ℤ) :=
    fun K L => AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor
      (Spec R).toRingedSpace K L
  ((specDerivedTensor R).mapIso ((DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso
      AlgebraicGeometry.tildeSelf)).app A ≪≫
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso (specRingedSite R)
      (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace) A

/-- **The quasi-coherence half of [Stacks, Tag 0DJX] in the affine case.** Let `f : R ⟶ S` be a
surjection of commutative rings with nilpotent kernel, so that `i = Spec f` is a finite-order
thickening, and let `A` be an object of `D(𝒪_{Spec R})` whose derived pullback `Li^*A` is
pseudo-coherent. Then every cohomology sheaf of `A` is quasi-coherent, that is, `A` lies in
`D_QCoh(𝒪_{Spec R})`.

This is the first paragraph of the source's proof. The dévissage is on the kernel ideal
`I = ker f`: writing `P` for the property of an `R`-module `N` that `Ñ[0] ⊗ᴸ_{𝒪_{Spec R}} A` has
quasi-coherent cohomology, `Stacks.Thickenings.prop_of_isNilpotent_of_smul_eq_bot` reduces `P` for
every module — in particular for `R` itself, where the unit of the derived tensor product
identifies `𝒪_{Spec R}[0] ⊗ᴸ A` with `A` — to `P` for a module annihilated by `I`.

*The inductive step.* `P` is stable under extensions: a short exact sequence of `R`-modules
becomes a short exact sequence of `𝒪_{Spec R}`-modules, `M ↦ M̃` being exact
(`AlgebraicGeometry.tilde.preservesFiniteLimits`), hence a distinguished triangle
(`CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`); the derived tensor
product is exact in its left variable, so tensoring with `A` keeps the triangle distinguished;
and the quasi-coherent modules form a weak Serre subcategory ([Stacks, Tag 01LA]), so the middle
vertex of a distinguished triangle whose outer vertices lie in `D_QCoh` lies in `D_QCoh`.

*The base case.* A module `N` annihilated by `I` is the restriction of scalars of an `S`-module
`M` (`Stacks.Thickenings.exists_restrictScalars_iso_of_smul_eq_bot`), and then
`Ñ ≅ i_*(M̃)` (`Stacks.Descent.restrictScalarsCompTildeIso`). The projection formula for the
closed embedding `i`, in the form
`exists_iso_derivedPushforward_derivedTensor_obj`, produces `D` in `D(𝒪_{Spec S})` with
`i_*(M̃)[0] ⊗ᴸ_{𝒪_{Spec R}} A ≅ Ri_*D` and `D ≅ M̃[0] ⊗ᴸ_{𝒪_{Spec S}} Li^*A`; the second
factor of the latter is in `D_QCoh(𝒪_{Spec S})` by [Stacks, Tag 08E5], the first because `M̃` is
quasi-coherent, so `D` is by [Stacks, Tag 08DX] in the form
`isQuasicoherent_homology_specDerivedTensor`, and `Ri_*D` is by [Stacks, Tag 08D5].

Note that `i_* = Ri_*` here, which is `derivedPushforwardQIsoOfIsClosedEmbedding`, and that no
identification of the isomorphism with the canonical projection-formula morphism of
[Stacks, Tag 0B53] is needed: only membership in `D_QCoh` is transported. -/
@[stacks 0DJX "the quasi-coherence of the cohomology, in the affine case"]
public theorem isQuasicoherent_homology_of_isPseudoCoherent_derivedPullback_specMap
    (hf : Function.Surjective f.hom) (hnil : IsNilpotent (RingHom.ker f.hom))
    (A : DerivedCategory (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace))
    (hA : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := (Spec S).toRingedSpace)
      ((derivedPullback (Spec.map f).toLRSHom.toShHom).obj A)) :
    ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj A).IsQuasicoherent := by
  have hg := isClosedEmbedding_specMap f hf
  have hpull : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec S).Modules n).obj
      ((derivedPullback (Spec.map f).toLRSHom.toShHom).obj A)).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent (Spec S) _ hA
  set P : ModuleCat.{u} R → Prop := fun N => ∀ n : ℤ,
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (((specDerivedTensor R).obj ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        ((tilde.functor R).obj N))).obj A)).IsQuasicoherent with hPdef
  have hext : ∀ C : ShortComplex (ModuleCat.{u} R), C.ShortExact → P C.X₁ → P C.X₃ → P C.X₂ := by
    intro C hC h1 h3
    let : PreservesFiniteLimits (tilde.functor R) :=
      AlgebraicGeometry.tilde.preservesFiniteLimits R
    let : PreservesFiniteColimits (tilde.functor R) :=
      Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
    have hTilde : (C.map (tilde.functor R)).ShortExact := hC.map_of_exact (tilde.functor R)
    let : ((specDerivedTensor R).flip.obj A).CommShift ℤ :=
      (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).commShift_left A
    let : ((specDerivedTensor R).flip.obj A).IsTriangulated :=
      (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).exact_left A
    exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre (Spec R))
      _ (Functor.map_distinguished ((specDerivedTensor R).flip.obj A) _
        hTilde.singleTriangle_distinguished) h1 h3
  have hbase : ∀ N : ModuleCat.{u} R,
      RingHom.ker f.hom • (⊤ : Submodule R N) = ⊥ → P N := by
    intro N hN
    obtain ⟨M, ⟨eM⟩⟩ := exists_restrictScalars_iso_of_smul_eq_bot f.hom hf N hN
    have e1 : (tilde.functor R).obj N ≅
        (modulePushforward (Spec.map f).toLRSHom.toShHom).obj ((tilde.functor S).obj M) :=
      ((tilde.functor R).mapIso eM).symm ≪≫ (Stacks.Descent.restrictScalarsCompTildeIso f).app M
    obtain ⟨D, ⟨eD⟩, ⟨eRD⟩⟩ := exists_iso_derivedPushforward_derivedTensor_obj
      (Spec.map f).toLRSHom.toShHom hg
      ((DerivedCategory.singleFunctor (Spec S).Modules 0).obj ((tilde.functor S).obj M)) A
    have hD : ∀ n : ℤ,
        ((DerivedCategory.homologyFunctor (Spec S).Modules n).obj D).IsQuasicoherent := by
      intro n
      refine isQuasicoherent_homology_of_iso eD n ?_
      exact isQuasicoherent_homology_specDerivedTensor S _ _
        (isQuasicoherent_homology_singleFunctor_obj (Spec S) _ inferInstance) hpull n
    have hRD : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((derivedPushforward (Spec.map f).toLRSHom.toShHom).obj D)).IsQuasicoherent :=
      AlgebraicGeometry.isQuasicoherent_derivedPushforward (Spec.map f) ⟨D, hD⟩
    intro n
    refine isQuasicoherent_homology_of_iso ?_ n (hRD n)
    exact ((specDerivedTensor R).mapIso
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso e1 ≪≫
      (derivedPushforwardSingleIso (Spec.map f).toLRSHom.toShHom hg
        ((tilde.functor S).obj M)).symm)).app A ≪≫ eRD
  have hR := prop_of_isNilpotent_of_smul_eq_bot (RingHom.ker f.hom) hnil P hext hbase
    (ModuleCat.of R (R : Type u))
  intro n
  exact isQuasicoherent_homology_of_iso (specDerivedTensorUnitIso R A).symm n (hR n)

end Devissage

end Stacks.Thickenings

end
