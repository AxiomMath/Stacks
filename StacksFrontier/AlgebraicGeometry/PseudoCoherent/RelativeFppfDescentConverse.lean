module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFinitePushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeOpenCoverLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowLemmaGeneral
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Fppf descent of relative `m`-pseudo-coherence (Stacks 0CSN)

Let `f : X ⟶ S` be locally of finite type, let `{g i : Y i ⟶ X}` be an fppf covering of schemes,
let `E ∈ D_QCoh(𝒪_X)` and let `m` be an integer. Stacks 0CSN says that `E` is
`m`-pseudo-coherent relative to `S` if and only if every `L(g i)^*E` is. The forward implication
is Stacks 0695 followed by Stacks 09US (it is also recorded, with Stacks 09US carried, in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/RelativeFppfDescent.lean`); this file proves the
converse, following the source, and registers the equivalence.

## Main results

* `AlgebraicGeometry.exists_linearMap_eq_one_of_faithfullyFlat`: a finite projective faithfully
  flat algebra `B` over `A` has an `A`-linear `r : B ⟶ A` with `r 1 = 1`.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_retract`: relative `m`-pseudo-coherence
  passes to retracts (a split monomorphism in a triangulated category is a biproduct inclusion,
  and Stacks 09UN takes the summand).
* `AlgebraicGeometry.retractDerivedPushforwardDerivedPullback`: for `π = Spec φ` with `φ` split by
  an `R`-linear retraction, `E` is a retract of `Rπ_*Lπ^*E` for `E ∈ D_QCoh`. This is the source's
  "locally on `X` the map `𝒪_X → π_*𝒪_Y` is the inclusion of a direct summand", combined with the
  identification `Rπ_*Lπ^*E = E ⊗^𝐋 π_*𝒪_Y` of Stacks 08EU and Stacks 08D7.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_openCover`: the Zariski case of the
  descent, gluing along an open cover by open immersions, read off the open-subscheme form
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_exists_opens`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isFinite_of_surjective`:
  descent along one finite flat surjective morphism of finite presentation (Stacks 09UK across
  `Rπ_*`, then the retract).
* `Scheme.Hom.isPseudoCoherentFrom_of_forall_derivedPullback_of_mem_fppfPrecoverage`: the converse
  of Stacks 0CSN, through the refinement of Stacks 05WN.
* `Scheme.Hom.isPseudoCoherentFrom_iff_forall_derivedPullback_of_mem_fppfPrecoverage`:
  **Stacks 0CSN.**

## Implementation notes

`D_QCoh(𝒪_X)` is spelled, as for Stacks 09UK, as quasi-coherence of every cohomology sheaf.
The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, made
a local instance at a high priority, as in the forward implication.

## References

* [The Stacks Project, Lemma 37.70.1 (0CSN)](https://stacks.math.columbia.edu/tag/0CSN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)
open Stacks.Cohomology.PseudoCoherence.FlatDescent
  (flat_of_mem_fppfPrecoverage locallyOfFinitePresentation_of_mem_fppfPrecoverage)

universe v u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- A finite projective faithfully flat algebra has an `A`-linear retraction of its unit. -/
public theorem exists_linearMap_eq_one_of_faithfullyFlat {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Module.Projective A B] [Module.FaithfullyFlat A B] :
    ∃ r : B →ₗ[A] A, r 1 = 1 := by
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  let c : Fin n → A := fun j ↦ i (1 : B) j
  have hc : Ideal.span (Set.range c) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hci : ∀ j, c j ∈ m := fun j ↦ hle (Ideal.subset_span ⟨j, rfl⟩)
    have hdecomp : i (1 : B) = ∑ j, c j • (Pi.single j (1 : A)) := by
      ext j
      simp [c, Finset.sum_apply, Pi.single_apply]
    have hone : (1 : B) ∈ m • (⊤ : Submodule A B) := by
      have hpi1 : p (i (1 : B)) = 1 := by
        simpa using congrArg (fun q : B →ₗ[A] B ↦ q 1) hpi
      rw [← hpi1, hdecomp, map_sum]
      exact Submodule.sum_mem _ fun j _ ↦ by
        rw [map_smul]; exact Submodule.smul_mem_smul (hci j) trivial
    apply Module.FaithfullyFlat.submodule_ne_top (M := B) hm
    rw [Ideal.smul_top_eq_map] at hone ⊢
    rw [eq_top_iff]
    intro x _
    simpa using (Ideal.map (algebraMap A B) m).mul_mem_left x hone
  have hmem : (1 : A) ∈ Ideal.span (Set.range c) := by rw [hc]; trivial
  obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun (v := c)).mp hmem
  refine ⟨∑ j, a j • (LinearMap.proj j).comp i, ?_⟩
  simpa [c, mul_comm] using ha


namespace Scheme.Hom

/-- A retract of an object which is `m`-pseudo-coherent relative to `S` is `m`-pseudo-coherent
relative to `S`. -/
public theorem IsPseudoCoherentFrom.of_retract {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {E F : DerivedCategory X.Modules} {m : ℤ} (r : Retract E F)
    (hF : IsPseudoCoherentFrom f F m) : IsPseudoCoherentFrom f E m := by
  obtain ⟨K, a, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle r.i
  have hm : Mono r.i := (show SplitMono r.i from ⟨r.r, r.retract⟩).mono
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang _ hT
    (Pretriangulated.Triangle.mor₃_eq_zero_of_mono₁ _ hT hm)
  exact IsPseudoCoherentFrom.of_biprod_left f E K m (hF.of_iso f e)

end Scheme.Hom

/-- For a ring map `φ : R ⟶ A` and an `R`-linear retraction `r` of it, `𝒪_{Spec R}` is a retract
of the pushforward of `𝒪_{Spec A}` along `Spec φ`. -/
public def unitRetractPushforwardUnit {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (r : letI := φ.hom.toAlgebra; A →ₗ[R] R) (hr : r 1 = 1) :
    Retract (SheafOfModules.unit (Spec R).ringCatSheaf)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (SheafOfModules.unit (Spec A).ringCatSheaf)) :=
  letI := φ.hom.toAlgebra
  let c : Retract (ModuleCat.of R R) ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A)) :=
    { i := ModuleCat.ofHom
        { toFun := fun a ↦ φ.hom a
          map_add' := map_add φ.hom
          map_smul' := fun a b ↦ by
            change φ.hom (a * b) = φ.hom a * φ.hom b
            exact map_mul φ.hom a b }
      r := ModuleCat.ofHom
        { toFun := r
          map_add' := r.map_add
          map_smul' := fun a b ↦ r.map_smul a b }
      retract := by
        ext : 1
        refine LinearMap.ext fun a ↦ ?_
        change r (φ.hom a) = a
        have : φ.hom a = a • (1 : A) := by rw [Algebra.smul_def, mul_one]; rfl
        rw [this, r.map_smul, hr, smul_eq_mul, mul_one] }
  ((Retract.ofIso tildeSelf.symm).trans (c.map (tilde.functor R))).trans
    (Retract.ofIso (Scheme.Modules.pushforwardUnitTildeIso φ).symm)


/-- **The affine core of the converse of Stacks 0CSN.** Let `φ : R ⟶ A` be a ring map admitting
an `R`-linear retraction `r` with `r 1 = 1`, write `π = Spec φ`, and let `E` be an object of
`D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves. Then `E` is a retract of `Rπ_*Lπ^*E`.

The projection formula of Stacks 08EU identifies `Rπ_*Lπ^*E` with `Rπ_*𝒪_{Spec A} ⊗^𝐋 E`; the
direct image `Rπ_*𝒪_{Spec A}` is `π_*𝒪_{Spec A}` in degree zero because `π` is affine
(`AlgebraicGeometry.derivedPushforwardSingleIsoOfIsAffineHom`); and
`𝒪_{Spec R}` is a retract of `π_*𝒪_{Spec A}` through the sheaf associated with `r`. -/
public def retractDerivedPushforwardDerivedPullback {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (r : letI := φ.hom.toAlgebra; A →ₗ[R] R) (hr : r 1 = 1) (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent) :
    Retract E ((derivedPushforward (Spec.map φ).toLRSHom.toShHom).obj
      ((derivedPullback (Spec.map φ).toLRSHom.toShHom).obj E)) :=
  let π := Spec.map φ
  let OA := SheafOfModules.unit (Spec A).ringCatSheaf
  let R2 : Retract ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf))
      ((derivedPushforward π.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj OA)) :=
    ((unitRetractPushforwardUnit φ r hr).map
      (DerivedCategory.singleFunctor (Spec R).Modules 0)).trans
      (Retract.ofIso (derivedPushforwardSingleIsoOfIsAffineHom π OA).symm)
  let T := (canonicalDerivedTensorProduct (Spec R).sheaf).tensor.flip.obj E
  have hpf :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      π inferInstance inferInstance
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj OA) E
      (Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj (Spec A) OA inferInstance) hE
  let e2 := @asIso _ _ _ _ _ hpf
  (Retract.ofIso (Scheme.Modules.derivedTensorUnitLeftIso (Spec R) E).symm).trans
    ((R2.map T).trans (Retract.ofIso (e2 ≪≫ (derivedPushforward π.toLRSHom.toShHom).mapIso
      (Scheme.Modules.derivedTensorUnitLeftIso (Spec A) _))))


/-- `Lπ^*` keeps `D_QCoh`, read in the spelling of the category of modules of a scheme. -/
public theorem isQuasicoherent_homology_derivedPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory Y.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback g.toLRSHom.toShHom).obj E)).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g E hE i

/-- **The converse of Stacks 0CSN for the spectrum of a finite faithfully flat ring map of finite
presentation.** -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_specMap {R A : CommRingCat.{u}}
    (φ : R ⟶ A) [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [Surjective (Spec.map φ)]
    [LocallyOfFinitePresentation (Spec.map φ)] {S : Scheme.{u}} (f : Spec R ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent)
    (m : ℤ)
    (h : (Spec.map φ ≫ f).IsPseudoCoherentFrom
      ((derivedPullback (Spec.map φ).toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  let := φ.hom.toAlgebra
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).mp ⟨‹_›, ‹_›⟩
  have : Module.FaithfullyFlat R A := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have : Module.Finite R A := (IsFinite.SpecMap_iff φ).mp inferInstance
  have : Algebra.FinitePresentation R A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp inferInstance
  have : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  have : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  obtain ⟨r, hr⟩ := exists_linearMap_eq_one_of_faithfullyFlat (A := R) (B := A)
  have hpush := (Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward (Spec.map φ)
    (Spec.map φ ≫ f) f rfl _ (isQuasicoherent_homology_derivedPullback _ E hE) m).1 h
  exact Scheme.Hom.IsPseudoCoherentFrom.of_retract f
    (retractDerivedPushforwardDerivedPullback φ r hr E hE) hpush


/-- `Lp^* Lg^* ≅ L(p ≫ g)^*` for composable morphisms of schemes: Stacks 0D5S at the underlying
morphisms of ringed spaces. -/
public def derivedPullbackCompIsoOfSchemes {T Y X : Scheme.{u}} (p : T ⟶ Y) (g : Y ⟶ X)
    (E : DerivedCategory X.Modules) :
    (derivedPullback p.toLRSHom.toShHom).obj ((derivedPullback g.toLRSHom.toShHom).obj E) ≅
      (derivedPullback (p ≫ g).toLRSHom.toShHom).obj E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      p.toLRSHom.toShHom g.toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun k : T.toRingedSpace ⟶ X.toRingedSpace => (derivedPullback k).obj E)
      (by simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]))

/-- **Moving relative pseudo-coherence along a pseudo-coherent morphism, with the derived pullbacks
composed.** If `L(g)^*E` is `m`-pseudo-coherent relative to `S` along `g ≫ f` and `p` is a
pseudo-coherent morphism, then `L(p ≫ g)^*E` is `m`-pseudo-coherent relative to `S` along
`p ≫ g ≫ f`. This is Stacks 09US followed by Stacks 0D5S. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_derivedPullback_comp {T Y X S : Scheme.{u}}
    (p : T ⟶ Y) (g : Y ⟶ X) (f : X ⟶ S) [PseudoCoherent p] [LocallyOfFiniteType (g ≫ f)]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : (g ≫ f).IsPseudoCoherentFrom ((derivedPullback g.toLRSHom.toShHom).obj E) m) :
    (p ≫ g ≫ f).IsPseudoCoherentFrom ((derivedPullback (p ≫ g).toLRSHom.toShHom).obj E) m :=
  (Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback p (g ≫ f) _ m h).of_iso _
    (derivedPullbackCompIsoOfSchemes p g E)

/-- `isPseudoCoherentFrom_derivedPullback_comp`, restated for a morphism `q` equal to `p ≫ g`. -/
private theorem isPseudoCoherentFrom_derivedPullback_of_comp_eq {T Y X S : Scheme.{u}}
    (p : T ⟶ Y) (g : Y ⟶ X) (f : X ⟶ S) (q : T ⟶ X) (hq : p ≫ g = q) [PseudoCoherent p]
    [LocallyOfFiniteType (g ≫ f)] [LocallyOfFiniteType (q ≫ f)] (E : DerivedCategory X.Modules)
    (m : ℤ) (h : (g ≫ f).IsPseudoCoherentFrom ((derivedPullback g.toLRSHom.toShHom).obj E) m) :
    (q ≫ f).IsPseudoCoherentFrom ((derivedPullback q.toLRSHom.toShHom).obj E) m := by
  subst hq
  exact (Scheme.Hom.isPseudoCoherentFrom_congr_hom (Category.assoc p g f).symm _ m).1
    (Scheme.Hom.isPseudoCoherentFrom_derivedPullback_comp p g f E m h)

/-- **Relative `m`-pseudo-coherence glues along an open cover.** Let `f : X ⟶ S` be locally of
finite type and let `𝒰` be an open cover of `X`. If `L(𝒰.f j)^*E` is `m`-pseudo-coherent relative
to `S` for every member `𝒰.f j` of the cover, then so is `E`.

This is `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_exists_opens`, the form for
open subschemes, at the images `U` of the members: the isomorphism of a member onto its image is
pseudo-coherent, so Stacks 09US moves the hypothesis to `U`, where derived pullback along the
inclusion is restriction. -/
@[sga "6 III 1.1"]
public theorem Scheme.Hom.isPseudoCoherentFrom_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (m : ℤ) (𝒰 : X.OpenCover.{v})
    (h : ∀ j, (𝒰.f j ≫ f).IsPseudoCoherentFrom
      ((derivedPullback (𝒰.f j).toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  refine Scheme.Hom.isPseudoCoherentFrom_of_forall_exists_opens f E m fun x => ?_
  let j := 𝒰.idx x
  refine ⟨(𝒰.f j).opensRange, 𝒰.covers x, ?_⟩
  have hinv : (𝒰.f j).isoOpensRange.inv ≫ 𝒰.f j = (𝒰.f j).opensRange.ι :=
    (𝒰.f j).isoOpensRange_inv_comp
  exact (isPseudoCoherentFrom_derivedPullback_of_comp_eq _ (𝒰.f j) f _ hinv E m (h j)).of_iso _
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback (𝒰.f j).opensRange.ι).app E).symm

/-- The converse of Stacks 0CSN over an affine target, for a finite flat surjective morphism of
finite presentation out of an affine scheme. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isAffine {Y : Scheme.{u}}
    [IsAffine Y] {R : CommRingCat.{u}} (π : Y ⟶ Spec R) [IsFinite π] [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] {S : Scheme.{u}} (f : Spec R ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent)
    (m : ℤ) (h : (π ≫ f).IsPseudoCoherentFrom ((derivedPullback π.toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Y.isoSpec.inv ≫ π := ⟨_, Spec.map_preimage _⟩
  have : IsFinite (Spec.map φ) := hφ ▸ inferInstance
  have : Flat (Spec.map φ) := hφ ▸ inferInstance
  have : Surjective (Spec.map φ) := hφ ▸ inferInstance
  have : LocallyOfFinitePresentation (Spec.map φ) := hφ ▸ inferInstance
  refine Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_specMap φ f E hE m ?_
  exact isPseudoCoherentFrom_derivedPullback_of_comp_eq Y.isoSpec.inv π f _ hφ.symm E m h

/-- **The converse of Stacks 0CSN along one finite flat surjective morphism of finite
presentation.** Let `π : Y ⟶ X` be finite, flat, surjective and locally of finite presentation,
let `f : X ⟶ S` be locally of finite type and let `E` have quasi-coherent cohomology sheaves. If
`Lπ^*E` is `m`-pseudo-coherent relative to `S`, then so is `E`.

The question is local on `X` by
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_openCover`, so `X` may be taken to be the
spectrum of a ring; then `Y` is affine, and the affine case is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isAffine`. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isFinite_of_surjective
    {Y X S : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) (h : (π ≫ f).IsPseudoCoherentFrom ((derivedPullback π.toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  suffices key : ∀ {R : CommRingCat.{u}} (g : Spec R ⟶ X) [IsOpenImmersion g],
      (g ≫ f).IsPseudoCoherentFrom ((derivedPullback g.toLRSHom.toShHom).obj E) m from
    Scheme.Hom.isPseudoCoherentFrom_of_openCover f E m X.affineOpenCover.openCover
      fun j => @key _ _ (X.affineOpenCover.openCover.map_prop j)
  intro R g _
  have : IsOpenImmersion (pullback.fst π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback π g).flip ‹_›
  have : IsFinite (pullback.snd π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback π g) ‹_›
  have : Flat (pullback.snd π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback π g) ‹_›
  have : Surjective (pullback.snd π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback π g) ‹_›
  have : LocallyOfFinitePresentation (pullback.snd π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
      (IsPullback.of_hasPullback π g) ‹_›
  have : IsAffine (pullback π g) := isAffine_of_isAffineHom (pullback.snd π g)
  refine Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isAffine (pullback.snd π g) (g ≫ f) _
    (isQuasicoherent_homology_derivedPullback g E hE) m ?_
  exact ((Scheme.Hom.isPseudoCoherentFrom_congr_hom (Category.assoc _ _ _) _ m).1
    (isPseudoCoherentFrom_derivedPullback_of_comp_eq (pullback.fst π g) π f _ pullback.condition
      E m h)).of_iso _ (derivedPullbackCompIsoOfSchemes (pullback.snd π g) g E).symm


/-- `Lp^* Lq^* Lr^* ≅ L(p ≫ q ≫ r)^*`, two applications of Stacks 0D5S. -/
public def derivedPullbackComp₃IsoOfSchemes {T Y Z X : Scheme.{u}} (p : T ⟶ Y) (q : Y ⟶ Z)
    (r : Z ⟶ X) (E : DerivedCategory X.Modules) :
    (derivedPullback p.toLRSHom.toShHom).obj ((derivedPullback q.toLRSHom.toShHom).obj
        ((derivedPullback r.toLRSHom.toShHom).obj E)) ≅
      (derivedPullback (p ≫ q ≫ r).toLRSHom.toShHom).obj E :=
  (derivedPullback p.toLRSHom.toShHom).mapIso (derivedPullbackCompIsoOfSchemes q r E) ≪≫
    derivedPullbackCompIsoOfSchemes p (q ≫ r) E

/-- **The converse of Stacks 0CSN.** Let `f : X ⟶ S` be locally of finite type, let
`{g i : Y i ⟶ X}` be an fppf covering of schemes, let `E` be an object of `D(𝒪_X)` with
quasi-coherent cohomology sheaves and let `m` be an integer. If every `L(g i)^*E` is
`m`-pseudo-coherent relative to `S`, then so is `E`.

This is the source's argument. Stacks 05WN refines the covering by a Zariski covering
`X = ⋃ U_j`, surjective finite locally free `W_j ⟶ U_j`, Zariski coverings `W_j = ⋃ W_{j,k}` and
surjective finite locally free `T_{j,k} ⟶ W_{j,k}`, each composite `T_{j,k} ⟶ X` factoring
through some `g i` by a morphism `l`. The composite is flat and locally of finite presentation,
hence pseudo-coherent by Stacks 0695, so `l` is pseudo-coherent by Stacks 0683 and Stacks 09US
moves the hypothesis to `T_{j,k}`. It is then descended through the four stages:
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_openCover` for the two Zariski coverings
and `Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isFinite_of_surjective` for the two
surjective finite locally free stages, the quasi-coherence of the cohomology sheaves being carried
along by Stacks 08DW. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_forall_derivedPullback_of_mem_fppfPrecoverage
    {X S : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage X)
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ)
    (h : ∀ i, letI : LocallyOfFinitePresentation (g i) :=
        locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
      (g i ≫ f).IsPseudoCoherentFrom ((derivedPullback (g i).toLRSHom.toShHom).obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  classical
  let 𝒮 : X.Cover.{v} Scheme.fppfPrecoverage := ⟨PreZeroHypercover.mk ι Y g, by simpa using hg⟩
  obtain ⟨𝒰, W, a, 𝒲, T, b, ha, hb, hcover, hfactor⟩ :=
    Stacks.Topologies.Fppf.exists_openCover_finiteLocallyFree_refinement X 𝒮
  have hq := fun j k => ((Scheme.ofArrows_mem_precoverage_iff
    (P := (@Flat ⊓ @LocallyOfFinitePresentation))).mp hcover).2 ⟨j, k⟩
  have hfinal : ∀ j k,
      let : LocallyOfFinitePresentation (b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j) := (hq j k).2
      ((b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j) ≫ f).IsPseudoCoherentFrom
        ((derivedPullback (b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j).toLRSHom.toShHom).obj E) m := by
    intro j k
    obtain ⟨i, l, hl⟩ := hfactor j k
    change l ≫ g i = _ at hl
    have : Flat (b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j) := (hq j k).1
    have : LocallyOfFinitePresentation (b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j) := (hq j k).2
    let : LocallyOfFinitePresentation (g i) :=
      locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
    have : Flat (g i) := flat_of_mem_fppfPrecoverage Y g hg i
    have : PseudoCoherent (l ≫ g i) := by rw [hl]; infer_instance
    have : PseudoCoherent l := pseudoCoherent_of_comp l (g i)
    exact isPseudoCoherentFrom_derivedPullback_of_comp_eq l (g i) f _ hl E m (h i)
  refine Scheme.Hom.isPseudoCoherentFrom_of_openCover f E m 𝒰 fun j => ?_
  obtain ⟨hafin, haflat, hafp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (a j)).mp (ha j).2
  have := (ha j).1
  have hE₁ := isQuasicoherent_homology_derivedPullback (𝒰.f j) E hE
  refine Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isFinite_of_surjective (a j)
    (𝒰.f j ≫ f) _ hE₁ m ?_
  refine Scheme.Hom.IsPseudoCoherentFrom.of_iso _ ?_ (derivedPullbackCompIsoOfSchemes _ _ E).symm
  refine Scheme.Hom.isPseudoCoherentFrom_of_openCover (a j ≫ 𝒰.f j ≫ f) _ m (𝒲 j) fun k => ?_
  obtain ⟨hbfin, hbflat, hbfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (b j k)).mp (hb j k).2
  have := (hb j k).1
  have hE₃ := isQuasicoherent_homology_derivedPullback ((𝒲 j).f k) _
    (isQuasicoherent_homology_derivedPullback (a j ≫ 𝒰.f j) E hE)
  refine Scheme.Hom.isPseudoCoherentFrom_of_derivedPullback_of_isFinite_of_surjective (b j k)
    ((𝒲 j).f k ≫ a j ≫ 𝒰.f j ≫ f) _ hE₃ m ?_
  have h' := (Scheme.Hom.isPseudoCoherentFrom_congr_hom
    (show (b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j) ≫ f = b j k ≫ (𝒲 j).f k ≫ a j ≫ 𝒰.f j ≫ f by
      simp only [Category.assoc]) _ m).1 (hfinal j k)
  exact h'.of_iso _ (derivedPullbackComp₃IsoOfSchemes _ _ _ E).symm


/-- **Stacks 0CSN.** Let `f : X ⟶ S` be locally of finite type, let `{g i : Y i ⟶ X}` be an fppf
covering of schemes, let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves and
let `m` be an integer. Then `E` is `m`-pseudo-coherent relative to `S` if and only if every
`L(g i)^*E` is `m`-pseudo-coherent relative to `S`.

The forward implication is Stacks 0695 (a member of an fppf covering is flat and locally of
finite presentation, hence pseudo-coherent) followed by Stacks 09US,
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`; it needs neither joint
surjectivity nor the quasi-coherence of `E`. The converse is
`Scheme.Hom.isPseudoCoherentFrom_of_forall_derivedPullback_of_mem_fppfPrecoverage` (Stacks 05WN,
0683, 09US, 09UK, 08EU, 09UN and Zariski gluing). The membership of `g i ≫ f` in the class of
morphisms locally of finite type, which the predicate takes as an instance argument, comes from the
covering. -/
@[stacks 0CSN "both implications, at the source's hypotheses: f locally of finite type, an \
arbitrary fppf covering of X (Presieve.ofArrows in Scheme.fppfPrecoverage, any index universe), \
E with quasi-coherent cohomology sheaves, any m"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_forall_derivedPullback_of_mem_fppfPrecoverage
    {X S : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage X)
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) :
    f.IsPseudoCoherentFrom E m ↔
      ∀ i, letI : LocallyOfFinitePresentation (g i) :=
          locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
        (g i ≫ f).IsPseudoCoherentFrom ((derivedPullback (g i).toLRSHom.toShHom).obj E) m :=
  ⟨fun hf i =>
      let : LocallyOfFinitePresentation (g i) :=
        locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
      have : Flat (g i) := flat_of_mem_fppfPrecoverage Y g hg i
      isPseudoCoherentFrom_comp_derivedPullback (g i) f E m hf,
    isPseudoCoherentFrom_of_forall_derivedPullback_of_mem_fppfPrecoverage Y g f hg E hE m⟩

end AlgebraicGeometry
