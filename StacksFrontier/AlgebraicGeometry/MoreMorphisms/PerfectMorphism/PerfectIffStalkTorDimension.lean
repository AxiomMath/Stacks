module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.StalkTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.RingTheory.PseudoCoherentMap.FiniteTorDimensionAtPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness and finite Tor dimension at the stalks

Let `f : X ⟶ S` be a morphism of schemes. This file proves, for a pseudo-coherent `f`, the
equivalence between perfectness of `f` and finiteness of the Tor dimension of `𝒪_{X, x}` as an
`𝒪_{S, f x}`-module at every point `x` of `X`.

## Main results

* `AlgebraicGeometry.Perfect.exists_hasTorAmplitudeCanonical_stalk_of_affineOpen`: a perfect
  morphism bounds the Tor amplitude of the stalks by *one* interval on each affine chart. This is
  the form in which condition (2) of Stacks 069C consumes perfectness.
* `AlgebraicGeometry.Perfect.hasFiniteTorDimensionCanonical_stalk`: a perfect morphism has finite
  Tor dimension at every stalk. No pseudo-coherence hypothesis is needed for this implication.
* `AlgebraicGeometry.perfect_of_forall_hasFiniteTorDimensionCanonical_stalk`: the converse, from
  the ring-theoretic criterion described below.  It is unconditional.
* `AlgebraicGeometry.perfect_iff_forall_hasFiniteTorDimensionCanonical_stalk`: the equivalence
  itself.
* `AlgebraicGeometry.hasTorAmplitudeCanonical_atPrime_of_hasTorAmplitudeAt` and
  `AlgebraicGeometry.hasTorAmplitudeCanonical_models_iff`: the two steps of the passage from a
  chart to the stalks, each stated at a fixed interval `[a, b]`.

## Implementation notes

Finite Tor dimension of a module over a commutative ring is read at the canonical derived tensor
product of Stacks 0BYI. The spelling used is
`StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical` — Stacks 0652 (2) at that tensor
product — applied to the module placed in degree zero, which is by definition
`StacksDraft.TorAmplitude.ModuleHasFiniteTorDimensionCanonical` of the module, Stacks 0652 (4).
The module-level wrapper is spelled out this way because it is the finite-Tor-dimension predicate
that carries a public characterisation, namely
`StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical`
together with `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative`, and
the bodies of the canonical predicates are not exposed, so nothing can be proved about the folded
module-level form. Both are the canonical notion: they hypothesise no tensor product, and
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff` identifies the amplitude they
read with the amplitude read off any certified derived tensoring, which is what
`AlgebraicGeometry.Perfect` quantifies over.

Every step of the argument below is therefore carried out on the flat representatives of
Stacks 0654, and converted into the canonical predicates only at the two ends.

**The two local rings are not the canonical localisations.** The chart-level input
`AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect` is stated at `Localization.AtPrime`,
whereas the stalk of a scheme is only *a* localisation. The passage between the two is
`hasTorAmplitudeCanonical_models_iff` below: both models are identified with the canonical
ones by `IsLocalization.algEquiv`, the square relating the two identifications to the two
structure maps is forced by the universal property of the localisation of the base ring, and
Tor amplitude is then moved across the resulting ring isomorphism by
`hasTorAmplitudeCanonical_of_ringEquiv`. Restriction of scalars along a ring isomorphism
carries a complex of flat modules to a complex of flat modules, because the isomorphism makes the
target ring flat over the source ring, so `Module.Flat.trans` applies.

**Why the passage is stated at a fixed interval.** Both steps of it —
`hasTorAmplitudeCanonical_atPrime_of_hasTorAmplitudeAt` and
`hasTorAmplitudeCanonical_models_iff` — only move flat representatives of Stacks 0654 across ring
isomorphisms, and that never changes the window, so each can be, and is, stated with `[a, b]`
fixed rather than existentially quantified. Only the wrappers
`Perfect.hasFiniteTorDimensionCanonical_stalk` and
`perfect_iff_forall_hasFiniteTorDimensionCanonical_stalk` drop the interval, because condition (3)
of Stacks 069C is pointwise. Condition (2) is not: it needs the interval uniform on each member of
a covering, which is what `Perfect.exists_hasTorAmplitudeCanonical_stalk_of_affineOpen` supplies.

**The converse direction does not go through Stacks 0B67.** The Tor dimension of `𝒪_{X, x}` over
`𝒪_{S, f x}` is not bounded uniformly in `x`, so the source's argument for (3) ⟹ (1) runs instead
through a finite polynomial presentation, the fibrewise criterion of Stacks 068X and the stalkwise
criterion for perfectness of Stacks 068W. That ring-theoretic implication is
`RingHom.hasFiniteTorDimensionRingHom_of_forall_localizationAtPrime` of
`StacksFrontier.RingTheory.PseudoCoherentMap.FiniteTorDimensionAtPrimes`: a pseudo-coherent ring map
whose localisations at every prime of the target have finite Tor dimension over the corresponding
localisation of the source has finite Tor dimension. What is proved here is the geometric half —
the reduction of perfectness to the affine charts and the passage between the stalks and the
canonical localisations.

## References

* [The Stacks Project, Lemma 37.61.11 (069C)](https://stacks.math.columbia.edu/tag/069C)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Definition 37.61.2 (0687)](https://stacks.math.columbia.edu/tag/0687)
* [The Stacks Project, Lemma 15.68.19 (0B67)](https://stacks.math.columbia.edu/tag/0B67)
* [The Stacks Project, Lemma 15.66.6 (0654)](https://stacks.math.columbia.edu/tag/0654)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-! ### Tor amplitude of a module through its projective resolution

The lemmas of this section restate, for use below, the comparison between Tor amplitude at the
canonical derived tensor product of Stacks 0BYI and the projective-resolution rendering of
Stacks 0DJF for a module placed in degree zero. Both renderings are needed: the chart-level input
is stated in the second and the conclusion in the first. -/

/-- For a module placed in degree zero, the projective-resolution Tor amplitude of Stacks 0DJF
gives a flat representative in the same window.

The projective resolution of the module is a K-flat, bounded-above, termwise flat model of it, so
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF` applies to that model, and the
resolution map is a quasi-isomorphism, which transports the hypothesis to the model. Stacks 0654
then produces the flat representative. -/
@[sga "4 XVII 4.1.9" "special case"]
private theorem hasFlatRepresentative_single_of_0DJF
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (a b : ℤ)
    (h : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b) :
    HasFlatRepresentative.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) a b := by
  let P := FaithfullyFlat.projResComplex M
  have hPle : P.IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE
      ((CategoryTheory.ProjectiveResolution.of M).complex.extend
        ComplexShape.embeddingDownNat) 0
    infer_instance
  have hPbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, by rwa [CochainComplex.isStrictlyLE_iff] at hPle⟩
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    (CategoryTheory.ProjectiveResolution.of M).π'
  have hq : QuasiIso q := by
    dsimp [q]
    change QuasiIso
      (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of M).π
        ComplexShape.embeddingDownNat ≫ _)
    have hπ' : QuasiIso (HomologicalComplex.extendMap
        (CategoryTheory.ProjectiveResolution.of M).π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2
        (CategoryTheory.ProjectiveResolution.quasiIso _)
    infer_instance
  have hPtor : FaithfullyFlat.HasTorAmplitude P a b := by
    intro N i hi
    have := quasiIso_tensorRight_map (projResComplex_kFlat R N).1 q
    exact (homologyIsoOfQuasiIso
      ((tensorRight (FaithfullyFlat.projResComplex N)).map q) i).isZero_iff.mpr (h N i hi)
  have hcan := (hasTorAmplitude_of_iso (comparison := canonicalTensorComparison R)
      (isLeftDerived := canonicalTensorIsLeftDerived R) (asIso (DerivedCategory.Q.map q)) a b).mp
    ((hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) P (projResComplex_kFlat R M).1 hPbound
      (projResComplex_kFlat R M).2 a b).mpr hPtor)
  exact hasFlatRepresentative_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M).symm
    ((hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) _ a b).mp hcan)

/-! ### Finite Tor dimension across a ring isomorphism -/

/-- A ring isomorphism makes the target a free module of rank one over the source, hence flat. -/
private theorem flat_of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (e : R ≃+* R') (he : algebraMap R R' = (e : R →+* R')) : Module.Flat R R' :=
  Module.Flat.of_linearEquiv (R := R) (M := R) (N := R')
    { toFun := e.symm
      map_add' := map_add e.symm
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, he, RingHom.coe_coe, map_mul, RingEquiv.symm_apply_apply,
          RingHom.id_apply, Algebra.algebraMap_self_apply]
      invFun := e
      left_inv := e.apply_symm_apply
      right_inv := e.symm_apply_apply }

/-- Having a flat representative in `[a, b]` is carried along restriction of scalars by a ring
isomorphism: the isomorphism makes the target ring flat over the source ring, so
`Module.Flat.trans` turns each flat term into a flat term. -/
private theorem hasFlatRepresentative_restrictScalars_ringEquiv {R R' : Type u} [CommRing R]
    [CommRing R'] (e : R ≃+* R') (K : DerivedCategory (ModuleCat.{u} R')) (a b : ℤ)
    (h : HasFlatRepresentative.{u, u} K a b) :
    HasFlatRepresentative.{u, u}
      ((ModuleCat.restrictScalars.{u} (e : R →+* R')).mapDerivedCategory.obj K) a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨eE⟩⟩ := h
  let G := ModuleCat.restrictScalars.{u} (e : R →+* R')
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, fun i => ?_,
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := E) G a).2 hGE,
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := E) G b).2 hLE,
    ⟨G.mapDerivedCategory.mapIso eE ≪≫ G.mapDerivedCategoryFactors.app E⟩⟩
  let _ : Algebra R R' := (e : R →+* R').toAlgebra
  have halg : algebraMap R R' = (e : R →+* R') := RingHom.algebraMap_toAlgebra _
  have hflatR' : Module.Flat R R' := flat_of_ringEquiv e halg
  have hEi := hflat i
  let _ : Module R (E.X i) := Module.compHom (E.X i) (e : R →+* R')
  have htower : IsScalarTower R R' (E.X i) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [halg]
      rfl
  exact Module.Flat.trans R R' (E.X i)

/-- **Tor amplitude moves across a ring isomorphism, with the interval kept.** If `e : R ≃+* R'`
and the `R`-module `N` is the restriction of scalars of the `R'`-module `M` along `e`, then Tor
amplitude of `M` over `R'` in `[a, b]` gives Tor amplitude of `N` over `R` in the *same* interval
`[a, b]`.

Tor amplitude is read through the flat representatives of Stacks 0654, which restriction of
scalars along a ring isomorphism carries to flat representatives in the same window: no step
moves the interval. -/
theorem hasTorAmplitudeCanonical_of_ringEquiv {R R' : Type u} [CommRing R]
    [CommRing R'] (e : R ≃+* R') (M : ModuleCat.{u} R') (N : ModuleCat.{u} R)
    (lin : N ≅ (ModuleCat.restrictScalars.{u} (e : R →+* R')).obj M) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R'
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj M) a b) :
    HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) a b := by
  have hrep := (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R'
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj M) a b).mp h
  let G := ModuleCat.restrictScalars.{u} (e : R →+* R')
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) a b).mpr
    (hasFlatRepresentative_of_iso
      (((G.mapDerivedCategorySingleFunctor 0).app M).trans
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso lin).symm)
      (hasFlatRepresentative_restrictScalars_ringEquiv e
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj M) a b hrep))

/-! ### The two local rings, read on arbitrary models -/

/-- One direction of `hasTorAmplitudeCanonical_iff_of_ringEquiv_square`. -/
private theorem hasTorAmplitudeCanonical_of_ringEquiv_square {R P Q T : Type u} [CommRing R]
    [CommRing P] [CommRing Q] [CommRing T] [Algebra P Q] [Algebra R T]
    (eR : R ≃+* P) (φ : Q ≃+* T) (hkey : ∀ r : R, φ (algebraMap P Q (eR r)) = algebraMap R T r)
    (a b : ℤ)
    (h : HasTorAmplitudeCanonical P
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P Q)) a b) :
    HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R T)) a b := by
  let _ : Module R Q :=
    ((ModuleCat.restrictScalars.{u} (eR : R →+* P)).obj (ModuleCat.of P Q)).isModule
  have hsmR : ∀ (r : R) (y : Q), (r • y : Q) = algebraMap P Q (eR r) * y :=
    fun r y => Algebra.smul_def (eR r) y
  let lin : Q ≃ₗ[R] T :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r y => by
        rw [hsmR r y, map_mul, hkey r, RingHom.id_apply, Algebra.smul_def]
      invFun := φ.symm
      left_inv := φ.symm_apply_apply
      right_inv := φ.apply_symm_apply }
  exact hasTorAmplitudeCanonical_of_ringEquiv eR (ModuleCat.of P Q) (ModuleCat.of R T)
    (lin.symm.toModuleIso (X₁ := ModuleCat.of R T)
      (X₂ := (ModuleCat.restrictScalars.{u} (eR : R →+* P)).obj (ModuleCat.of P Q))) a b h

/-- Tor amplitude is carried across a commuting square of ring isomorphisms `R ≃ P` and
`Q ≃ T`, with the interval kept. -/
theorem hasTorAmplitudeCanonical_iff_of_ringEquiv_square {R P Q T : Type u} [CommRing R]
    [CommRing P] [CommRing Q] [CommRing T] [Algebra P Q] [Algebra R T]
    (eR : R ≃+* P) (φ : Q ≃+* T) (hkey : ∀ r : R, φ (algebraMap P Q (eR r)) = algebraMap R T r)
    (a b : ℤ) :
    HasTorAmplitudeCanonical P
        ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P Q)) a b ↔
      HasTorAmplitudeCanonical R
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R T)) a b :=
  ⟨hasTorAmplitudeCanonical_of_ringEquiv_square eR φ hkey a b,
    hasTorAmplitudeCanonical_of_ringEquiv_square eR.symm φ.symm
      (fun s => φ.symm_apply_eq.2 (by simpa using (hkey (eR.symm s)).symm)) a b⟩

/-- **Tor amplitude of the local rings does not depend on the models, and the interval is the
same.** Let `A → B` be a ring map, `q` a prime of `B` lying over the prime `p` of `A`, and let `R`
and `T` be arbitrary models of `A_p` and `B_q` fitting into a commuting square with `A → B`. Then
`T` has Tor amplitude in `[a, b]` over `R` if and only if `B_q` has Tor amplitude in the *same*
interval `[a, b]` over `A_p` at the canonical localisations.

Both models are compared with the canonical localisations by `IsLocalization.algEquiv`, and the
comparison squares with the two structure maps are forced by the universal property of the
localisation of `A` at `p`, which is where `htower` is used. The passage itself is
`hasTorAmplitudeCanonical_of_ringEquiv` in each direction, which keeps the interval. -/
theorem hasTorAmplitudeCanonical_models_iff
    {A B R T : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing T]
    [Algebra A B] [Algebra A R] [Algebra B T] [Algebra R T]
    (q : Ideal B) [q.IsPrime] (p : Ideal A) [p.IsPrime] (hp : Ideal.under A q = p)
    [IsLocalization.AtPrime R p] [IsLocalization.AtPrime T q]
    (htower : (algebraMap R T).comp (algebraMap A R) = (algebraMap B T).comp (algebraMap A B))
    (a b : ℤ) :
    (let _ : Algebra (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q) :=
       Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
     HasTorAmplitudeCanonical (Localization.AtPrime (Ideal.under A q))
       ((DerivedCategory.singleFunctor
           (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q))) 0).obj
         (ModuleCat.of (Localization.AtPrime (Ideal.under A q))
           (Localization.AtPrime q))) a b) ↔
      HasTorAmplitudeCanonical R
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R T)) a b := by
  subst hp
  set p := Ideal.under A q
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let e : Localization.AtPrime p ≃ₐ[A] R := IsLocalization.algEquiv p.primeCompl _ _
  let φ : Localization.AtPrime q ≃ₐ[B] T := IsLocalization.algEquiv q.primeCompl _ _
  let lrh : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over
  have hsq : (φ : Localization.AtPrime q →+* T).comp lrh =
      (algebraMap R T).comp (e : Localization.AtPrime p →+* R) := by
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    ext y
    have hl : lrh (algebraMap A (Localization.AtPrime p) y) =
        algebraMap B (Localization.AtPrime q) (algebraMap A B y) :=
      Localization.localRingHom_to_map p q (algebraMap A B) Ideal.LiesOver.over y
    have hr : (e : Localization.AtPrime p →+* R) (algebraMap A (Localization.AtPrime p) y) =
        algebraMap A R y := e.commutes y
    have h2 := RingHom.congr_fun htower y
    simp only [RingHom.coe_comp, Function.comp_apply] at h2 ⊢
    rw [hl, hr]
    exact (φ.commutes _).trans h2.symm
  let eR : R ≃+* Localization.AtPrime p := e.toRingEquiv.symm
  have hkey : ∀ r : R, φ (lrh (eR r)) = algebraMap R T r := fun r => by
    simpa [eR] using RingHom.congr_fun hsq (eR r)
  exact hasTorAmplitudeCanonical_iff_of_ringEquiv_square eR φ.toRingEquiv hkey a b

/-- **Finite Tor dimension of the local rings does not depend on the models.** The existential
form of `hasTorAmplitudeCanonical_models_iff`: finite Tor dimension at the canonical derived
tensor product is Tor amplitude in some interval, and that iff holds interval by interval. -/
private theorem hasFiniteTorDimensionCanonical_models_iff
    {A B R T : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing T]
    [Algebra A B] [Algebra A R] [Algebra B T] [Algebra R T]
    (q : Ideal B) [q.IsPrime] (p : Ideal A) [p.IsPrime] (hp : Ideal.under A q = p)
    [IsLocalization.AtPrime R p] [IsLocalization.AtPrime T q]
    (htower : (algebraMap R T).comp (algebraMap A R) = (algebraMap B T).comp (algebraMap A B)) :
    (let _ : Algebra (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q) :=
       Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
     HasFiniteTorDimensionCanonical (Localization.AtPrime (Ideal.under A q))
       ((DerivedCategory.singleFunctor
           (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q))) 0).obj
         (ModuleCat.of (Localization.AtPrime (Ideal.under A q))
           (Localization.AtPrime q)))) ↔
      HasFiniteTorDimensionCanonical R
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R T)) := by
  let _ : Algebra (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
  simp only [hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical]
  exact exists_congr fun a => exists_congr fun b =>
    hasTorAmplitudeCanonical_models_iff q p hp htower a b

/-! ### From a Tor-amplitude bound at a prime to Tor amplitude of the localisations -/

/-- **A Tor-amplitude bound at a prime, read at the canonical localisations, with the interval
kept.** The localised single complex of `B` over `A` is the single complex of `B_q` read over
`A_p`, so a Tor-amplitude bound in `[a, b]` at the prime `q` is Tor amplitude of `B_q` over `A_p`
in the *same* interval `[a, b]`.

Only the projective-resolution rendering of Stacks 0DJF is transported, by
`hasTorAmplitude0DJF_of_isoComplex` across two isomorphisms of complexes, and Stacks 0654 is
applied in the window `[a, b]` at the end; nothing here enlarges the interval. -/
theorem hasTorAmplitudeCanonical_atPrime_of_hasTorAmplitudeAt
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (q : Ideal B) [q.IsPrime] (a b : ℤ)
    (hamp : HasTorAmplitudeAt A
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) q a b) :
    let _ : Algebra (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
    HasTorAmplitudeCanonical (Localization.AtPrime (Ideal.under A q))
      ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q))) 0).obj
        (ModuleCat.of (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q)))
      a b := by
  set p := Ideal.under A q
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let ext := ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q))
  let restr := ModuleCat.restrictScalars
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
  have hextAdd : ext.Additive :=
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap B (Localization.AtPrime q))).left_adjoint_additive
  have hrestrAdd : restr.Additive := inferInstance
  let comp := CategoryTheory.Functor.comp ext restr
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  let K' : HomologicalComplex (ModuleCat.{u} B) (ComplexShape.up ℤ) := K
  let eComp := (CategoryTheory.Functor.mapHomologicalComplexCompIso
    (CategoryTheory.Iso.refl comp) (ComplexShape.up ℤ)).app K'
  let eSingleC := (HomologicalComplex.singleMapHomologicalComplex
    comp (ComplexShape.up ℤ) 0).app (ModuleCat.of B B)
  have hamp1 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
        (comp.obj (ModuleCat.of B B))) a b := by
    change FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).obj
        ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b
      at hamp
    exact hasTorAmplitude0DJF_of_isoComplex (eComp ≪≫ eSingleC) hamp
  let eModule : (comp.obj (ModuleCat.of B B)) ≅
      ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q) := by
    let eExt : (ext.obj (ModuleCat.of B B)) ≅
        ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q) :=
      (LinearEquiv.trans
        (FaithfullyFlat.extendScalarsCarrierEquiv B (Localization.AtPrime q)
          (ModuleCat.of B B))
        (TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime q)
          (Localization.AtPrime q))).toModuleIso
    change restr.obj (ext.obj (ModuleCat.of B B)) ≅
      restr.obj (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))
    exact restr.mapIso eExt
  have hamp2 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
        (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q))) a b :=
    hasTorAmplitude0DJF_of_isoComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).mapIso eModule)
      hamp1
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative (Localization.AtPrime p)
    ((DerivedCategory.singleFunctor
        (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q))) a b).mpr
    (hasFlatRepresentative_single_of_0DJF (Localization.AtPrime p)
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q)) a b hamp2)

/-! ### The geometric square at a point -/

/-- The commuting square of structure maps at a point of a compatible pair of affine opens: the
stalk map of `f` after the germ map of the base is the germ map of the source after `f.appLE`. -/
private theorem stalk_tower_eq {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (hxU : x ∈ U) :
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    let _ := S.presheaf.algebra_section_stalk (⟨f.base x, hUV hxU⟩ : V)
    let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)).comp
        (algebraMap Γ(S, V) (S.presheaf.stalk (f.base x)))
      = (algebraMap Γ(X, U) (X.presheaf.stalk x)).comp (algebraMap Γ(S, V) Γ(X, U)) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ := S.presheaf.algebra_section_stalk (⟨f.base x, hUV hxU⟩ : V)
  let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  have halgR : (algebraMap Γ(S, V) (S.presheaf.stalk (f.base x)))
      = (S.presheaf.germ V (f.base x) (hUV hxU)).hom := RingHom.algebraMap_toAlgebra _
  have halgM : (algebraMap Γ(X, U) (X.presheaf.stalk x))
      = (X.presheaf.germ U x hxU).hom := RingHom.algebraMap_toAlgebra _
  have halgRM : (algebraMap (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x))
      = (f.stalkMap x).hom := RingHom.algebraMap_toAlgebra _
  have halgAB : (algebraMap Γ(S, V) Γ(X, U)) = (f.appLE V U hUV).hom :=
    RingHom.algebraMap_toAlgebra _
  have hsq : f.appLE V U hUV ≫ X.presheaf.germ U x hxU
      = S.presheaf.germ V (f.base x) (hUV hxU) ≫ f.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res,
      ← Scheme.Hom.germ_stalkMap f V x (hUV hxU)]
  ext s
  simp only [RingHom.coe_comp, Function.comp_apply, halgR, halgM, halgRM, halgAB]
  exact (ConcreteCategory.congr_hom hsq s).symm

/-! ### The equivalence -/

namespace Perfect

/-- **Perfectness bounds the Tor amplitude of the stalks uniformly on an affine chart.** Let
`f : X ⟶ S` be perfect and let `U ≤ f ⁻¹ᵁ V` be a compatible pair of affine opens. Then there is
*one* interval `[a, b]` containing the Tor amplitude of `𝒪_{X, y}` over `𝒪_{S, f y}` for every
point `y` of `U`.

This is `AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect` read at the stalks instead of at
the canonical localisations, and the point of the statement is that the interval survives the
passage: `hasTorAmplitudeCanonical_atPrime_of_hasTorAmplitudeAt` and
`hasTorAmplitudeCanonical_models_iff` both keep it, since both only move flat representatives of
Stacks 0654 across ring isomorphisms. It is the chart-level hypothesis of
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_of_forall_affineOpen`, so it
is what carries the implication (1) ⟹ (2) of Stacks 069C; the weaker
`hasFiniteTorDimensionCanonical_stalk` below, which drops the interval, is enough only for
(1) ⟹ (3). -/
theorem exists_hasTorAmplitudeCanonical_stalk_of_affineOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [Perfect f] (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃ a b : ℤ, ∀ y : X, y ∈ U →
      let _ : Algebra (S.presheaf.stalk (f.base y)) (X.presheaf.stalk y) :=
        (f.stalkMap y).hom.toAlgebra
      HasTorAmplitudeCanonical (S.presheaf.stalk (f.base y))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base y))) 0).obj
          (ModuleCat.of (S.presheaf.stalk (f.base y)) (X.presheaf.stalk y))) a b := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  obtain ⟨a, b, hamp⟩ := hasTorAmplitudeAt_of_perfect f U hU V hV hUV
  refine ⟨a, b, fun y hyU => ?_⟩
  let _ : Algebra (S.presheaf.stalk (f.base y)) (X.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  let _ := S.presheaf.algebra_section_stalk (⟨f.base y, hUV hyU⟩ : V)
  let _ := X.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  have hqPrime : ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal).IsPrime :=
    (hU.primeIdealOf ⟨y, hyU⟩).isPrime
  have hpPrime : ((hV.primeIdealOf ⟨f.base y, hUV hyU⟩).asIdeal).IsPrime :=
    (hV.primeIdealOf ⟨f.base y, hUV hyU⟩).isPrime
  have hlocS : IsLocalization.AtPrime (S.presheaf.stalk (f.base y))
      (hV.primeIdealOf ⟨f.base y, hUV hyU⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f.base y, hUV hyU⟩
  have hlocX : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := hU.isLocalization_stalk ⟨y, hyU⟩
  exact (hasTorAmplitudeCanonical_models_iff
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal (hV.primeIdealOf ⟨f.base y, hUV hyU⟩).asIdeal
    (under_primeIdealOf_eq f U hU V hV hUV hyU)
    (stalk_tower_eq f U V hUV hyU) a b).mp
    (hasTorAmplitudeCanonical_atPrime_of_hasTorAmplitudeAt
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal a b
      (hamp (hU.primeIdealOf ⟨y, hyU⟩).asIdeal hqPrime))

/-- **Perfectness gives finite Tor dimension at every stalk.** For a perfect morphism of schemes
`f : X ⟶ S` and a point `x` of `X`, the local ring `𝒪_{X, x}`, viewed as an `𝒪_{S, f x}`-module
through the stalk map, has finite Tor dimension.

This is the implication (1) ⟹ (3) of Stacks 069C. Perfectness is used through
`AlgebraicGeometry.Perfect.exists_hasTorAmplitudeCanonical_stalk_of_affineOpen`, which gives one
interval bounding the Tor amplitude at every point of an affine chart around `x`; only the
existence of some interval at `x` is kept here. -/
theorem hasFiniteTorDimensionCanonical_stalk {X S : Scheme.{u}} (f : X ⟶ S) [Perfect f] (x : X) :
    let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base x))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base x))) 0).obj
        (ModuleCat.of (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x))) := by
  let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxV (f ⁻¹ᵁ V).2
  obtain ⟨a, b, hamp⟩ := exists_hasTorAmplitudeCanonical_stalk_of_affineOpen f U hU V hV hUV
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
    (S.presheaf.stalk (f.base x)) _).mpr ⟨a, b, hamp x hxU⟩

end Perfect

/-- The stalk condition at the point of an affine chart `U ≤ f ⁻¹ᵁ V` corresponding to a prime
`y` of `Γ(X, U)` gives finite Tor dimension of the localisation at `y` over the localisation at
the prime of `Γ(S, V)` under it. -/
private theorem hasFiniteTorDimensionCanonical_localization_of_stalk {X S : Scheme.{u}}
    (f : X ⟶ S) (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (y : PrimeSpectrum Γ(X, U))
    (hstalk :
      let _ : Algebra (S.presheaf.stalk (f.base (hU.fromSpec.base y)))
          (X.presheaf.stalk (hU.fromSpec.base y)) :=
        (f.stalkMap (hU.fromSpec.base y)).hom.toAlgebra
      HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base (hU.fromSpec.base y)))
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (S.presheaf.stalk (f.base (hU.fromSpec.base y)))) 0).obj
          (ModuleCat.of (S.presheaf.stalk (f.base (hU.fromSpec.base y)))
            (X.presheaf.stalk (hU.fromSpec.base y))))) :
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    let _ : Algebra (Localization.AtPrime (Ideal.under Γ(S, V) y.asIdeal))
        (Localization.AtPrime y.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under Γ(S, V) y.asIdeal) y.asIdeal
    HasFiniteTorDimensionCanonical (Localization.AtPrime (Ideal.under Γ(S, V) y.asIdeal))
      ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Localization.AtPrime (Ideal.under Γ(S, V) y.asIdeal))) 0).obj
        (ModuleCat.of (Localization.AtPrime (Ideal.under Γ(S, V) y.asIdeal))
          (Localization.AtPrime y.asIdeal))) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hxU : hU.fromSpec.base y ∈ U := by
    have hmem : hU.fromSpec.base y ∈ Set.range hU.fromSpec.base := Set.mem_range_self y
    rwa [hU.range_fromSpec] at hmem
  have hprime : hU.primeIdealOf ⟨hU.fromSpec.base y, hxU⟩ = y :=
    hU.fromSpec.isOpenEmbedding.injective
      (hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base y, hxU⟩)
  let _ : Algebra (S.presheaf.stalk (f.base (hU.fromSpec.base y)))
      (X.presheaf.stalk (hU.fromSpec.base y)) :=
    (f.stalkMap (hU.fromSpec.base y)).hom.toAlgebra
  let _ := S.presheaf.algebra_section_stalk
    (⟨f.base (hU.fromSpec.base y), hUV hxU⟩ : V)
  let _ := X.presheaf.algebra_section_stalk (⟨hU.fromSpec.base y, hxU⟩ : U)
  have hpPrime :
      ((hV.primeIdealOf ⟨f.base (hU.fromSpec.base y), hUV hxU⟩).asIdeal).IsPrime :=
    (hV.primeIdealOf ⟨f.base (hU.fromSpec.base y), hUV hxU⟩).isPrime
  have hlocS : IsLocalization.AtPrime
      (S.presheaf.stalk (f.base (hU.fromSpec.base y)))
      (hV.primeIdealOf ⟨f.base (hU.fromSpec.base y), hUV hxU⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f.base (hU.fromSpec.base y), hUV hxU⟩
  have hlocX : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec.base y))
      y.asIdeal := by
    have h0 := hU.isLocalization_stalk (⟨hU.fromSpec.base y, hxU⟩ : U)
    rwa [hprime] at h0
  have hpq : Ideal.under Γ(S, V) y.asIdeal
      = (hV.primeIdealOf ⟨f.base (hU.fromSpec.base y), hUV hxU⟩).asIdeal := by
    have h1 := Perfect.under_primeIdealOf_eq f U hU V hV hUV hxU
    rwa [hprime] at h1
  exact (hasFiniteTorDimensionCanonical_models_iff
    (R := S.presheaf.stalk (f.base (hU.fromSpec.base y)))
    (T := X.presheaf.stalk (hU.fromSpec.base y)) y.asIdeal
    (hV.primeIdealOf ⟨f.base (hU.fromSpec.base y), hUV hxU⟩).asIdeal hpq
    (stalk_tower_eq f U V hUV hxU)).mpr hstalk

/-- **Finite Tor dimension at every stalk gives perfectness.** This is the implication (3) ⟹ (1)
of Stacks 069C, from the affine ring-theoretic core of the source's argument.

The affine core of the source's argument — a pseudo-coherent ring map `A → B` all of whose
localisations `B_q` have finite Tor dimension over `A_{q ∩ A}` has finite Tor dimension — is
`RingHom.hasFiniteTorDimensionRingHom_of_forall_localizationAtPrime`. What is proved here is the
geometric half: the affine-local reduction of perfectness, and the identification of the stalks
with the localisations that core is stated at. -/
theorem perfect_of_forall_hasFiniteTorDimensionCanonical_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    [PseudoCoherent f]
    (hstalk : ∀ x : X,
      let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base x))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base x))) 0).obj
          (ModuleCat.of (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)))) :
    Perfect f := by
  refine { perfect_appLE := ?_ }
  intro U hU V hV hUV
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hpc : (f.appLE V U hUV).hom.PseudoCoherent :=
    PseudoCoherent.pseudoCoherent_appLE f hV hU hUV
  have htor : HasFiniteTorDimensionRingHom (f.appLE V U hUV).hom :=
    RingHom.hasFiniteTorDimensionRingHom_of_forall_localizationAtPrime (f.appLE V U hUV).hom hpc
      fun q hq =>
        hasFiniteTorDimensionCanonical_localization_of_stalk f U hU V hV hUV ⟨q, hq⟩ (hstalk _)
  exact fun D => ⟨hpc, (hasFiniteTorDimensionRingHom_iff_forall (f.appLE V U hUV).hom).mp htor D⟩

/-- **The equivalence of (1) and (3) in Stacks 069C.** A pseudo-coherent morphism of schemes
`f : X ⟶ S` is perfect if and only if, for every point `x` of `X`, the local ring `𝒪_{X, x}` has
finite Tor dimension as a module over `𝒪_{S, f x}` through the stalk map.

The full equivalence of the three conditions of Stacks 069C, including that `𝒪_X` locally has
finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules, is `AlgebraicGeometry.perfect_tfae` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RelativeTorDimensionClause`.

The converse rests on the affine ring-theoretic core of the
source's argument — a pseudo-coherent ring map `A → B` all of whose localisations `B_q` have
finite Tor dimension over `A_{q ∩ A}` has finite Tor dimension — which is
`RingHom.hasFiniteTorDimensionRingHom_of_forall_localizationAtPrime`, proved from a finite
polynomial presentation together with Stacks 068X and 068W as the source does. -/
theorem perfect_iff_forall_hasFiniteTorDimensionCanonical_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    [PseudoCoherent f] :
    Perfect f ↔
      ∀ x : X,
        let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
          (f.stalkMap x).hom.toAlgebra
        HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base x))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base x))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x))) :=
  ⟨fun _ x => Perfect.hasFiniteTorDimensionCanonical_stalk f x,
    perfect_of_forall_hasFiniteTorDimensionCanonical_stalk f⟩

end AlgebraicGeometry

end
