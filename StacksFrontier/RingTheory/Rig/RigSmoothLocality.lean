module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothTower
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocal

/-!
# Rig-smoothness is a local property of arrows of `WAdm^Noeth`

A continuous homomorphism of Noetherian adic topological rings is rig-smooth (Stacks 0GCJ) when
it is adic of topologically finite type — condition (6) of Stacks 0GBW — and a power of an ideal
of definition of its source annihilates `Ext¹` out of the completed naive cotangent complex of
its target.  Stacks 0GCK asserts that this is a *local property* in the sense of Situation 0CBA,
in the Noetherian form of Remark 0ANI: writing a localization diagram as

```
B ────────→ (B')^
│             │
│ φ           │ φ'
↓             ↓
A ────────→ (A')^
```

with `B → B'` and `A → A'` étale, rig-smoothness ascends from `φ` to `φ'`, descends from `φ'` to
`φ` when `A → A'` is faithfully flat, and is preserved by finite products of targets.

The finite-type half of rig-smoothness is the locality of Stacks 0GBW.  For the annihilation
half the proof follows the source.  The completed naive cotangent complexes of `(A')^` over `A`
and of `(B')^` over `B` have bijective differential, by Stacks 0GAF applied to the étale maps
(`Rig.isRigSmoothArrow_canonicalMap`), so the transitivity sequence of Stacks 0ALM for
`B → (B')^ → (A')^` compares `NL^∧_{(A')^/B}` with `NL^∧_{(A')^/(B')^}`
(`Rig.isRigSmooth_of_comp_of_bijective`), and the one for `B → A → (A')^`, together with
Stacks 0AQJ for the étale reductions of `A → (A')^`, compares `NL^∧_{(A')^/B}` with
`NL^∧_{A/B} ⊗_A (A')^` (`Rig.exists_factor_innerBaseChange_of_bijective_outer`).  Ascent then
goes through Stacks 0GCM, descent through faithfully flat descent of the factorization of
condition (3) of Stacks 0GAJ (`Rig.isRigSmooth_of_faithfullyFlat_of_bijective_outer`), and
finite products through the same comparison for the projections `∏ Aᵢ → Aᵢ`, which are
localizations at idempotents, followed by gluing the factorizations over the factors
(`Rig.exists_factor_of_finite_family`).

## Main results

* `Rig.rigSmooth_isLocalNoetherian` — **Stacks 0GCK**.
* `Rig.rigSmooth_localizationPreserves`, `Rig.rigSmooth_faithfullyFlatDescent` and
  `Rig.rigSmooth_finiteProductPreserves` — the three axioms separately.
* `Rig.isAdic_pi` — a finite product of Noetherian adic topological rings is adic.

## Implementation notes

The three locality axioms are quantified over the subcategory of Noetherian adic rings, so each
corner of a localization diagram and each factor of a finite product comes with adicness and
Noetherianity.  `RingHom.IsRigSmoothArrow` quantifies over the linear-topology and Noetherian
instances of its source and target instead of demanding them, so in each axiom those instances
arrive as hypotheses of the goal and never have to be constructed — except for the product of a
finite family, whose adicness is not an instance and is `Rig.isAdic_pi`.  That lemma rests on
the identification of a power of `Ideal.pi` with the `Ideal.pi` of the powers, which holds
because ideals of a finite product of rings are products of ideals (`Ideal.piOrderIso`).

## References

* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GCI](https://stacks.math.columbia.edu/tag/0GCI)
* [Stacks Project, Tag 0GCJ](https://stacks.math.columbia.edu/tag/0GCJ)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0AQJ](https://stacks.math.columbia.edu/tag/0AQJ)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory Filter TopologicalRing Rig.CompletedPolynomialPresentation
open scoped Topology TensorProduct

namespace Rig

attribute [local instance] HasDerivedCategory.standard

universe u

/-- A power of the product of a family of ideals is the product of their powers, over a finite
index type. -/
private theorem pi_pow {ι : Type*} [Finite ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    (I : ∀ i, Ideal (R i)) (n : ℕ) :
    (Ideal.pi I) ^ n = Ideal.pi (fun i ↦ I i ^ n) := by
  calc (Ideal.pi I) ^ n
      = Ideal.pi (fun i ↦ ((Ideal.pi I) ^ n).map (Pi.evalRingHom R i)) :=
        (Ideal.piOrderIso.symm_apply_apply ((Ideal.pi I) ^ n)).symm
    _ = Ideal.pi (fun i ↦ I i ^ n) := by
        refine congrArg Ideal.pi (funext fun i ↦ ?_)
        rw [Ideal.map_pow, Ideal.map_evalRingHom_pi]

/-- A power of the product of a family of ideals is the product of their powers, over a finite
index type. -/
public alias pi_pow' := pi_pow

/-- The underlying set of a product of ideals is the product of their underlying sets. -/
private theorem coe_pi_eq {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    (I : ∀ i, Ideal (R i)) :
    ((Ideal.pi I : Ideal (∀ i, R i)) : Set (∀ i, R i)) =
      Set.univ.pi (fun i ↦ ((I i : Ideal (R i)) : Set (R i))) := by
  ext x
  simp [Ideal.mem_pi]

/-- **A finite product of Noetherian adic topological rings is adic.** The product of ideals of
definition of the factors is an ideal of definition of the product and defines its topology
through its powers, and a finite product of complete separated rings is complete and
separated. -/
public theorem isAdic_pi {ι : Type u} [Finite ι] (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
    [∀ i, IsLinearTopology (A i) (A i)]
    (h : ∀ i, TopologicalRing.IsAdic (A i)) :
    TopologicalRing.IsAdic (∀ i, A i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose I hIdef hIadic using fun i ↦ (h i).1
  have hopen : ∀ (J : ∀ i, Ideal (A i)), (∀ i, IsOpen ((J i : Ideal (A i)) : Set (A i))) →
      IsOpen ((Ideal.pi J : Ideal (∀ i, A i)) : Set (∀ i, A i)) := by
    intro J hJ
    rw [coe_pi_eq]
    exact isOpen_set_pi Set.finite_univ fun i _ ↦ hJ i
  have hJadic : _root_.IsAdic (Ideal.pi I) := by
    refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
    · rw [pi_pow]
      exact hopen _ fun i ↦ ((isAdic_iff.mp (hIadic i)).1 n)
    · rw [nhds_pi] at hs
      obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hs
      choose m hm using fun i ↦ (isAdic_iff.mp (hIadic i)).2 (V i) (hV i)
      refine ⟨Finset.univ.sup m, fun x hx ↦ hsub fun i _ ↦ ?_⟩
      rw [pi_pow] at hx
      have hxi : x i ∈ I i ^ Finset.univ.sup m := hx i
      exact hm i (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) hxi)
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).2.1
  let : ∀ i, UniformSpace (A i) := fun i ↦ IsTopologicalAddGroup.rightUniformSpace (A i)
  let : ∀ i, IsUniformAddGroup (A i) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ i, CompleteSpace (A i) := fun i ↦ (h i).2.2
  let : UniformSpace (∀ i, A i) := Pi.uniformSpace A
  let : IsUniformAddGroup (∀ i, A i) := ⟨by
    rw [uniformContinuous_pi]
    intro i
    exact ((Pi.uniformContinuous_proj A i).comp uniformContinuous_fst).sub
      ((Pi.uniformContinuous_proj A i).comp uniformContinuous_snd)⟩
  have hPiComplete : @CompleteSpace (∀ i, A i)
      (IsTopologicalAddGroup.rightUniformSpace (∀ i, A i)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact Pi.complete A
  refine ⟨⟨Ideal.pi I, ⟨?_, ?_⟩, hJadic⟩, inferInstance, hPiComplete⟩
  · simpa using (isAdic_iff.mp hJadic).1 1
  · exact (isAdic_iff.mp hJadic).2

/-- A positive power of an ideal defining an adic topology defines the same topology. -/
private theorem isAdic_pow_succ {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {J : Ideal R} (hJ : _root_.IsAdic J) (n : ℕ) :
    _root_.IsAdic (J ^ (n + 1)) := by
  rw [isAdic_iff]
  refine ⟨fun m => by simpa [pow_mul] using (isAdic_iff.mp hJ).1 ((n + 1) * m),
    fun s hs => ?_⟩
  obtain ⟨m, hm⟩ := (isAdic_iff.mp hJ).2 s hs
  refine ⟨m, fun x hx => hm ?_⟩
  have hle : (J ^ (n + 1)) ^ m ≤ J ^ m := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left m (Nat.succ_pos n))
  exact hle hx

/-- A positive power of an ideal defining an adic topology defines the same topology — the
publicly visible form of the private `Rig.isAdic_pow_succ`, for the consumers of this file that
need it outside the module (`StacksFrontier.RingTheory.Rig.RigEtaleLocality`). -/
public alias isAdic_pow_succ' := isAdic_pow_succ

/-- Condition (1) of Stacks 0GBW is equivalent to condition (6) for Noetherian adic rings. -/
private theorem adicFiniteType_iff {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] (φ : A →+* B)
    (hA : TopologicalRing.IsAdic A) (hAn : IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B) (hBn : IsNoetherianRing B) :
    (RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) ↔
      Rig.FiniteTypeAdicAlgebraForEveryIdeal φ :=
  (Rig.adicFiniteType_tfae φ hA hB (exists_idealOfDefinition_fg hA hAn)
    (exists_idealOfDefinition_fg hB hBn)).out 1 6

/-- **Rig-smoothness ascends along a localization diagram** (axiom (1) of Situation 0CBA).
The composite `B → A → (A')^` is rig-smooth by Stacks 0GCM, `A → (A')^` being rig-smooth as the
completion of an étale map; it equals `B → (B')^ → (A')^`, and `B → (B')^` has a presentation
with bijective completed cotangent differential, so `(B')^ → (A')^` is rig-smooth by
`Rig.isRigSmooth_of_comp_of_bijective`.  Condition (6) of Stacks 0GBW for `(B')^ → (A')^` is
the locality of Stacks 0GBW. -/
public theorem rigSmooth_localizationPreserves :
    TopologicalRing.LocalizationPreserves.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP _ _ _ _
  let : IsNoetherianRing A := hA.2
  let : IsNoetherianRing B := hB.2
  have hPmap : Continuous D.map ∧ RingHom.IsRigSmooth D.map := hP
  obtain ⟨-, hft, -⟩ := hPmap
  have hone : RingHom.IsAdic D.map ∧ TopologicalRing.IsTopologicallyOfFiniteType D.map :=
    (adicFiniteType_iff D.map hB.1 hB.2 hA.1 hA.2).mpr hft
  have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.localizationPreserves
    D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
    (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hone
  have hft' : Rig.FiniteTypeAdicAlgebraForEveryIdeal D.completedMap :=
    (adicFiniteType_iff D.completedMap hB'.1 hB'.2 hA'.1 hA'.2).mp hcomp
  obtain ⟨-, hβcont, -, -, -⟩ := canonicalMap_facts D.toA' hA.1 hA'.1 D.etaleA
  obtain ⟨-, hαcont, hαadic, hαft, -⟩ := canonicalMap_facts D.toB' hB.1 hB'.1 D.etaleB
  have hcomp' := rigSmooth_comp hA' hA hB (CompletionOver.canonicalMap D.toA') D.map hβcont
    D.continuousMap (isRigSmoothArrow_canonicalMap D.toA' D.etaleA hA.1 hA') hP
  rw [D.commutes] at hcomp'
  obtain ⟨hcont', hrig'⟩ := hcomp'
  have hftα : Rig.FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap D.toB') :=
    (adicFiniteType_iff _ hB.1 hB.2 hB'.1 hB'.2).mp ⟨hαadic, hαft⟩
  obtain ⟨I, hI, hIadic⟩ := hB.1.1
  obtain ⟨P, hPbij⟩ := exists_presentation_bijective_canonicalMap D.toB' D.etaleB hftα hI hIadic
  exact ⟨D.continuousCompletedMap, isRigSmooth_of_comp_of_bijective hA'.1 hB.1 D.completedMap
    (CompletionOver.canonicalMap D.toB') hcont' hft' hftα hI P hPbij hrig'⟩

/-- **Rig-smoothness descends along a faithfully flat localization diagram** (axiom (2) of
Situation 0CBA).  The composite `B → (B')^ → (A')^` is rig-smooth by Stacks 0GCM; it equals
`B → A → (A')^`, where `A → (A')^` is faithfully flat (Stacks 0AN9), has a presentation with
bijective completed cotangent differential, and has étale reductions modulo the powers of an
ideal of definition, so `B → A` is rig-smooth by
`Rig.isRigSmooth_of_faithfullyFlat_of_bijective_outer`. -/
public theorem rigSmooth_faithfullyFlatDescent :
    TopologicalRing.FaithfullyFlatDescent.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hP _ _ _ _
  let : IsNoetherianRing (CompletionOver D.toA') := hA'.2
  let : IsNoetherianRing (CompletionOver D.toB') := hB'.2
  have hPmap : Continuous D.completedMap ∧ RingHom.IsRigSmooth D.completedMap := hP
  obtain ⟨-, hft', -⟩ := hPmap
  have hone' : RingHom.IsAdic D.completedMap ∧
      TopologicalRing.IsTopologicallyOfFiniteType D.completedMap :=
    (adicFiniteType_iff D.completedMap hB'.1 hB'.2 hA'.1 hA'.2).mpr hft'
  have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.faithfullyFlatDescent
    D (exists_fg_isAdic hA.1 hA.2) (exists_fg_isAdic hB.1 hB.2)
    (exists_fg_isAdic hA'.1 hA'.2) (exists_fg_isAdic hB'.1 hB'.2) hFF hone'
  have hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal D.map :=
    (adicFiniteType_iff D.map hB.1 hB.2 hA.1 hA.2).mp hcomp
  obtain ⟨-, hαcont, -, -, -⟩ := canonicalMap_facts D.toB' hB.1 hB'.1 D.etaleB
  obtain ⟨hA'noeth, hβcont, hβadic, hβft, -⟩ := canonicalMap_facts D.toA' hA.1 hA'.1 D.etaleA
  let : IsNoetherianRing A' := hA'noeth
  have hcomp' := rigSmooth_comp hA' hB' hB D.completedMap (CompletionOver.canonicalMap D.toB')
    D.continuousCompletedMap hαcont hP (isRigSmoothArrow_canonicalMap D.toB' D.etaleB hB.1 hB')
  rw [← D.commutes] at hcomp'
  obtain ⟨hcontc, hftc, I₀, hI₀, hrig₀⟩ := hcomp'
  obtain ⟨I, hI, -⟩ := hB.1.1
  have hrigI := (Rig.isRigSmooth_iff_forall_idealOfDefinition
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hA'.1) _ hcontc
    hftc).mp ⟨I₀, hI₀, hrig₀⟩ I hI
  have hftβ : Rig.FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap D.toA') :=
    (adicFiniteType_iff _ hA.1 hA.2 hA'.1 hA'.2).mp ⟨hβadic, hβft⟩
  have hJadic : _root_.IsAdic (I.map D.map) := (hft I hI).1
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map D.map) :=
    Rig.isIdealOfDefinition_of_isAdic hJadic
  let : Algebra B A := D.map.toAlgebra
  let : Algebra A (CompletionOver D.toA') := (CompletionOver.canonicalMap D.toA').toAlgebra
  let : Algebra B (CompletionOver D.toA') :=
    ((CompletionOver.canonicalMap D.toA').comp D.map).toAlgebra
  let base := adicFiniteTypeAlgebra D.map hft I hI
  let total := adicFiniteTypeAlgebra ((CompletionOver.canonicalMap D.toA').comp D.map) hftc I hI
  let fiber : AdicFiniteTypeAlgebra.{u, u} base.carrier base.adicIdeal :=
    adicFiniteTypeAlgebra (CompletionOver.canonicalMap D.toA') hftβ (I.map D.map) hJ
  let : Algebra base.carrier total.carrier :=
    (inferInstance : Algebra base.carrier fiber.carrier)
  let : IsScalarTower B base.carrier total.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨Q, hQ⟩ := exists_presentation_bijective_canonicalMap D.toA' D.etaleA hftβ hJ hJadic
  let KF := completedNaiveCotangentComplex fiber Q
  let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin Q.variableCount)
      →ₐ[base.carrier] total.carrier := Q.toAlgHom
  have hψ : Function.Surjective (ψ.restrictScalars B) := Q.toAlgHom_surjective
  have houter : outerDifferential Q.variableCount ψ hψ (fun j => KF.partialDeriv j) =
      KF.differential := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Q.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  have : Module.FaithfullyFlat base.carrier total.carrier :=
    TopologicalRing.CompletionOver.faithfullyFlat_canonicalMap hA.1 hFF
  have hlci := isLocalCompleteIntersection_reductionMap_of_etale (base := base) (total := total)
    fun n => etale_quotientMap_canonicalMap D.toA'
      (Rig.isIdealOfDefinition_of_isAdic (isAdic_pow_succ hJadic n))
      (isAdic_pow_succ hJadic n) D.etaleA
  exact ⟨D.continuousMap, hft, I, hI, isRigSmooth_of_faithfullyFlat_of_bijective_outer
    Q.variableCount ψ hψ (fun j => KF.partialDeriv j)
    (houter ▸ hQ) hlci hrigI⟩

/-- **Rig-smoothness is preserved by finite products of targets** (axiom (3) of Situation
0CBA).  Each projection `∏ Aⱼ → Aᵢ` is the localization at an idempotent, hence étale and flat,
and `Aᵢ` is its own completion; so the comparison of
`Rig.exists_factor_innerBaseChange_of_bijective_outer` applies to `B → ∏ Aⱼ → Aᵢ`, and the
factorizations it produces after base change to the factors glue
(`Rig.exists_factor_of_finite_family`). -/
public theorem rigSmooth_finiteProductPreserves :
    TopologicalRing.FiniteProductPreserves.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) := by
  intro B _ _ _ _ hBweak hBcount ι _ A _ _ _ _ hAweak hAcount f hf hCB hCA hPi _ _ _ _
  classical
  let : ∀ i, IsNoetherianRing (A i) := fun i ↦ (hCA i).2
  have hPi' : ∀ i, Continuous (f i) ∧ RingHom.IsRigSmooth (f i) := fun i ↦ hPi i
  have hprodadic : TopologicalRing.IsAdic (∀ i, A i) := isAdic_pi A fun i ↦ (hCA i).1
  have hone : ∀ i, RingHom.IsAdic (f i) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (f i) := by
    intro i
    obtain ⟨-, hfti, -⟩ := hPi' i
    exact (adicFiniteType_iff (f i) hCB.1 hCB.2 (hCA i).1 (hCA i).2).mpr hfti
  have hcomp := TopologicalRing.adicTopologicallyFiniteType_isLocal.finiteProduct
    hBweak hBcount A hAweak hAcount f hf (exists_fg_isAdic hCB.1 hCB.2)
    (fun i ↦ exists_fg_isAdic (hCA i).1 (hCA i).2) hone
  have hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal (RingHom.pi f) :=
    (adicFiniteType_iff (RingHom.pi f) hCB.1 hCB.2 hprodadic inferInstance).mp
      hcomp
  obtain ⟨I, hI, -⟩ := hCB.1.1
  have hfti : ∀ i, Rig.FiniteTypeAdicAlgebraForEveryIdeal (f i) := fun i ↦ (hPi' i).2.1
  have hrigi : ∀ i, Rig.IsRigSmooth (adicFiniteTypeAlgebra (f i) (hfti i) I hI) := by
    intro i
    obtain ⟨-, hft₀, I₀, hI₀, hrig₀⟩ := hPi' i
    exact (Rig.isRigSmooth_iff_forall_idealOfDefinition
      (weaklyAdmissible_of_isAdicRing hCB.1) (weaklyAdmissible_of_isAdicRing (hCA i).1)
      (f i) (hf i) (hfti i)).mp ⟨I₀, hI₀, hrig₀⟩ I hI
  let : Algebra B (∀ j, A j) := (RingHom.pi f).toAlgebra
  let : ∀ i, Algebra B (A i) := fun i ↦ (f i).toAlgebra
  let base := adicFiniteTypeAlgebra (RingHom.pi f) hft I hI
  let total : ι → AdicFiniteTypeAlgebra.{u, u} B I := fun i ↦
    adicFiniteTypeAlgebra (f i) (hfti i) I hI
  let : ∀ i, Algebra (∀ j, A j) (A i) := fun i ↦ (Pi.evalRingHom A i).toAlgebra
  let : ∀ i, Algebra base.carrier (total i).carrier := fun i ↦ (Pi.evalRingHom A i).toAlgebra
  have : ∀ i, IsScalarTower B base.carrier (total i).carrier := fun i ↦
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hloc : ∀ i, IsLocalization.Away (Pi.single i 1 : ∀ j, A j) (A i) := by
    intro i
    refine IsLocalization.away_of_isIdempotentElem_of_mul ?_ (fun x y => ?_) (fun x => ?_)
    · funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    · change x i = y i ↔ _
      constructor
      · intro hxy
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hxy]
        · simp [Pi.single_eq_of_ne hj]
      · intro hxy
        simpa using congrFun hxy i
    · exact ⟨Pi.single i x, by simp [RingHom.algebraMap_toAlgebra]⟩
  have hétale : ∀ i, (algebraMap base.carrier (total i).carrier).Etale := fun i ↦
    (RingHom.etale_algebraMap.mpr
      (Algebra.Etale.of_isLocalizationAway (Pi.single i 1 : ∀ j, A j)) :
        (Pi.evalRingHom A i).Etale)
  have : ∀ i, Module.Flat base.carrier (total i).carrier := fun i ↦
    (IsLocalization.flat (A i) (Submonoid.powers (Pi.single i 1 : ∀ j, A j)) :
      Module.Flat (∀ j, A j) (A i))
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  let KB := completedNaiveCotangentComplex base P
  have key : ∀ i, ∃ c : ℕ, ∀ a : B, a ∈ I ^ c →
      ∃ h : (Fin P.variableCount → (total i).carrier) →ₗ[(total i).carrier]
          (total i).carrier ⊗[base.carrier] P.extension.Cotangent,
        h ∘ₗ P.innerBaseChangeDifferential (C := total i) KB =
          (algebraMap B (total i).carrier a) • LinearMap.id := by
    intro i
    let K := base.adicIdeal.map (algebraMap base.carrier (total i).carrier)
    have hid : K = (total i).adicIdeal := AdicFiniteTypeAlgebra.map_adicIdeal_tower
    have hcompl : IsAdicComplete K (total i).carrier := hid ▸ (total i).isAdicallyComplete
    have : Algebra.FiniteType (base.carrier ⧸ base.adicIdeal) ((total i).carrier ⧸ K) := by
      refine Algebra.FiniteType.of_surjective (Algebra.ofId _ _) fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨Ideal.Quotient.mk _ (show base.carrier from Pi.single i (show A i from x)), ?_⟩
      exact congrArg (Ideal.Quotient.mk K) (Pi.single_eq_same i (show A i from x))
    let X : AdicFiniteTypeAlgebra.{u, u} base.carrier base.adicIdeal :=
      AdicFiniteTypeAlgebra.of (total i).carrier hcompl
    obtain ⟨Q, hQ⟩ := exists_presentation_bijective_of_etale base.adicIdeal
      (algebraMap base.carrier (total i).carrier) (hétale i) X
      (AdicCompletion.ofAlgEquiv K).symm.toRingEquiv fun s => by
        have h1 : algebraMap (total i).carrier (AdicCompletion K (total i).carrier)
            (algebraMap base.carrier (total i).carrier s) =
            AdicCompletion.ofAlgEquiv K (algebraMap base.carrier (total i).carrier s) :=
          ((AdicCompletion.ofAlgEquiv K).commutes _).symm
        exact (congrArg _ h1).trans ((AdicCompletion.ofAlgEquiv K).symm_apply_apply _)
    let KF := completedNaiveCotangentComplex X Q
    let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin Q.variableCount)
        →ₐ[base.carrier] (total i).carrier := Q.toAlgHom
    have hψ : Function.Surjective (ψ.restrictScalars B) := Q.toAlgHom_surjective
    have houter : outerDifferential Q.variableCount ψ hψ (fun j => KF.partialDeriv j) =
        KF.differential := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Q.extension) z
      funext j
      exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
        (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
    have hlci := isLocalCompleteIntersection_reductionMap_of_etale (base := base)
      (total := total i) fun n => TopologicalRing.quotientMap_of_isStableUnderBaseChange
        RingHom.Etale.isStableUnderBaseChange RingHom.Etale.respectsIso
        (algebraMap base.carrier (total i).carrier) (hétale i) (base.adicIdeal ^ (n + 1))
    exact exists_factor_innerBaseChange_of_bijective_outer P Q.variableCount ψ hψ
      (fun j => KF.partialDeriv j)
      (houter ▸ hQ) hlci (hrigi i)
  choose c hc using key
  have : Module.FinitePresentation base.carrier P.extension.Cotangent := by
    let : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
    let : IsNoetherianRing P.extension.Ring := by
      change IsNoetherianRing P.completedPolynomialRing
      infer_instance
    have hfinite : Module.Finite base.carrier P.extension.Cotangent :=
      Algebra.Extension.Cotangent.finite (Ideal.fg_of_isNoetherianRing _)
    let : IsNoetherianRing base.carrier := Rig.isNoetherianRing base
    exact Module.finitePresentation_of_finite base.carrier P.extension.Cotangent
  refine ⟨continuous_pi hf, hft, I, hI, (isRigSmooth_iff_cotangentFactorization base P).mpr ?_⟩
  unfold HasCotangentFactorization
  refine ⟨Finset.univ.sup c, fun a ha => ?_⟩
  have hsingle : ∀ i (s : ∀ j, A j) (y : A i),
      (Pi.single i (s i * y) : ∀ j, A j) = s * Pi.single i y := by
    intro i s y
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  let β : ∀ i, (total i).carrier →ₗ[base.carrier] base.carrier := fun i ↦
    { toFun := fun x ↦ show base.carrier from Pi.single i (show A i from x)
      map_add' := fun x y => Pi.single_add i (show A i from x) (show A i from y)
      map_smul' := fun s x => hsingle i s x }
  have hβ : ∑ i, β i 1 = 1 := Finset.univ_sum_single (1 : ∀ j, A j)
  refine exists_factor_of_finite_family (A := fun i ↦ (total i).carrier) KB.differential β hβ
    (algebraMap B base.carrier a) fun i => ?_
  obtain ⟨h, hh⟩ := hc i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha)
  refine ⟨h, ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact hh

/-- **Stacks 0GCK.** Rig-smoothness is a local property of arrows of `WAdm^Noeth`: it ascends
along a completed étale localization diagram, descends along one whose target-side horizontal
map is faithfully flat, and is preserved by finite products of targets. -/
@[stacks 0GCK]
public theorem rigSmooth_isLocalNoetherian :
    TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigSmoothArrow φ) :=
  ⟨rigSmooth_localizationPreserves, rigSmooth_faithfullyFlatDescent,
    rigSmooth_finiteProductPreserves⟩

end Rig

end
