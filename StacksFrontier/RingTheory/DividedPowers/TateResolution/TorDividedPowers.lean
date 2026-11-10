module

public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Comparison
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ScalarRestriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateColimitResolution

/-!
# Divided powers on the homology of a base-changed Tate resolution

Let `R` be a commutative ring and let `S` and `T` be commutative `R`-algebras. The Tate
resolution `A` of `S` along the tautological polynomial presentation is a strictly
graded-commutative divided power differential graded `R`-algebra, free over `R` in every degree
and exact in positive degrees. Its base change `T ⊗[R] A` is again a divided power differential
graded algebra, and the homology of `T ⊗[R] A` carries an induced strictly graded-commutative
graded `R`-algebra structure with divided powers, determined on the class of a homogeneous cycle
by `γₙ` of that cycle.

The divided powers on the homology come from Tag 09PK, which needs a surjection onto `T ⊗[R] A`
from a divided power differential graded algebra with no homology in positive degrees. That
algebra is `P ⊗[R] A` for a polynomial algebra `P` surjecting onto `T`: the divided powers on
both base changes are those of Tag 09PL, and the vanishing of the positive homology of
`P ⊗[R] A` is the exactness of a positively exact complex after tensoring with a flat module.

## Main definitions

* `DividedPowers.TateResolution.HasInducedDividedPowers` — the conclusion of Tag 09PK, as a
  predicate on a divided power differential graded algebra.
* `DividedPowers.TateResolution.gradeDifferential` — the differential of a differential graded
  algebra, between two homogeneous pieces.
* `DividedPowers.TateResolution.baseChangeMap` — base change of an algebra along a map of the
  coefficient algebras.
* `DividedPowers.TateResolution.tautologicalPresentation` — the presentation of an algebra by
  the polynomial algebra on its own elements.

## Main results

* `DividedPowers.TateResolution.exact_positive_baseChange` — base change along a flat algebra
  preserves exactness in positive degrees.
* `DividedPowers.TateResolution.baseChangeMap_dpow` — base change of divided powers is
  functorial in the coefficient algebra.
* `DividedPowers.TateResolution.exists_dividedPowerStructure_homology_baseChange` — the induced
  divided power structure on the homology of a base change.
* `DividedPowers.TateResolution.exists_dividedPowerStructure_homology_tateResolution` — the same
  for the Tate resolution of `S` along the tautological presentation.

### Where Tag 09PQ is carried

Tag 09PQ puts the structure on `Tor_*^R(S, T)`, and what is equipped here is the homology of
`T ⊗[R] A`, a different object. The identification of the two, in each degree, is
`DividedPowers.TateResolution.gradeHomologyEquivTor` in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.TorComparison`, and the structure is
transported onto `Tor_*^R(S, T)` itself by
`DividedPowers.TateResolution.exists_dividedPowerStructure_torDirectSum` in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowerAlgebra`, which is what
carries the tag. The results of this file are the input to that transport and carry no tag of
their own.

## Implementation notes

The conclusion of Tag 09PK is given the name `HasInducedDividedPowers` so that it can be
asserted of a concrete algebra; written out inline for a base change it does not elaborate.
In the main theorem the resolution is existentially quantified and pinned by an equation to
`tateResolution`, which names it without changing the statement, since `∃ x, x = a ∧ p x` is
`p a`.

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
* [Stacks Project, Tag 09PL](https://stacks.math.columbia.edu/tag/09PL)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w t

section GradeDifferential

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- The differential of a differential graded algebra, as a map between two homogeneous
pieces. -/
public def gradeDifferential (n : ℕ) : 𝒜 (n + 1) →ₗ[R] 𝒜 n :=
  (d.comp (𝒜 (n + 1)).subtype).codRestrict (𝒜 n)
    fun x ↦ IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) x.2

/-- `gradeDifferential` is `d` on the underlying elements. -/
@[simp]
public theorem coe_gradeDifferential (n : ℕ) (x : 𝒜 (n + 1)) :
    (gradeDifferential 𝒜 d n x : A) = d (x : A) := rfl

/-- Exactness in positive degrees, read as exactness of the maps between homogeneous
pieces. -/
public theorem exact_gradeDifferential
    (hex : ∀ (n : ℕ) (x : A), 0 < n → x ∈ 𝒜 n → d x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ d z = x) (n : ℕ) :
    Function.Exact (gradeDifferential 𝒜 d (n + 1)) (gradeDifferential 𝒜 d n) := by
  refine fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨z, hz, hdz⟩ := hex (n + 1) x (Nat.succ_pos n) x.2 (congrArg Subtype.val hx)
    exact ⟨⟨z, hz⟩, Subtype.ext hdz⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext (IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) (y : A))

end GradeDifferential

section BaseChangeExact

variable {R : Type u} {P : Type v} {A : Type w} [CommRing R] [CommRing P] [Ring A]
  [Algebra R P] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- The base-changed differential commutes with the base change of the inclusion of a
homogeneous piece. -/
public theorem baseChange_gradeDifferential (n : ℕ) (u : P ⊗[R] 𝒜 (n + 1)) :
    LinearMap.baseChange P d ((𝒜 (n + 1)).subtype.baseChange P u) =
      (𝒜 n).subtype.baseChange P ((gradeDifferential 𝒜 d n).baseChange P u) := by
  induction u using TensorProduct.inductionOn with
  | tmul p x => simp
  | add u v hu hv => simp [hu, hv]

/-- **Base change along a flat algebra preserves exactness in positive degrees.** -/
public theorem exact_positive_baseChange [Module.Flat R P]
    (hex : ∀ (n : ℕ) (x : A), 0 < n → x ∈ 𝒜 n → d x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ d z = x)
    (n : ℕ) (x : P ⊗[R] A) (hn : 0 < n) (hx : x ∈ (𝒜 n).baseChange P)
    (hdx : LinearMap.baseChange P d x = 0) :
    ∃ z : P ⊗[R] A, z ∈ (𝒜 (n + 1)).baseChange P ∧ LinearMap.baseChange P d z = x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hn)
  obtain ⟨u, rfl⟩ := hx
  have hinj : Function.Injective ((𝒜 m).subtype.baseChange P) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (𝒜 m).injective_subtype
  have hker : (gradeDifferential 𝒜 d m).baseChange P u = 0 :=
    hinj (by rwa [map_zero, ← baseChange_gradeDifferential 𝒜 d m u])
  have hexact := Module.Flat.lTensor_exact P (exact_gradeDifferential 𝒜 d hex m)
  rw [LinearMap.baseChange_eq_lTensor] at hker
  obtain ⟨w, hw⟩ := (hexact u).1 hker
  have hw' : (gradeDifferential 𝒜 d (m + 1)).baseChange P w = u := by
    rw [LinearMap.baseChange_eq_lTensor]; exact hw
  refine ⟨(𝒜 (m + 2)).subtype.baseChange P w, ⟨w, rfl⟩, ?_⟩
  rw [baseChange_gradeDifferential 𝒜 d (m + 1) w, hw']

end BaseChangeExact

section Restriction

variable {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S] [Ring M]
  [Algebra R M] [Algebra S M] [Module S R] [IsScalarTower S R M]

/-- The differential graded algebra axioms do not depend on the coefficient ring. -/
public theorem isDifferentialGradedAlgebra_restrictGrade (𝒜 : ℕ → Submodule R M)
    [GradedAlgebra 𝒜] (d : M →ₗ[R] M) [IsDifferentialGradedAlgebra 𝒜 d] :
    IsDifferentialGradedAlgebra (restrictGrade S 𝒜) (d.restrictScalars S) where
  d_grade_zero hx := IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) hx
  d_mem hx := IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) hx
  d_sq_zero x := IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) x
  leibniz hx hy := by
    simp only [LinearMap.coe_restrictScalars]
    rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) hx hy]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_pow, map_pow, map_neg, map_neg,
      map_one, map_one]

/-- Compatibility of divided powers with a differential does not depend on the coefficient
ring. -/
public theorem isCompatibleWithDifferential_restrictGrade {𝒜 : ℕ → Submodule R M}
    [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜)
    (d : M →ₗ[R] M) [IsCompatibleWithDifferential γ d] :
    IsCompatibleWithDifferential (γ.restrictScalars S) (d.restrictScalars S) where
  d_dpow hn hx := IsCompatibleWithDifferential.d_dpow (γ := γ) (d := d) hn
    ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)

/-- The differential graded algebra axioms, assembled from the four displayed identities. -/
public theorem isDifferentialGradedAlgebra_of_axioms (𝒜 : ℕ → Submodule R M) [GradedAlgebra 𝒜]
    (d : M →ₗ[R] M) (d_sq : d.comp d = 0) (d_grade_zero : ∀ x : M, x ∈ 𝒜 0 → d x = 0)
    (d_mem : ∀ (n : ℕ) (x : M), x ∈ 𝒜 (n + 1) → d x ∈ 𝒜 n)
    (d_mul : ∀ (i j : ℕ) (x y : M), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y)) :
    IsDifferentialGradedAlgebra 𝒜 d where
  d_grade_zero hx := d_grade_zero _ hx
  d_mem hx := d_mem _ _ hx
  d_sq_zero x := LinearMap.congr_fun d_sq x
  leibniz hx hy := d_mul _ _ _ _ hx hy

end Restriction

section Transfer

variable {R : Type u} {A : Type v} {P : Type w} {T : Type t}
  [CommRing R] [Ring A] [CommRing P] [CommRing T]
  [Algebra R A] [Algebra R P] [Algebra R T]

/-- Base change of an algebra along a map of the coefficient algebras. -/
public def baseChangeMap (ψ : P →ₐ[R] T) : P ⊗[R] A →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map ψ (AlgHom.id R A)

/-- `baseChangeMap ψ` applies `ψ` to the coefficient of a pure tensor. -/
@[simp]
public theorem baseChangeMap_tmul (ψ : P →ₐ[R] T) (p : P) (a : A) :
    baseChangeMap ψ (p ⊗ₜ[R] a) = ψ p ⊗ₜ[R] a := rfl

/-- A surjection of coefficient algebras base changes to a surjection. -/
public theorem surjective_baseChangeMap (ψ : P →ₐ[R] T) (hψ : Function.Surjective ψ) :
    Function.Surjective (baseChangeMap (A := A) ψ) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul t a =>
      obtain ⟨p, rfl⟩ := hψ t
      exact ⟨p ⊗ₜ[R] a, rfl⟩
  | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩

/-- The base change of an algebra map is semilinear for the coefficient map. -/
public theorem baseChangeMap_smul (ψ : P →ₐ[R] T) (p : P) (x : P ⊗[R] A) :
    baseChangeMap ψ (p • x) = ψ p • baseChangeMap ψ x := by
  induction x using TensorProduct.inductionOn with
  | tmul q a => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- Base change of an algebra map takes a base-changed submodule into the corresponding
base-changed submodule. -/
public theorem baseChangeMap_mem_baseChange (ψ : P →ₐ[R] T) (p : Submodule R A)
    {x : P ⊗[R] A} (hx : x ∈ p.baseChange P) :
    baseChangeMap ψ x ∈ p.baseChange T := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using Submodule.tmul_mem_baseChange_of_mem (1 : T) ha
  | zero => simp
  | add x y _ _ ihx ihy => simpa [map_add] using Submodule.add_mem _ ihx ihy
  | smul q x _ ih =>
      rw [baseChangeMap_smul]
      exact Submodule.smul_mem _ _ ih

/-- Base change of an algebra map commutes with the base-changed differential. -/
public theorem baseChangeMap_baseChange (ψ : P →ₐ[R] T) (d : A →ₗ[R] A) (x : P ⊗[R] A) :
    baseChangeMap ψ (LinearMap.baseChange P d x) =
      LinearMap.baseChange T d (baseChangeMap ψ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p a => simp
  | add x y hx hy => simp [map_add, hx, hy]

/-- Base change commutes with suprema of submodules. -/
public theorem baseChange_iSup (p : ℕ → Submodule R A) :
    (⨆ i, p i).baseChange P = ⨆ i, (p i).baseChange P := by
  have h (i : ℕ) : (p i).baseChange P =
      Submodule.span P (TensorProduct.mk R P A 1 '' (p i : Set A)) := by
    rw [Submodule.baseChange_eq_span, Submodule.map_coe]
  calc
    (⨆ i, p i).baseChange P =
        Submodule.span P (TensorProduct.mk R P A 1 '' ⋃ i, (p i : Set A)) := by
          rw [Submodule.iSup_eq_span, Submodule.baseChange_span]
    _ = ⨆ i, Submodule.span P (TensorProduct.mk R P A 1 '' (p i : Set A)) := by
          rw [Set.image_iUnion, Submodule.span_iUnion]
    _ = ⨆ i, (p i).baseChange P := by simp only [← h]

/-- The positive even part of a base change is the base change of the positive even part. -/
public theorem positiveEvenPart_baseChange_eq (𝒜 : ℕ → Submodule R A) :
    positiveEvenPart (fun i ↦ (𝒜 i).baseChange P) = (positiveEvenPart 𝒜).baseChange P :=
  (baseChange_iSup (P := P) fun d ↦ 𝒜 (2 * (d + 1))).symm

/-- Scalar multiplication on a base change is multiplication by a coefficient. -/
public theorem smul_eq_tmul_one_mul (p : P) (x : P ⊗[R] A) :
    p • x = (p ⊗ₜ[R] (1 : A)) * x := by
  induction x using TensorProduct.inductionOn with
  | tmul q a => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp [mul_add, hx, hy]

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

omit [IsStrictlyGradedComm 𝒜] in
/-- A coefficient times the identity lies in the even part of a base change. -/
public theorem tmul_one_mem_evenPart_baseChange (p : P) :
    p ⊗ₜ[R] (1 : A) ∈ evenPart (fun i ↦ (𝒜 i).baseChange P) := by
  refine Submodule.mem_iSup_of_mem 0 ?_
  simpa using Submodule.tmul_mem_baseChange_of_mem (R := R) (A := P) (p := 𝒜 0) p
    SetLike.GradedOne.one_mem

/-- A coefficient scales the divided powers of a positive even element by its own power. -/
private theorem dpow_smul_baseChange (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm fun i ↦ (𝒜 i).baseChange P]
    (γ : DividedPowerStructure fun i ↦ (𝒜 i).baseChange P) (q : P) {m : ℕ} (hm : m ≠ 0)
    {z : P ⊗[R] A} (hz : z ∈ positiveEvenPart fun i ↦ (𝒜 i).baseChange P) :
    γ.dpow m (q • z) = (q ⊗ₜ[R] (1 : A)) ^ m * γ.dpow m z := by
  rw [smul_eq_tmul_one_mul q z, γ.dpow_mul_even hm (tmul_one_mem_evenPart_baseChange 𝒜 q) hz]

/-- **Base change of divided powers is functorial in the coefficient algebra.** The base change
of an algebra map along a map of coefficients preserves every divided power, once both base
changes are normalized by their values on `1 ⊗ x`. -/
public theorem baseChangeMap_dpow (γ : DividedPowerStructure 𝒜) (ψ : P →ₐ[R] T)
    [IsStrictlyGradedComm fun i ↦ (𝒜 i).baseChange P]
    [IsStrictlyGradedComm fun i ↦ (𝒜 i).baseChange T]
    (γP : DividedPowerStructure fun i ↦ (𝒜 i).baseChange P)
    (γT : DividedPowerStructure fun i ↦ (𝒜 i).baseChange T)
    (hP : ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
      γP.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x)
    (hT : ∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
      γT.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x)
    (n : ℕ) {z : P ⊗[R] A} (hz : z ∈ positiveEvenPart fun i ↦ (𝒜 i).baseChange P) :
    baseChangeMap ψ (γP.dpow n z) = γT.dpow n (baseChangeMap ψ z) := by
  have key : ∀ z ∈ Submodule.span P ((positiveEvenPart 𝒜).map (TensorProduct.mk R P A 1)),
      ∀ m : ℕ, baseChangeMap ψ (γP.dpow m z) = γT.dpow m (baseChangeMap ψ z) := by
    intro z hz
    have hmem : ∀ w ∈ Submodule.span P ((positiveEvenPart 𝒜).map (TensorProduct.mk R P A 1)),
        w ∈ positiveEvenPart fun i ↦ (𝒜 i).baseChange P := by
      intro w hw
      rwa [positiveEvenPart_baseChange_eq, Submodule.baseChange_eq_span]
    have hmemT : ∀ w ∈ Submodule.span P ((positiveEvenPart 𝒜).map (TensorProduct.mk R P A 1)),
        baseChangeMap ψ w ∈ positiveEvenPart fun i ↦ (𝒜 i).baseChange T := by
      intro w hw
      rw [positiveEvenPart_baseChange_eq]
      exact baseChangeMap_mem_baseChange ψ _ (by rwa [Submodule.baseChange_eq_span])
    have h0 : ∀ w ∈ Submodule.span P ((positiveEvenPart 𝒜).map (TensorProduct.mk R P A 1)),
        baseChangeMap ψ (γP.dpow 0 w) = γT.dpow 0 (baseChangeMap ψ w) := fun w hw => by
      rw [γP.dpow_zero (hmem w hw), map_one, γT.dpow_zero (hmemT w hw)]
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, ha, rfl⟩ := hz
        intro m
        simp only [TensorProduct.mk_apply, hP m a ha, baseChangeMap_tmul, map_one]
        rw [hT m a ha]
    | zero =>
        intro m
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact h0 0 (Submodule.zero_mem _)
        · rw [DividedPowerStructure.dpow_eval_zero _ γP hm.ne']
          simp only [map_zero]
          rw [DividedPowerStructure.dpow_eval_zero _ γT hm.ne']
    | add z w hz hw ihz ihw =>
        intro m
        rw [γP.dpow_add (hmem z hz) (hmem w hw), map_add,
          γT.dpow_add (hmemT z hz) (hmemT w hw), map_sum]
        exact Finset.sum_congr rfl fun ij _ => by rw [map_mul, ihz ij.1, ihw ij.2]
    | smul q z hz ih =>
        intro m
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact h0 _ (Submodule.smul_mem _ _ hz)
        · rw [baseChangeMap_smul, dpow_smul_baseChange 𝒜 γP q hm.ne' (hmem z hz),
            dpow_smul_baseChange 𝒜 γT (ψ q) hm.ne' (hmemT z hz), map_mul, map_pow,
            baseChangeMap_tmul, ih m]
  rw [positiveEvenPart_baseChange_eq, Submodule.baseChange_eq_span] at hz
  exact key z hz n

end Transfer

section InducedStructure

variable {R : Type u} {B : Type v} [CommRing R] [Ring B] [Algebra R B]

/-- The homology of `B` carries an induced strictly graded-commutative graded `R`-algebra
structure with divided powers: a ring and `R`-algebra structure whose class map is additive,
`R`-linear, unital and multiplicative, a grading whose degree-`n` piece is spanned by the
classes of the cycles of degree `n`, strict graded commutativity, and divided powers sending
the class of a positive even cycle `x` to the class of `γₙ x`. -/
public def HasInducedDividedPowers (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    [IsStrictlyGradedComm ℬ] (dB : B →ₗ[R] B) [IsDifferentialGradedAlgebra ℬ dB]
    (γB : DividedPowerStructure ℬ) : Prop :=
  ∃ hRing : Ring (Homology (𝒜 := ℬ) dB),
    letI : Ring (Homology (𝒜 := ℬ) dB) := hRing
    ∃ hAlgebra : Algebra R (Homology (𝒜 := ℬ) dB),
      letI : Algebra R (Homology (𝒜 := ℬ) dB) := hAlgebra
      letI : AddCommMonoid (Homology (𝒜 := ℬ) dB) := hRing.toAddCommMonoid
      letI : Module R (Homology (𝒜 := ℬ) dB) := Algebra.toModule
      let ℋ : ℕ → Submodule R (Homology (𝒜 := ℬ) dB) := fun n =>
        Submodule.span R {z | ∃ x : cycles dB, (x : B) ∈ ℬ n ∧
          (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB) = z}
      ∃ hGraded : GradedAlgebra ℋ,
        letI : GradedAlgebra ℋ := hGraded
        ∃ hStrict : IsStrictlyGradedComm ℋ,
          letI : IsStrictlyGradedComm ℋ := hStrict
          ∃ γH : @DividedPowerStructure R (Homology (𝒜 := ℬ) dB)
              _ hRing hAlgebra ℋ hGraded hStrict,
            (Submodule.Quotient.mk (0 : cycles dB) :
              Homology (𝒜 := ℬ) dB) = 0 ∧
            (∀ x y : cycles dB,
              (Submodule.Quotient.mk (x + y) : Homology (𝒜 := ℬ) dB) =
                Submodule.Quotient.mk x + Submodule.Quotient.mk y) ∧
            (∀ (r : R) (x : cycles dB),
              (Submodule.Quotient.mk (r • x) : Homology (𝒜 := ℬ) dB) =
                r • (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB)) ∧
            (∃ h1 : dB (1 : B) = 0,
              (Submodule.Quotient.mk (⟨1, h1⟩ : cycles dB) :
                Homology (𝒜 := ℬ) dB) = 1) ∧
            (∀ {x y : B} (hx : dB x = 0) (hy : dB y = 0),
              ∃ hxy : dB (x * y) = 0,
                (Submodule.Quotient.mk (⟨x * y, hxy⟩ : cycles dB) :
                  Homology (𝒜 := ℬ) dB) =
                  Submodule.Quotient.mk (⟨x, hx⟩ : cycles dB) *
                    Submodule.Quotient.mk (⟨y, hy⟩ : cycles dB)) ∧
            (∀ {n : ℕ} {x : B} (_hx : x ∈ positiveEvenPart ℬ)
                (hd : dB x = 0),
              ∃ hγ : dB (γB.dpow n x) = 0,
                γH.dpow n (Submodule.Quotient.mk (⟨x, hd⟩ : cycles dB)) =
                  Submodule.Quotient.mk (⟨γB.dpow n x, hγ⟩ : cycles dB))

/-- Tag 09PK, in the form of `HasInducedDividedPowers`. -/
public theorem hasInducedDividedPowers_of_surjective {A : Type w}
    [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_d : ∀ x : A, f (dA x) = dB (f x))
    (hf_dpow : ∀ {n : ℕ} {x : A}, x ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n x) = γB.dpow n (f x))
    (hf_surjective : Function.Surjective f)
    (hA : ∀ {n : ℕ}, 0 < n → ∀ {x : A}, x ∈ 𝒜 n → dA x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ dA z = x) :
    HasInducedDividedPowers ℬ dB γB :=
  dividedPowerStructureOnHomology_of_surjective 𝒜 ℬ dA dB γA γB f hf_grade hf_d
    hf_dpow hf_surjective hA

end InducedStructure

section HomologyBaseChange

variable {R : Type u} {A : Type v} {P : Type w} {T : Type t}
  [CommRing R] [Ring A] [CommRing P] [CommRing T]
  [Algebra R A] [Algebra R P] [Algebra R T]

/-- **Divided powers on the homology of a base change.** If `A` is a strictly graded-commutative
divided power differential graded `R`-algebra exact in positive degrees and `ψ : P → T` is a
surjection of commutative `R`-algebras with `P` flat over `R`, then `T ⊗[R] A` is again such an
algebra and its homology carries the induced divided power structure. -/
public theorem exists_dividedPowerStructure_homology_baseChange
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d] [IsCompatibleWithDifferential γ d]
    (hex : ∀ (n : ℕ) (x : A), 0 < n → x ∈ 𝒜 n → d x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ d z = x)
    (ψ : P →ₐ[R] T) (hψ : Function.Surjective ψ) [Module.Flat R P] :
    let ℬ : ℕ → Submodule R (T ⊗[R] A) := restrictGrade R fun i ↦ (𝒜 i).baseChange T
    let dB : T ⊗[R] A →ₗ[R] T ⊗[R] A := (LinearMap.baseChange T d).restrictScalars R
    ∃ hStrict : IsStrictlyGradedComm ℬ,
      letI : IsStrictlyGradedComm ℬ := hStrict
      ∃ hDGA : IsDifferentialGradedAlgebra ℬ dB,
        letI : IsDifferentialGradedAlgebra ℬ dB := hDGA
        ∃ γB : DividedPowerStructure ℬ,
          IsCompatibleWithDifferential γB dB ∧
          (∀ (n : ℕ) (x : A), x ∈ positiveEvenPart 𝒜 →
            γB.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] γ.dpow n x) ∧
          HasInducedDividedPowers ℬ dB γB := by
  intro ℬ dB
  have hdsq : d.comp d = 0 := by
    ext x
    exact IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) x
  have hd0 : ∀ x : A, x ∈ 𝒜 0 → d x = 0 := fun _ hx =>
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) hx
  have hdm : ∀ (n : ℕ) (x : A), x ∈ 𝒜 (n + 1) → d x ∈ 𝒜 n := fun _ _ hx =>
    IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) hx
  have hdmul : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y) := fun _ _ _ _ hx hy =>
    IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) hx hy
  obtain ⟨hcommP, γP, hPsq, hP0, hPm, hPmul, hPcompat, hPdpow⟩ :=
    exists_dividedPowerStructure_baseChange (R' := P) 𝒜 γ d hdsq hd0 hdm hdmul
  obtain ⟨hcommT, γT, hTsq, hT0, hTm, hTmul, hTcompat, hTdpow⟩ :=
    exists_dividedPowerStructure_baseChange (R' := T) 𝒜 γ d hdsq hd0 hdm hdmul
  let : IsStrictlyGradedComm fun i ↦ (𝒜 i).baseChange P := hcommP
  let : IsStrictlyGradedComm fun i ↦ (𝒜 i).baseChange T := hcommT
  let : IsDifferentialGradedAlgebra (fun i ↦ (𝒜 i).baseChange P)
      (LinearMap.baseChange P d) :=
    isDifferentialGradedAlgebra_of_axioms _ _ hPsq hP0 hPm hPmul
  let : IsDifferentialGradedAlgebra (fun i ↦ (𝒜 i).baseChange T)
      (LinearMap.baseChange T d) :=
    isDifferentialGradedAlgebra_of_axioms _ _ hTsq hT0 hTm hTmul
  let : IsCompatibleWithDifferential γP (LinearMap.baseChange P d) := hPcompat
  let : IsCompatibleWithDifferential γT (LinearMap.baseChange T d) := hTcompat
  let : IsDifferentialGradedAlgebra
      (restrictGrade R fun i ↦ (𝒜 i).baseChange P)
      ((LinearMap.baseChange P d).restrictScalars R) :=
    isDifferentialGradedAlgebra_restrictGrade (S := R)
      (fun i ↦ (𝒜 i).baseChange P) (LinearMap.baseChange P d)
  let : IsCompatibleWithDifferential (γP.restrictScalars R)
      ((LinearMap.baseChange P d).restrictScalars R) :=
    isCompatibleWithDifferential_restrictGrade (S := R) γP (LinearMap.baseChange P d)
  let hdgaB : IsDifferentialGradedAlgebra ℬ dB :=
    isDifferentialGradedAlgebra_restrictGrade (S := R)
      (fun i ↦ (𝒜 i).baseChange T) (LinearMap.baseChange T d)
  have hcompB : IsCompatibleWithDifferential (γT.restrictScalars R)
      ((LinearMap.baseChange T d).restrictScalars R) :=
    isCompatibleWithDifferential_restrictGrade (S := R) γT (LinearMap.baseChange T d)
  exact ⟨inferInstance, hdgaB, γT.restrictScalars R, hcompB, hTdpow,
    hasInducedDividedPowers_of_surjective
      (restrictGrade R fun i ↦ (𝒜 i).baseChange P) ℬ
      ((LinearMap.baseChange P d).restrictScalars R) dB
      (γP.restrictScalars R) (γT.restrictScalars R) (baseChangeMap ψ)
      (fun {n} {x} hx => baseChangeMap_mem_baseChange ψ (𝒜 n) hx)
      (baseChangeMap_baseChange ψ d)
      (fun {n} {x} hx => baseChangeMap_dpow 𝒜 γ ψ γP γT hPdpow hTdpow n
        ((mem_positiveEvenPart_restrictGrade R _ x).1 hx))
      (surjective_baseChangeMap ψ hψ)
      (fun {n} hn {x} hx hdx => exact_positive_baseChange 𝒜 d hex n x hn hx hdx)⟩

end HomologyBaseChange

section TorAlgebra

/-- The tautological presentation of an algebra by the polynomial algebra on its own
elements. -/
public noncomputable def tautologicalPresentation (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] : MvPolynomial S R →ₐ[R] S :=
  MvPolynomial.aeval id

/-- The tautological presentation is surjective. -/
public theorem surjective_tautologicalPresentation (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] :
    Function.Surjective (tautologicalPresentation R S) := fun s =>
  ⟨MvPolynomial.X s, by simp [tautologicalPresentation]⟩

/-- **Divided powers on the homology of `T ⊗[R] A` for the Tate resolution `A` of `S`.** For
commutative `R`-algebras `S` and `T`, the homology of the base change `T ⊗[R] A` of the Tate
resolution of `S` along the tautological presentation carries a strictly graded-commutative
graded `R`-algebra structure with divided powers, induced by those of `A`. -/
public theorem exists_dividedPowerStructure_homology_tateResolution
    (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    ∃ Res : Resolution R S S (tautologicalPresentation R S),
      Res = tateResolution (tautologicalPresentation R S)
          (surjective_tautologicalPresentation R S) ∧
      (letI : Ring Res.A := Res.ring
       letI : Algebra R Res.A := Res.algebra
       letI : GradedAlgebra Res.grade := Res.graded
       letI : IsStrictlyGradedComm Res.grade := Res.strict
       letI : IsDifferentialGradedAlgebra Res.grade Res.differential := Res.dga
       letI : IsCompatibleWithDifferential Res.gamma Res.differential := Res.compatible
       let ℬ : ℕ → Submodule R (T ⊗[R] Res.A) :=
         restrictGrade R fun i ↦ (Res.grade i).baseChange T
       let dB : T ⊗[R] Res.A →ₗ[R] T ⊗[R] Res.A :=
         (LinearMap.baseChange T Res.differential).restrictScalars R
       ∃ hStrict : IsStrictlyGradedComm ℬ,
         letI : IsStrictlyGradedComm ℬ := hStrict
         ∃ hDGA : IsDifferentialGradedAlgebra ℬ dB,
           letI : IsDifferentialGradedAlgebra ℬ dB := hDGA
           ∃ γB : DividedPowerStructure ℬ,
             IsCompatibleWithDifferential γB dB ∧
             (∀ (n : ℕ) (x : Res.A), x ∈ positiveEvenPart Res.grade →
               γB.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] Res.gamma.dpow n x) ∧
             HasInducedDividedPowers ℬ dB γB) := by
  set Res := tateResolution (tautologicalPresentation R S)
    (surjective_tautologicalPresentation R S)
  refine ⟨Res, rfl, ?_⟩
  let : Ring Res.A := Res.ring
  let : Algebra R Res.A := Res.algebra
  let : GradedAlgebra Res.grade := Res.graded
  let : IsStrictlyGradedComm Res.grade := Res.strict
  let : IsDifferentialGradedAlgebra Res.grade Res.differential := Res.dga
  let : IsCompatibleWithDifferential Res.gamma Res.differential := Res.compatible
  exact exists_dividedPowerStructure_homology_baseChange (P := MvPolynomial T R)
    Res.grade Res.gamma Res.differential Res.exact_positive
    (tautologicalPresentation R T) (surjective_tautologicalPresentation R T)

end TorAlgebra

end DividedPowers.TateResolution

end
