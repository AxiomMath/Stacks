module

public import StacksFrontier.RingTheory.Rig.JacobianCramerCriterion
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReductionIdentification
public import StacksFrontier.RingTheory.Rig.RigEtaleLifting

/-!
# The seven Artin criteria for rig-étaleness: Stacks 0AJU

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`, so
that `NL^∧_{B/A} = (J / J² --d--> ⨁ i, B dxᵢ)`.  Stacks 0AJU lists seven conditions and asserts
that they are equivalent:

1. `B` is rig-étale over `(A, I)`;
2. some `Iᶜ` annihilates the identity of `NL^∧_{B/A}` in `D(B)`;
3. some `IᶜB` annihilates `H⁻¹(NL^∧_{B/A}) = ker d` and `H⁰(NL^∧_{B/A}) = coker d`;
4. some `IᶜB` annihilates `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0` and every `n ≥ 1`;
5. for every `a ∈ I` there is a `c` with `a ^ c` killing `H⁰(NL^∧_{B/A})` and with
   `f₁, …, f_r ∈ J` satisfying `a ^ c · J ⊆ (f₁, …, f_r) + J²`;
6. the same, with the annihilation of `H⁰` replaced by the divisibility of `a ^ c` by the
   Jacobian determinant `det(∂fⱼ/∂xᵢ)`;
7. for generators `f₁, …, f_t` of `J` the Jacobian ideal and the Cramer ideal each contain a
   power of `IB`.

Six of the implications are already in the library; this file supplies the two that were
missing and assembles the equivalence.

The two new steps are elementary determinant arithmetic.  Write `M = (∂fⱼ/∂xᵢ)` for the square
Jacobian matrix of the family `f₁, …, f_r` of (5) and (6); its columns are the images
`d[fⱼ]` of the conormal classes, so every vector in the image of `M` lies in the image of `d`.

* **(6) ⇒ (5).**  `M · adj(M) = det(M) · 1` exhibits `det(M) · eᵢ` as a vector in the image of
  `M`, hence in the image of `d`; as `det(M) ∣ a ^ c`, the scalar `a ^ c` carries all of
  `⨁ i, B dxᵢ` into the image of `d`, which is annihilation of `H⁰`.  The second halves of (5)
  and (6) are the same sentence, so the exponent and the family are unchanged.
* **(5) ⇒ (3).**  Condition (5) says `a ^ c` carries `⨁ i, B dxᵢ` into the image of `d` and
  (through `Algebra.Extension.cotangentMk_smul_mem_span`) that it carries `J / J²` into the
  span of the `[fⱼ]`.  Composing, `a ^ {2c}` carries `⨁ i, B dxᵢ` into the image of `M`, so
  there is a matrix `N` with `M · N = a ^ {2c} · 1` and therefore `det(M) ∣ a ^ {2cr}`.  Now
  `adj(M) · M = det(M) · 1` runs the argument backwards: an element `x` of `ker d` has
  `a ^ c · x = ∑ vⱼ [fⱼ]` with `M · v = 0`, hence `det(M) · v = 0`, hence `a ^ {2cr} · v = 0`,
  hence `a ^ {2cr + c} · x = 0`.  So every `a ∈ I` has a power annihilating both cohomology
  modules; `B` being Noetherian, the ideal they generate contains a power of `IB`.

## Main results

* `Rig.isArtinPreliminary_of_isArtinJacobian`: **Stacks 0AJU, (6) ⇒ (5)**.
* `Rig.isCohomologyAnnihilated_of_isArtinPreliminary`: **Stacks 0AJU, (5) ⇒ (3)**, which closes
  the cycle `(1) ⇒ (6) ⇒ (5) ⇒ (3) ⇒ (1)`.
* `Rig.isRigEtale_iff_isJacobianCramerBounded`: **Stacks 0AJU, (1) ⇔ (7)**, condition (7) being
  read as a statement about *every* finite generating family of `J`.
* `Rig.tfae_isRigEtale`: **Stacks 0AJU**, the seven conditions.

## Implementation notes

Conditions (2), (3), (4), (5), (6) and (7) are given names (`Rig.IsDerivedAnnihilated`, …) so
that the `List.TFAE` statement is readable; they are abbreviations, so each unfolds to the
proposition the contributing theorem already states and no transport is needed.

Condition (7) of the source fixes one generating family of `J`.  Here it quantifies over all
of them, which is the stronger reading and therefore the honest one for an equivalence: the
implication from (7) to (1) only needs one family, and `J` has a finite one because
`A⟨x₁, …, x_r⟩` is Noetherian.  The underlying single-family equivalence is Stacks 0AJY,
`Rig.isRigEtale_iff_exists_pow_le_completedJacobianIdeal_and_completedCramerIdeal`.

Condition (4) is presentation-free and so takes no presentation argument, matching
`Rig.isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated`.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AJY](https://stacks.math.columbia.edu/tag/0AJY)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Algebra.Extension

/-- **A relation modulo `J²` read in the conormal module.**  If `β · g` lies in
`(f₁, …, f_t) + J²` for elements `fⱼ` of `J`, then the class of `β · g` in `J / J²` — that is,
the image of `β` acting on `[g]` — lies in the `S`-span of the classes `[fⱼ]`.

This is the converse reading of `Algebra.Extension.sub_sum_mul_mem_ker_sq`, and is what turns
the second halves of conditions (5) and (6) of Stacks 0AJU into a statement about `J / J²`. -/
public theorem cotangentMk_smul_mem_span {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) {ι : Type*} [Fintype ι] (f : ι → P.ker) (β : P.Ring)
    (g : P.ker)
    (h : β * (g : P.Ring) ∈ Ideal.span (Set.range fun i => (f i : P.Ring)) + P.ker ^ 2) :
    algebraMap P.Ring S β • Cotangent.mk g ∈
      Submodule.span S (Set.range fun i => Cotangent.mk (f i)) := by
  rw [Submodule.add_eq_sup] at h
  obtain ⟨s, hs, q, hq, hsq⟩ := Submodule.mem_sup.mp h
  have hsmem : s ∈ P.ker :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (f i).2) hs
  have hqmem : q ∈ P.ker := Ideal.pow_le_self two_ne_zero hq
  have hsplit : β • g = (⟨s, hsmem⟩ : P.ker) + ⟨q, hqmem⟩ :=
    Subtype.ext (by simpa [smul_eq_mul] using hsq.symm)
  have hzero : Cotangent.mk (⟨q, hqmem⟩ : P.ker) = 0 := (Cotangent.mk_eq_zero_iff _).mpr hq
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun P.Ring).mp hs
  have hsum : (⟨s, hsmem⟩ : P.ker) = ∑ i, c i • f i := Subtype.ext (by simpa using hc.symm)
  rw [← Cotangent.mk_smul_algebraMap, hsplit, map_add, hzero, add_zero, hsum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Cotangent.mk_smul_algebraMap]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Algebra.Extension

namespace Rig

attribute [local instance] HasDerivedCategory.standard

/-- A scalar annihilates a quotient module exactly when it carries the whole module into the
submodule quotiented out. -/
public theorem mem_annihilator_quotient_iff {R : Type*} [CommRing R] {N : Type*}
    [AddCommGroup N] [Module R N] (p : Submodule R N) (b : R) :
    b ∈ Module.annihilator R (N ⧸ p) ↔ ∀ y : N, b • y ∈ p := by
  constructor
  · intro h y
    have hy := Module.mem_annihilator.mp h (Submodule.mkQ p y)
    rwa [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ] at hy
  · intro h
    refine Module.mem_annihilator.mpr fun z => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective p z
    rw [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact h y

/-- `M *ᵥ w` is the combination of the columns of `M` with coefficients `w`. -/
public theorem mulVec_eq_sum_smul_col {R : Type*} [CommRing R] {m n : Type*} [Fintype n]
    (M : Matrix m n R) (w : n → R) :
    M.mulVec w = ∑ j, w j • fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **A matrix whose columns are images of `d` factors through `d`.**  If `d (eⱼ)` is the
`j`-th column of `M`, then `M *ᵥ w` is the image under `d` of the combination of the `eⱼ` with
coefficients `w`.  This is the only way the Jacobian matrix enters the arguments of
Stacks 0AJU, and stating it for an abstract `d` keeps the conormal module out of the matrix
manipulations. -/
public theorem mulVec_eq_apply_sum_smul {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] {m t : ℕ} (d : N →ₗ[R] (Fin m → R)) (M : Matrix (Fin m) (Fin t) R)
    (e : Fin t → N) (hcol : ∀ j, d (e j) = fun i => M i j) (w : Fin t → R) :
    M.mulVec w = d (∑ j, w j • e j) := by
  rw [mulVec_eq_sum_smul_col, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hcol j]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-! ## The seven conditions -/

/-- Condition (2) of Stacks 0AJU: a power of `I` acts by zero on `NL^∧_{B/A}` in `D(B)`. -/
public abbrev IsDerivedAnnihilated (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∃ c : ℕ, ∀ a : A, a ∈ I ^ c →
    (algebraMap A B.carrier a) •
      𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
        (completedNaiveCotangentComplex B P).cochainComplex) = 0

/-- Condition (3) of Stacks 0AJU: one power of `IB` kills both cohomology modules of
`NL^∧_{B/A}`. -/
public abbrev IsCohomologyAnnihilated (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∃ c : ℕ,
    (I ^ c).map (algebraMap A B.carrier) ≤
      Module.annihilator B.carrier
        (LinearMap.ker (completedNaiveCotangentComplex B P).differential) ∧
    (I ^ c).map (algebraMap A B.carrier) ≤
      Module.annihilator B.carrier
        ((Fin P.variableCount → B.carrier) ⧸
          LinearMap.range (completedNaiveCotangentComplex B P).differential)

/-- Condition (4) of Stacks 0AJU: one power of `I` kills, at every finite level `n ≥ 1`, both
homology modules of `NL_{Bₙ/Aₙ}` with `Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`. -/
public abbrev IsReductionCohomologyAnnihilated (B : AdicFiniteTypeAlgebra.{u, v} A I) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∀ a : A, a ∈ I ^ c →
      ((Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
              (algebraMap A B.carrier a)) ∈
            Module.annihilator (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
                (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))).homology 1) ∧
          (Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
              (algebraMap A B.carrier a)) ∈
            Module.annihilator (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))
              ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
                (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))).homology 0))

/-- Condition (5) of Stacks 0AJU: for every `a ∈ I` some `a ^ c` annihilates
`H⁰(NL^∧_{B/A})` and there are `f₁, …, f_r ∈ J` with `a ^ c · J ⊆ (f₁, …, f_r) + J²`. -/
public abbrev IsArtinPreliminary (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∀ a : A, a ∈ I →
    ∃ c : ℕ,
      (algebraMap A B.carrier a) ^ c ∈
        Module.annihilator B.carrier
          ((Fin P.variableCount → B.carrier) ⧸
            LinearMap.range (completedNaiveCotangentComplex B P).differential) ∧
      ∃ f : Fin P.variableCount → P.ker,
        ∀ g : P.ker,
          algebraMap A P.completedPolynomialRing (a ^ c) * (g : P.completedPolynomialRing) ∈
            Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2

/-- Condition (6) of Stacks 0AJU: for every `a ∈ I` there are `f₁, …, f_r ∈ J` whose Jacobian
determinant divides `a ^ c` and with `a ^ c · J ⊆ (f₁, …, f_r) + J²`. -/
public abbrev IsArtinJacobian (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∀ a : A, a ∈ I →
    ∃ (c : ℕ) (f : Fin P.variableCount → P.ker),
      Matrix.det (fun i j : Fin P.variableCount =>
        P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv i
          (f j : P.completedPolynomialRing))) ∣ (algebraMap A B.carrier a) ^ c ∧
      ∀ g : P.ker,
        algebraMap A P.completedPolynomialRing (a ^ c) * (g : P.completedPolynomialRing) ∈
          Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2

/-- Condition (7) of Stacks 0AJU: for every finite generating family of `J` the Jacobian ideal
and the Cramer ideal each contain a power of `IB`. -/
public abbrev IsJacobianCramerBounded (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∀ (t : ℕ) (f : Fin t → P.completedPolynomialRing), P.ker = Ideal.span (Set.range f) →
    ((∃ c : ℕ, (I ^ c).map (algebraMap A B.carrier) ≤ completedJacobianIdeal B P f) ∧
      ∃ c : ℕ, (I ^ c).map (algebraMap A B.carrier) ≤ completedCramerIdeal B P)

/-! ## The missing implications -/

section Missing

variable {B : AdicFiniteTypeAlgebra.{u, v} A I} {P : CompletedPolynomialPresentation I B}

/-- **Stacks 0AJU, (6) ⇒ (5).**  If the Jacobian determinant of `f₁, …, f_r ∈ J` divides
`a ^ c`, then `a ^ c` annihilates `H⁰(NL^∧_{B/A})`.

Cramer's rule `M · adj(M) = det(M) · 1` puts `det(M) · eᵢ` in the image of the Jacobian matrix,
whose columns are images of the differential; so `det(M)`, and with it every multiple of it,
carries `⨁ i, B dxᵢ` into the image of the differential.  The second half of the two
conditions is literally the same sentence, so the exponent and the family carry over. -/
@[stacks 0AJU "(6) implies (5)"]
public theorem isArtinPreliminary_of_isArtinJacobian (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (h : IsArtinJacobian B P) :
    IsArtinPreliminary B P := by
  classical
  intro a ha
  obtain ⟨c, f, hdet, hrel⟩ := h a ha
  refine ⟨c, ?_, f, hrel⟩
  set M : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier :=
    fun i j => P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv i
      (f j : P.completedPolynomialRing)) with hM
  have hcol : ∀ j, (completedNaiveCotangentComplex B P).differential
      (Algebra.Extension.Cotangent.mk (f j)) = fun i => M i j := fun j =>
    (completedNaiveCotangentComplex B P).differential_mk (f j)
  have hdetsmul : ∀ z : Fin P.variableCount → B.carrier,
      M.det • z ∈ LinearMap.range (completedNaiveCotangentComplex B P).differential := by
    intro z
    have hz : M.det • z = M.mulVec (M.adjugate.mulVec z) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hz, mulVec_eq_apply_sum_smul _ M _ hcol]
    exact LinearMap.mem_range_self _ _
  obtain ⟨e, he⟩ := hdet
  rw [mem_annihilator_quotient_iff]
  intro y
  rw [he, mul_smul]
  exact hdetsmul _

/-- **Condition (5) of Stacks 0AJU for a single element annihilates `H⁻¹`.**  Suppose `a ^ c`
annihilates `H⁰(NL^∧_{B/A})` and `f₁, …, f_r ∈ J` satisfy `a ^ c · J ⊆ (f₁, …, f_r) + J²`.
Then `a ^ {2cr + c}` annihilates `H⁻¹(NL^∧_{B/A}) = ker d`.

Write `M` for the Jacobian matrix of the family; its columns are the images `d[fⱼ]`.  The
hypotheses say that `a ^ c` carries `⨁ i, B dxᵢ` into the image of `d` and `J / J²` into the
span of the classes `[fⱼ]`; composing, `a ^ {2c}` carries `⨁ i, B dxᵢ` into the image of `M`,
so collecting the preimages of the standard basis into a matrix `N` gives
`M · N = a ^ {2c} · 1` and hence `det(M) ∣ a ^ {2cr}`.  Now for `x ∈ ker d` write
`a ^ c · x = ∑ vⱼ [fⱼ]`; applying `d` gives `M · v = 0`, so `adj(M) · M = det(M) · 1` gives
`det(M) · v = 0`, hence `a ^ {2cr} · v = 0` and `a ^ {2cr + c} · x = 0`. -/
public theorem pow_mem_annihilator_ker_differential_of_artinPreliminary
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (a : A) (c : ℕ)
    (hcoker : (algebraMap A B.carrier a) ^ c ∈
      Module.annihilator B.carrier
        ((Fin P.variableCount → B.carrier) ⧸
          LinearMap.range (completedNaiveCotangentComplex B P).differential))
    (f : Fin P.variableCount → P.ker)
    (hrel : ∀ g : P.ker,
      algebraMap A P.completedPolynomialRing (a ^ c) * (g : P.completedPolynomialRing) ∈
        Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2) :
    (algebraMap A B.carrier a) ^ (2 * c * P.variableCount + c) ∈
      Module.annihilator B.carrier
        (LinearMap.ker (completedNaiveCotangentComplex B P).differential) := by
  classical
  set K := completedNaiveCotangentComplex B P with hK
  set u : B.carrier := algebraMap A B.carrier a with hu
  set M : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier :=
    fun i j => P.toAlgHom (K.partialDeriv i (f j : P.completedPolynomialRing)) with hM
  set F : Fin P.variableCount → P.extension.Cotangent :=
    fun j => Algebra.Extension.Cotangent.mk (f j) with hF
  have hcol : ∀ j, K.differential (F j) = fun i => M i j := fun j => K.differential_mk (f j)
  -- (5)(a): `a ^ c` carries `⨁ i, B dxᵢ` into the image of `d`.
  have hC1 : ∀ y : Fin P.variableCount → B.carrier,
      u ^ c • y ∈ LinearMap.range K.differential :=
    (mem_annihilator_quotient_iff _ _).mp hcoker
  -- (5)(b): `a ^ c` carries `J / J²` into the span of the classes `[fⱼ]`.
  have hmap : (algebraMap P.extension.Ring B.carrier)
      (algebraMap A P.completedPolynomialRing (a ^ c)) = u ^ c := by
    show P.toAlgHom (algebraMap A P.completedPolynomialRing (a ^ c)) = u ^ c
    rw [AlgHom.commutes, hu, map_pow]
  have hC2 : ∀ x : P.extension.Cotangent, ∃ w : Fin P.variableCount → B.carrier,
      ∑ j, w j • F j = u ^ c • x ∧ M.mulVec w = K.differential (u ^ c • x) := by
    intro x
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    have hx := Algebra.Extension.cotangentMk_smul_mem_span P.extension f
      (algebraMap A P.completedPolynomialRing (a ^ c)) g (hrel g)
    rw [hmap] at hx
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun B.carrier).mp hx
    exact ⟨w, hw, by rw [mulVec_eq_apply_sum_smul K.differential M F hcol w, hw]⟩
  -- Composing the two: `a ^ {2c}` carries `⨁ i, B dxᵢ` into the image of `M`.
  have hC3 : ∀ y : Fin P.variableCount → B.carrier, ∃ w : Fin P.variableCount → B.carrier,
      M.mulVec w = u ^ (2 * c) • y := by
    intro y
    obtain ⟨x, hx⟩ := hC1 y
    obtain ⟨w, -, hw⟩ := hC2 x
    exact ⟨w, by rw [hw, map_smul, hx, smul_smul, ← pow_add, two_mul]⟩
  choose w hw using hC3
  -- Hence a matrix `N` with `M · N = a ^ {2c} · 1`, and `det M ∣ a ^ {2cr}`.
  set N : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier :=
    fun j i => w (Pi.single i 1) j with hN
  have hMN : M * N = (u ^ (2 * c)) •
      (1 : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier) := by
    ext i' i
    have hentry : (M.mulVec (w (Pi.single i 1))) i' =
        (u ^ (2 * c) • (Pi.single i 1 : Fin P.variableCount → B.carrier)) i' :=
      congrFun (hw (Pi.single i 1)) i'
    have hmul : (M * N) i' i = (M.mulVec (w (Pi.single i 1))) i' := by
      rw [Matrix.mul_apply]
      rfl
    rw [hmul, hentry]
    simp [Matrix.one_apply, Pi.single_apply]
  obtain ⟨e, he⟩ : M.det ∣ u ^ (2 * c * P.variableCount) := by
    refine ⟨N.det, ?_⟩
    have hd := congrArg Matrix.det hMN
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      ← pow_mul] at hd
    exact hd.symm
  -- Running Cramer's rule backwards kills the kernel.
  refine Module.mem_annihilator.mpr ?_
  rintro ⟨x, hx⟩
  obtain ⟨v, hv, hMv'⟩ := hC2 x
  have hMv : M.mulVec v = 0 := by rw [hMv', map_smul, LinearMap.mem_ker.mp hx, smul_zero]
  have hdetv : M.det • v = 0 := by
    have hadj := congrArg (Matrix.mulVec M.adjugate) hMv
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hadj
    simpa using hadj
  have hpowv : u ^ (2 * c * P.variableCount) • v = 0 := by
    rw [he, mul_comm, mul_smul, hdetv, smul_zero]
  have hxzero : u ^ (2 * c * P.variableCount + c) • x = 0 := by
    rw [pow_add, mul_smul, ← hv, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_smul]
    rw [show u ^ (2 * c * P.variableCount) * v j = 0 from congrFun hpowv j, zero_smul]
  exact Subtype.ext (by simpa using hxzero)

/-- **Stacks 0AJU, (5) ⇒ (3).**  Condition (5) gives, for each `a ∈ I`, a power of `a`
annihilating both cohomology modules of `NL^∧_{B/A}`: for `H⁰` this is its first half and for
`H⁻¹` it is `Rig.pow_mem_annihilator_ker_differential_of_artinPreliminary`.  The scalars
annihilating both form an ideal of the Noetherian ring `B`, and every element of `IB` has a
power in it, so a single power of `IB` lies in it. -/
@[stacks 0AJU "(5) implies (3)"]
public theorem isCohomologyAnnihilated_of_isArtinPreliminary
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (h : IsArtinPreliminary B P) : IsCohomologyAnnihilated B P := by
  set Ann : Ideal B.carrier :=
    Module.annihilator B.carrier
        (LinearMap.ker (completedNaiveCotangentComplex B P).differential) ⊓
      Module.annihilator B.carrier
        ((Fin P.variableCount → B.carrier) ⧸
          LinearMap.range (completedNaiveCotangentComplex B P).differential) with hAnn
  have key : ∀ a ∈ I, algebraMap A B.carrier a ∈ Ann.radical := by
    intro a ha
    obtain ⟨c, hcoker, f, hrel⟩ := h a ha
    refine Ideal.mem_radical_iff.mpr
      ⟨2 * c * P.variableCount + c, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · exact pow_mem_annihilator_ker_differential_of_artinPreliminary B P a c hcoker f hrel
    · rw [pow_add]
      exact Ideal.mul_mem_left _ _ hcoker
  have hle : I.map (algebraMap A B.carrier) ≤ Ann.radical :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => key a ha
  obtain ⟨c, hc⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hle (Ideal.fg_of_isNoetherianRing _)
  refine ⟨c, ?_, ?_⟩
  · rw [Ideal.map_pow]
    exact hc.trans inf_le_left
  · rw [Ideal.map_pow]
    exact hc.trans inf_le_right

/-- **Stacks 0AJU, (1) ⇔ (7).**  Rig-étaleness of `B` over `(A, I)` is equivalent to the
Jacobian ideal and the Cramer ideal of *every* finite generating family of `J` each containing
a power of `IB`.

For a single family this is Stacks 0AJY,
`Rig.isRigEtale_iff_exists_pow_le_completedJacobianIdeal_and_completedCramerIdeal`; the
quantified form follows because `J` is a finitely generated ideal of the Noetherian ring
`A⟨x₁, …, x_r⟩`, so at least one such family exists. -/
@[stacks 0AJU "(1) iff (7)"]
public theorem isRigEtale_iff_isJacobianCramerBounded (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    IsRigEtale B ↔ IsJacobianCramerBounded B P := by
  constructor
  · intro hB t f hf
    exact (isRigEtale_iff_exists_pow_le_completedJacobianIdeal_and_completedCramerIdeal
      B P f hf).mp hB
  · intro h
    obtain ⟨t, f, hf⟩ :=
      Submodule.fg_iff_exists_fin_generating_family.mp (Ideal.fg_of_isNoetherianRing P.ker)
    exact (isRigEtale_iff_exists_pow_le_completedJacobianIdeal_and_completedCramerIdeal
      B P f hf.symm).mpr (h t f hf.symm)

end Missing

/-- **Stacks 0AJU.**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an `I`-adically
complete `A`-algebra of finite type modulo `I` and `B = A⟨x₁, …, x_r⟩ / J` a completed
polynomial presentation.  The seven Artin criteria are equivalent:

1. `B` is rig-étale over `(A, I)`;
2. some power of `I` annihilates the identity of `NL^∧_{B/A}` in `D(B)`;
3. some power of `IB` annihilates `H⁻¹(NL^∧_{B/A})` and `H⁰(NL^∧_{B/A})`;
4. some power of `I` annihilates `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0` and every `n ≥ 1`;
5. for every `a ∈ I` some `a ^ c` annihilates `H⁰(NL^∧_{B/A})` and there are `f₁, …, f_r ∈ J`
   with `a ^ c · J ⊆ (f₁, …, f_r) + J²`;
6. for every `a ∈ I` there are `f₁, …, f_r ∈ J` whose Jacobian determinant divides `a ^ c` and
   with `a ^ c · J ⊆ (f₁, …, f_r) + J²`;
7. the Jacobian ideal and the Cramer ideal of every finite generating family of `J` each
   contain a power of `IB`.

The cycle is closed as `(1) ⇒ (6) ⇒ (5) ⇒ (3) ⇒ (1)`, with `(1) ⇔ (2)`, `(3) ⇔ (4)` and
`(1) ⇔ (7)` hung off it. -/
@[stacks 0AJU]
public theorem tfae_isRigEtale (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    List.TFAE [IsRigEtale B, IsDerivedAnnihilated B P, IsCohomologyAnnihilated B P,
      IsReductionCohomologyAnnihilated B, IsArtinPreliminary B P, IsArtinJacobian B P,
      IsJacobianCramerBounded B P] := by
  tfae_have 1 ↔ 2 := isRigEtale_iff B P
  tfae_have 1 ↔ 3 := isRigEtale_iff_exists_annihilator_cohomology B P
  tfae_have 3 ↔ 4 := isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated B P
  tfae_have 1 → 6 := isArtinJacobian_of_isRigEtale B P
  tfae_have 6 → 5 := isArtinPreliminary_of_isArtinJacobian B P
  tfae_have 5 → 3 := isCohomologyAnnihilated_of_isArtinPreliminary B P
  tfae_have 1 ↔ 7 := isRigEtale_iff_isJacobianCramerBounded B P
  tfae_finish

end Rig

end
