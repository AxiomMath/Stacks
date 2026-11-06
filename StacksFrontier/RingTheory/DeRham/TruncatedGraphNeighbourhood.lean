module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import StacksFrontier.Algebra.DirectSum.GradedQuotient
public import StacksFrontier.RingTheory.DeRham.GradedPoincare

/-!
# The de Rham complex of a truncated graph neighbourhood

Let `A` be a `ℚ`-algebra with an ideal `𝔪` such that `𝔪^N = 0`, and let `R`, `R'` be two
`A`-algebras with a common reduction `R₀`: a surjection `π : R → R₀` with kernel `𝔪 R`, and a
map `π' : R' → R₀`. Assume `R'` has étale coordinates, that is, it is formally étale over a
polynomial ring `A[x_1, …, x_d]`. Let `I ⊆ R ⊗_A R'` be the kernel of `r ⊗ r' ↦ π(r) π'(r')`,
the ideal of the "graph" of the identification of reductions. Then

`Ω^•_{R/A} → Ω^•_{((R ⊗_A R')/I^N)/A}`

is a quasi-isomorphism. Indeed `(R ⊗_A R')/I^N ≅ R[y_1, …, y_d]/((y) + 𝔪 R[y])^N` as `R`-algebras,
with `y_i = 1 ⊗ x'_i - x_i ⊗ 1` for lifts `x_i ∈ R` of the images of the coordinates, and the
truncated polynomial algebra is graded by degree in `y` with weight-zero part `R`.

## Main definitions

* `GradedDeRham.quotientGradedAlgebra`: the grading of a quotient by a homogeneous ideal.
* `GradedDeRham.truncationIdeal`, `GradedDeRham.TruncatedAlgebra`: `((y) + 𝔪 R[y])^N` and
  `R[y]/((y) + 𝔪 R[y])^N`.
* `GradedDeRham.graphIdeal`, `GradedDeRham.GraphNeighbourhood`: `I` and `(R ⊗_A R')/I^N`.
* `GradedDeRham.graphEquiv`: `(R ⊗_A R')/I^N ≅ R[y]/((y) + 𝔪 R[y])^N`.

## Main results

* `GradedDeRham.quasiIso_deRhamComplexMap_truncatedAlgebra`: the truncated Poincaré lemma.
* `GradedDeRham.quasiIso_deRhamComplexMap_graphNeighbourhood`: the graph neighbourhood has the
  de Rham complex of `R`.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential DirectSum

universe u

namespace GradedDeRham

section Quotient

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
  (𝒜 : ℕ → Submodule R P) [GradedAlgebra 𝒜] (J : Ideal P)

/-- The grading of `P ⧸ J` by the images of the graded pieces of `P`. -/
def quotientGrading (n : ℕ) : Submodule R (P ⧸ J) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R J).toLinearMap

variable {𝒜 J}

omit [GradedAlgebra 𝒜] in
/-- The image in `P ⧸ J` of an element of degree `n` has degree `n`. -/
theorem mk_mem_quotientGrading {n : ℕ} {p : P} (hp : p ∈ 𝒜 n) :
    Ideal.Quotient.mk J p ∈ quotientGrading 𝒜 J n :=
  ⟨p, hp, rfl⟩

/-- The component of degree `i₀` of a sum of elements of distinct degrees. -/
theorem decompose_sum_of_mem (s : Finset ℕ) (p : ℕ → P) (hp : ∀ i ∈ s, p i ∈ 𝒜 i) {i₀ : ℕ}
    (hi₀ : i₀ ∈ s) : (decompose 𝒜 (∑ i ∈ s, p i) i₀ : P) = p i₀ := by
  rw [decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finset_sum,
    Finset.sum_eq_single_of_mem i₀ hi₀]
  · exact decompose_of_mem_same 𝒜 (hp i₀ hi₀)
  · exact fun i hi hne => decompose_of_mem_ne 𝒜 (hp i hi) hne

/-- If `J` is homogeneous, then `P ⧸ J` is the internal direct sum of the images of the graded
pieces of `P`. -/
theorem isInternal_quotientGrading (hJ : J.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (quotientGrading 𝒜 J) := by
  classical
  refine DirectSum.isInternal_of_eq_zero_of_exists_sum _ ?_ ?_
  · intro s y hy hsum i₀ hi₀
    choose! p hp hpy using hy
    have hmem : ∑ i ∈ s, p i ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa [← hpy _ (Finset.mem_coe.1 _)] using
        (Finset.sum_congr rfl fun i hi => hpy i hi).trans hsum
    rw [← hpy i₀ hi₀]
    show Ideal.Quotient.mk J (p i₀) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← decompose_sum_of_mem s p hp hi₀]
    exact (hJ.mem_iff.1 hmem) i₀
  · intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(decompose 𝒜 q).support, fun i => Ideal.Quotient.mk J (decompose 𝒜 q i : P),
      fun i => mk_mem_quotientGrading (decompose 𝒜 q i).2, fun i hi => ?_, ?_⟩
    · show Ideal.Quotient.mk J _ = 0
      rw [DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, map_zero]
    · rw [← map_sum, sum_support_decompose 𝒜 q]

/-- **The quotient of a graded algebra by a homogeneous ideal is graded** by the images of the
graded pieces. -/
@[instance_reducible]
def quotientGradedAlgebra (hJ : J.IsHomogeneous 𝒜) : GradedAlgebra (quotientGrading 𝒜 J) :=
  { (isInternal_quotientGrading hJ).chooseDecomposition with
    one_mem := mk_mem_quotientGrading SetLike.GradedOne.one_mem
    mul_mem := by
      rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, by simp⟩ }

end Quotient

section RestrictScalars

variable {A R T : Type u} [CommRing A] [CommRing R] [CommRing T] [Algebra A R] [Algebra R T]
  [Algebra A T] [IsScalarTower A R T] (𝒜 : ℕ → Submodule R T) [GradedAlgebra 𝒜]

/-- A grading by `R`-submodules, read as a grading by `A`-submodules. -/
def restrictGrading (n : ℕ) : Submodule A T := (𝒜 n).restrictScalars A

/-- The restricted grading is a grading. -/
@[instance_reducible]
def restrictGradedAlgebra : GradedAlgebra (restrictGrading (A := A) 𝒜) :=
  { DirectSum.IsInternal.chooseDecomposition (ℳ := restrictGrading (A := A) 𝒜)
      (DirectSum.Decomposition.isInternal 𝒜) with
    one_mem := SetLike.GradedOne.one_mem (A := 𝒜)
    mul_mem := fun _ _ _ _ ha hb => SetLike.GradedMul.mul_mem (A := 𝒜) ha hb }

end RestrictScalars

section Truncation

open MvPolynomial

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] (m : Ideal A) (d N : ℕ)

/-- **The truncation ideal** `((y_1, …, y_d) + 𝔪 R[y])^N` of `R[y_1, …, y_d]`, whose quotient is
the local model of the `N`-th infinitesimal neighbourhood of a graph of two liftings over `A`
of a common reduction modulo `𝔪`. -/
def truncationIdeal : Ideal (MvPolynomial (Fin d) R) :=
  (Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) R)) ⊔
    m.map (algebraMap A (MvPolynomial (Fin d) R))) ^ N

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The truncation ideal is homogeneous for the grading by degree in `y`. -/
theorem isHomogeneous_truncationIdeal :
    (truncationIdeal (R := R) m d N).IsHomogeneous (homogeneousSubmodule (Fin d) R) := by
  refine Ideal.IsHomogeneous.pow _ ?_ N
  refine Ideal.IsHomogeneous.sup ?_ ?_
  · refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨1, isHomogeneous_X R i⟩
  · rw [Ideal.map]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨a, -, rfl⟩
    exact ⟨0, by
      rw [IsScalarTower.algebraMap_apply A R (MvPolynomial (Fin d) R), algebraMap_eq]
      exact isHomogeneous_C _ _⟩

variable {m d N}

/-- Evaluation at `y = 0` kills the truncation ideal once `𝔪^N = 0`. -/
theorem map_aeval_zero_truncationIdeal (hN : m ^ N = ⊥) :
    (truncationIdeal (R := R) m d N).map (aeval (R := R) (0 : Fin d → R)).toRingHom = ⊥ := by
  have h1 : (Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) R))).map
      (aeval (R := R) (0 : Fin d → R)).toRingHom = ⊥ := by
    rw [Ideal.map_span, Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp
  have h2 : (aeval (R := R) (0 : Fin d → R)).toRingHom.comp
      (algebraMap A (MvPolynomial (Fin d) R)) = algebraMap A R := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A R (MvPolynomial (Fin d) R),
      algebraMap_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [truncationIdeal, Ideal.map_pow, Ideal.map_sup, Ideal.map_map, h1, h2, bot_sup_eq,
    ← Ideal.map_pow, hN, Ideal.map_bot]

/-- Once `𝔪^N = 0`, the truncation ideal is contained in the kernel of evaluation at `y = 0`. -/
theorem truncationIdeal_le_ker (hN : m ^ N = ⊥) :
    truncationIdeal (R := R) m d N ≤ RingHom.ker (aeval (R := R) (0 : Fin d → R)).toRingHom :=
  (Ideal.map_eq_bot_iff_le_ker _).1 (map_aeval_zero_truncationIdeal hN)

/-- A polynomial of degree zero is the constant given by its constant coefficient. -/
private theorem eq_C_coeff_zero_of_mem_degreeZero {p : MvPolynomial (Fin d) R}
    (hp : p ∈ homogeneousSubmodule (Fin d) R 0) : p = C (p.coeff 0) := by
  rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hp, if_pos rfl]

/-- **The truncation ideal has no weight-zero elements**: a constant in
`((y) + 𝔪 R[y])^N` vanishes once `𝔪^N = 0`. -/
theorem eq_zero_of_mem_truncationIdeal_of_mem_degreeZero (hN : m ^ N = ⊥)
    {p : MvPolynomial (Fin d) R} (hpJ : p ∈ truncationIdeal m d N)
    (hp0 : p ∈ homogeneousSubmodule (Fin d) R 0) : p = 0 := by
  have h := truncationIdeal_le_ker hN hpJ
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_zero,
    Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq] at h
  rw [eq_C_coeff_zero_of_mem_degreeZero hp0, h, map_zero]

variable (m d N)

/-- **The truncated polynomial algebra** `R[y_1, …, y_d]/((y) + 𝔪 R[y])^N`. -/
abbrev TruncatedAlgebra := MvPolynomial (Fin d) R ⧸ truncationIdeal (R := R) m d N

/-- The grading of the truncated algebra by degree in `y`, by `A`-submodules. -/
def truncatedGrading : ℕ → Submodule A (TruncatedAlgebra (R := R) m d N) :=
  restrictGrading (A := A)
    (quotientGrading (homogeneousSubmodule (Fin d) R) (truncationIdeal (R := R) m d N))

/-- The truncated algebra is graded by degree in `y`. -/
@[instance_reducible]
def truncatedGradedAlgebra : GradedAlgebra (truncatedGrading (R := R) m d N) := by
  letI := quotientGradedAlgebra (isHomogeneous_truncationIdeal (R := R) m d N)
  exact restrictGradedAlgebra _

variable {m d N}

/-- Evaluation at `y = 0` on the truncated algebra, defined once `𝔪^N = 0`. -/
def truncatedEval (hN : m ^ N = ⊥) : TruncatedAlgebra (R := R) m d N →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (0 : Fin d → R)) fun _ ha =>
    RingHom.mem_ker.1 (truncationIdeal_le_ker hN ha)

/-- Evaluation at `y = 0` sends the class of `p` to its constant coefficient. -/
theorem truncatedEval_mk (hN : m ^ N = ⊥) (p : MvPolynomial (Fin d) R) :
    truncatedEval hN (Ideal.Quotient.mk _ p) = p.coeff 0 := by
  show aeval (0 : Fin d → R) p = p.coeff 0
  rw [aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq]

/-- **The truncated Poincaré lemma**: over a `ℚ`-algebra `A` with `𝔪^N = 0`, the restriction of
forms `Ω^•_{R/A} → Ω^•_{T/A}` to the truncated polynomial algebra
`T = R[y_1, …, y_d]/((y) + 𝔪 R[y])^N` is a quasi-isomorphism. -/
theorem quasiIso_deRhamComplexMap_truncatedAlgebra [Algebra ℚ A] (hN : m ^ N = ⊥) :
    QuasiIso (deRhamComplexMap A R (TruncatedAlgebra (R := R) m d N)) := by
  let := truncatedGradedAlgebra (R := R) m d N
  let : Algebra (TruncatedAlgebra (R := R) m d N) R := (truncatedEval hN).toAlgebra
  have : IsScalarTower A (TruncatedAlgebra (R := R) m d N) R :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap A R a = truncatedEval hN (algebraMap A _ a)
      rw [IsScalarTower.algebraMap_apply A R (TruncatedAlgebra (R := R) m d N), AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
  let : Algebra ℚ (TruncatedAlgebra (R := R) m d N) :=
    ((algebraMap A (TruncatedAlgebra (R := R) m d N)).comp (algebraMap ℚ A)).toAlgebra
  refine Retraction.quasiIso (gr := truncatedGrading (R := R) m d N) ⟨fun s => ?_, ?_, ?_⟩
  · exact (truncatedEval hN).commutes s
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨p.coeff 0, ?_⟩
    conv_rhs => rw [eq_C_coeff_zero_of_mem_degreeZero hp]
    rfl
  · rintro n hn _ ⟨p, hp, rfl⟩
    show truncatedEval hN (Ideal.Quotient.mk _ p) = 0
    rw [truncatedEval_mk]
    exact (mem_homogeneousSubmodule n p).1 hp |>.coeff_eq_zero (by simpa using hn.ne)

end Truncation

section Graph

open MvPolynomial TensorProduct

variable {A R R' R₀ : Type u} [CommRing A] [CommRing R] [CommRing R'] [CommRing R₀]
  [Algebra A R] [Algebra A R'] [Algebra A R₀] (π : R →ₐ[A] R₀) (π' : R' →ₐ[A] R₀)

/-- The multiplication `R ⊗_A R' → R₀`, `r ⊗ r' ↦ π(r) π'(r')`. -/
def graphMult : R ⊗[A] R' →ₐ[A] R₀ :=
  Algebra.TensorProduct.lift π π' fun _ _ => .all _ _

/-- `graphMult π π'` sends `r ⊗ r'` to `π(r) π'(r')`. -/
@[simp]
theorem graphMult_tmul (r : R) (r' : R') : graphMult π π' (r ⊗ₜ r') = π r * π' r' :=
  Algebra.TensorProduct.lift_tmul _ _ _ r r'

/-- **The ideal of the graph**: the kernel of `R ⊗_A R' → R₀`. -/
def graphIdeal : Ideal (R ⊗[A] R') := RingHom.ker (graphMult π π')

/-- **The `N`-th infinitesimal neighbourhood of the graph**, `(R ⊗_A R') / I^N`. -/
abbrev GraphNeighbourhood (N : ℕ) := (R ⊗[A] R') ⧸ graphIdeal π π' ^ N

variable {d : ℕ} [Algebra (MvPolynomial (Fin d) A) R'] [IsScalarTower A (MvPolynomial (Fin d) A) R']

/-- The coordinates `x'_i ∈ R'`. -/
abbrev coord (i : Fin d) : R' := algebraMap (MvPolynomial (Fin d) A) R' (X i)

variable {π π'} {m : Ideal A} {N : ℕ} {x : Fin d → R}

omit [Algebra (MvPolynomial (Fin d) A) R'] [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- The image of an ideal `I` in `B / I^N` has vanishing `N`-th power. -/
theorem map_mk_pow_eq_bot {B : Type*} [CommRing B] (I : Ideal B) (N : ℕ) :
    (I.map (Ideal.Quotient.mk (I ^ N))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

omit [Algebra (MvPolynomial (Fin d) A) R'] [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- If `𝔪` maps to zero in `R₀`, then the image of every element of `𝔪` lies in the ideal of the
graph. -/
theorem algebraMap_mem_graphIdeal (hm : ∀ a ∈ m, algebraMap A R₀ a = 0) {a : A} (ha : a ∈ m) :
    algebraMap A (R ⊗[A] R') a ∈ graphIdeal π π' := by
  rw [graphIdeal, RingHom.mem_ker, AlgHom.commutes, hm a ha]

/-- The map `R[y]/J → (R ⊗_A R')/I^N`, `y_i ↦ 1 ⊗ x'_i - x̃_i ⊗ 1`. -/
def truncatedToGraph (hm : ∀ a ∈ m, algebraMap A R₀ a = 0)
    (hx : ∀ i, π (x i) = π' (coord (A := A) i)) :
    TruncatedAlgebra (R := R) m d N →ₐ[R] GraphNeighbourhood π π' N :=
  Ideal.Quotient.liftₐ _ (aeval fun i =>
      Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i - x i ⊗ₜ[A] (1 : R')))
    fun p hp => by
    set g : MvPolynomial (Fin d) R →ₐ[R] GraphNeighbourhood π π' N := aeval fun i =>
      Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i - x i ⊗ₜ[A] (1 : R'))
    have hI : ∀ i, (1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i - x i ⊗ₜ[A] (1 : R') ∈
        graphIdeal π π' := fun i => by
      rw [graphIdeal, RingHom.mem_ker, map_sub, graphMult_tmul, graphMult_tmul, map_one, map_one,
        one_mul, mul_one, hx, sub_self]
    have h1 : (Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) R))).map g.toRingHom ≤
        (graphIdeal π π').map (Ideal.Quotient.mk _) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      simp only [g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      exact Ideal.mem_map_of_mem _ (hI i)
    have h2 : (m.map (algebraMap A (MvPolynomial (Fin d) R))).map g.toRingHom ≤
        (graphIdeal π π').map (Ideal.Quotient.mk _) := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (g.restrictScalars A) (algebraMap A (MvPolynomial (Fin d) R) a) ∈ _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (R ⊗[A] R')
          (GraphNeighbourhood π π' N), Ideal.Quotient.algebraMap_eq]
      exact Ideal.mem_map_of_mem _ (algebraMap_mem_graphIdeal hm ha)
    have hJ : (truncationIdeal (R := R) m d N).map g.toRingHom = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [← map_mk_pow_eq_bot (graphIdeal π π') N, truncationIdeal, Ideal.map_pow, Ideal.map_sup]
      exact Ideal.pow_right_mono (sup_le h1 h2) N
    exact (Ideal.map_eq_bot_iff_le_ker _).1 hJ hp

variable (π π' m N x) in
/-- The standing hypotheses on the graph data: `𝔪^N = 0`, `π : R → R₀` is surjective with kernel
`𝔪 R`, and `x_i ∈ R` lifts the image of the coordinate `x'_i` of `R'`. -/
structure GraphHyp : Prop where
  pos : N ≠ 0
  pow : m ^ N = ⊥
  surj : Function.Surjective π
  ker : RingHom.ker π = m.map (algebraMap A R)
  coord : ∀ i, π (x i) = π' (coord (A := A) i)

omit [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- Under the standing hypotheses, `𝔪` maps to zero in `R₀`. -/
theorem GraphHyp.algebraMap_eq_zero (h : GraphHyp π π' m N x) {a : A} (ha : a ∈ m) :
    algebraMap A R₀ a = 0 := by
  rw [← π.commutes, ← RingHom.mem_ker, h.ker]
  exact Ideal.mem_map_of_mem _ ha

/-- The reduction `R[y]/J → R₀`, `y ↦ 0` followed by `π`. -/
def truncatedReduction (h : GraphHyp π π' m N x) : TruncatedAlgebra (R := R) m d N →ₐ[A] R₀ :=
  π.comp ((truncatedEval h.pow).restrictScalars A)

omit [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- The reduction `R[y]/J → R₀` restricts to `π` on `R`. -/
theorem truncatedReduction_algebraMap (h : GraphHyp π π' m N x) (r : R) :
    truncatedReduction h (algebraMap R _ r) = π r := by
  simp [truncatedReduction]

omit [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- The reduction `R[y]/J → R₀` sends the class of `p` to `π` of its constant coefficient. -/
theorem truncatedReduction_mk (h : GraphHyp π π' m N x) (p : MvPolynomial (Fin d) R) :
    truncatedReduction h (Ideal.Quotient.mk _ p) = π (p.coeff 0) := by
  simp [truncatedReduction, truncatedEval_mk]

omit [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- The reduction `R[y]/J → R₀` is surjective. -/
theorem surjective_truncatedReduction (h : GraphHyp π π' m N x) :
    Function.Surjective (truncatedReduction h) := fun r₀ => by
  obtain ⟨r, rfl⟩ := h.surj r₀
  exact ⟨algebraMap R _ r, truncatedReduction_algebraMap h r⟩

omit [IsScalarTower A (MvPolynomial (Fin d) A) R'] in
/-- The kernel of the reduction `R[y]/J → R₀` has vanishing `N`-th power. -/
theorem ker_truncatedReduction_pow (h : GraphHyp π π' m N x) :
    RingHom.ker (truncatedReduction h : TruncatedAlgebra (R := R) m d N →+* R₀) ^ N = ⊥ := by
  set L : Ideal (MvPolynomial (Fin d) R) :=
    Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) R)) ⊔
      m.map (algebraMap A (MvPolynomial (Fin d) R))
  have hle : RingHom.ker (truncatedReduction h : TruncatedAlgebra (R := R) m d N →+* R₀) ≤
      L.map (Ideal.Quotient.mk _) := by
    intro t ht
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [RingHom.mem_ker, AlgHom.coe_toRingHom, truncatedReduction_mk, ← RingHom.mem_ker,
      h.ker] at ht
    refine Ideal.mem_map_of_mem _ ?_
    rw [← sub_add_cancel p (C (p.coeff 0))]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · rw [← Set.image_univ, mem_ideal_span_X_image]
      intro μ hμ
      by_contra hne
      simp only [Set.mem_univ, true_and, not_exists, not_not] at hne
      have hμ0 : μ = 0 := Finsupp.ext hne
      subst hμ0
      simp at hμ
    · have hC : (m.map (algebraMap A R)).map (C : R →+* MvPolynomial (Fin d) R) =
          m.map (algebraMap A (MvPolynomial (Fin d) R)) := by
        rw [Ideal.map_map]
        rfl
      rw [← hC]
      exact Ideal.mem_map_of_mem _ ht
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle N).trans ?_)
  rw [← Ideal.map_pow]
  exact (Ideal.map_quotient_self (truncationIdeal (R := R) m d N)).le

variable (m N x) in
/-- The images `x_i + y_i` of the coordinates in the truncated algebra. -/
def truncatedCoord : MvPolynomial (Fin d) A →ₐ[A] TruncatedAlgebra (R := R) m d N :=
  aeval fun i => Ideal.Quotient.mk _ (C (x i) + X i)

/-- The reduction of the coordinates `x_i + y_i` of `R[y]/J` is `π'` of the coordinates `x'_i`
of `R'`. -/
theorem truncatedReduction_comp_truncatedCoord (h : GraphHyp π π' m N x) :
    (truncatedReduction h).comp (truncatedCoord m N x) =
      π'.comp (IsScalarTower.toAlgHom A (MvPolynomial (Fin d) A) R') := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, truncatedCoord, aeval_X, truncatedReduction_mk, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', ← h.coord i]
  simp

variable [Algebra.FormallyEtale (MvPolynomial (Fin d) A) R']

variable (m N x) in
/-- `R[y]/J` as an `A[x]`-algebra through the coordinates `x_i + y_i`. -/
@[instance_reducible]
def truncatedCoordAlgebra : Algebra (MvPolynomial (Fin d) A) (TruncatedAlgebra (R := R) m d N) :=
  (truncatedCoord m N x).toRingHom.toAlgebra

variable (π') in
/-- `R₀` as an `A[x]`-algebra through `π'`. -/
@[instance_reducible]
def reductionAlgebra : Algebra (MvPolynomial (Fin d) A) R₀ :=
  (π'.toRingHom.comp (algebraMap _ R')).toAlgebra

variable (m N x) in
/-- `A → A[x] → R[y]/J` is a scalar tower for the coordinates `x_i + y_i`. -/
theorem truncatedCoord_isScalarTower :
    letI := truncatedCoordAlgebra m N x
    IsScalarTower A (MvPolynomial (Fin d) A) (TruncatedAlgebra (R := R) m d N) :=
  let := truncatedCoordAlgebra m N x
  IsScalarTower.of_algebraMap_eq fun a => ((truncatedCoord m N x).commutes a).symm

variable (π') in
omit [Algebra.FormallyEtale (MvPolynomial (Fin d) A) R'] in
/-- `A → A[x] → R₀` is a scalar tower for the `A[x]`-algebra structure through `π'`. -/
theorem reduction_isScalarTower :
    letI := reductionAlgebra (d := d) π'
    IsScalarTower A (MvPolynomial (Fin d) A) R₀ :=
  let := reductionAlgebra (d := d) π'
  IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A R₀ a = π' (algebraMap _ R' (algebraMap A _ a))
    rw [← IsScalarTower.algebraMap_apply, π'.commutes]

/-- **The étale lift** `R' → R[y]/J`: the unique map over the coordinates `x'_i ↦ x_i + y_i`
lifting `π' : R' → R₀`, by formal étaleness of `A[x] → R'`. -/
def coordLift (h : GraphHyp π π' m N x) : R' →ₐ[A] TruncatedAlgebra (R := R) m d N :=
  letI := truncatedCoordAlgebra m N x
  letI := reductionAlgebra (d := d) π'
  haveI := truncatedCoord_isScalarTower m N x
  haveI := reduction_isScalarTower (d := d) π'
  (Algebra.FormallySmooth.liftOfSurjective
    ({ π'.toRingHom with commutes' := fun _ => rfl } : R' →ₐ[MvPolynomial (Fin d) A] R₀)
    ({ (truncatedReduction h).toRingHom with
      commutes' := fun p => AlgHom.congr_fun (truncatedReduction_comp_truncatedCoord h) p } :
      TruncatedAlgebra (R := R) m d N →ₐ[MvPolynomial (Fin d) A] R₀)
    (surjective_truncatedReduction h)
    ⟨N, by rw [Ideal.zero_eq_bot]; exact ker_truncatedReduction_pow h⟩).restrictScalars A

/-- The étale lift `R' → R[y]/J` lifts `π'` and is `A[x]`-linear for the coordinates `x_i + y_i`. -/
private theorem coordLift_spec (h : GraphHyp π π' m N x) :
    (∀ r', truncatedReduction h (coordLift h r') = π' r') ∧
      ∀ p, coordLift h (algebraMap (MvPolynomial (Fin d) A) R' p) = truncatedCoord m N x p := by
  let := truncatedCoordAlgebra m N x
  let := reductionAlgebra (d := d) π'
  have := truncatedCoord_isScalarTower m N x
  have := reduction_isScalarTower (d := d) π'
  let g : R' →ₐ[MvPolynomial (Fin d) A] R₀ := { π'.toRingHom with commutes' := fun _ => rfl }
  let q : TruncatedAlgebra (R := R) m d N →ₐ[MvPolynomial (Fin d) A] R₀ :=
    { (truncatedReduction h).toRingHom with
      commutes' := fun p => AlgHom.congr_fun (truncatedReduction_comp_truncatedCoord h) p }
  have hq : ∃ n : ℕ, (RingHom.ker q) ^ n = 0 :=
    ⟨N, by rw [Ideal.zero_eq_bot]; exact ker_truncatedReduction_pow h⟩
  exact ⟨fun r' => Algebra.FormallySmooth.liftOfSurjective_apply g q
    (surjective_truncatedReduction h) hq r',
    (Algebra.FormallySmooth.liftOfSurjective g q (surjective_truncatedReduction h) hq).commutes⟩

/-- The étale lift `R' → R[y]/J` lifts `π'`. -/
theorem truncatedReduction_coordLift (h : GraphHyp π π' m N x) (r' : R') :
    truncatedReduction h (coordLift h r') = π' r' :=
  (coordLift_spec h).1 r'

/-- The étale lift `R' → R[y]/J` sends the coordinate `x'_i` to `x_i + y_i`. -/
theorem coordLift_coord (h : GraphHyp π π' m N x) (i : Fin d) :
    coordLift h (coord (A := A) i) = Ideal.Quotient.mk _ (C (x i) + X i) := by
  rw [coord, (coordLift_spec h).2, truncatedCoord, aeval_X]

/-- The étale lift `R' → R[y]/J` restricts on `A[x]` to the coordinates `x_i + y_i`. -/
theorem coordLift_comp (h : GraphHyp π π' m N x) :
    (coordLift h).comp (IsScalarTower.toAlgHom A (MvPolynomial (Fin d) A) R') =
      truncatedCoord m N x :=
  MvPolynomial.algHom_ext fun i => by
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', coordLift_coord, truncatedCoord, aeval_X]

/-- The map `R ⊗_A R' → R[y]/J`, `r ⊗ r' ↦ r · χ(r')`. -/
def graphLift (h : GraphHyp π π' m N x) : R ⊗[A] R' →ₐ[R] TruncatedAlgebra (R := R) m d N :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) (coordLift h) fun _ _ => .all _ _

/-- `graphLift h` sends `r ⊗ r'` to `r` times the étale lift of `r'`. -/
theorem graphLift_tmul (h : GraphHyp π π' m N x) (r : R) (r' : R') :
    graphLift h (r ⊗ₜ r') = algebraMap R _ r * coordLift h r' :=
  Algebra.TensorProduct.lift_tmul _ _ _ r r'

/-- `R ⊗_A R' → R[y]/J → R₀` is the multiplication `R ⊗_A R' → R₀`. -/
theorem truncatedReduction_comp_graphLift (h : GraphHyp π π' m N x) :
    (truncatedReduction h).comp ((graphLift h).restrictScalars A) = graphMult π π' :=
  Algebra.TensorProduct.ext' fun r r' => by
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, graphLift_tmul, map_mul,
      truncatedReduction_algebraMap, truncatedReduction_coordLift, graphMult_tmul]

/-- `R ⊗_A R' → R[y]/J` kills `I^N`. -/
theorem graphLift_pow_le_ker (h : GraphHyp π π' m N x) :
    graphIdeal π π' ^ N ≤ RingHom.ker (graphLift h).toRingHom := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  refine le_bot_iff.1 ((Ideal.pow_right_mono ?_ N).trans (ker_truncatedReduction_pow h).le)
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := AlgHom.congr_fun (truncatedReduction_comp_graphLift h) c
  rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
  exact this.trans hc

/-- The map `(R ⊗_A R')/I^N → R[y]/J`. -/
def graphToTruncated (h : GraphHyp π π' m N x) :
    GraphNeighbourhood π π' N →ₐ[R] TruncatedAlgebra (R := R) m d N :=
  Ideal.Quotient.liftₐ _ (graphLift h) fun _ ha => graphLift_pow_le_ker h ha

/-- The multiplication `(R ⊗_A R')/I^N → R₀`. -/
def graphNeighbourhoodMult (hN : N ≠ 0) : GraphNeighbourhood π π' N →ₐ[A] R₀ :=
  Ideal.Quotient.liftₐ _ (graphMult π π') fun _ ha => Ideal.pow_le_self hN ha

/-- `(R ⊗_A R')/I^N → R[y]/J` sends the class of `c` to `graphLift h c`. -/
theorem graphToTruncated_mk (h : GraphHyp π π' m N x) (c : R ⊗[A] R') :
    graphToTruncated h (Ideal.Quotient.mk _ c) = graphLift h c := rfl

omit [IsScalarTower A (MvPolynomial (Fin d) A) R']
  [Algebra.FormallyEtale (MvPolynomial (Fin d) A) R'] in
/-- `R[y]/J → (R ⊗_A R')/I^N` sends `y_i` to the class of `1 ⊗ x'_i - x_i ⊗ 1`. -/
theorem truncatedToGraph_mk_X (hm : ∀ a ∈ m, algebraMap A R₀ a = 0)
    (hx : ∀ i, π (x i) = π' (coord (A := A) i)) (i : Fin d) :
    truncatedToGraph (N := N) hm hx (Ideal.Quotient.mk _ (X i)) =
      Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i - x i ⊗ₜ[A] (1 : R')) := by
  show (aeval fun i => Ideal.Quotient.mk (graphIdeal π π' ^ N)
    ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i - x i ⊗ₜ[A] (1 : R'))) (X i) = _
  rw [aeval_X]

/-- The multiplication `(R ⊗_A R')/I^N → R₀` sends the class of `c` to `graphMult π π' c`. -/
theorem graphNeighbourhoodMult_mk (hN : N ≠ 0) (c : R ⊗[A] R') :
    graphNeighbourhoodMult (π := π) (π' := π') hN (Ideal.Quotient.mk _ c) = graphMult π π' c := rfl

/-- The kernel of the multiplication `(R ⊗_A R')/I^N → R₀` has vanishing `N`-th power. -/
theorem ker_graphNeighbourhoodMult_pow (hN : N ≠ 0) :
    RingHom.ker (graphNeighbourhoodMult (π := π) (π' := π') hN).toRingHom ^ N = ⊥ := by
  refine le_bot_iff.1 ((Ideal.pow_right_mono (I := RingHom.ker _)
    (J := (graphIdeal π π').map (Ideal.Quotient.mk _)) ?_ N).trans
      (map_mk_pow_eq_bot (graphIdeal π π') N).le)
  intro q hq
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Ideal.mem_map_of_mem _ hq

omit [IsScalarTower A (MvPolynomial (Fin d) A) R']
  [Algebra.FormallyEtale (MvPolynomial (Fin d) A) R'] in
/-- The multiplication of the graph neighbourhood restricts along `R[y]/J → (R ⊗_A R')/I^N` to
the reduction `R[y]/J → R₀`. -/
theorem graphNeighbourhoodMult_truncatedToGraph (h : GraphHyp π π' m N x)
    (t : TruncatedAlgebra (R := R) m d N) :
    graphNeighbourhoodMult h.pos (truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha)
      h.coord t) = truncatedReduction h t := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  suffices H : (graphNeighbourhoodMult h.pos).toRingHom.comp
      (((truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha) h.coord).toRingHom).comp
        (Ideal.Quotient.mk _)) =
      (truncatedReduction h).toRingHom.comp (Ideal.Quotient.mk _) from
    RingHom.congr_fun H p
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk R, AlgHom.commutes,
      AlgHom.commutes, truncatedReduction_algebraMap,
      IsScalarTower.algebraMap_apply R (R ⊗[A] R') (GraphNeighbourhood π π' N),
      Ideal.Quotient.algebraMap_eq, graphNeighbourhoodMult_mk]
    simp
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [truncatedToGraph_mk_X, graphNeighbourhoodMult_mk, map_sub, graphMult_tmul,
      graphMult_tmul, map_one, map_one, one_mul, mul_one, ← h.coord i, sub_self,
      truncatedReduction_mk]
    simp

/-- `R[y]/J → (R ⊗_A R')/I^N → R[y]/J` is the identity. -/
theorem graphToTruncated_comp_truncatedToGraph (h : GraphHyp π π' m N x) :
    (graphToTruncated h).comp
        (truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha) h.coord) =
      AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, truncatedToGraph_mk_X,
    graphToTruncated_mk, map_sub, graphLift_tmul, coordLift_coord, map_one, mul_one, one_mul,
    AlgHom.id_apply, map_add]
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin d) R) (TruncatedAlgebra (R := R) m d N),
    Ideal.Quotient.algebraMap_eq]
  simp only [MvPolynomial.algebraMap_eq]
  abel

/-- `(R ⊗_A R')/I^N → R[y]/J → (R ⊗_A R')/I^N` is the identity: on `R` by `R`-linearity, and on
`R'` by formal unramifiedness of `A[x] → R'`, both maps reducing to `π'` modulo the nilpotent
ideal `I/I^N`. -/
theorem truncatedToGraph_comp_graphToTruncated (h : GraphHyp π π' m N x) :
    (truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha) h.coord).comp
        (graphToTruncated h) = AlgHom.id R _ := by
  set q : R ⊗[A] R' →ₐ[R] GraphNeighbourhood π π' N := Ideal.Quotient.mkₐ R _
  refine Ideal.Quotient.algHom_ext R (Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_)
  let : Algebra (MvPolynomial (Fin d) A) (GraphNeighbourhood π π' N) :=
    (aeval fun i => q ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i) :
      MvPolynomial (Fin d) A →ₐ[A] GraphNeighbourhood π π' N).toRingHom.toAlgebra
  have h₁ : (((truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha)
      h.coord).restrictScalars A).comp (coordLift h)).comp
      (IsScalarTower.toAlgHom A (MvPolynomial (Fin d) A) R') =
      aeval fun i => q ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i) := by
    rw [AlgHom.comp_assoc, coordLift_comp]
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, truncatedCoord, aeval_X, aeval_X, AlgHom.restrictScalars_apply,
      map_add, map_add, truncatedToGraph_mk_X, ← MvPolynomial.algebraMap_eq,
      ← Ideal.Quotient.mkₐ_eq_mk R, AlgHom.commutes, AlgHom.commutes]
    simp [q, IsScalarTower.algebraMap_apply R (R ⊗[A] R') (GraphNeighbourhood π π' N),
      Ideal.Quotient.algebraMap_eq]
  have h₂ : (((q.restrictScalars A).comp Algebra.TensorProduct.includeRight).comp
      (IsScalarTower.toAlgHom A (MvPolynomial (Fin d) A) R')) =
      aeval fun i => q ((1 : R) ⊗ₜ[A] coord (A := A) (R' := R') i) :=
    MvPolynomial.algHom_ext fun i => by simp
  let g₁ : R' →ₐ[MvPolynomial (Fin d) A] GraphNeighbourhood π π' N :=
    { (((truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha)
        h.coord).restrictScalars A).comp (coordLift h)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun h₁ p }
  let g₂ : R' →ₐ[MvPolynomial (Fin d) A] GraphNeighbourhood π π' N :=
    { ((q.restrictScalars A).comp Algebra.TensorProduct.includeRight).toRingHom with
      commutes' := fun p => AlgHom.congr_fun h₂ p }
  have heq : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext' (graphNeighbourhoodMult h.pos).toRingHom
      ⟨N, by rw [Ideal.zero_eq_bot]; exact ker_graphNeighbourhoodMult_pow h.pos⟩ g₁ g₂
      fun r' => ?_
    show graphNeighbourhoodMult h.pos ((truncatedToGraph (N := N)
      (fun _ ha => h.algebraMap_eq_zero ha) h.coord) (coordLift h r')) =
      graphNeighbourhoodMult h.pos (q ((1 : R) ⊗ₜ r'))
    rw [graphNeighbourhoodMult_truncatedToGraph h, truncatedReduction_coordLift]
    simp [q, graphNeighbourhoodMult_mk]
  ext r'
  have := AlgHom.congr_fun heq r'
  change (truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha) h.coord)
    (coordLift h r') = q ((1 : R) ⊗ₜ r') at this
  simpa [q, graphToTruncated_mk, graphLift_tmul] using this

/-- **The truncated graph neighbourhood is a truncated polynomial algebra**:
`(R ⊗_A R')/I^N ≅ R[y_1, …, y_d]/((y) + 𝔪 R[y])^N` as `R`-algebras, with
`y_i = 1 ⊗ x'_i - x_i ⊗ 1`. -/
def graphEquiv (h : GraphHyp π π' m N x) :
    GraphNeighbourhood π π' N ≃ₐ[R] TruncatedAlgebra (R := R) m d N :=
  AlgEquiv.ofAlgHom (graphToTruncated h)
    (truncatedToGraph (N := N) (fun _ ha => h.algebraMap_eq_zero ha) h.coord)
    (graphToTruncated_comp_truncatedToGraph h) (truncatedToGraph_comp_graphToTruncated h)

include d in
/-- **The de Rham complex of a truncated graph neighbourhood.** Let `A` be a `ℚ`-algebra with an
ideal `𝔪` such that `𝔪^N = 0` (`N ≠ 0`), let `π : R → R₀` be a surjection of `A`-algebras with
kernel `𝔪 R`, and let `π' : R' → R₀` be a map of `A`-algebras where `R'` is formally étale over a
polynomial ring `A[x_1, …, x_d]`. Write `I` for the kernel of `R ⊗_A R' → R₀`. Then the
restriction of forms `Ω^•_{R/A} → Ω^•_{(R ⊗_A R')/I^N / A}` is a quasi-isomorphism. -/
theorem quasiIso_deRhamComplexMap_graphNeighbourhood [Algebra ℚ A] (hN0 : N ≠ 0)
    (hN : m ^ N = ⊥) (hsurj : Function.Surjective π)
    (hker : RingHom.ker π = m.map (algebraMap A R)) :
    QuasiIso (deRhamComplexMap A R (GraphNeighbourhood π π' N)) := by
  choose x hx using fun i : Fin d => hsurj (π' (coord (A := A) i))
  have h : GraphHyp π π' m N x := ⟨hN0, hN, hsurj, hker, hx⟩
  let e := graphEquiv h
  let : Algebra (TruncatedAlgebra (R := R) m d N) (GraphNeighbourhood π π' N) :=
    e.symm.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R (TruncatedAlgebra (R := R) m d N) (GraphNeighbourhood π π' N) :=
    IsScalarTower.of_algebraMap_eq fun r => (e.symm.commutes r).symm
  have : IsScalarTower A (TruncatedAlgebra (R := R) m d N) (GraphNeighbourhood π π' N) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A R (TruncatedAlgebra (R := R) m d N),
        IsScalarTower.algebraMap_apply A R (GraphNeighbourhood π π' N)]
      exact (e.symm.commutes _).symm
  have hcomp := deRhamComplexMap_comp A R (TruncatedAlgebra (R := R) m d N)
    (GraphNeighbourhood π π' N)
  have := quasiIso_deRhamComplexMap_truncatedAlgebra (R := R) (d := d) hN
  have : IsIso (deRhamComplexMap A (TruncatedAlgebra (R := R) m d N)
      (GraphNeighbourhood π π' N)) :=
    isIso_deRhamComplexMap_of_algEquiv A (e.symm.restrictScalars A) rfl
  rw [← hcomp]
  infer_instance

end Graph

end GradedDeRham
