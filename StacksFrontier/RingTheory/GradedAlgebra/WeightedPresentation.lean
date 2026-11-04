module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksFrontier.RingTheory.GradedAlgebra.Nakayama

/-!
# Weighted graded presentations of finitely generated graded algebras

Let `k` be a field and `P = ⨁_{i ≥ 0} P_i` a graded `k`-algebra which is of finite type over
`k` and whose degree-zero piece is finite-dimensional. This file produces a *weighted graded
presentation* of `P`: weights `d : Fin n → ℕ`, homogeneous elements `x i ∈ P_{d i}` generating
`P` as a `k`-algebra, and finitely many weighted homogeneous polynomials `F j` of weighted
degrees `e j` generating the kernel of the evaluation map
`k[X_1, …, X_n] → P`, `X_i ↦ x i`.

This is the first step of the Stacks proof of the tangent-space half of Tag 0DVZ, where it is
written *"we choose a presentation `k[X_1, …, X_n]/(F_1, …, F_m) → P` of graded `k`-algebras
where `deg(X_i) = d_i` and `F_j` is homogeneous of degree `e_j`"*. It is stated here for its
own sake, with no deformation theory in it.

## Main results

* `GradedAlgebra.isScalarTower_gradeZero`: the degree-zero piece of a graded algebra acts
  compatibly with the base field.
* `GradedAlgebra.exists_fin_homogeneous_adjoin_eq_top`: a graded algebra of finite type over a
  field with finite-dimensional degree-zero piece is generated over the field by finitely many
  homogeneous elements, given with their degrees.
* `GradedAlgebra.aeval_mem_grading_of_isWeightedHomogeneous`: evaluating a weighted homogeneous
  polynomial at homogeneous elements whose degrees are the weights lands in the graded piece of
  the corresponding weighted degree. Stated over an arbitrary commutative base ring, since the
  lifted presentations of Tag 0DVZ evaluate over the deformation base rather than over the
  field.
* `GradedAlgebra.aevalGradedRingHom`: that evaluation as a homomorphism of graded rings.
* `GradedAlgebra.exists_weightedGradedPresentation`: the weighted graded presentation.

## Implementation notes

The weighted grading on the polynomial algebra is Mathlib's
`MvPolynomial.weightedHomogeneousSubmodule`, whose `GradedAlgebra` structure
`MvPolynomial.weightedGradedAlgebra` is a `def` rather than an instance and so is introduced
locally where it is needed.

Homogeneity of the kernel is obtained by bundling the evaluation map as a graded ring
homomorphism and taking `HomogeneousIdeal.comap` of the zero ideal, whose underlying ideal is
definitionally the preimage; this avoids any direct argument with homogeneous components.
Finitely many *homogeneous* generators of that kernel then come from
`Submodule.IsHomogeneous.exists_finset_homogeneous_span_eq`, which Mathlib does not have, and
finite generation from Noetherianity of the polynomial algebra.

Mathlib's generators `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous` generate `P`
over the degree-zero piece rather than over `k`, which is why the degree-zero piece has to be
finite-dimensional: a `k`-basis of it is adjoined to those generators, in degree `0`.

`exists_fin_homogeneous_adjoin_eq_top` below asks only that the degree-zero piece be
finite-dimensional, which is all its proof uses, and it is the only declaration of that name:
the weighted-homogeneous presentations that consume it import it from here.
-/

@[expose] public section

universe u v

namespace GradedAlgebra

section Base

open MvPolynomial

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]

/-- Evaluating a weighted homogeneous polynomial at homogeneous elements whose degrees are the
weights lands in the graded piece of the corresponding weighted degree. -/
theorem aeval_mem_grading_of_isWeightedHomogeneous (grading : ℕ → Submodule R P)
    [GradedAlgebra grading] {n : ℕ} {x : Fin n → P} {d : Fin n → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) {e : ℕ} {F : MvPolynomial (Fin n) R}
    (hF : IsWeightedHomogeneous d F e) : aeval x F ∈ grading e := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => simpa using (grading e).add_mem ihp ihq
  | monomial m r hr =>
      rw [aeval_monomial]
      have hprod : (m.prod fun i c => x i ^ c) ∈ grading e := by
        rw [Finsupp.prod_fintype _ _ (fun i => by simp), ← hr, Finsupp.weight_eq_sum]
        exact SetLike.prod_pow_mem_graded (F := (Finset.univ : Finset (Fin n)))
          grading d x (fun i => m i) (fun i _ => hx i)
      rw [← Algebra.smul_def]
      exact (grading e).smul_mem r hprod

end Base

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

/-- The degree-zero piece of a graded algebra acts on the algebra compatibly with the base
field. -/
theorem isScalarTower_gradeZero (grading : ℕ → Submodule k P) [GradedAlgebra grading] :
    IsScalarTower k (grading 0) P := by
  refine IsScalarTower.of_algebraMap_smul (R := k) (A := grading 0) (M := P) fun r x => ?_
  rw [Algebra.smul_def, Algebra.smul_def]
  congr 1

/-- A graded algebra of finite type over a field whose degree-zero piece is finite-dimensional
is generated over the field by finitely many homogeneous elements, given together with their
degrees. -/
theorem exists_fin_homogeneous_adjoin_eq_top (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] [Module.Finite k (grading 0)] [Algebra.FiniteType k P] :
    ∃ (n : ℕ) (x : Fin n → P) (d : Fin n → ℕ),
      (∀ i, x i ∈ grading (d i)) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  classical
  let : IsScalarTower k (grading 0) P := isScalarTower_gradeZero grading
  let : Algebra.FiniteType (grading 0) P :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := grading 0) (A := P)
  obtain ⟨s, hsgen, hshom⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous (𝒜 := grading)
  let b : Module.Basis (Fin (Module.finrank k (grading 0))) k (grading 0) :=
    Module.finBasis k (grading 0)
  let ι := Sum {y : P // y ∈ s} (Fin (Module.finrank k (grading 0)))
  let w : ι → P := Sum.elim (fun y => y.1) (fun j => (b j : grading 0))
  let T : Subalgebra k P := Algebra.adjoin k (Set.range w)
  have hzero : ∀ y : grading 0, (y : P) ∈ T := by
    intro y
    have hle : Submodule.span k (Set.range b) ≤
        T.toSubmodule.comap (Submodule.subtype (grading 0)) := by
      apply Submodule.span_le.2
      rintro _ ⟨j, rfl⟩
      exact Algebra.subset_adjoin ⟨Sum.inr j, rfl⟩
    rw [b.span_eq] at hle
    exact hle Submodule.mem_top
  have hcontains : ∀ z ∈ Algebra.adjoin (grading 0) (s : Set P), z ∈ T := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    | algebraMap r => exact hzero r
    | add z₁ z₂ _ _ ih₁ ih₂ => exact T.add_mem ih₁ ih₂
    | mul z₁ z₂ _ _ ih₁ ih₂ => exact T.mul_mem ih₁ ih₂
  have hgen : Algebra.adjoin k (Set.range w) = ⊤ :=
    eq_top_iff.mpr fun y _ => hcontains y (by rw [hsgen]; exact Set.mem_univ y)
  let chooseDeg : (y : {y : P // y ∈ s}) → ℕ := fun y => Classical.choose (hshom y.1 y.2)
  have chooseDeg_spec (y : {y : P // y ∈ s}) : y.1 ∈ grading (chooseDeg y) :=
    Classical.choose_spec (hshom y.1 y.2)
  let dg : ι → ℕ := Sum.elim chooseDeg fun _ => 0
  have hw : ∀ i : ι, w i ∈ grading (dg i) := by
    rintro (y | j)
    exacts [chooseDeg_spec y, (b j).property]
  let : Fintype ι := inferInstance
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, w ∘ e.symm, dg ∘ e.symm, fun i => hw _, ?_⟩
  rwa [EquivLike.range_comp]

open MvPolynomial

/-- The evaluation of a weighted polynomial algebra at homogeneous elements whose degrees are
the weights, as a homomorphism of graded rings. -/
noncomputable def aevalGradedRingHom (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n : ℕ} (x : Fin n → P) (d : Fin n → ℕ) (hx : ∀ i, x i ∈ grading (d i)) :
    weightedHomogeneousSubmodule k d →+*ᵍ grading where
  __ := (aeval x : MvPolynomial (Fin n) k →ₐ[k] P).toRingHom
  map_mem := fun hF => aeval_mem_grading_of_isWeightedHomogeneous grading hx hF

/-- **A finitely generated graded algebra over a field has a weighted graded presentation.**
If the degree-zero piece of `P` is finite over `k` and `P` is of finite type over `k`, then
there are weights `d : Fin n → ℕ` and homogeneous elements `x i ∈ grading (d i)` for which the
evaluation map `k[X_1, …, X_n] → P`, `X_i ↦ x i`, is surjective, carries weighted homogeneous
polynomials of weighted degree `e` into `grading e`, and has kernel generated by finitely many
weighted homogeneous polynomials `F j` of weighted degrees `e j`. -/
theorem exists_weightedGradedPresentation (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] [Module.Finite k (grading 0)] [Algebra.FiniteType k P] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (x : Fin n → P),
      (∀ i, x i ∈ grading (d i)) ∧
      Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P) ∧
      (∀ (e : ℕ) (F : MvPolynomial (Fin n) k), IsWeightedHomogeneous d F e →
        aeval x F ∈ grading e) ∧
      ∃ (r : ℕ) (e : Fin r → ℕ) (F : Fin r → MvPolynomial (Fin n) k),
        (∀ j, IsWeightedHomogeneous d (F j) (e j)) ∧
        RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] P) = Ideal.span (Set.range F) := by
  classical
  obtain ⟨n, x, d, hx, hgen⟩ := exists_fin_homogeneous_adjoin_eq_top grading
  let : GradedAlgebra (weightedHomogeneousSubmodule k d) :=
    MvPolynomial.weightedGradedAlgebra k d
  have hsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P) := by
    intro y
    have : y ∈ (aeval x : MvPolynomial (Fin n) k →ₐ[k] P).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, hgen]; exact Algebra.mem_top
    exact this
  let f := aevalGradedRingHom grading x d hx
  have hker : (RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] P)).IsHomogeneous
      (weightedHomogeneousSubmodule k d) := (HomogeneousIdeal.comap f ⊥).isHomogeneous
  have hfg : (RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] P)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨S, hShom, hSspan⟩ := hker.exists_finset_homogeneous_span_eq hfg
  let eqv := S.equivFin
  refine ⟨n, d, x, hx, hsurj,
    fun _ _ hF => aeval_mem_grading_of_isWeightedHomogeneous grading hx hF,
    S.card, fun j => ((eqv.symm j : ℕ × MvPolynomial (Fin n) k)).1,
    fun j => ((eqv.symm j : ℕ × MvPolynomial (Fin n) k)).2, fun j => ?_, ?_⟩
  · exact hShom _ (eqv.symm j).2
  · rw [← hSspan]
    congr 1
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨eqv ⟨q, hq⟩, by simp⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, (eqv.symm j).2, rfl⟩

end GradedAlgebra

end
