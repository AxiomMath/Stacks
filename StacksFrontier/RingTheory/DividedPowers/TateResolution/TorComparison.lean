module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedChainComplex
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedHomology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorComputation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowers

/-!
# The homology of a base-changed Tate resolution is Tor

Let `R` be a commutative ring, let `S` and `T` be commutative `R`-algebras, and let `A` be a Tate
resolution of `S`. The homology of the base change `T ⊗[R] A` carries a strictly
graded-commutative graded `R`-algebra structure with divided powers, by
`DividedPowers.TateResolution.exists_dividedPowerStructure_homology_tateResolution`. Tag 09PQ
asserts that structure on `Tor_*^R(S, T)` instead, and the step that is missing there is the
identification, in each degree `n`, of the degree-`n` piece of the homology of `T ⊗[R] A` with
`Tor_n^R(S, T)`. This file supplies that identification.

The three comparisons named in the module documentation of
`StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowers` are carried out as
follows.

(a) `baseChangeGradeEquiv` identifies the degree-`n` piece `(𝒜 n).baseChange T` of `T ⊗[R] A`
with `T ⊗[R] 𝒜 n`, and `baseChangeGradeEquiv_gradeDifferential` is the commuting square against
the differentials. The comparison is an isomorphism because `𝒜 n` is a *direct summand* of `A`:
the grading supplies a projection `gradeProjection` retracting the inclusion of `𝒜 n`, so the
base change of that inclusion is split and in particular injective. No flatness is used.

(b) `baseChangeComplexIso` assembles the degreewise comparisons into an isomorphism between the
complex of homogeneous pieces of `T ⊗[R] A` and the complex of homogeneous pieces of `A`
tensored with `T`, which is the complex whose homology
`DividedPowers.TateResolution.Resolution.torIsoHomology` identifies with `Tor_*^R(S, T)`.

(c) `gradeHomologyEquivCoefficientHomology` and `gradedChainComplexHomologyEquiv` identify the
degree-`n` graded homology `gradeHomology` of `T ⊗[R] A` with the degree-`n` homology of that
complex; this is the homogeneity of the differential. Composing (a), (b) and (c) with
`torIsoHomology` gives `gradeHomologyEquivTor`.

Finally, the total homology is shown to be the direct sum of its graded pieces
(`directSumTotalHomologyGradeEquiv`) — the pieces span because the homogeneous components of a
cycle are cycles, and they are independent because a homogeneous element that is a boundary is
the differential of a homogeneous element one degree up — so the degreewise identification
assembles into `torDirectSumEquivHomology`, an identification of `⨁ n, Tor_n^R(S, T)` with the
homology algebra that carries the `n`-th summand onto the degree-`n` graded piece.

## Main definitions

* `DividedPowers.TateResolution.gradeProjection` — the projection of a graded algebra onto a
  homogeneous piece.
* `DividedPowers.TateResolution.baseChangeGradeEquiv` — the summand comparison, comparison (a).
* `DividedPowers.TateResolution.baseChangeComplexIso` — the comparison of complexes,
  comparison (b).
* `DividedPowers.TateResolution.directSumTotalHomologyGradeEquiv` — the total homology as the
  direct sum of its graded pieces.
* `DividedPowers.TateResolution.torGraded` — the family `n ↦ Tor_n^R(S, T)`.

## Main results

* `DividedPowers.TateResolution.baseChangeGradeEquiv_gradeDifferential` — the summand comparison
  commutes with the differentials.
* `DividedPowers.TateResolution.gradeHomologyEquivComplexHomology` — the degreewise homology
  comparison, comparisons (b) and (c).
* `DividedPowers.TateResolution.gradeHomologyEquivTor` — the degree-`n` graded homology of
  `T ⊗[R] A` is `Tor_n^R(S, T)`.
* `DividedPowers.TateResolution.torDirectSumEquivHomology` and
  `DividedPowers.TateResolution.map_torDirectSumEquivHomology_range_lof` — the direct sum of the
  `Tor_n^R(S, T)` is the homology of `T ⊗[R] A`, degreewise.

### Where Tag 09PQ is carried

Tag 09PQ asks for the divided power structure *on* `⨁ n, Tor_n^R(S, T)`. The comparisons here
are its input; the transport itself is
`DividedPowers.TateResolution.exists_dividedPowerStructure_torDirectSum` in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.TorDividedPowerAlgebra`, and the tag, with
the independence of the Tate resolution, is carried by
`DividedPowers.TateResolution.exists_dividedPowerStructure_torDirectSum_forall_resolution` in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.TorIndependence`. Nothing in this file
carries it, the comparisons being statements about homology and `Tor` and not about divided
powers.

The transport does not go through `torDirectSumEquivHomology` as an isomorphism of rings. It
cannot: `DividedPowers.TateResolution.HasInducedDividedPowers` quantifies the ring and algebra
on the homology existentially, and the three additive clauses it records — on `0`, on sums and
on scalar multiples of a class — elaborate against the canonical instances of the quotient
`cycles ⧸ boundaries`, so they are theorems of the canonical structure and do not pin the
existential one. Its `1`, `*` and `dpow` clauses are the informative ones, the quotient having
no canonical multiplication. The transport is therefore built on `⨁ n, Tor_n^R(S, T)` with that
direct sum's own additive structure, pushing each axiom through the surjective class map.

## Implementation notes

The summand comparison is stated for the grading `restrictGrade R fun i ↦ (𝒜 i).baseChange T`
rather than for `(𝒜 n).baseChange T` directly: the latter is a `T`-submodule, and the `R`-module
structure in which the comparison is `R`-linear is exactly the restriction of scalars. The two
subtypes are definitionally equal, but stating the comparison with the restricted grading keeps
every later rewrite type-correct.

The structure data of a `DividedPowers.TateResolution.Resolution` are fields rather than
instances. They are registered as local instances for this file, so that `Res.grade` and
`T ⊗[R] Res.A` elaborate without a `letI` in every statement.

`torGraded` is an `abbrev` so that the module structure of each `Tor_n^R(S, T)` is found by
instance search.

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
* [Stacks Project, Tag 09PL](https://stacks.math.columbia.edu/tag/09PL)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open TensorProduct CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

section Summand

variable {R : Type u} {A : Type v} {T : Type w} [CommRing R] [Ring A] [CommRing T]
  [Algebra R A] [Algebra R T] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The projection of a graded algebra onto its degree-`n` homogeneous piece, as a retraction
of the inclusion of that piece. -/
public def gradeProjection (n : ℕ) : A →ₗ[R] ↥(𝒜 n) :=
  (GradedAlgebra.proj 𝒜 n).codRestrict (𝒜 n) fun x => by
    rw [GradedAlgebra.proj_apply]
    exact (DirectSum.decompose 𝒜 x n).property

/-- The projection is the identity on the degree-`n` piece. -/
@[simp]
public theorem gradeProjection_coe (n : ℕ) (x : ↥(𝒜 n)) :
    gradeProjection 𝒜 n (x : A) = x := by
  apply Subtype.ext
  change GradedAlgebra.proj 𝒜 n (x : A) = (x : A)
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 x.property]

/-- The degree-`n` piece is a direct summand: the projection retracts its inclusion. -/
public theorem gradeProjection_comp_subtype (n : ℕ) :
    (gradeProjection 𝒜 n).comp (𝒜 n).subtype = LinearMap.id :=
  LinearMap.ext fun x => gradeProjection_coe 𝒜 n x

/-- The base change of the projection retracts the base change of the inclusion. -/
public theorem baseChange_gradeProjection_baseChange_subtype (n : ℕ) (u : T ⊗[R] ↥(𝒜 n)) :
    LinearMap.baseChange T (gradeProjection 𝒜 n)
        (LinearMap.baseChange T (𝒜 n).subtype u) = u := by
  have h : (LinearMap.baseChange T (gradeProjection 𝒜 n)).comp
      (LinearMap.baseChange T (𝒜 n).subtype) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, gradeProjection_comp_subtype, LinearMap.baseChange_id]
  simpa using LinearMap.congr_fun h u

/-- **The base change of the inclusion of a homogeneous piece is injective.** The piece is a
direct summand, so the inclusion is split and its base change is split as well. -/
public theorem injective_baseChange_subtype (n : ℕ) :
    Function.Injective (LinearMap.baseChange T (𝒜 n).subtype) :=
  Function.LeftInverse.injective
    (g := LinearMap.baseChange T (gradeProjection 𝒜 n))
    (baseChange_gradeProjection_baseChange_subtype 𝒜 n)

/-- The base change of the projection onto a homogeneous piece retracts the base change of the
inclusion, on the base-changed submodule. -/
public theorem baseChange_subtype_baseChange_gradeProjection (n : ℕ) {z : T ⊗[R] A}
    (hz : z ∈ (𝒜 n).baseChange T) :
    LinearMap.baseChange T (𝒜 n).subtype
        (LinearMap.baseChange T (gradeProjection 𝒜 n) z) = z := by
  obtain ⟨u, rfl⟩ := hz
  rw [baseChange_gradeProjection_baseChange_subtype]

/-- The base change of a homogeneous piece, included into the base change of the algebra. -/
public def toBaseChangeGrade (n : ℕ) :
    T ⊗[R] ↥(𝒜 n) →ₗ[R] ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) n) :=
  ((LinearMap.baseChange T (𝒜 n).subtype).restrictScalars R).codRestrict _ fun u => ⟨u, rfl⟩

/-- The degree-`n` part of the base change, projected into the base change of the degree-`n`
piece. -/
public def fromBaseChangeGrade (n : ℕ) :
    ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) n) →ₗ[R] T ⊗[R] ↥(𝒜 n) :=
  ((LinearMap.baseChange T (gradeProjection 𝒜 n)).restrictScalars R).comp
    (restrictGrade R (fun i => (𝒜 i).baseChange T) n).subtype

/-- **The summand comparison.** The degree-`n` piece of the base change of a graded algebra —
the submodule `(𝒜 n).baseChange T` of `T ⊗[R] A`, read over the base ring — is the tensor
product `T ⊗[R] 𝒜 n`. The inverse is the base change of the inclusion of `𝒜 n`, which is
injective because `𝒜 n` is a direct summand of `A`. -/
public def baseChangeGradeEquiv (n : ℕ) :
    ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) n) ≃ₗ[R] T ⊗[R] ↥(𝒜 n) :=
  LinearEquiv.ofLinearMap (fromBaseChangeGrade (T := T) 𝒜 n) (toBaseChangeGrade (T := T) 𝒜 n)
    (LinearMap.ext fun u => baseChange_gradeProjection_baseChange_subtype 𝒜 n u)
    (LinearMap.ext fun x => Subtype.ext
      (baseChange_subtype_baseChange_gradeProjection 𝒜 n x.property))

/-- The inverse of the summand comparison is the base change of the inclusion. -/
@[simp]
public theorem coe_baseChangeGradeEquiv_symm (n : ℕ) (u : T ⊗[R] ↥(𝒜 n)) :
    (((baseChangeGradeEquiv (T := T) 𝒜 n).symm u :
        ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) n)) : T ⊗[R] A) =
      LinearMap.baseChange T (𝒜 n).subtype u := rfl

/-- The summand comparison does not change the underlying element of `T ⊗[R] A`. -/
@[simp]
public theorem baseChange_subtype_baseChangeGradeEquiv (n : ℕ)
    (x : ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) n)) :
    LinearMap.baseChange T (𝒜 n).subtype (baseChangeGradeEquiv (T := T) 𝒜 n x) =
      (x : T ⊗[R] A) :=
  baseChange_subtype_baseChange_gradeProjection 𝒜 n x.property

section Differential

variable (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]

/-- **The summand comparison is compatible with the differentials**, read inside the ambient
base change `T ⊗[R] A`. -/
public theorem baseChange_subtype_baseChange_gradeDifferential (n : ℕ)
    (x : ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) (n + 1))) :
    LinearMap.baseChange T (𝒜 n).subtype
        (LinearMap.baseChange T (gradeDifferential 𝒜 d n)
          (baseChangeGradeEquiv (T := T) 𝒜 (n + 1) x)) =
      LinearMap.baseChange T d (x : T ⊗[R] A) := by
  rw [← baseChange_gradeDifferential 𝒜 d n, baseChange_subtype_baseChangeGradeEquiv]

variable [IsDifferentialGradedAlgebra (restrictGrade R fun i => (𝒜 i).baseChange T)
  ((LinearMap.baseChange T d).restrictScalars R)]

/-- **Comparison (a): the summand comparison commutes with the differentials.** The square
formed by `baseChangeGradeEquiv` in degrees `n + 1` and `n`, the differential
`gradeDifferential` of the base-changed algebra, and the base change of the differential
`gradeDifferential 𝒜 d n`, commutes. -/
public theorem baseChangeGradeEquiv_gradeDifferential (n : ℕ)
    (x : ↥(restrictGrade R (fun i => (𝒜 i).baseChange T) (n + 1))) :
    baseChangeGradeEquiv (T := T) 𝒜 n
        (gradeDifferential (restrictGrade R fun i => (𝒜 i).baseChange T)
          ((LinearMap.baseChange T d).restrictScalars R) n x) =
      LinearMap.baseChange T (gradeDifferential 𝒜 d n)
        (baseChangeGradeEquiv (T := T) 𝒜 (n + 1) x) := by
  apply injective_baseChange_subtype (T := T) 𝒜 n
  rw [baseChange_subtype_baseChangeGradeEquiv,
    baseChange_subtype_baseChange_gradeDifferential]
  rfl

end Differential

/-- The coefficients of the base ring land in degree zero of the base change. -/
public theorem algebraMap_mem_baseChange_zero (r : R) :
    algebraMap R (T ⊗[R] A) r ∈ restrictGrade R (fun i => (𝒜 i).baseChange T) 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  refine Submodule.smul_mem _ r ?_
  have h : (1 : T ⊗[R] A) = (1 : T) ⊗ₜ[R] (1 : A) := rfl
  rw [h]
  exact Submodule.tmul_mem_baseChange_of_mem (1 : T) (SetLike.GradedOne.one_mem (A := 𝒜))

end Summand

section CoefficientBridge

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d] (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

/-- The degree-`n` cycles as a submodule of the degree-`n` piece and the degree-`n` cycles as a
submodule of the algebra are the same module. -/
public def gradeCyclesEquivCoefficientCycles (n : ℕ) :
    ↥(gradeCycles 𝒜 d n) ≃ₗ[R] ↥(coefficientCycles 𝒜 d h0 n) where
  toFun x := ⟨((x : ↥(𝒜 n)) : A), (x : ↥(𝒜 n)).2, (mem_gradeCycles_iff 𝒜 d).mp x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨(y : A), y.2.1⟩, (mem_gradeCycles_iff 𝒜 d).mpr y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the two models of the cycles does not change the element. -/
@[simp]
public theorem coe_gradeCyclesEquivCoefficientCycles (n : ℕ) (x : ↥(gradeCycles 𝒜 d n)) :
    ((gradeCyclesEquivCoefficientCycles 𝒜 d h0 n x : ↥(coefficientCycles 𝒜 d h0 n)) : A) =
      ((x : ↥(𝒜 n)) : A) := rfl

/-- Under that identification the degree-`n` boundaries correspond. -/
public theorem map_gradeCyclesEquivCoefficientCycles_gradeBoundaries (n : ℕ) :
    Submodule.map (gradeCyclesEquivCoefficientCycles 𝒜 d h0 n :
        ↥(gradeCycles 𝒜 d n) →ₗ[R] ↥(coefficientCycles 𝒜 d h0 n))
        ((gradeBoundaries 𝒜 d n).comap (gradeCycles 𝒜 d n).subtype) =
      (coefficientBoundaries 𝒜 d h0 n).comap (coefficientCycles 𝒜 d h0 n).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_coefficientBoundaries 𝒜 d h0).mpr ((mem_gradeBoundaries_iff 𝒜 d).mp hx)
  · intro hy
    exact ⟨(gradeCyclesEquivCoefficientCycles 𝒜 d h0 n).symm y,
      (mem_gradeBoundaries_iff 𝒜 d).mpr ((mem_coefficientBoundaries 𝒜 d h0).mp hy),
      (gradeCyclesEquivCoefficientCycles 𝒜 d h0 n).apply_symm_apply y⟩

/-- The degree-`n` homology of a differential graded algebra, as a quotient of the cycles
inside the degree-`n` piece, is its degree-`n` homology as a quotient of the cycles inside the
algebra. -/
public def gradeHomologyEquivCoefficientHomology (n : ℕ) :
    gradeHomology 𝒜 d n ≃ₗ[R] coefficientHomology 𝒜 d h0 n :=
  Submodule.Quotient.equiv _ _ (gradeCyclesEquivCoefficientCycles 𝒜 d h0 n)
    (map_gradeCyclesEquivCoefficientCycles_gradeBoundaries 𝒜 d h0 n)

/-- The identification of the two models of the homology sends the class of a cycle to the
class of that cycle. -/
@[simp]
public theorem gradeHomologyEquivCoefficientHomology_mk (n : ℕ) (x : ↥(gradeCycles 𝒜 d n)) :
    gradeHomologyEquivCoefficientHomology 𝒜 d h0 n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (gradeCyclesEquivCoefficientCycles 𝒜 d h0 n x) := rfl

end CoefficientBridge

section TermComparison

variable {R : Type u} {A : Type v} {T : Type w} [CommRing R] [Ring A] [CommRing T]
  [Algebra R A] [Algebra R T] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- Over the base ring as coefficient algebra, a homogeneous piece is itself. -/
public theorem coefficientGrade_eq_grade (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0) (n : ℕ) :
    coefficientGrade 𝒜 h0 n = 𝒜 n :=
  Submodule.ext fun _ => Iff.rfl

/-- `𝒜 n ⊗[R] T`, included into the base change `T ⊗[R] A`. -/
public def rTensorGradeInclusion (n : ℕ) : ↥(𝒜 n) ⊗[R] T →ₗ[R] T ⊗[R] A :=
  ((LinearMap.baseChange T (𝒜 n).subtype).restrictScalars R).comp
    (TensorProduct.comm R ↥(𝒜 n) T).toLinearMap

omit [GradedAlgebra 𝒜] in
/-- The inclusion of `𝒜 n ⊗[R] T` into `T ⊗[R] A`, computed by swapping the factors and base
changing the inclusion of `𝒜 n`. -/
@[simp]
public theorem rTensorGradeInclusion_apply (n : ℕ) (u : ↥(𝒜 n) ⊗[R] T) :
    rTensorGradeInclusion (T := T) 𝒜 n u =
      LinearMap.baseChange T (𝒜 n).subtype (TensorProduct.comm R ↥(𝒜 n) T u) := rfl

/-- The inclusion of `𝒜 n ⊗[R] T` into `T ⊗[R] A` is injective: up to the swap of factors it
is the base change of the split inclusion of a homogeneous piece. -/
public theorem injective_rTensorGradeInclusion (n : ℕ) :
    Function.Injective (rTensorGradeInclusion (T := T) 𝒜 n) :=
  (injective_baseChange_subtype 𝒜 n).comp (TensorProduct.comm R ↥(𝒜 n) T).injective

/-- **Comparison (b): the degree-`n` term.** The degree-`n` piece of the base change, as a
module over the base ring sitting in degree zero, is `𝒜 n ⊗[R] T`. -/
public def baseChangeCoefficientGradeEquiv (n : ℕ) :
    ↥(coefficientGrade (restrictGrade R fun i => (𝒜 i).baseChange T)
        (algebraMap_mem_baseChange_zero (T := T) 𝒜) n) ≃ₗ[R] ↥(𝒜 n) ⊗[R] T :=
  (LinearEquiv.ofEq _ _
      (coefficientGrade_eq_grade (restrictGrade R fun i => (𝒜 i).baseChange T)
        (algebraMap_mem_baseChange_zero (T := T) 𝒜) n)).trans
    ((baseChangeGradeEquiv (T := T) 𝒜 n).trans
      (TensorProduct.comm R ↥(𝒜 n) T).symm)

/-- The degree-`n` term comparison, unfolded into the summand comparison followed by the swap
of the two tensor factors. -/
@[simp]
public theorem baseChangeCoefficientGradeEquiv_apply (n : ℕ)
    (x : ↥(coefficientGrade (restrictGrade R fun i => (𝒜 i).baseChange T)
      (algebraMap_mem_baseChange_zero (T := T) 𝒜) n)) :
    baseChangeCoefficientGradeEquiv (T := T) 𝒜 n x =
      (TensorProduct.comm R ↥(𝒜 n) T).symm
        (baseChangeGradeEquiv (T := T) 𝒜 n
          (LinearEquiv.ofEq _ _
            (coefficientGrade_eq_grade (restrictGrade R fun i => (𝒜 i).baseChange T)
              (algebraMap_mem_baseChange_zero (T := T) 𝒜) n) x)) := rfl

/-- The degree-`n` term comparison does not change the underlying element of `T ⊗[R] A`. -/
public theorem rTensorGradeInclusion_baseChangeCoefficientGradeEquiv (n : ℕ)
    (x : ↥(coefficientGrade (restrictGrade R fun i => (𝒜 i).baseChange T)
      (algebraMap_mem_baseChange_zero (T := T) 𝒜) n)) :
    rTensorGradeInclusion (T := T) 𝒜 n (baseChangeCoefficientGradeEquiv (T := T) 𝒜 n x) =
      (x : T ⊗[R] A) := by
  rw [baseChangeCoefficientGradeEquiv_apply, rTensorGradeInclusion_apply,
    LinearEquiv.apply_symm_apply, baseChange_subtype_baseChangeGradeEquiv]
  rfl

omit [GradedAlgebra 𝒜] in
/-- Reading `𝒜 n ⊗[R] T` inside `T ⊗[R] A` turns `rTensor` of a map into its base change. -/
public theorem rTensorGradeInclusion_rTensor {B : ℕ → Submodule R A} (m n : ℕ)
    (f : ↥(𝒜 m) →ₗ[R] ↥(B n)) (u : ↥(𝒜 m) ⊗[R] T) :
    LinearMap.baseChange T (B n).subtype
        (TensorProduct.comm R ↥(B n) T (LinearMap.rTensor T f u)) =
      LinearMap.baseChange T ((B n).subtype.comp f)
        (TensorProduct.comm R ↥(𝒜 m) T u) := by
  induction u using TensorProduct.inductionOn with
  | tmul a t => simp
  | add x y hx hy => simp [hx, hy]

/-- The degree-`n` term comparison, read inside `T ⊗[R] A`. -/
public theorem comm_baseChangeCoefficientGradeEquiv (n : ℕ)
    (x : ↥(coefficientGrade (restrictGrade R fun i => (𝒜 i).baseChange T)
      (algebraMap_mem_baseChange_zero (T := T) 𝒜) n)) :
    TensorProduct.comm R ↥(𝒜 n) T (baseChangeCoefficientGradeEquiv (T := T) 𝒜 n x) =
      baseChangeGradeEquiv (T := T) 𝒜 n
        (LinearEquiv.ofEq _ _
          (coefficientGrade_eq_grade (restrictGrade R fun i => (𝒜 i).baseChange T)
            (algebraMap_mem_baseChange_zero (T := T) 𝒜) n) x) := by
  rw [baseChangeCoefficientGradeEquiv_apply, LinearEquiv.apply_symm_apply]

section TermDifferential

variable (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
  [IsDifferentialGradedAlgebra (restrictGrade R fun i => (𝒜 i).baseChange T)
    ((LinearMap.baseChange T d).restrictScalars R)]

/-- **Comparison (b): the term comparison commutes with the differentials.** The differential
of the complex of homogeneous pieces of the base change corresponds, under the term comparison,
to the differential of the complex of homogeneous pieces tensored with `T`. -/
public theorem rTensor_gradeDifferential_baseChangeCoefficientGradeEquiv (n : ℕ)
    (x : ↥(coefficientGrade (restrictGrade R fun i => (𝒜 i).baseChange T)
      (algebraMap_mem_baseChange_zero (T := T) 𝒜) (n + 1))) :
    LinearMap.rTensor T (gradeDifferential 𝒜 d n)
        (baseChangeCoefficientGradeEquiv (T := T) 𝒜 (n + 1) x) =
      baseChangeCoefficientGradeEquiv (T := T) 𝒜 n
        (coefficientDifferential (restrictGrade R fun i => (𝒜 i).baseChange T)
          ((LinearMap.baseChange T d).restrictScalars R)
          (algebraMap_mem_baseChange_zero (T := T) 𝒜) n x) := by
  apply injective_rTensorGradeInclusion (T := T) 𝒜 n
  rw [rTensorGradeInclusion_apply, rTensorGradeInclusion_rTensor,
    LinearMap.baseChange_comp, LinearMap.comp_apply,
    comm_baseChangeCoefficientGradeEquiv,
    baseChange_subtype_baseChange_gradeDifferential,
    rTensorGradeInclusion_baseChangeCoefficientGradeEquiv,
    LinearEquiv.coe_ofEq_apply, coe_coefficientDifferential]
  rfl

end TermDifferential

end TermComparison

section HomologyDecomposition

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]


/-- **The homogeneous components of a cycle are cycles.** -/
public theorem d_decompose_eq_zero {x : A} (hx : d x = 0) (n : ℕ) :
    d ((DirectSum.decompose 𝒜 x n : 𝒜 n) : A) = 0 := by
  match n with
  | 0 =>
      exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
        (DirectSum.decompose 𝒜 x 0).property
  | m + 1 => rw [differential_decompose_succ 𝒜 d x m, hx]; simp

/-- The degree-`n` homogeneous component of a cycle, as a cycle. -/
public def cycleComponent {x : A} (hx : d x = 0) (n : ℕ) : cycles d :=
  ⟨((DirectSum.decompose 𝒜 x n : 𝒜 n) : A),
    LinearMap.mem_ker.mpr (d_decompose_eq_zero 𝒜 d hx n)⟩

/-- The underlying element of the degree-`n` component of a cycle. -/
@[simp]
public theorem coe_cycleComponent {x : A} (hx : d x = 0) (n : ℕ) :
    ((cycleComponent 𝒜 d hx n : cycles d) : A) =
      ((DirectSum.decompose 𝒜 x n : 𝒜 n) : A) := rfl

/-- **The graded pieces of the total homology span it**: every homology class is a sum of classes
of homogeneous cycles. -/
public theorem iSup_totalHomologyGrade : iSup (totalHomologyGrade 𝒜 d) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro z -
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries (𝒜 := 𝒜) d) z
  have hx : d (x : A) = 0 := x.property
  have hsum : x = ∑ j ∈ (DirectSum.decompose 𝒜 (x : A)).support,
      cycleComponent 𝒜 d hx j := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using (DirectSum.sum_support_decompose 𝒜 (x : A)).symm
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ?_
  exact Submodule.subset_span
    ⟨cycleComponent 𝒜 d hx j, (DirectSum.decompose 𝒜 (x : A) j).property, rfl⟩

/-- A class in the span of the graded pieces away from degree `i` is the class of a cycle whose
degree-`i` component vanishes. -/
private theorem exists_rep_decompose_eq_zero (i : ℕ) {z : Homology (𝒜 := 𝒜) d}
    (hz : z ∈ ⨆ j, ⨆ (_ : j ≠ i), totalHomologyGrade 𝒜 d j) :
    ∃ w : cycles d, (Submodule.Quotient.mk w : Homology (𝒜 := 𝒜) d) = z ∧
      ((DirectSum.decompose 𝒜 (w : A) i : 𝒜 i) : A) = 0 := by
  classical
  induction hz using Submodule.iSup_induction' with
  | mem j z hzj =>
      by_cases hj : j = i
      · subst hj
        rw [iSup_neg (fun h => h rfl), Submodule.mem_bot] at hzj
        exact ⟨0, by rw [hzj]; simp, by simp⟩
      · rw [iSup_pos hj, totalHomologyGrade_eq_range] at hzj
        obtain ⟨y, rfl⟩ := hzj
        refine ⟨gradeCyclesToCycles 𝒜 d j y, rfl, ?_⟩
        rw [coe_gradeCyclesToCycles, DirectSum.decompose_coe, DirectSum.of_apply]
        simp [hj]
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ iha ihb =>
      obtain ⟨wa, hwa, hwa0⟩ := iha
      obtain ⟨wb, hwb, hwb0⟩ := ihb
      refine ⟨wa + wb, ?_, ?_⟩
      · rw [← hwa, ← hwb]; rfl
      · rw [Submodule.coe_add, DirectSum.decompose_add, DirectSum.add_apply,
          Submodule.coe_add, hwa0, hwb0, add_zero]

/-- **The graded pieces of the total homology are independent.** A homogeneous class that lies in
the span of the other degrees is the class of a homogeneous cycle which, by
`differential_decompose_succ`, is a boundary. -/
public theorem iSupIndep_totalHomologyGrade : iSupIndep (totalHomologyGrade 𝒜 d) := by
  classical
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro z hzi hzsup
  obtain ⟨w, hwz, hwi⟩ := exists_rep_decompose_eq_zero 𝒜 d i hzsup
  rw [totalHomologyGrade_eq_range] at hzi
  obtain ⟨y, rfl⟩ := hzi
  have hquot : (Submodule.Quotient.mk w : Homology (𝒜 := 𝒜) d) =
      Submodule.Quotient.mk (gradeCyclesToCycles 𝒜 d i y) := hwz
  obtain ⟨u, hu⟩ := (mem_boundaries_iff (𝒜 := 𝒜) d (w - gradeCyclesToCycles 𝒜 d i y)).mp
    ((Submodule.Quotient.eq (boundaries (𝒜 := 𝒜) d)).mp hquot)
  have hcomp : ((DirectSum.decompose 𝒜 (d u) i : 𝒜 i) : A) =
      -((gradeCyclesToCycles 𝒜 d i y : cycles d) : A) := by
    rw [show d u = (w : A) - ((gradeCyclesToCycles 𝒜 d i y : cycles d) : A) by
      simpa using hu, DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      hwi, coe_gradeCyclesToCycles, DirectSum.decompose_coe, DirectSum.of_eq_same,
      zero_sub]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [mem_boundaries_iff]
  refine ⟨-((DirectSum.decompose 𝒜 u (i + 1) : 𝒜 (i + 1)) : A), ?_⟩
  rw [map_neg, differential_decompose_succ 𝒜 d u i, hcomp, neg_neg]

/-- The total homology decomposes as the direct sum of its graded pieces. -/
@[instance_reducible]
public def totalHomologyGradeDecomposition :
    DirectSum.Decomposition (totalHomologyGrade 𝒜 d) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_totalHomologyGrade 𝒜 d) (iSup_totalHomologyGrade 𝒜 d)).chooseDecomposition _

/-- **The total homology is the direct sum of its graded pieces.** -/
public def directSumTotalHomologyGradeEquiv :
    DirectSum ℕ (fun n => ↥(totalHomologyGrade 𝒜 d n)) ≃ₗ[R] Homology (𝒜 := 𝒜) d :=
  letI := totalHomologyGradeDecomposition 𝒜 d
  (DirectSum.decomposeLinearEquiv (totalHomologyGrade 𝒜 d)).symm

/-- The decomposition of the homology sends the `n`-th summand to the degree-`n` graded
piece. -/
@[simp]
public theorem directSumTotalHomologyGradeEquiv_lof (n : ℕ)
    (x : ↥(totalHomologyGrade 𝒜 d n)) :
    directSumTotalHomologyGradeEquiv 𝒜 d
        (DirectSum.lof R ℕ (fun i => ↥(totalHomologyGrade 𝒜 d i)) n x) =
      (x : Homology (𝒜 := 𝒜) d) :=
  let := totalHomologyGradeDecomposition 𝒜 d
  DirectSum.decomposeLinearEquiv_symm_lof (totalHomologyGrade 𝒜 d) n x

end HomologyDecomposition

section DirectSumCongr

variable {R : Type u} {M : ℕ → Type v} {N : ℕ → Type v} [CommRing R]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- A family of linear equivalences induces a linear equivalence of direct sums. -/
public def directSumCongr (e : ∀ n, M n ≃ₗ[R] N n) :
    DirectSum ℕ M ≃ₗ[R] DirectSum ℕ N :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule R ℕ _ fun n => (DirectSum.lof R ℕ N n).comp (e n).toLinearMap)
    (DirectSum.toModule R ℕ _ fun n => (DirectSum.lof R ℕ M n).comp (e n).symm.toLinearMap)
    (DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => by
      simp [DirectSum.toModule_lof])
    (DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => by
      simp [DirectSum.toModule_lof])

/-- The induced equivalence of direct sums acts summandwise. -/
@[simp]
public theorem directSumCongr_lof (e : ∀ n, M n ≃ₗ[R] N n) (n : ℕ) (x : M n) :
    directSumCongr e (DirectSum.lof R ℕ M n x) = DirectSum.lof R ℕ N n (e n x) :=
  DirectSum.toModule_lof R n x

end DirectSumCongr

section TorGraded

/-- **The graded Tor module**: the family `n ↦ Tor_n^R(S, T)`. It is an `abbrev` so that the
module structure of each `Tor_n^R(S, T)` is found by instance search. -/
public abbrev torGraded (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (n : ℕ) : Type u :=
  ↥(((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))

end TorGraded

section ResolutionComparison

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

variable {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {φ : MvPolynomial σ R →ₐ[R] S} (Res : Resolution R S σ φ)
  (T : Type u) [CommRing T] [Algebra R T]

/-- The restricted differential of a resolution is the differential between two homogeneous
pieces of the underlying differential graded algebra. -/
public theorem differentialAt_eq_gradeDifferential (n : ℕ) :
    Res.differentialAt n = gradeDifferential Res.grade Res.differential n := rfl

/-- **The base change of a Tate resolution is again a differential graded algebra.** -/
public theorem isDifferentialGradedAlgebra_baseChange :
    IsDifferentialGradedAlgebra (restrictGrade R fun i => (Res.grade i).baseChange T)
      ((LinearMap.baseChange T Res.differential).restrictScalars R) := by
  obtain ⟨hcomm, γ', hsq, hz, hm, hmul, -, -⟩ :=
    exists_dividedPowerStructure_baseChange (R' := T) Res.grade Res.gamma Res.differential
      (LinearMap.ext fun x => IsDifferentialGradedAlgebra.d_sq_zero
        (𝒜 := Res.grade) (d := Res.differential) x)
      (fun _ hx => IsDifferentialGradedAlgebra.d_grade_zero
        (𝒜 := Res.grade) (d := Res.differential) hx)
      (fun _ _ hx => IsDifferentialGradedAlgebra.d_mem
        (𝒜 := Res.grade) (d := Res.differential) hx)
      (fun _ _ _ _ hx hy => IsDifferentialGradedAlgebra.leibniz
        (𝒜 := Res.grade) (d := Res.differential) hx hy)
  let : IsStrictlyGradedComm fun i => (Res.grade i).baseChange T := hcomm
  let : IsDifferentialGradedAlgebra (fun i => (Res.grade i).baseChange T)
      (LinearMap.baseChange T Res.differential) :=
    isDifferentialGradedAlgebra_of_axioms _ _ hsq hz hm hmul
  exact isDifferentialGradedAlgebra_restrictGrade (S := R) _ _

attribute [local instance] isDifferentialGradedAlgebra_baseChange

/-- The degree-`n` term of the complex of the resolution tensored with `T`. -/
public theorem tensorComplex_X (n : ℕ) :
    ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Res.complex).X n =
      ModuleCat.of R (↥(Res.grade n) ⊗[R] T) := rfl

/-- The differential of the complex of the resolution tensored with `T` is the differential of
the resolution tensored with the identity of `T`. -/
public theorem tensorComplex_d (n : ℕ) (v : ↥(Res.grade (n + 1)) ⊗[R] T) :
    (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Res.complex).d (n + 1) n).hom v =
      LinearMap.rTensor T (Res.differentialAt n) v := by
  change ((Res.complex.d (n + 1) n ▷ ModuleCat.of R T).hom) v = _
  rw [ModuleCat.hom_whiskerRight]
  simp only [Resolution.complex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- **Comparison (b): the complex of homogeneous pieces of the base change is the complex of
homogeneous pieces of the resolution, tensored with `T`.** In each degree the comparison is the
summand comparison `baseChangeCoefficientGradeEquiv`, and the squares commute by
`baseChangeGradeEquiv_gradeDifferential`. -/
public def baseChangeComplexIso :
    gradedChainComplex (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)
        (algebraMap_mem_baseChange_zero (T := T) Res.grade) ≅
      (((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj Res.complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (baseChangeCoefficientGradeEquiv (T := T) Res.grade n).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      refine ModuleCat.hom_ext ?_
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, gradedChainComplex_d]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      exact (tensorComplex_d Res T j _).trans
        (rTensor_gradeDifferential_baseChangeCoefficientGradeEquiv Res.grade
          Res.differential j x))

/-- **Comparison (b) and (c): the degreewise homology comparison.** The degree-`n` graded
homology of the base-changed resolution is the degree-`n` homology of the complex of the
resolution tensored with `T` — the complex whose homology `Resolution.torIsoHomology`
identifies with `Tor_n^R(S, T)`. -/
public def gradeHomologyEquivComplexHomology (n : ℕ) :
    gradeHomology (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) n ≃ₗ[R]
      ↥((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).obj
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R T)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Res.complex)) :=
  ((gradeHomologyEquivCoefficientHomology
        (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)
        (algebraMap_mem_baseChange_zero (T := T) Res.grade) n).trans
      (gradedChainComplexHomologyEquiv
        (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R)
        (algebraMap_mem_baseChange_zero (T := T) Res.grade) n).symm).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso
      (baseChangeComplexIso Res T)).toLinearEquiv

/-- **The Tor identification.** For a Tate resolution `A` of `S` along a surjection `φ`, the
degree-`n` graded homology of `T ⊗[R] A` is `Tor_n^R(S, T)`. This is the identification that
Tag 09PQ needs in order to read the divided power structure on the homology of `T ⊗[R] A` as a
structure on `Tor_*^R(S, T)`. -/
public def gradeHomologyEquivTor (hφ : Function.Surjective φ) (n : ℕ) :
    gradeHomology (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) n ≃ₗ[R]
      ↥(((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T)) :=
  (gradeHomologyEquivComplexHomology Res T n).trans
    (Res.torIsoHomology hφ (ModuleCat.of R T) n).symm.toLinearEquiv

/-- **The graded Tor module is the homology of the base-changed resolution.** The direct sum of
the `Tor_n^R(S, T)` is the total homology of `T ⊗[R] A`, by the degreewise identification
`gradeHomologyEquivTor` together with the decomposition of the homology into its graded
pieces. -/
public def torDirectSumEquivHomology (hφ : Function.Surjective φ) :
    DirectSum ℕ (fun n => torGraded R S T n) ≃ₗ[R]
      Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) :=
  (directSumCongr fun n =>
      (gradeHomologyEquivTor Res T hφ n).symm.trans
        (gradeHomologyEquivTotalGrade
          (restrictGrade R fun i => (Res.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R) n)).trans
    (directSumTotalHomologyGradeEquiv _ _)

/-- On the `n`-th summand, the comparison with the homology is the degreewise identification
`gradeHomologyEquivTor` followed by the inclusion of the degree-`n` graded piece. -/
@[simp]
public theorem torDirectSumEquivHomology_lof (hφ : Function.Surjective φ) (n : ℕ)
    (y : torGraded R S T n) :
    torDirectSumEquivHomology Res T hφ
        (DirectSum.lof R ℕ (fun m => torGraded R S T m) n y) =
      ((gradeHomologyEquivTotalGrade
          (restrictGrade R fun i => (Res.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R) n
          ((gradeHomologyEquivTor Res T hφ n).symm y) :
        ↥(totalHomologyGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R) n)) :
        Homology (𝒜 := restrictGrade R fun i => (Res.grade i).baseChange T)
          ((LinearMap.baseChange T Res.differential).restrictScalars R)) := by
  rw [torDirectSumEquivHomology, LinearEquiv.trans_apply, directSumCongr_lof,
    directSumTotalHomologyGradeEquiv_lof]
  rfl

/-- **The comparison is degreewise**: it carries the `n`-th summand of the direct sum onto the
degree-`n` graded piece of the homology, which is the piece carrying the degree-`n` part of the
divided power structure. -/
public theorem map_torDirectSumEquivHomology_range_lof (hφ : Function.Surjective φ) (n : ℕ) :
    Submodule.map (torDirectSumEquivHomology Res T hφ).toLinearMap
        (LinearMap.range (DirectSum.lof R ℕ (fun m => torGraded R S T m) n)) =
      totalHomologyGrade (restrictGrade R fun i => (Res.grade i).baseChange T)
        ((LinearMap.baseChange T Res.differential).restrictScalars R) n := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    rw [torDirectSumEquivHomology_lof]
    exact (gradeHomologyEquivTotalGrade _ _ n ((gradeHomologyEquivTor Res T hφ n).symm y)).property
  · intro hz
    refine ⟨DirectSum.lof R ℕ (fun m => torGraded R S T m) n
      (gradeHomologyEquivTor Res T hφ n
        ((gradeHomologyEquivTotalGrade _ _ n).symm ⟨z, hz⟩)), ⟨_, rfl⟩, ?_⟩
    rw [torDirectSumEquivHomology_lof, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]

end ResolutionComparison

end DividedPowers.TateResolution

end
