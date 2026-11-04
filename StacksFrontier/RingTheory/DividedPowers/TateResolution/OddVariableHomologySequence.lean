module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedHomology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential

/-!
# The long exact sequence of an odd degree-one extension

Let `A` be a strictly graded-commutative nonnegatively graded algebra with a differential `dA`
that lowers degrees by one, and let `f` be an element of degree zero, so that `f` is automatically
a cycle. Adjoining a variable `T` of degree one with `dT = f` produces the extension `A⟨T⟩`, and
this file records the long exact sequence

`… → Hₙ(A) --·f--> Hₙ(A) → Hₙ(A⟨T⟩) → Hₙ₋₁(A) --·f--> Hₙ₋₁(A) → … → H₀(A) → H₀(A⟨T⟩) → 0`

in every degree. The three maps are multiplication by `f`, the map induced by the canonical
inclusion of `A` into `A⟨T⟩`, and the connecting map, which sends the class of a cycle of degree
`n + 1` to the class of its coefficient along `T`. Exactness is stated at each of the three kinds
of spot, as an equality of a range with a kernel, and the right end of the sequence is the
surjectivity in degree zero proved in the degree-zero file.

## Main definitions

* `DividedPowers.TateResolution.OddVariableExtension.variableCoeff` — the coefficient of the
  adjoined variable, as a linear map to the coefficient algebra.
* `DividedPowers.TateResolution.mulOnGradeCycles` and
  `DividedPowers.TateResolution.mulOnGradeHomology` — multiplication by a degree-zero cycle on
  degree-`n` cycles and on degree-`n` homology.
* `DividedPowers.TateResolution.toExtensionOnGradeCycles` and
  `DividedPowers.TateResolution.toExtensionOnGradeHomology` — the maps induced by the canonical
  inclusion into the odd degree-one extension.
* `DividedPowers.TateResolution.connectingOnGradeCycles` and
  `DividedPowers.TateResolution.connectingOnGradeHomology` — the connecting map, extracting the
  coefficient of the adjoined variable.

## Main results

* `DividedPowers.TateResolution.variableCoeff_dExt` — the coefficient of the adjoined variable in
  the differential of a homogeneous element of positive degree is the differential of the
  coefficient of that element.
* `DividedPowers.TateResolution.range_mulOnGradeHomology_eq_ker_toExtension` — exactness at the
  second copy of `Hₙ(A)`.
* `DividedPowers.TateResolution.range_toExtensionOnGradeHomology_eq_ker_connecting` — exactness
  at `Hₙ₊₁(A⟨T⟩)`.
* `DividedPowers.TateResolution.range_connectingOnGradeHomology_eq_ker_mul` — exactness at the
  first copy of `Hₙ(A)`.
* `DividedPowers.TateResolution.surjective_toExtensionOnGradeHomology_zero` — the right end of
  the sequence.
* `DividedPowers.TateResolution.oddExtensionDifferential_inclusion` and
  `DividedPowers.TateResolution.oddExtensionDifferential_generator` — the two prescribed
  values of the explicit differential of Tag 09PM.
* `DividedPowers.TateResolution.oddExtensionDifferential_one_isDGA` — for a degree-one odd
  variable the explicit differential of Tag 09PM is a differential graded algebra structure on
  the extension, with no cycle condition left to supply.
* The same four exactness statements for the differential of Tag 09PM itself, assuming neither a
  differential nor the two equations pinning it down, in the namespace
  `DividedPowers.TateResolution`:
  `range_mulOnGradeHomology_eq_ker_toExtension_oddExtensionDifferential`,
  `range_toExtensionOnGradeHomology_eq_ker_connecting_oddExtensionDifferential`,
  `range_connectingOnGradeHomology_eq_ker_mul_oddExtensionDifferential` and
  `surjective_toExtensionOnGradeHomology_zero_oddExtensionDifferential`.

## Implementation notes

The differential `dExt` on the extension is not constructed here. As in the degree-zero file it
enters as a parameter together with the two equations that pin it down on the two summands of
`A⟨T⟩`: it restricts to `dA` along the inclusion, and it sends the adjoined variable to `f`.
Writing a homogeneous element of degree `m + 1` as `a + bT`, with `a` of degree `m + 1` and `b` of
degree `m`, the Leibniz rule gives `dExt (a + bT) = (dA a + (-1) ^ m • (f * b)) + (dA b) T`; this
is `fst_dExt` together with `variableCoeff_dExt`, and everything else is read off from them. The
formula for the coefficient of `T` needs only that `dExt T` has no component along `T`, which the
grading already forces, so the connecting map and the exactness statement at `Hₙ₊₁(A⟨T⟩)` do not
mention `f` at all.

The second coefficient of the extension lives in the twisted copy `TwistedModule 𝒜 1` of `A`, a
type synonym on which no multiplication is declared. All the computations here take place in `A`
itself, so the coefficient is extracted by the linear map `variableCoeff` landing in `A` rather
than through `TrivSqZeroExt.snd`.

Multiplication by `f` on homology is the unsigned map `a ↦ f * a`: because `f` has degree zero its
Koszul sign against any homogeneous element is `+1`, and strict graded commutativity is used only
to move `f` from the right of a product to the left. The sign `(-1) ^ m` of the Leibniz rule is
genuinely present in the differential of the extension and it is carried through the proofs
unchanged; it never reaches a statement because it is a unit of the coefficient ring, so rescaling
the chain-level witness of a range or kernel membership by it changes no submodule. For the same
reason the connecting map is taken to be the unsigned `a + bT ↦ b` rather than one of its signed
variants: a sign convention composes an automorphism onto the connecting homomorphism and
therefore does not affect which ranges and kernels coincide.

Each exactness statement therefore comes in two forms, and both are kept. The general form takes
the differential of the extension as data, pinned down only by the two equations above, and is
what a caller holding some other construction of `A⟨T⟩` can use. The instantiated form, with the
suffix `_oddExtensionDifferential`, assumes no differential at all: it uses
`oddExtensionDifferential 𝒜 dA 1 f`, the explicit differential of Tag 09PM, whose existence and
uniqueness is `existsUnique_differential_oddVariableExtension`. Nothing is lost by having both,
because that uniqueness says the two forms speak about the same map: any `dExt` satisfying the
hypotheses of the general form *is* `oddExtensionDifferential 𝒜 dA 1 f`. The cycle condition on
`f` that Tag 09PM asks for is automatic here, since in degree one the prescribed value has degree
zero and the differential vanishes in degree zero.

## References

* [Stacks Project, Tag 0GZ6](https://stacks.math.columbia.edu/tag/0GZ6)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open OddVariableExtension

attribute [local implicit_reducible] TwistedModule

universe u v

namespace OddVariableExtension

/-- The coefficient of the adjoined variable, as a linear map to the coefficient algebra. This is
`TrivSqZeroExt.snd` composed with the identification of the twisted copy of `A` with `A`. -/
public def variableCoeff {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    OddVariableExtension 𝒜 1 →ₗ[R] A :=
  (LinearMap.snd R A A).comp (coefficients 𝒜 1).toLinearMap

/-- The constant coefficient of the image of the inclusion. -/
@[simp]
public theorem fst_inclusion {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (a : A) :
    (inclusion 𝒜 1 a).fst = a := rfl

/-- The image of the inclusion has no component along the adjoined variable. -/
@[simp]
public theorem variableCoeff_inclusion {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (a : A) :
    variableCoeff 𝒜 (inclusion 𝒜 1 a) = 0 := rfl

/-- The adjoined variable has no constant coefficient. -/
@[simp]
public theorem fst_generator {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    (generator 𝒜 1 : OddVariableExtension 𝒜 1).fst = 0 := rfl

/-- The adjoined variable is its own coefficient. -/
@[simp]
public theorem variableCoeff_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    variableCoeff 𝒜 (generator 𝒜 1) = 1 := rfl

/-- Two elements of the extension agree as soon as their two coefficients do. -/
public theorem ext_coeff {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {y z : OddVariableExtension 𝒜 1}
    (h1 : y.fst = z.fst) (h2 : variableCoeff 𝒜 y = variableCoeff 𝒜 z) : y = z :=
  TrivSqZeroExt.ext h1 h2

/-- The constant coefficient of a product whose left factor comes from `A`. -/
public theorem fst_inclusion_mul {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (b : A) (z : OddVariableExtension 𝒜 1) :
    (inclusion 𝒜 1 b * z).fst = b * z.fst :=
  TrivSqZeroExt.fst_mul _ _

/-- The coefficient of the adjoined variable in a product whose left factor comes from `A`. -/
public theorem variableCoeff_inclusion_mul {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (b : A) (z : OddVariableExtension 𝒜 1) :
    variableCoeff 𝒜 (inclusion 𝒜 1 b * z) = b * variableCoeff 𝒜 z := by
  have h : variableCoeff 𝒜 (inclusion 𝒜 1 b * z) =
      b * variableCoeff 𝒜 z + 0 * signRingEquiv 𝒜 1 z.fst := mul_snd 𝒜 1 _ _
  rw [h, zero_mul, add_zero]

/-- The coefficient of `bT` along the adjoined variable is `b`. -/
@[simp]
public theorem variableCoeff_inclusion_mul_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (b : A) :
    variableCoeff 𝒜 (inclusion 𝒜 1 b * generator 𝒜 1) = b := by
  rw [variableCoeff_inclusion_mul, variableCoeff_generator, mul_one]

/-- The element `bT` has no constant coefficient. -/
@[simp]
public theorem fst_inclusion_mul_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (b : A) :
    (inclusion 𝒜 1 b * generator 𝒜 1).fst = 0 := by
  rw [fst_inclusion_mul, fst_generator, mul_zero]

/-- Homogeneity of degree `m + 1` is homogeneity of the two coefficients, in degrees `m + 1` and
`m`. -/
public theorem mem_grade_succ_iff {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (m : ℕ) (y : OddVariableExtension 𝒜 1) :
    y ∈ grade 𝒜 1 (m + 1) ↔ y.fst ∈ 𝒜 (m + 1) ∧ variableCoeff 𝒜 y ∈ 𝒜 m := by
  rw [mem_grade_iff, ite_eq_left (Nat.le_add_left 1 m), Nat.add_sub_cancel]
  exact Iff.rfl

/-- The element `bT` is homogeneous of degree `m + 1` when `b` is homogeneous of degree `m`. -/
public theorem inclusion_mul_generator_mem_grade_succ {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {m : ℕ} {b : A} (hb : b ∈ 𝒜 m) :
    inclusion 𝒜 1 b * generator 𝒜 1 ∈ grade 𝒜 1 (m + 1) :=
  (mem_grade_succ_iff 𝒜 m _).mpr ⟨by simp, by simpa using hb⟩

/-- The element `a + bT` is homogeneous of degree `m + 1` when `a` and `b` are homogeneous of
degrees `m + 1` and `m`. -/
public theorem add_mul_generator_mem_grade_succ {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {m : ℕ} {a b : A}
    (ha : a ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) :
    inclusion 𝒜 1 a + inclusion 𝒜 1 b * generator 𝒜 1 ∈ grade 𝒜 1 (m + 1) :=
  Submodule.add_mem _ (inclusion_mem_grade 𝒜 1 (m + 1) ha)
    (inclusion_mul_generator_mem_grade_succ 𝒜 hb)

/-- The canonical expression `a + bT` of an element of the extension. -/
public theorem eq_inclusion_add_mul_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (y : OddVariableExtension 𝒜 1) :
    y = inclusion 𝒜 1 y.fst + inclusion 𝒜 1 (variableCoeff 𝒜 y) * generator 𝒜 1 :=
  (inclusion_fst_add_inclusion_snd_mul_generator 𝒜 1 y).symm

/-- An element with no component along the adjoined variable is the image of its own constant
coefficient. -/
public theorem eq_inclusion_of_variableCoeff_eq_zero {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {y : OddVariableExtension 𝒜 1}
    (hy : variableCoeff 𝒜 y = 0) : y = inclusion 𝒜 1 y.fst := by
  refine ext_coeff 𝒜 rfl ?_
  rw [hy, variableCoeff_inclusion]

/-- The canonical inclusion is injective, as is visible on constant coefficients. -/
public theorem inclusion_eq_zero_iff {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {a : A} :
    inclusion 𝒜 1 a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using congrArg TrivSqZeroExt.fst h, fun h => by rw [h, map_zero]⟩

end OddVariableExtension

/-! ### The differential of the extension in coefficient coordinates -/

/-- The differential of a degree-`m + 1` element of the extension, expanded along the canonical
expression `a + bT` of that element. -/
private theorem dExt_eq {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    {m : ℕ} {y : OddVariableExtension 𝒜 1}
    (hy : y ∈ OddVariableExtension.grade 𝒜 1 (m + 1)) :
    dExt y = inclusion 𝒜 1 (dA y.fst) +
      (inclusion 𝒜 1 (dA (variableCoeff 𝒜 y)) * generator 𝒜 1 +
        (-1 : R) ^ m • (inclusion 𝒜 1 (variableCoeff 𝒜 y) * dExt (generator 𝒜 1))) := by
  have hcoeff : variableCoeff 𝒜 y ∈ 𝒜 m := ((mem_grade_succ_iff 𝒜 m y).mp hy).2
  conv_lhs => rw [eq_inclusion_add_mul_generator 𝒜 y]
  rw [map_add, IsDifferentialGradedAlgebra.leibniz
    (𝒜 := OddVariableExtension.grade 𝒜 1) (d := dExt)
    (inclusion_mem_grade 𝒜 1 m hcoeff) (generator_mem_grade 𝒜 1), hdExt, hdExt]

/-- The differential sends the adjoined variable into the image of the inclusion: it lowers the
degree to zero, and the degree-zero part of the extension has no component along the variable. -/
private theorem variableCoeff_dExt_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt] :
    variableCoeff 𝒜 (dExt (OddVariableExtension.generator 𝒜 1)) = 0 := by
  have hmem : dExt (generator 𝒜 1) ∈ OddVariableExtension.grade 𝒜 1 0 :=
    IsDifferentialGradedAlgebra.d_mem (𝒜 := OddVariableExtension.grade 𝒜 1) (d := dExt)
      (n := 0) (by simpa only [Nat.zero_add] using generator_mem_grade 𝒜 1)
  have h := ((mem_grade_iff 𝒜 1 0 (dExt (generator 𝒜 1))).mp hmem).2
  rwa [ite_eq_right (by lia : ¬ (1 : ℕ) ≤ 0), Submodule.mem_bot] at h

/-- The coefficient of the adjoined variable in the differential of a degree-`m + 1` element is
the differential of the coefficient of that element. No sign appears, and the value of `dExt` on
the adjoined variable is not needed. -/
public theorem variableCoeff_dExt {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    {m : ℕ} {y : OddVariableExtension 𝒜 1}
    (hy : y ∈ OddVariableExtension.grade 𝒜 1 (m + 1)) :
    variableCoeff 𝒜 (dExt y) = dA (variableCoeff 𝒜 y) := by
  rw [dExt_eq 𝒜 dA dExt hdExt hy, map_add, map_add, variableCoeff_inclusion,
    variableCoeff_inclusion_mul_generator, map_smul, variableCoeff_inclusion_mul,
    variableCoeff_dExt_generator 𝒜 dExt, mul_zero, smul_zero, add_zero, zero_add]

/-- The constant coefficient of the differential of a degree-`m + 1` element: the differential of
the constant coefficient, plus the product of `f` with the coefficient of the variable, carrying
the Koszul sign `(-1) ^ m` of the Leibniz rule. -/
private theorem fst_dExt {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    (f : A) (hf : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) = OddVariableExtension.inclusion 𝒜 1 f)
    {m : ℕ} {y : OddVariableExtension 𝒜 1}
    (hy : y ∈ OddVariableExtension.grade 𝒜 1 (m + 1)) :
    (dExt y).fst = dA y.fst + (-1 : R) ^ m • (f * variableCoeff 𝒜 y) := by
  have hcoeff : variableCoeff 𝒜 y ∈ 𝒜 m := ((mem_grade_succ_iff 𝒜 m y).mp hy).2
  have hgen : (dExt (generator 𝒜 1)).fst = f := by rw [hT, fst_inclusion]
  have hcomm : variableCoeff 𝒜 y * f = f * variableCoeff 𝒜 y := by
    simpa using IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) (i := m) (j := 0) hcoeff hf
  rw [dExt_eq 𝒜 dA dExt hdExt hy, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_add,
    fst_inclusion, fst_inclusion_mul_generator, TrivSqZeroExt.fst_smul, fst_inclusion_mul,
    hgen, hcomm, zero_add]

/-- The differential of the degree-`n + 1` element `bT`, for `b` a degree-`n` cycle: the signed
inclusion of `f * b`. -/
private theorem dExt_inclusion_mul_generator {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    (f : A) (hf : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) = OddVariableExtension.inclusion 𝒜 1 f)
    {n : ℕ} {b : A} (hb : b ∈ 𝒜 n) (hcyc : dA b = 0) :
    dExt (OddVariableExtension.inclusion 𝒜 1 b * OddVariableExtension.generator 𝒜 1) =
      (-1 : R) ^ n • OddVariableExtension.inclusion 𝒜 1 (f * b) := by
  have hmem : inclusion 𝒜 1 b * generator 𝒜 1 ∈ OddVariableExtension.grade 𝒜 1 (n + 1) :=
    inclusion_mul_generator_mem_grade_succ 𝒜 hb
  refine ext_coeff 𝒜 ?_ ?_
  · rw [fst_dExt 𝒜 dA f hf dExt hdExt hT hmem, fst_inclusion_mul_generator, map_zero,
      variableCoeff_inclusion_mul_generator, TrivSqZeroExt.fst_smul, fst_inclusion, zero_add]
  · rw [variableCoeff_dExt 𝒜 dA dExt hdExt hmem, variableCoeff_inclusion_mul_generator, hcyc,
      map_smul, variableCoeff_inclusion, smul_zero]

/-- A degree-`m + 1` element has differential `a` (from `A`) exactly when `a` is the constant
coefficient of its differential and the coefficient of its variable is a cycle. -/
private theorem dExt_eq_inclusion_iff {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    (f : A) (hf : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) = OddVariableExtension.inclusion 𝒜 1 f)
    {m : ℕ} {y : OddVariableExtension 𝒜 1}
    (hy : y ∈ OddVariableExtension.grade 𝒜 1 (m + 1)) (a : A) :
    dExt y = inclusion 𝒜 1 a ↔
      dA y.fst + (-1 : R) ^ m • (f * variableCoeff 𝒜 y) = a ∧ dA (variableCoeff 𝒜 y) = 0 := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => ext_coeff 𝒜 ?_ ?_⟩
  · have h1 := congrArg TrivSqZeroExt.fst h
    have h2 := congrArg (variableCoeff 𝒜) h
    rw [fst_dExt 𝒜 dA f hf dExt hdExt hT hy, fst_inclusion] at h1
    rw [variableCoeff_dExt 𝒜 dA dExt hdExt hy, variableCoeff_inclusion] at h2
    exact ⟨h1, h2⟩
  · rw [fst_dExt 𝒜 dA f hf dExt hdExt hT hy, h1, fst_inclusion]
  · rw [variableCoeff_dExt 𝒜 dA dExt hdExt hy, h2, variableCoeff_inclusion]

/-- Two copies of the sign `(-1) ^ n` cancel. -/
private theorem neg_one_pow_smul_neg_one_pow_smul {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) (x : M) :
    (-1 : R) ^ n • (-1 : R) ^ n • x = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp

/-! ### Multiplication by a degree-zero cycle -/

/-- Multiplication by a degree-zero element, on the degree-`n` cycles. -/
public def mulOnGradeCycles {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ) :
    gradeCycles 𝒜 dA n →ₗ[R] gradeCycles 𝒜 dA n :=
  LinearMap.codRestrict (gradeCycles 𝒜 dA n)
    (LinearMap.codRestrict (𝒜 n)
      ((LinearMap.mulLeft R f).comp ((𝒜 n).subtype.comp (gradeCycles 𝒜 dA n).subtype))
      fun x => by simpa using SetLike.mul_mem_graded hf (x : 𝒜 n).property)
    fun x => by
      change dA (f * ((x : 𝒜 n) : A)) = 0
      rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := dA) hf (x : 𝒜 n).property,
        IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := dA) hf, zero_mul, zero_add,
        (mem_gradeCycles_iff 𝒜 dA).mp x.property, mul_zero, smul_zero]

/-- `mulOnGradeCycles` multiplies the underlying element by `f`. -/
@[simp]
public theorem mulOnGradeCycles_coe {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ)
    (x : gradeCycles 𝒜 dA n) :
    ((mulOnGradeCycles 𝒜 dA f hf n x : 𝒜 n) : A) = f * ((x : 𝒜 n) : A) := rfl

/-- Multiplication by a degree-zero cycle on degree-`n` homology, generalising
`mulOnDegreeZeroHomology` to every degree. Because `f` has degree zero no Koszul sign intervenes,
so this is the unsigned map `a ↦ f * a`. -/
public def mulOnGradeHomology {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ) :
    gradeHomology 𝒜 dA n →ₗ[R] gradeHomology 𝒜 dA n :=
  Submodule.mapQ _ _ (mulOnGradeCycles 𝒜 dA f hf n) <| by
    intro x hx
    obtain ⟨y, hy, hdy⟩ := (mem_gradeBoundaries_iff 𝒜 dA).mp hx
    refine (mem_gradeBoundaries_iff 𝒜 dA).mpr
      ⟨f * y, by simpa using SetLike.mul_mem_graded hf hy, ?_⟩
    have hleib : dA (f * y) = f * dA y := by
      rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := dA) hf hy,
        IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := dA) hf, zero_mul, zero_add,
        pow_zero, one_smul]
    exact hleib.trans (congrArg (fun z : A => f * z) hdy)

/-- `mulOnGradeHomology` sends the class of a cycle `x` to the class of `f x`. -/
@[simp]
public theorem mulOnGradeHomology_mk {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ)
    (x : gradeCycles 𝒜 dA n) :
    mulOnGradeHomology 𝒜 dA f hf n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mulOnGradeCycles 𝒜 dA f hf n x) := rfl

/-! ### The map induced by the inclusion -/

/-- The canonical inclusion carries degree-`n` cycles of `A` to degree-`n` cycles of the odd
degree-one extension. -/
public def toExtensionOnGradeCycles {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) :
    gradeCycles 𝒜 dA n →ₗ[R] gradeCycles (OddVariableExtension.grade 𝒜 1) dExt n :=
  LinearMap.codRestrict (gradeCycles (OddVariableExtension.grade 𝒜 1) dExt n)
    (LinearMap.codRestrict (OddVariableExtension.grade 𝒜 1 n)
      ((inclusionAlgHom 𝒜 1).toLinearMap.comp
        ((𝒜 n).subtype.comp (gradeCycles 𝒜 dA n).subtype))
      fun x => inclusion_mem_grade 𝒜 1 n (x : 𝒜 n).property)
    fun x => by
      change dExt (OddVariableExtension.inclusion 𝒜 1 ((x : 𝒜 n) : A)) = 0
      rw [hdExt, (mem_gradeCycles_iff 𝒜 dA).mp x.property, map_zero]

/-- `toExtensionOnGradeCycles` sends a cycle to its image under the inclusion of `A` into the
extension. -/
@[simp]
public theorem toExtensionOnGradeCycles_coe {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) (x : gradeCycles 𝒜 dA n) :
    ((toExtensionOnGradeCycles 𝒜 dA dExt hdExt n x :
        OddVariableExtension.grade 𝒜 1 n) : OddVariableExtension 𝒜 1) =
      OddVariableExtension.inclusion 𝒜 1 ((x : 𝒜 n) : A) := rfl

/-- The map on degree-`n` homology induced by the canonical inclusion into the odd degree-one
extension, generalising `toExtensionOnDegreeZeroHomology` to every degree. -/
public def toExtensionOnGradeHomology {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) :
    gradeHomology 𝒜 dA n →ₗ[R] gradeHomology (OddVariableExtension.grade 𝒜 1) dExt n :=
  Submodule.mapQ _ _ (toExtensionOnGradeCycles 𝒜 dA dExt hdExt n) <| by
    intro x hx
    obtain ⟨y, hy, hdy⟩ := (mem_gradeBoundaries_iff 𝒜 dA).mp hx
    refine (mem_gradeBoundaries_iff (OddVariableExtension.grade 𝒜 1) dExt).mpr
      ⟨OddVariableExtension.inclusion 𝒜 1 y, inclusion_mem_grade 𝒜 1 (n + 1) hy, ?_⟩
    exact (hdExt y).trans
      (congrArg (fun z : A => OddVariableExtension.inclusion 𝒜 1 z) hdy)

/-- `toExtensionOnGradeHomology` sends the class of a cycle to the class of its image in the
extension. -/
@[simp]
public theorem toExtensionOnGradeHomology_mk {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) (x : gradeCycles 𝒜 dA n) :
    toExtensionOnGradeHomology 𝒜 dA dExt hdExt n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (toExtensionOnGradeCycles 𝒜 dA dExt hdExt n x) := rfl

/-! ### The connecting map -/

/-- The coefficient of the adjoined variable in a degree-`n + 1` cycle of the extension is a
degree-`n` cycle of `A`. -/
public def connectingOnGradeCycles {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) :
    gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1) →ₗ[R] gradeCycles 𝒜 dA n :=
  LinearMap.codRestrict (gradeCycles 𝒜 dA n)
    (LinearMap.codRestrict (𝒜 n)
      ((variableCoeff 𝒜).comp
        ((OddVariableExtension.grade 𝒜 1 (n + 1)).subtype.comp
          (gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1)).subtype))
      fun x => ((mem_grade_succ_iff 𝒜 n _).mp
        (x : OddVariableExtension.grade 𝒜 1 (n + 1)).property).2)
    fun x => by
      change dA (variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1)) = 0
      rw [← variableCoeff_dExt 𝒜 dA dExt hdExt
          (x : OddVariableExtension.grade 𝒜 1 (n + 1)).property,
        (mem_gradeCycles_iff (OddVariableExtension.grade 𝒜 1) dExt).mp x.property, map_zero]

/-- `connectingOnGradeCycles` sends a cycle of the extension to its coefficient of the adjoined
variable. -/
@[simp]
public theorem connectingOnGradeCycles_coe {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ)
    (x : gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1)) :
    ((connectingOnGradeCycles 𝒜 dA dExt hdExt n x : 𝒜 n) : A) =
      variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1) := rfl

/-- The connecting map of the long exact sequence: the class of a degree-`n + 1` cycle of the
extension is sent to the class of its coefficient along the adjoined variable. -/
public def connectingOnGradeHomology {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) :
    gradeHomology (OddVariableExtension.grade 𝒜 1) dExt (n + 1) →ₗ[R]
      gradeHomology 𝒜 dA n :=
  Submodule.mapQ _ _ (connectingOnGradeCycles 𝒜 dA dExt hdExt n) <| by
    intro x hx
    obtain ⟨y, hy, hdy⟩ :=
      (mem_gradeBoundaries_iff (OddVariableExtension.grade 𝒜 1) dExt).mp hx
    refine (mem_gradeBoundaries_iff 𝒜 dA).mpr
      ⟨variableCoeff 𝒜 y, ((mem_grade_succ_iff 𝒜 (n + 1) y).mp hy).2, ?_⟩
    exact (variableCoeff_dExt 𝒜 dA dExt hdExt hy).symm.trans
      (congrArg (fun z : OddVariableExtension 𝒜 1 => variableCoeff 𝒜 z) hdy)

/-- `connectingOnGradeHomology` sends the class of a cycle of the extension to the class of its
coefficient of the adjoined variable. -/
@[simp]
public theorem connectingOnGradeHomology_mk {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ)
    (x : gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1)) :
    connectingOnGradeHomology 𝒜 dA dExt hdExt n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (connectingOnGradeCycles 𝒜 dA dExt hdExt n x) := rfl

/-! ### Exactness -/

/-- Exactness at the second copy of `Hₙ(A)`: the image of multiplication by `f` is the kernel of
the map induced by the inclusion into the odd degree-one extension. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_mulOnGradeHomology_eq_ker_toExtension {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) = OddVariableExtension.inclusion 𝒜 1 f)
    (n : ℕ) :
    LinearMap.range (mulOnGradeHomology 𝒜 dA f hf n) =
      LinearMap.ker (toExtensionOnGradeHomology 𝒜 dA dExt hdExt n) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker]
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hq
    refine Submodule.Quotient.induction_on _ p fun a => ?_
    rw [mulOnGradeHomology_mk, toExtensionOnGradeHomology_mk]
    have hbmem : ((a : 𝒜 n) : A) ∈ 𝒜 n := (a : 𝒜 n).property
    have hbcyc : dA ((a : 𝒜 n) : A) = 0 := (mem_gradeCycles_iff 𝒜 dA).mp a.property
    have hbdry : (toExtensionOnGradeCycles 𝒜 dA dExt hdExt n
        (mulOnGradeCycles 𝒜 dA f hf n a) : OddVariableExtension.grade 𝒜 1 n) ∈
        gradeBoundaries (OddVariableExtension.grade 𝒜 1) dExt n := by
      refine (mem_gradeBoundaries_iff (OddVariableExtension.grade 𝒜 1) dExt).mpr
        ⟨(-1 : R) ^ n • (OddVariableExtension.inclusion 𝒜 1 ((a : 𝒜 n) : A) *
            OddVariableExtension.generator 𝒜 1),
          Submodule.smul_mem _ _ (inclusion_mul_generator_mem_grade_succ 𝒜 hbmem), ?_⟩
      have hgoal : dExt ((-1 : R) ^ n • (OddVariableExtension.inclusion 𝒜 1 ((a : 𝒜 n) : A) *
          OddVariableExtension.generator 𝒜 1)) =
          OddVariableExtension.inclusion 𝒜 1 (f * ((a : 𝒜 n) : A)) := by
        rw [map_smul, dExt_inclusion_mul_generator 𝒜 dA f hf dExt hdExt hT hbmem hbcyc,
          neg_one_pow_smul_neg_one_pow_smul]
      exact hgoal
    exact (Submodule.Quotient.mk_eq_zero _).2 hbdry
  · intro hq
    rw [LinearMap.mem_ker] at hq
    revert hq
    refine Submodule.Quotient.induction_on _ q fun a hq => ?_
    rw [toExtensionOnGradeHomology_mk] at hq
    have hmem0 : (toExtensionOnGradeCycles 𝒜 dA dExt hdExt n a :
        OddVariableExtension.grade 𝒜 1 n) ∈
        gradeBoundaries (OddVariableExtension.grade 𝒜 1) dExt n :=
      ((Submodule.Quotient.mk_eq_zero _).1 hq :)
    obtain ⟨y, hy, hdy⟩ :=
      (mem_gradeBoundaries_iff (OddVariableExtension.grade 𝒜 1) dExt).mp hmem0
    have hyfst : y.fst ∈ 𝒜 (n + 1) := ((mem_grade_succ_iff 𝒜 n y).mp hy).1
    have hycoeff : variableCoeff 𝒜 y ∈ 𝒜 n := ((mem_grade_succ_iff 𝒜 n y).mp hy).2
    obtain ⟨hfst, hcyc⟩ :=
      (dExt_eq_inclusion_iff 𝒜 dA f hf dExt hdExt hT hy ((a : 𝒜 n) : A)).mp hdy
    refine ⟨Submodule.Quotient.mk
      (⟨⟨(-1 : R) ^ n • variableCoeff 𝒜 y, Submodule.smul_mem _ _ hycoeff⟩,
        (mem_gradeCycles_iff 𝒜 dA).mpr (by rw [map_smul, hcyc, smul_zero])⟩ :
        gradeCycles 𝒜 dA n), ?_⟩
    rw [mulOnGradeHomology_mk]
    have hbdry : (mulOnGradeCycles 𝒜 dA f hf n
        (⟨⟨(-1 : R) ^ n • variableCoeff 𝒜 y, Submodule.smul_mem _ _ hycoeff⟩,
          (mem_gradeCycles_iff 𝒜 dA).mpr (by rw [map_smul, hcyc, smul_zero])⟩ :
          gradeCycles 𝒜 dA n) - a : 𝒜 n) ∈ gradeBoundaries 𝒜 dA n := by
      refine (mem_gradeBoundaries_iff 𝒜 dA).mpr ⟨-y.fst, (𝒜 (n + 1)).neg_mem hyfst, ?_⟩
      have hgoal : dA (-y.fst) =
          f * ((-1 : R) ^ n • variableCoeff 𝒜 y) - ((a : 𝒜 n) : A) := by
        rw [map_neg, mul_smul_comm, ← hfst]
        abel
      exact hgoal
    exact (Submodule.Quotient.eq _).2 hbdry

/-- Exactness at `Hₙ₊₁(A⟨T⟩)`: the image of the map induced by the inclusion in degree `n + 1` is
the kernel of the connecting map out of degree `n + 1`. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_toExtensionOnGradeHomology_eq_ker_connecting {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (n : ℕ) :
    LinearMap.range (toExtensionOnGradeHomology 𝒜 dA dExt hdExt (n + 1)) =
      LinearMap.ker (connectingOnGradeHomology 𝒜 dA dExt hdExt n) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker]
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hq
    refine Submodule.Quotient.induction_on _ p fun a => ?_
    rw [toExtensionOnGradeHomology_mk, connectingOnGradeHomology_mk]
    have hzero : connectingOnGradeCycles 𝒜 dA dExt hdExt n
        (toExtensionOnGradeCycles 𝒜 dA dExt hdExt (n + 1) a) = 0 :=
      Subtype.ext (Subtype.ext rfl)
    rw [hzero]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)
  · intro hq
    rw [LinearMap.mem_ker] at hq
    revert hq
    refine Submodule.Quotient.induction_on _ q fun x hq => ?_
    rw [connectingOnGradeHomology_mk] at hq
    have hvmem : ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1) ∈ OddVariableExtension.grade 𝒜 1 (n + 1) :=
      (x : OddVariableExtension.grade 𝒜 1 (n + 1)).property
    have hvcyc : dExt ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1) = 0 :=
      (mem_gradeCycles_iff (OddVariableExtension.grade 𝒜 1) dExt).mp x.property
    have hmem0 : (connectingOnGradeCycles 𝒜 dA dExt hdExt n x : 𝒜 n) ∈
        gradeBoundaries 𝒜 dA n :=
      ((Submodule.Quotient.mk_eq_zero _).1 hq :)
    obtain ⟨w, hw, hdw⟩ := (mem_gradeBoundaries_iff 𝒜 dA).mp hmem0
    have hdw' : dA w = variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1) := hdw
    have hzmem : OddVariableExtension.inclusion 𝒜 1 w *
        OddVariableExtension.generator 𝒜 1 ∈
        OddVariableExtension.grade 𝒜 1 (n + 1 + 1) :=
      inclusion_mul_generator_mem_grade_succ 𝒜 hw
    have hdzmem : dExt (OddVariableExtension.inclusion 𝒜 1 w *
        OddVariableExtension.generator 𝒜 1) ∈
        OddVariableExtension.grade 𝒜 1 (n + 1) :=
      IsDifferentialGradedAlgebra.d_mem
        (𝒜 := OddVariableExtension.grade 𝒜 1) (d := dExt) hzmem
    have hdzcoeff : variableCoeff 𝒜 (dExt (OddVariableExtension.inclusion 𝒜 1 w *
        OddVariableExtension.generator 𝒜 1)) =
        variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
          OddVariableExtension 𝒜 1) := by
      rw [variableCoeff_dExt 𝒜 dA dExt hdExt hzmem,
        variableCoeff_inclusion_mul_generator]
      exact hdw'
    obtain ⟨u, hu⟩ : ∃ u : OddVariableExtension 𝒜 1, u = ((x : OddVariableExtension.grade 𝒜 1
        (n + 1)) : OddVariableExtension 𝒜 1) - dExt (OddVariableExtension.inclusion 𝒜 1 w *
          OddVariableExtension.generator 𝒜 1) := ⟨_, rfl⟩
    have humem : u ∈ OddVariableExtension.grade 𝒜 1 (n + 1) :=
      hu ▸ Submodule.sub_mem _ hvmem hdzmem
    have hucoeff : variableCoeff 𝒜 u = 0 := by rw [hu, map_sub, hdzcoeff, sub_self]
    have hufst : u.fst ∈ 𝒜 (n + 1) := ((mem_grade_succ_iff 𝒜 n _).mp humem).1
    have hueq := eq_inclusion_of_variableCoeff_eq_zero 𝒜 hucoeff
    have hucyc : dExt u = 0 := by
      rw [hu, map_sub, hvcyc, IsDifferentialGradedAlgebra.d_sq_zero
        (𝒜 := OddVariableExtension.grade 𝒜 1) (d := dExt), sub_zero]
    have hafcyc : dA u.fst = 0 := by
      refine (inclusion_eq_zero_iff 𝒜).mp ?_
      rwa [← hdExt, ← hueq]
    refine ⟨Submodule.Quotient.mk
      (⟨⟨u.fst, hufst⟩, (mem_gradeCycles_iff 𝒜 dA).mpr hafcyc⟩ : gradeCycles 𝒜 dA (n + 1)), ?_⟩
    rw [toExtensionOnGradeHomology_mk]
    have hbdry : (toExtensionOnGradeCycles 𝒜 dA dExt hdExt (n + 1)
        (⟨⟨u.fst, hufst⟩, (mem_gradeCycles_iff 𝒜 dA).mpr hafcyc⟩ : gradeCycles 𝒜 dA (n + 1)) - x :
        OddVariableExtension.grade 𝒜 1 (n + 1)) ∈
        gradeBoundaries (OddVariableExtension.grade 𝒜 1) dExt (n + 1) := by
      refine (mem_gradeBoundaries_iff (OddVariableExtension.grade 𝒜 1) dExt).mpr
        ⟨-(OddVariableExtension.inclusion 𝒜 1 w * OddVariableExtension.generator 𝒜 1),
          (OddVariableExtension.grade 𝒜 1 (n + 1 + 1)).neg_mem hzmem, ?_⟩
      have hgoal : dExt (-(OddVariableExtension.inclusion 𝒜 1 w *
          OddVariableExtension.generator 𝒜 1)) = OddVariableExtension.inclusion 𝒜 1 u.fst -
            ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) : OddVariableExtension 𝒜 1) := by
        rw [map_neg, ← hueq, hu]
        abel
      exact hgoal
    exact (Submodule.Quotient.eq _).2 hbdry

/-- Exactness at the first copy of `Hₙ(A)`: the image of the connecting map out of degree `n + 1`
is the kernel of multiplication by `f`. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_connectingOnGradeHomology_eq_ker_mul {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0)
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x))
    (hT : dExt (OddVariableExtension.generator 𝒜 1) = OddVariableExtension.inclusion 𝒜 1 f)
    (n : ℕ) :
    LinearMap.range (connectingOnGradeHomology 𝒜 dA dExt hdExt n) =
      LinearMap.ker (mulOnGradeHomology 𝒜 dA f hf n) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker]
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hq
    refine Submodule.Quotient.induction_on _ p fun x => ?_
    rw [connectingOnGradeHomology_mk, mulOnGradeHomology_mk]
    have hvmem : ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1) ∈ OddVariableExtension.grade 𝒜 1 (n + 1) :=
      (x : OddVariableExtension.grade 𝒜 1 (n + 1)).property
    have hvfst : ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
        OddVariableExtension 𝒜 1).fst ∈ 𝒜 (n + 1) :=
      ((mem_grade_succ_iff 𝒜 n _).mp hvmem).1
    have hfst : dA ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
          OddVariableExtension 𝒜 1).fst +
        (-1 : R) ^ n • (f * variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
          OddVariableExtension 𝒜 1)) = 0 := by
      refine ((dExt_eq_inclusion_iff 𝒜 dA f hf dExt hdExt hT hvmem 0).mp ?_).1
      rw [map_zero]
      exact (mem_gradeCycles_iff (OddVariableExtension.grade 𝒜 1) dExt).mp x.property
    have hdv : dA ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
          OddVariableExtension 𝒜 1).fst =
        -((-1 : R) ^ n • (f * variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
          OddVariableExtension 𝒜 1))) :=
      eq_neg_iff_add_eq_zero.mpr hfst
    have hbdry : (mulOnGradeCycles 𝒜 dA f hf n
        (connectingOnGradeCycles 𝒜 dA dExt hdExt n x) : 𝒜 n) ∈ gradeBoundaries 𝒜 dA n := by
      refine (mem_gradeBoundaries_iff 𝒜 dA).mpr
        ⟨-((-1 : R) ^ n • ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
            OddVariableExtension 𝒜 1).fst),
          (𝒜 (n + 1)).neg_mem (Submodule.smul_mem _ _ hvfst), ?_⟩
      have hgoal : dA (-((-1 : R) ^ n •
          ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
            OddVariableExtension 𝒜 1).fst)) =
          f * variableCoeff 𝒜 ((x : OddVariableExtension.grade 𝒜 1 (n + 1)) :
            OddVariableExtension 𝒜 1) := by
        rw [map_neg, map_smul, hdv, smul_neg, neg_neg,
          neg_one_pow_smul_neg_one_pow_smul]
      exact hgoal
    exact (Submodule.Quotient.mk_eq_zero _).2 hbdry
  · intro hq
    rw [LinearMap.mem_ker] at hq
    revert hq
    refine Submodule.Quotient.induction_on _ q fun a hq => ?_
    rw [mulOnGradeHomology_mk] at hq
    have hbmem : ((a : 𝒜 n) : A) ∈ 𝒜 n := (a : 𝒜 n).property
    have hbcyc : dA ((a : 𝒜 n) : A) = 0 := (mem_gradeCycles_iff 𝒜 dA).mp a.property
    have hmem0 : (mulOnGradeCycles 𝒜 dA f hf n a : 𝒜 n) ∈ gradeBoundaries 𝒜 dA n :=
      ((Submodule.Quotient.mk_eq_zero _).1 hq :)
    obtain ⟨c, hc, hdc⟩ := (mem_gradeBoundaries_iff 𝒜 dA).mp hmem0
    have hdc' : dA c = f * ((a : 𝒜 n) : A) := hdc
    obtain ⟨y, hyfst, hycoeff⟩ : ∃ y : OddVariableExtension 𝒜 1,
        y.fst = -((-1 : R) ^ n • c) ∧ variableCoeff 𝒜 y = ((a : 𝒜 n) : A) :=
      ⟨OddVariableExtension.inclusion 𝒜 1 (-((-1 : R) ^ n • c)) +
        OddVariableExtension.inclusion 𝒜 1 ((a : 𝒜 n) : A) *
          OddVariableExtension.generator 𝒜 1, by simp, by simp⟩
    have hymem : y ∈ OddVariableExtension.grade 𝒜 1 (n + 1) :=
      (mem_grade_succ_iff 𝒜 n y).mpr
        ⟨hyfst ▸ (𝒜 (n + 1)).neg_mem (Submodule.smul_mem _ _ hc), hycoeff ▸ hbmem⟩
    have hycyc : dExt y = 0 := by
      rw [← map_zero (inclusion 𝒜 1)]
      refine (dExt_eq_inclusion_iff 𝒜 dA f hf dExt hdExt hT hymem 0).mpr ⟨?_, ?_⟩
      · rw [hyfst, hycoeff, map_neg, map_smul, hdc', neg_add_cancel]
      · rw [hycoeff, hbcyc]
    have heq : connectingOnGradeCycles 𝒜 dA dExt hdExt n
        (⟨⟨y, hymem⟩,
          (mem_gradeCycles_iff (OddVariableExtension.grade 𝒜 1) dExt).mpr hycyc⟩ :
          gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1)) = a :=
      Subtype.ext (Subtype.ext hycoeff)
    exact ⟨Submodule.Quotient.mk
      (⟨⟨y, hymem⟩,
        (mem_gradeCycles_iff (OddVariableExtension.grade 𝒜 1) dExt).mpr hycyc⟩ :
        gradeCycles (OddVariableExtension.grade 𝒜 1) dExt (n + 1)),
      by rw [connectingOnGradeHomology_mk, heq]⟩

/-! ### The right end of the sequence -/

/-- In degree zero the map induced by the inclusion agrees, under the identification of
degree-zero graded homology with the degree-zero quotient of the previous file, with the map
studied there. -/
private theorem gradeHomologyZeroEquiv_toExtension {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) (q : gradeHomology 𝒜 dA 0) :
    gradeHomologyZeroEquiv (OddVariableExtension.grade 𝒜 1) dExt
        (toExtensionOnGradeHomology 𝒜 dA dExt hdExt 0 q) =
      toExtensionOnDegreeZeroHomology 𝒜 dA dExt hdExt (gradeHomologyZeroEquiv 𝒜 dA q) :=
  Submodule.Quotient.induction_on _ q fun _ => rfl

/-- The right end of the long exact sequence: the map to the degree-zero homology of the odd
degree-one extension is surjective. This is
`surjective_degreeZeroHomology_oddVariableExtension` transported along the identification
`gradeHomologyZeroEquiv` of degree-zero graded homology with the degree-zero quotient of the
previous file, rather than a second proof of it. -/
@[stacks 0GZ6 "degree_one"]
public theorem surjective_toExtensionOnGradeHomology_zero {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    (dExt : OddVariableExtension 𝒜 1 →ₗ[R] OddVariableExtension 𝒜 1)
    [IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1) dExt]
    (hdExt : ∀ x : A, dExt (OddVariableExtension.inclusion 𝒜 1 x) =
      OddVariableExtension.inclusion 𝒜 1 (dA x)) :
    Function.Surjective (toExtensionOnGradeHomology 𝒜 dA dExt hdExt 0) := by
  intro q
  obtain ⟨p, hp⟩ := surjective_degreeZeroHomology_oddVariableExtension 𝒜 dA dExt hdExt
    (gradeHomologyZeroEquiv (OddVariableExtension.grade 𝒜 1) dExt q)
  refine ⟨(gradeHomologyZeroEquiv 𝒜 dA).symm p, ?_⟩
  apply (gradeHomologyZeroEquiv (OddVariableExtension.grade 𝒜 1) dExt).injective
  rw [gradeHomologyZeroEquiv_toExtension 𝒜 dA dExt hdExt, LinearEquiv.apply_symm_apply, hp]

/-! ### The sequence for the differential of Tag 09PM -/

/-- For a degree-one odd variable the explicit differential of Tag 09PM is a differential on the
extension. The element `f` prescribed as the value on the variable has degree `1 - 1 = 0`, so the
cycle condition that Tag 09PM imposes on it holds automatically. -/
public theorem oddExtensionDifferential_one_isDGA {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) :
    IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1)
      (oddExtensionDifferential 𝒜 dA 1 f) :=
  oddExtensionDifferential_isDGA 𝒜 dA 1 Nat.one_pos odd_one f hf
    (IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := dA) hf)

/-- Exactness at the second copy of `Hₙ(A)` for the differential of Tag 09PM: no differential on
the extension is assumed, the one of Tag 09PM being used. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_mulOnGradeHomology_eq_ker_toExtension_oddExtensionDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ) :
    letI : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1)
        (oddExtensionDifferential 𝒜 dA 1 f) := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
    LinearMap.range (mulOnGradeHomology 𝒜 dA f hf n) =
      LinearMap.ker (toExtensionOnGradeHomology 𝒜 dA (oddExtensionDifferential 𝒜 dA 1 f)
        (oddExtensionDifferential_inclusion 𝒜 dA 1 f) n) := by
  have := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
  exact range_mulOnGradeHomology_eq_ker_toExtension 𝒜 dA f hf
    (oddExtensionDifferential 𝒜 dA 1 f) (oddExtensionDifferential_inclusion 𝒜 dA 1 f)
    (oddExtensionDifferential_generator 𝒜 dA 1 f) n

/-- Exactness at `Hₙ₊₁(A⟨T⟩)` for the differential of Tag 09PM: no differential on the extension
is assumed, the one of Tag 09PM being used. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_toExtensionOnGradeHomology_eq_ker_connecting_oddExtensionDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ) :
    letI : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1)
        (oddExtensionDifferential 𝒜 dA 1 f) := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
    LinearMap.range (toExtensionOnGradeHomology 𝒜 dA (oddExtensionDifferential 𝒜 dA 1 f)
        (oddExtensionDifferential_inclusion 𝒜 dA 1 f) (n + 1)) =
      LinearMap.ker (connectingOnGradeHomology 𝒜 dA (oddExtensionDifferential 𝒜 dA 1 f)
        (oddExtensionDifferential_inclusion 𝒜 dA 1 f) n) := by
  have := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
  exact range_toExtensionOnGradeHomology_eq_ker_connecting 𝒜 dA
    (oddExtensionDifferential 𝒜 dA 1 f) (oddExtensionDifferential_inclusion 𝒜 dA 1 f) n

/-- Exactness at the first copy of `Hₙ(A)` for the differential of Tag 09PM: no differential on
the extension is assumed, the one of Tag 09PM being used. -/
@[stacks 0GZ6 "degree_one"]
public theorem range_connectingOnGradeHomology_eq_ker_mul_oddExtensionDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) (n : ℕ) :
    letI : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1)
        (oddExtensionDifferential 𝒜 dA 1 f) := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
    LinearMap.range (connectingOnGradeHomology 𝒜 dA (oddExtensionDifferential 𝒜 dA 1 f)
        (oddExtensionDifferential_inclusion 𝒜 dA 1 f) n) =
      LinearMap.ker (mulOnGradeHomology 𝒜 dA f hf n) := by
  have := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
  exact range_connectingOnGradeHomology_eq_ker_mul 𝒜 dA f hf
    (oddExtensionDifferential 𝒜 dA 1 f) (oddExtensionDifferential_inclusion 𝒜 dA 1 f)
    (oddExtensionDifferential_generator 𝒜 dA 1 f) n

/-- The right end of the long exact sequence for the differential of Tag 09PM: no differential on
the extension is assumed, the one of Tag 09PM being used. -/
@[stacks 0GZ6 "degree_one"]
public theorem surjective_toExtensionOnGradeHomology_zero_oddExtensionDifferential
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] (dA : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 dA] (f : A) (hf : f ∈ 𝒜 0) :
    letI : IsDifferentialGradedAlgebra (OddVariableExtension.grade 𝒜 1)
        (oddExtensionDifferential 𝒜 dA 1 f) := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
    Function.Surjective (toExtensionOnGradeHomology 𝒜 dA (oddExtensionDifferential 𝒜 dA 1 f)
      (oddExtensionDifferential_inclusion 𝒜 dA 1 f) 0) := by
  have := oddExtensionDifferential_one_isDGA 𝒜 dA f hf
  exact surjective_toExtensionOnGradeHomology_zero 𝒜 dA
    (oddExtensionDifferential 𝒜 dA 1 f) (oddExtensionDifferential_inclusion 𝒜 dA 1 f)

end DividedPowers.TateResolution

end
