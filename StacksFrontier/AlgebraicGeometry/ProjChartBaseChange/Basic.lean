module

public import StacksFrontier.AlgebraicGeometry.ProjAwayBaseChange.Basic

/-!
# The chart-level base change of `Proj`

Let `A` be a graded `R`-algebra with grading `𝒜 : ℕ → Submodule R A`, let `S` be an `R`-algebra,
and give `S ⊗[R] A` Mathlib's base-changed grading `fun i ↦ (𝒜 i).baseChange S`
(`Stacks.ProjBaseChange.grading`). For `a` homogeneous of degree `d` this file proves the
chart-level content of the base change of `Proj`: the comparison

`(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a ⟶ Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`,  `s ⊗ z ↦ s · awayMap z`

is a ring isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartBaseChange.zeroAlgebra`: the `𝒜 0`-algebra structure on
  `(S ⊗[R] 𝒜) 0` given by `Stacks.AlgebraicGeometry.ProjAwayBaseChange.gradedZeroMap`.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.num`: the numerator map
  `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} 𝒜 i ⟶ S ⊗[R] A`, `s ⊗ x ↦ s * (1 ⊗ₜ x)`.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.numInv`: the map
  `S ⊗[R] 𝒜 i ⟶ (S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} 𝒜 i`, `s ⊗ₜ y ↦ (s ⊗ₜ 1) ⊗ y`, which exhibits `num` as a
  bijection onto the degree-`i` piece of the base change.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartMap` and
  `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartEquiv`: the chart comparison map and the
  resulting ring isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartBaseChange.num_injective`: the degree-`i` piece of the base
  change is the base change of the degree-`i` piece.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartMap_surjective`: the comparison is
  surjective.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartMap_injective`: the comparison is injective.
* `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartEquiv`: the chart-level base-change
  isomorphism.

## Implementation notes

The `𝒜 0`-algebra structure `Stacks.AlgebraicGeometry.ProjChartBaseChange.zeroAlgebra` on
`(S ⊗[R] 𝒜) 0`, the induced one `Stacks.AlgebraicGeometry.ProjChartBaseChange.chartAlgebra` on
`Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)` and their compatibility
`Stacks.AlgebraicGeometry.ProjChartBaseChange.isScalarTower_chart` are only local instances: they
depend on the ring homomorphism `Stacks.AlgebraicGeometry.ProjAwayBaseChange.gradedZeroMap`, which
is data.

The numerator map `num` is built with `TensorProduct.liftAddHom` rather than `TensorProduct.lift`,
since its target `S ⊗[R] A` carries no `𝒜 0`-module structure; the balancedness is the identity
`(1 ⊗ₜ c) * s * (1 ⊗ₜ x) = s * (1 ⊗ₜ (c * x))`.

The `𝒜 0`-module structure on the homogeneous pieces is
`Stacks.AlgebraicGeometry.ProjAwayBaseChange.piece₀ 𝒜 i`, a `Submodule (𝒜 0) A` with the same
carrier as `𝒜 i`; `Stacks.AlgebraicGeometry.ProjChartBaseChange.toPiece₀` is the identity map
between the two.

The tensor product here is taken over `𝒜 0`, in contrast to
`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`, which identifies
`R' ⊗[R] Away 𝒜 f` with `Away ((𝒜 ·).baseChange R') (1 ⊗ₜ f)`, a tensor product over `R`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open HomogeneousLocalization TensorProduct
open Stacks.ProjBaseChange Stacks.AlgebraicGeometry.ProjAwayBaseChange

universe u

namespace Stacks.AlgebraicGeometry.ProjChartBaseChange

/-! ### Degree-zero scalars as fractions -/

section Fractions

variable {ι B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [AddCommMonoid ι]
  [DecidableEq ι] (ℬ : ι → τ) [GradedRing ℬ] {f : B} {d : ι} (hf : f ∈ ℬ d)

/-- A degree-zero element over the denominator `f ^ 0 = 1` is the structure map of `Away ℬ f`. -/
public theorem awayMk_zero_eq_algebraMap (c : ℬ 0) (hc : (c : B) ∈ ℬ (0 • d)) :
    Away.mk ℬ hf 0 (c : B) hc = algebraMap (ℬ 0) (Away ℬ f) c := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.algebraMap_eq]
  show _ = Localization.mk (c : B) 1
  congr 1
  exact Subtype.ext (pow_zero f)

/-- Fractions with a common denominator and equal numerators agree. -/
public theorem awayMk_congr (n : ℕ) {x y : B} (hx : x ∈ ℬ (n • d)) (hy : y ∈ ℬ (n • d))
    (h : x = y) : Away.mk ℬ hf n x hx = Away.mk ℬ hf n y hy := by
  subst h
  rfl

/-- Multiplying by a degree-zero element preserves the degree. -/
private theorem mul_mem_of_mem_zero {x y : B} {i : ι} (hx : x ∈ ℬ 0) (hy : y ∈ ℬ i) :
    x * y ∈ ℬ i := by
  simpa using SetLike.mul_mem_graded hx hy

end Fractions

/-! ### The degree-zero algebra structures -/

section Algebras

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]

/-- The degree-zero part of the base-changed grading, as an algebra over the degree-zero part of
`𝒜`, along `Stacks.AlgebraicGeometry.ProjAwayBaseChange.gradedZeroMap`. -/
@[instance_reducible]
public def zeroAlgebra : Algebra (𝒜 0) (grading 𝒜 S 0) :=
  (gradedZeroMap 𝒜 S).toAlgebra

attribute [local instance] zeroAlgebra

/-- The structure map of `zeroAlgebra` is `gradedZeroMap`. -/
@[simp]
public theorem algebraMap_zeroAlgebra :
    algebraMap (𝒜 0) (grading 𝒜 S 0) = gradedZeroMap 𝒜 S := rfl

/-- The base-changed chart, as an algebra over the degree-zero part of `𝒜`. -/
@[instance_reducible]
public def chartAlgebra (a : A) :
    Algebra (𝒜 0) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) :=
  ((algebraMap (grading 𝒜 S 0) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))).comp
    (gradedZeroMap 𝒜 S)).toAlgebra

attribute [local instance] chartAlgebra

/-- The two degree-zero structure maps into the base-changed chart agree. -/
public theorem isScalarTower_chart (a : A) :
    IsScalarTower (𝒜 0) (grading 𝒜 S 0) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) :=
  .of_algebraMap_eq' rfl

attribute [local instance] isScalarTower_chart

/-- Scalars from `𝒜 0` act on the degree-zero part of the base-changed grading through
`1 ⊗ₜ c`. -/
public theorem coe_smul_gradingZero (c : 𝒜 0) (s : grading 𝒜 S 0) :
    ((c • s : grading 𝒜 S 0) : S ⊗[R] A) = ((1 : S) ⊗ₜ[R] (c : A)) * (s : S ⊗[R] A) := by
  rw [Algebra.smul_def, algebraMap_zeroAlgebra]
  rfl

/-- Scalars from `𝒜 0` act on a homogeneous piece by multiplication. -/
public theorem coe_smul_piece₀ (i : ℕ) (c : 𝒜 0) (x : piece₀ 𝒜 i) :
    ((c • x : piece₀ 𝒜 i) : A) = (c : A) * (x : A) := by
  rw [Submodule.coe_smul, Algebra.smul_def, SetLike.GradeZero.algebraMap_apply]

/-! ### The homogeneous pieces of the base change -/

/-- A homogeneous piece of `𝒜`, reindexed as a submodule over the degree-zero part. The carrier
sets agree, so this is the identity on elements. -/
public def toPiece₀ (i : ℕ) : (𝒜 i) →+ (piece₀ 𝒜 i) where
  toFun y := ⟨(y : A), y.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `toPiece₀` is the identity on underlying elements of `A`. -/
@[simp]
public theorem coe_toPiece₀ (i : ℕ) (y : 𝒜 i) : (toPiece₀ 𝒜 i y : A) = (y : A) := rfl

/-- The image `1 ⊗ₜ x` of a degree-`i` element lies in the degree-`i` piece of the base change. -/
private theorem one_tmul_mem_grading (i : ℕ) (x : piece₀ 𝒜 i) :
    ((1 : S) ⊗ₜ[R] (x : A)) ∈ grading 𝒜 S i :=
  Submodule.tmul_mem_baseChange_of_mem 1 ((mem_piece₀ 𝒜 i _).mp x.2)

/-- Multiplication `x ↦ s * (1 ⊗ₜ x)` of a fixed degree-zero element `s` of the base change by
the image of a degree-`i` element of `𝒜`. -/
public def numRight (i : ℕ) (s : grading 𝒜 S 0) : (piece₀ 𝒜 i) →+ S ⊗[R] A where
  toFun x := (s : S ⊗[R] A) * ((1 : S) ⊗ₜ[R] (x : A))
  map_zero' := by simp
  map_add' x y := by simp only [Submodule.coe_add, TensorProduct.tmul_add, mul_add]

/-- `numRight 𝒜 S i s` sends `x` to `s * (1 ⊗ₜ x)`. -/
@[simp]
public theorem numRight_apply (i : ℕ) (s : grading 𝒜 S 0) (x : piece₀ 𝒜 i) :
    numRight 𝒜 S i s x = (s : S ⊗[R] A) * ((1 : S) ⊗ₜ[R] (x : A)) := rfl

/-- `Stacks.AlgebraicGeometry.ProjChartBaseChange.numRight`, additive in the degree-zero
variable as well. -/
public def numBilin (i : ℕ) : (grading 𝒜 S 0) →+ ((piece₀ 𝒜 i) →+ S ⊗[R] A) where
  toFun := numRight 𝒜 S i
  map_zero' := AddMonoidHom.ext fun x => by simp
  map_add' s t := AddMonoidHom.ext fun x => by
    simp only [numRight_apply, AddMonoidHom.add_apply, Submodule.coe_add, add_mul]

/-- `numBilin 𝒜 S i` sends `s` to `numRight 𝒜 S i s`. -/
@[simp]
public theorem numBilin_apply (i : ℕ) (s : grading 𝒜 S 0) :
    numBilin 𝒜 S i s = numRight 𝒜 S i s := rfl

/-- The numerator map: multiplication `(s, x) ↦ s * (1 ⊗ₜ x)` of a degree-zero element of the
base change by the image of a degree-`i` element of `𝒜`, descended to the tensor product over
`𝒜 0`. -/
public def num (i : ℕ) : (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 i) →+ S ⊗[R] A :=
  TensorProduct.liftAddHom (numBilin 𝒜 S i) fun c s x => by
    rw [numBilin_apply, numBilin_apply, numRight_apply, numRight_apply, coe_smul_gradingZero,
      coe_smul_piece₀, show ((1 : S) ⊗ₜ[R] ((c : A) * (x : A))) =
        ((1 : S) ⊗ₜ[R] (c : A)) * ((1 : S) ⊗ₜ[R] (x : A)) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
    ring

/-- The numerator map sends `s ⊗ x` to `s * (1 ⊗ₜ x)`. -/
@[simp]
public theorem num_tmul (i : ℕ) (s : grading 𝒜 S 0) (x : piece₀ 𝒜 i) :
    num 𝒜 S i (s ⊗ₜ[𝒜 0] x) = (s : S ⊗[R] A) * ((1 : S) ⊗ₜ[R] (x : A)) := rfl

/-- The numerator map lands in the degree-`i` piece of the base-changed grading. -/
public theorem num_mem (i : ℕ) (u : (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 i)) :
    num 𝒜 S i u ∈ grading 𝒜 S i := by
  induction u using TensorProduct.induction_on with
  | zero => simp [zero_mem (grading 𝒜 S i)]
  | tmul s x =>
      rw [num_tmul]
      exact mul_mem_of_mem_zero (grading 𝒜 S) s.2 (one_tmul_mem_grading 𝒜 S i x)
  | add u v hu hv => simpa only [map_add] using add_mem hu hv

/-- The degree-zero scalar `s ⊗ₜ 1` tensored with a degree-`i` element of `𝒜`. -/
public def numInvRight (i : ℕ) (s : S) : (𝒜 i) →+ (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 i) where
  toFun y := tmulOne 𝒜 S s ⊗ₜ[𝒜 0] toPiece₀ 𝒜 i y
  map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
  map_add' y z := by rw [map_add, TensorProduct.tmul_add]

/-- `numInvRight 𝒜 S i s` sends `y` to `(s ⊗ₜ 1) ⊗ y`. -/
@[simp]
public theorem numInvRight_apply (i : ℕ) (s : S) (y : 𝒜 i) :
    numInvRight 𝒜 S i s y = tmulOne 𝒜 S s ⊗ₜ[𝒜 0] toPiece₀ 𝒜 i y := rfl

/-- `Stacks.AlgebraicGeometry.ProjChartBaseChange.numInvRight`, additive in `s` as well. -/
public def numInvBilin (i : ℕ) : S →+ ((𝒜 i) →+ (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 i)) where
  toFun := numInvRight 𝒜 S i
  map_zero' := AddMonoidHom.ext fun y => by
    rw [numInvRight_apply, show tmulOne 𝒜 S 0 = 0 from Subtype.ext (by simp [tmulOne]),
      TensorProduct.zero_tmul, AddMonoidHom.zero_apply]
  map_add' s t := AddMonoidHom.ext fun y => by
    rw [numInvRight_apply, AddMonoidHom.add_apply, numInvRight_apply, numInvRight_apply,
      show tmulOne 𝒜 S (s + t) = tmulOne 𝒜 S s + tmulOne 𝒜 S t from
        Subtype.ext (by simp [tmulOne, TensorProduct.add_tmul]),
      TensorProduct.add_tmul]

/-- `numInvBilin 𝒜 S i` sends `s` to `numInvRight 𝒜 S i s`. -/
@[simp]
public theorem numInvBilin_apply (i : ℕ) (s : S) :
    numInvBilin 𝒜 S i s = numInvRight 𝒜 S i s := rfl

/-- The map `S ⊗[R] 𝒜 i ⟶ (S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} 𝒜 i` sending `s ⊗ₜ y` to `(s ⊗ₜ 1) ⊗ y`. -/
public def numInv (i : ℕ) : S ⊗[R] (𝒜 i) →+ (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 i) :=
  TensorProduct.liftAddHom (numInvBilin 𝒜 S i) fun r s y => by
    have hc : algebraMap R A r ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 r
    have h1 : tmulOne 𝒜 S (r • s) = (⟨_, hc⟩ : 𝒜 0) • tmulOne 𝒜 S s :=
      Subtype.ext (by
        rw [coe_smul_gradingZero]
        simp [tmulOne, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
    have h2 : toPiece₀ 𝒜 i (r • y) = (⟨_, hc⟩ : 𝒜 0) • toPiece₀ 𝒜 i y :=
      Subtype.ext (by rw [coe_smul_piece₀]; simp [Algebra.smul_def])
    rw [numInvBilin_apply, numInvBilin_apply, numInvRight_apply, numInvRight_apply, h1, h2,
      TensorProduct.smul_tmul]

/-- `numInv` sends `s ⊗ₜ y` to `(s ⊗ₜ 1) ⊗ y`. -/
@[simp]
public theorem numInv_tmul (i : ℕ) (s : S) (y : 𝒜 i) :
    numInv 𝒜 S i (s ⊗ₜ[R] y) = tmulOne 𝒜 S s ⊗ₜ[𝒜 0] toPiece₀ 𝒜 i y := rfl

/-- The numerator map composed with `numInv` is the comparison map `(𝒜 i).toBaseChange S`. -/
public theorem num_numInv (i : ℕ) (w : S ⊗[R] (𝒜 i)) :
    num 𝒜 S i (numInv 𝒜 S i w) = ((𝒜 i).toBaseChange S w : S ⊗[R] A) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s y =>
      rw [numInv_tmul, num_tmul, Submodule.coe_toBaseChange_tmul]
      simp [tmulOne, Algebra.TensorProduct.tmul_mul_tmul]
  | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, Submodule.coe_add]

/-- Every `s ⊗ x` with `s` in the degree-zero part of the base change is in the range of
`Stacks.AlgebraicGeometry.ProjChartBaseChange.numInv`. -/
public theorem exists_numInv_eq_tmul (i : ℕ) (σ : S ⊗[R] (𝒜 0)) (x : piece₀ 𝒜 i) :
    ∃ w, numInv 𝒜 S i w = ((𝒜 0).toBaseChange S σ) ⊗ₜ[𝒜 0] x := by
  induction σ using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero, TensorProduct.zero_tmul]⟩
  | tmul s c =>
      have hcx : (c : A) * (x : A) ∈ 𝒜 i := by
        exact mul_mem_of_mem_zero 𝒜 c.2 ((mem_piece₀ 𝒜 i _).mp x.2)
      refine ⟨s ⊗ₜ[R] ⟨(c : A) * (x : A), hcx⟩, ?_⟩
      have h1 : (𝒜 0).toBaseChange S (s ⊗ₜ[R] c) = c • tmulOne 𝒜 S s :=
        Subtype.ext (by
          rw [Submodule.coe_toBaseChange_tmul, coe_smul_gradingZero]
          simp [tmulOne, Algebra.TensorProduct.tmul_mul_tmul])
      rw [numInv_tmul, h1, TensorProduct.smul_tmul]
      congr 1
  | add σ₁ σ₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁⟩ := h₁
      obtain ⟨w₂, hw₂⟩ := h₂
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂, map_add, TensorProduct.add_tmul]⟩

/-- The map `Stacks.AlgebraicGeometry.ProjChartBaseChange.numInv` is surjective. -/
public theorem numInv_surjective (i : ℕ) : Function.Surjective (numInv 𝒜 S i) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s x =>
      obtain ⟨σ, hσ⟩ := (𝒜 0).toBaseChange_surjective' S s.2
      obtain ⟨w, hw⟩ := exists_numInv_eq_tmul 𝒜 S i σ x
      exact ⟨w, by rw [hw]; congr 1; exact Subtype.ext hσ⟩
  | add u v hu hv =>
      obtain ⟨w₁, hw₁⟩ := hu
      obtain ⟨w₂, hw₂⟩ := hv
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂]⟩

/-- The numerator map `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} 𝒜 i ⟶ S ⊗[R] A` is injective: the degree-`i` piece of
the base change is the base change of the degree-`i` piece. -/
public theorem num_injective (i : ℕ) : Function.Injective (num 𝒜 S i) := by
  refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
  obtain ⟨w, rfl⟩ := numInv_surjective 𝒜 S i u
  rw [num_numInv] at hu
  obtain rfl : w = 0 := by
    refine DirectSum.toBaseChange_injective 𝒜 (S := S) i ?_
    rw [map_zero]
    exact Submodule.coe_eq_zero.mp hu
  exact map_zero _

/-! ### The comparison on a standard affine chart -/

section Chart

variable {d : ℕ} {a : A}

/-- The chart map of the base change, as a homomorphism of `𝒜 0`-algebras. -/
public def awayAlgMap (ha : a ∈ 𝒜 d) :
    Away 𝒜 a →ₐ[𝒜 0] Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  { awayMap 𝒜 S a with
    commutes' := fun c => by
      have hc : (c : A) ∈ 𝒜 (0 • d) := by rw [zero_nsmul]; exact c.2
      rw [← awayMk_zero_eq_algebraMap 𝒜 ha c hc]
      change awayMap 𝒜 S a (Away.mk 𝒜 ha 0 (c : A) hc) = _
      rw [awayMap_mk 𝒜 S ha 0 (c : A) hc]
      exact awayMk_zero_eq_algebraMap (grading 𝒜 S) (tmul_one_mem 𝒜 S ha)
        (gradedZeroMap 𝒜 S c) _ }

/-- The underlying map of `awayAlgMap` is `awayMap`. -/
@[simp]
public theorem awayAlgMap_apply (ha : a ∈ 𝒜 d) (z : Away 𝒜 a) :
    awayAlgMap 𝒜 S ha z = awayMap 𝒜 S a z := rfl

/-- The chart comparison map `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a ⟶ Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`,
`s ⊗ z ↦ s · awayMap z`, the `(S ⊗[R] 𝒜) 0`-algebra map extending
`Stacks.AlgebraicGeometry.ProjChartBaseChange.awayAlgMap`. -/
public def chartMap (ha : a ∈ 𝒜 d) :
    ((grading 𝒜 S 0) ⊗[𝒜 0] (Away 𝒜 a)) →ₐ[grading 𝒜 S 0]
      Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  AlgHom.liftEquiv (𝒜 0) (grading 𝒜 S 0) (Away 𝒜 a)
    (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) (awayAlgMap 𝒜 S ha)

/-- The chart comparison map sends `s ⊗ z` to `s • awayMap z`. -/
@[simp]
public theorem chartMap_tmul (ha : a ∈ 𝒜 d) (s : grading 𝒜 S 0) (z : Away 𝒜 a) :
    chartMap 𝒜 S ha (s ⊗ₜ[𝒜 0] z) = s • awayMap 𝒜 S a z := rfl

/-- The chart comparison map is surjective. -/
public theorem chartMap_surjective (ha : a ∈ 𝒜 d) :
    Function.Surjective (chartMap 𝒜 S ha) := by
  have hle : Submodule.span (grading 𝒜 S 0) (Set.range (awayMap 𝒜 S a)) ≤
      LinearMap.range (chartMap 𝒜 S ha).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact ⟨1 ⊗ₜ[𝒜 0] z, by rw [AlgHom.toLinearMap_apply, chartMap_tmul, one_smul]⟩
  exact fun z => hle ((span_range_awayMap_eq_top 𝒜 S ha).ge Submodule.mem_top)

/-- An element of
`(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} 𝒜 (n • d)` pushed into the tensor product with `Away 𝒜 a` and compared
is the fraction whose numerator is its image under
`Stacks.AlgebraicGeometry.ProjChartBaseChange.num` and whose denominator is `(1 ⊗ₜ a) ^ n`. -/
public theorem chartMap_lTensor_mkLin (ha : a ∈ 𝒜 d) (n : ℕ)
    (v : (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 (n • d)))
    (hv : num 𝒜 S (n • d) v ∈ grading 𝒜 S (n • d)) :
    chartMap 𝒜 S ha (LinearMap.lTensor (grading 𝒜 S 0) (mkLin 𝒜 ha n) v) =
      Away.mk (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n (num 𝒜 S (n • d) v) hv := by
  induction v using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact ((awayMk_congr (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n hv (zero_mem _)
        (map_zero (num 𝒜 S (n • d)))).trans
        (awayMk_zero (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n)).symm
  | tmul s x =>
      have hx := one_tmul_mem_grading 𝒜 S (n • d) x
      rw [LinearMap.lTensor_tmul, chartMap_tmul, mkLin_apply,
        awayMap_mk 𝒜 S ha n (x : A) ((mem_piece₀ 𝒜 (n • d) _).mp x.2)]
      exact (awayMk_smul_zero (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n s
        ((1 : S) ⊗ₜ[R] (x : A)) (num 𝒜 S (n • d) (s ⊗ₜ[𝒜 0] x)) hx hv rfl).symm
  | add w₁ w₂ h₁ h₂ =>
      rw [map_add, map_add, h₁ (num_mem 𝒜 S (n • d) w₁), h₂ (num_mem 𝒜 S (n • d) w₂),
        awayMk_congr (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n hv
          (add_mem (num_mem 𝒜 S (n • d) w₁) (num_mem 𝒜 S (n • d) w₂))
          (map_add (num 𝒜 S (n • d)) w₁ w₂),
        ProjAwayBaseChange.awayMk_add (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n]

/-- The numerator map intertwines the transition map `mulPowTo` of the direct system with
multiplication by `(1 ⊗ₜ a) ^ k`. -/
public theorem num_lTensor_mulPowTo (ha : a ∈ 𝒜 d) (n m k : ℕ) (hk : n + k = m)
    (v : (grading 𝒜 S 0) ⊗[𝒜 0] (piece₀ 𝒜 (n • d))) :
    num 𝒜 S (m • d) (LinearMap.lTensor (grading 𝒜 S 0) (mulPowTo 𝒜 ha n m k hk) v) =
      ((1 : S) ⊗ₜ[R] a) ^ k * num 𝒜 S (n • d) v := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, mul_zero]
  | tmul s x =>
      rw [LinearMap.lTensor_tmul, num_tmul, num_tmul, mulPowTo_coe,
        show ((1 : S) ⊗ₜ[R] (a ^ k * (x : A))) =
          ((1 : S) ⊗ₜ[R] a) ^ k * ((1 : S) ⊗ₜ[R] (x : A)) by
            rw [Algebra.TensorProduct.tmul_pow, one_pow,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
      ring
  | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mul_add]

/-- The chart comparison map is injective. -/
public theorem chartMap_injective (ha : a ∈ 𝒜 d) :
    Function.Injective (chartMap 𝒜 S ha) := by
  refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
  obtain ⟨n, v, rfl⟩ := exists_lTensor_mkLin_eq 𝒜 ha u
  rw [chartMap_lTensor_mkLin 𝒜 S ha n v (num_mem 𝒜 S (n • d) v),
    awayMk_eq_zero_iff] at hu
  obtain ⟨k, hk⟩ := hu
  have hz : LinearMap.lTensor (grading 𝒜 S 0) (mulPowTo 𝒜 ha n (n + k) k rfl) v = 0 := by
    refine num_injective 𝒜 S ((n + k) • d) ?_
    rw [num_lTensor_mulPowTo 𝒜 S ha n (n + k) k rfl, hk, map_zero]
  have hcomp : (mkLin 𝒜 ha (n + k)).comp (mulPowTo 𝒜 ha n (n + k) k rfl) = mkLin 𝒜 ha n :=
    LinearMap.ext fun x => mkLin_mulPowTo 𝒜 ha n (n + k) k rfl x
  rw [← hcomp, LinearMap.lTensor_comp_apply, hz, map_zero]

/-- The chart-level base-change isomorphism
`(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a ≅ Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`. -/
public def chartEquiv (ha : a ∈ 𝒜 d) :
    ((grading 𝒜 S 0) ⊗[𝒜 0] (Away 𝒜 a)) ≃+* Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  RingEquiv.ofBijective (chartMap 𝒜 S ha).toRingHom
    ⟨chartMap_injective 𝒜 S ha, chartMap_surjective 𝒜 S ha⟩

/-- The chart-level base-change isomorphism sends `s ⊗ z` to `s • awayMap z`. -/
@[simp]
public theorem chartEquiv_tmul (ha : a ∈ 𝒜 d) (s : grading 𝒜 S 0) (z : Away 𝒜 a) :
    chartEquiv 𝒜 S ha (s ⊗ₜ[𝒜 0] z) = s • awayMap 𝒜 S a z := rfl

end Chart

end Algebras

end Stacks.AlgebraicGeometry.ProjChartBaseChange

end
