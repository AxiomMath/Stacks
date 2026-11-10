module

public import StacksFrontier.Algebra.DifferentialGraded.TensorProductInclusion
public import StacksFrontier.RingTheory.Koszul.PowAlgebraMultiplication

/-!
# The Koszul algebra of a concatenation is a tensor product of Koszul algebras

Let `g₁, …, g_r` and `h₁, …, h_s` be elements of a commutative ring `R` and let `t` be a natural
number. The Koszul differential graded algebra of the concatenated sequence is the tensor product
of the Koszul algebras of the two pieces,
$$K_t(g_1, \ldots, g_r, h_1, \ldots, h_s) \cong K_t(g_1, \ldots, g_r) \otimes_R
  K_t(h_1, \ldots, h_s),$$
as differential graded algebras. The isomorphism sends the generator `ξ_i` of the left piece to
`ξ_i ⊗ 1` and the generator `ξ_j` of the right piece to `1 ⊗ ξ_j`.

This is the differential graded form of the isomorphism of Koszul complexes of Tag 0664, which is
an isomorphism of complexes only; the multiplicative structure is extra information and is not
part of that statement.

## Main definitions

* `Koszul.powVec`: a vector of `Rʳ`, named as a generator of the Koszul algebra `K_t`.
* `Koszul.coordLeft` and `Koszul.coordRight`: the two coordinate projections of `R^{r+s}`.
* `Koszul.appendInclLeft` and `Koszul.appendInclRight`: the two coordinate inclusions into
  `R^{r+s}`.
* `Koszul.appendFromLeft` and `Koszul.appendFromRight`: the two homomorphisms of the pieces into
  the Koszul algebra of the concatenation.
* `Koszul.powAppendFromTensor`: the homomorphism `K_t(g) ⊗_R K_t(h) → K_t(g, h)`.
* `Koszul.powAppendToTensor`: the homomorphism `K_t(g, h) → K_t(g) ⊗_R K_t(h)` inverse to it.

## Main results

* `Koszul.seqDual_append_apply`: the functional of the concatenation is the sum of the two
  functionals read on the two groups of coordinates.
* `Koszul.powAppendToTensor_powAppendFromTensor` and
  `Koszul.powAppendFromTensor_powAppendToTensor`: the two composites are the identity.
* `Koszul.powAppendFromTensor_bijective`: `Koszul.powAppendFromTensor` is bijective, so it is an
  isomorphism of differential graded algebras.

## Implementation notes

The homomorphism out of the tensor product comes from the universal property
`DifferentialGradedAlgebra.tensorLift`, whose Koszul anticommutation hypothesis holds by
`Koszul.anticommutesAlong_cohomological`: the Koszul algebra of the concatenation is graded
commutative, being an exterior algebra in the cohomological grading. The homomorphism into the
tensor product comes from the universal property of the exterior algebra applied to the linear map
`v ↦ ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')`, where `v'` and `v''` are the two groups of coordinates of `v`; the
square-zero hypothesis combines `Koszul.powVec_mul_self` on each factor with
`DifferentialGradedAlgebra.tensorIncl_add_swap_of_mem_neg_one` for the cross terms.

Every element is named at the carrier type of the differential graded algebra it belongs to, which
is what `Koszul.powVec` is for. The graded tensor product needs the graded-algebra instance of
each factor, and that instance is found only when the submodule family and the element live over
the same carrier; a type ascription on a bare generator of the exterior algebra does not survive
elaboration, and the instance search then fails.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0664](https://stacks.math.columbia.edu/tag/0664)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R] {r s : ℕ}

section Generators

/-- A vector of `Rʳ`, named as an element of the Koszul algebra `K_t` rather than of the exterior
algebra that its carrier unfolds to. -/
def powVec {q : ℕ} (f : Fin q → R) (t : ℕ) : (Fin q → R) →ₗ[R] (powAlgebra f t).A :=
  ExteriorAlgebra.ι R

/-- `Koszul.powVec f t v` is the generator `ι v` of the exterior algebra. -/
theorem powVec_eq {q : ℕ} (f : Fin q → R) (t : ℕ) (v : Fin q → R) :
    powVec f t v = (ExteriorAlgebra.ι R v : ExteriorAlgebra R (Fin q → R)) := rfl

/-- A generator of `K_t` lies in degree `-1`. -/
theorem powVec_mem_grading {q : ℕ} (f : Fin q → R) (t : ℕ) (v : Fin q → R) :
    powVec f t v ∈ (powAlgebra f t).grading (-1) :=
  ι_mem_powAlgebra_grading f t v

/-- A generator of `K_t` squares to zero. -/
theorem powVec_mul_self {q : ℕ} (f : Fin q → R) (t : ℕ) (v : Fin q → R) :
    powVec f t v * powVec f t v = 0 :=
  ExteriorAlgebra.ι_sq_zero v

/-- The differential of `K_t` on a generator is the value of the functional of the sequence. -/
theorem d_powVec {q : ℕ} (f : Fin q → R) (t : ℕ) (v : Fin q → R) :
    (powAlgebra f t).d (powVec f t v) =
      algebraMap R (powAlgebra f t).A (seqDual (fun i => f i ^ t) v) :=
  CliffordAlgebra.contractLeft_ι (0 : QuadraticForm R (Fin q → R)) _ _

end Generators

section Coordinates

/-- The first `r` coordinates of `R^{r+s}`. -/
def coordLeft (R : Type u) [CommRing R] (r s : ℕ) :
    (Fin (r + s) → R) →ₗ[R] (Fin r → R) :=
  LinearMap.funLeft R R (Fin.castAdd s)

/-- The last `s` coordinates of `R^{r+s}`. -/
def coordRight (R : Type u) [CommRing R] (r s : ℕ) :
    (Fin (r + s) → R) →ₗ[R] (Fin s → R) :=
  LinearMap.funLeft R R (Fin.natAdd r)

/-- The `i`-th coordinate of `Koszul.coordLeft R r s v` is the `i`-th coordinate of `v`. -/
@[simp] theorem coordLeft_apply (v : Fin (r + s) → R) (i : Fin r) :
    coordLeft R r s v i = v (Fin.castAdd s i) := rfl

/-- The `i`-th coordinate of `Koszul.coordRight R r s v` is the `(r + i)`-th coordinate of `v`. -/
@[simp] theorem coordRight_apply (v : Fin (r + s) → R) (i : Fin s) :
    coordRight R r s v i = v (Fin.natAdd r i) := rfl

/-- `(w, 0) + (0, w') = (w, w')` in `R^{r+s}`. -/
theorem append_zero_add_zero_append (w : Fin r → R) (w' : Fin s → R) :
    Fin.append w (0 : Fin s → R) + Fin.append (0 : Fin r → R) w' = Fin.append w w' := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Pi.add_apply, Fin.append_left]
    simp
  · simp only [Pi.add_apply, Fin.append_right]
    simp

/-- `(w + w', 0) = (w, 0) + (w', 0)` in `R^{r+s}`. -/
theorem append_zero_add (w w' : Fin r → R) :
    Fin.append (w + w') (0 : Fin s → R) =
      Fin.append w (0 : Fin s → R) + Fin.append w' (0 : Fin s → R) := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Pi.add_apply, Fin.append_left]
  · simp only [Pi.add_apply, Fin.append_right]
    simp

/-- `(c • w, 0) = c • (w, 0)` in `R^{r+s}`. -/
theorem append_zero_smul (c : R) (w : Fin r → R) :
    Fin.append (c • w) (0 : Fin s → R) = c • Fin.append w (0 : Fin s → R) := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Pi.smul_apply, Fin.append_left]
  · simp only [Pi.smul_apply, Fin.append_right]
    simp

/-- `(0, w + w') = (0, w) + (0, w')` in `R^{r+s}`. -/
theorem zero_append_add (w w' : Fin s → R) :
    Fin.append (0 : Fin r → R) (w + w') =
      Fin.append (0 : Fin r → R) w + Fin.append (0 : Fin r → R) w' := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Pi.add_apply, Fin.append_left]
    simp
  · simp only [Pi.add_apply, Fin.append_right]

/-- `(0, c • w) = c • (0, w)` in `R^{r+s}`. -/
theorem zero_append_smul (c : R) (w : Fin s → R) :
    Fin.append (0 : Fin r → R) (c • w) = c • Fin.append (0 : Fin r → R) w := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Pi.smul_apply, Fin.append_left]
    simp
  · simp only [Pi.smul_apply, Fin.append_right]

/-- The inclusion of `Rʳ` into `R^{r+s}` as the first `r` coordinates. -/
def appendInclLeft (R : Type u) [CommRing R] (r s : ℕ) :
    (Fin r → R) →ₗ[R] (Fin (r + s) → R) where
  toFun w := Fin.append w 0
  map_add' := append_zero_add
  map_smul' := append_zero_smul

/-- The inclusion of `R^s` into `R^{r+s}` as the last `s` coordinates. -/
def appendInclRight (R : Type u) [CommRing R] (r s : ℕ) :
    (Fin s → R) →ₗ[R] (Fin (r + s) → R) where
  toFun w := Fin.append 0 w
  map_add' := zero_append_add
  map_smul' := zero_append_smul

/-- `Koszul.appendInclLeft R r s w` is the concatenation `(w, 0)`. -/
@[simp] theorem appendInclLeft_apply (w : Fin r → R) :
    appendInclLeft R r s w = Fin.append w 0 := rfl

/-- `Koszul.appendInclRight R r s w` is the concatenation `(0, w)`. -/
@[simp] theorem appendInclRight_apply (w : Fin s → R) :
    appendInclRight R r s w = Fin.append 0 w := rfl

/-- The first `r` coordinates of `(w, 0)` are `w`. -/
theorem coordLeft_appendInclLeft (w : Fin r → R) :
    coordLeft R r s (appendInclLeft R r s w) = w := by
  refine funext fun i => ?_
  rw [coordLeft_apply, appendInclLeft_apply, Fin.append_left]

/-- The last `s` coordinates of `(w, 0)` vanish. -/
theorem coordRight_appendInclLeft (w : Fin r → R) :
    coordRight R r s (appendInclLeft R r s w) = 0 := by
  refine funext fun i => ?_
  rw [coordRight_apply, appendInclLeft_apply, Fin.append_right]

/-- The first `r` coordinates of `(0, w)` vanish. -/
theorem coordLeft_appendInclRight (w : Fin s → R) :
    coordLeft R r s (appendInclRight R r s w) = 0 := by
  refine funext fun i => ?_
  rw [coordLeft_apply, appendInclRight_apply, Fin.append_left]

/-- The last `s` coordinates of `(0, w)` are `w`. -/
theorem coordRight_appendInclRight (w : Fin s → R) :
    coordRight R r s (appendInclRight R r s w) = w := by
  refine funext fun i => ?_
  rw [coordRight_apply, appendInclRight_apply, Fin.append_right]

/-- A vector of `R^{r+s}` is the concatenation of its two groups of coordinates. -/
theorem append_coordLeft_coordRight (v : Fin (r + s) → R) :
    Fin.append (coordLeft R r s v) (coordRight R r s v) = v := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, coordLeft_apply]
  · rw [Fin.append_right, coordRight_apply]

end Coordinates

section Functional

/-- The functional of a concatenated sequence is the sum of the two functionals read on the two
groups of coordinates. -/
theorem seqDual_append_apply (g : Fin r → R) (h : Fin s → R) (t : ℕ) (v : Fin (r + s) → R) :
    seqDual (fun j => Fin.append g h j ^ t) v =
      seqDual (fun i => g i ^ t) (coordLeft R r s v) +
        seqDual (fun i => h i ^ t) (coordRight R r s v) := by
  rw [seqDual_apply, seqDual_apply, seqDual_apply, Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · rw [coordLeft_apply, Fin.append_left]
  · rw [coordRight_apply, Fin.append_right]

/-- The functional of the concatenated sequence restricts to the functional of `g` on the first
`r` coordinates. -/
theorem seqDual_comp_appendInclLeft (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    seqDual (fun j => Fin.append g h j ^ t) ∘ₗ appendInclLeft R r s =
      seqDual (fun i => g i ^ t) := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, seqDual_append_apply, coordLeft_appendInclLeft,
    coordRight_appendInclLeft, map_zero, add_zero]

/-- The functional of the concatenated sequence restricts to the functional of `h` on the last
`s` coordinates. -/
theorem seqDual_comp_appendInclRight (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    seqDual (fun j => Fin.append g h j ^ t) ∘ₗ appendInclRight R r s =
      seqDual (fun i => h i ^ t) := by
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.comp_apply, seqDual_append_apply, coordLeft_appendInclRight,
    coordRight_appendInclRight, map_zero, zero_add]

end Functional

section Pieces

/-- The homomorphism `K_t(g) → K_t(g, h)` of differential graded algebras induced by the
inclusion of the first `r` coordinates. -/
def appendFromLeft (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    (powAlgebra g t).Hom (powAlgebra (Fin.append g h) t) where
  toAlgebraHom := ExteriorAlgebra.map (appendInclLeft R r s)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin r → R) (Fin (r + s) → R) _ ha
  map_d a := by
    change ExteriorAlgebra.map (appendInclLeft R r s)
        (contraction (seqDual fun i => g i ^ t) a) =
      contraction (seqDual fun j => Fin.append g h j ^ t)
        (ExteriorAlgebra.map (appendInclLeft R r s) a)
    rw [← seqDual_comp_appendInclLeft g h t]
    exact (contractLeft_exteriorAlgebraMap (appendInclLeft R r s) _ a).symm

/-- The homomorphism `K_t(h) → K_t(g, h)` of differential graded algebras induced by the
inclusion of the last `s` coordinates. -/
def appendFromRight (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    (powAlgebra h t).Hom (powAlgebra (Fin.append g h) t) where
  toAlgebraHom := ExteriorAlgebra.map (appendInclRight R r s)
  map_grading _ _ ha :=
    map_mem_cohomologicalExteriorGrade R (Fin s → R) (Fin (r + s) → R) _ ha
  map_d a := by
    change ExteriorAlgebra.map (appendInclRight R r s)
        (contraction (seqDual fun i => h i ^ t) a) =
      contraction (seqDual fun j => Fin.append g h j ^ t)
        (ExteriorAlgebra.map (appendInclRight R r s) a)
    rw [← seqDual_comp_appendInclRight g h t]
    exact (contractLeft_exteriorAlgebraMap (appendInclRight R r s) _ a).symm

/-- The underlying algebra homomorphism of `Koszul.appendFromLeft` is the map of exterior
algebras induced by `Koszul.appendInclLeft`. -/
@[simp] theorem appendFromLeft_toAlgebraHom (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    (appendFromLeft g h t).toAlgebraHom = ExteriorAlgebra.map (appendInclLeft R r s) := rfl

/-- The underlying algebra homomorphism of `Koszul.appendFromRight` is the map of exterior
algebras induced by `Koszul.appendInclRight`. -/
@[simp] theorem appendFromRight_toAlgebraHom (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    (appendFromRight g h t).toAlgebraHom = ExteriorAlgebra.map (appendInclRight R r s) := rfl

/-- `Koszul.appendFromLeft` sends the generator `ξ(w)` to the generator `ξ(w, 0)`. -/
theorem appendFromLeft_powVec (g : Fin r → R) (h : Fin s → R) (t : ℕ) (w : Fin r → R) :
    (appendFromLeft g h t).toAlgebraHom (powVec g t w) =
      powVec (Fin.append g h) t (Fin.append w 0) := by
  change ExteriorAlgebra.map (appendInclLeft R r s) (ExteriorAlgebra.ι R w) =
    (ExteriorAlgebra.ι R (Fin.append w 0) : ExteriorAlgebra R (Fin (r + s) → R))
  rw [ExteriorAlgebra.map_apply_ι, appendInclLeft_apply]

/-- `Koszul.appendFromRight` sends the generator `ξ(w)` to the generator `ξ(0, w)`. -/
theorem appendFromRight_powVec (g : Fin r → R) (h : Fin s → R) (t : ℕ) (w : Fin s → R) :
    (appendFromRight g h t).toAlgebraHom (powVec h t w) =
      powVec (Fin.append g h) t (Fin.append 0 w) := by
  change ExteriorAlgebra.map (appendInclRight R r s) (ExteriorAlgebra.ι R w) =
    (ExteriorAlgebra.ι R (Fin.append 0 w) : ExteriorAlgebra R (Fin (r + s) → R))
  rw [ExteriorAlgebra.map_apply_ι, appendInclRight_apply]

/-- **The homomorphism `K_t(g) ⊗_R K_t(h) → K_t(g, h)`**, sending `a ⊗ b` to the product of the
images of `a` and `b`. -/
def powAppendFromTensor (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).Hom (powAlgebra (Fin.append g h) t) :=
  tensorLift (anticommutesAlong_cohomological (appendFromLeft g h t) (appendFromRight g h t))

/-- `Koszul.powAppendFromTensor` sends `a ⊗ b` to the product of the images of `a` under
`Koszul.appendFromLeft` and of `b` under `Koszul.appendFromRight`. -/
theorem powAppendFromTensor_tmul (g : Fin r → R) (h : Fin s → R) (t : ℕ)
    (a : (powAlgebra g t).A) (b : (powAlgebra h t).A) :
    (powAppendFromTensor g h t).toAlgebraHom
        (a ᵍ⊗ₜ[R] b : (powAlgebra g t).grading ᵍ⊗[R] (powAlgebra h t).grading) =
      (appendFromLeft g h t).toAlgebraHom a * (appendFromRight g h t).toAlgebraHom b := rfl

end Pieces

section ToTensor

variable (g : Fin r → R) (h : Fin s → R) (t : ℕ)

/-- The element `ξ(v') ⊗ 1` of `K_t(g) ⊗_R K_t(h)` attached to the first group of coordinates
of `v`. -/
def appendTensorLeft (v : Fin (r + s) → R) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).A :=
  (tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom
    (powVec g t (coordLeft R r s v))

/-- The element `1 ⊗ ξ(v'')` of `K_t(g) ⊗_R K_t(h)` attached to the last group of coordinates
of `v`. -/
def appendTensorRight (v : Fin (r + s) → R) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).A :=
  (tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom
    (powVec h t (coordRight R r s v))

/-- `Koszul.appendTensorLeft g h t v` is the image of `ξ(v')` under the left inclusion. -/
theorem appendTensorLeft_def (v : Fin (r + s) → R) :
    appendTensorLeft g h t v =
      (tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom
        (powVec g t (coordLeft R r s v)) := rfl

/-- `Koszul.appendTensorRight g h t v` is the image of `ξ(v'')` under the right inclusion. -/
theorem appendTensorRight_def (v : Fin (r + s) → R) :
    appendTensorRight g h t v =
      (tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom
        (powVec h t (coordRight R r s v)) := rfl

/-- `ξ(v') ⊗ 1` lies in degree `-1` of `K_t(g) ⊗_R K_t(h)`. -/
theorem appendTensorLeft_mem_grading (v : Fin (r + s) → R) :
    appendTensorLeft g h t v ∈
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading (-1) :=
  (tensorInclLeft (powAlgebra g t) (powAlgebra h t)).map_grading (-1) _
    (powVec_mem_grading g t (coordLeft R r s v))

/-- `1 ⊗ ξ(v'')` lies in degree `-1` of `K_t(g) ⊗_R K_t(h)`. -/
theorem appendTensorRight_mem_grading (v : Fin (r + s) → R) :
    appendTensorRight g h t v ∈
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading (-1) :=
  (tensorInclRight (powAlgebra g t) (powAlgebra h t)).map_grading (-1) _
    (powVec_mem_grading h t (coordRight R r s v))

/-- The linear map `R^{r+s} → K_t(g) ⊗_R K_t(h)` sending `v` to `ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')`. -/
def powAppendToTensorMap :
    (Fin (r + s) → R) →ₗ[R] (tensorProduct (powAlgebra g t) (powAlgebra h t)).A :=
  (tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom.toLinearMap ∘ₗ
      powVec g t ∘ₗ coordLeft R r s +
    (tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom.toLinearMap ∘ₗ
      powVec h t ∘ₗ coordRight R r s

/-- `Koszul.powAppendToTensorMap g h t v = ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')`. -/
@[simp] theorem powAppendToTensorMap_apply (v : Fin (r + s) → R) :
    powAppendToTensorMap g h t v = appendTensorLeft g h t v + appendTensorRight g h t v := rfl

/-- `ξ(v') ⊗ 1` squares to zero. -/
theorem appendTensorLeft_mul_self (v : Fin (r + s) → R) :
    appendTensorLeft g h t v * appendTensorLeft g h t v = 0 := by
  rw [appendTensorLeft_def, ← map_mul, powVec_mul_self, map_zero]

/-- `1 ⊗ ξ(v'')` squares to zero. -/
theorem appendTensorRight_mul_self (v : Fin (r + s) → R) :
    appendTensorRight g h t v * appendTensorRight g h t v = 0 := by
  rw [appendTensorRight_def, ← map_mul, powVec_mul_self, map_zero]

/-- `ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')` squares to zero. -/
theorem powAppendToTensorMap_mul_self (v : Fin (r + s) → R) :
    powAppendToTensorMap g h t v * powAppendToTensorMap g h t v = 0 := by
  have hcross := tensorIncl_add_swap_of_mem_neg_one (powAlgebra g t) (powAlgebra h t)
    (powVec_mem_grading g t (coordLeft R r s v))
    (powVec_mem_grading h t (coordRight R r s v))
  rw [powAppendToTensorMap_apply, add_mul, mul_add, mul_add, appendTensorLeft_mul_self,
    appendTensorRight_mul_self, zero_add, add_zero, appendTensorLeft_def,
    appendTensorRight_def]
  exact hcross

/-- The underlying algebra homomorphism `K_t(g, h) → K_t(g) ⊗_R K_t(h)`. -/
def powAppendToTensorAlgHom :
    ExteriorAlgebra R (Fin (r + s) → R) →ₐ[R]
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).A :=
  ExteriorAlgebra.lift R ⟨powAppendToTensorMap g h t, powAppendToTensorMap_mul_self g h t⟩

/-- `Koszul.powAppendToTensorAlgHom` sends `ι v` to `ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')`. -/
@[simp] theorem powAppendToTensorAlgHom_ι (v : Fin (r + s) → R) :
    powAppendToTensorAlgHom g h t (ExteriorAlgebra.ι R v) =
      appendTensorLeft g h t v + appendTensorRight g h t v :=
  ExteriorAlgebra.lift_ι_apply R _ _ v

/-- `Koszul.powAppendToTensorAlgHom` sends `ι v` into degree `-1`. -/
theorem powAppendToTensorAlgHom_ι_mem (v : Fin (r + s) → R) :
    powAppendToTensorAlgHom g h t (ExteriorAlgebra.ι R v) ∈
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading (-1) := by
  rw [powAppendToTensorAlgHom_ι]
  exact Submodule.add_mem _ (appendTensorLeft_mem_grading g h t v)
    (appendTensorRight_mem_grading g h t v)

/-- `Koszul.powAppendToTensorAlgHom` sends a product of `k` vectors into degree `-k`. -/
theorem powAppendToTensorAlgHom_ιMulti_mem (k : ℕ) :
    ∀ w : Fin k → (Fin (r + s) → R),
      powAppendToTensorAlgHom g h t (ExteriorAlgebra.ιMulti R k w) ∈
        (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading (-(k : ℤ)) := by
  induction k with
  | zero =>
      intro w
      rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, show -((0 : ℕ) : ℤ) = 0 from by norm_num]
      exact SetLike.one_mem_graded
        (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading
  | succ j ih =>
      intro w
      rw [ιMulti_succ_apply, map_mul]
      have hmul := SetLike.mul_mem_graded (powAppendToTensorAlgHom_ι_mem g h t (w 0))
        (ih (Fin.tail w))
      rw [show (-1 : ℤ) + -(j : ℤ) = -((j + 1 : ℕ) : ℤ) from by push_cast; ring] at hmul
      exact hmul

/-- `Koszul.powAppendToTensorAlgHom` sends the `k`-th exterior power into degree `-k`. -/
theorem powAppendToTensorAlgHom_mem (k : ℕ)
    {a : ExteriorAlgebra R (Fin (r + s) → R)}
    (ha : a ∈ exteriorGrade R (Fin (r + s) → R) k) :
    powAppendToTensorAlgHom g h t a ∈
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading (-(k : ℤ)) := by
  rw [← (Submodule.ext_iff.mp
    (exteriorPower.ιMulti_span_fixedDegree R k (Fin (r + s) → R)))] at ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      exact powAppendToTensorAlgHom_ιMulti_mem g h t k w
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

/-- `Koszul.powAppendToTensorAlgHom` preserves the grading. -/
theorem powAppendToTensorAlgHom_mem_grading (m : ℤ)
    {a : ExteriorAlgebra R (Fin (r + s) → R)}
    (ha : a ∈ (powAlgebra (Fin.append g h) t).grading m) :
    powAppendToTensorAlgHom g h t a ∈
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).grading m := by
  rw [powAlgebra_grading] at ha
  by_cases hm : m ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [cohomologicalExteriorGrade_neg_natCast] at ha
    exact powAppendToTensorAlgHom_mem g h t k ha
  · have h0 : a = 0 := eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R _ (by omega) ha
    rw [h0, map_zero]
    exact Submodule.zero_mem _

/-- A homomorphism of differential graded algebras out of `K_t(f)` sends a generator to an
element whose differential is the value of the functional of `f`. -/
private theorem d_toAlgebraHom_powVec {q : ℕ} (f : Fin q → R)
    (B : DifferentialGradedAlgebra.{u, u} R) (φ : (powAlgebra f t).Hom B) (v : Fin q → R) :
    B.d (φ.toAlgebraHom (powVec f t v)) = algebraMap R B.A (seqDual (fun i => f i ^ t) v) := by
  have hd := φ.map_d (powVec f t v)
  rw [d_powVec] at hd
  rw [← hd]
  exact φ.toAlgebraHom.commutes _

/-- The differential of `ξ(v') ⊗ 1` is the value of the functional of `g` on `v'`. -/
theorem d_appendTensorLeft (v : Fin (r + s) → R) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).d (appendTensorLeft g h t v) =
      algebraMap R (tensorProduct (powAlgebra g t) (powAlgebra h t)).A
        (seqDual (fun i => g i ^ t) (coordLeft R r s v)) :=
  d_toAlgebraHom_powVec t g _ (tensorInclLeft (powAlgebra g t) (powAlgebra h t)) _

/-- The differential of `1 ⊗ ξ(v'')` is the value of the functional of `h` on `v''`. -/
theorem d_appendTensorRight (v : Fin (r + s) → R) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).d (appendTensorRight g h t v) =
      algebraMap R (tensorProduct (powAlgebra g t) (powAlgebra h t)).A
        (seqDual (fun i => h i ^ t) (coordRight R r s v)) :=
  d_toAlgebraHom_powVec t h _ (tensorInclRight (powAlgebra g t) (powAlgebra h t)) _

/-- The differential of `K_t(g) ⊗_R K_t(h)` takes the value of the functional of the
concatenated sequence on the image of a vector. -/
theorem d_powAppendToTensorAlgHom_ι (v : Fin (r + s) → R) :
    (tensorProduct (powAlgebra g t) (powAlgebra h t)).d
        (powAppendToTensorAlgHom g h t (ExteriorAlgebra.ι R v)) =
      algebraMap R (tensorProduct (powAlgebra g t) (powAlgebra h t)).A
        (seqDual (fun j => Fin.append g h j ^ t) v) := by
  rw [powAppendToTensorAlgHom_ι, map_add, d_appendTensorLeft, d_appendTensorRight,
    seqDual_append_apply, map_add]

/-- `Koszul.powAppendToTensorAlgHom` intertwines the differentials of `K_t(g, h)` and of
`K_t(g) ⊗_R K_t(h)`. -/
theorem powAppendToTensorAlgHom_map_contraction (a : ExteriorAlgebra R (Fin (r + s) → R)) :
    powAppendToTensorAlgHom g h t
        (contraction (seqDual (fun j => Fin.append g h j ^ t)) a) =
      (tensorProduct (powAlgebra g t) (powAlgebra h t)).d
        (powAppendToTensorAlgHom g h t a) := by
  have hsign : (((-1 : ℤ).negOnePow : ℤ)) = -1 := by
    rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, Int.negOnePow_neg, Int.negOnePow_one]
    rfl
  induction a using CliffordAlgebra.left_induction with
  | algebraMap c =>
      have hL : powAppendToTensorAlgHom g h t
          (contraction (seqDual (fun j => Fin.append g h j ^ t))
            (algebraMap R (ExteriorAlgebra R (Fin (r + s) → R)) c)) = 0 := by
        rw [CliffordAlgebra.contractLeft_algebraMap]
        exact map_zero _
      have hR : (tensorProduct (powAlgebra g t) (powAlgebra h t)).d
          (powAppendToTensorAlgHom g h t
            (algebraMap R (ExteriorAlgebra R (Fin (r + s) → R)) c)) = 0 := by
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul,
          d_one (tensorProduct (powAlgebra g t) (powAlgebra h t)), smul_zero]
      exact hL.trans hR.symm
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
      have hdx : contraction (seqDual (fun j => Fin.append g h j ^ t))
          (ExteriorAlgebra.ι R m * x) =
          seqDual (fun j => Fin.append g h j ^ t) m • x -
            ExteriorAlgebra.ι R m *
              contraction (seqDual (fun j => Fin.append g h j ^ t)) x :=
        CliffordAlgebra.contractLeft_ι_mul _ _ _
      have hleib := d_mul_of_mem (tensorProduct (powAlgebra g t) (powAlgebra h t))
        (powAppendToTensorAlgHom_ι_mem g h t m) (powAppendToTensorAlgHom g h t x)
      rw [hsign] at hleib
      rw [hdx, map_sub, map_smul,
        map_mul (powAppendToTensorAlgHom g h t) (ExteriorAlgebra.ι R m)
          (contraction (seqDual (fun j => Fin.append g h j ^ t)) x), hx,
        map_mul (powAppendToTensorAlgHom g h t) (ExteriorAlgebra.ι R m) x, hleib,
        d_powAppendToTensorAlgHom_ι, Algebra.smul_def, neg_smul, one_smul]
      abel

/-- **The homomorphism `K_t(g, h) → K_t(g) ⊗_R K_t(h)`** of differential graded algebras, sending
the generator `ξ_i` of the first group to `ξ_i ⊗ 1` and the generator `ξ_j` of the second group to
`1 ⊗ ξ_j`. -/
def powAppendToTensor :
    (powAlgebra (Fin.append g h) t).Hom (tensorProduct (powAlgebra g t) (powAlgebra h t)) where
  toAlgebraHom := powAppendToTensorAlgHom g h t
  map_grading m _ ha := powAppendToTensorAlgHom_mem_grading g h t m ha
  map_d a := powAppendToTensorAlgHom_map_contraction g h t a

/-- The underlying algebra homomorphism of `Koszul.powAppendToTensor` is
`Koszul.powAppendToTensorAlgHom`. -/
@[simp] theorem powAppendToTensor_toAlgebraHom :
    (powAppendToTensor g h t).toAlgebraHom = powAppendToTensorAlgHom g h t := rfl

/-- `Koszul.powAppendToTensor` sends the generator `ξ(v)` to `ξ(v') ⊗ 1 + 1 ⊗ ξ(v'')`. -/
theorem powAppendToTensor_powVec (v : Fin (r + s) → R) :
    (powAppendToTensor g h t).toAlgebraHom (powVec (Fin.append g h) t v) =
      appendTensorLeft g h t v + appendTensorRight g h t v :=
  powAppendToTensorAlgHom_ι g h t v

end ToTensor

section Composites

variable (g : Fin r → R) (h : Fin s → R) (t : ℕ)

/-- `Koszul.powAppendFromTensor` restricts to `Koszul.appendFromLeft` on the left factor. -/
private theorem powAppendFromTensor_inclLeft (a : (powAlgebra g t).A) :
    (powAppendFromTensor g h t).toAlgebraHom
        ((tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom a) =
      (appendFromLeft g h t).toAlgebraHom a := by
  have h0 : (powAppendFromTensor g h t).toAlgebraHom
      ((tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom a) =
      (appendFromLeft g h t).toAlgebraHom a *
        (appendFromRight g h t).toAlgebraHom (1 : (powAlgebra h t).A) := rfl
  rw [h0, map_one, mul_one]

/-- `Koszul.powAppendFromTensor` restricts to `Koszul.appendFromRight` on the right factor. -/
private theorem powAppendFromTensor_inclRight (b : (powAlgebra h t).A) :
    (powAppendFromTensor g h t).toAlgebraHom
        ((tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom b) =
      (appendFromRight g h t).toAlgebraHom b := by
  have h0 : (powAppendFromTensor g h t).toAlgebraHom
      ((tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom b) =
      (appendFromLeft g h t).toAlgebraHom (1 : (powAlgebra g t).A) *
        (appendFromRight g h t).toAlgebraHom b := rfl
  rw [h0, map_one, one_mul]

/-- `Koszul.powAppendFromTensor` sends `ξ(v') ⊗ 1` to the generator `ξ(v', 0)`. -/
theorem powAppendFromTensor_appendTensorLeft (v : Fin (r + s) → R) :
    (powAppendFromTensor g h t).toAlgebraHom (appendTensorLeft g h t v) =
      powVec (Fin.append g h) t (Fin.append (coordLeft R r s v) 0) := by
  rw [appendTensorLeft_def, powAppendFromTensor_inclLeft, appendFromLeft_powVec]

/-- `Koszul.powAppendFromTensor` sends `1 ⊗ ξ(v'')` to the generator `ξ(0, v'')`. -/
theorem powAppendFromTensor_appendTensorRight (v : Fin (r + s) → R) :
    (powAppendFromTensor g h t).toAlgebraHom (appendTensorRight g h t v) =
      powVec (Fin.append g h) t (Fin.append 0 (coordRight R r s v)) := by
  rw [appendTensorRight_def, powAppendFromTensor_inclRight, appendFromRight_powVec]

/-- **`K_t(g, h) → K_t(g) ⊗_R K_t(h) → K_t(g, h)` is the identity.** -/
theorem powAppendFromTensor_powAppendToTensor :
    (powAppendFromTensor g h t).toAlgebraHom.comp (powAppendToTensorAlgHom g h t) =
      AlgHom.id R (ExteriorAlgebra R (Fin (r + s) → R)) := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  change (powAppendFromTensor g h t).toAlgebraHom
      (powAppendToTensorAlgHom g h t (ExteriorAlgebra.ι R v)) = ExteriorAlgebra.ι R v
  rw [powAppendToTensorAlgHom_ι, map_add, powAppendFromTensor_appendTensorLeft,
    powAppendFromTensor_appendTensorRight, ← map_add, append_zero_add_zero_append,
    append_coordLeft_coordRight]
  rfl

/-- `Koszul.powAppendToTensorAlgHom` sends the image of `ξ(w)` under `Koszul.appendFromLeft` to
`ξ(w) ⊗ 1`. -/
theorem powAppendToTensor_appendFromLeft (w : Fin r → R) :
    powAppendToTensorAlgHom g h t
        ((appendFromLeft g h t).toAlgebraHom (powVec g t w)) =
      appendTensorLeft g h t (appendInclLeft R r s w) := by
  rw [appendFromLeft_powVec]
  change (powAppendToTensor g h t).toAlgebraHom
      (powVec (Fin.append g h) t (Fin.append w 0)) = _
  rw [powAppendToTensor_powVec,
    show Fin.append w (0 : Fin s → R) = appendInclLeft R r s w from rfl,
    appendTensorRight_def, coordRight_appendInclLeft,
    show powVec h t (0 : Fin s → R) = 0 from map_zero _, map_zero, add_zero]

/-- `Koszul.powAppendToTensorAlgHom` sends the image of `ξ(w)` under `Koszul.appendFromRight` to
`1 ⊗ ξ(w)`. -/
theorem powAppendToTensor_appendFromRight (w : Fin s → R) :
    powAppendToTensorAlgHom g h t
        ((appendFromRight g h t).toAlgebraHom (powVec h t w)) =
      appendTensorRight g h t (appendInclRight R r s w) := by
  rw [appendFromRight_powVec]
  change (powAppendToTensor g h t).toAlgebraHom
      (powVec (Fin.append g h) t (Fin.append 0 w)) = _
  rw [powAppendToTensor_powVec,
    show Fin.append (0 : Fin r → R) w = appendInclRight R r s w from rfl,
    appendTensorLeft_def, coordLeft_appendInclRight,
    show powVec g t (0 : Fin r → R) = 0 from map_zero _, map_zero, zero_add]

/-- **`K_t(g) ⊗_R K_t(h) → K_t(g, h) → K_t(g) ⊗_R K_t(h)` is the identity.** -/
theorem powAppendToTensor_powAppendFromTensor :
    (powAppendToTensorAlgHom g h t).comp (powAppendFromTensor g h t).toAlgebraHom =
      AlgHom.id R (tensorProduct (powAlgebra g t) (powAlgebra h t)).A := by
  refine GradedTensorProduct.algHom_ext (powAlgebra g t).grading (powAlgebra h t).grading ?_ ?_
  · refine ExteriorAlgebra.hom_ext (LinearMap.ext fun w => ?_)
    change powAppendToTensorAlgHom g h t ((powAppendFromTensor g h t).toAlgebraHom
        ((tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom (powVec g t w))) =
      (tensorInclLeft (powAlgebra g t) (powAlgebra h t)).toAlgebraHom (powVec g t w)
    rw [powAppendFromTensor_inclLeft, powAppendToTensor_appendFromLeft, appendTensorLeft_def,
      coordLeft_appendInclLeft]
  · refine ExteriorAlgebra.hom_ext (LinearMap.ext fun w => ?_)
    change powAppendToTensorAlgHom g h t ((powAppendFromTensor g h t).toAlgebraHom
        ((tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom (powVec h t w))) =
      (tensorInclRight (powAlgebra g t) (powAlgebra h t)).toAlgebraHom (powVec h t w)
    rw [powAppendFromTensor_inclRight, powAppendToTensor_appendFromRight, appendTensorRight_def,
      coordRight_appendInclRight]

/-- **The Koszul algebra of a concatenated sequence is the tensor product of the Koszul algebras
of the two pieces.** The homomorphism `Koszul.powAppendFromTensor` is bijective, with inverse the
homomorphism `Koszul.powAppendToTensor` of differential graded algebras. -/
theorem powAppendFromTensor_bijective :
    Function.Bijective (powAppendFromTensor g h t).toAlgebraHom :=
  Function.bijective_iff_has_inverse.mpr ⟨powAppendToTensorAlgHom g h t,
    AlgHom.congr_fun (powAppendToTensor_powAppendFromTensor g h t),
    AlgHom.congr_fun (powAppendFromTensor_powAppendToTensor g h t)⟩

end Composites

end Koszul
