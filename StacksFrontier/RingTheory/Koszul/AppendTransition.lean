module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractTensor
public import StacksFrontier.RingTheory.Koszul.AppendTensorIsomorphism

/-!
# The append isomorphism of Koszul algebras is compatible with the transition maps

Let `g₁, …, g_r` and `h₁, …, h_s` be elements of a commutative ring `R` and let `1 ≤ t ≤ m`. The
Koszul algebra of the concatenated sequence is the tensor product of the Koszul algebras of the two
pieces, and both sides carry transition homomorphisms lowering the exponent from `m` to `t`: on the
left the transition homomorphism `τ_{m,t}` of the concatenated sequence, on the right the tensor
product `τ_{m,t} ⊗ τ_{m,t}` of the transition homomorphisms of the two pieces. This file proves
that the isomorphism of Tag 0664 identifies the two, so that the append isomorphism is an
isomorphism of inverse systems of differential graded algebras.

Concretely the composite
$$K_m(g, h) \longrightarrow K_m(g) \otimes_R K_m(h) \longrightarrow K_t(g) \otimes_R K_t(h)
  \longrightarrow K_t(g, h)$$
of the isomorphism into the tensor product, the tensor product of the two transition
homomorphisms, and the isomorphism back is the transition homomorphism `τ_{m,t}` of the
concatenated sequence.

## Main definitions

* `Koszul.powTensorTransition`: the homomorphism `τ_{m,t} ⊗ τ_{m,t}` of the tensor products,
  `K_m(g) ⊗_R K_m(h) → K_t(g) ⊗_R K_t(h)`.

## Main results

* `Koszul.append_mulLeft_pow`: scaling the coordinates of `R^{r+s}` by the `k`-th powers of the
  concatenated sequence is the concatenation of the two one-sided scalings.
* `Koszul.powTransition_comp_appendFromLeft` and `Koszul.powTransition_comp_appendFromRight`: the
  transition homomorphisms commute with the two inclusions of the pieces.
* `Koszul.powAppendFromTensor_powTensorTransition`: **the append isomorphism commutes with the
  transition homomorphisms.**

## Implementation notes

Every identity is checked on a generator, by `ExteriorAlgebra.hom_ext`: both sides are algebra
homomorphisms out of an exterior algebra, and the generator is named at the carrier type of the
differential graded algebra it belongs to through `Koszul.powVec`, since a bare type ascription on
a generator of the exterior algebra does not survive elaboration and the graded-algebra instance
search then fails.

The value of the composite on a generator `ξ(v)` is the sum of its two one-sided pieces, and each
piece is computed by rewriting the scaled vector's two groups of coordinates with
`Koszul.coordLeft_mulLeft_pow` and `Koszul.coordRight_mulLeft_pow`: this is what lets the already
available lemmas `Koszul.powAppendFromTensor_appendTensorLeft` and
`Koszul.powAppendFromTensor_appendTensorRight` finish the computation, the sum of the two pieces
being reassembled by `Koszul.append_zero_add_zero_append`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0664](https://stacks.math.columbia.edu/tag/0664)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R] {r s : ℕ}

section Scaling

variable (g : Fin r → R) (h : Fin s → R) (k : ℕ)

/-- The first `r` coordinates of a vector of `R^{r+s}` scaled by the `k`-th powers of the
concatenated sequence are its first `r` coordinates scaled by the `k`-th powers of `g`. -/
theorem coordLeft_mulLeft_pow (v : Fin (r + s) → R) :
    coordLeft R r s (LinearMap.mulLeft R (fun j => Fin.append g h j ^ k) v) =
      LinearMap.mulLeft R (fun i => g i ^ k) (coordLeft R r s v) := by
  refine funext fun i => ?_
  simp only [coordLeft_apply, LinearMap.mulLeft_apply, Pi.mul_apply, Fin.append_left]

/-- The last `s` coordinates of a vector of `R^{r+s}` scaled by the `k`-th powers of the
concatenated sequence are its last `s` coordinates scaled by the `k`-th powers of `h`. -/
theorem coordRight_mulLeft_pow (v : Fin (r + s) → R) :
    coordRight R r s (LinearMap.mulLeft R (fun j => Fin.append g h j ^ k) v) =
      LinearMap.mulLeft R (fun i => h i ^ k) (coordRight R r s v) := by
  refine funext fun i => ?_
  simp only [coordRight_apply, LinearMap.mulLeft_apply, Pi.mul_apply, Fin.append_right]

/-- Scaling the coordinates of `R^{r+s}` by the `k`-th powers of the concatenated sequence is the
concatenation of the two one-sided scalings. -/
theorem append_mulLeft_pow (v : Fin (r + s) → R) :
    Fin.append (LinearMap.mulLeft R (fun i => g i ^ k) (coordLeft R r s v))
        (LinearMap.mulLeft R (fun i => h i ^ k) (coordRight R r s v)) =
      LinearMap.mulLeft R (fun j => Fin.append g h j ^ k) v := by
  refine funext fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left, LinearMap.mulLeft_apply, Pi.mul_apply, coordLeft_apply]
  · simp only [Fin.append_right, LinearMap.mulLeft_apply, Pi.mul_apply, coordRight_apply]

/-- Scaling by the `k`-th powers of the concatenated sequence preserves the inclusion of `Rʳ` as
the first `r` coordinates of `R^{r+s}`. -/
theorem mulLeft_pow_append_zero (w : Fin r → R) :
    LinearMap.mulLeft R (fun j => Fin.append g h j ^ k) (Fin.append w (0 : Fin s → R)) =
      Fin.append (LinearMap.mulLeft R (fun i => g i ^ k) w) (0 : Fin s → R) := by
  simpa only [← appendInclLeft_apply, coordLeft_appendInclLeft, coordRight_appendInclLeft,
    map_zero] using (append_mulLeft_pow g h k (appendInclLeft R r s w)).symm

/-- Scaling by the `k`-th powers of the concatenated sequence preserves the inclusion of `R^s` as
the last `s` coordinates of `R^{r+s}`. -/
theorem mulLeft_pow_zero_append (w : Fin s → R) :
    LinearMap.mulLeft R (fun j => Fin.append g h j ^ k) (Fin.append (0 : Fin r → R) w) =
      Fin.append (0 : Fin r → R) (LinearMap.mulLeft R (fun i => h i ^ k) w) := by
  simpa only [← appendInclRight_apply, coordLeft_appendInclRight, coordRight_appendInclRight,
    map_zero] using (append_mulLeft_pow g h k (appendInclRight R r s w)).symm

end Scaling

section Transition

/-- The transition homomorphism `K_m → K_n` scales a vector of generators by the `(m - n)`-th
powers of the sequence. -/
theorem powTransition_powVec {q : ℕ} (f : Fin q → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (u : Fin q → R) :
    (powTransition f hn hnm).toAlgebraHom (powVec f m u) =
      powVec f n (LinearMap.mulLeft R (fun i => f i ^ (m - n)) u) := by
  change ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (m - n))
      (ExteriorAlgebra.ι R u) =
    (ExteriorAlgebra.ι R (LinearMap.mulLeft R (fun i => f i ^ (m - n)) u) :
      ExteriorAlgebra R (Fin q → R))
  rw [ExteriorAlgebra.map_apply_ι]

variable (g : Fin r → R) (h : Fin s → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m)

/-- **The transition homomorphisms commute with the inclusion of the first piece**: lowering the
exponent and then including `K_t(g)` into `K_t(g, h)` is including `K_m(g)` into `K_m(g, h)` and
then lowering the exponent. -/
theorem powTransition_comp_appendFromLeft :
    (powTransition (Fin.append g h) ht htm).toAlgebraHom.comp
        (appendFromLeft g h m).toAlgebraHom =
      (appendFromLeft g h t).toAlgebraHom.comp (powTransition g ht htm).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun w => ?_)
  change (powTransition (Fin.append g h) ht htm).toAlgebraHom
      ((appendFromLeft g h m).toAlgebraHom (powVec g m w)) =
    (appendFromLeft g h t).toAlgebraHom ((powTransition g ht htm).toAlgebraHom (powVec g m w))
  rw [appendFromLeft_powVec, powTransition_powVec, powTransition_powVec, appendFromLeft_powVec,
    mulLeft_pow_append_zero]

/-- **The transition homomorphisms commute with the inclusion of the second piece**: lowering the
exponent and then including `K_t(h)` into `K_t(g, h)` is including `K_m(h)` into `K_m(g, h)` and
then lowering the exponent. -/
theorem powTransition_comp_appendFromRight :
    (powTransition (Fin.append g h) ht htm).toAlgebraHom.comp
        (appendFromRight g h m).toAlgebraHom =
      (appendFromRight g h t).toAlgebraHom.comp (powTransition h ht htm).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun w => ?_)
  change (powTransition (Fin.append g h) ht htm).toAlgebraHom
      ((appendFromRight g h m).toAlgebraHom (powVec h m w)) =
    (appendFromRight g h t).toAlgebraHom ((powTransition h ht htm).toAlgebraHom (powVec h m w))
  rw [appendFromRight_powVec, powTransition_powVec, powTransition_powVec,
    appendFromRight_powVec, mulLeft_pow_zero_append]

end Transition

section TensorTransition

variable (g : Fin r → R) (h : Fin s → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m)

/-- **The tensor product `τ_{m,t} ⊗ τ_{m,t}` of the two transition homomorphisms**, as a
homomorphism `K_m(g) ⊗_R K_m(h) → K_t(g) ⊗_R K_t(h)` of differential graded algebras. -/
def powTensorTransition :
    (tensorProduct (powAlgebra g m) (powAlgebra h m)).Hom
      (tensorProduct (powAlgebra g t) (powAlgebra h t)) :=
  (tensorHomLeft (powTransition g ht htm) (powAlgebra h t)).comp
    (tensorHomRight (powAlgebra g m) (powTransition h ht htm))

/-- The underlying algebra homomorphism of `τ_{m,t} ⊗ τ_{m,t}` is the composite of the algebra
homomorphisms applying the transition homomorphism to the second and then to the first factor. -/
@[simp] theorem powTensorTransition_toAlgebraHom :
    (powTensorTransition g h ht htm).toAlgebraHom =
      (tensorHomLeft (powTransition g ht htm) (powAlgebra h t)).toAlgebraHom.comp
        (tensorHomRight (powAlgebra g m) (powTransition h ht htm)).toAlgebraHom := rfl

/-- The homomorphism `τ_{m,t} ⊗ τ_{m,t}` applies the two transition homomorphisms to the two
factors of a pure tensor. -/
@[simp] theorem powTensorTransition_tmul (a : (powAlgebra g m).A) (b : (powAlgebra h m).A) :
    (powTensorTransition g h ht htm).toAlgebraHom
        (a ᵍ⊗ₜ[R] b : (powAlgebra g m).grading ᵍ⊗[R] (powAlgebra h m).grading) =
      ((powTransition g ht htm).toAlgebraHom a ᵍ⊗ₜ[R]
          (powTransition h ht htm).toAlgebraHom b :
        (powAlgebra g t).grading ᵍ⊗[R] (powAlgebra h t).grading) := by
  rw [powTensorTransition_toAlgebraHom, AlgHom.comp_apply, tensorHomRight_tmul,
    tensorHomLeft_tmul]

/-- The homomorphism `τ_{m,t} ⊗ τ_{m,t}` sends the element `ξ(v') ⊗ 1` attached to the first group
of coordinates of `v` to the one attached to the first group of coordinates of the scaled
vector. -/
theorem powTensorTransition_appendTensorLeft (v : Fin (r + s) → R) :
    (powTensorTransition g h ht htm).toAlgebraHom (appendTensorLeft g h m v) =
      appendTensorLeft g h t
        (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v) := by
  have hL : appendTensorLeft g h m v =
      (powVec g m (coordLeft R r s v) ᵍ⊗ₜ[R] (1 : (powAlgebra h m).A) :
        (powAlgebra g m).grading ᵍ⊗[R] (powAlgebra h m).grading) := rfl
  have hR : appendTensorLeft g h t
        (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v) =
      (powVec g t (LinearMap.mulLeft R (fun i => g i ^ (m - t)) (coordLeft R r s v))
          ᵍ⊗ₜ[R] (1 : (powAlgebra h t).A) :
        (powAlgebra g t).grading ᵍ⊗[R] (powAlgebra h t).grading) := by
    rw [appendTensorLeft_def, coordLeft_mulLeft_pow]
    rfl
  rw [hL, hR, powTensorTransition_tmul, map_one, powTransition_powVec]

/-- The homomorphism `τ_{m,t} ⊗ τ_{m,t}` sends the element `1 ⊗ ξ(v'')` attached to the last group
of coordinates of `v` to the one attached to the last group of coordinates of the scaled
vector. -/
theorem powTensorTransition_appendTensorRight (v : Fin (r + s) → R) :
    (powTensorTransition g h ht htm).toAlgebraHom (appendTensorRight g h m v) =
      appendTensorRight g h t
        (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v) := by
  have hL : appendTensorRight g h m v =
      ((1 : (powAlgebra g m).A) ᵍ⊗ₜ[R] powVec h m (coordRight R r s v) :
        (powAlgebra g m).grading ᵍ⊗[R] (powAlgebra h m).grading) := rfl
  have hR : appendTensorRight g h t
        (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v) =
      ((1 : (powAlgebra g t).A) ᵍ⊗ₜ[R]
          powVec h t (LinearMap.mulLeft R (fun i => h i ^ (m - t)) (coordRight R r s v)) :
        (powAlgebra g t).grading ᵍ⊗[R] (powAlgebra h t).grading) := by
    rw [appendTensorRight_def, coordRight_mulLeft_pow]
    rfl
  rw [hL, hR, powTensorTransition_tmul, map_one, powTransition_powVec]

/-- **The append isomorphism of Tag 0664 commutes with the transition homomorphisms.** The
composite of the isomorphism `K_m(g, h) ≅ K_m(g) ⊗_R K_m(h)`, the tensor product
`τ_{m,t} ⊗ τ_{m,t}` of the transition homomorphisms of the two pieces, and the isomorphism
`K_t(g) ⊗_R K_t(h) ≅ K_t(g, h)` is the transition homomorphism `τ_{m,t}` of the concatenated
sequence. -/
theorem powAppendFromTensor_powTensorTransition :
    (powAppendFromTensor g h t).toAlgebraHom.comp
        ((powTensorTransition g h ht htm).toAlgebraHom.comp
          (powAppendToTensor g h m).toAlgebraHom) =
      (powTransition (Fin.append g h) ht htm).toAlgebraHom := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
  change (powAppendFromTensor g h t).toAlgebraHom
      ((powTensorTransition g h ht htm).toAlgebraHom
        ((powAppendToTensor g h m).toAlgebraHom (powVec (Fin.append g h) m v))) =
    (powTransition (Fin.append g h) ht htm).toAlgebraHom (powVec (Fin.append g h) m v)
  have hsum : powVec (Fin.append g h) t
          (Fin.append (coordLeft R r s
            (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v)) (0 : Fin s → R)) +
        powVec (Fin.append g h) t
          (Fin.append (0 : Fin r → R) (coordRight R r s
            (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v))) =
      powVec (Fin.append g h) t
        (LinearMap.mulLeft R (fun j => Fin.append g h j ^ (m - t)) v) := by
    rw [← map_add, append_zero_add_zero_append, append_coordLeft_coordRight]
  rw [powAppendToTensor_powVec, map_add, map_add, powTensorTransition_appendTensorLeft,
    powTensorTransition_appendTensorRight, powAppendFromTensor_appendTensorLeft,
    powAppendFromTensor_appendTensorRight, hsum, powTransition_powVec]

/-- **The append isomorphism of Tag 0664 commutes with the transition homomorphisms**, elementwise.
-/
theorem powAppendFromTensor_powTensorTransition_apply (x : (powAlgebra (Fin.append g h) m).A) :
    (powAppendFromTensor g h t).toAlgebraHom
        ((powTensorTransition g h ht htm).toAlgebraHom
          ((powAppendToTensor g h m).toAlgebraHom x)) =
      (powTransition (Fin.append g h) ht htm).toAlgebraHom x := by
  have h0 := powAppendFromTensor_powTensorTransition g h ht htm
  exact congrArg (fun φ => φ x) h0

end TensorTransition

end Koszul
