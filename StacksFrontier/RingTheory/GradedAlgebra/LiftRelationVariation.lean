module

public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobian
public import StacksFrontier.RingTheory.GradedAlgebra.LiftPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# How the lifted relations change when the lifted generators change

Let `k` be a commutative ring, `P` a `k`-algebra with a presentation `k[X_1, …, X_n] → P`,
`X_i ↦ x i`, with relations `F j`, and let `Q` be an algebra over a `k`-algebra `A` with a
square-zero ideal `I` and an augmentation `ε : A →ₐ[k] k` with `ker ε ⊆ I`, together with a
reduction `π : Q → P` exhibiting `P` as `Q/IQ`.

A choice of lifts `q i ∈ Q` of the `x i` determines, for each relation `F j`, the obstruction
`aeval q (F_j^{can})` to the canonical coefficientwise lift `F_j^{can}` of `F j` being a
relation of `Q`. That obstruction lies in `I • Q`, and so — by
`Ideal.exists_addMonoidHom_tmul_smul` — is recorded by an element `g j` of `I ⊗[k] P`. This
file computes how `g j` changes when the lifts `q i` are changed, which is the computation
Stacks 0DVZ (`examples-defos.tex:683`) omits:

> *"Moreover, if we change our choice of `q_i` into `q_i + ε p_i` with `p_i` of degree `d_i`
> then a computation (omitted) shows that `g_j` changes into
> `g_j^{new} = g_j - ∑_i p_i ∂F_j/∂X_i`."*

The answer is `GradedAlgebra.sub_eq_sum_lTensor_mulRight_of_lift_relation`, and the
`∂F_j/∂X_i` which appears there is exactly the entry of
`GradedAlgebra.gradedJacobian`: by `GradedAlgebra.gradedJacobianTerm_apply_coe` the `(i, j)`
term of the graded Jacobian is the restriction of `LinearMap.mulRight k (aeval x (pderiv i
(F j)))` to the graded pieces. So the formula says that the vector `(g j)` is well defined
modulo the image of the Jacobian, which is the vector space `W` of the source.

Nothing here is tagged: this is step (vii) of 0DVZ's *proof*, and Stacks does not tag the steps
of a proof.

## Main results

* `MvPolynomial.aeval_add_of_mul_eq_zero_fin`: **first-order Taylor expansion.** If the shifts
  `z i` have pairwise vanishing products then
  `aeval (q + z) G = aeval q G + ∑ i, z i * aeval q (∂G/∂X_i)`. The `_fin` suffix records that
  the variables are indexed by `Fin n` and the two points are implicit;
  `MvPolynomial.aeval_add_of_mul_eq_zero` in
  `StacksFrontier/RingTheory/GradedAlgebra/WeightedHomogeneousPresentation.lean` is the same
  expansion over an arbitrary `Fintype` index with the points explicit.
* `Submodule.mul_mem_smul_top`: `I • ⊤` is an ideal of an algebra over the base.
* `Submodule.mul_eq_zero_of_mem_smul_top_of_mul_eq_bot`: two elements of `I • ⊤` have vanishing
  product when `I` is square zero.
* `GradedAlgebra.map_lTensor_mulRight`: the comparison map `I ⊗[k] P → Q` intertwines
  multiplication by an element of `P` with multiplication by any of its lifts.
* `GradedAlgebra.sub_eq_sum_lTensor_mulRight_of_lift_relation`: the change-of-generators
  formula.

## Implementation notes

The Taylor expansion is stated with the hypothesis `∀ i l, z i * z l = 0` rather than with an
ideal of `Q`, because that is exactly what the induction uses and because the shifts arrive as
elements of the `A`-submodule `I • ⊤` of `Q`, not of an ideal of `Q`;
`Submodule.mul_eq_zero_of_mem_smul_top_of_mul_eq_bot` is the bridge.

The comparison map `θ` is taken as a parameter together with its characterising property
`θ (b ⊗ₜ π y) = b • y`, rather than constructed here. It is unique with that property because
`π` is surjective, and `Ideal.exists_addMonoidHom_tmul_smul` provides one; carrying it as a
parameter avoids having to make a choice of section canonical.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace MvPolynomial

variable {A Q : Type*} [CommRing A] [CommRing Q] [Algebra A Q]

/-- **First-order Taylor expansion of a multivariate polynomial.** If the shifts `z i` have
pairwise vanishing products — as they do when they lie in a square-zero ideal — then the value
of `G` at `q + z` is its value at `q` plus the first-order term
`∑ i, z i * (∂G/∂X_i)(q)`.

This is the computation the proof of Stacks 0DVZ calls *"a computation (omitted)"*. -/
theorem aeval_add_of_mul_eq_zero_fin {n : ℕ} {q z : Fin n → Q}
    (hzz : ∀ i l : Fin n, z i * z l = 0) (G : MvPolynomial (Fin n) A) :
    aeval (fun i => q i + z i) G =
      aeval q G + ∑ i : Fin n, z i * aeval q (pderiv i G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' =>
      rw [map_add, map_add, hp, hp']
      simp only [map_add, mul_add, Finset.sum_add_distrib]
      ring
  | mul_X p i hp =>
      have hterm : ∀ l : Fin n, z l * aeval q (pderiv l (p * MvPolynomial.X i)) =
          z l * aeval q (pderiv l p) * q i + (if l = i then z i * aeval q p else 0) := by
        intro l
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, aeval_X, mul_add, mul_assoc]
        rcases eq_or_ne l i with rfl | hne
        · simp
        · simp [MvPolynomial.pderiv_X_of_ne hne.symm, hne]
      have hcross : (∑ l : Fin n, z l * aeval q (pderiv l p)) * z i = 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [mul_comm (z l), mul_assoc, hzz l i, mul_zero]
      have hsum : ∑ l : Fin n, z l * aeval q (pderiv l (p * MvPolynomial.X i)) =
          (∑ l : Fin n, z l * aeval q (pderiv l p)) * q i + z i * aeval q p := by
        rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, Finset.sum_mul]
        simp
      rw [map_mul, hp, map_mul, aeval_X, aeval_X, hsum, add_mul, mul_add, mul_add, hcross,
        add_zero]
      ring

end MvPolynomial

namespace Submodule

variable {A Q : Type*} [CommRing A] [CommRing Q] [Algebra A Q]

/-- `I • ⊤` is an ideal of `Q`, not merely a submodule over the base: the scalars commute with
multiplication in `Q`. -/
@[ega "0 1.0.4" "special case"]
theorem mul_mem_smul_top {I : Ideal A} (y : Q) {w : Q}
    (hw : w ∈ I • (⊤ : Submodule A Q)) : y * w ∈ I • (⊤ : Submodule A Q) := by
  refine Submodule.smul_induction_on hw (fun a ha u _ => ?_) (fun u v hu hv => ?_)
  · rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [mul_add]
    exact Submodule.add_mem _ hu hv

/-- Two elements of `I • ⊤` have vanishing product when `I` is square zero. -/
theorem mul_eq_zero_of_mem_smul_top_of_mul_eq_bot {I : Ideal A} (hI : I * I = ⊥) {u v : Q}
    (hu : u ∈ I • (⊤ : Submodule A Q)) (hv : v ∈ I • (⊤ : Submodule A Q)) : u * v = 0 := by
  refine Submodule.smul_induction_on hu (fun a ha w _ => ?_) (fun w w' hw hw' => ?_)
  · rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_eq_zero_of_mem_smul_top_of_mul_eq_bot hI ha
      (Submodule.mul_mem_smul_top w hv)
  · rw [add_mul, hw, hw', add_zero]

end Submodule

namespace GradedAlgebra

open MvPolynomial

universe u v w t

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]
  (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A)

/-- The comparison map `θ : I ⊗[k] P → Q` of `Ideal.exists_addMonoidHom_tmul_smul` intertwines
multiplication by `c ∈ P` on the second factor with multiplication by any lift `y` of `c`. -/
theorem map_lTensor_mulRight (θ : (↥I) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hπsurj : Function.Surjective π) (y : Q) (ξ : (↥I) ⊗[k] P) :
    θ (LinearMap.lTensor (↥I) (LinearMap.mulRight k (π y)) ξ) = θ ξ * y := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
      obtain ⟨w, rfl⟩ := hπsurj m
      rw [LinearMap.lTensor_tmul]
      rw [show (LinearMap.mulRight k (π y)) (π w) = π (w * y) from by rw [map_mul]; rfl]
      rw [hθ, hθ, Algebra.smul_mul_assoc]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv, add_mul]

/-- **The change-of-generators formula for the recorded relation vector.** Let `q` and `q'` be
two families of lifts of the generators `x i` which differ by elements of `I • Q`, let
`p i ∈ I ⊗[k] P` record the differences `q' i - q i`, and let `g j`, `g' j ∈ I ⊗[k] P` record
the corrections `- aeval q (F_j^{can})`, `- aeval q' (F_j^{can})` to the canonical lifts of the
relations. Then

`g' j - g j = - ∑ i, (id ⊗ (· * (∂F_j/∂X_i)(x))) (p i)`,

which is the formula `g_j^{new} = g_j - ∑_i p_i ∂F_j/∂X_i` of the proof of Stacks 0DVZ.

In particular the class of the vector `(g j)` modulo the image of the Jacobian — whose `(i, j)`
entry is, by `gradedJacobianTerm_apply_coe`, precisely
`LinearMap.mulRight k (aeval x (pderiv i (F j)))` — does not depend on the chosen lifts of the
generators. Together with the injectivity half of
`Ideal.exists_addMonoidHom_tmul_smul`, which makes `g j` independent of the chosen lift of the
relation, this is the whole of step (vii) of the source. -/
theorem sub_eq_sum_lTensor_mulRight_of_lift_relation (θ : (↥I) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθinj : Function.Injective θ) (hIsq : I * I = ⊥)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y) (hπsurj : Function.Surjective π)
    {n r : ℕ} {x : Fin n → P} {F : Fin r → MvPolynomial (Fin n) k}
    {q q' : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    (hqq : ∀ i, q' i - q i ∈ I • (⊤ : Submodule A Q))
    {g g' : Fin r → (↥I) ⊗[k] P} {p : Fin n → (↥I) ⊗[k] P}
    (hg : ∀ j, θ (g j) = -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hg' : ∀ j, θ (g' j) = -aeval q' (MvPolynomial.map (algebraMap k A) (F j)))
    (hp : ∀ i, θ (p i) = q' i - q i) (j : Fin r) :
    g' j - g j = - ∑ i : Fin n,
      LinearMap.lTensor (↥I) (LinearMap.mulRight k (aeval x (pderiv i (F j)))) (p i) := by
  have hconst := map_algebraMap_of_smul ε π hπsmul
  set z : Fin n → Q := fun i => q' i - q i with hzdef
  have hzz : ∀ i l : Fin n, z i * z l = 0 := fun i l =>
    Submodule.mul_eq_zero_of_mem_smul_top_of_mul_eq_bot hIsq (hqq i) (hqq l)
  have hq' : ∀ i, q' i = q i + z i := fun i => by rw [hzdef]; ring
  -- the derivative of the canonical lift is the canonical lift of the derivative
  have hyπ : ∀ i : Fin n,
      π (aeval q (MvPolynomial.map (algebraMap k A) (pderiv i (F j)))) =
        aeval x (pderiv i (F j)) := by
    intro i
    rw [MvPolynomial.hom_aeval_eq_aeval_map ε π hconst hq, MvPolynomial.map_map_algebraMap]
  refine hθinj ?_
  rw [map_sub, map_neg, map_sum, hg, hg']
  rw [show ∑ i : Fin n, θ (LinearMap.lTensor (↥I)
      (LinearMap.mulRight k (aeval x (pderiv i (F j)))) (p i)) =
      ∑ i : Fin n, z i * aeval q (MvPolynomial.map (algebraMap k A) (pderiv i (F j))) from
    Finset.sum_congr rfl fun i _ => by
      rw [← hyπ i, map_lTensor_mulRight π I θ hθ hπsurj, hp i]]
  simp only [← MvPolynomial.pderiv_map]
  rw [funext hq', MvPolynomial.aeval_add_of_mul_eq_zero_fin hzz]
  ring

end GradedAlgebra

end
