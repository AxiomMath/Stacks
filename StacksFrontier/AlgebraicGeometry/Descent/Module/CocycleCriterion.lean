module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData

/-!
# The cocycle condition is coassociativity of the unit of the transition

Let `R → A` be a ring map, let `N` be an `A`-module and let
`e : N ⊗[R] A ≃ A ⊗[R] N` be an `A ⊗[R] A`-linear isomorphism between the two pullbacks of `N`,
i.e. the transition isomorphism of a candidate descent datum, Stacks 023G. The cocycle condition
`φ₁₂ ∘ φ₀₁ = φ₀₂` of `ModuleCat.DescentData` is an equation of `R`-linear maps on the triple
tensor product. This file shows that it follows from a single equation involving only
`σ : N → A ⊗[R] N`, `σ n = e (n ⊗ 1)`, namely

`(id_A ⊗ σ) (σ n) = (id_A ⊗ (1 ⊗ ·)) (σ n)`   in `A ⊗[R] (A ⊗[R] N)`.

Geometrically `σ` is the action of the groupoid `Spec A ×_{Spec R} Spec A` on the scheme or module
being descended, and the displayed equation is associativity of that action; in the proof of
Stacks 023N it is the identity `Σ aᵢ ⊗ a_{ij} ⊗ y_j = Σ aᵢ ⊗ 1 ⊗ xᵢ` which the source deduces from
the cocycle condition.

The point of the reduction is that the displayed equation mentions only *one* tensor power of `A`
beyond the transition itself, so for a transition coming from geometry it can be verified against a
single morphism out of a triple fibre product, rather than by identifying all three triple tensor
products with their geometric counterparts.

## Main definitions

* `ModuleCat.targetSmulMap` is multiplication by a fixed element of `A ⊗[R] A` on `A ⊗[R] N`,
  packaged as an `R`-linear map so that it can be tensored.
* `ModuleCat.unitTransition` is `σ : n ↦ e (n ⊗ 1)`.

## Main results

* `ModuleCat.transition_apply_tmul`: the transition is determined by its unit,
  `e (n ⊗ a) = (1 ⊗ a) • σ n`.
* `ModuleCat.cocycle_of_unitTransition`: **the cocycle criterion.** If `σ` is coassociative in the
  sense displayed above, then `e` satisfies the cocycle condition of
  `ModuleCat.DescentData`.

## References

* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory TensorProduct

namespace ModuleCat

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (N : ModuleCat.{w} A)

/-- Multiplication by a fixed element of `A ⊗[R] A` on `A ⊗[R] N`, as an `R`-linear map.

It is `R`-linear because the `R`-module structure of `A ⊗[R] N` is the restriction of its
`A ⊗[R] A`-module structure, `ModuleCat.targetTensor_isScalarTower`, and `A ⊗[R] A` is
commutative. -/
def targetSmulMap (s : A ⊗[R] A) :
    (A ⊗[R] restrictModule R A N) →ₗ[R] (A ⊗[R] restrictModule R A N) where
  toFun z := s • z
  map_add' _ _ := smul_add s _ _
  map_smul' r z := by
    rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul (A ⊗[R] A) r z,
      ← IsScalarTower.algebraMap_smul (A ⊗[R] A) r (s • z), smul_smul, smul_smul, mul_comm]

/-- `ModuleCat.targetSmulMap` is multiplication by `s`. -/
@[simp]
lemma targetSmulMap_apply (s : A ⊗[R] A) (z : A ⊗[R] restrictModule R A N) :
    targetSmulMap R A N s z = s • z := rfl

variable (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N))

/-- **The unit of a transition isomorphism**, `σ : n ↦ e (n ⊗ 1)`, as an `R`-linear map
`N → A ⊗[R] N`. The invariants of the datum are the `n` with `σ n = 1 ⊗ n`. -/
def unitTransition : (restrictModule R A N) →ₗ[R] (A ⊗[R] restrictModule R A N) :=
  (e.restrictScalars R).toLinearMap ∘ₗ ((TensorProduct.mk R (restrictModule R A N) A).flip 1)

/-- `ModuleCat.unitTransition` sends `n` to `e (n ⊗ 1)`. -/
@[simp]
lemma unitTransition_apply (n : restrictModule R A N) :
    unitTransition R A N e n = e (n ⊗ₜ[R] (1 : A)) := rfl

/-- The transition applied to `(a • n) ⊗ b` is `(a ⊗ b) • σ n`. -/
private lemma transition_apply_restrictedScalarAction_tmul (a b : A) (n : restrictModule R A N) :
    e (restrictedScalarAction R A N a n ⊗ₜ[R] b) = (a ⊗ₜ[R] b) • unitTransition R A N e n := by
  rw [unitTransition_apply, ← e.map_smul, sourceTensor_smul_tmul, mul_one]

/-- A transition isomorphism is determined by its unit: `e (n ⊗ a) = (1 ⊗ a) • σ n`. -/
lemma transition_apply_tmul (n : restrictModule R A N) (a : A) :
    e (n ⊗ₜ[R] a) = ((1 : A) ⊗ₜ[R] a) • unitTransition R A N e n := by
  rw [← transition_apply_restrictedScalarAction_tmul]
  congr 3
  exact (LinearMap.congr_fun (restrictedScalarAction R A N).map_one n).symm

/-- The unit of a transition isomorphism is semilinear for the `A`-action on `N`. -/
lemma unitTransition_restrictedScalarAction (a : A) (n : restrictModule R A N) :
    unitTransition R A N e (restrictedScalarAction R A N a n)
      = (a ⊗ₜ[R] (1 : A)) • unitTransition R A N e n :=
  transition_apply_restrictedScalarAction_tmul R A N e a 1 n

/-- The left-hand side of the cocycle condition, rewritten through the unit: the composite
`φ₁₂ ∘ φ₀₁` applied to `((1 ⊗ a₁) • y) ⊗ a₂` is `y` tensored with
`z ↦ (a₁ ⊗ a₂) • σ z`. -/
lemma lTensor_assoc_smul_tmul (a₁ a₂ : A) (y : A ⊗[R] restrictModule R A N) :
    LinearMap.lTensor A (e.restrictScalars R).toLinearMap
        ((TensorProduct.assoc R A (restrictModule R A N) A)
          ((((1 : A) ⊗ₜ[R] a₁) • y) ⊗ₜ[R] a₂))
      = LinearMap.lTensor A
          (targetSmulMap R A N (a₁ ⊗ₜ[R] a₂) ∘ₗ unitTransition R A N e) y := by
  induction y with
  | add u v hu hv =>
    rw [smul_add, TensorProduct.add_tmul, map_add, map_add, hu, hv, map_add]
  | tmul x n =>
    rw [targetTensor_smul_tmul, one_mul, TensorProduct.assoc_tmul,
      LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    congr 1
    exact transition_apply_restrictedScalarAction_tmul R A N e a₁ a₂ n

/-- The right-hand side of the cocycle condition, rewritten through the unit. -/
lemma assoc_symm_lTensor_mk (a₁ a₂ : A) (z : A ⊗[R] restrictModule R A N) :
    (TensorProduct.assoc R A A (restrictModule R A N)).symm
        (LinearMap.lTensor A (targetSmulMap R A N (a₁ ⊗ₜ[R] a₂)
          ∘ₗ TensorProduct.mk R A (restrictModule R A N) 1) z)
      = (TensorProduct.rightComm R A (restrictModule R A N) A)
          ((((1 : A) ⊗ₜ[R] a₂) • z) ⊗ₜ[R] a₁) := by
  induction z with
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, smul_add, TensorProduct.add_tmul, map_add]
  | tmul x n =>
    rw [LinearMap.lTensor_tmul, targetTensor_smul_tmul, one_mul, TensorProduct.rightComm_tmul]
    show (TensorProduct.assoc R A A (restrictModule R A N)).symm
      (x ⊗ₜ[R] ((a₁ ⊗ₜ[R] a₂) • ((1 : A) ⊗ₜ[R] n))) = _
    rw [targetTensor_smul_tmul, mul_one, TensorProduct.assoc_symm_tmul]

/-- **The cocycle criterion.** A transition isomorphism whose unit `σ` is coassociative, in the
sense that `(id_A ⊗ σ) (σ n) = (id_A ⊗ (1 ⊗ ·)) (σ n)` for every `n`, satisfies the cocycle
condition of `ModuleCat.DescentData`.

The cocycle condition is an equation of `R`-linear maps
`(N ⊗[R] A) ⊗[R] A → (A ⊗[R] A) ⊗[R] N`; both sides are computed on a generator
`(n ⊗ a₁) ⊗ a₂` by `ModuleCat.lTensor_assoc_smul_tmul` and
`ModuleCat.assoc_symm_lTensor_mk`, after which the hypothesis is exactly what is left. -/
theorem cocycle_of_unitTransition
    (hkey : ∀ n : restrictModule R A N,
      LinearMap.lTensor A (unitTransition R A N e) (unitTransition R A N e n)
        = LinearMap.lTensor A (TensorProduct.mk R A (restrictModule R A N) 1)
            (unitTransition R A N e n)) :
    (transition12 R A N e).comp (transition01 R A N e) = transition02 R A N e := by
  apply TensorProduct.ext'
  intro x a₂
  induction x with
  | add u v hu hv => rw [TensorProduct.add_tmul, map_add, map_add, hu, hv]
  | tmul n a₁ =>
    show (TensorProduct.assoc R A A (restrictModule R A N)).symm
        (LinearMap.lTensor A (e.restrictScalars R).toLinearMap
          ((TensorProduct.assoc R A (restrictModule R A N) A)
            (e (n ⊗ₜ[R] a₁) ⊗ₜ[R] a₂)))
      = (TensorProduct.rightComm R A (restrictModule R A N) A) (e (n ⊗ₜ[R] a₂) ⊗ₜ[R] a₁)
    rw [transition_apply_tmul R A N e n a₁, transition_apply_tmul R A N e n a₂,
      lTensor_assoc_smul_tmul, LinearMap.lTensor_comp, LinearMap.comp_apply, hkey,
      ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, assoc_symm_lTensor_mk]

end ModuleCat

end

end
