module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CocycleCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FaithfullyFlatAlgebraDescent

/-!
# The cocycle condition for an algebra descent datum

`ModuleCat.bijective_productMap_descentInvariants` — effective descent for algebras along a
faithfully flat ring map, the algebra step in the proof of Stacks 0245 — takes a transition
isomorphism of `A ⊗[R] A`-algebras `τ : B ⊗[R] A ≃ A ⊗[R] B` together with the cocycle condition
in the form the `cocycle` field of `ModuleCat.DescentData` asks for: an equality of `R`-linear maps
between triple tensor products of the *module* `ModuleCat.restrictModule R A (ModuleCat.of A B)`.

That form is awkward for a transition which comes from geometry, because a geometric descent datum
produces an isomorphism of schemes over `Spec (A ⊗[R] A)` and verifying the triple-tensor equation
means identifying all three triple tensor products with triple fibre products. This file replaces
it by a single equation in `A ⊗[R] (A ⊗[R] B)` about

`σ : B → A ⊗[R] B`,  `σ b = τ (b ⊗ 1)`,

namely coassociativity `(id_A ⊗ σ) (σ b) = (id_A ⊗ (1 ⊗ ·)) (σ b)`. The underlying reduction, for
an arbitrary module transition, is `ModuleCat.cocycle_of_unitTransition`; what is added here is the
comparison between the module `ModuleCat.restrictModule R A (ModuleCat.of A B)` and the algebra
`B`, which is `ModuleCat.algebraTargetEquiv` and is the identity on elements.

## Main definitions

* `ModuleCat.algebraUnitTransition` is `σ : b ↦ τ (b ⊗ 1)`, as an `R`-linear map `B → A ⊗[R] B`.
  Its invariants are `ModuleCat.descentInvariants`.

## Main results

* `ModuleCat.cocycle_algebraTransition_of_unitCoassoc`: coassociativity of `σ` implies the cocycle
  condition for `ModuleCat.algebraTransition`.
* `ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc`: **effective descent for
  algebras, with the cocycle condition replaced by coassociativity of `σ`.** For `R → A`
  faithfully flat, the canonical map `A ⊗[R] C → B` out of the invariants is bijective.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TensorProduct

namespace ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- **The unit of an algebra transition isomorphism**, `σ : b ↦ τ (b ⊗ 1)`. The invariant
subalgebra `ModuleCat.descentInvariants` is the set of `b` with `σ b = 1 ⊗ b`. -/
def algebraUnitTransition (τ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B)) : B →ₗ[R] (A ⊗[R] B) :=
  τ.toLinearMap ∘ₗ ((TensorProduct.mk R B A).flip 1)

omit [Algebra A B] [IsScalarTower R A B] in
/-- `ModuleCat.algebraUnitTransition` sends `b` to `τ (b ⊗ 1)`. -/
@[simp]
lemma algebraUnitTransition_apply (τ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B)) (b : B) :
    algebraUnitTransition R A B τ b = τ (b ⊗ₜ[R] (1 : A)) := rfl

variable (τ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
    (hτ : ∀ a b : A, τ (algebraMap A B a ⊗ₜ[R] b) = a ⊗ₜ[R] algebraMap A B b)

/-- The unit of the module transition of an algebra descent datum is the unit of the algebra
transition, read through `ModuleCat.algebraTargetEquiv`. -/
lemma unitTransition_algebraTransition (n : restrictModule R A (ModuleCat.of A B)) :
    unitTransition R A (ModuleCat.of A B) (algebraTransition R A B τ hτ) n
      = (algebraTargetEquiv R A B).symm (algebraUnitTransition R A B τ (show B from n)) := rfl

/-- Tensoring the unit of the module transition on the right of `A` agrees with tensoring the
unit of the algebra transition, up to `ModuleCat.algebraTargetEquiv`. -/
lemma lTensor_unitTransition_symm (u : A ⊗[R] B) :
    LinearMap.lTensor A (unitTransition R A (ModuleCat.of A B) (algebraTransition R A B τ hτ))
        ((algebraTargetEquiv R A B).symm u)
      = (TensorProduct.congr (LinearEquiv.refl R A) (algebraTargetEquiv R A B).symm)
          (LinearMap.lTensor A (algebraUnitTransition R A B τ) u) := by
  induction u with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x b =>
    rw [algebraTargetEquiv_symm_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, unitTransition_algebraTransition]

omit hτ in
/-- The same comparison for the trivial coaction `b ↦ 1 ⊗ b`. -/
lemma lTensor_mk_symm (u : A ⊗[R] B) :
    LinearMap.lTensor A
        (TensorProduct.mk R A (restrictModule R A (ModuleCat.of A B)) 1)
        ((algebraTargetEquiv R A B).symm u)
      = (TensorProduct.congr (LinearEquiv.refl R A) (algebraTargetEquiv R A B).symm)
          (LinearMap.lTensor A (TensorProduct.mk R A B 1) u) := by
  induction u with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x b =>
    rw [algebraTargetEquiv_symm_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    congr 1

/-- **The cocycle condition for an algebra descent datum, from coassociativity of its unit.** If
`σ b = τ (b ⊗ 1)` satisfies `(id_A ⊗ σ) (σ b) = (id_A ⊗ (1 ⊗ ·)) (σ b)` for every `b`, then
`ModuleCat.algebraTransition` satisfies the cocycle condition of `ModuleCat.DescentData`. -/
theorem cocycle_algebraTransition_of_unitCoassoc
    (hkey : ∀ b : B, LinearMap.lTensor A (algebraUnitTransition R A B τ)
        (algebraUnitTransition R A B τ b)
      = LinearMap.lTensor A (TensorProduct.mk R A B 1) (algebraUnitTransition R A B τ b)) :
    (transition12 R A (ModuleCat.of A B) (algebraTransition R A B τ hτ)).comp
        (transition01 R A (ModuleCat.of A B) (algebraTransition R A B τ hτ))
      = transition02 R A (ModuleCat.of A B) (algebraTransition R A B τ hτ) := by
  refine cocycle_of_unitTransition R A _ _ (fun n => ?_)
  rw [unitTransition_algebraTransition R A B τ hτ n, lTensor_unitTransition_symm,
    lTensor_mk_symm, hkey]

include hτ in
/-- **Effective descent for algebras along a faithfully flat ring map, with the cocycle condition
replaced by coassociativity of the unit.** This is
`ModuleCat.bijective_productMap_descentInvariants` in the form in which a geometric descent datum
can supply its hypotheses: `hτ` says that `τ` lies over `A ⊗[R] A`, and `hkey` says that the
coaction `σ b = τ (b ⊗ 1)` is associative.

Together with `ModuleCat.transition_smul_descentInvariants`, which needs neither hypothesis, this
is effectivity of the algebra descent datum: the descended `R`-algebra is
`ModuleCat.descentInvariants R A B τ`. -/
theorem bijective_productMap_descentInvariants_of_unitCoassoc [Module.FaithfullyFlat R A]
    (hkey : ∀ b : B, LinearMap.lTensor A (algebraUnitTransition R A B τ)
        (algebraUnitTransition R A B τ b)
      = LinearMap.lTensor A (TensorProduct.mk R A B 1) (algebraUnitTransition R A B τ b)) :
    Function.Bijective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom R A B) (descentInvariants R A B τ).val) :=
  bijective_productMap_descentInvariants R A B τ hτ
    (cocycle_algebraTransition_of_unitCoassoc R A B τ hτ hkey)

end ModuleCat

end

end
