module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensoring with a bimodule

Let `A ⟶ B` be a map of commutative rings and let `N` be a `B`-module which is also an
`A`-module, the two actions forming a tower. Then `M ↦ N ⊗[A] M` is a functor

`ModuleCat A ⥤ ModuleCat B`,

the `B`-module structure of the value coming from the one on the left factor. This file builds
that functor and shows that it is additive, and that it is exact — hence preserves homology,
finite limits and finite products — as soon as `N` is flat over `A`.

For `N = B` the functor is `ModuleCat.extendScalars`; the point of the extra generality is that
flatness is then a hypothesis on the module `N` and not on the ring map `A ⟶ B`.

## Main definitions

* `Stacks.TensorBimodule.tensorHom`: the `B`-linear map `N ⊗[A] M ⟶ N ⊗[A] M'` induced by an
  `A`-linear map `M ⟶ M'`.
* `Stacks.TensorBimodule.functor`: **the functor** `M ↦ N ⊗[A] M`.

## Main results

* `Stacks.TensorBimodule.functor_map_tmul`: the normalisation of the functor on morphisms, on a
  pure tensor.
* `Stacks.TensorBimodule.functor_additive`: the functor is additive.
* `Stacks.TensorBimodule.hom_ext`: two morphisms out of a value of the functor agreeing on pure
  tensors are equal.
* `Stacks.TensorBimodule.exact_map_of_flat`: **for `N` flat over `A` the functor preserves
  exactness of short complexes.**
* `Stacks.TensorBimodule.preservesHomology_of_flat`,
  `Stacks.TensorBimodule.preservesFiniteLimits_of_flat`,
  `Stacks.TensorBimodule.preservesFiniteColimits_of_flat`: hence it preserves homology, finite
  limits and finite colimits.
* `Stacks.TensorBimodule.preservesLimitsOfShape_discrete_of_flat`: hence it preserves products
  indexed by a finite type in an arbitrary universe.

## Implementation notes

The morphism part is `TensorProduct.AlgebraTensorModule.map` with the identity in the first
variable, which is `B`-linear precisely because the first factor is the `B`-module; the
underlying function is `LinearMap.lTensor`, and `tensorHom_apply_eq_lTensor` records that.
Exactness is therefore `Module.Flat.lTensor_exact` read through
`CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`, and everything else
is `CategoryTheory.Functor.exact_tfae`.

The elementwise statements are about `tensorHom` rather than about `(functor A B N).map`, and
this is not cosmetic: the carrier of `(functor A B N).obj M` is `N ⊗[A] M` only up to unfolding
`functor`, so an induction over the tensor product performed on a goal written in the second
spelling produces subgoals that are not type-correct at `implicit` transparency.

Preservation of products indexed by a finite type `J` in a universe other than `Type 0` does not
follow from `CategoryTheory.Limits.PreservesFiniteLimits` by definitional unfolding: that
hypothesis quantifies over small categories. It is obtained by transporting along the
equivalence `Discrete J ≌ Discrete (Fin n)` given by a choice of enumeration of `J`.

## References

* [Stacks Project, Tag 00HD](https://stacks.math.columbia.edu/tag/00HD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.TensorBimodule

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- **Tensoring a morphism with an `A`-`B`-bimodule `N`.** An `A`-linear map `M ⟶ M'` induces a
`B`-linear map `N ⊗[A] M ⟶ N ⊗[A] M'`, the `B`-action coming from the left factor. -/
def tensorHom {M M' : ModuleCat.{u} A} (φ : M ⟶ M') :
    (N ⊗[A] (M : Type u)) →ₗ[B] (N ⊗[A] (M' : Type u)) :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := B) (M := N)) φ.hom

/-- `tensorHom` sends a pure tensor `n ⊗ₜ m` to `n ⊗ₜ φ m`. -/
@[simp]
lemma tensorHom_tmul {M M' : ModuleCat.{u} A} (φ : M ⟶ M') (n : N) (m : M) :
    tensorHom A B N φ (n ⊗ₜ[A] m) = n ⊗ₜ[A] φ m :=
  rfl

/-- Tensoring the identity with `N` is the identity. -/
lemma tensorHom_id (M : ModuleCat.{u} A) :
    tensorHom A B N (𝟙 M) = LinearMap.id :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

/-- Tensoring a composite with `N` is the composite of the tensored maps. -/
lemma tensorHom_comp {M M' M'' : ModuleCat.{u} A} (φ : M ⟶ M') (ψ : M' ⟶ M'') :
    tensorHom A B N (φ ≫ ψ) = (tensorHom A B N ψ).comp (tensorHom A B N φ) :=
  TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl

/-- **Tensoring with `N` is additive in the morphism.** -/
lemma tensorHom_add {M M' : ModuleCat.{u} A} (φ ψ : M ⟶ M') :
    tensorHom A B N (φ + ψ) = tensorHom A B N φ + tensorHom A B N ψ := by
  refine TensorProduct.AlgebraTensorModule.ext fun n m => ?_
  exact TensorProduct.tmul_add n (φ.hom m) (ψ.hom m)

/-- The underlying function of `tensorHom` is `LinearMap.lTensor`. -/
lemma tensorHom_apply_eq_lTensor {M M' : ModuleCat.{u} A} (φ : M ⟶ M')
    (z : N ⊗[A] (M : Type u)) :
    tensorHom A B N φ z = LinearMap.lTensor N φ.hom z := by
  exact LinearMap.congr_fun (f := (tensorHom A B N φ).restrictScalars A)
    (g := LinearMap.lTensor N φ.hom) (TensorProduct.ext' fun _ _ => rfl) z

/-- **Tensoring with an `A`-`B`-bimodule `N`**, as a functor `ModuleCat A ⥤ ModuleCat B`: it
sends an `A`-module `M` to `N ⊗[A] M`, a `B`-module through the `B`-action on `N`. -/
def functor : ModuleCat.{u} A ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (N ⊗[A] M)
  map φ := ModuleCat.ofHom (tensorHom A B N φ)
  map_id M := ModuleCat.hom_ext (tensorHom_id A B N M)
  map_comp φ ψ := ModuleCat.hom_ext (tensorHom_comp A B N φ ψ)

/-- The value of the functor at an `A`-module is the tensor product. -/
lemma functor_obj (M : ModuleCat.{u} A) :
    (functor A B N).obj M = ModuleCat.of B (N ⊗[A] M) :=
  rfl

/-- The functor acts on morphisms by `tensorHom`. -/
lemma functor_map {M M' : ModuleCat.{u} A} (φ : M ⟶ M') :
    ((functor A B N).map φ).hom = tensorHom A B N φ :=
  rfl

/-- **The normalisation on morphisms.** The functor acts on a morphism in the second variable
only. -/
@[simp]
lemma functor_map_tmul {M M' : ModuleCat.{u} A} (φ : M ⟶ M') (n : N) (m : M) :
    (functor A B N).map φ (n ⊗ₜ[A] m) = n ⊗ₜ[A] φ m :=
  rfl

/-- The functor is additive: a tensor product is additive in each variable. -/
instance functor_additive : (functor A B N).Additive where
  map_add {_ _ φ ψ} := ModuleCat.hom_ext (tensorHom_add A B N φ ψ)

/-- **Two morphisms out of `N ⊗[A] M` agreeing on pure tensors are equal.** -/
theorem hom_ext {M : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
    {φ ψ : (functor A B N).obj M ⟶ Y}
    (h : ∀ (n : N) (m : M), φ.hom (n ⊗ₜ[A] m) = ψ.hom (n ⊗ₜ[A] m)) : φ = ψ := by
  let φ' : (N ⊗[A] (M : Type u)) →ₗ[B] (Y : Type u) := φ.hom
  let ψ' : (N ⊗[A] (M : Type u)) →ₗ[B] (Y : Type u) := ψ.hom
  have key : ∀ z : N ⊗[A] (M : Type u), φ' z = ψ' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul n m => exact h n m
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact ModuleCat.hom_ext (LinearMap.ext key)

/-- **For `N` flat over `A` the functor preserves exactness of short complexes.** This is
`Module.Flat.lTensor_exact`, read through the description of exactness in `ModuleCat` by
exactness of the underlying maps of sets. -/
theorem exact_map_of_flat [Module.Flat A N] (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.Exact) : (S.map (functor A B N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  have h : Function.Exact (LinearMap.lTensor N S.f.hom) (LinearMap.lTensor N S.g.hom) :=
    Module.Flat.lTensor_exact N hS
  rw [show ⇑(S.map (functor A B N)).f.hom = ⇑(LinearMap.lTensor N S.f.hom) from
      funext (tensorHom_apply_eq_lTensor A B N S.f),
    show ⇑(S.map (functor A B N)).g.hom = ⇑(LinearMap.lTensor N S.g.hom) from
      funext (tensorHom_apply_eq_lTensor A B N S.g)]
  exact h

/-- Exactness of the functor gives preservation of both finite limits and finite colimits. -/
private theorem preserves_finite_limits_and_colimits_of_flat [Module.Flat A N] :
    PreservesFiniteLimits (functor A B N) ∧ PreservesFiniteColimits (functor A B N) :=
  ((Functor.exact_tfae (functor A B N)).out 2 4).mp (exact_map_of_flat A B N)

/-- **For `N` flat over `A` the functor preserves homology.** -/
theorem preservesHomology_of_flat [Module.Flat A N] : (functor A B N).PreservesHomology :=
  ((Functor.exact_tfae (functor A B N)).out 2 3).mp (exact_map_of_flat A B N)

/-- **For `N` flat over `A` the functor preserves finite limits.** -/
theorem preservesFiniteLimits_of_flat [Module.Flat A N] :
    PreservesFiniteLimits (functor A B N) :=
  (preserves_finite_limits_and_colimits_of_flat A B N).1

/-- **For `N` flat over `A` the functor preserves finite colimits.** -/
theorem preservesFiniteColimits_of_flat [Module.Flat A N] :
    PreservesFiniteColimits (functor A B N) :=
  (preserves_finite_limits_and_colimits_of_flat A B N).2

/-- **For `N` flat over `A` the functor preserves products indexed by a finite type**, in an
arbitrary universe. -/
theorem preservesLimitsOfShape_discrete_of_flat [Module.Flat A N] (J : Type*) [Finite J] :
    PreservesLimitsOfShape (Discrete J) (functor A B N) := by
  have := preservesFiniteLimits_of_flat A B N
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have h : PreservesLimitsOfShape (Discrete (Fin n)) (functor A B N) := inferInstance
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e).symm (functor A B N)

end Stacks.TensorBimodule

end
