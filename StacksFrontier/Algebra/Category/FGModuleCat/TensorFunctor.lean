module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensoring with a fixed module, as a functor on finitely generated modules

For a fixed `R`-module `W`, tensoring with `W` is an `R`-linear additive functor

`FGModuleCat R ⥤ ModuleCat R`,  `V ↦ W ⊗[R] V`.

The target universe is forced to contain both the universe of `W` and the universe of the
finitely generated modules, so this is not an endofunctor of `ModuleCat` and is not the
monoidal `tensorLeft`; `W` may be much larger than the modules it is tensored with.

## Main definitions

* `FGModuleCat.tensorFunctor`: the functor `V ↦ W ⊗[R] V`.
* `FGModuleCat.tensorFunctorObjRankOne`: the identification of its value at the rank-one module
  with `W`.

## Main results

* `FGModuleCat.tensorFunctor_additive` and `FGModuleCat.tensorFunctor_linear`: the functor is
  additive and `R`-linear.
* `FGModuleCat.finite_tensorFunctor_obj_rankOne`: its value at the rank-one module is a finite
  module whenever `W` is.
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace FGModuleCat

universe u u₂

variable (R : Type u) [CommRing R] (W : Type u₂) [AddCommGroup W] [Module R W]

/-- Tensoring with a fixed module `W`, as a functor from finitely generated `R`-modules to
`R`-modules: `V ↦ W ⊗[R] V`. -/
noncomputable def tensorFunctor : FGModuleCat.{u} R ⥤ ModuleCat.{max u₂ u} R where
  obj V := ModuleCat.of R (TensorProduct R W V.obj)
  map f := ModuleCat.ofHom (LinearMap.lTensor W f.hom.hom)
  map_id V := by ext x; simp
  map_comp f g := by ext x; simp

/-- The functor `W ⊗[R] -` sends a morphism `f` to `𝟙 W ⊗ f`: it maps `a ⊗ₜ b` to `a ⊗ₜ f b`. -/
@[simp]
theorem tensorFunctor_map_tmul {V V' : FGModuleCat.{u} R} (f : V ⟶ V') (a : W) (b : V.obj) :
    (tensorFunctor R W).map f (a ⊗ₜ[R] b) = a ⊗ₜ[R] f.hom.hom b := rfl

/-- Tensoring with a fixed module is an additive functor. -/
instance tensorFunctor_additive : (tensorFunctor R W).Additive where
  map_add := by
    intro V V' f g
    apply ModuleCat.hom_ext
    change LinearMap.lTensor W (f.hom + g.hom).hom = _
    rw [ModuleCat.hom_add, LinearMap.lTensor_add]
    rfl

/-- Tensoring with a fixed module is an `R`-linear functor. -/
instance tensorFunctor_linear : (tensorFunctor R W).Linear R where
  map_smul := by
    intro V V' f r
    apply ModuleCat.hom_ext
    change LinearMap.lTensor W (r • f.hom).hom = _
    rw [ModuleCat.hom_smul, LinearMap.lTensor_smul]
    rfl

/-- The value of `W ⊗[R] -` at the rank-one module is `W`. -/
noncomputable def tensorFunctorObjRankOne :
    (tensorFunctor R W).obj (FGModuleCat.of R R) ≃ₗ[R] W :=
  TensorProduct.rid R W

/-- The value of `W ⊗[R] -` at the rank-one module is a finite module whenever `W` is; in
particular it is finite dimensional when `R` is a field and `W` is. -/
instance finite_tensorFunctor_obj_rankOne [Module.Finite R W] :
    Module.Finite R ((tensorFunctor R W).obj (FGModuleCat.of R R)) :=
  Module.Finite.equiv (tensorFunctorObjRankOne R W).symm

end FGModuleCat

end
