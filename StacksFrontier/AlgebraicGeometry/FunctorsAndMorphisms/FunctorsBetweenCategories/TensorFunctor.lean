module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring with a bimodule as a functor between module categories

Let `A` and `B` be algebras over a commutative ring `R`. A module over `A ⊗[R] B` determines a
functor from `A`-modules to `B`-modules by tensoring. This functor is `R`-linear and has the
standard exactness, cocontinuity and adjointness properties of a tensor functor.

## Main definitions

* `ModuleCat.tensorFunctor` is tensoring with an `A ⊗[R] B`-module, viewed as a functor from
  `A`-modules to `B`-modules.

## Main results

* `ModuleCat.tensorFunctor_linear`: the functor is `R`-linear.
* `ModuleCat.tensorFunctor_preservesFiniteColimits`: it is right exact.
* `ModuleCat.tensorFunctor_preservesDirectSums`: it preserves arbitrary direct sums.
* `ModuleCat.tensorFunctor_preservesColimits`: it preserves all colimits.
* `ModuleCat.tensorFunctor_isLeftAdjoint`: it has a right adjoint.

## Implementation notes

Tensoring is expressed as extension of scalars from `A` to `A ⊗[R] B`, tensoring there with the
given module, and restriction of scalars to `B`. Right exactness is preservation of finite
colimits and preservation of arbitrary direct sums is preservation of colimits of discrete
diagrams, so each of the five properties is stated in the form in which it is used.

## References

* [Stacks Project, Tag 0GNT](https://stacks.math.columbia.edu/tag/0GNT)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra TensorProduct

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

private noncomputable instance extendScalarsLinear :
    (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).Linear R where
  map_smul {X Y} f r := by
    -- Both sides are evaluated on `1 ⊗ₜ x`. `rw` cannot rewrite with
    -- `ExtendScalars.map_tmul` here, because the `Module A (A ⊗[R] B)` instance in the goal is
    -- the one `ModuleCat.restrictScalars` builds rather than the one instance search finds, so
    -- the two spellings of the tensor product are not syntactically equal. Applying the lemma
    -- as a term instead lets the elaborator discharge that mismatch by unification.
    ext x
    refine (ModuleCat.ExtendScalars.map_tmul _ (r • f) 1 x).trans ?_
    refine Eq.symm ((congrArg (fun z => r • z) (ModuleCat.ExtendScalars.map_tmul
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) f 1 x)).trans ?_)
    exact TensorProduct.smul_tmul (algebraMap R A r) _ _

/-- Tensoring with an `A ⊗[R] B`-module, regarded as a functor from `A`-modules to
`B`-modules. -/
@[stacks 0GNT "the functor"]
public noncomputable def tensorFunctor
    (K : ModuleCat.{u} (A ⊗[R] B)) : ModuleCat.{u} A ⥤ ModuleCat.{u} B :=
  ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) ⋙
    (MonoidalCategory.tensoringRight (ModuleCat.{u} (A ⊗[R] B))).obj K ⋙
    ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom

/-- Tensoring with an `A ⊗[R] B`-module is `R`-linear. -/
@[stacks 0GNT "R-linearity"]
public lemma tensorFunctor_linear (K : ModuleCat.{u} (A ⊗[R] B)) :
    (tensorFunctor R A B K).Linear R := by
  let : (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).Linear R :=
    extendScalarsLinear R A B
  let : ((MonoidalCategory.tensoringRight
      (ModuleCat.{u} (A ⊗[R] B))).obj K).Linear R :=
    ⟨fun f r => Functor.Linear.map_smul (R := A ⊗[R] B) f (algebraMap R (A ⊗[R] B) r)⟩
  unfold tensorFunctor
  infer_instance

/-- Tensoring with an `A ⊗[R] B`-module is right exact. -/
@[stacks 0GNT "right exactness"]
public lemma tensorFunctor_preservesFiniteColimits (K : ModuleCat.{u} (A ⊗[R] B)) :
    PreservesFiniteColimits (tensorFunctor R A B K) := by unfold tensorFunctor; infer_instance

/-- Tensoring with an `A ⊗[R] B`-module commutes with arbitrary direct sums. -/
@[stacks 0GNT "arbitrary direct sums"]
public lemma tensorFunctor_preservesDirectSums (K : ModuleCat.{u} (A ⊗[R] B))
    (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (tensorFunctor R A B K) := by
  unfold tensorFunctor; infer_instance

/-- Tensoring with an `A ⊗[R] B`-module commutes with all colimits. -/
@[stacks 0GNT "all colimits"]
public lemma tensorFunctor_preservesColimits (K : ModuleCat.{u} (A ⊗[R] B)) :
    PreservesColimits (tensorFunctor R A B K) := by unfold tensorFunctor; infer_instance

/-- Tensoring with an `A ⊗[R] B`-module has a right adjoint. -/
@[stacks 0GNT "right adjoint"]
public lemma tensorFunctor_isLeftAdjoint (K : ModuleCat.{u} (A ⊗[R] B)) :
    (tensorFunctor R A B K).IsLeftAdjoint := by unfold tensorFunctor; infer_instance

end ModuleCat
