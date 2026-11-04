module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorColimits

/-!
# The relative tensor product of graded modules is a bifunctor

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras,
let `h : P ⟶ P'` be a homomorphism of right graded `A`-modules and let `f : N ⟶ N'` be a
homomorphism of left graded `A`-modules. The two induced maps on relative tensor products
commute:

`(h ⊗ 1) ∘ (1 ⊗ f) = (1 ⊗ f) ∘ (h ⊗ 1) : P ⊗_A N ⟶ P' ⊗_A N'`.

Equivalently, the maps `P ⊗_A f` assemble into a natural transformation between the functors
`- ⊗_A N` and `- ⊗_A N'` of the right graded module.

## Main definitions

* `SheafOfModules.RelativeTensor.gradedTensorDegreeNatTrans` is `P ↦ P ⊗_A f` read as a natural
  transformation `gradedTensorDegree N n ⟶ gradedTensorDegree N' n`.

## Main results

* `SheafOfModules.RelativeTensor.tensorSumMapRight_tensorSumMap` and
  `relationSumMapRight_relationSumMap`: the two direct sums of the presentation of the relative
  tensor product are bifunctorial.
* `SheafOfModules.RelativeTensor.gradedTensorMapPreRight_gradedTensorMapPre` and
  `gradedTensorMapRight_gradedTensorMap`: the relative tensor product of graded modules is a
  bifunctor, before and after sheafification.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}
  {P P' : GradedModule.{t, m, m} A} {N N' : LeftGradedModule.{t, m, m} A}

/-- The direct sum `⨁_{p + q = n} P^p ⊗_O N^q` of the presentation of the relative tensor
product is bifunctorial. -/
theorem tensorSumMapRight_tensorSumMap (h : P ⟶ P') (f : N ⟶ N') (n : ℤ) :
    tensorSumMapRight h N n ≫ tensorSumMap P' f n =
      tensorSumMap P f n ≫ tensorSumMapRight h N' n := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [reassoc_of% tensorSumι_tensorSumMapRight, tensorSumι_tensorSumMap,
    reassoc_of% tensorSumι_tensorSumMap, tensorSumι_tensorSumMapRight,
    reassoc_of% PresheafOfModules.tensorHom_comp_tensorHom,
    reassoc_of% PresheafOfModules.tensorHom_comp_tensorHom]
  simp

/-- The direct sum `⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t` of relations of the presentation of
the relative tensor product is bifunctorial. -/
theorem relationSumMapRight_relationSumMap (h : P ⟶ P') (f : N ⟶ N') (n : ℤ) :
    relationSumMapRight h N n ≫ relationSumMap P' f n =
      relationSumMap P f n ≫ relationSumMapRight h N' n := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [reassoc_of% relationSumι_relationSumMapRight, relationSumι_relationSumMap,
    reassoc_of% relationSumι_relationSumMap, relationSumι_relationSumMapRight,
    reassoc_of% PresheafOfModules.tensorHom_comp_tensorHom,
    reassoc_of% PresheafOfModules.tensorHom_comp_tensorHom]
  simp

/-- The relative tensor product of graded modules is a bifunctor, as a statement about
presheaves of modules. -/
theorem gradedTensorMapPreRight_gradedTensorMapPre (h : P ⟶ P') (f : N ⟶ N') (n : ℤ) :
    gradedTensorMapPreRight h N n ≫ gradedTensorMapPre P' f n =
      gradedTensorMapPre P f n ≫ gradedTensorMapPreRight h N' n := by
  refine (cancel_epi (gradedTensorπ P N n)).mp ?_
  simp [gradedTensorMapPre, reassoc_of% gradedTensorπ_gradedTensorMapPreRight,
    reassoc_of% tensorSumMapRight_tensorSumMap]

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- The relative tensor product of graded modules is a bifunctor: tensoring a homomorphism
of right graded modules and a homomorphism of left graded modules in either order gives the
same map `P ⊗_A N ⟶ P' ⊗_A N'`. -/
theorem gradedTensorMapRight_gradedTensorMap (h : P ⟶ P') (f : N ⟶ N') (n : ℤ) :
    gradedTensorMapRight h N n ≫ gradedTensorMap P' f n =
      gradedTensorMap P f n ≫ gradedTensorMapRight h N' n := by
  have key := congrArg (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map (gradedTensorMapPreRight_gradedTensorMapPre h f n)
  rw [Functor.map_comp, Functor.map_comp] at key
  exact key

/-- Two successive homomorphisms of left graded modules can be moved across a homomorphism of
right graded modules. -/
theorem gradedTensorMap_gradedTensorMap_gradedTensorMapRight (h : P ⟶ P')
    {N₁ N₂ N₃ : LeftGradedModule.{t, m, m} A} (a : N₁ ⟶ N₂) (b : N₂ ⟶ N₃) (n : ℤ) :
    gradedTensorMap P a n ≫ gradedTensorMap P b n ≫ gradedTensorMapRight h N₃ n =
      gradedTensorMapRight h N₁ n ≫ gradedTensorMap P' a n ≫ gradedTensorMap P' b n := by
  rw [← gradedTensorMapRight_gradedTensorMap h b n, ← Category.assoc,
    ← gradedTensorMapRight_gradedTensorMap h a n, Category.assoc]

/-- Tensoring with a homomorphism `f : N ⟶ N'` of left graded modules, as a natural
transformation between the degree-`n` relative tensor product functors of the right graded
module. -/
noncomputable def gradedTensorDegreeNatTrans (f : N ⟶ N') (n : ℤ) :
    gradedTensorDegree N n ⟶ gradedTensorDegree N' n where
  app P := gradedTensorMap P f n
  naturality _ _ h := gradedTensorMapRight_gradedTensorMap h f n

/-- The component of `gradedTensorDegreeNatTrans f n` at `Q` is `Q ⊗_A f`. -/
@[simp]
theorem gradedTensorDegreeNatTrans_app (f : N ⟶ N') (n : ℤ) (Q : GradedModule.{t, m, m} A) :
    (gradedTensorDegreeNatTrans f n).app Q = gradedTensorMap Q f n :=
  rfl

end Sheafify

end RelativeTensor

end SheafOfModules
