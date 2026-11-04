module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian

/-!
# The relative tensor product is additive in the right module

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras and
let `N` be a left graded `A`-module. The functor `- ⊗_A N` is additive on homomorphisms of right
graded `A`-modules, and likewise for the differential graded tensor product.

## Main results

* `SheafOfModules.RelativeTensor.gradedTensorMapRight_add` and `gradedTensorMapRight_zero`: the
  map induced on `- ⊗_A N` by a homomorphism of right graded modules is additive in that
  homomorphism.
* `SheafOfModules.RelativeTensor.dgTensorFunctor_additive`: the functor `- ⊗_A N` from right
  differential graded `A`-modules to complexes of `O`-modules is additive, hence carries a
  biproduct of right differential graded modules to a biproduct of complexes.

## Implementation notes

Additivity is proved on the presentation and transported: the balance map is unchanged by the
homomorphism, so the induced map of cokernels is additive as soon as the map of the direct sums
`⨁_{p + q = n} P^p ⊗_O N^q` is, and that reduces summandwise to the additivity of the objectwise
tensor product in its first factor. Sheafification is additive, so the sheafified maps inherit
it.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u


namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

namespace RelativeTensor

section Graded

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)} {P P' : GradedModule.{t, m, m} A}
  (N : LeftGradedModule.{t, m, m} A)

/-- The map of direct sums induced by a homomorphism of right graded modules is additive in the
homomorphism. -/
theorem tensorSumMapRight_add (h h' : P ⟶ P') (n : ℤ) :
    tensorSumMapRight (h + h') N n = tensorSumMapRight h N n + tensorSumMapRight h' N n := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [tensorSumι_tensorSumMapRight, Preadditive.comp_add, tensorSumι_tensorSumMapRight,
    tensorSumι_tensorSumMapRight, ← Preadditive.add_comp]
  refine congrArg (fun φ ↦ φ ≫ tensorSumι P' N p) ?_
  rw [show ((h + h').app p.1.1).val = (h.app p.1.1).val + (h'.app p.1.1).val from rfl]
  exact PresheafOfModules.tensorHom_add_left _ _ _

/-- The map of direct sums induced by the zero homomorphism of right graded modules is zero. -/
theorem tensorSumMapRight_zero (n : ℤ) : tensorSumMapRight (0 : P ⟶ P') N n = 0 := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [tensorSumι_tensorSumMapRight, comp_zero,
    show ((0 : P ⟶ P').app p.1.1).val = 0 from rfl,
    PresheafOfModules.tensorHom_zero_left, zero_comp]

/-- Degree `n` of the map of relative tensor products of presheaves induced by a homomorphism of
right graded modules is additive in the homomorphism. -/
theorem gradedTensorMapPreRight_add (h h' : P ⟶ P') (n : ℤ) :
    gradedTensorMapPreRight (h + h') N n =
      gradedTensorMapPreRight h N n + gradedTensorMapPreRight h' N n := by
  refine (cancel_epi (gradedTensorπ P N n)).mp ?_
  rw [gradedTensorπ_gradedTensorMapPreRight, Preadditive.comp_add,
    gradedTensorπ_gradedTensorMapPreRight, gradedTensorπ_gradedTensorMapPreRight,
    ← Preadditive.add_comp, tensorSumMapRight_add]

/-- The zero homomorphism of right graded modules induces the zero map of relative tensor
products of presheaves. -/
theorem gradedTensorMapPreRight_zero (n : ℤ) :
    gradedTensorMapPreRight (0 : P ⟶ P') N n = 0 := by
  refine (cancel_epi (gradedTensorπ P N n)).mp ?_
  rw [gradedTensorπ_gradedTensorMapPreRight, tensorSumMapRight_zero, zero_comp, comp_zero]

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Degree `n` of the map `- ⊗_A N` induced by a homomorphism of right graded modules is
additive in the homomorphism. -/
theorem gradedTensorMapRight_add (h h' : P ⟶ P') (n : ℤ) :
    gradedTensorMapRight (h + h') N n =
      gradedTensorMapRight h N n + gradedTensorMapRight h' N n := by
  rw [gradedTensorMapRight, gradedTensorMapPreRight_add]
  exact (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map_add

/-- The zero homomorphism of right graded modules induces the zero map of `- ⊗_A N`. -/
theorem gradedTensorMapRight_zero (n : ℤ) : gradedTensorMapRight (0 : P ⟶ P') N n = 0 := by
  rw [gradedTensorMapRight, gradedTensorMapPreRight_zero]
  exact (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).map_zero _ _

/-- The functor `- ⊗_A N` on right graded modules is additive degreewise. -/
theorem gradedTensorFunctor_map_add {P P' : GradedModule.{t, m, m} A} (h h' : P ⟶ P') :
    (gradedTensorFunctor N).map (h + h') =
      fun n ↦ gradedTensorMapRight h N n + gradedTensorMapRight h' N n :=
  funext fun n ↦ gradedTensorMapRight_add N h h' n

end Sheafify

end Graded

section DifferentialGraded

variable {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {P P' : DifferentialGradedModule.{t, m, m} A}
  (N : LeftDifferentialGradedModule.{t, m, m} A)

/-- Forgetting the differential of a morphism of right differential graded modules is additive. -/
theorem gMap_add (h h' : P ⟶ P') : gMap (h + h') = gMap h + gMap h' :=
  GradedModule.Hom.ext fun _ ↦ rfl

/-- Forgetting the differential sends the zero morphism to the zero homomorphism. -/
theorem gMap_zero : gMap (0 : P ⟶ P') = 0 :=
  GradedModule.Hom.ext fun _ ↦ rfl

/-- The map of relative tensor products of presheaves induced by a morphism of right
differential graded modules is additive in the morphism. -/
theorem dgTensorPreMap_add (h h' : P ⟶ P') :
    dgTensorPreMap N (h + h') = dgTensorPreMap N h + dgTensorPreMap N h' := by
  ext n
  rw [dgTensorPreMap_f, gMap_add, gradedTensorMapPreRight_add]
  rfl

/-- The zero morphism of right differential graded modules induces the zero map of relative
tensor products of presheaves. -/
theorem dgTensorPreMap_zero : dgTensorPreMap N (0 : P ⟶ P') = 0 := by
  ext n
  rw [dgTensorPreMap_f, gMap_zero, gradedTensorMapPreRight_zero]
  rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- **The functor `- ⊗_A N` to complexes of `O`-modules is additive**, so it carries a biproduct
of right differential graded modules to a biproduct of complexes. -/
instance dgTensorFunctor_additive : (dgTensorFunctor N).Additive where
  map_add {_ _ h h'} := by
    change sheafifyComplex.map (dgTensorPreMap N (h + h')) = _
    rw [dgTensorPreMap_add]
    exact sheafifyComplex.map_add

end Sheafify

end DifferentialGraded

end RelativeTensor

end SheafOfModules
