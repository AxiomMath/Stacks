module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor
public import StacksFrontier.CategoryTheory.Limits.PresentedFunctorColimits

/-!
# The relative tensor product commutes with colimits in the right module

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras
and let `N` be a left graded `A`-module. Degree `n` of the relative tensor product `- ⊗_A N`
is, by construction, the associated sheaf of the cokernel of the balance map
`⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t ⟶ ⨁_{p + q = n} P^p ⊗_O N^q`. This file shows that
`P ↦ (P ⊗_A N)ⁿ` commutes with colimits of right graded `A`-modules, given that the associated
sheaf of the objectwise tensor product with a fixed presheaf of modules commutes with colimits of
sheaves of modules in its first variable.

## Main definitions

* `SheafOfModules.RelativeTensor.tensorRightPre` is the objectwise tensor product with a fixed
  presheaf of modules in the second variable, and
  `SheafOfModules.RelativeTensor.sheafTensorRightPre` its associated sheaf, a functor on sheaves
  of modules.
* `SheafOfModules.RelativeTensor.tensorSumFunctor` and
  `SheafOfModules.RelativeTensor.relationSumFunctor` are the two direct sums of the presentation,
  read as functors of the right graded module.
* `SheafOfModules.RelativeTensor.tensorSumInclusion` and
  `SheafOfModules.RelativeTensor.relationSumInclusion` are the inclusions of the summands, and
  `SheafOfModules.RelativeTensor.balanceNatTrans`,
  `SheafOfModules.RelativeTensor.gradedTensorProjection` are the balance map and the canonical
  surjection, all four as natural transformations.
* `SheafOfModules.RelativeTensor.gradedTensorDegree` is degree `n` of `- ⊗_A N`.

## Main results

* `SheafOfModules.RelativeTensor.relationSumMapRight_id` and
  `relationSumMapRight_comp`: the direct sum of relations is functorial in the right graded
  module.
* `SheafOfModules.RelativeTensor.isColimitCofan_tensorSum` and
  `isColimitCofan_relationSum`: the inclusions of the summands remain a colimiting cofan after
  sheafification.
* `SheafOfModules.RelativeTensor.isColimitCokernelCofork_gradedTensor`: the canonical surjection
  remains a cokernel of the balance map after sheafification.
* `SheafOfModules.RelativeTensor.preservesColimitsOfSize_tensorSumFunctor`,
  `preservesColimitsOfSize_relationSumFunctor` and
  `preservesColimitsOfSize_gradedTensorDegree`: the functor `- ⊗_A N` commutes in each degree
  with the colimits of right graded `A`-modules, given that the associated sheaf of the
  objectwise tensor product with a fixed presheaf of modules does.

## Implementation notes

The three colimit statements assume `PreservesColimitsOfSize (sheafTensorRightPre G)` for every
presheaf of modules `G`. The second tensor factor is a presheaf rather than a sheaf because the
summands of the direct sum of relations are `P^r ⊗_O (A^s ⊗_O N^t)`, whose second factor is an
objectwise tensor product.

The presentation is given by natural transformations and pointwise universal properties rather
than by isomorphisms with `∐` and `cokernel`. `sheafTensorRightPre G` is built from
`PresheafOfModules.tensorBifunctor`, so that the functoriality of the summands in the right graded
module is definitionally the map of the presentation.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.CategoryTheory.PresentedFunctor

universe s' s t m v u

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- Sheafification of presheaves of `O`-modules. -/
noncomputable abbrev moduleSheafify :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      SheafOfModules.{m} (toRingCat J Osharp) :=
  PresheafOfModules.sheafification (R := toRingCat J Osharp) (𝟙 (toRingCat J Osharp).obj)

/-- Sheafification of presheaves of modules commutes with all colimits. -/
instance moduleSheafify_preservesColimitsOfSize :
    PreservesColimitsOfSize.{s, s'} (moduleSheafify.{t, m} (Osharp := Osharp)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (toRingCat J Osharp).obj)).leftAdjoint_preservesColimits

/-- The objectwise tensor product with a fixed presheaf of modules in the second variable. -/
noncomputable def tensorRightPre
    (G : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) :=
  (_root_.PresheafOfModules.tensorBifunctor.{v, u, t, m, m} Osharp.obj).flip.obj G

/-- The associated sheaf of the objectwise tensor product with a fixed presheaf of modules, as
a functor of the sheaf of modules in the first variable. -/
noncomputable def sheafTensorRightPre
    (G : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    SheafOfModules.{m} (toRingCat J Osharp) ⥤ SheafOfModules.{m} (toRingCat J Osharp) :=
  SheafOfModules.forget _ ⋙ tensorRightPre G ⋙ moduleSheafify

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

section Functoriality

variable {P P' P'' : GradedModule.{t, m, m} A} (N : LeftGradedModule.{t, m, m} A)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- The direct sum of relations of the presentation of `P ⊗_A N` is unchanged by the identity
of `P`. -/
theorem relationSumMapRight_id (n : ℤ) :
    relationSumMapRight (𝟙 P) N n = 𝟙 (relationSum P N n) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [relationSumι_relationSumMapRight, Category.comp_id]
  refine (congrArg (· ≫ relationSumι P N i) ?_).trans (Category.id_comp _)
  exact PresheafOfModules.tensorObj_hom_ext fun X x y ↦ PresheafOfModules.tensorHom_tmul ..

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- The direct sum of relations of the presentation of `P ⊗_A N` is functorial in `P`. -/
theorem relationSumMapRight_comp (h : P ⟶ P') (h' : P' ⟶ P'') (n : ℤ) :
    relationSumMapRight (h ≫ h') N n =
      relationSumMapRight h N n ≫ relationSumMapRight h' N n := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [relationSumι_relationSumMapRight, ← Category.assoc, relationSumι_relationSumMapRight,
    Category.assoc, relationSumι_relationSumMapRight, ← Category.assoc]
  refine congrArg (· ≫ relationSumι P'' N i) ?_
  exact PresheafOfModules.tensorObj_hom_ext fun X x y ↦ PresheafOfModules.tensorHom_tmul ..

end Functoriality

section Presentation

variable (N : LeftGradedModule.{t, m, m} A) (n : ℤ)

/-- The direct sum `⨁_{p + q = n} P^p ⊗_O N^q` of the presentation, sheafified, as a functor of
the right graded module `P`. -/
noncomputable def tensorSumFunctor :
    GradedModule.{t, m, m} A ⥤ SheafOfModules.{m} (toRingCat J Osharp) where
  obj P := moduleSheafify.obj (tensorSum P N n)
  map h := moduleSheafify.map (tensorSumMapRight h N n)
  map_id P := by rw [tensorSumMapRight_id]; exact moduleSheafify.map_id _
  map_comp h h' := by rw [tensorSumMapRight_comp]; exact moduleSheafify.map_comp _ _

/-- The direct sum `⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t` of relations, sheafified, as a
functor of the right graded module `P`. -/
noncomputable def relationSumFunctor :
    GradedModule.{t, m, m} A ⥤ SheafOfModules.{m} (toRingCat J Osharp) where
  obj P := moduleSheafify.obj (relationSum P N n)
  map h := moduleSheafify.map (relationSumMapRight h N n)
  map_id P := by rw [relationSumMapRight_id]; exact moduleSheafify.map_id _
  map_comp h h' := by rw [relationSumMapRight_comp]; exact moduleSheafify.map_comp _ _

/-- Degree `n` of the relative tensor product `- ⊗_A N`, as a functor of the right graded
module. -/
noncomputable abbrev gradedTensorDegree :
    GradedModule.{t, m, m} A ⥤ SheafOfModules.{m} (toRingCat J Osharp) :=
  gradedTensorFunctor N ⋙ GradedObject.eval n

/-- The inclusion of the summand `P^p ⊗_O N^q` into the sheafified direct sum of degree `n`, as
a natural transformation in `P`. -/
noncomputable def tensorSumInclusion (p : TensorIndex n) :
    GradedModule.pieceFunctor A p.1.1 ⋙ sheafTensorRightPre (N.piece p.1.2).val ⟶
      tensorSumFunctor N n where
  app P := moduleSheafify.map (tensorSumι P N p)
  naturality P P' h := by
    change moduleSheafify.map
        (PresheafOfModules.tensorHom (h.app p.1.1).val (𝟙 (N.piece p.1.2).val)) ≫
          moduleSheafify.map (tensorSumι P' N p) =
        moduleSheafify.map (tensorSumι P N p) ≫ moduleSheafify.map (tensorSumMapRight h N n)
    rw [← moduleSheafify.map_comp, ← moduleSheafify.map_comp, tensorSumι_tensorSumMapRight]

/-- The inclusion of the summand `P^r ⊗_O A^s ⊗_O N^t` into the sheafified direct sum of
relations of degree `n`, as a natural transformation in `P`. -/
noncomputable def relationSumInclusion (i : RelationIndex n) :
    GradedModule.pieceFunctor A i.1.1 ⋙
        sheafTensorRightPre
          (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val) ⟶
      relationSumFunctor N n where
  app P := moduleSheafify.map (relationSumι P N i)
  naturality P P' h := by
    change moduleSheafify.map (PresheafOfModules.tensorHom (h.app i.1.1).val
          (𝟙 (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val))) ≫
          moduleSheafify.map (relationSumι P' N i) =
        moduleSheafify.map (relationSumι P N i) ≫
          moduleSheafify.map (relationSumMapRight h N n)
    rw [← moduleSheafify.map_comp, ← moduleSheafify.map_comp,
      relationSumι_relationSumMapRight]

/-- The balance map of the presentation, sheafified, as a natural transformation in the right
graded module. -/
noncomputable def balanceNatTrans : relationSumFunctor N n ⟶ tensorSumFunctor N n where
  app P := moduleSheafify.map (balanceMap P N n)
  naturality P P' h := by
    change moduleSheafify.map (relationSumMapRight h N n) ≫
          moduleSheafify.map (balanceMap P' N n) =
        moduleSheafify.map (balanceMap P N n) ≫ moduleSheafify.map (tensorSumMapRight h N n)
    rw [← moduleSheafify.map_comp, ← moduleSheafify.map_comp, balanceMap_naturality_right]

/-- The canonical surjection onto degree `n` of `P ⊗_A N`, as a natural transformation in the
right graded module. -/
noncomputable def gradedTensorProjection : tensorSumFunctor N n ⟶ gradedTensorDegree N n where
  app P := moduleSheafify.map (gradedTensorπ P N n)
  naturality P P' h := by
    change moduleSheafify.map (tensorSumMapRight h N n) ≫
          moduleSheafify.map (gradedTensorπ P' N n) =
        moduleSheafify.map (gradedTensorπ P N n) ≫
          moduleSheafify.map (gradedTensorMapPreRight h N n)
    rw [← moduleSheafify.map_comp, ← moduleSheafify.map_comp,
      gradedTensorπ_gradedTensorMapPreRight]

/-- The balance map composed with the canonical surjection vanishes. -/
theorem balanceNatTrans_comp_gradedTensorProjection (P : GradedModule.{t, m, m} A) :
    (balanceNatTrans N n).app P ≫ (gradedTensorProjection N n).app P = 0 := by
  show moduleSheafify.map (balanceMap P N n) ≫ moduleSheafify.map (gradedTensorπ P N n) = 0
  rw [← moduleSheafify.map_comp, cokernel.condition, moduleSheafify.map_zero]

/-- The inclusions of the summands remain a colimiting cofan after sheafification. -/
noncomputable def isColimitCofan_tensorSum (P : GradedModule.{t, m, m} A) :
    IsColimit (Cofan.mk ((tensorSumFunctor N n).obj P)
      fun p ↦ (tensorSumInclusion N n p).app P) :=
  isColimitCofanMkObjOfIsColimit moduleSheafify (tensorSummand P N) (tensorSumι P N)
    (coproductIsCoproduct _)

/-- The inclusions of the summands of relations remain a colimiting cofan after
sheafification. -/
noncomputable def isColimitCofan_relationSum (P : GradedModule.{t, m, m} A) :
    IsColimit (Cofan.mk ((relationSumFunctor N n).obj P)
      fun i ↦ (relationSumInclusion N n i).app P) :=
  isColimitCofanMkObjOfIsColimit moduleSheafify (relationSummand P N) (relationSumι P N)
    (coproductIsCoproduct _)

/-- The canonical surjection remains a cokernel of the balance map after sheafification. -/
noncomputable def isColimitCokernelCofork_gradedTensor (P : GradedModule.{t, m, m} A) :
    IsColimit (CokernelCofork.ofπ ((gradedTensorProjection N n).app P)
      (balanceNatTrans_comp_gradedTensorProjection N n P)) := by
  have h : IsColimit ((moduleSheafify (Osharp := Osharp)).mapCocone
      (CokernelCofork.ofπ (gradedTensorπ P N n) (cokernel.condition (balanceMap P N n)))) :=
    isColimitOfPreserves moduleSheafify (cokernelIsCokernel (balanceMap P N n))
  exact isColimitMapCoconeCoforkEquiv' moduleSheafify _ h

end Presentation

section Colimits

variable (N : LeftGradedModule.{t, m, m} A) (n : ℤ)
  [∀ G : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat),
    PreservesColimitsOfSize.{m, m} (sheafTensorRightPre G)]

/-- The sheafified objectwise tensor product with a fixed presheaf of modules, applied to a
graded piece of the right graded module, commutes with colimits. -/
private theorem preservesColimitsOfSize_pieceFunctor_comp (k : ℤ)
    (G : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    PreservesColimitsOfSize.{m, m} (GradedModule.pieceFunctor A k ⋙ sheafTensorRightPre G) :=
  have : PreservesColimitsOfSize.{m, m} (GradedModule.pieceFunctor.{t, m, m} A k) :=
    GradedModule.pieceFunctor_preservesColimitsOfSize' (A := A) k
  inferInstance

/-- The sheafified direct sum `⨁_{p + q = n} P^p ⊗_O N^q` commutes with the colimits of right
graded modules. -/
theorem preservesColimitsOfSize_tensorSumFunctor :
    PreservesColimitsOfSize.{m, m} (tensorSumFunctor N n) := by
  have := fun p : TensorIndex n ↦
    preservesColimitsOfSize_pieceFunctor_comp (A := A) p.1.1 (N.piece p.1.2).val
  exact preservesColimitsOfSize_of_isColimitCofan (tensorSumInclusion N n)
    (isColimitCofan_tensorSum N n)

/-- The sheafified direct sum of relations commutes with the colimits of right graded
modules. -/
theorem preservesColimitsOfSize_relationSumFunctor :
    PreservesColimitsOfSize.{m, m} (relationSumFunctor N n) := by
  have := fun i : RelationIndex n ↦ preservesColimitsOfSize_pieceFunctor_comp (A := A) i.1.1
    (PresheafOfModules.tensorObj (A.piece i.1.2.1).val (N.piece i.1.2.2).val)
  exact preservesColimitsOfSize_of_isColimitCofan (relationSumInclusion N n)
    (isColimitCofan_relationSum N n)

/-- Degree `n` of the relative tensor product `- ⊗_A N` commutes with the colimits of right
graded `A`-modules, given that the associated sheaf of the objectwise tensor product with a
fixed presheaf of modules commutes with the colimits of sheaves of modules in its first
variable. -/
theorem preservesColimitsOfSize_gradedTensorDegree :
    PreservesColimitsOfSize.{m, m} (gradedTensorDegree N n) := by
  have := preservesColimitsOfSize_relationSumFunctor N n
  have := preservesColimitsOfSize_tensorSumFunctor N n
  exact preservesColimitsOfSize_of_isColimitCokernelCofork (balanceNatTrans N n)
    (gradedTensorProjection N n) (balanceNatTrans_comp_gradedTensorProjection N n)
    (isColimitCokernelCofork_gradedTensor N n)

end Colimits

end RelativeTensor

end SheafOfModules

end
