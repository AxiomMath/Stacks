module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover

/-!
# The associated sheaf of the objectwise tensor product commutes with colimits

Let `O` be a sheaf of commutative rings on a site `C` and let `G` be a presheaf of
`O`-modules. The endofunctor `F ↦ (F ⊗_O G)^#` of sheaves of `O`-modules — forget to
presheaves, take the objectwise tensor product with `G`, sheafify — commutes with all
colimits.

## Main results

* `Stacks.preservesColimitsOfSize_tensorRight_endo`: the objectwise tensor product of
  presheaves of modules commutes with colimits in its first variable, with the module universe
  independent of the ring universe.
* `SheafOfModules.RelativeTensor.preservesColimitsOfSize_sheafTensorRightPre`: **the associated
  sheaf of the objectwise tensor product with a fixed presheaf of modules commutes with the
  colimits of sheaves of modules in its first variable.**
* `SheafOfModules.RelativeTensor.preservesColimitsOfSize_gradedTensorDegree_of_sheafify`:
  degree `n` of the relative tensor product `- ⊗_A N` commutes with the colimits of right
  graded `A`-modules, with no hypothesis.

## Implementation notes

`SheafOfModules.RelativeTensor.tensorRightPre G` and `Stacks.tensorRight G` are the same
functor on the nose: the three spellings of the objectwise tensor product of presheaves of
modules in this library — `PresheafOfModules.tensorObj`, `Stacks.tensorObj` and
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj` — are definitionally equal, so
no transport appears here and the results about one spelling apply verbatim to the others.

`Stacks.preservesColimitsOfSize_tensorRight_split` is the same statement at module universe
`max t w` over a ring presheaf in `CommRingCat.{w}`.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe s' s t m v u w z

namespace Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Tensoring presheaves of modules on the right preserves colimits**, with the module
universe independent of the ring universe. -/
instance preservesColimitsOfSize_tensorRight_endo (F : PresheafOfModules.{z} (ringPresheaf O)) :
    PreservesColimitsOfSize.{z, z}
      (tensorRight F : PresheafOfModules.{z} (ringPresheaf O) ⥤ _) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨by
    refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)
    exact isColimitOfPreserves (ModuleCat.tensorRightSplit
      (show ModuleCat.{z} ((ringPresheaf O).obj X) from F.obj X))
      (isColimitOfPreserves (PresheafOfModules.evaluation _ X) hc)⟩⟩⟩

end Stacks

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules gives it back: the
counit of the sheafification adjunction is an isomorphism. -/
noncomputable def forgetCompModuleSheafifyIso :
    SheafOfModules.forget (toRingCat J Osharp) ⋙ moduleSheafify.{t, m} (Osharp := Osharp) ≅
      𝟭 _ := by
  have e := asIso ((PresheafOfModules.sheafificationAdjunction
    (R := toRingCat J Osharp) (𝟙 (toRingCat J Osharp).obj)).counit)
  exact e

variable (G : PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat))

/-- A colimit cocone of sheaves of modules stays a colimit cocone after tensoring objectwise
with a fixed presheaf of modules and sheafifying. -/
noncomputable def isColimitSheafTensorRightPreMapCocone {D : Type s} [Category.{s'} D]
    {K : D ⥤ SheafOfModules.{m} (toRingCat J Osharp)}
    [HasColimitsOfShape D (PresheafOfModules.{m} (toRingCat J Osharp).obj)]
    [PreservesColimitsOfShape D (Stacks.tensorRight.{v, u, t, m, m} G)]
    (c : Cocone K) (hc : IsColimit c) :
    IsColimit ((sheafTensorRightPre G).mapCocone c) := by
  have hP : IsColimit (colimit.cocone (K ⋙ SheafOfModules.forget _)) := colimit.isColimit _
  haveI : PreservesColimitsOfShape D
      (SheafOfModules.forget (toRingCat J Osharp) ⋙ moduleSheafify.{t, m} (Osharp := Osharp)) :=
    preservesColimitsOfShape_of_natIso (forgetCompModuleSheafifyIso (Osharp := Osharp)).symm
  haveI hu : IsIso (moduleSheafify.{t, m} (Osharp := Osharp).map
      (hP.desc ((SheafOfModules.forget (toRingCat J Osharp)).mapCocone c))) :=
    Stacks.isIso_map_desc hP _ (isColimitOfPreserves
      (SheafOfModules.forget (toRingCat J Osharp) ⋙ moduleSheafify) hc)
  have hW := Stacks.W_toPresheaf_map_of_isIso (O := Osharp.obj) (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj) _ hu
  haveI := hW.isLocallyInjective
  haveI := hW.isLocallySurjective
  exact Stacks.isColimitMapCocone hP (Stacks.tensorRight.{v, u, t, m, m} G ⋙ moduleSheafify)
    ((SheafOfModules.forget (toRingCat J Osharp)).mapCocone c)
    (Stacks.isIso_sheafification_map_tensorRight_map (O := Osharp.obj)
      (R := toRingCat J Osharp) (N := G) (𝟙 (toRingCat J Osharp).obj) _)

/-- **The associated sheaf of the objectwise tensor product with a fixed presheaf of modules
commutes with the colimits of sheaves of modules in its first variable.** -/
instance preservesColimitsOfSize_sheafTensorRightPre :
    PreservesColimitsOfSize.{m, m} (sheafTensorRightPre G) where
  preservesColimitsOfShape := by
    intro D _
    have : PreservesColimitsOfShape D (Stacks.tensorRight.{v, u, t, m, m} G) :=
      (Stacks.preservesColimitsOfSize_tensorRight_endo.{v, u, t, m}
        (O := Osharp.obj) G).preservesColimitsOfShape
    exact ⟨⟨fun hc ↦ ⟨isColimitSheafTensorRightPreMapCocone G _ hc⟩⟩⟩

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- **Degree `n` of the relative tensor product `- ⊗_A N` commutes with the colimits of right
graded `A`-modules.** -/
theorem preservesColimitsOfSize_gradedTensorDegree_of_sheafify
    (N : LeftGradedModule.{t, m, m} A) (n : ℤ) :
    PreservesColimitsOfSize.{m, m} (gradedTensorDegree N n) :=
  preservesColimitsOfSize_gradedTensorDegree N n

end RelativeTensor

end SheafOfModules
