module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonCanonical

/-!
# The canonical tensor map of [Stacks, Tag 0EX3] (b) is natural in the module on the base

`TensorComparisonCanonical.lean` builds the canonical map

`R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`

of conclusion (b) of [Stacks, Tag 0EX3] over an arbitrary base and proves it canonical.  This
file proves it natural in `G`.

Naturality in `G` is what the invertibility half of conclusion (b) consumes.  The source's proof
of (b) reduces to an affine base and there applies Eilenberg–Watts: a natural transformation out
of `A ⊗ -` is determined by its value at the base ring, because for `m` a section the
multiplication `r ↦ r • m` is a morphism of modules and naturality moves the comparison along it.
`Stacks.EilenbergWatts.map_tmul` is that description of the Eilenberg–Watts comparison, so
identifying it with the map of this directory is exactly a naturality statement plus the value at
the structure sheaf.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorLocalSection_naturality`: **tensoring with a local section is natural in the module the
  section lives in.**
* `conjugateRestrict_naturality`: the conjugated derived pushforward carries that naturality,
  for a variable module downstairs.
* `higherDirectImageTensorSection_naturality`: **the bilinear family is natural in `G`**, as an
  identity of morphisms of sheaves over an open.
* `tensorTopSection_naturality`: the same read on sections.
* `higherDirectImageTensorMap_naturality`: **the canonical map is natural in `G`.**

## Implementation notes

The discipline of this directory is kept: `conjugateRestrict_naturality` has the module
downstairs and both local morphisms as variables, so that no statement pairs the tensor product
with the restriction comparison, and every source and target is in the
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling.

The last statement is proved by `hom_ext_of_tensorSection`: the two sides are morphisms out of a
tensor sheaf, so they agree as soon as they agree on the local pure tensors, and there
`higherDirectImageTensorMap_tmul` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection` compute
them.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso
  rightDerivedPlusRestrictObjIso_hom_naturality)

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

/- The sheafification instance under the tensor product, as `TensorComparison.lean` and the
modules between it and this one resolve it.  Instance search here otherwise reaches
`CategoryTheory.sheafToPresheaf_isRightAdjoint` first, and two spellings of one tensor product
that differ in this instance are compared by the kernel only by evaluating the sheafification,
which exceeds its budget. -/
attribute [local instance high] CategoryTheory.instHasWeakSheafifyOfHasSheafify

/-! ### Tensoring with a local section is natural in the module -/

/-- **Tensoring with a local section is natural in the module the section lives in.**  For
`ψ : B ⟶ B'` the morphism `x ↦ x ⊗ t`, followed by `ψ` in the second factor, is `x ↦ x ⊗ ψ t`. -/
theorem tensorLocalSection_naturality {Z : Scheme.{u}} (A : Z.Modules) {B B' : Z.Modules}
    (ψ : B ⟶ B') (V : Z.Opens) (t : Γ(B, V)) :
    tensorLocalSection Z A B V t ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.toRingedSpace.presheaf,
            Z.toRingedSpace.IsSheaf⟩).obj A).map ψ)) =
      tensorLocalSection Z A B' V (ψ.app V t) := by
  refine Scheme.Modules.hom_ext _ _ fun S => ?_
  have key : ∀ x : Γ(A, V.ι ''ᵁ S),
      (tensorLocalSection Z A B V t ≫
            (Scheme.Modules.restrictFunctor V.ι).map
              ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.toRingedSpace.presheaf,
                Z.toRingedSpace.IsSheaf⟩).obj A).map ψ))).app S x =
        (tensorLocalSection Z A B' V (ψ.app V t)).app S x := fun x => by
    rw [← ModuleLimits.imageSections_rfl_app
        (tensorLocalSection Z A B' V (ψ.app V t)) S x,
      imageSections_tensorLocalSection A B' (ψ.app V t) rfl (V.ι_image_le S) x,
      ModuleLimits.Hom_app_presheaf_map ψ (V.ι_image_le S) t]
    show (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.toRingedSpace.presheaf,
        Z.toRingedSpace.IsSheaf⟩).obj A).map ψ)).val.app (op (V.ι ''ᵁ S))).hom
        (toTensorSheafSection Z.toRingedSpace A B (op (V.ι ''ᵁ S))
          (x ⊗ₜ[Z.presheaf.obj (op (V.ι ''ᵁ S))]
            B.presheaf.map (homOfLE (V.ι_image_le S)).op t)) = _
    exact sheafTensor_obj_map_toTensorSheafSection A ψ (op (V.ι ''ᵁ S)) x _
  ext x
  exact key x

/-! ### The conjugated derived pushforward carries that naturality -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ) (V : Y.Opens)

/-- **The degree-`n` right derived pushforward along `f ∣_ V`, conjugated by the restriction
comparison of [Stacks, Tag 01E5], is natural in the module downstairs.**  The two modules
downstairs and the two local morphisms are variables, so that the statement mentions no tensor
product; this is the discipline of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.conjugateRestrict_add`.  The local morphisms are
typed in the `_.restrict` spelling of the type of `tensorLocalSection`, as in
`conjugateRestrict_scalar`, so that at a tensor product this elaborates to the same term as
`higherDirectImageTensorSection_eq`. -/
theorem conjugateRestrict_naturality (H H' : X.Modules) (μ : H ⟶ H')
    (τ : Scheme.Modules.restrict F (f ⁻¹ᵁ V).ι ⟶ Scheme.Modules.restrict H (f ⁻¹ᵁ V).ι)
    (τ' : Scheme.Modules.restrict F (f ⁻¹ᵁ V).ι ⟶ Scheme.Modules.restrict H' (f ⁻¹ᵁ V).ι)
    (hτ : τ ≫ (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map μ = τ') :
    ((rightDerivedPlusRestrictObjIso f V n F).inv ≫
          ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ)).map τ ≫
            (rightDerivedPlusRestrictObjIso f V n H).hom) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map μ) =
      (rightDerivedPlusRestrictObjIso f V n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ)).map τ' ≫
          (rightDerivedPlusRestrictObjIso f V n H').hom := by
  rw [← hτ, Functor.map_comp]
  simp only [Category.assoc]
  rw [rightDerivedPlusRestrictObjIso_hom_naturality f V n μ]

/-! ### The bilinear family and the canonical map are natural in `G` -/

variable (G G' : Y.Modules)

/-- **The bilinear family of conclusion (b) of [Stacks, Tag 0EX3] is natural in `G`.** -/
theorem higherDirectImageTensorSection_naturality (ψ : G ⟶ G') (s : Γ(G, V)) :
    @CategoryStruct.comp _ _
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩).obj F).obj ((Scheme.Modules.pullback f).obj G))))
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩).obj F).obj ((Scheme.Modules.pullback f).obj G'))))
        (higherDirectImageTensorSection f F G n V s)
        ((Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩).obj F).map ((Scheme.Modules.pullback f).map ψ))))) =
      higherDirectImageTensorSection f F G' n V (ψ.app V s) := by
  rw [higherDirectImageTensorSection_eq f F G n V s,
    higherDirectImageTensorSection_eq f F G' n V (ψ.app V s)]
  refine conjugateRestrict_naturality f F n V _ _ _ _ _ ?_
  refine Eq.trans (tensorLocalSection_naturality F
    ((Scheme.Modules.pullback f).map ψ) (f ⁻¹ᵁ V) _) ?_
  refine congrArg (tensorLocalSection X F ((Scheme.Modules.pullback f).obj G') (f ⁻¹ᵁ V)) ?_
  exact ConcreteCategory.congr_hom
    (congrArg (fun α => Scheme.Modules.Hom.app α V)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality ψ)).symm s

/-- **The candidate value on sections is natural in `G`.** -/
theorem tensorTopSection_naturality (ψ : G ⟶ G') (s : Γ(G, V))
    (a : Γ(topDirectImage f F n, V)) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
            X.toRingedSpace.IsSheaf⟩).obj F).map ((Scheme.Modules.pullback f).map ψ)))).app V
        (tensorTopSection f F G n V s a) =
      tensorTopSection f F G' n V (ψ.app V s) a := by
  rw [tensorTopSection, tensorTopSection,
    ← higherDirectImageTensorSection_naturality f F n V G G' ψ s, topReading_comp,
    topReading_restrictFunctor_map]

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3] is natural in `G`.**  Two
morphisms out of a tensor sheaf which agree on the local pure tensors are equal, and there both
sides are the candidate value on sections. -/
theorem higherDirectImageTensorMap_naturality (ψ : G ⟶ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
      Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).map ψ) ≫
        higherDirectImageTensorMap f F G' n =
      higherDirectImageTensorMap f F G n ≫
        ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
            X.toRingedSpace.IsSheaf⟩).obj F).map ((Scheme.Modules.pullback f).map ψ))) := by
  refine hom_ext_of_tensorSection fun W a t => ?_
  show ((higherDirectImageTensorMap f F G' n).val.app W).hom
      ((((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).map ψ)).val.app W).hom
        (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) G W
          (a ⊗ₜ[Y.presheaf.obj W] t))) = _
  rw [sheafTensor_obj_map_toTensorSheafSection (topDirectImage f F n) ψ W a t]
  show Scheme.Modules.Hom.app (higherDirectImageTensorMap f F G' n) W.unop
      (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) G' (op W.unop)
        (a ⊗ₜ[Y.presheaf.obj (op W.unop)] (ψ.app W.unop t))) = _
  rw [higherDirectImageTensorMap_tmul f F G' n W.unop a (ψ.app W.unop t),
    ← tensorTopSection_naturality f F n W.unop G G' ψ t a,
    ← higherDirectImageTensorMap_tmul f F G n W.unop a t]
  rfl

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
