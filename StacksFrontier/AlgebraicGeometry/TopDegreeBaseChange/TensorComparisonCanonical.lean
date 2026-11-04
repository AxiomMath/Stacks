module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonScalar

/-!
# The canonical tensor map of [Stacks, Tag 0EX3] (b), over an arbitrary base

`TensorComparison.lean` states the canonicity condition
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap` that conclusion (b) of
[Stacks, Tag 0EX3] asks of a map

`R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`,

and proves that at most one map satisfies it.  This file builds that map, for an **arbitrary**
morphism of schemes, arbitrary sheaves of modules and an arbitrary degree, and proves that it
satisfies the condition.  Nothing is assumed of the base: it is not affine, and the construction
is not local on it.

By the sheafification adjunction of [Stacks, Tag 01CB] a map out of the tensor sheaf is a bilinear
family on sections, so what is produced is, over every open `U` of `Y`, a biadditive and bilinear

`Γ(R^n f_* F, U) × Γ(G, U) ⟶ Γ(R^n f_*(F ⊗ f^* G), U)`,

compatible with shrinking `U`.  Its value is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorTopSection`, and its five fields are the
results of the files this one rests on: additivity and linearity in the section of `R^n f_* F`
(`tensorTopSection_add` and `topReading_smul`), additivity in the section of `G`
(`higherDirectImageTensorSection_add`, through `tensorTopSection_add_section`), linearity in the
section of `G` (`tensorTopSection_smul`) and compatibility with shrinking the open
(`tensorTopSection_presheaf_map`).

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorPresheafMap`: the bilinear
  family, as a morphism out of the objectwise tensor product of the two presheaves of modules.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorMap`: **the canonical map
  `R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`**, over an arbitrary base.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorTopSection_add_section`: the candidate value on sections is additive in the section
  of `G`.
* `higherDirectImageTensorMap_tmul`: **the canonical map on a local pure tensor is the candidate
  value on sections**, which is what pins the map down.
* `isHigherDirectImageTensorMap_higherDirectImageTensorMap`: **the canonical map satisfies the
  canonicity condition of [Stacks, Tag 0EX3] (b)**, so by `eq_of_isHigherDirectImageTensorMap`
  it is the unique map that does.
* `topDirectImageTensorComparisonOfIsIso'`: conclusion (b) from invertibility of this map alone,
  the canonicity condition being discharged.

## Implementation notes

The bilinear family is given to `PresheafOfModules.tensorMk`, whose five hypotheses are plain
functions and equations between *sections*, rather than to `PresheafOfModules.ofBilinear` through
a `Stacks.BilinearMap`.  The difference is not cosmetic: a `Stacks.BilinearMap` packages the
family as an iterated `AddMonoidHom`, so its `app` field has to be built by proving two
*equalities of `AddMonoidHom`s*, and each of those is reported as `maximum recursion depth has
been reached` — the additive structure of the sections of a right-derived-functor object is not
reached by instance search within the depth available.  `tensorMk` never forms that structure.

For the same reason the pure-tensor computation rule is read off `PresheafOfModules.tensorMk_tmul`
in its own declaration (`higherDirectImageTensorPresheafMap_tmul`) rather than by definitional
unfolding at the point of use: the unfolding is available but too deep.

Every statement is in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling of a
restriction, and `topReading` was retyped into it for this purpose: a declaration that pairs two
spellings of one right-derived-functor object more than once exceeds the kernel's budget, and the
applications below would pair three.

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

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)

/-! ### The bilinear family -/

/-- **The candidate value on sections is additive in the section of `G`.** -/
theorem tensorTopSection_add_section (U : Y.Opens) (s s' : Γ(G, U))
    (a : Γ(topDirectImage f F n, U)) :
    tensorTopSection f F G n U (s + s') a =
      tensorTopSection f F G n U s a + tensorTopSection f F G n U s' a :=
  topReading_add_hom_of_eq U _ _ _ (higherDirectImageTensorSection_add f F G n U s s') a

/-- **The bilinear family of conclusion (b) of [Stacks, Tag 0EX3], as a morphism out of the
objectwise tensor product of the two presheaves of modules.**  Its five hypotheses are the
biadditivity, the bilinearity and the compatibility with shrinking the open of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorTopSection`. -/
def higherDirectImageTensorPresheafMap :
    PresheafOfModules.tensorObj (topDirectImage f F n).val G.val ⟶
      (topDirectImageTensor f F G n).val :=
  PresheafOfModules.tensorMk
    (fun W a s => tensorTopSection f F G n W.unop s a)
    (fun W a a' s => tensorTopSection_add f F G n W.unop s a a')
    (fun W r a s => topReading_smul W.unop _ r a)
    (fun W a s s' => tensorTopSection_add_section f F G n W.unop s s' a)
    (fun W r a s => tensorTopSection_smul f W.unop F G n r s a)
    (fun {W W'} i a s => by
      have h := tensorTopSection_presheaf_map f F n (leOfHom i.unop) G s a
      rw [Subsingleton.elim (homOfLE (leOfHom i.unop)) i.unop] at h
      exact h)

/-- The presheaf-level bilinear family on a pure tensor of sections. -/
theorem higherDirectImageTensorPresheafMap_tmul (W : Y.Opens)
    (a : Γ(topDirectImage f F n, W)) (t : Γ(G, W)) :
    PresheafOfModules.Hom.app (higherDirectImageTensorPresheafMap f F G n) (op W)
        (a ⊗ₜ[Y.presheaf.obj (op W)] t) =
      tensorTopSection f F G n W t a :=
  PresheafOfModules.tensorMk_tmul _ _ _ _ _ _ (op W) a t

/-- **The canonical map `R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)` of conclusion (b) of
[Stacks, Tag 0EX3]**, for an arbitrary morphism of schemes, arbitrary sheaves of modules and an
arbitrary degree: the bilinear family on sections, through the sheafification adjunction of
[Stacks, Tag 01CB]. -/
def higherDirectImageTensorMap :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).obj G) ⟶
      topDirectImageTensor f F G n :=
  ((PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing Y.toRingedSpace)
      (𝟙 (structureSheafRing Y.toRingedSpace).obj)).homEquiv
    ((PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) (topDirectImage f F n).val G.val))
    (topDirectImageTensor f F G n)).symm (higherDirectImageTensorPresheafMap f F G n)

/-- **The canonical map agrees with the presheaf-level bilinear family on the image of the
sheafification unit.** -/
theorem higherDirectImageTensorMap_toTensorSheafSection (W : (Y.Opens)ᵒᵖ)
    (t : TensorProduct (Y.presheaf.obj W) ((topDirectImage f F n).val.obj W) (G.val.obj W)) :
    ((higherDirectImageTensorMap f F G n).val.app W).hom
        (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) G W t) =
      PresheafOfModules.Hom.app (higherDirectImageTensorPresheafMap f F G n) W t :=
  congrArg (fun q => PresheafOfModules.Hom.app q W t)
    (((PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing Y.toRingedSpace)
      (𝟙 (structureSheafRing Y.toRingedSpace).obj)).homEquiv
      ((PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf)
        (topDirectImage f F n).val G.val))
      (topDirectImageTensor f F G n)).apply_symm_apply
        (higherDirectImageTensorPresheafMap f F G n))

/-- **The canonical map on a local pure tensor is the candidate value on sections.**  This is the
computation rule of the sheafification adjunction at the bilinear family, and it is what pins the
map down. -/
theorem higherDirectImageTensorMap_tmul (W : Y.Opens)
    (a : Γ(topDirectImage f F n, W)) (t : Γ(G, W)) :
    Scheme.Modules.Hom.app (higherDirectImageTensorMap f F G n) W
        (toTensorSheafSection Y.toRingedSpace (topDirectImage f F n) G (op W)
          (a ⊗ₜ[Y.presheaf.obj (op W)] t)) =
      tensorTopSection f F G n W t a :=
  (higherDirectImageTensorMap_toTensorSheafSection f F G n (op W)
      (a ⊗ₜ[Y.presheaf.obj (op W)] t)).trans
    (higherDirectImageTensorPresheafMap_tmul f F G n W a t)

/-! ### The canonicity condition -/

/-- **The canonical map satisfies the canonicity condition of [Stacks, Tag 0EX3] (b).**  Over
every open `V` of `Y` and for every section `s` of `G` over `V`, composing with the restriction of
the map carries the local pure tensor `x ⊗ s` to the higher direct image of `t ↦ t ⊗ f^* s`.

With `eq_of_isHigherDirectImageTensorMap` this says that `higherDirectImageTensorMap` is **the**
map conclusion (b) is about: no hypothesis on `f`, on the modules, on the degree or on the
base. -/
theorem isHigherDirectImageTensorMap_higherDirectImageTensorMap :
    IsHigherDirectImageTensorMap f F G n (higherDirectImageTensorMap f F G n) := by
  intro V s
  refine Scheme.Modules.hom_ext _ _ fun S => ?_
  have hL : ∀ a : Γ(topDirectImage f F n, V.ι ''ᵁ S),
      (tensorLocalSection Y (topDirectImage f F n) G V s ≫
            (Scheme.Modules.restrictFunctor V.ι).map
              (higherDirectImageTensorMap f F G n)).app S a =
        tensorTopSection f F G n (V.ι ''ᵁ S)
          (G.presheaf.map (homOfLE (V.ι_image_le S)).op s) a := fun a =>
    higherDirectImageTensorMap_tmul f F G n (V.ι ''ᵁ S) a
      (G.presheaf.map (homOfLE (V.ι_image_le S)).op s)
  have hR : ∀ a : Γ(topDirectImage f F n, V.ι ''ᵁ S),
      topReading (V.ι ''ᵁ S)
          (higherDirectImageTensorSection f F G n (V.ι ''ᵁ S)
            (G.presheaf.map (homOfLE (V.ι_image_le S)).op s)) a =
        (higherDirectImageTensorSection f F G n V s).app S a := fun a => by
    rw [topReading_eq_imageSections,
      ← higherDirectImageTensorSection_restrictHomOfLE f F n (V.ι_image_le S) G s,
      ModuleLimits.imageSections_restrictHomOfLE (V.ι_image_le S)
        (higherDirectImageTensorSection f F G n V s) (V.ι ''ᵁ S).ι_image_top
        (ModuleLimits.image_preimage_of_le (V.ι_image_le S)),
      ModuleLimits.imageSections_congr (higherDirectImageTensorSection f F G n V s)
        (ModuleLimits.image_preimage_of_le (V.ι_image_le S)) rfl,
      ModuleLimits.imageSections_rfl_app]
  ext a
  exact (hL a).trans (hR a)

/-- **Conclusion (b) of [Stacks, Tag 0EX3] from invertibility of the canonical map alone.**  The
canonicity condition is discharged by
`isHigherDirectImageTensorMap_higherDirectImageTensorMap`, so what remains of the conclusion is
the invertibility of one named morphism. -/
def topDirectImageTensorComparisonOfIsIso' [IsIso (higherDirectImageTensorMap f F G n)] :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
            ((Scheme.Modules.pullback f).obj G))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).obj G) //
      IsHigherDirectImageTensorMap f F G n e.inv } :=
  topDirectImageTensorComparisonOfIsIso f F G n (higherDirectImageTensorMap f F G n)
    (isHigherDirectImageTensorMap_higherDirectImageTensorMap f F G n)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
