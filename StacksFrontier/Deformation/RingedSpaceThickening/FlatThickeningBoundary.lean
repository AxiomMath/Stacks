module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatModuleDeformation
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatThickeningSituation
public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningComplexBoundary
import StacksCore.Tactic.StacksAttribute

/-!
# The boundary of the difference of two flat lifts (Stacks 08VT)

In the situation of **Stacks 08VS** the two `𝒪'₁`-modules `π^* ℱ` and `h^* ℱ'₂` are flat over
`S'₁` and restrict to `ℱ` on `X`, so **Stacks 08VR** clause (2) attaches to them a difference
`θ ∈ Ext¹_{𝒪_X}(ℱ, f^* 𝒥₁ ⊗_{𝒪_X} ℱ)`. **Stacks 08VT** says that the boundary of `θ` in
`Ext²_{𝒪_X}(ℱ, f^* 𝒥₃ ⊗_{𝒪_X} ℱ)` is the obstruction of **Stacks 08VR** clause (1) to lifting
`ℱ` to an `𝒪'₃`-module flat over `S'₃`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FlatShortExactThickeningDiagram.morphism₁`,
  `.morphism₂`, `.morphism₃`: the three vertical squares of the situation, read as morphisms of
  thickenings in the sense of **Stacks 08KZ**.
* `AlgebraicGeometry.RingedSpaceThickening.FlatShortExactThickeningDiagram.trivialization`: the
  canonical splitting `π : X'₁ ⟶ X` of **Stacks 08LE**, which the upper row determines.
* `AlgebraicGeometry.RingedSpaceThickening.FlatShortExactThickeningDiagram.liftOfModule₂`: the
  module `ℱ'₂` read as a flat lift of `ℱ` across the middle square.
* `FlatShortExactThickeningDiagram.idealTensorTransition₂₁` and `.idealTensorTransition₃₂`: the
  transition maps of the coefficient modules `ℐᵢ ⊗_{𝒪_X} ℱ`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference_eq_sub_underlyingExtensionClass`:
  across a trivialized thickening the difference of **Stacks 08LM** is the difference of the
  classes `ξ` of **Stacks 08LB** of the kernel extensions of the two lifts.
* `boundary_flatLiftClassDifferenceBase_eq_flatDeformationObstruction`, in the same namespace:
  **Stacks 08VT**.

## Implementation notes

The difference `θ` is `FlatModuleDeformation.flatLiftClassDifferenceBase` of **Stacks 08VR**
clause (2) and the obstruction is `FlatModuleDeformation.flatDeformationObstruction` of
**Stacks 08VR** clause (1). The boundary is Yoneda composition with the class of the short exact
sequence `0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0`, as in **Stacks 08LF**
(`boundary_underlyingExtensionClass`).

Two reductions turn 08VT into 08LF. First, the source's sequence of coefficient modules is
transported to the canonical sequence of the modules `ℐᵢ ⊗_{𝒪_X} ℱ` with `cᵢ = 1`, the
normalization in which both classes of **Stacks 08VR** are defined, through the identifications
`ℐᵢ = f^* 𝒥ᵢ`; the boundary maps then agree by naturality of the class of a short exact
sequence. Second, the difference `θ` is identified with the class `ξ` of the kernel extension of
`h^* ℱ'₂`, because `ξ` and the descent along `i₁` through which **Stacks 08LM** defines the
difference are mutually inverse — `splitRestrictionExtHom_extClass_map` — and because the class
of `π^* ℱ`, whose kernel extension is split by `π`, vanishes.

## Scope

The hypotheses of
`boundary_flatLiftClassDifferenceBase_eq_flatDeformationObstruction` carry inputs of the
source, each named on the attribute. The short
exactness of the sequence of coefficient modules is the source's own second step, which it
deduces from the hypotheses of **Stacks 08VS** together with flatness of `ℱ` over `S`. The two
lifts are identified by the only properties of them that the argument uses: that the class of
the first vanishes, which is what the splitting `π` gives for `π^* ℱ`, and that the kernel
extension of the second is the one **Stacks 08LC** produces from `ℱ'₂`, which is what `h^* ℱ'₂`
is. The hypothesis `hrestrict` is the one that **Stacks 08LF** itself carries.

## References

* [Stacks Project, Tag 08VT](https://stacks.math.columbia.edu/tag/08VT)
* [Stacks Project, Tag 08VS](https://stacks.math.columbia.edu/tag/08VS)
* [Stacks Project, Tag 08VR](https://stacks.math.columbia.edu/tag/08VR)
* [Stacks Project, Tag 08LF](https://stacks.math.columbia.edu/tag/08LF)
* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.RingedSpaceThickening.FlatModuleDeformation
open Stacks.Thickenings

universe u w w'

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The difference of two flat lifts as a difference of classes `ξ` -/

/-- **The difference of two flat lifts is the difference of the classes of their kernel
extensions.** Across a trivialized first order thickening the difference of **Stacks 08LM** of
two flat lifts is `ξ_{ℱ'_A} - ξ_{ℱ'_B}`, for the classes `ξ` of **Stacks 08LB** attached to
their kernel extensions by the trivialization. -/
theorem flatLiftDifference_eq_sub_underlyingExtensionClass {D : MorphismOfThickenings.{u}}
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X'))]
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict) (π : SplitMono D.i)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    flatLiftDifference hi hs A B =
      underlyingExtensionClass D.i π hi.1.1 F (idealTensor D F) (A.kernelExtension hi hs) -
        underlyingExtensionClass D.i π hi.1.1 F (idealTensor D F)
          (B.kernelExtension hi hs) := by
  have hfull : (modulePushforward D.i).Full :=
    (closedQuotientOfIsThickening D.i D.i_isThickening).full_modulePushforward
  have hfaith : (modulePushforward D.i).Faithful :=
    (closedQuotientOfIsThickening D.i D.i_isThickening).faithful_modulePushforward
  have hlim : Limits.PreservesFiniteLimits (modulePushforward D.i) :=
    preservesFiniteLimits_modulePushforward D.i
  have hcolim : Limits.PreservesFiniteColimits (modulePushforward D.i) :=
    preservesFiniteColimits_modulePushforward D.i D.i_isThickening
  obtain ⟨P⟩ := exists_differencePresentation.{u, w} hi hs A B
  have h := P.mapExactFunctor_differenceClass
  rw [A.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extA
      (A.isKernelExtension_kernelExtension hi hs),
    B.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extB
      (B.isKernelExtension_kernelExtension hi hs)] at h
  rw [flatLiftDifference_eq hi hs P]
  simp only [underlyingExtensionClass_eq_splitRestrictionExtHom D.i π hi.1.1 F (idealTensor D F)]
  rw [← map_sub, ← h, DifferencePresentation.differenceClass,
    CategoryTheory.Abelian.Ext.mapExactFunctor_extClass,
    splitRestrictionExtHom_extClass_map]

/-! ### The three squares of the situation of Stacks 08VS -/

namespace FlatShortExactThickeningDiagram

variable (D : FlatShortExactThickeningDiagram.{u})

/-- The left vertical square `(f, f'₁)` of the situation, as a morphism of thickenings. -/
abbrev morphism₁ : MorphismOfThickenings.{u} where
  X := D.upper.X
  X' := D.upper.X₁
  S := D.lower.X
  S' := D.lower.X₁
  i := D.upper.i₁
  t := D.lower.i₁
  f := D.f
  f' := D.f₁
  i_isThickening := D.upper.firstOrder₁.1
  t_isThickening := D.lower.firstOrder₁.1
  comm := D.restrict₁

/-- The middle vertical square `(f, f'₂)` of the situation, as a morphism of thickenings. -/
abbrev morphism₂ : MorphismOfThickenings.{u} where
  X := D.upper.X
  X' := D.upper.X₂
  S := D.lower.X
  S' := D.lower.X₂
  i := D.upper.i₂
  t := D.lower.i₂
  f := D.f
  f' := D.f₂
  i_isThickening := D.upper.firstOrder₂.1
  t_isThickening := D.lower.firstOrder₂.1
  comm := D.restrict₂

/-- The right vertical square `(f, f'₃)` of the situation, as a morphism of thickenings. -/
abbrev morphism₃ : MorphismOfThickenings.{u} where
  X := D.upper.X
  X' := D.upper.X₃
  S := D.lower.X
  S' := D.lower.X₃
  i := D.upper.i₃
  t := D.lower.i₃
  f := D.f
  f' := D.f₃
  i_isThickening := D.upper.firstOrder₃.1
  t_isThickening := D.lower.firstOrder₃.1
  comm := D.restrict₃

/-- The left square is strict. -/
theorem isStrict₁ : D.morphism₁.IsStrict := D.strict₁

/-- The middle square is strict. -/
theorem isStrict₂ : D.morphism₂.IsStrict := D.strict₂

/-- The right square is strict. -/
theorem isStrict₃ : D.morphism₃.IsStrict := D.strict₃

/-- The upper row is a complex of first order thickenings: short exactness of its ideal
sequence contains the vanishing of the composite. -/
theorem isComplex_upper : IsComplex D.upper :=
  ⟨D.upper_exact.1, D.upper_exact.2.elim fun h _ => h⟩

/-- The canonical splitting `π : X'₁ ⟶ X` of **Stacks 08LE**, determined by the upper row. -/
noncomputable def trivialization : SplitMono D.upper.i₁ where
  retraction :=
    (D.upper.existsUnique_trivialization_of_isComplex D.isComplex_upper).choose
  id := (D.upper.existsUnique_trivialization_of_isComplex D.isComplex_upper).choose_spec.1.1

/-- The canonical splitting satisfies the compatibility `π ≫ i₃ = f₁₂ ≫ f₂₃` of
**Stacks 08LE**. -/
theorem trivialization_retraction_comp :
    D.trivialization.retraction ≫ D.upper.i₃ = D.upper.f₁₂ ≫ D.upper.f₂₃ :=
  (D.upper.existsUnique_trivialization_of_isComplex D.isComplex_upper).choose_spec.1.2

/-- The module `ℱ'₂` of the situation, read as a flat lift of `ℱ = ℱ'₂|_X` across the middle
vertical square. -/
noncomputable def liftOfModule₂ : FlatLift D.morphism₂ D.restriction where
  module' := D.module₂
  flat := D.module₂_flat
  identification := Iso.refl _

-- Reconciling the `.obj`-applied spelling of the coefficient modules with the uncurried
-- spelling of the map needs `Functor.uncurry` to unfold, but not the tensor product itself;
-- leaving `Stacks.SheafOfModules.Tensor.sheafTensor` folded for these two declarations is what
-- keeps the unifier from grinding through its four-fold functor composition.
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The transition map `ℐ₂ ⊗_{𝒪_X} ℱ ⟶ ℐ₁ ⊗_{𝒪_X} ℱ` of the coefficient modules, induced by
`f₁₂ : X'₁ ⟶ X'₂`. -/
noncomputable def idealTensorTransition₂₁ :
    idealTensor D.morphism₂ D.restriction ⟶ idealTensor D.morphism₁ D.restriction :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((D.upper.X)).presheaf,
      ((D.upper.X)).IsSheaf⟩)).map
      (((thickeningIdealMap D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂), (𝟙 D.restriction)) :
      (_, _) ⟶ (_, _)))

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The transition map `ℐ₃ ⊗_{𝒪_X} ℱ ⟶ ℐ₂ ⊗_{𝒪_X} ℱ` of the coefficient modules, induced by
`f₂₃ : X'₂ ⟶ X'₃`. -/
noncomputable def idealTensorTransition₃₂ :
    idealTensor D.morphism₃ D.restriction ⟶ idealTensor D.morphism₂ D.restriction :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((D.upper.X)).presheaf,
      ((D.upper.X)).IsSheaf⟩)).map
      (((thickeningIdealMap D.upper.i₂ D.upper.i₃ D.upper.f₂₃ D.upper.comm₂₃), (𝟙 D.restriction)) :
      (_, _) ⟶ (_, _)))

end FlatShortExactThickeningDiagram


/-! ### Stacks 08VT -/

/-- In the situation of **Stacks 08VS** the two `𝒪'₁`-modules
`π^* ℱ` and `h^* ℱ'₂` are flat over `S'₁` and restrict to `ℱ` on `X`, so **Stacks 08VR**
clause (2) attaches to them a difference `θ ∈ Ext¹_{𝒪_X}(ℱ, f^* 𝒥₁ ⊗_{𝒪_X} ℱ)`. The boundary of
`θ` along `0 ⟶ f^* 𝒥₃ ⊗ ℱ ⟶ f^* 𝒥₂ ⊗ ℱ ⟶ f^* 𝒥₁ ⊗ ℱ ⟶ 0` is the obstruction of **Stacks 08VR**
clause (1) to lifting `ℱ` to an `𝒪'₃`-module flat over `S'₃`.

The difference is taken in the order `(h^* ℱ'₂, π^* ℱ)`; the other order negates both it and its
boundary. The hypotheses carrying inputs of the source are described in the Scope section of the
module docstring. -/
@[stacks 08VT "the boundary of the difference of `π^* ℱ` and `h^* ℱ'₂` is the obstruction to \
lifting `ℱ` to an `𝒪'₃`-module flat over `S'₃`, difference in the order `(h^* ℱ'₂, π^* ℱ)`; \
inputs of the source are hypotheses -- the 08VQ identifications `ℐᵢ = f^* 𝒥ᵢ`, as 08VR already \
carries them, the short exactness of the tensored ideal sequence, and 08LF's own `hrestrict` -- \
each named in the Scope section of the module docstring"]
theorem boundary_flatLiftClassDifferenceBase_eq_flatDeformationObstruction
    (D : FlatShortExactThickeningDiagram.{u})
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.upper.X))]
    [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.upper.X₁))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing D.upper.X))]
    (hI₁ : IsIso D.morphism₁.baseToSourceIdeal)
    (hI₂ : IsIso D.morphism₂.baseToSourceIdeal)
    (hI₃ : IsIso D.morphism₃.baseToSourceIdeal)
    (k₃₂ : baseIdealTensor D.morphism₃ D.restriction ⟶
      baseIdealTensor D.morphism₂ D.restriction)
    (k₂₁ : baseIdealTensor D.morphism₂ D.restriction ⟶
      baseIdealTensor D.morphism₁ D.restriction)
    (hk : k₃₂ ≫ k₂₁ = 0) (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (hk₃₂ : (baseIdealTensorIso D.morphism₃ hI₃ D.restriction).inv ≫ k₃₂ =
      D.idealTensorTransition₃₂ ≫ (baseIdealTensorIso D.morphism₂ hI₂ D.restriction).inv)
    (hk₂₁ : (baseIdealTensorIso D.morphism₂ hI₂ D.restriction).inv ≫ k₂₁ =
      D.idealTensorTransition₂₁ ≫ (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).inv)
    (Aπ Bh : FlatLift D.morphism₁ D.restriction)
    (hAπ : underlyingExtensionClass D.upper.i₁ D.trivialization D.upper.firstOrder₁.1.1
      D.restriction (idealTensor D.morphism₁ D.restriction)
      (Aπ.kernelExtension D.upper.firstOrder₁ D.isStrict₁) = 0)
    (w : PushedExtension D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂ D.restriction
      (idealTensor D.morphism₁ D.restriction) (idealTensor D.morphism₂ D.restriction)
      D.idealTensorTransition₂₁
      (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂)
      (Bh.kernelExtension D.upper.firstOrder₁ D.isStrict₁))
    (hw : IsPushout (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂).f
      ((modulePushforward D.upper.i₂).map D.idealTensorTransition₂₁ ≫
        (thickeningPushforwardComp D.upper.i₁ D.upper.i₂ D.upper.f₁₂ D.upper.comm₁₂).inv.app
          (idealTensor D.morphism₁ D.restriction))
      w.hom ((modulePushforward D.upper.f₁₂).map
        (Bh.kernelExtension D.upper.firstOrder₁ D.isStrict₁).f))
    (hrestrict : (firstOrderExtensionAction D.upper.i₃ D.restriction
        (idealTensor D.morphism₂ D.restriction) D.upper.firstOrder₃
        (sequenceRestrictedExtension D.upper D.restriction
          (idealTensor D.morphism₂ D.restriction)
          (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂))).val =
      D.idealTensorTransition₃₂) :
    (flatLiftClassDifferenceBase D.morphism₁ D.upper.firstOrder₁ D.isStrict₁ hI₁ D.restriction
          (Quotient.mk (flatLiftSetoid D.morphism₁ D.restriction) Bh)
          (Quotient.mk (flatLiftSetoid D.morphism₁ D.restriction) Aπ)).comp
        hK.extClass (by decide) =
      flatDeformationObstruction D.morphism₃ D.upper.firstOrder₃ hI₃ D.restriction := by
  have hκ : D.idealTensorTransition₃₂ ≫ D.idealTensorTransition₂₁ = 0 := by
    have h1 : (D.idealTensorTransition₃₂ ≫ D.idealTensorTransition₂₁) ≫
        (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).inv = 0 := by
      rw [Category.assoc, ← hk₂₁, ← Category.assoc, ← hk₃₂, Category.assoc, hk, comp_zero]
    have h2 := congrArg
      (fun z => z ≫ (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).hom) h1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using h2
  have hKideal : (ShortComplex.mk D.idealTensorTransition₃₂
      D.idealTensorTransition₂₁ hκ).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (baseIdealTensorIso D.morphism₃ hI₃ D.restriction).symm
        (baseIdealTensorIso D.morphism₂ hI₂ D.restriction).symm
        (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).symm hk₃₂ hk₂₁).symm hK
  have hnat : hKideal.extClass.comp (CategoryTheory.Abelian.Ext.mk₀
        (baseIdealTensorIso D.morphism₃ hI₃ D.restriction).inv) (add_zero 1) =
      (CategoryTheory.Abelian.Ext.mk₀
          (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).inv).comp
        hK.extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality hKideal hK
      { τ₁ := (baseIdealTensorIso D.morphism₃ hI₃ D.restriction).inv
        τ₂ := (baseIdealTensorIso D.morphism₂ hI₂ D.restriction).inv
        τ₃ := (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).inv
        comm₁₂ := hk₃₂
        comm₂₃ := hk₂₁ }
  have h08LF := boundary_underlyingExtensionClass D.upper D.isComplex_upper D.trivialization
    D.trivialization_retraction_comp D.restriction
    (idealTensor D.morphism₁ D.restriction) (idealTensor D.morphism₂ D.restriction)
    (idealTensor D.morphism₃ D.restriction)
    D.idealTensorTransition₃₂ D.idealTensorTransition₂₁ hκ hKideal
    (𝟙 (idealTensor D.morphism₁ D.restriction))
    (𝟙 (idealTensor D.morphism₂ D.restriction))
    (𝟙 (idealTensor D.morphism₃ D.restriction))
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (D.liftOfModule₂.kernelExtension D.upper.firstOrder₂ D.isStrict₂)
    (D.liftOfModule₂.kernelExtension_action D.upper.firstOrder₂ D.isStrict₂)
    (Bh.kernelExtension D.upper.firstOrder₁ D.isStrict₁)
    (Bh.kernelExtension_action D.upper.firstOrder₁ D.isStrict₁)
    w hw (hrestrict.trans (Category.comp_id _).symm)
  have hθ : flatLiftDifference D.upper.firstOrder₁ D.isStrict₁ Bh Aπ =
      underlyingExtensionClass D.upper.i₁ D.trivialization D.upper.firstOrder₁.1.1
        D.restriction (idealTensor D.morphism₁ D.restriction)
        (Bh.kernelExtension D.upper.firstOrder₁ D.isStrict₁) := by
    rw [flatLiftDifference_eq_sub_underlyingExtensionClass D.upper.firstOrder₁ D.isStrict₁
      D.trivialization Bh Aπ, hAπ, sub_zero]
  have key : ((flatLiftDifference D.upper.firstOrder₁ D.isStrict₁ Bh Aπ).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (baseIdealTensorIso D.morphism₁ hI₁ D.restriction).inv)
          (add_zero 1)).comp hK.extClass (by decide) =
      (obstructionClass D.upper.i₃ D.upper.firstOrder₃ D.restriction
          (idealTensor D.morphism₃ D.restriction)
          (𝟙 (idealTensor D.morphism₃ D.restriction))).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (baseIdealTensorIso D.morphism₃ hI₃ D.restriction).inv)
        (add_zero 2) := by
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero, ← hnat,
      ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero, hθ, h08LF]
  exact key

end AlgebraicGeometry.RingedSpaceThickening

end
