module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.OverSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.CategoryTheory.Comma.IsoComma

/-!
# Algebraic spaces of finite presentation over an object of the big fppf site

Let `X` be an object of the big fppf site of a scheme `S`. An *algebraic space of finite
presentation over `X`* is an algebraic space over `S` together with a morphism to the
representable presheaf of `X` which is of finite presentation in the sense of Stacks 03XP,
part (3). These form the full subcategory `FP_X` of the slice of presheaves on the big fppf site
of `S` over the representable presheaf of `X`.

A morphism `j : X ⟶ Y` of the site induces a base-change functor `FP_Y ⥤ FP_X`, given by the
fibre product of presheaves along the Yoneda image of `j`: fibre products of algebraic spaces
over `S` are algebraic spaces by Stacks 02X2, and finite presentation is stable under base
change by Stacks 03XR. Base change along an identity is isomorphic to the identity functor, base
change along a composite is isomorphic to the composite of the base changes, and a commuting
square of the site induces an isomorphism between the two iterated base changes along it.

For a commuting square with vertices `V`, `U`, `W`, `Z` the last isomorphism gives the
comparison functor from `FP_Z` to the `2`-fibre product `FP_U ×_{FP_V} FP_W`, taking an algebraic
space of finite presentation over `Z` to its two base changes together with the canonical
identification of their further base changes to `V`.

## Main definitions

* `AlgebraicGeometry.IsFinitePresentationSpaceOver`: the defining property of an object of the
  slice — an algebraic space over the base whose structural morphism is of finite presentation.
* `AlgebraicGeometry.FinitePresentationSpacesOver`: the category `FP_X`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.baseChange`: the base-change functor along a
  morphism of the site.
* `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeId` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeComp`: the unit and composition
  comparisons of base change.
* `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso`: the comparison
  isomorphism attached to a commuting square of the site.
* `AlgebraicGeometry.FinitePresentationSpacesOver.glueingFunctor`: the comparison functor into
  the `2`-fibre product attached to a commuting square of the site.

## Main results

* `AlgebraicGeometry.isFinitePresentationSpaceOver_pullback`: the fibre product of an algebraic
  space of finite presentation over `Y` along the Yoneda image of `j : X ⟶ Y` is an algebraic
  space of finite presentation over `X`.

## Implementation notes

The base is a single object of the site throughout and the ambient category is the single
presheaf category on the big fppf site of `S`; algebraicity and finite presentation of the
structural morphism are read there, and base change is `CategoryTheory.Over.pullback` of that
category. Consequently the coherence of base change is Mathlib's coherence for
`CategoryTheory.Over.pullback`, transported into the full subcategories along the fully faithful
inclusion by `CategoryTheory.Functor.fullyFaithfulCancelRight`; no comparison between presheaf
categories on different sites enters.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The category -/

/-- An object of the slice of presheaves on the big fppf site of `S` over the representable
presheaf of `X` is an *algebraic space of finite presentation over `X`* when its source is an
algebraic space over `S` and its structural morphism is of finite presentation. -/
abbrev IsFinitePresentationSpaceOver (X : BigFppfOver B S hS)
    (F : Over (yoneda.obj X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) : Prop :=
  IsAlgebraicSpace B S hS F.left ∧ Space.IsFinitePresentation B S hS F.hom

/-- The category `FP_X` of algebraic spaces of finite presentation over an object `X` of the big
fppf site of `S`: the full subcategory of the slice of presheaves over the representable presheaf
of `X` on the objects whose source is an algebraic space over `S` and whose structural morphism
is of finite presentation. -/
abbrev FinitePresentationSpacesOver (X : BigFppfOver B S hS) :=
  ObjectProperty.FullSubcategory (IsFinitePresentationSpaceOver B S hS X)

/-! ### Base change -/

/-- The fibre product of an algebraic space of finite presentation over `Y` along the Yoneda
image of a morphism `j : X ⟶ Y` of the big fppf site of `S` is an algebraic space of finite
presentation over `X`: algebraicity is Stacks 02X2 and finite presentation is Stacks 03XR. -/
theorem isFinitePresentationSpaceOver_pullback {X Y : BigFppfOver B S hS} (j : X ⟶ Y)
    {F : Over (yoneda.obj Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hF : IsFinitePresentationSpaceOver B S hS Y F) :
    IsFinitePresentationSpaceOver B S hS X ((Over.pullback (yoneda.map j)).obj F) := by
  refine ⟨isAlgebraicSpace_pullback B S hS F.hom (yoneda.map j) hF.1
    (isAlgebraicSpace_yoneda B S hS X) (isAlgebraicSpace_yoneda B S hS Y), ?_⟩
  exact (Space.isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk F.hom :
        (⟨F.left, hF.1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩)
      (ObjectProperty.homMk (yoneda.map j) :
        (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩)) hF.2

namespace FinitePresentationSpacesOver

/-- Base change along a morphism `j : X ⟶ Y` of the big fppf site of `S`, as a functor from the
algebraic spaces of finite presentation over `Y` to those over `X`. On objects it is the fibre
product of presheaves along the Yoneda image of `j`. -/
noncomputable def baseChange {X Y : BigFppfOver B S hS} (j : X ⟶ Y) :
    FinitePresentationSpacesOver B S hS Y ⥤ FinitePresentationSpacesOver B S hS X :=
  ObjectProperty.lift _
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Y) ⋙
      Over.pullback (yoneda.map j))
    fun F ↦ isFinitePresentationSpaceOver_pullback B S hS j F.2

/-- Base change along an identity of the big fppf site of `S` is isomorphic to the identity
functor. -/
noncomputable def baseChangeId (X : BigFppfOver B S hS) :
    baseChange B S hS (𝟙 X) ≅ 𝟭 (FinitePresentationSpacesOver B S hS X) :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X))
    (Functor.isoWhiskerLeft (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X))
      (eqToIso (show (Over.pullback (yoneda.map (𝟙 X)) :
            Over (yoneda.obj X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ _) =
          Over.pullback (𝟙 (yoneda.obj X)) by rw [yoneda.map_id]) ≪≫ Over.pullbackId))

/-- Base change along a composite of the big fppf site of `S` is isomorphic to the composite of
the base changes, in the reverse order. -/
noncomputable def baseChangeComp {X Y Z : BigFppfOver B S hS} (i : X ⟶ Y) (j : Y ⟶ Z) :
    baseChange B S hS (i ≫ j) ≅ baseChange B S hS j ⋙ baseChange B S hS i :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X))
    (Functor.isoWhiskerLeft (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Z))
      (eqToIso (show (Over.pullback (yoneda.map (i ≫ j)) :
            Over (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ _) =
          Over.pullback (yoneda.map i ≫ yoneda.map j) by rw [yoneda.map_comp]) ≪≫
        Over.pullbackComp (yoneda.map i) (yoneda.map j)))

/-- The comparison isomorphism between the two iterated base changes attached to a commuting
square `iU ≫ jU = iW ≫ jW` of the big fppf site of `S`. -/
noncomputable def baseChangeSquareIso {V U W Z : BigFppfOver B S hS} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (w : iU ≫ jU = iW ≫ jW) :
    baseChange B S hS jU ⋙ baseChange B S hS iU ≅
      baseChange B S hS jW ⋙ baseChange B S hS iW :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V))
    (Functor.isoWhiskerLeft (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Z))
      (Over.pullbackSquareIso (by rw [← Functor.map_comp, ← Functor.map_comp, w])))

/-! ### The comparison with the `2`-fibre product -/

/-- The comparison functor attached to a commuting square `iU ≫ jU = iW ≫ jW` of the big fppf
site of `S`, from the algebraic spaces of finite presentation over `Z` to the `2`-fibre product
`FP_U ×_{FP_V} FP_W`. It takes an algebraic space of finite presentation over `Z` to its base
changes to `U` and to `W` together with the canonical identification of their further base
changes to `V`. -/
noncomputable def glueingFunctor {V U W Z : BigFppfOver B S hS} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (w : iU ≫ jU = iW ≫ jW) :
    FinitePresentationSpacesOver B S hS Z ⥤
      IsoComma (baseChange B S hS iU) (baseChange B S hS iW) :=
  IsoComma.lift _ _ (baseChange B S hS jU) (baseChange B S hS jW)
    (baseChangeSquareIso B S hS w)

/-- The first projection of the comparison functor is base change along `jU`. -/
theorem glueingFunctor_comp_fst {V U W Z : BigFppfOver B S hS} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (w : iU ≫ jU = iW ≫ jW) :
    glueingFunctor B S hS w ⋙ IsoComma.fst (baseChange B S hS iU) (baseChange B S hS iW) =
      baseChange B S hS jU :=
  rfl

/-- The second projection of the comparison functor is base change along `jW`. -/
theorem glueingFunctor_comp_snd {V U W Z : BigFppfOver B S hS} {jU : U ⟶ Z} {jW : W ⟶ Z}
    {iU : V ⟶ U} {iW : V ⟶ W} (w : iU ≫ jU = iW ≫ jW) :
    glueingFunctor B S hS w ⋙ IsoComma.snd (baseChange B S hS iU) (baseChange B S hS iW) =
      baseChange B S hS jW :=
  rfl

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
