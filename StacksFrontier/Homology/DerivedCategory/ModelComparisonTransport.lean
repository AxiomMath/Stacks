module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# Transporting derived-category data between the standard and the locally small model

`HasDerivedCategory.{w} C` is the assumption that a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms has been *chosen*, with morphisms in `Type w`. The repository runs two choices
side by side: the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`,
activated
file-locally, with morphisms in `Type u`, and `HasDerivedCategory.standard`, installed
file-locally, with morphisms in `Type (u + 1)`. A morphism of one model cannot be composed with a
morphism of the other, which is what this file repairs.

The comparison of two *arbitrary* models lives upstream in
`StacksFrontier.Homology.DerivedCategory.ModelComparison`, which this file imports: `modelEquiv`,
`modelCompQIso`, `modelInverseCompQIso` and their lemmas. What is added here is the comparison of
the two models actually in play, and the transport of a total derived functor across any such
comparison.

## Why this is a separate module

`StacksFrontier.Homology.DerivedCategory.LocallySmall` declares three *global* `HasDerivedCategory`
instances, with morphisms in `Type u`. A module that imports it therefore has those instances in
scope, and instance search prefers them to a file-local `HasDerivedCategory.standard`, whose
morphisms live in `Type (u + 1)`. Any downstream module that leaves the `HasDerivedCategory`
argument of `derivedPullback`, `derivedPushforward` or `pullbackOnHomotopy` to search then
elaborates it at the wrong model and fails with a universe constraint or a non-definitional
instance, even though it never mentions local smallness at all.

So the import of `LocallySmall` is kept *here*, out of the import closure of `ModelComparison`.
`ModelComparison` has six importers in the library that pin `HasDerivedCategory.standard` locally
and rely on search finding it; adding `LocallySmall` to its imports breaks them, and breaks their
own importers in turn — among them
`StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChangeIsomorphism`, which mentions neither
file. A consumer that genuinely wants the transport imports this module and pays the cost of
spelling every `HasDerivedCategory` instance explicitly, which is the discipline every declaration
below follows.

## Main definitions

All in the namespace `StacksDraft.DerivedModel`. The comparison equivalence they are stated in
terms of is `Stacks.Injectives.grothendieckModelEquiv`, which goes from the standard model to the
locally small model of a Grothendieck abelian category and is the shrinking equivalence.

* `shrinkComparisonQhIso` — it identifies the two localization functors out of the homotopy
  category.
* `shrinkComparisonHomEquiv` — the bijection it induces on morphism types.
* `schemeModulesComparison` — the same comparison for `D(𝒪_X)` of a scheme `X`.
* `rightDerivedModelIso` and `leftDerivedModelIso` — a total derived functor transported across a
  comparison of models of its source and of its target.
* `derivedPushforwardModelIso` and `derivedPullbackModelIso` — those applied to `Rf_*` and `Lf^*`
  of a morphism of ringed spaces.

## Main results

* `derivedCategory_eq_standard` — the two models have the same objects, by definitional equality.
  That they also have the same localization functor out of cochain complexes, again by
  definitional equality, is `Stacks.Injectives.grothendieckModelEquiv_comp_Q`.
* `isIso_shrinkComparison_functor_map_iff` and `isIso_shrinkComparison_inverse_map_iff` — a
  morphism is invertible in one model if and only if its transport is invertible in the other.

## Implementation notes

*No `@[stacks]` attribute is attached to anything in this file.* The source has nothing to say
about the matter: it is an artefact of formalizing the derived category as a chosen localization
with a chosen morphism universe, and the statements below are about two Lean definitions, not
about two mathematical objects. The one tag that does appear in the chain, Tag 079Q, is carried
where it belongs, by `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`.

*What is definitional.* Three things, and they are the content of
`derivedCategory_eq_standard`, `Stacks.Injectives.grothendieckModelEquiv_comp_Q` and the type
ascription inside `Stacks.Injectives.grothendieckModelEquiv`.
`MorphismProperty.hasLocalizationOfLocallySmall W L` has underlying type `ShrinkHoms D` and
localization functor `L ⋙ ShrinkHoms.functor`, and
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` is that construction applied to
the standard `DerivedCategory.Q`. Since `ShrinkHoms D` is a type synonym for `D`, the objects of
the two models are *equal*, not merely corresponding; since `LocallySmall` is a `Prop`, the
category structure the small model carries is the one `ShrinkHoms` puts on the standard model,
whichever proof of local smallness is used; and `Q` factors on the nose. The practical effect is
that `Stacks.Injectives.grothendieckModelEquiv_functor_obj` and
`Stacks.Injectives.grothendieckModelEquiv_inverse_obj` are `rfl` and that no object has to be
transported at all — only morphisms do.

*What needed real work.* Two things. First, `Qh` does *not* factor on the nose: it is built from
`Q` by `CategoryTheory.Quotient.lift`, and lifting a composite is not the composite of a lift, so
`shrinkComparisonQhIso` is a genuine natural isomorphism, obtained from the universal property of
the quotient by `CategoryTheory.Quotient.natIsoLift` out of the factorization of `Q`. Second, a
total derived functor is a choice, so nothing about it is definitional at all;
`rightDerivedModelIso` is the uniqueness of left Kan extensions used twice, once to post-compose
with the equivalence on the target (`Functor.IsRightDerivedFunctor` is stable under composition
with a left adjoint) and once to change the localization functor along which the extension is
taken (`Functor.isLeftKanExtension_iff_precomp_equivalence`, whose coherence hypothesis holds
because `transportRightDerivedUnit` is *defined* to make it hold). `leftDerivedModelIso` is the
dual.

*What is not transported.* The comparison carries no triangulated or shift structure here. For
two arbitrary models that is supplied by `StacksDraft.Perfect.derivedEquivalenceCommShift` and
`StacksDraft.Perfect.derivedEquivalence_isTriangulated`, which are *not* available for
`Stacks.Injectives.grothendieckModelEquiv`, that being a different equivalence; a consumer needing
exactness of the comparison should use `modelEquiv`, and one needing the explicit description of
objects and morphisms should use `Stacks.Injectives.grothendieckModelEquiv`. Nothing here
identifies the two equivalences, and no
adjunction is transported: `derivedPushforwardModelIso` and `derivedPullbackModelIso` compare the
two functors but say nothing about the two adjunctions of Tag 079W relating them.

*Binders versus transport.* No declaration here takes a free `[HasDerivedCategory.{w}]` binder
over a category that also admits a global instance; the two models are always named explicitly, as
`HasDerivedCategory.standard` and `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`.
This is the discipline urged by the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`: a free
binder on a category whose spelling instance search can reach by another route gives two ways to
fill one argument of a type, and the transport below is offered instead.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u v w

namespace StacksDraft.DerivedModel

/-! ### Transporting a total derived functor across a comparison of models

The source of a total right derived functor is a localized category and its target is arbitrary,
so transporting one asks for two comparisons: an equivalence `G` of the two models of the
localized category, compatible with the two localization functors, and an equivalence `J` of the
two targets. -/

section Derived

variable {K : Type u} [Category.{v} K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K)
  {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W] [L₂.IsLocalization W]
  {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]

/-- The canonical map exhibiting `G ⋙ RF₂` as a right derived functor along `L₁` of what `RF₂`
is a right derived functor of along `L₂`. It is *defined* as the composite the coherence
hypothesis of `Functor.isLeftKanExtension_iff_precomp_equivalence` asks for, which is what makes
`isRightDerivedFunctor_comp_isEquivalence` below hold with no coherence chase. -/
def transportRightDerivedUnit {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂} (α₂ : F₂ ⟶ L₂ ⋙ RF₂)
    (hG : L₁ ⋙ G ≅ L₂) : F₂ ⟶ L₁ ⋙ (G ⋙ RF₂) :=
  α₂ ≫ whiskerRight hG.inv RF₂ ≫ (Functor.associator L₁ G RF₂).hom

/-- A right derived functor along `L₂` is, after precomposition with an equivalence `G` carrying
`L₁` to `L₂`, a right derived functor along `L₁`: being a left Kan extension is stable under
replacing the functor one extends along by an equivalent one. -/
theorem isRightDerivedFunctor_comp_isEquivalence {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂}
    (α₂ : F₂ ⟶ L₂ ⋙ RF₂) [RF₂.IsRightDerivedFunctor α₂ W] (hG : L₁ ⋙ G ≅ L₂) :
    (G ⋙ RF₂).IsRightDerivedFunctor (transportRightDerivedUnit α₂ hG) W := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have h₂ : RF₂.IsLeftKanExtension α₂ := by
    rwa [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W]
  rw [← Functor.isLeftKanExtension_iff_precomp_equivalence (G := 𝟭 K) (G' := G)
    (transportRightDerivedUnit α₂ hG) α₂ (Functor.leftUnitor L₂ ≪≫ hG.symm)
    (Functor.leftUnitor F₂).symm (Iso.refl (G ⋙ RF₂)) ?_]
  · exact h₂
  · ext X
    simp [transportRightDerivedUnit]

/-- **A total right derived functor read at two models.** If `RF₁` is a right derived functor of
`F₁` along `L₁` and `RF₂` one of `F₂` along `L₂`, and the two situations are matched by
equivalences `G` of the localized categories and `J` of the targets, then `RF₁` and `RF₂` agree up
to those equivalences. Both sides are right derived functors of `F₂` along `L₁`, and a right
derived functor is unique up to a canonical isomorphism. -/
def rightDerivedModelIso
    {F₁ : K ⥤ E₁} {RF₁ : D₁ ⥤ E₁} (α₁ : F₁ ⟶ L₁ ⋙ RF₁) [RF₁.IsRightDerivedFunctor α₁ W]
    {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂} (α₂ : F₂ ⟶ L₂ ⋙ RF₂) [RF₂.IsRightDerivedFunctor α₂ W]
    (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂) :
    RF₁ ⋙ J ≅ G ⋙ RF₂ :=
  letI := isRightDerivedFunctor_comp_isEquivalence W α₂ hG
  Functor.rightDerivedNatIso (RF₁ ⋙ J) (G ⋙ RF₂)
    (whiskerRight α₁ J ≫ (Functor.associator L₁ RF₁ J).hom)
    (transportRightDerivedUnit α₂ hG) W hF

/-- The dual of `transportRightDerivedUnit` for a left derived functor. -/
def transportLeftDerivedCounit {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ F₂)
    (hG : L₁ ⋙ G ≅ L₂) : L₁ ⋙ (G ⋙ LF₂) ⟶ F₂ :=
  (Functor.associator L₁ G LF₂).inv ≫ whiskerRight hG.hom LF₂ ≫ α₂

/-- The dual of `isRightDerivedFunctor_comp_isEquivalence`: a left derived functor along `L₂` is,
after precomposition with an equivalence `G` carrying `L₁` to `L₂`, a left derived functor along
`L₁`. -/
theorem isLeftDerivedFunctor_comp_isEquivalence {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂}
    (α₂ : L₂ ⋙ LF₂ ⟶ F₂) [LF₂.IsLeftDerivedFunctor α₂ W] (hG : L₁ ⋙ G ≅ L₂) :
    (G ⋙ LF₂).IsLeftDerivedFunctor (transportLeftDerivedCounit α₂ hG) W := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  have h₂ : LF₂.IsRightKanExtension α₂ := by
    rwa [← Functor.isLeftDerivedFunctor_iff_isRightKanExtension _ _ W]
  rw [← Functor.isRightKanExtension_iff_precomp_equivalence (G := 𝟭 K) (G' := G)
    (transportLeftDerivedCounit α₂ hG) α₂ (Functor.leftUnitor L₂ ≪≫ hG.symm)
    (Functor.leftUnitor F₂).symm (Iso.refl (G ⋙ LF₂)) ?_]
  · exact h₂
  · ext X
    simp [transportLeftDerivedCounit]

/-- **A total left derived functor read at two models**, the dual of `rightDerivedModelIso`. -/
def leftDerivedModelIso
    {F₁ : K ⥤ E₁} {LF₁ : D₁ ⥤ E₁} (α₁ : L₁ ⋙ LF₁ ⟶ F₁) [LF₁.IsLeftDerivedFunctor α₁ W]
    {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ F₂) [LF₂.IsLeftDerivedFunctor α₂ W]
    (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂) :
    LF₁ ⋙ J ≅ G ⋙ LF₂ :=
  letI := isLeftDerivedFunctor_comp_isEquivalence W α₂ hG
  Functor.leftDerivedNatIso (LF₁ ⋙ J) (G ⋙ LF₂)
    ((Functor.associator L₁ LF₁ J).inv ≫ whiskerRight α₁ J)
    (transportLeftDerivedCounit α₂ hG) W hF

end Derived

/-! ### The locally small model is the standard one with the morphisms shrunk -/

section Shrink

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **The two models have the same objects.** The locally small derived category of Tag 079Q is
obtained from the standard one by `MorphismProperty.hasLocalizationOfLocallySmall`, whose
underlying type is `ShrinkHoms` of the given one, and `ShrinkHoms` is a type synonym. -/
theorem derivedCategory_eq_standard :
    @DerivedCategory C _ _ (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) =
      @DerivedCategory C _ _ (HasDerivedCategory.standard C) := rfl

/-- **Morphisms correspond.** The comparison induces a bijection on each morphism type, being an
equivalence and hence fully faithful; concretely this bijection is `equivShrink`. Composition and
identities need no statement of their own, being `Functor.map_comp` and `Functor.map_id`. -/
def shrinkComparisonHomEquiv
    (X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)) :
    (X ⟶ Y) ≃ ((Stacks.Injectives.grothendieckModelEquiv C).functor.obj X ⟶
      (Stacks.Injectives.grothendieckModelEquiv C).functor.obj Y) :=
  (Stacks.Injectives.grothendieckModelEquiv C).fullyFaithfulFunctor.homEquiv

/-- The comparison identifies the two localization functors out of the homotopy category. Unlike
`Stacks.Injectives.grothendieckModelEquiv_comp_Q` this is a genuine isomorphism and not an
equality: `DerivedCategory.Qh` is produced from `DerivedCategory.Q` by the universal property of
the quotient by homotopy, and a lift of a composite is only canonically isomorphic to the
composite of the lift. -/
def shrinkComparisonQhIso :
    @DerivedCategory.Qh C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) ≅
      @DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C) ⋙
        (Stacks.Injectives.grothendieckModelEquiv C).functor :=
  Quotient.natIsoLift (r := homotopic C (ComplexShape.up ℤ))
    (@DerivedCategory.quotientCompQhIso C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C) ≪≫
      eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q C).symm ≪≫
      Functor.isoWhiskerRight
        (@DerivedCategory.quotientCompQhIso C _ _ (HasDerivedCategory.standard C)).symm
        (Stacks.Injectives.grothendieckModelEquiv C).functor ≪≫
      Functor.associator _ _ _)

/-- **Invertibility transports from the standard model to the locally small one.** A morphism of
the standard derived category is invertible if and only if its image in the locally small derived
category of Tag 079Q is. -/
theorem isIso_shrinkComparison_functor_map_iff
    {X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} (f : X ⟶ Y) :
    IsIso ((Stacks.Injectives.grothendieckModelEquiv C).functor.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f (Stacks.Injectives.grothendieckModelEquiv C).functor

/-- **Invertibility transports from the locally small model to the standard one**, the converse
direction of `isIso_shrinkComparison_functor_map_iff`. -/
theorem isIso_shrinkComparison_inverse_map_iff
    {X Y : @DerivedCategory C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)} (f : X ⟶ Y) :
    IsIso ((Stacks.Injectives.grothendieckModelEquiv C).inverse.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f (Stacks.Injectives.grothendieckModelEquiv C).inverse

end Shrink

/-- The comparison of the two models of `D(𝒪_X)` for a scheme `X`: the standard derived category
of `X.Modules` is equivalent to the locally small one,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
abbrev schemeModulesComparison (X : Scheme.{u}) :
    @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules) ≌
      DerivedCategory X.Modules :=
  Stacks.Injectives.grothendieckModelEquiv X.Modules

/-! ### The derived pushforward and the derived pullback at the two models -/

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived pushforward read at the two models.** For a morphism of ringed spaces,
`Rf_*` taken at the standard model and `Rf_*` taken at the locally small model of Tag 079Q agree
up to the comparison equivalences on source and target. Both are total right derived functors of
degreewise pushforward followed by localization. -/
def derivedPushforwardModelIso :
    @derivedPushforward X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ⋙
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing X))).functor ⋙
        @derivedPushforward X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (@derivedPushforwardUnit X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (@derivedPushforwardUnit X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm)

/-- **The derived pullback read at the two models**, the counterpart of
`derivedPushforwardModelIso` for the total left derived functor `Lf^*` of Tag 079W. -/
def derivedPullbackModelIso :
    @derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance ⋙
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing X))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing Y))).functor ⋙
        @derivedPullback X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance :=
  leftDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (@derivedPullbackComparison X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm)

end RingedSpaces

end StacksDraft.DerivedModel

end
