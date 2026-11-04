module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The base-change diagram for cohomology of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓕` be a
quasi-coherent `𝒪_X`-module, and let `g : Y' ⟶ Y` be a second morphism of algebraic spaces.
Writing `X' = Y' ×_Y X` for the base change of `X`, `f' : X' ⟶ Y'` for the base change of `f`,
`g' : X' ⟶ X` for the projection and `𝓕' = (g')^*𝓕`, Stacks 073J is the diagram

```
𝓕' = (g')^*𝓕   X' --g'--> X    𝓕
                |          |
                f'         f
                |          |
Rf'_*𝓕'         Y' --g-->  Y    Rf_*𝓕
```

This file defines that diagram as a structure, together with the three objects it displays
that are determined by the square: the pulled-back coefficient `𝓕'` and the two total derived
direct images `Rf_*𝓕` and `Rf'_*𝓕'`. It is the algebraic-space analogue of
`AlgebraicGeometry.BaseChangeDiagram`, the scheme-level diagram of Stacks 02KF.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram` is the cartesian square of algebraic spaces
  together with the quasi-coherent `𝒪_X`-module `𝓕` on its upper-right corner.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pulledBack` is the coefficient `𝓕' = (g')^*𝓕` on
  the base-changed source.
* `AlgebraicGeometry.Space.BaseChangeDiagram.derivedPushforward` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.derivedPushforward'` are the total derived direct
  images `Rf_*𝓕` and `Rf'_*𝓕'` on the bottom row.

## Main results

* `AlgebraicGeometry.Space.modules_enoughInjectives`: the `𝒪_X`-modules of an algebraic space
  have enough injectives.

## References

* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

universe u v

/-! ### Module sheaves over an essentially small site have enough injectives -/

section EssentiallySmallSite

variable {C : Type v} [Category.{u} C] [EssentiallySmall.{u} C] {J : GrothendieckTopology C}

private noncomputable instance moduleSiteHasSheafify : HasSheafify J AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u, _, _} J

private instance moduleSiteLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} J

/-- Presheaves of modules over an essentially small site have a separator. -/
private noncomputable instance modulePresheavesHaveSeparator (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasSeparator (PresheafOfModules.{u} R) := by
  let E := equivSmallModel.{u} C
  let G := E.inverse ⋙ yoneda ⋙ PresheafOfModules.free R
  have hG : (ObjectProperty.ofObj G.obj).IsSeparating := by
    intro M N f g h
    apply PresheafOfModules.freeYoneda.isSeparating R f g
    rintro _ ⟨X⟩ k
    let e := (yoneda ⋙ PresheafOfModules.free R).mapIso (E.unitIso.app X)
    simpa only [Category.assoc, Iso.cancel_iso_inv_left] using
      h _ (ObjectProperty.ofObj_apply G.obj (E.functor.obj X)) (e.inv ≫ k)
  exact ⟨_, hG.isSeparator_coproduct⟩

private noncomputable instance modulePresheavesLocallySmall (R : Cᵒᵖ ⥤ RingCat.{u}) :
    LocallySmall.{u} (PresheafOfModules.{u} R) := by
  have : LocallySmall.{u} (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (locallySmall_congr (Equivalence.congrLeft (equivSmallModel.{u} Cᵒᵖ))).mpr inferInstance
  exact locallySmall_of_faithful (PresheafOfModules.toPresheaf R)

/-- Presheaves of modules over an essentially small site form a Grothendieck abelian
category. -/
private noncomputable instance modulePresheavesGrothendieck (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun D _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := D) ⋙ PresheafOfModules.toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (PresheafOfModules.toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

/-- Sheaves of modules over an essentially small site form a Grothendieck abelian category. -/
private noncomputable instance moduleSheavesGrothendieck (R : Sheaf J RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where
  locallySmall := locallySmall_of_faithful (SheafOfModules.forget R)
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ ↦
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
  hasSeparator := .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

private instance moduleSheavesEnoughInjectives (R : Sheaf J RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives

end EssentiallySmallSite

/-! ### Modules on an algebraic space -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_X`-modules of an algebraic space have enough injectives. -/
instance modules_enoughInjectives (X : AlgebraicSpaces B S hS) :
    EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) := by
  have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
  infer_instance

/-- The sheaves of modules over the structure sheaf of the small étale ringed topos of an
algebraic space have enough injectives. -/
instance toposModules_enoughInjectives (X : AlgebraicSpaces B S hS) :
    EnoughInjectives (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) :=
  inferInstance

variable {B S hS}

/-- The module pushforward along a morphism of algebraic spaces is a right adjoint. -/
private theorem pushforwardModules_isRightAdjoint {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).IsRightAdjoint :=
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposModulesHom B S hS f)).isRightAdjoint

/-- The module pushforward along a morphism of algebraic spaces is additive. -/
instance pushforwardModules_additive {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).Additive :=
  have := pushforwardModules_isRightAdjoint f
  Functor.additive_of_preserves_binary_products _

/-! ### The base-change diagram -/

variable (B S hS)

/-- The base-change diagram for cohomology of algebraic spaces: a cartesian square of algebraic
spaces over `S`, together with a quasi-coherent `𝒪_X`-module `𝓕` on the source `X` of the
morphism `f` that is being base changed. -/
@[stacks 073J "the cartesian square and its coefficient"]
structure BaseChangeDiagram where
  /-- The base change `X' = Y' ×_Y X` of `X`. -/
  X' : AlgebraicSpaces B S hS
  /-- The source of the morphism being base changed. -/
  X : AlgebraicSpaces B S hS
  /-- The base `Y'` over which `X` is being base changed. -/
  Y' : AlgebraicSpaces B S hS
  /-- The target of the morphism being base changed. -/
  Y : AlgebraicSpaces B S hS
  /-- The projection `g' : X' ⟶ X`. -/
  g' : X' ⟶ X
  /-- The base change `f' : X' ⟶ Y'` of `f`. -/
  f' : X' ⟶ Y'
  /-- The morphism `f : X ⟶ Y` being base changed. -/
  f : X ⟶ Y
  /-- The morphism `g : Y' ⟶ Y` along which `f` is being base changed. -/
  g : Y' ⟶ Y
  /-- The square is cartesian, so `X'` is the base change `Y' ×_Y X`. -/
  isPullback : IsPullback g' f' f g
  /-- The coefficient `𝓕` on `X`. -/
  F : Modules.{u, u} B S hS X.1 X.2
  [isQuasicoherent : F.IsQuasicoherentOnSite]

namespace BaseChangeDiagram

attribute [instance] isQuasicoherent

variable {B S hS} (D : BaseChangeDiagram B S hS)

/-- The coefficient `𝓕' = (g')^*𝓕` on the base-changed source. -/
@[stacks 073J "the pulled-back coefficient"]
abbrev pulledBack : Modules.{u, u} B S hS D.X'.1 D.X'.2 :=
  (modulePullback B S hS D.g').obj D.F

/-- The total derived direct image `Rf_*𝓕` on the lower-right corner. -/
@[stacks 073J "the lower-right derived direct image"]
abbrev derivedPushforward : DerivedCategory.Plus (Modules.{u, u} B S hS D.Y.1 D.Y.2) :=
  (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS D.f)).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS D.X.1 D.X.2) 0).obj D.F)

/-- The total derived direct image `Rf'_*𝓕'` on the lower-left corner. -/
@[stacks 073J "the lower-left derived direct image"]
abbrev derivedPushforward' : DerivedCategory.Plus (Modules.{u, u} B S hS D.Y'.1 D.Y'.2) :=
  (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS D.f')).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor (Modules.{u, u} B S hS D.X'.1 D.X'.2) 0).obj
      D.pulledBack)

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
