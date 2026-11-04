module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.Lifting.Left
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackEssentiallySmallUnivLE
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of modules has a left adjoint over an essentially small site

Let `F : C ⥤ D` be a functor and let `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings.
Mathlib's `PresheafOfModules.pullback φ` is the left adjoint of `PresheafOfModules.pushforward φ`
*when one exists*, the existence being carried by the typeclass
`(PresheafOfModules.pushforward φ).IsRightAdjoint`, which Mathlib discharges only when both sites
are `SmallCategory` in the universe of the rings.

`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackUnivLE.lean` discharges it whenever the
source site is `v`-**small**. That is not enough for the sites of algebraic geometry: the site of
**Stacks 06TP** of a category fibred in groupoids has its objects in `Type (u + 1)` while its
structure sheaf of **Stacks 06TV** takes its sections in `Type u`, so the type of its objects is
not `u`-small — it is only *essentially* `u`-small, because every object is isomorphic to one of a
`u`-small family.

This file discharges the typeclass from essential smallness instead. The argument is a different
one: rather than resolving a presheaf of modules into free modules on representables, it lifts the
adjunction through the free–forgetful adjunction of presheaves of modules
(`CategoryTheory.isRightAdjoint_triangle_lift`), for which the only input is that restriction of
presheaves of *types* along `F.op` has a left adjoint, i.e. that `F.op` admits pointwise left Kan
extensions — and that is exactly what essential smallness of the source supplies, through
`CategoryTheory.Limits.hasColimitsOfShape_of_essentiallySmall` applied to the comma categories
`CostructuredArrow F.op Y`.

## Main results

* `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall`: pushforward of presheaves of
  modules is a right adjoint as soon as the source site is essentially small in the universe of
  the rings and the module sections.
* `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE`: the same with the
  universe of the presheaves of rings independent of the universe of the module sections, the
  rings being asked only to take `v`-small values.
* `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`: hence so is pushforward of
  sheaves of modules, given sheafification of abelian presheaves on the target site.
* `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall_univLE`: the same with the
  universe of the sheaves of rings independent of the universe of the module sections.

## Implementation notes

The target site needs only to be *locally* `v`-small, for `CostructuredArrow F.op Y` to be
essentially small; nothing here asks it to be essentially small itself.

The composite `pushforward φ ⋙ (toPresheaf S ⋙ (whiskeringRight _ _ _).obj (forget Ab))` is
equal on the nose to `(toPresheaf R ⋙ (whiskeringRight _ _ _).obj (forget Ab)) ⋙
(whiskeringLeft _ _ _).obj F.op`, which is why the hypothesis of the lifting theorem is supplied
by `Functor.isRightAdjoint_of_iso` at `Iso.refl`: both sides send a presheaf of modules to its
underlying presheaf of types restricted along `F.op`, and the two spellings differ only in the
order in which the forgetful functor and the restriction are applied.

That lifting argument ties the module universe to the ring universe, because
`PresheafOfModules.freeAdjunction` does. The universe-independent statement therefore goes by the
other route: the canonical presentation of a presheaf of modules by free presheaves of modules on
representables of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackEssentiallySmallUnivLE.lean`, whose free
objects are `PresheafOfModules.freeObjShrink` and whose corepresentation of sections is
`PresheafOfModules.freeYonedaShrinkEquiv`, both with the two universes independent. Essential
smallness enters there as a `v`-small family of objects meeting every isomorphism class, namely
the image of `CategoryTheory.SmallModel`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

universe v v₁ v₂ u₁ u₂ r

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [EssentiallySmall.{v} C] [LocallySmall.{v} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{v}} {S : Cᵒᵖ ⥤ RingCat.{v}} (φ : S ⟶ F.op ⋙ R)

/-- **The pushforward of presheaves of modules is a right adjoint** as soon as the source site is
essentially small in the universe of the rings and of the module sections, the target site being
locally small in that universe. Instance, so that `PresheafOfModules.pullback φ` and
`PresheafOfModules.pullbackPushforwardAdjunction φ` are available with no adjointness
hypothesis. -/
@[stacks 03D6 "part (2), presheaves of modules over an essentially small site"]
instance isRightAdjoint_pushforward_of_essentiallySmall :
    (pushforward.{v} φ).IsRightAdjoint := by
  have h : ∀ M, RegularEpi ((freeAdjunction S).counit.app M) := fun _ ↦ regularEpiOfEpi _
  let _ : ∀ P : Cᵒᵖ ⥤ Type v, F.op.HasPointwiseLeftKanExtension P := fun _ Y ↦ by
    let _ := hasColimitsOfShape_of_essentiallySmall.{v} (CostructuredArrow F.op Y) (Type v)
    infer_instance
  let _ := (F.op.lanAdjunction (Type v)).isRightAdjoint
  let _ := (freeAdjunction R).isRightAdjoint
  have _ : (pushforward.{v} φ ⋙ (toPresheaf S ⋙
      (Functor.whiskeringRight _ _ _).obj (forget Ab))).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (Iso.refl
      ((toPresheaf R ⋙ (Functor.whiskeringRight _ _ _).obj (forget Ab)) ⋙
        (Functor.whiskeringLeft _ _ (Type v)).obj F.op))
  exact isRightAdjoint_triangle_lift _ (freeAdjunction S) h

section UnivLE

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [EssentiallySmall.{v} C] [LocallySmall.{v} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}}
  [∀ X, Small.{v} (R.obj X)] [∀ X, Small.{v} (S.obj X)] (φ : S ⟶ F.op ⋙ R)

/-- **The pushforward of presheaves of modules is a right adjoint** as soon as the source site is
essentially small in the universe of the module sections, the target site being locally small in
that universe and the presheaves of rings taking `v`-small values — the universe of the rings
being otherwise unrelated to the universe `v` of the module sections. Instance, so that
`PresheafOfModules.pullback φ` and `PresheafOfModules.pullbackPushforwardAdjunction φ` are
available with no adjointness hypothesis.

This is `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall` with the ring universe
freed: the sections of a presheaf of modules may live above the universe of the rings, which is
what the structure sheaf of a site of algebraic geometry together with a module of larger
sections requires. -/
instance isRightAdjoint_pushforward_of_essentiallySmall_univLE :
    (pushforward.{v} φ).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top_of_family.{v} φ
      (ι := fun U : SmallModel C ↦ (equivSmallModel C).inverse.obj U)
      (hι := fun X ↦ ⟨(equivSmallModel C).functor.obj X,
        ⟨((equivSmallModel C).unitIso.app X).symm⟩⟩))

end UnivLE

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [EssentiallySmall.{v} C] [LocallySmall.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K] {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R)
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Mathlib's presheaf-level existence instance restated at the spelling the sheaf-level
construction resolves against. The restatement is needed because
`((F.sheafPushforwardContinuous RingCat J K).obj R).obj` is not syntactically `F.op ⋙ R.obj`, so
the implicit functor and presheaves of rings of
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall` cannot be read off the type of
`φ.hom`; ascribing the type pins them. -/
instance presheafPushforward_isRightAdjoint_of_essentiallySmall :
    (PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{v} φ.hom

/-- **Pushforward of sheaves of modules along a continuous functor of sites has a left adjoint**
as soon as the source site is essentially small in the universe of the sheaves of rings and of
the module sections. This is the existence half of the lower shriek for modules. -/
@[stacks 03D6 "part (2), sheaves of modules over an essentially small site"]
instance pushforward_isRightAdjoint_of_essentiallySmall :
    (pushforward.{v} φ).IsRightAdjoint :=
  (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

section UnivLE

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [EssentiallySmall.{v} C] [LocallySmall.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K] {R : Sheaf K RingCat.{r}} {S : Sheaf J RingCat.{r}} [UnivLE.{r, v}]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE` restated at the
spelling the sheaf-level construction resolves against, for the same reason as
`SheafOfModules.presheafPushforward_isRightAdjoint_of_essentiallySmall`. -/
instance presheafPushforward_isRightAdjoint_of_essentiallySmall_univLE :
    (PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{v} φ.hom

/-- **Pushforward of sheaves of modules along a continuous functor of sites has a left adjoint**,
with the universe of the sheaves of rings independent of the universe `v` of the module sections:
the source site is asked to be essentially small in `v`, the target site to be locally small in
it, and the universe of the sheaves of rings to be at most `v`.  This is
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` with the two universes untied.

The ring universe is free because the construction's two inputs have it free: the presheaf-level
instance above goes through
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE`, and Mathlib's
`SheafOfModules.PullbackConstruction.adjunction` is already stated with the universe of the
sheaves of rings independent of the universe of the module sections.

Freeing the ring universe is what makes the instance applicable to the restriction of modules
along the functor `u_X : X_étale ⥤ 𝒳` of Stacks 073M, whose structure sheaves take their sections
in the universe `u` of the schemes while the module universe has to be enlarged; see
`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`. -/
instance pushforward_isRightAdjoint_of_essentiallySmall_univLE :
    (pushforward.{v} φ).IsRightAdjoint :=
  (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

end UnivLE

end SheafOfModules

end
