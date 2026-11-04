module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.Functor.KanExtension.PointwiseExistence

/-!
# Lower shriek of sheaves of modules on categories fibred in groupoids

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`, and let `τ` be a topology on the underlying category of schemes, coarser than the
fppf topology. Both `𝒳` and `𝒴` carry the sites they inherit from `τ` (Stacks 06TP) and their
structure sheaves `𝒪_𝒳`, `𝒪_𝒴`, and `f` is continuous and cocontinuous with
`f⁻¹ 𝒪_𝒴 = 𝒪_𝒳` (Stacks 06NW). Restriction of scalars along this identification is the inverse
image `f^* : Mod(𝒴_τ, 𝒪_𝒴) ⥤ Mod(𝒳_τ, 𝒪_𝒳)`.

Then `f^*` has a left adjoint `f_!`, on presheaves and on sheaves of modules, which agrees with
the lower shriek of abelian sheaves after forgetting the module structure; when `f` is faithful and
`𝒳` has equalizers, `f_!` is exact and `f^*` preserves injective objects (**Stacks 06X2**). The
categories `𝒳` and `𝒴` are assumed essentially small in the universe `t` of the module sections,
and the universe `u` of the schemes is at most `t`.

## Main results

* `AlgebraicGeometry.Stack.isRightAdjoint_presheafOfModules_pushforward`: inverse image of
  presheaves of modules along `f` has a left adjoint.
* `AlgebraicGeometry.Stack.isRightAdjoint_sheafOfModules_pushforward`: **Stacks 06X2**, inverse
  image of sheaves of modules along `f` has a left adjoint `f_!`.
* `AlgebraicGeometry.Stack.lowerShriekModulesForgetIso`: **Stacks 06X2**, `f_!` on sheaves of
  modules agrees with `f_!` on abelian sheaves (Stacks 06X1) on underlying abelian sheaves.
* `AlgebraicGeometry.Stack.exactFunctor_sheafOfModules_pullback`: **Stacks 06X2 (1)**, for `f`
  faithful and `𝒳` with equalizers, `f_!` on sheaves of modules is exact.
* `AlgebraicGeometry.Stack.injective_sheafOfModules_pushforward_obj_of_injective`: **Stacks
  06X2 (2)**, under the same hypotheses `f^*` carries injective sheaves of modules to injective
  sheaves of modules.

## References

* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂ t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- Inverse image of presheaves of modules along a 1-morphism of categories fibred in groupoids
has a left adjoint, the presheaf-level lower shriek, when the source is essentially small and the
target locally small in the universe of the module sections, and the universe of the schemes is
at most that universe. -/
theorem isRightAdjoint_presheafOfModules_pushforward
    [EssentiallySmall.{t} 𝒳] [LocallySmall.{t} 𝒴] [UnivLE.{u, t}]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    (PresheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  exact PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{t} _

/-- Abelian sheaves with sections in `Type t` on the site inherited by an essentially `t`-small
category over the big fppf category admit sheafification. -/
theorem hasSheafify_associatedTopology_of_essentiallySmall [EssentiallySmall.{t} 𝒴] :
    HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{t} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the site inherited by an essentially `t`-small category over the big fppf category, a
morphism of presheaves of abelian groups with sections in `Type t` becomes an isomorphism after
sheafification exactly when it is locally bijective. -/
theorem wEqualsLocallyBijective_associatedTopology_of_essentiallySmall
    [EssentiallySmall.{t} 𝒴] :
    (associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **Stacks 06X2, existence of `f_!`.** Inverse image of sheaves of modules along a
1-morphism of categories fibred in groupoids over the big fppf category of a scheme has a left
adjoint `f_!`. -/
@[stacks 06X2 "f^* on sheaves of modules has a left adjoint f_!"]
theorem isRightAdjoint_sheafOfModules_pushforward
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] [UnivLE.{u, t}]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    (SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).IsRightAdjoint := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let := isRightAdjoint_presheafOfModules_pushforward.{u, v₁, v₂, w₁, w₂, t}
    B S hS p q F τ hp hq hcomp hτ
  let := hasSheafify_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  let := wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  exact SheafOfModules.instIsRightAdjointPushforward _

/-- Run `k` with the left Kan extension and sheafification instances needed for `f_!` available. -/
private theorem with_instances [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴]
    [UnivLE.{u, t}] {P : Prop}
    (k : [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, F.op.HasPointwiseLeftKanExtension G] →
      [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{t}] →
      [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{t}] → P) : P :=
  haveI := fun G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t} ↦
    Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall.{t} F.op G
  haveI := hasSheafify_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  haveI := wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  k

/-- **Stacks 06X2, comparison with abelian sheaves.** The lower shriek `f_!` of sheaves of
modules along a 1-morphism of categories fibred in groupoids agrees, on underlying abelian
sheaves, with the lower shriek of abelian sheaves of Stacks 06X1. -/
@[stacks 06X2 "f_! on sheaves of modules agrees with f_! on abelian sheaves"]
noncomputable def lowerShriekModulesForgetIso
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] [UnivLE.{u, t}]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI := isRightAdjoint_sheafOfModules_pushforward.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q F τ hp hq hcomp hτ
    letI := fun G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t} ↦
      Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall.{t} F.op G
    letI := hasSheafify_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
    SheafOfModules.pullback.{t} (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ) ⋙
        SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS q hq τ hτ) ≅
      SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ) ⋙
        Functor.sheafPullbackConstruction.sheafPullback F AddCommGrpCat.{t}
          (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) :=
  letI := fun G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t} ↦
    Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall.{t} F.op G
  letI := hasSheafify_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  letI := wEqualsLocallyBijective_associatedTopology_of_essentiallySmall.{u, v₂, w₂, t} B S hS q τ
  lowerShriekForgetIso B S hS p q F τ hp hq hcomp hτ
    (isRightAdjoint_presheafOfModules_pushforward B S hS p q F τ hp hq hcomp hτ)

/-- **Stacks 06X2, part (1).** For a faithful 1-morphism of categories fibred in groupoids
whose source has equalizers, the lower shriek `f_!` of sheaves of modules is exact. -/
@[stacks 06X2 "part (1)"]
theorem exactFunctor_sheafOfModules_pullback
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] [UnivLE.{u, t}]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) [F.Faithful] [HasEqualizers 𝒳] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI := isRightAdjoint_sheafOfModules_pushforward.{u, v₁, v₂, w₁, w₂, t}
      B S hS p q F τ hp hq hcomp hτ
    exactFunctor _ _
      (SheafOfModules.pullback.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)) :=
  with_instances.{u, v₁, v₂, w₁, w₂, t} B S hS q F τ <|
  exact_sheafOfModules_pullback_of_faithful B S hS p q F τ hp hq hcomp hτ
    (isRightAdjoint_presheafOfModules_pushforward B S hS p q F τ hp hq hcomp hτ)

/-- **Stacks 06X2, part (2).** For a faithful 1-morphism of categories fibred in groupoids
whose source has equalizers, the inverse image of an injective sheaf of modules is an injective
sheaf of modules. -/
@[stacks 06X2 "part (2)"]
theorem injective_sheafOfModules_pushforward_obj_of_injective
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] [UnivLE.{u, t}]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) [F.Faithful] [HasEqualizers 𝒳]
    (I : SheafOfModules.{t} (ringStructureSheafCore B S hS q hq τ hτ)) [Injective I] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    Injective ((SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).obj I) :=
  with_instances.{u, v₁, v₂, w₁, w₂, t} B S hS q F τ <|
  injective_sheafOfModules_pushforward_obj B S hS p q F τ hp hq hcomp hτ
    (isRightAdjoint_presheafOfModules_pushforward B S hS p q F τ hp hq hcomp hτ) I

end AlgebraicGeometry.Stack

end
