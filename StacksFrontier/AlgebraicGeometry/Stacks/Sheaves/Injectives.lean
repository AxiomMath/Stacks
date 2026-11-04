module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LowerShriekSliceEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.TwoFibreProductEqualizers
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# Injective sheaves on the sites associated to categories fibred in groupoids

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`, and let `τ` be a topology on the underlying category of schemes. Each of `𝒳`
and `𝒴` carries the site it inherits from the localization of `τ` at `S` (Stacks 06TP), and `f`
induces a morphism of topoi between them (Stacks 06NW). This file records which of the three
functors of that morphism preserve injective objects, for abelian sheaves and for sheaves of
modules over the structure sheaves.

Direct image always preserves injectives, because its left adjoint — the inverse image — is
restriction along `f`, hence exact. The inverse image preserves injectives only under extra
hypotheses, because what must be exact is then its *left* adjoint `f_!`: that is where
faithfulness of `f` and the existence of equalizers in `𝒳` enter, through the exactness
criterion for lower shriek (Stacks 04BH), whose hypotheses are that the source have fibre
products and equalizers and that `f` preserve them.

## Main definitions

* `AlgebraicGeometry.Stack.ringStructureSheafCoreHom`: the identification of the structure sheaf
  of `𝒳` with the inverse image of the structure sheaf of `𝒴`, which is the morphism of sheaves
  of rings along which modules are transported.
* `AlgebraicGeometry.Stack.lowerShriekForgetIso`: **Stacks 06X2**, lower shriek on sheaves of
  modules agrees with lower shriek on abelian sheaves after forgetting the module structure.

## Main results

* `AlgebraicGeometry.Stack.preservesInjectiveObjects_sheafPushforwardCocontinuous`: **Stacks
  06WX (1)**, direct image preserves injective abelian sheaves.
* `AlgebraicGeometry.Stack.preservesInjectiveObjects_of_adjunction_sheafOfModules_pushforward`:
  **Stacks 06WX (2)**, direct image preserves injective sheaves of modules.
* `AlgebraicGeometry.Stack.exact_sheafPullback_of_faithful` and
  `AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj`: **Stacks 06X1**, `f_!` is
  exact on abelian sheaves and `f⁻¹` preserves injectives, given the pointwise Kan extensions.
* `AlgebraicGeometry.Stack.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall`,
  `AlgebraicGeometry.Stack.exact_leftAdjoint_sheafPushforwardContinuous_of_faithful` and
  `AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj_of_essentiallySmall`:
  **Stacks 06X1** for essentially small `𝒳` and `𝒴`, with the left adjoint `f_!` of `f⁻¹`
  constructed rather than assumed.
* `AlgebraicGeometry.Stack.exact_sheafOfModules_pullback_of_faithful` and
  `AlgebraicGeometry.Stack.injective_sheafOfModules_pushforward_obj`: **Stacks 06X2**, the same
  for sheaves of modules.

## Implementation notes

The source fixes `τ` among the Zariski, étale, smooth, syntomic and fppf topologies; nothing
below uses which one is chosen, so everything is stated for an arbitrary topology on
`B.Schemes`, and the five statements of the source are its values at those five. This follows
`AlgebraicGeometry.Stack.associatedTopology` itself and is a generalization of the source's
hypothesis, not a weakening of its conclusion.

Stacks 06WX (1) is stated for a 1-morphism of *fibred* categories rather than of categories
fibred in groupoids, since its proof uses only the induced adjunction and the exactness of the
inverse image. The remaining statements genuinely need groupoid fibres: Stacks 06X1 obtains
fibre products in `𝒳` from them (Stacks 06WY) and preservation of fibre products and equalizers
by `f` from them (Stacks 06WZ), through the independent-universe forms
`CategoryTheory.TwoFibreProductOver.preservesPullbacks_of_fibred` and
`CategoryTheory.TwoFibreProductOver.preservesEqualizers_of_faithful`.

Mathlib's `SheafOfModules.pushforward φ` is the inverse image `f^*` of sheaves of modules, being
restriction of scalars along `φ`, and `SheafOfModules.pullback φ` is `f_!`. Direct image of
sheaves of modules is therefore the right adjoint of `SheafOfModules.pushforward φ`; its
existence is the content of Stacks 06X0, and is taken as the hypothesis `adj` of Stacks 06WX (2)
rather than constructed here. The `IsRightAdjoint` and Kan-extension hypotheses elsewhere are
likewise the size conditions under which the available constructions of `f_!` exist. For abelian
sheaves they are discharged in the last section, from essential smallness of `𝒳` and `𝒴`: the
source's categories have a set of objects (Stacks 0015), and that is what makes the colimits
defining `f_!` exist.

## References

* [Stacks Project, Tag 06WX](https://stacks.math.columbia.edu/tag/06WX)
* [Stacks Project, Tag 06X1](https://stacks.math.columbia.edu/tag/06X1)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **Stacks 0CN0, relative form.** For a 1-morphism `F` of categories fibred in groupoids over
a common base, the slice functor `Over x ⥤ Over (F x)` is an equivalence. Both slices identify,
through `CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_overPost`, with the slice of
the base over the image of `x`.

This belongs with Stacks 0CN0 in
`StacksFrontier/CategoryTheory/Sites/Gerbe/Localization.lean`. -/
theorem isEquivalence_overPost_of_comp_eq
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃}
    [Category.{v₃} 𝒴] {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p) (x : 𝒳) :
    (Over.post (X := x) F).IsEquivalence := by
  cases hcomp
  have h1 : (Over.post (X := x) (F ⋙ q)).IsEquivalence := hp.isEquivalence_overPost x
  have h2 : (Over.post (X := F.obj x) q).IsEquivalence := hq.isEquivalence_overPost (F.obj x)
  have h3 : (Over.post (X := x) F ⋙ Over.post (X := F.obj x) q).IsEquivalence :=
    Functor.isEquivalence_of_iso (Over.postComp (X := x) F q)
  exact Functor.isEquivalence_of_comp_right _ (Over.post (X := F.obj x) q)

end CategoryTheory.Functor.IsFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂ t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- The right adjoint of a functor preserving finite limits preserves injective objects. -/
private theorem preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits
    {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [PreservesFiniteLimits L] : R.PreservesInjectiveObjects :=
  have := preservesMonomorphisms_of_preservesLimitsOfShape L
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

/-- **Stacks 06WX, part (1).** Direct image along a 1-morphism of fibred categories over the
big fppf category of a scheme carries injective abelian sheaves to injective abelian sheaves,
for the site each side inherits from an arbitrary topology on the base.

The inverse image is the left adjoint of direct image and preserves finite limits, hence
monomorphisms, and a right adjoint of a monomorphism-preserving functor preserves injectives. -/
@[stacks 06WX "part (1)"]
theorem preservesInjectiveObjects_sheafPushforwardCocontinuous
    [p.IsFibered] [q.IsFibered] (hF : p.IsFibredOneMorphism q F)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, F.op.HasPointwiseRightKanExtension G] :
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{t}
      (associatedTopology B S hS p τ)
      (associatedTopology B S hS q τ)).PreservesInjectiveObjects := by
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := hF.preservesFiniteLimits_inverseImage (J := τ.over (B.obj hS))
    (A := AddCommGrpCat.{t})
  exact preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits
    (hF.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) AddCommGrpCat.{t})

/-- The structure sheaf of the source of a 1-morphism of categories fibred in groupoids is the
inverse image of the structure sheaf of the target: both are the structure presheaf of the base
restricted along the structure functor of the source. -/
noncomputable def ringStructureSheafCoreHom
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    ringStructureSheafCore B S hS p hp τ hτ ⟶
      (F.sheafPushforwardContinuous RingCat.{u}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).obj
        (ringStructureSheafCore B S hS q hq τ hτ) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  refine eqToHom ?_
  cases hcomp
  rfl

/-- Inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids is
left exact: it is restriction along the structure-sheaf identification, so on underlying abelian
sheaves it is the inverse image of **Stacks 06NW**, which preserves finite limits, and
`SheafOfModules.toSheaf` reflects them. -/
theorem preservesFiniteLimits_sheafOfModules_pushforward
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    PreservesFiniteLimits (SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let := (hq.isFibredOneMorphism hcomp).preservesFiniteLimits_inverseImage
    (J := τ.over (B.obj hS)) (A := AddCommGrpCat.{t})
  let φ := ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ
  let e : SheafOfModules.pushforward.{t} φ ⋙
      SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ) ≅
    SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS q hq τ hτ) ⋙
      F.sheafPushforwardContinuous AddCommGrpCat.{t}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) := Iso.refl _
  let : PreservesFiniteLimits (SheafOfModules.pushforward.{t} φ ⋙
      SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ))

/-- **Stacks 06WX, part (2).** Direct image along a 1-morphism of categories fibred in
groupoids carries injective sheaves of modules to injective sheaves of modules: any functor `G`
right adjoint to the inverse image of modules preserves injective objects.

`G` is the direct image of sheaves of modules; its existence is Stacks 06X0 and is taken as the
hypothesis `adj` rather than constructed, so that the statement is about whichever functor is
adjoint to the inverse image. -/
@[stacks 06WX "part (2)"]
theorem preservesInjectiveObjects_of_adjunction_sheafOfModules_pushforward
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology)
    (G : letI : p.IsFibered := hp.isFibered
      SheafOfModules.{t} (ringStructureSheafCore B S hS p hp τ hτ) ⥤
        SheafOfModules.{t} (ringStructureSheafCore B S hS q hq τ hτ))
    (adj : letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
        (τ.over (B.obj hS))).1
      SheafOfModules.pushforward.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ) ⊣ G) :
    G.PreservesInjectiveObjects := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let := preservesFiniteLimits_sheafOfModules_pushforward.{u, v₁, v₂, w₁, w₂, t}
    B S hS p q F τ hp hq hcomp hτ
  exact preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits adj

add_to_stacks 06X1 "the adjunction f_! ⊣ f⁻¹"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

/-- **Stacks 06X1, part (1).** For a faithful 1-morphism of categories fibred in groupoids
whose source has equalizers, lower shriek `f_!` on abelian sheaves is exact.

Finite colimits are preserved because `f_!` is a left adjoint. Finite limits are preserved by
the criterion of Stacks 04BH: the source has fibre products (Stacks 06WY) and equalizers by
hypothesis, and `f` preserves both (Stacks 06WZ, in the form that places no constraint between
the universes of source and target). -/
@[stacks 06X1 "part (1)"]
theorem exact_sheafPullback_of_faithful
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    [F.Faithful] [HasEqualizers 𝒳]
    [∀ G : 𝒳ᵒᵖ ⥤ Ab.{t}, F.op.HasPointwiseLeftKanExtension G]
    [HasSheafify (associatedTopology B S hS q τ) Ab.{t}] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    exactFunctor _ _
      (Functor.sheafPullbackConstruction.sheafPullback F Ab.{t}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let : PreservesLimitsOfShape WalkingParallelPair F :=
    TwoFibreProductOver.preservesEqualizers_of_faithful p q F hp hq hcomp
  let : PreservesLimitsOfShape WalkingCospan F :=
    TwoFibreProductOver.preservesPullbacks_of_fibred p q F hp hq hcomp
  rw [exactFunctor_iff]
  exact ⟨Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits F _ _,
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits Ab.{t} F _ _⟩

/-- **Stacks 06X1, part (2).** The inverse image of an injective abelian sheaf is injective,
when the 1-morphism is faithful and its source has equalizers.

The inverse image is right adjoint to the exact functor `f_!` of part (1), which therefore
preserves monomorphisms. -/
@[stacks 06X1 "part (2)"]
theorem injective_sheafPushforwardContinuous_obj
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    [F.Faithful] [HasEqualizers 𝒳]
    [∀ G : 𝒳ᵒᵖ ⥤ Ab.{t}, F.op.HasPointwiseLeftKanExtension G]
    [HasSheafify (associatedTopology B S hS q τ) Ab.{t}]
    (I : Sheaf (associatedTopology B S hS q τ) Ab.{t}) [Injective I] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    Injective ((F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).obj I) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback F Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)) :=
    ((exactFunctor_iff _).mp
      (exact_sheafPullback_of_faithful B S hS p q F τ hp hq hcomp)).1
  let := preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ))
  exact Functor.injective_obj_of_injective _ (X := I) inferInstance

add_to_stacks 06X2 "the adjunction f_! ⊣ f^* on modules"
  SheafOfModules.instIsRightAdjointPushforward

/-- **Stacks 06X2.** Lower shriek on sheaves of modules agrees, on underlying abelian sheaves,
with lower shriek on abelian sheaves.

Both sides are computed by sheafifying a presheaf-level left adjoint, and at the presheaf level
the two agree because every slice functor of a 1-morphism of categories fibred in groupoids is
an equivalence: that is
`Stacks.ModuleLowerShriek.pullbackCompToPresheafIso`. Without the slice hypothesis the
statement is false, by `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`. -/
@[stacks 06X2 "underlying abelian sheaves"]
noncomputable def lowerShriekForgetIso
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology)
    (hPresheaf :
      letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
        (τ.over (B.obj hS))).1
      (PresheafOfModules.pushforward.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, F.op.HasPointwiseLeftKanExtension G]
    [HasWeakSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{t}]
    [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{t}] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI : (PresheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint := hPresheaf
    letI : (SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).IsRightAdjoint :=
      SheafOfModules.instIsRightAdjointPushforward _
    SheafOfModules.pullback.{t} (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ) ⋙
        SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS q hq τ hτ) ≅
      SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ) ⋙
        Functor.sheafPullbackConstruction.sheafPullback F AddCommGrpCat.{t}
          (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let (x : 𝒳) : (Over.post (X := x) F).IsEquivalence :=
    Functor.IsFiberedInGroupoids.isEquivalence_overPost_of_comp_eq hp hq hcomp x
  let K := associatedTopology B S hS q τ
  let RX := ringStructureSheafCore B S hS p hp τ hτ
  let RY := ringStructureSheafCore B S hS q hq τ hτ
  let φ := ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ
  let : (PresheafOfModules.pushforward.{t} φ.hom).IsRightAdjoint := hPresheaf
  let : (SheafOfModules.pushforward.{t} φ).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward _
  cases hcomp
  let : (PresheafOfModules.pushforward.{t} (F := F) (𝟙 (F.op ⋙ RY.obj))).IsRightAdjoint :=
    hPresheaf
  have e : PresheafOfModules.pullback.{t} φ.hom ⋙ PresheafOfModules.toPresheaf RY.obj ≅
      PresheafOfModules.toPresheaf RX.obj ⋙ F.op.lan := by
    change PresheafOfModules.pullback.{t} (F := F) (𝟙 (F.op ⋙ RY.obj)) ⋙
      PresheafOfModules.toPresheaf RY.obj ≅
        PresheafOfModules.toPresheaf (F.op ⋙ RY.obj) ⋙ F.op.lan
    exact Stacks.ModuleLowerShriek.pullbackCompToPresheafIso F RY.obj
  calc
    _ ≅ SheafOfModules.forget RX ⋙ PresheafOfModules.pullback.{t} φ.hom ⋙
        PresheafOfModules.toPresheaf RY.obj ⋙ presheafToSheaf K AddCommGrpCat.{t} :=
      Functor.isoWhiskerRight (SheafOfModules.pullbackIso φ) _
    _ ≅ SheafOfModules.forget RX ⋙ PresheafOfModules.toPresheaf RX.obj ⋙
        F.op.lan ⋙ presheafToSheaf K AddCommGrpCat.{t} :=
      Functor.isoWhiskerLeft (SheafOfModules.forget RX)
        (Functor.isoWhiskerRight e (presheafToSheaf K AddCommGrpCat.{t}))
    _ ≅ _ := Iso.refl _

/-- **Stacks 06X2, part (1).** For a faithful 1-morphism of categories fibred in groupoids
whose source has equalizers, lower shriek `f_!` on sheaves of modules is exact.

Finite colimits are preserved because `f_!` is a left adjoint. Finite limits are preserved
because `SheafOfModules.toSheaf` reflects them and, composed with `f_!`, is the abelian `f_!`
of Stacks 06X1 (1) up to `lowerShriekForgetIso`, which is exact. -/
@[stacks 06X2 "part (1)"]
theorem exact_sheafOfModules_pullback_of_faithful
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) [F.Faithful] [HasEqualizers 𝒳]
    (hPresheaf :
      letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
        (τ.over (B.obj hS))).1
      (PresheafOfModules.pushforward.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, F.op.HasPointwiseLeftKanExtension G]
    [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{t}]
    [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{t}] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI : (PresheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint := hPresheaf
    letI : (SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).IsRightAdjoint :=
      SheafOfModules.instIsRightAdjointPushforward _
    exactFunctor _ _
      (SheafOfModules.pullback.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let : (PresheafOfModules.pushforward.{t}
    (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint := hPresheaf
  let : (SheafOfModules.pushforward.{t}
    (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward _
  let M := SheafOfModules.pullback.{t} (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)
  let T := SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS p hp τ hτ)
  let T' := SheafOfModules.toSheaf.{t} (ringStructureSheafCore B S hS q hq τ hτ)
  let A := Functor.sheafPullbackConstruction.sheafPullback F AddCommGrpCat.{t}
    (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)
  have hForget : M ⋙ T' ≅ T ⋙ A := by
    simpa [M, T, T', A] using
      lowerShriekForgetIso B S hS p q F τ hp hq hcomp hτ hPresheaf
  let : PreservesFiniteLimits A :=
    ((exactFunctor_iff A).mp (exact_sheafPullback_of_faithful B S hS p q F τ hp hq hcomp)).1
  let : PreservesFiniteLimits (M ⋙ T') := preservesFiniteLimits_of_natIso hForget.symm
  let : PreservesColimits M :=
    (SheafOfModules.pullbackPushforwardAdjunction.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).leftAdjoint_preservesColimits
  exact (exactFunctor_iff _).mpr
    ⟨preservesFiniteLimits_of_reflects_of_preserves M T', inferInstance⟩

/-- **Stacks 06X2, part (2).** The inverse image of an injective sheaf of modules is
injective, when the 1-morphism is faithful and its source has equalizers.

The inverse image of modules is right adjoint to the exact functor `f_!` of part (1), which
therefore preserves monomorphisms. -/
@[stacks 06X2 "part (2)"]
theorem injective_sheafOfModules_pushforward_obj
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) [F.Faithful] [HasEqualizers 𝒳]
    (hPresheaf :
      letI : p.IsFibered := hp.isFibered
      letI : q.IsFibered := hq.isFibered
      letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
        (τ.over (B.obj hS))).1
      (PresheafOfModules.pushforward.{t}
        (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, F.op.HasPointwiseLeftKanExtension G]
    [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{t}]
    [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{t}]
    (I : SheafOfModules.{t} (ringStructureSheafCore B S hS q hq τ hτ)) [Injective I] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    Injective ((SheafOfModules.pushforward.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).obj I) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let : (PresheafOfModules.pushforward.{t}
    (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ).hom).IsRightAdjoint := hPresheaf
  let : (SheafOfModules.pushforward.{t}
    (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward _
  let M := SheafOfModules.pullback.{t} (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ)
  let : PreservesFiniteLimits M := ((exactFunctor_iff M).mp
    (exact_sheafOfModules_pullback_of_faithful B S hS p q F τ hp hq hcomp hτ hPresheaf)).1
  let := preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits
    (SheafOfModules.pullbackPushforwardAdjunction.{t}
      (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ))
  exact Functor.injective_obj_of_injective _ (X := I) inferInstance

/-! ### Stacks 06X1 for essentially small sites

The source works with categories in the sense of Stacks 0015, whose objects form a *set*, and
with abelian sheaves valued in the category of all abelian groups. In Lean the abelian groups are
`Ab.{t}` and the corresponding smallness of `𝒳` and `𝒴` is `EssentiallySmall.{t}`. It is
genuinely needed: the base `(Sch/S)_fppf` is essentially small
(`AlgebraicGeometry.essentiallySmallSchemes`), but a category fibred in groupoids over it may
have fibres with more than `t`-many isomorphism classes, and then the colimits defining `f_!` do
not exist in `Ab.{t}`.

For essentially small `𝒳` and `𝒴` the comma categories over which `f_{p!}` is computed are
essentially small (`CategoryTheory.CostructuredArrow.essentiallySmall`), so the pointwise left Kan
extensions exist (`CategoryTheory.Limits.hasColimitsOfShape_of_essentiallySmall`), and abelian
presheaves on `𝒴` sheafify (`CategoryTheory.hasSheafifyEssentiallySmallSite`). So the left
adjoint of `f⁻¹` is constructed here and not assumed, as in the source's proof through
Stacks 04BG. -/

/-- Pointwise left Kan extensions of abelian presheaves along `F.op` exist when `𝒳` and `𝒴` are
essentially small. -/
private theorem hasPointwiseLeftKanExtension_of_essentiallySmall
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] :
    ∀ G : 𝒳ᵒᵖ ⥤ Ab.{t}, F.op.HasPointwiseLeftKanExtension G := fun _ V => by
  have := hasColimitsOfShape_of_essentiallySmall.{t} (CostructuredArrow F.op V) Ab.{t}
  infer_instance

/-- **Stacks 06X1, the left adjoint.** For a 1-morphism `f` of categories fibred in groupoids
over the big fppf category of `S` and any topology `τ` on the underlying category of schemes,
the inverse image `f⁻¹ : Ab(𝒴_τ) ⥤ Ab(𝒳_τ)` has a left adjoint `f_!`.

The functor `f` is continuous for the associated topologies (Stacks 06NW). The pointwise left Kan
extensions along `f.op` exist because `𝒳` is essentially small and `𝒴` locally small, and
sheafification on `𝒴_τ` exists because `𝒴` is essentially small; so `f_!` is the sheafified
left Kan extension of Stacks 04BG,
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`. -/
@[stacks 06X1 "f⁻¹ has a left adjoint f_!"]
theorem isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    (F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).IsRightAdjoint := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  have := hasPointwiseLeftKanExtension_of_essentiallySmall.{v₁, v₂, w₁, w₂, t} F
  have : HasSheafify (associatedTopology B S hS q τ) Ab.{t} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, t} _ _
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{t}
    (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).isRightAdjoint

/-- **Stacks 06X1, part (1).** For a faithful 1-morphism of categories fibred in groupoids over
the big fppf category of `S` whose source has equalizers, the left adjoint `f_!` of the inverse
image `f⁻¹ : Ab(𝒴_τ) ⥤ Ab(𝒳_τ)` is exact, for any topology `τ` on the underlying category of
schemes.

The left adjoint is isomorphic to the sheafified left Kan extension, which is exact by
`AlgebraicGeometry.Stack.exact_sheafPullback_of_faithful` (Stacks 04BH, with the hypotheses of
that criterion supplied by Stacks 06WY and 06WZ); the pointwise Kan extensions and the
sheafification it uses exist by essential smallness of `𝒳` and `𝒴`. -/
@[stacks 06X1 "part (1)"]
theorem exact_leftAdjoint_sheafPushforwardContinuous_of_faithful
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    [F.Faithful] [HasEqualizers 𝒳] [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI : (F.sheafPushforwardContinuous Ab.{t}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).IsRightAdjoint :=
      isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall B S hS p q F τ hp hq hcomp
    exactFunctor _ _ (F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).leftAdjoint := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let : (F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).IsRightAdjoint :=
    isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall B S hS p q F τ hp hq hcomp
  have := hasPointwiseLeftKanExtension_of_essentiallySmall.{v₁, v₂, w₁, w₂, t} F
  have : HasSheafify (associatedTopology B S hS q τ) Ab.{t} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, t} _ _
  let e := (Adjunction.ofIsRightAdjoint (F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ))).leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ))
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp
    (exact_sheafPullback_of_faithful.{u, v₁, v₂, w₁, w₂, t} B S hS p q F τ hp hq hcomp)
  exact (exactFunctor_iff _).mpr
    ⟨preservesFiniteLimits_of_natIso e.symm, preservesFiniteColimits_of_natIso e.symm⟩

/-- **Stacks 06X1, part (2).** For a faithful 1-morphism of categories fibred in groupoids over
the big fppf category of `S` whose source has equalizers, the inverse image of an injective
abelian sheaf on `𝒴_τ` is an injective abelian sheaf on `𝒳_τ`, for any topology `τ` on the
underlying category of schemes.

The inverse image is right adjoint to the functor `f_!`, which is exact by part (1) and so
preserves monomorphisms (Stacks 015Z). -/
@[stacks 06X1 "part (2)"]
theorem injective_sheafPushforwardContinuous_obj_of_essentiallySmall
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    [F.Faithful] [HasEqualizers 𝒳] [EssentiallySmall.{t} 𝒳] [EssentiallySmall.{t} 𝒴]
    (I : Sheaf (associatedTopology B S hS q τ) Ab.{t}) [Injective I] :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    Injective ((F.sheafPushforwardContinuous Ab.{t}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).obj I) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let G := F.sheafPushforwardContinuous Ab.{t}
    (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)
  let : G.IsRightAdjoint :=
    isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall B S hS p q F τ hp hq hcomp
  let : PreservesFiniteLimits G.leftAdjoint := ((exactFunctor_iff _).mp
    (exact_leftAdjoint_sheafPushforwardContinuous_of_faithful B S hS p q F τ hp hq hcomp)).1
  let := preservesInjectiveObjects_of_adjunction_of_preservesFiniteLimits
    (Adjunction.ofIsRightAdjoint G)
  exact Functor.injective_obj_of_injective G (X := I) inferInstance

end AlgebraicGeometry.Stack

end
