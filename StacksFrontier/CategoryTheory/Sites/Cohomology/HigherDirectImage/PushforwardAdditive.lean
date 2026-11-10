module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the direct image and of taking sections

The direct image of sheaves of modules along a morphism of ring sheaves over a continuous
functor, and the cohomology functor whose right derived functors compute the cohomology presheaf
of a higher direct image, are both additive: addition of morphisms of sheaves of modules is
computed sectionwise and both functors act sectionwise. Recording this as instances is what makes
the right derived functors — the higher direct images — available without an additivity
hypothesis.

The same two sentences prove the corresponding fact for the direct image of abelian sheaves along
a continuous functor. It is stated here as a theorem rather than an instance, because the files
that need it activate it with `attribute [local instance]` and do not want it in the library's
global instance set. The companion fact about sections over an object is not stated here; see the
comment below.

## Main results

* `CategoryTheory.SheafOfModules.pushforward_additive`
* `cohFunctor_additive`
* `Stacks.Cohomology.HigherDirectImage.sheafPushforwardContinuous_additive`

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ uRing uMod a b d

namespace Stacks.Cohomology.HigherDirectImage

/- **The sections fact is NOT stated here, because the library already has it more generally.**
`CategoryTheory.sheafSections_additive`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/MayerVietoris/CanonicalMapOfASquare.lean:121`) is a
GLOBAL INSTANCE for an arbitrary `[Category.{w} C]`, an arbitrary preadditive target and an
arbitrary `X : Cᵒᵖ`, with the same one-line `rfl` proof; a copy restricted to `SmallCategory C`,
to `Ab`, and to an `X` of the form `op U` is its specialisation and had no users, so it is gone.

There is deliberately no `example ... := inferInstance` certifying the specialisation here: that
general instance is NOT in this module's import closure. Elaborating the `example` fails with
    error(lean.synthInstanceFailed): failed to synthesize
      ((sheafSections J Ab).obj (Opposite.op U)).Additive
and this module has a single import while
`StacksFrontier/CategoryTheory/Sites/Cohomology/MayerVietoris/CanonicalMapOfASquare.lean` has
thirteen and does not import this one. Making the general form usable everywhere therefore means
relocating it to a
module both can see, which changes the global instance set for every module that gains it. -/

/-- The direct image of abelian sheaves along a continuous functor is additive: it does not
change the underlying presheaf, and addition of morphisms of sheaves is sectionwise.

Activate it where it is needed with `attribute [local instance]`. -/
@[ega "0 12.2.1" "partial"]
public theorem sheafPushforwardContinuous_additive {C : Type a} {D : Type d} [SmallCategory C]
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : D ⥤ C)
    [u.IsContinuous K J] : (u.sheafPushforwardContinuous (Ab.{b}) K J).Additive where
  map_add := by intros; rfl

end Stacks.Cohomology.HigherDirectImage

variable {Dsite : Type u₁} [Category.{v₁} Dsite] {Csite : Type u₂} [Category.{v₂} Csite]
  {J𝒟 : GrothendieckTopology Dsite} {J𝒞 : GrothendieckTopology Csite}
  (u : Dsite ⥤ Csite) [u.IsContinuous J𝒟 J𝒞]
  (O𝒞 : Sheaf J𝒞 RingCat.{uRing}) (O𝒟 : Sheaf J𝒟 RingCat.{uRing})
  (φ : O𝒟 ⟶ (u.sheafPushforwardContinuous RingCat.{uRing} J𝒟 J𝒞).obj O𝒞)
  [HasSheafify J𝒟 AddCommGrpCat.{uMod}] [J𝒟.WEqualsLocallyBijective AddCommGrpCat.{uMod}]
  [HasSheafify J𝒞 AddCommGrpCat.{uMod}] [J𝒞.WEqualsLocallyBijective AddCommGrpCat.{uMod}]

namespace CategoryTheory.SheafOfModules

/-- The direct image of sheaves of modules is additive: it does not change the underlying
presheaf, and addition of morphisms of sheaves of modules is sectionwise. -/
public instance pushforward_additive :
    (SheafOfModules.pushforward.{uMod} φ).Additive where
  map_add := by intros; rfl

end CategoryTheory.SheafOfModules

/-- The functor computing the cohomology presheaf of a higher direct image is additive, for the
same reason as the direct image itself: it acts sectionwise. -/
public instance cohFunctor_additive :
    (cohFunctor.{v₁, u₁, v₂, u₂, uRing, uMod} u O𝒞 O𝒟 φ).Additive where
  map_add := by intros; rfl

end
