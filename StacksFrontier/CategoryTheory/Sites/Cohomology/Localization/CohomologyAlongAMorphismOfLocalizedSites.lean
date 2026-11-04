module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology along a morphism of localized sites

Let `(C, J)` be a site and `f : X ⟶ Y` a morphism of `C`. Composing with `f` is a continuous and
cocontinuous functor `Over.map f : C/X ⥤ C/Y` for the localized topologies, whose direct image on
abelian sheaves is the restriction `J.overMapPullback A f : Ab(C/Y) ⥤ Ab(C/X)`. This file proves
that that restriction is exact and preserves injective objects, and deduces

`H^p_{C/X}(V, F|_X) ≅ H^p_{C/Y}((Over.map f) V, F)`

for `V` an object of `C/X` and `F` an abelian sheaf on `C/Y`, naturally in `F`, assuming only
sheafification on the localized sites and `UnivLE.{max u v, w}`. This is the analogue for
`Over.map f` of `Stacks.Cohomology.LocalizedSite.overPullbackRightDerivedSectionsIso`, which is
stated for `Over.forget X : C/X ⥤ C`.

## Main results

All in the namespace `Stacks.Cohomology.LocalizedSite`.

* `preservesFiniteLimits_overMapExtensionByZero`: extension by zero along `Over.map f` is left
  exact.
* `preservesInjectiveObjects_overMapPullback`: restriction along a morphism of localized sites
  preserves injective abelian sheaves.
* `preservesFiniteColimits_overMapPullback_of_univLE`: that restriction is right exact, under
  `UnivLE.{max u v, w}` in place of the hypothesis `(J.over Y).WEqualsLocallyBijective Ab.{w}` of
  `preservesFiniteColimits_overMapPullback`.
* `overMapPullbackRightDerivedSheafToPresheafIso`,
  `overMapPullbackRightDerivedSectionsIso`: the cohomology comparison, as presheaves on `C/X`
  and objectwise.

## Implementation notes

`preservesMonomorphisms_of_preservesLimitsOfShape` is applied by name rather than found by instance
search, which would select an unproved `PreservesMonomorphisms` instance for the left adjoint of a
restriction (see `Stacks.Injectives.extensionByZero_preservesMonos`).

## References

* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.LocalizedSite

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max u v, w}] [∀ U : C, HasSheafify (J.over U) Ab.{w}]

/-- **Extension by zero along a morphism of localized sites is left exact**: the left adjoint
`(Over.map f).sheafPullback` of the restriction `J.overMapPullback Ab f` preserves finite
limits. -/
theorem preservesFiniteLimits_overMapExtensionByZero {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{w} (J.over X) (J.over Y)) := by
  let G := Over.map f
  let adj := G.sheafAdjunctionContinuous Ab.{w} (J.over X) (J.over Y)
  let adjLan := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{w}
    (J.over X) (J.over Y)
  let : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback G Ab.{w} (J.over X) (J.over Y)) := by
    dsimp only [Functor.sheafPullbackConstruction.sheafPullback]
    let : PreservesFiniteLimits ((Over.map f).op.lan :
        ((Over X)ᵒᵖ ⥤ Ab.{w}) ⥤ (Over Y)ᵒᵖ ⥤ Ab.{w}) :=
      Stacks.Cohomology.Localization.preservesFiniteLimits_overMap_op_lan f
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq adj adjLan).symm

/-- **Restriction of abelian sheaves along a morphism of localized sites preserves injective
objects** ([Stacks, Tag 015Z]): its left adjoint is extension by zero, which is left exact
([Stacks, Tag 01DR]), hence preserves monomorphisms. -/
@[sga "4 V 2.2" "special case"]
theorem preservesInjectiveObjects_overMapPullback {X Y : C} (f : X ⟶ Y) :
    (J.overMapPullback Ab.{w} f).PreservesInjectiveObjects := by
  let : PreservesFiniteLimits ((Over.map f).sheafPullback Ab.{w} (J.over X) (J.over Y)) :=
    preservesFiniteLimits_overMapExtensionByZero J f
  let : ((Over.map f).sheafPullback Ab.{w} (J.over X) (J.over Y)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact preservesInjectiveObjects_pushforwardOfContinuous Ab.{w} (Over.map f)

omit [∀ U : C, HasSheafify (J.over U) Ab.{w}] in
/-- **Restriction of abelian sheaves along a morphism of localized sites is right exact**, under
`UnivLE.{max u v, w}` (where `preservesFiniteColimits_overMapPullback` assumes
`(J.over Y).WEqualsLocallyBijective Ab.{w}`). -/
@[sga "4 I 5.8.3" "Clause 1, special case"]
theorem preservesFiniteColimits_overMapPullback_of_univLE {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteColimits (J.overMapPullback Ab.{w} f) :=
  preservesFiniteColimits_pushforwardOfContinuous Ab.{w} (Over.map f)

/-- **The cohomology presheaf of a sheaf restricted along a morphism of localized sites.** For
every `p`, `(-)|_X ⋙ R^p Γ_{C/X} ≅ R^p Γ_{C/Y} ⋙ (- ∘ (Over.map f).op)`, an isomorphism of
functors into presheaves on `C/X`, hence natural in the object as well as in the sheaf. -/
def overMapPullbackRightDerivedSheafToPresheafIso {X Y : C} (f : X ⟶ Y)
    [EnoughInjectives (Sheaf (J.over X) Ab.{w})]
    [EnoughInjectives (Sheaf (J.over Y) Ab.{w})] (p : ℕ) :
    J.overMapPullback Ab.{w} f ⋙ (sheafToPresheaf (J.over X) Ab.{w}).rightDerived p ≅
      (sheafToPresheaf (J.over Y) Ab.{w}).rightDerived p ⋙
        (Functor.whiskeringLeft (Over X)ᵒᵖ (Over Y)ᵒᵖ Ab.{w}).obj (Over.map f).op :=
  haveI := preservesFiniteColimits_overMapPullback_of_univLE J f
  haveI := preservesInjectiveObjects_overMapPullback J f
  pushforwardRightDerivedSheafToPresheafIso Ab.{w} (Over.map f) p

/-- **Cohomology along a morphism of localized sites, objectwise.** For `V` an object of `C/X`,
the cohomology over `V` of the restriction of `F` along `Over.map f` is the cohomology of `F` over
`(Over.map f) V`, naturally in `F`. -/
def overMapPullbackRightDerivedSectionsIso {X Y : C} (f : X ⟶ Y)
    [EnoughInjectives (Sheaf (J.over X) Ab.{w})]
    [EnoughInjectives (Sheaf (J.over Y) Ab.{w})] (p : ℕ) (V : Over X) :
    J.overMapPullback Ab.{w} f ⋙
        (sheafToPresheaf (J.over X) Ab.{w} ⋙
          (evaluation (Over X)ᵒᵖ Ab.{w}).obj (op V)).rightDerived p ≅
      (sheafToPresheaf (J.over Y) Ab.{w} ⋙
        (evaluation (Over Y)ᵒᵖ Ab.{w}).obj (op ((Over.map f).obj V))).rightDerived p :=
  haveI := preservesFiniteColimits_overMapPullback_of_univLE J f
  haveI := preservesInjectiveObjects_overMapPullback J f
  pushforwardRightDerivedSectionsIso Ab.{w} (Over.map f) p V

end Stacks.Cohomology.LocalizedSite

end
