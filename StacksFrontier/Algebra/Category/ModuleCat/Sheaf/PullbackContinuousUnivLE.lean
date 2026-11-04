module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of sheaves of modules has a left adjoint, at independent universes

Let `F : C ⥤ D` be a continuous functor of sites, let `R` and `S` be sheaves of rings on
`(D, K)` and on `(C, J)`, and let `φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`
be a morphism of sheaves of rings. Mathlib's `SheafOfModules.pullback φ` and
`SheafOfModules.pullbackPushforwardAdjunction φ` are the left adjoint of
`SheafOfModules.pushforward φ` and the adjunction, available under the typeclass
`(SheafOfModules.pushforward φ).IsRightAdjoint`, and Mathlib discharges that typeclass from
the presheaf-level `(PresheafOfModules.pushforward φ.hom).IsRightAdjoint` together with the
two sheafification hypotheses on the target site.

This file discharges both typeclasses with the universes of the two sites, of their
morphisms, of the sheaves of rings and of the module sections **mutually independent**, using
`PresheafOfModules.isRightAdjoint_pushforward_of_univLE`. It is the independent-universe form
of `Stacks.Sheaves.ModuleAdjunction.presheafPushforward_isRightAdjoint` and
`.pushforward_isRightAdjoint`, which are stated for two `SmallCategory` sites whose objects,
morphisms, rings and module sections all lie in one universe.

## Main results

* `SheafOfModules.presheafPushforward_isRightAdjoint_of_univLE`: the presheaf-level instance,
  at the shape the sheaf-level instance resolves against.
* `SheafOfModules.pushforward_isRightAdjoint_of_univLE`: pushforward of sheaves of modules has
  a left adjoint.
* `SheafOfModules.pullbackPushforwardAdjunctionUnivLE`: the resulting adjunction, with no
  adjointness hypothesis.

## Implementation notes

The presheaf-level instance is restated here rather than being left to instance search, and
this is not redundant: the goal `(PresheafOfModules.pushforward φ.hom).IsRightAdjoint` arising
from Mathlib's sheaf-level instance does not unify with the conclusion of
`PresheafOfModules.isRightAdjoint_pushforward_of_univLE`, whose implicit functor and
presheaves of rings would have to be read off the type of `φ.hom` — and
`((F.sheafPushforwardContinuous RingCat J K).obj R).val` is not syntactically `F.op ⋙ R.val`.
Supplying the instance with its type ascribed pins those implicit arguments, after which the
body elaborates. `Stacks.Sheaves.ModuleAdjunction` performs exactly the same step for small
sites, for the same reason. The module universe of the presheaf-level result must be pinned by
a `.{v}` application and not left to unification: its smallness hypotheses are elaborated
first, and `Small.small_max` then assigns the module universe `max r ?u` with `?u`
unconstrained, after which the result type no longer unifies.

The smallness hypotheses are stated as `UnivLE`, not as the `Small` and `LocallySmall`
statements that `PresheafOfModules.isRightAdjoint_pushforward_of_univLE` takes. That is also
forced rather than stylistic: the presheaf of rings that instance search reads off `φ.hom` is
`(sheafToPresheaf K RingCat).obj R`, not `R.val`, so a hypothesis written at `R.val` is not
the one the goal asks for, whereas `UnivLE.{r, v}` supplies `Small.{v}` for every type in the
ring universe however it is spelled.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

universe v w u w' u' r

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K]
  {R : Sheaf K RingCat.{r}} {S : Sheaf J RingCat.{r}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
  [UnivLE.{r, v}] [UnivLE.{w, v}] [UnivLE.{w', v}] [UnivLE.{u, v}]

/-- **Pushforward of presheaves of modules along a continuous functor of sites has a left
adjoint**, at the shape Mathlib's sheaf-level instance resolves against, and with the
universes of the two sites, of their morphisms, of the sheaves of rings and of the module
sections independent. -/
instance presheafPushforward_isRightAdjoint_of_univLE :
    (PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{v} φ.hom

variable [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Pushforward of sheaves of modules along a continuous functor of sites and a morphism of
sheaves of rings always has a left adjoint**, with the universes of the two sites, of their
morphisms, of the sheaves of rings and of the module sections independent. -/
instance pushforward_isRightAdjoint_of_univLE :
    (SheafOfModules.pushforward.{v} φ).IsRightAdjoint :=
  inferInstance

/-- **Stacks 03D7**, with the universes of the two sites, of their morphisms, of the sheaves
of rings and of the module sections independent: for a continuous functor of sites and a
morphism of sheaves of rings, pullback of sheaves of modules is left adjoint to pushforward.
The adjunction supplies the natural bijection between morphisms out of a pullback and
morphisms into a pushforward. -/
@[stacks 03D7 "ringed sites, at independent universes"]
def pullbackPushforwardAdjunctionUnivLE :
    SheafOfModules.pullback.{v} φ ⊣ SheafOfModules.pushforward.{v} φ :=
  SheafOfModules.pullbackPushforwardAdjunction.{v} φ

end SheafOfModules

namespace CategoryTheory

/-- A slice category is `v`-small as soon as its base is `v`-small and locally `v`-small: an
object of `C/U` is an object of `C` together with a morphism to `U`. The objects of `C/U` lie
in `max u w` for a site `C : Type u` with `Category.{w} C`, so this does not follow from
`Small.{v} C` alone, and it is what makes the coproducts indexing extension by zero exist. -/
instance small_over {C : Type u} [Category.{w} C] (U : C) [Small.{v} C] [LocallySmall.{v} C] :
    Small.{v} (Over U) :=
  small_of_surjective (f := fun p : Σ X : C, (X ⟶ U) ↦ Over.mk p.2)
    (fun A ↦ ⟨⟨A.left, A.hom⟩, rfl⟩)

/-- A slice category is locally `v`-small as soon as its base is: a morphism of `C/U` is a
morphism of `C` together with a commutation property. -/
instance locallySmall_over {C : Type u} [Category.{w} C] (U : C) [LocallySmall.{v} C] :
    LocallySmall.{v} (Over U) :=
  ⟨fun _ _ ↦ small_of_injective (f := fun f ↦ f.left) (fun _ _ h ↦ Over.OverMorphism.ext h)⟩

end CategoryTheory

namespace Stacks.Sites.ExtensionByZero

open CategoryTheory.Limits

variable {C : Type u} [Category.{w} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{r})
  (U : C) [UnivLE.{r, v}] [UnivLE.{w, v}] [UnivLE.{u, v}]

/-- **Restriction of presheaves of modules along `Over.forget U` has a left adjoint**, with
the universes of the site, of its morphisms, of the sheaves of rings and of the module
sections independent. Stated with the morphism of presheaves of rings spelled as the identity
of `R.over U`, which is the form the extension-by-zero declarations and Stacks 07AC ask for;
`Stacks.Sites.ExtensionByZero.presheafRestrictionIsRightAdjoint` is the same statement for a
site that is small in the universe of the module sections. -/
instance presheafRestrictionIsRightAdjoint_of_univLE :
    (PresheafOfModules.pushforward.{v} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{v}
    (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Restriction of sheaves of modules along `Over.forget U` has a left adjoint**, namely
extension by zero, with the universes of the site, of its morphisms, of the sheaves of rings
and of the module sections independent. This is the instance hypothesis that Stacks 07AC's
existence theorem
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic` carries
for the slices of its source site. -/
instance sheafRestrictionIsRightAdjoint_of_univLE :
    (SheafOfModules.pushforward.{v} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint :=
  have := presheafRestrictionIsRightAdjoint_of_univLE.{v} J R U
  (SheafOfModules.PullbackConstruction.adjunction.{v}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).isRightAdjoint

end Stacks.Sites.ExtensionByZero

end
