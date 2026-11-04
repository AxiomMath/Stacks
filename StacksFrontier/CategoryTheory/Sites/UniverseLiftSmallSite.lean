module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
import all StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits

/-!
# The universe lift of abelian sheaves on a small site

Raising the universe of the sections of a sheaf of abelian groups is
`CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor`.  This file collects what is needed
to run a homological comparison across it on a **small** site: that it is exact in the shape
`CategoryTheory.Abelian.Ext.mapExactFunctor` asks for, that it preserves injective objects, and
that it carries the constant sheaf on `ULift ℤ` — the object sheaf cohomology is an `Ext` out of
— to the constant sheaf on `ULift ℤ` at the larger universe.

Smallness is not a restriction in practice: the base's
`Stacks.Cohomology.CoefficientLift.sheafCompose_preservesInjectives_of_restriction` carries the
conclusion from a small dense subsite to the site itself, which is how the large sites of this
development are reached.

`StacksFrontier/CategoryTheory/Sites/UniverseLiftInjective.lean` proves preservation of injective
objects by a different route — Baer's criterion at a separator which is itself a universe lift
— and neither subsumes the other: that route asks for such a separator, which its own
implementation notes observe needs the site to be small relative to the smaller coefficient
universe, whereas this one asks only for a small dense subsite.

Preservation of injective objects is the only step with content.  On a small site it is
`AlgebraicGeometry.Space.sheafCompose_preservesInjectiveObjects`, together with
`AlgebraicGeometry.Space.ab_ulift_preservesInjectiveObjects` and
`AlgebraicGeometry.Space.ulift_preservesSheafification`, all three `private` to
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleCohomologyFilteredColimits.lean` and reached here
by `import all` rather than restated.  Exactness of the lift is
`CategoryTheory.preservesColimitsOfShape_sheafCompose` and
`SheafOfModules.preservesLimitsOfShape_sheafCompose_uliftFunctor`.

## Main definitions

* `Stacks.Sheaves.UniverseLift.constantSheafUliftIso`: the constant sheaf on `ULift ℤ` at a
  large coefficient universe is the universe lift of the constant sheaf on `ULift ℤ` at the
  small one.

## Main results

* `Stacks.Sheaves.UniverseLift.sheafUlift_properties_of_small_subsite`: on a site with a small
  dense subsite the universe lift is compatible with sheafification and preserves injective
  objects.
* `Stacks.Sheaves.UniverseLift.largeAbSheafify`: sheafification of abelian groups above the
  universe of a small site.

## Implementation notes

None of these is registered as an instance, for the reason given in
`StacksFrontier/CategoryTheory/Sites/UniverseLiftColimits.lean`: they are general statements about
`AddCommGrpCat.uliftFunctor` and about `CategoryTheory.sheafCompose`, and letting instance
search use them would make it try the universe lift on every injectivity, limit and
sheafification goal in the library.  They are used through `have` at the point of use.

`AlgebraicGeometry.Space.ulift_preservesSheafification` and
`Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor` of
`StacksFrontier/CategoryTheory/Sites/UniverseLiftColimits.lean` prove the same compatibility from
different hypotheses — smallness of the site there, and local bijectivity of the maps
sheafification inverts in the latter — so neither subsumes the other.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a b w u v

namespace Stacks.Sheaves.UniverseLift

/-- Presheaves of abelian groups whose sections lie above the universe of a small site admit a
left exact sheafification. -/
theorem largeAbSheafify {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{max u w} :=
  have _ : EssentiallySmall.{max u w} C := essentiallySmall_lift.{w, u} C
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u w, u, u} J

attribute [local instance] largeAbSheafify

/-- **Universe lifting of abelian groups on a site with a small dense subsite is compatible with
sheafification and preserves injective objects.**  Both statements are proved on the small
subsite, where the site is small enough for
`AlgebraicGeometry.Space.sheafCompose_preservesInjectiveObjects` to apply, and transported
along the restriction, which is an equivalence on sheaves at either coefficient universe. -/
lemma sheafUlift_properties_of_small_subsite
    {C : Type u} [SmallCategory C] {D : Type*} [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (i : C ⥤ D) [i.Full] [i.IsCoverDense K] [i.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{max u w}]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsEquivalence]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).IsEquivalence] :
    K.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} ∧
      (sheafCompose K AddCommGrpCat.uliftFunctor.{w, u}).PreservesInjectiveObjects := by
  have : HasLimitsOfSize.{u, u} AddCommGrpCat.{max u w} :=
    hasLimitsOfSizeShrink.{u, u, max u w, max u w} _
  have hGA : IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u}) := inferInstance
  have : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) := hGA.enoughInjectives
  have : J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} :=
    AlgebraicGeometry.Space.ulift_preservesSheafification J
  have : AddCommGrpCat.uliftFunctor.{w, u}.PreservesInjectiveObjects :=
    AlgebraicGeometry.Space.ab_ulift_preservesInjectiveObjects
  have : (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u}).PreservesInjectiveObjects :=
    AlgebraicGeometry.Space.sheafCompose_preservesInjectiveObjects J _
  exact ⟨GrothendieckTopology.PreservesSheafification.transport K J i _ _,
    Stacks.Cohomology.CoefficientLift.sheafCompose_preservesInjectives_of_restriction J K i _⟩

/-- The constant sheaf on `ULift ℤ` at a large coefficient universe is the universe lift of the
constant sheaf on `ULift ℤ` at the small one.  This is the object sheaf cohomology is an `Ext`
out of, so it is what lets a cohomology comparison cross the universe lift. -/
noncomputable def constantSheafUliftIso
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify J AddCommGrpCat.{max a b}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{b, a}] :
    (constantSheaf J AddCommGrpCat.{max a b}).obj
        (AddCommGrpCat.of (ULift.{max a b} ℤ)) ≅
      (sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).obj
        ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) :=
  have e : AddCommGrpCat.of (ULift.{max a b} ℤ) ≅
      AddCommGrpCat.uliftFunctor.{b, a}.obj (AddCommGrpCat.of (ULift.{a} ℤ)) :=
    AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ ⟨⟨x.down⟩⟩
        invFun := fun x ↦ ⟨x.down.down⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  (constantSheaf J AddCommGrpCat.{max a b}).mapIso e ≪≫
    (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{b, a}
      (sheafificationAdjunction J AddCommGrpCat.{a})
      (sheafificationAdjunction J AddCommGrpCat.{max a b})).app
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{a} ℤ)))

end Stacks.Sheaves.UniverseLift

end
