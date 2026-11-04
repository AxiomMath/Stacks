module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact

/-!
# Sheafification of presheaves of modules over a ring

Sheaves of `Λ`-modules, for `Λ` a ring which need not be commutative, come with side conditions
that must be discharged before the lift of an additive functor on abelian sheaves can be read on
them: presheaves of `Λ`-modules must admit sheafification, and postcomposition with the forgetful
functor to abelian groups must both carry sheaves to sheaves and commute with sheafification.
This file supplies all of them for an arbitrary ring, commutative or not, under the single
universe inequality `UnivLE.{max u v, w}` relating the module universe `w` to the site.

## Main results

* `Stacks.ModuleSheaf.hasSheafCompose_forget₂`: postcomposition with
  `forget₂ (ModuleCat Λ) AddCommGrpCat` carries sheaves to sheaves.
* `Stacks.ModuleSheaf.hasSheafify_addCommGrpCat`: presheaves of abelian groups admit
  sheafification, together with its left exactness.
* `Stacks.ModuleSheaf.hasSheafify_moduleCat` and
  `Stacks.ModuleSheaf.hasSheafify_over_moduleCat`: presheaves of `Λ`-modules admit
  sheafification, together with its left exactness, for a topology and for the localized
  topology on a slice site.
* `Stacks.ModuleSheaf.preservesSheafification_forget₂`: postcomposition with
  `forget₂ (ModuleCat Λ) AddCommGrpCat` commutes with sheafification.

## Implementation notes

The forgetful functor of `Λ`-modules preserves limits of every size the site can present, which
is `ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize` under the universe inequality
`UnivLE.{max u v, w}`; that is all `hasSheafCompose_of_preservesLimitsOfSize` consumes. The
hypothesis is satisfied in the case this is built for, where the site and the modules live in
the same universe.

The companion condition `GrothendieckTopology.PreservesSheafification` is *not* obtained from
`preservesSheafification_of_adjunction`: that route needs
`(forget₂ (ModuleCat Λ) AddCommGrpCat).IsLeftAdjoint`, which Mathlib has only for `Λ = ℤ`, where
the functor is half of an equivalence. For a general ring the right adjoint is coextension of
scalars along `ℤ → Λ`, and Mathlib's `ModuleCat.restrictCoextendScalarsAdj` is stated at module
universe `max r w`, so it cannot be read at `ModuleCat.{w} Λ` for an unconstrained `w`. Instead
the functor is fed to `GrothendieckTopology.instPreservesSheafification`, which asks only that
both value categories have the limits and colimits the site presents and that the functor, and
the two forgetful functors to types, preserve them. The three pieces instance search does not
find on its own are supplied by hand: `ModuleCat.hasLimitsOfSize` and
`Limits.preservesFilteredColimitsOfSize_of_univLE` are lemmas rather than instances, and
`hasSheafCompose_forget₂` above is a theorem. The same colimit computation is what makes
sheafification itself available, so `hasSheafify_moduleCat` shares the two
`preservesColimitsOfShape_forget_*` steps.

None of the three sheafification statements can be found by instance search, and they are not
redundant with Mathlib: each rests on `preservesColimitsOfShape_forget_addCommGrp`, which is a
theorem rather than an instance because the size shrink it performs,
`Limits.preservesFilteredColimitsOfSize_of_univLE`, is itself a lemma that instance search will
not apply. So `HasSheafify J AddCommGrpCat` has to be applied by name, and
`hasSheafify_addCommGrpCat` is recorded for that purpose rather than re-derived at each use.

Nothing here carries a `stacks` attribute: these are side conditions of a construction that is
tagged elsewhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u v

namespace Stacks.ModuleSheaf

variable (Λ : Type r) [Ring Λ] {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Postcomposition with the forgetful functor from `Λ`-modules to abelian groups carries
sheaves to sheaves: the functor preserves limits of every size the site can present. -/
public theorem hasSheafCompose_forget₂ [UnivLE.{max u v, w}] :
    J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  hasSheafCompose_of_preservesLimitsOfSize (J := J)
    (F := forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

/-- The forgetful functor of abelian groups commutes with the colimits over the covers of a
site. -/
public theorem preservesColimitsOfShape_forget_addCommGrp [UnivLE.{max u v, w}] (Y : C) :
    PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{w}) := by
  have : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  infer_instance

/-- Sheafification of presheaves of abelian groups, together with its left exactness. -/
alias hasSheafify_addCommGrpCat := CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat

/-- The forgetful functor of `Λ`-modules commutes with the colimits over the covers of a site. -/
public theorem preservesColimitsOfShape_forget_moduleCat [UnivLE.{max u v, w}] (Y : C) :
    PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{w} Λ)) := by
  have := preservesColimitsOfShape_forget_addCommGrp.{w} J Y
  exact comp_preservesColimitsOfShape
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) (forget AddCommGrpCat.{w})

/-- Sheafification of presheaves of `Λ`-modules, together with its left exactness. -/
public theorem hasSheafify_moduleCat [UnivLE.{max u v, w}] :
    HasSheafify J (ModuleCat.{w} Λ) := by
  have h : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{w} Λ)) :=
    fun Y => preservesColimitsOfShape_forget_moduleCat Λ J Y
  exact HasSheafify.mk' J (ModuleCat.{w} Λ) (plusPlusAdjunction J (ModuleCat.{w} Λ))

/-- Sheafification of presheaves of `Λ`-modules for the localized topology on a slice site. -/
public theorem hasSheafify_over_moduleCat [UnivLE.{max u v, w}] (Y : C) :
    HasSheafify (J.over Y) (ModuleCat.{w} Λ) :=
  hasSheafify_moduleCat Λ (J.over Y)

/-- Postcomposition with the forgetful functor from `Λ`-modules to abelian groups commutes with
sheafification. -/
public theorem preservesSheafification_forget₂ [UnivLE.{max u v, w}] :
    J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) := by
  have hlim : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{w} Λ) := ModuleCat.hasLimitsOfSize
  have hsc := hasSheafCompose_forget₂.{w} Λ J
  have hA : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{w}) :=
    fun Y => preservesColimitsOfShape_forget_addCommGrp.{w} J Y
  have hM : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{w} Λ)) :=
    fun Y => preservesColimitsOfShape_forget_moduleCat Λ J Y
  exact GrothendieckTopology.instPreservesSheafification J
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

end Stacks.ModuleSheaf

end
