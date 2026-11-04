module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Global cohomology along an equivalence of sites, at independent morphism universes

Let `G : C ⥤ D` be a continuous and cocontinuous functor of sites whose restriction functor
`g⁻¹ = G.sheafPushforwardContinuous` on abelian sheaves is an *equivalence*.  Then restriction
along `G` does not change global sheaf cohomology:

`g⁻¹ ⋙ H^p(C, -) ≅ H^p(D, -)`,

naturally in the abelian sheaf on `(D, K)`.

This is the statement of
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` with **the morphism
universes of the two sites untied**: there the two sites are `C D : Type u` with `Category.{v}`
for one and the same `v`, here they are `Category.{v}` and `Category.{v'}`.  Only the *object*
universe has to be shared, and it has to be shared because the comparison is proved by
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`, which needs the two abelian
categories to have their morphisms in one universe: those of `Sheaf J AddCommGrpCat.{w}` live in
`max u w`, which involves the object universe of the site and the coefficient universe but not
the morphism universe of the site.

The generality is what a *small model* of a site needs.  `CategoryTheory.AsSmall` of a category
with objects in `Type u` and morphisms in `Type v` has both in `Type (max u v)`, so a site and
its small model do not have their morphism universes in one universe, while their sheaf
categories do share their morphism universe and the two cohomologies agree.

## Main definitions

* `Stacks.Cohomology.SiteEquivalenceGlobal.inverseConstantSheafIso` — the degree-zero datum
  `g⁻¹^{-1} ℤ_C ≅ ℤ_D` obtained, when `g⁻¹` is an equivalence, from
  `Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`, which holds at independent
  universes.

## Main results

* `Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence` — **restriction
  along a continuous and cocontinuous functor whose restriction of abelian sheaves is an
  equivalence does not change global cohomology**, in every degree, at independent site morphism
  universes.
* `Stacks.Cohomology.SiteEquivalenceGlobal.sheafHAddEquivOfIsEquivalence` — the same at a fixed
  abelian sheaf, as an additive equivalence of the cohomology groups.

## What is and is not proved

No tag attribute is placed.  [Stacks, Tag 03YU] is already tagged in
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/BiggerSiteGlobalCohomology.lean`;
what is below is a universe generalisation of the same statement and not a separate statement of
the source.

Everything stated is proved, with no carried hypothesis beyond the instances in the signatures.
Those instances are exactly the ones
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` carries — sheafification,
`Ext`-groups in the common morphism universe `max u w` and enough injectives on both sides, plus
the structured-arrow limits that the comparison of sheafification with restriction needs — and
the proof is the same: an equivalence changes neither the constant sheaf on `ℤ` nor the injective
objects.  Nothing is proved here about cohomology over an object, nor about sheaves of modules.

The adjunction used is the one of the equivalence `g⁻¹` itself, `g⁻¹^{-1} ⊣ g⁻¹`, rather than
`CategoryTheory.Functor.sheafAdjunctionContinuous`; that is what lets the file avoid assuming
that `g⁻¹` has a left adjoint for an independent reason, and the inverse of an equivalence is
exact and preserves injectives for free.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.Cohomology.SiteEquivalenceGlobal

universe w vA uA v v' u u'

/-! ### The constant sheaf -/

section ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type uA) [Category.{vA} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]

variable [(G.sheafPushforwardContinuous A J K).IsEquivalence]

/-- **The inverse of restriction takes the constant sheaf to the constant sheaf**,
`g⁻¹^{-1} M_C ≅ M_D`, when restriction is an equivalence.  Restriction takes `M_D` to `M_C` by
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`, so applying the inverse
equivalence to that identification and undoing the unit of the equivalence gives the
comparison. -/
def inverseConstantSheafIso (M : A) :
    (G.sheafPushforwardContinuous A J K).inv.obj ((constantSheaf J A).obj M) ≅
      (constantSheaf K A).obj M :=
  ((G.sheafPushforwardContinuous A J K).inv.mapIso
      ((DenseSubsiteGlobal.constantSheafRestrictionIso J K G A).app M)).symm ≪≫
    ((G.sheafPushforwardContinuous A J K).asEquivalence.unitIso.app
      ((constantSheaf K A).obj M)).symm

end ConstantSheaf

/-! ### The comparison of cohomology -/

section Cohomology

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- **Restriction along a continuous and cocontinuous functor of sites whose restriction of
abelian sheaves is an equivalence does not change global cohomology**, with the morphism universes
of the two sites independent.  For every degree `p`,

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on `(D, K)`, where `H^p` is `CategoryTheory.Sheaf.functorH`,
the `Ext`-groups out of the constant sheaf on `ℤ`.

Global cohomology is `Ext` out of the constant sheaf on `ℤ`, so this is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` for the adjunction of the equivalence
`g⁻¹`, at the identification `inverseConstantSheafIso` of the two constant sheaves.  Nothing has
to be proved exact or injective-preserving: an equivalence and its inverse are both. -/
def sheafCohomologyIsoOfIsEquivalence (p : ℕ) :
    G.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v', u} K p :=
  haveI : (G.sheafPushforwardContinuous AddCommGrpCat.{w} J
      K).asEquivalence.symm.functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).asEquivalence.symm.toAdjunction
  (ExtComparison.extFunctorObjIsoCompOfIso
    (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).asEquivalence.symm.toAdjunction
    (inverseConstantSheafIso J K G AddCommGrpCat.{w}
      (AddCommGrpCat.of (ULift.{w} ℤ))) p).symm

/-- **The cohomology of an abelian sheaf is the cohomology of its restriction along an
equivalence of sites**, at a fixed sheaf and in the form of an additive equivalence of the
cohomology groups. -/
def sheafHAddEquivOfIsEquivalence (F : Sheaf K AddCommGrpCat.{w}) (p : ℕ) :
    Sheaf.H.{max u w, w}
        ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F) p ≃+
      Sheaf.H.{max u w, w} F p :=
  ((sheafCohomologyIsoOfIsEquivalence.{w} J K G p).app F).addCommGroupIsoToAddEquiv

end Cohomology

end Stacks.Cohomology.SiteEquivalenceGlobal

end
