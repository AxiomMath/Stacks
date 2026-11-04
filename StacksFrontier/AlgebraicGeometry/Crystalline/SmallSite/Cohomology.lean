module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE

/-!
# Cohomology of abelian sheaves on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  This file makes the cohomology groups
`H^j(Cris(X/S), F)` of an abelian sheaf on the small crystalline site available, by discharging
the four typeclass hypotheses that the general construction of sheaf cohomology carries.

Sheaf cohomology on a site is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant
sheaf on `ℤ` in the category of abelian sheaves.  To write it down for a given site one needs
sheafification (`HasSheafify`) and the existence of `Ext`-groups in a chosen universe
(`HasExt`), the latter coming from enough injectives together with local smallness; and to know
that it deserves the name "cohomology" one needs it to be the right derived functor of global
sections, which is `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`.  None of this is
automatic for `Cris(X/S)`, whose objects form a `Type (u + 1)` while its morphisms form a
`Type u`: Mathlib's instances are stated for a site that is literally small with its hom
universe equal to the coefficient universe, and that shape cannot be instantiated here.  The
coefficient universe is therefore the object universe `u + 1`, and the four hypotheses are
discharged at that universe from the general criteria of
`StacksFrontier/CategoryTheory/Sites/GrothendieckAbelianUnivLE.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardExact.lean`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `cohomologyFunctor` — the `j`-th cohomology functor `H^j(Cris(X/S), -)` of abelian sheaves on
  the small crystalline site.
* `cohomology` — the cohomology group `H^j(Cris(X/S), F)` of an abelian sheaf.
* `globalSections` — the global sections functor `Γ(Cris(X/S), -)` of abelian sheaves, the right
  adjoint of the constant sheaf functor.

## Main results

* `instHasSheafifyAddCommGrpCat`, `instLocallySmall`, `instEnoughInjectives`, `instHasExt` — the
  four instances that make cohomology on the small crystalline site exist: abelian sheaves in
  `AddCommGrpCat.{u + 1}` admit sheafification, are locally `(u + 1)`-small, have enough
  injectives, and have `Ext`-groups in `Type (u + 1)`.
* `rightDerivedGlobalSectionsIso` — **cohomology on the small crystalline site is the right
  derived functor of global sections**, `R^j Γ(Cris(X/S), -) ≅ H^j(Cris(X/S), -)`.
* `cohomologyFunctorZeroIso` — **`H^0(Cris(X/S), -) = Γ(Cris(X/S), -)`**.
* `subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections` — the vanishing of
  `H^j(Cris(X/S), F)` and of `R^j Γ(Cris(X/S), F)` are the same condition.

The higher cohomology of an injective abelian sheaf vanishes by Mathlib's instance
`Subsingleton (F.H (n + 1))` for injective `F`, which applies to `cohomology` directly, this being
an abbreviation of `CategoryTheory.Sheaf.H`.

## What is and is not proved

What is proved is that the graded cohomology groups `H^j(Cris(X/S), F)` of an abelian sheaf
exist, are functorial in `F`, compute the right derived functors of global sections, and agree
with global sections in degree zero.  That is the form in which the crystalline cohomology of
[Stacks, Tag 07IT] is consumed by the vanishing and comparison statements of the chapter.

What is not proved here:

* There is no derived-category-valued `RΓ(Cris(X/S), -)` here.  The repository has one for a
  site whose underlying category is small, `Stacks.Cohomology.CompositeRightDerived.RGammaSite`,
  landing in `HomotopyCategory (Ab.{u}) (ComplexShape.up ℕ)`; its `SmallCategory` hypothesis
  fails for `Cris(X/S)` for the universe reason above, and transporting it is not a matter of
  re-running the construction at free universes, because the bounded-below derived category of
  the abelian sheaves would have to be produced at the coefficient universe as well.  The graded
  groups defined here are what the vanishing statements need.
* Nothing is proved about module-valued cohomology.  A sheaf of `𝒪_{X/S}`-modules in the sense
  of `Crystalline.GlobalCrystallineSituation.SmallSite.structureSheaf` has its modules in
  `Type u`, and its underlying abelian sheaf therefore lands in `AddCommGrpCat.{u}`, where
  sheafification on `Cris(X/S)` is *not* available: the criterion of
  `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` asks `UnivLE.{u + 1, u}`.  A
  module-valued crystalline cohomology has to be set up with the modules one universe higher,
  as `Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_over`
  already does for the global presentations it needs.
* The long exact sequence of a short exact sequence of abelian sheaves is not stated.  It is
  available for `Ext` out of a fixed object in Mathlib and would be an application, not a new
  ingredient.

## References

* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 071E](https://stacks.math.columbia.edu/tag/071E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- Abelian sheaves on the small crystalline site admit sheafification, with the coefficients in
the universe of the objects of the site.  The objects of `Cris(X/S)` form a `Type (u + 1)` and
its morphisms a `Type u`, so `u + 1` is the smallest coefficient universe for which the
criterion `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` applies. -/
instance instHasSheafifyAddCommGrpCat :
    HasSheafify (smallTopology S) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Abelian sheaves on the small crystalline site are locally `(u + 1)`-small: a morphism of
sheaves is a family of components indexed by the objects of the site, and those form a
`Type (u + 1)`. -/
instance instLocallySmall :
    LocallySmall.{u + 1} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2} (smallTopology S)
    AddCommGrpCat.{u + 1}

/-- **Abelian sheaves on the small crystalline site have enough injectives**, so their cohomology
can be computed by injective resolutions.  They form a Grothendieck abelian category at the
universe `u + 1` of the objects of the site, by
`CategoryTheory.Sheaf.enoughInjectives_of_small`. -/
instance instEnoughInjectives :
    EnoughInjectives (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2} (smallTopology S)
    AddCommGrpCat.{u + 1}

/-- **`Ext`-groups of abelian sheaves on the small crystalline site exist in `Type (u + 1)`**,
which is what makes the cohomology groups `H^j(Cris(X/S), F)` writable down.  This is enough
injectives together with local `(u + 1)`-smallness. -/
instance instHasExt :
    HasExt.{u + 1} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- **The global sections functor `Γ(Cris(X/S), -)` of abelian sheaves on the small crystalline
site**, Mathlib's right adjoint of the constant sheaf functor. -/
abbrev globalSections :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.Γ (smallTopology S) AddCommGrpCat.{u + 1}

/-- Global sections of abelian sheaves on the small crystalline site are additive, being a right
adjoint and hence preserving binary products. -/
instance instAdditiveGlobalSections : (globalSections S).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} (smallTopology S)

/-- **The `j`-th cohomology functor `H^j(Cris(X/S), -)` of abelian sheaves on the small
crystalline site**: the `Ext`-groups in degree `j` out of the constant sheaf on `ℤ`.  That these
are the right derived functors of global sections is `rightDerivedGlobalSectionsIso`. -/
def cohomologyFunctor (j : ℕ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} (smallTopology S) j

/-- **The cohomology group `H^j(Cris(X/S), F)` of an abelian sheaf on the small crystalline
site.** -/
abbrev cohomology (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) : Type (u + 1) :=
  Sheaf.H.{u + 1, u + 1} F j

/-- The value of the `j`-th cohomology functor on an abelian sheaf `F` on the small crystalline
site is the cohomology group `H^j(Cris(X/S), F)`. -/
theorem cohomologyFunctor_obj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    ((cohomologyFunctor S j).obj F : Type (u + 1)) = cohomology S F j := rfl

/-- **Cohomology on the small crystalline site is the right derived functor of global
sections**, `R^j Γ(Cris(X/S), -) ≅ H^j(Cris(X/S), -)`.  Global sections are corepresented by the
constant sheaf on `ℤ`, and cohomology is `Ext` out of that sheaf. -/
def rightDerivedGlobalSectionsIso (j : ℕ) :
    (globalSections S).rightDerived j ≅ cohomologyFunctor S j :=
  Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
    (smallTopology S) j

/-- **`H^0(Cris(X/S), -) = Γ(Cris(X/S), -)`.**  Global sections on the small crystalline site are
left exact, being a right adjoint, so their zeroth right derived functor is themselves. -/
def cohomologyFunctorZeroIso : cohomologyFunctor S 0 ≅ globalSections S :=
  (rightDerivedGlobalSectionsIso S 0).symm ≪≫ (globalSections S).rightDerivedZeroIsoSelf

/-- The vanishing of `H^j(Cris(X/S), F)` and of `R^j Γ(Cris(X/S), F)` are the same condition. -/
theorem subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    Subsingleton (cohomology S F j) ↔
      IsZero (((globalSections S).rightDerived j).obj F) :=
  Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1, u, u + 1}
    (smallTopology S) F j

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
