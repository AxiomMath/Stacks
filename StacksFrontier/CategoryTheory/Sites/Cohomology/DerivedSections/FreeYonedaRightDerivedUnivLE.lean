module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf cohomology is right-derived sections, in a coefficient universe of its own

For a site `C` with `C : Type u` and `Category.{v} C`, the identification of sheaf cohomology
over an object of the site with the right-derived functor of sections over that object is
available only with the coefficient universe pinned to the homs of the site:
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` is stated for
`[SmallCategory C]` and `Ab.{u}`, and
`Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections` for `Opens X` with
`X : TopCat.{u}` and `AddCommGrpCat.{u}`.

That pinning is the one `DerivedSections/FreeYonedaSectionsUnivLE.lean` removes for the
cohomology presheaf itself, and this file carries it through to the comparison with right-derived
sections. The input is the corepresentation: `Stacks.Cohomology.FreeYonedaUnivLE.sectionsAddEquiv`
says that morphisms out of `freeYoneda.obj U` are the sections over `U`, at any coefficient
universe dominating the homs of the site, and
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived` turns a corepresentation into the
comparison of `Ext` with right-derived functors. That lemma is already universe-general.

The coefficient universe here is `max u v t` rather than `max v t`: the comparison equates a
functor to `AddCommGrpCat.{max u v t}` — the hom universe of `Sheaf J AddCommGrpCat.{max u v t}`,
in which `preadditiveCoyoneda` takes its values — with sections, which land in the coefficients
themselves, so the coefficients must dominate the objects of the site as well as its homs. On the
site of opens of a space, which is the case of interest, `u = v` and the condition is vacuous.
`freeYoneda` is therefore used at `t := max u t`, which is legitimate because its `t` is free.

## Main definitions

All in the namespace `Stacks.Cohomology.FreeYonedaUnivLE`.

* `evaluationRepresentation`: sections over `U` are corepresented by `freeYoneda.obj U`.
* `cohomologyPresheafObjIsoRightDerivedSections`: `H^p(U, F)` is the `p`-th right-derived functor
  of sections over `U`, evaluated at `F`.

## Main results

* `nonempty_extFunctorObj_iso_rightDerived_sections`: the functor-level comparison, of which
  `cohomologyPresheafObjIsoRightDerivedSections` is a choice.
* `cohomologyPresheafObjIsoPinned`: at `t := v` the freed cohomology presheaf is Mathlib's
  `CategoryTheory.Sheaf.cohomologyPresheaf`.
* `nonempty_extFunctorObj_iso_rightDerived_sections_pinned`: at `t := v` on a site whose objects
  and homs share a universe this recovers
  `Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections`, so
  nothing is weakened.

## Implementation notes

Only existence is asserted upstream — see
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived` — so
`cohomologyPresheafObjIsoRightDerivedSections` is a choice and no compatibility in degree zero
with the canonical map to the right-derived functor is claimed. For the degree-zero statement
that *is* canonical, use `cohomologyPresheafIsoSections`.

These declarations carry no tag. They are infrastructure for [Stacks, Tag 09V3] and the derived
clause of [Stacks, Tag 0DCU], whose statements are the ones that need the freed coefficient
universe.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe s t v u

noncomputable section

/-- Sections over an object of the site are left exact, at any coefficient universe: the functor
is isomorphic to evaluation of the underlying presheaf, which preserves finite limits. The
library's instances of this fact are stated for `[SmallCategory C]` with `AddCommGrpCat.{u}`
(`Stacks.Cohomology.ModuleComparison.siteSections_preservesFiniteLimits`) and for the site of
opens of a space; the coefficient universe is free here, and is a universe variable of its own
rather than a `max`, so that instance search can solve for it. -/
@[sga "4 V 2.3.1" "left exactness of Γ(X"]
instance preservesFiniteLimits_sheafSections_obj {D : Type u} [Category.{v} D]
    (K : GrothendieckTopology D) (U : D) :
    PreservesFiniteLimits ((sheafSections K AddCommGrpCat.{s}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation K AddCommGrpCat.{s}).symm

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}]

/-- **Sections over an object of the site are corepresented by the free abelian sheaf on that
object**, at any coefficient universe dominating the objects and the homs of the site. This is
`ModuleSheafCohomology.evaluationRepresentation` with the coefficients no longer pinned; the
bijection is `sectionsAddEquiv` and its naturality is `sectionsEquiv_naturality`. -/
@[sga "4 XVIII 1.4.24" "(a), special case"]
def evaluationRepresentation (U : C) :
    (sheafSections J AddCommGrpCat.{max u v t}).obj (op U) ≅
      preadditiveCoyoneda.obj (op ((freeYoneda.{max u t} J).obj U)) := by
  refine (NatIso.ofComponents
    (fun F ↦ (sectionsAddEquiv.{max u t} U F).toAddCommGrpIso) ?_).symm
  intro F G β
  ext α
  change sectionsEquiv.{max u t} U G (α ≫ β) = β.hom.app (op U) (sectionsEquiv.{max u t} U F α)
  exact sectionsEquiv_naturality.{max u t} U α β

variable [HasExt.{max u v t} (Sheaf J AddCommGrpCat.{max u v t})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v t})]

/-- **The `Ext`-functors out of the free abelian sheaf on `U` are the right-derived functors of
sections over `U`**, with the coefficient universe freed. This is
`Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections` without
the pinning of the coefficients to the homs of the site. -/
theorem nonempty_extFunctorObj_iso_rightDerived_sections (U : C) (p : ℕ) :
    Nonempty (extFunctorObj.{max u v t} ((freeYoneda.{max u t} J).obj U) p ≅
      ((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)).rightDerived p) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived
    ((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)) _
    (evaluationRepresentation.{t} J U) p

/-- **Sheaf cohomology over an object of the site is right-derived sections, with the coefficient
universe freed.** This is `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` for
the cohomology presheaf of `DerivedSections/FreeYonedaSectionsUnivLE.lean`.

This is a choice: see `nonempty_extFunctorObj_iso_rightDerived_sections`. -/
def cohomologyPresheafObjIsoRightDerivedSections
    (F : Sheaf J AddCommGrpCat.{max u v t}) (p : ℕ) (U : C) :
    (cohomologyPresheaf.{max u v t, max u t} F p).obj (op U) ≅
      (((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)).rightDerived p).obj F :=
  (nonempty_extFunctorObj_iso_rightDerived_sections.{t} J U p).some.app F

section Pinned

/-- **At `t := v` the freed cohomology presheaf is Mathlib's.** `freeYonedaIso` identifies the
free abelian sheaf built on `uliftYoneda.{v}` with the one built on `yoneda`, and `Ext` is
functorial in its first variable, so no statement about
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf` at `t := v` is weaker than the
corresponding statement about `CategoryTheory.Sheaf.cohomologyPresheaf`. -/
def cohomologyPresheafObjIsoPinned {D : Type u} [Category.{v} D]
    (K : GrothendieckTopology D) [HasSheafify K AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf K AddCommGrpCat.{v})] (F : Sheaf K AddCommGrpCat.{v}) (p : ℕ) (U : D) :
    (cohomologyPresheaf.{v, v} F p).obj (op U) ≅ (Sheaf.cohomologyPresheaf F p).obj (op U) :=
  ((extFunctor p).mapIso ((freeYonedaIso.{v} K).app U).symm.op).app F

/-- **At `t := v` this comparison is the pinned one.** On a site whose objects and homs share a
universe the statement above, instantiated at `t := v`, is
`Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections` — the free
abelian sheaf is the sheafification of the free abelian presheaf on `yoneda.obj U` by
`freeYonedaIso`, so no statement proved with the freed coefficient universe is weaker than its
pinned counterpart. -/
@[sga "4 V 2.1.2" "Ext^q(A_X, special case"]
theorem nonempty_extFunctorObj_iso_rightDerived_sections_pinned {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) [HasSheafify K AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{u})] (U : D) (p : ℕ) :
    Nonempty (extFunctorObj.{u} (Stacks.Cohomology.FreeYoneda.freeYoneda K |>.obj U) p ≅
      ((sheafSections K AddCommGrpCat.{u}).obj (op U)).rightDerived p) :=
  ⟨(extFunctor p).mapIso ((freeYonedaIso.{u} K).app U).op ≪≫
    (nonempty_extFunctorObj_iso_rightDerived_sections.{u} K U p).some⟩

end Pinned

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
