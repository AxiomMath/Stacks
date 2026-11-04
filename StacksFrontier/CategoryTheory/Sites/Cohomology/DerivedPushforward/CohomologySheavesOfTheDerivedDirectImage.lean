module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology sheaves of the unbounded derived direct image on a site

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C` and let `K` be an object of the unbounded derived category `D(O_C)`. Then the `i`-th
cohomology sheaf of `Rf_* K` is the sheaf associated to the presheaf

`V ↦ H^i(u(V), K) = H^i(V, Rf_* K)`,

which is [Stacks, Tag 0D6I]. The presheaf is `derivedPushforwardCohomologyPresheaf`: it is the
degree-`i` cohomology of derived sections of `Rf_* K` taken over all objects of `D` at once, so
its restriction maps are part of the construction and not only its values on objects.

## Main definitions

* `Stacks.Cohomology.UnboundedHigherDirectImageOnSites.derivedPushforwardCohomologyPresheaf`: the
  presheaf of `O_D`-modules `V ↦ H^i(V, Rf_* K)` on `D`, with its restriction maps.

## Main results

* `higherDirectImageIsoSheafifyCohomologyPresheaf` (associated sheaf): the `i`-th cohomology
  sheaf of `Rf_* K` is the sheafification of that presheaf, naturally in `K`.
* `derivedPushforwardCohomologyPresheafEvaluationIso` (values on objects of the target site): the
  value of that presheaf on `V` is `H^i(V, Rf_* K)`.
* `cohomologyOverObjectPushforwardIso` (the displayed equality): the identification
  `H^i(u(V), K) = H^i(V, Rf_* K)`.
* `derivedPushforwardCohomologyPresheafSourceValueIso` (values on objects of the target site read
  on the source site): the value of that presheaf on `V` is `H^i(u(V), K)`, which is the
  description of the presheaf the source displays.

None of the four carries the `@[stacks 0D6I]` attribute. Each is one clause of the tag, and the
last two carry a hypothesis the source does not have; the tag is stated whole and without that
hypothesis in the sibling module
`CohomologySheavesOfTheDerivedDirectImageUnconditional.lean`, as
`cohomologySheavesOfTheDerivedDirectImage`, which is assembled from the first two of these and
from the hypothesis-free replacements for the last two.

## Implementation notes

All statements are natural isomorphisms of functors on `D(O_C)` rather than families of
isomorphisms indexed by `K`, so they retain the naturality the source leaves implicit.

The two halves of the source's proof are already available and are not redone. The sheafification
half and the identification of the values of the cohomology presheaf with hypercohomology over an
object are [Stacks, Tag 0BKV] on the target site,
`Stacks.Cohomology.SiteCohomologyPresheaf.sheafificationCohomologyPresheafIso` and
`cohomologyPresheafEvaluationIso`; the only work there is composing them with `Rf_*`, and those
two clauses are therefore unconditional. The displayed equality `H^i(u(V), K) = H^i(V, Rf_* K)` is
`H^i` of [Stacks, Tag 0D6I]'s input [Stacks, Tag 0D6H], available as
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIso`.

**The two clauses below that use that input carry a hypothesis, and they no longer have to.**
The version of Tag 0D6H available when this module was written was proved from [Stacks, Tag 093Y]
— degreewise `f_*` carries K-injective complexes to K-injective complexes — which is not a
hypothesis of the source, so `cohomologyOverObjectPushforwardIso` and
`derivedPushforwardCohomologyPresheafSourceValueIso` take it as the named hypothesis `h093Y`,
exactly as that Tag 0D6H does, and `…OfFlat` discharges it for a flat morphism of ringed sites by
`Stacks.Cohomology.LerayUnbounded.isKInjective_pushforwardTopos_of_flat`.

The clause of Tag 0D6H on sections over an object is now available for an arbitrary morphism of
ringed sites, as
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral` — not by
proving Tag 093Y, but by corepresenting `Γ(V, -)` by `j_{V!} O_V` and testing on a K-injective
resolution, which needs no preservation of K-injectivity at all. The hypothesis-free forms of
the two clauses, and the statement of the whole tag, are therefore in the sibling module
`CohomologySheavesOfTheDerivedDirectImageUnconditional.lean`; the declarations here are kept
because they are what the existing consumers apply, `derivedPushforwardCohomologyPresheaf` and
the two unconditional clauses being shared between the two modules.

The three universes of the ringed sites are collapsed, as they are in
`AlgebraicGeometry.RingedSite.Hom` and throughout the unbounded derived development on sites.

## References

* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward)
open Stacks.Cohomology.Localization (derivedSectionsOverObject)
open Stacks.Cohomology.SiteCohomologyPresheaf
  (derivedSectionsPresheaf sheafificationCohomologyPresheafIso cohomologyPresheafEvaluationIso)

namespace Stacks.Cohomology.UnboundedHigherDirectImageOnSites

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- **The presheaf `V ↦ H^i(V, Rf_* K)`** of `O_D`-modules on the target site, together with its
restriction maps: the degree-`i` cohomology presheaf of the unbounded derived direct image of `K`.
Its values are identified with hypercohomology over `V`, and with hypercohomology over `u(V)` on
the source site, by `derivedPushforwardCohomologyPresheafEvaluationIso` and
`derivedPushforwardCohomologyPresheafSourceValueIso`; its sheafification is the `i`-th cohomology
sheaf of `Rf_* K` by `higherDirectImageIsoSheafifyCohomologyPresheaf`. -/
abbrev derivedPushforwardCohomologyPresheaf
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (i : ℤ) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj :=
  (DerivedCategory.homologyFunctor
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i).obj
    ((derivedSectionsPresheaf Y).obj ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K))

/-- **The associated-sheaf clause of Stacks 0D6I.** The `i`-th cohomology sheaf of `Rf_* K` is the
sheaf associated to the presheaf `V ↦ H^i(V, Rf_* K)`, naturally in `K`.

This is Tag 0BKV on the target site — the cohomology sheaf of an object of `D(O_D)` is the
sheafification of its cohomology presheaf — composed with `Rf_*`. One clause of the tag, so it
carries no attribute: the tag is stated whole as
`cohomologySheavesOfTheDerivedDirectImage`, which has this as its first component. -/
def higherDirectImageIsoSheafifyCohomologyPresheaf (i : ℤ) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i ≅
      derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
        PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :=
  (Functor.isoWhiskerLeft (derivedPushforward.{u} f.toRingedToposSiteHom)
    (sheafificationCohomologyPresheafIso Y i)).symm

/-- **The clause of Stacks 0D6I on values on objects of the target site.** The value on `V ∈ D` of
the presheaf `derivedPushforwardCohomologyPresheaf` is the hypercohomology `H^i(V, Rf_* K)`,
naturally in `K`.

This is Tag 0BKV on the target site, composed with `Rf_*`. One clause of the tag, so it carries
no attribute: the tag is stated whole as `cohomologySheavesOfTheDerivedDirectImage`, which has
this as its third component. -/
def derivedPushforwardCohomologyPresheafEvaluationIso (V : Y.C) (i : ℤ) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
          (Opposite.op V) ⋙
        forget₂
          (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V)))
          AddCommGrpCat.{u} ≅
      derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  Functor.isoWhiskerLeft (derivedPushforward.{u} f.toRingedToposSiteHom)
    (cohomologyPresheafEvaluationIso Y V i)

/-- **The displayed equality of Stacks 0D6I, over a carried hypothesis.** Cohomology over `u(V)`
on the source site agrees with cohomology over `V` after the unbounded derived direct image:
`H^i(u(V), K) = H^i(V, Rf_* K)`, naturally in `K`. This is `H^i` applied to the isomorphism of
Tag 0D6H.

The hypothesis `h093Y` is Tag 093Y for `f` — degreewise direct image carries K-injective complexes
of `O_C`-modules to K-injective complexes of `O_D`-modules. It is not a hypothesis of the source:
it is the input the first proof of Tag 0D6H in this library rested on. No attribute, for that
reason and because this is one clause of the tag; the hypothesis-free form is
`cohomologyOverObjectPushforwardIsoGeneral`, and the tag is stated whole as
`cohomologySheavesOfTheDerivedDirectImage`. See `cohomologyOverObjectPushforwardIsoOfFlat` for
the flat case, in which `h093Y` is discharged from flatness instead. -/
def cohomologyOverObjectPushforwardIso (V : Y.C) (i : ℤ)
    (h093Y : ∀ (I : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ), I.IsKInjective →
      CochainComplex.IsKInjective
        ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    derivedSectionsOverObject X (f.u.obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i ≅
      derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  Functor.isoWhiskerRight
    (Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoOfKInjective
      f V h093Y).symm
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)

/-- **The clause of Stacks 0D6I on values read on the source site, over a carried hypothesis.**
The value on `V ∈ D` of the presheaf `derivedPushforwardCohomologyPresheaf` is the hypercohomology
`H^i(u(V), K)` over `u(V)` on the source site, naturally in `K`. This is the description of the
presheaf that the source displays.

It is `H^i(V, Rf_* K)` by Tag 0BKV on the target site, and that is `H^i(u(V), K)` by
`cohomologyOverObjectPushforwardIso`; the hypothesis `h093Y` is the one of that lemma, and is not
a hypothesis of the source. No attribute, for that reason and because this is one clause of the
tag; the hypothesis-free form is
`derivedPushforwardCohomologyPresheafSourceValueIsoGeneral`, and the tag is stated whole as
`cohomologySheavesOfTheDerivedDirectImage`. -/
def derivedPushforwardCohomologyPresheafSourceValueIso (V : Y.C) (i : ℤ)
    (h093Y : ∀ (I : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ), I.IsKInjective →
      CochainComplex.IsKInjective
        ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
          (Opposite.op V) ⋙
        forget₂
          (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V)))
          AddCommGrpCat.{u} ≅
      derivedSectionsOverObject X (f.u.obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  derivedPushforwardCohomologyPresheafEvaluationIso f V i ≪≫
    (cohomologyOverObjectPushforwardIso f V i h093Y).symm

section Flat

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [PreservesFiniteLimits f.toRingedToposSiteHom.pullbackTopos]

/-- The displayed equality `H^i(u(V), K) = H^i(V, Rf_* K)` of Stacks 0D6I for a **flat** morphism
of ringed sites, with no hypothesis carried: flatness of `f` — left exactness of `f^*`, Tag 03DJ —
gives Tag 093Y. -/
def cohomologyOverObjectPushforwardIsoOfFlat (V : Y.C) (i : ℤ) :
    derivedSectionsOverObject X (f.u.obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i ≅
      derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  cohomologyOverObjectPushforwardIso f V i
    (Stacks.Cohomology.LerayUnbounded.isKInjective_pushforwardTopos_of_flat f)

/-- The value on `V` of the presheaf `derivedPushforwardCohomologyPresheaf` is `H^i(u(V), K)`, for
a **flat** morphism of ringed sites and with no hypothesis carried. -/
def derivedPushforwardCohomologyPresheafSourceValueIsoOfFlat (V : Y.C) (i : ℤ) :
    derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
          (Opposite.op V) ⋙
        forget₂
          (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V)))
          AddCommGrpCat.{u} ≅
      derivedSectionsOverObject X (f.u.obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  derivedPushforwardCohomologyPresheafSourceValueIso f V i
    (Stacks.Cohomology.LerayUnbounded.isKInjective_pushforwardTopos_of_flat f)

end Flat

end Stacks.Cohomology.UnboundedHigherDirectImageOnSites

end
