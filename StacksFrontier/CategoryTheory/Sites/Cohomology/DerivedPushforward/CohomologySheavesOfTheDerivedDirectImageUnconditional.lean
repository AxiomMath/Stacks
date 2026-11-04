module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CohomologySheavesOfTheDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSectionsGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology sheaves of the unbounded derived direct image, for an arbitrary morphism

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C` and let `K` be an object of the unbounded derived category `D(O_C)`. Then the `i`-th
cohomology sheaf of `Rf_* K` is the sheaf associated to the presheaf

`V ↦ H^i(u(V), K) = H^i(V, Rf_* K)`,

which is [Stacks, Tag 0D6I]. This file states that in full and with no hypothesis beyond the
source's, and it is where the `@[stacks 0D6I]` attribute lives.

## How the hypothesis went away

The sibling module `CohomologySheavesOfTheDerivedDirectImage.lean` builds the presheaf
`derivedPushforwardCohomologyPresheaf`, identifies its sheafification with the cohomology sheaf
and its value at `V` with `H^i(V, Rf_* K)` — both unconditionally, both being [Stacks, Tag 0BKV]
on the target site composed with `Rf_*` — and then reads the displayed equality
`H^i(u(V), K) = H^i(V, Rf_* K)` off [Stacks, Tag 0D6H]. Its version of that last step carried a
named hypothesis: [Stacks, Tag 093Y], that degreewise `f_*` sends K-injective complexes to
K-injective complexes, which is the input the library's first proof of Tag 0D6H rested on and
which is *not* a hypothesis of the source.

That hypothesis is gone, and not because Tag 093Y was proved. The clause of Tag 0D6H on sections
over an object is now available for an arbitrary morphism of ringed sites as
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral`, proved by
corepresenting `Γ(V, -)` by `j_{V!} O_V` and testing on a K-injective resolution rather than by
preserving K-injectivity; see `LerayForUnboundedSectionsGeneral.lean`. Composing with `H^i` is
the whole of the source's first step, so every clause of Tag 0D6I is now unconditional.

## Main results

All in the namespace `Stacks.Cohomology.UnboundedHigherDirectImageOnSites`.

* `cohomologyOverObjectPushforwardIsoGeneral`: the displayed equality
  `H^i(u(V), K) = H^i(V, Rf_* K)`, naturally in `K`, for an arbitrary morphism of ringed sites.
* `derivedPushforwardCohomologyPresheafSourceValueIsoGeneral`: the value at `V` of the presheaf
  `derivedPushforwardCohomologyPresheaf` is `H^i(u(V), K)`, which is the description of the
  presheaf that the source displays.
* `cohomologySheavesOfTheDerivedDirectImage`: **Stacks 0D6I**, the whole of it — the
  sheafification clause together with both readings of the presheaf's values.

## Implementation notes

**No instance binders.** `derivedSectionsOverObjectPushforwardIsoGeneral` is stated with
`HasSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat` on both sites in its binders, and
with the `Prop` class `HasLeftDerivedFunctor` for the degreewise pullback. None of the three
reaches the statements here. The first two are found by instance search for every
`AlgebraicGeometry.RingedSite.{u, u, u}`, and the third is discharged by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy` from
`AlgebraicGeometry.RingedSite.Hom.isMorphismOfSites_toRingedToposSiteHom`, which a morphism of
ringed sites *stores*. So the binders of the results below are exactly `f`, `V`, `i` and the
universe, and the naturality in `K` is built into the statements, which are isomorphisms of
functors on `D(O_C)`.

**The tag sits on one declaration.** `cohomologySheavesOfTheDerivedDirectImage` is a triple: the
sheafification isomorphism, and the two identifications of the presheaf's value at `V` that the
source's display writes as an equality. Taken apart, its three components are the three clauses
the sibling module proves; taken together they are the statement of the tag, which is why the
attribute is here and not on any one of them.

## References

* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward)
open Stacks.Cohomology.Localization (derivedSectionsOverObject)
open Stacks.Cohomology.SiteCohomologyPresheaf (derivedSectionsPresheaf)

namespace Stacks.Cohomology.UnboundedHigherDirectImageOnSites

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- **The displayed equality of Stacks 0D6I, for an arbitrary morphism of ringed sites.**
Cohomology over `u(V)` on the source site agrees with cohomology over `V` after the unbounded
derived direct image: `H^i(u(V), K) = H^i(V, Rf_* K)`, naturally in `K`.

This is `H^i` applied to the clause of Stacks 0D6H on sections over an object, which
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral` has for every
morphism of ringed sites. No hypothesis is carried; in particular Stacks 093Y, on which
`cohomologyOverObjectPushforwardIso` depends, is not needed. -/
def cohomologyOverObjectPushforwardIsoGeneral (V : Y.C) (i : ℤ) :
    derivedSectionsOverObject X (f.u.obj V) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i ≅
      derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i :=
  letI : (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      f.toRingedToposSiteHom).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      f.toRingedToposSiteHom f.isMorphismOfSites_toRingedToposSiteHom
  Functor.isoWhiskerRight
    (Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral f V).symm
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)

/-- **The presheaf of Stacks 0D6I, read on the source site, for an arbitrary morphism of ringed
sites.** The value on `V ∈ D` of the presheaf `derivedPushforwardCohomologyPresheaf` is the
hypercohomology `H^i(u(V), K)` over `u(V)` on the source site, naturally in `K`. This is the
description of the presheaf that the source displays.

It is `H^i(V, Rf_* K)` by Stacks 0BKV on the target site, and that is `H^i(u(V), K)` by
`cohomologyOverObjectPushforwardIsoGeneral`. No hypothesis is carried. -/
def derivedPushforwardCohomologyPresheafSourceValueIsoGeneral (V : Y.C) (i : ℤ) :
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
    (cohomologyOverObjectPushforwardIsoGeneral f V i).symm

/-- **Stacks 0D6I.** Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites corresponding to
the continuous functor `u : D ⥤ C` and let `i : ℤ`. Then the `i`-th cohomology sheaf of `Rf_* K`
is the sheaf associated to the presheaf

`V ↦ H^i(u(V), K) = H^i(V, Rf_* K)`,

naturally in the object `K` of `D(O_C)`.

The presheaf is `derivedPushforwardCohomologyPresheaf`, which carries its restriction maps, and
the three components are the three assertions the source makes about it: that its sheafification
is the cohomology sheaf of `Rf_* K`, and that its value on `V` is `H^i(u(V), K)` and is
`H^i(V, Rf_* K)` — the two sides of the source's displayed equality, whose composite
`H^i(u(V), K) ≅ H^i(V, Rf_* K)` is `cohomologyOverObjectPushforwardIsoGeneral`.

Everything is stated as an isomorphism of functors on `D(O_C)`, so the naturality in `K` that
the source leaves implicit is part of the statement. There is no hypothesis beyond the source's:
the sheafification clause is Stacks 0BKV on the target site composed with `Rf_*`, and the
displayed equality is `H^i` of the clause of Stacks 0D6H on sections over an object, which
`Stacks.Cohomology.LerayUnbounded.derivedSectionsOverObjectPushforwardIsoGeneral` proves for an
arbitrary morphism of ringed sites. -/
@[stacks 0D6I "the i-th cohomology sheaf of Rf_*K is the sheaf associated to the presheaf
V ↦ H^i(u(V), K) = H^i(V, Rf_*K), naturally in K, for an arbitrary morphism of ringed sites:
the associated-sheaf clause and both readings of the value of the presheaf on an object"]
def cohomologySheavesOfTheDerivedDirectImage (i : ℤ) :
    (derivedPushforward.{u} f.toRingedToposSiteHom ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) i ≅
        derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
          PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)) ×
      (∀ V : Y.C,
          derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
              DerivedCategory.homologyFunctor
                (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
              PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
                (Opposite.op V) ⋙
              forget₂
                (ModuleCat.{u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V)))
                AddCommGrpCat.{u} ≅
            derivedSectionsOverObject X (f.u.obj V) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) ×
      (∀ V : Y.C,
          derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
              DerivedCategory.homologyFunctor
                (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) i ⋙
              PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
                (Opposite.op V) ⋙
              forget₂
                (ModuleCat.{u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V)))
                AddCommGrpCat.{u} ≅
            derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsOverObject Y V ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) :=
  ⟨higherDirectImageIsoSheafifyCohomologyPresheaf f i,
    fun V => derivedPushforwardCohomologyPresheafSourceValueIsoGeneral f V i,
    fun V => derivedPushforwardCohomologyPresheafEvaluationIso f V i⟩

end Stacks.Cohomology.UnboundedHigherDirectImageOnSites

end
