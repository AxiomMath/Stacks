module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.Exactness
public import StacksFrontier.Cotangent.CohomologyPresheaf.BiggerSiteObjectwise

/-!
# Cohomology over an object of a simplicial component

Stacks 0DBZ says that for a simplicial-site situation of Stacks 09WE, the cohomology of an
abelian sheaf on the total site over an object lying in one simplicial degree agrees with the
cohomology, over that object, of the restriction of the sheaf to that degree.

Restriction is the pullback of sheaves along the cocontinuous component inclusion, and cohomology
is Mathlib's `Ext`-based `CategoryTheory.Sheaf.H'`. The statement is an instance of
`Stacks.Cohomology.BiggerSite.cohomologyObjIso` — Stacks 03YU, statement 2, objectwise — whose
one non-formal hypothesis is the exactness of the abelian lower shriek along the functor
concerned. For a component inclusion that hypothesis is Stacks 09WG (7), supplied by
`Stacks.Sites.ComponentSumFormula.preservesMonomorphisms_sheafPullback_componentFunctor`.

## Main results

* `Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv`: Mathlib's
  `CategoryTheory.Abelian.Ext.chgUniv` is additive, so the `Ext`-group of an abelian category does
  not depend on its auxiliary universe even as an abelian group.
* `Stacks.Cohomology.SimplicialComponent.sheafHAddEquivChgUniv`: consequently sheaf cohomology
  does not depend on the `Ext` universe.
* `Stacks.Cohomology.SimplicialComponent.cohomologyObjIsoExtUniv`: Stacks 03YU statement 2,
  objectwise, for an arbitrary `Ext` universe.
* `Stacks.Cohomology.SimplicialComponent.cohomologyObj_iso_component`: **Stacks 0DBZ.**

## Implementation notes

`Stacks.Cohomology.BiggerSite.cohomologyObjIso` is available only for `Ext` in the morphism
universe of the sites, because the corepresentation it is transported along identifies sections
over an object with a `preadditiveCoyoneda`, whose values live in that universe; the
implementation notes of
`StacksFrontier/Cotangent/CohomologyPresheaf/SiteSectionsComparison.lean` record this. The statement
below is for an arbitrary `Ext` universe, and the two are bridged by
`extChgUnivAddEquiv`: Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` is a bijection of the two
`Ext`-groups, and it is additive because `CategoryTheory.Abelian.Ext.homEquiv_chgUniv` says it
commutes with the identification of an `Ext`-group with a group of morphisms of the derived
category, along which the group structure on `Ext` is defined. Note that the two cohomology groups
live in *different* categories — `AddCommGrpCat` at two universes — so the bridge cannot be an
isomorphism and has to be an additive equivalence.

The four instance binders are those of the tagged statement, kept verbatim. `HasSheafify J Ab` is in
fact an
instance for every Grothendieck topology on a small site, and so is `HasExt` in the site's own
universe; both are therefore redundant, but `CategoryTheory.HasSheafify` and
`CategoryTheory.HasExt` are `Prop`-valued classes, so a redundant binder cannot make the statement
about a different sheafification.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0DBZ](https://stacks.math.columbia.edu/tag/0DBZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' v u

namespace Stacks.Cohomology.SimplicialComponent

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasExt.{w'} C]

/-- **`CategoryTheory.Abelian.Ext.chgUniv` is additive.** The abelian group structure on an
`Ext`-group is transported from a group of morphisms of the derived category along
`CategoryTheory.Abelian.Ext.homEquiv`, and
`CategoryTheory.Abelian.Ext.homEquiv_chgUniv` says that the change of universe commutes with that
identification. -/
theorem extChgUniv_add {X Y : C} {n : ℕ} (e₁ e₂ : Ext.{w} X Y n) :
    Ext.chgUniv.{w'} (e₁ + e₂) = Ext.chgUniv.{w'} e₁ + Ext.chgUniv.{w'} e₂ := by
  let := HasDerivedCategory.standard C
  refine (Ext.homEquiv (X := X) (Y := Y) (n := n)).injective ?_
  have h := Ext.homEquiv_chgUniv (e₁ + e₂)
  have h1 := Ext.homEquiv_chgUniv e₁
  have h2 := Ext.homEquiv_chgUniv e₂
  rw [h]
  change (e₁ + e₂).hom = (Ext.chgUniv.{w'} e₁ + Ext.chgUniv.{w'} e₂).hom
  rw [Ext.add_hom, Ext.add_hom]
  exact (congrArg (fun z => z + Ext.hom e₂) h1.symm).trans
    (congrArg (fun z => Ext.hom (Ext.chgUniv.{w'} e₁) + z) h2.symm)

/-- **An `Ext`-group does not depend on its auxiliary universe, as an abelian group.** This is
`CategoryTheory.Abelian.Ext.chgUniv` promoted to an additive equivalence. -/
def extChgUnivAddEquiv {X Y : C} {n : ℕ} : Ext.{w} X Y n ≃+ Ext.{w'} X Y n :=
  { Ext.chgUniv.{w'} with map_add' := extChgUniv_add }

end Ext

section Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u}] [HasExt.{w} (Sheaf J Ab.{u})]

/-- **Sheaf cohomology does not depend on the `Ext` universe.** The two groups lie in
`AddCommGrpCat` at two different universes, so the comparison is an additive equivalence and not
an isomorphism of the category. -/
def sheafHAddEquivChgUniv (F : Sheaf J Ab.{u}) (p : ℕ) (X : C) :
    (Sheaf.H'.{w, u, u} F p X : Type w) ≃+ (Sheaf.H'.{u, u, u} F p X : Type u) :=
  extChgUnivAddEquiv.{w, u, u, u + 1} (C := Sheaf J Ab.{u})

end Sheaf

/-- **Stacks 03YU, statement 2, objectwise, for an arbitrary `Ext` universe.** Cohomology of an
abelian sheaf over `v U` on the bigger site agrees with the cohomology over `U` of its
restriction. This is `Stacks.Cohomology.BiggerSite.cohomologyObjIso`, which is available only for
`Ext` in the morphism universe of the sites, bridged to an arbitrary `Ext` universe by
`Stacks.Cohomology.SimplicialComponent.sheafHAddEquivChgUniv`. -/
def cohomologyObjIsoExtUniv {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (v : C ⥤ D)
    [v.IsContinuous J K] [v.IsCocontinuous J K]
    [(v.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
    [∀ P : Cᵒᵖ ⥤ Ab.{u}, v.op.HasPointwiseRightKanExtension P]
    [(v.sheafPullback Ab.{u} J K).PreservesMonomorphisms]
    [HasSheafify J Ab.{u}] [HasSheafify K Ab.{u}]
    [HasExt.{w} (Sheaf J Ab.{u})] [HasExt.{w} (Sheaf K Ab.{u})]
    (F : Sheaf K Ab.{u}) (p : ℕ) (U : C) :
    Sheaf.H'.{w, u, u} F p (v.obj U) ≅
      Sheaf.H'.{w, u, u} ((v.sheafPullbackCocontinuous Ab.{u} J K).obj F) p U :=
  AddEquiv.toAddCommGrpIso
    ((sheafHAddEquivChgUniv K F p (v.obj U)).trans
      (((BiggerSite.cohomologyObjIso J K v F p U).addCommGroupIsoToAddEquiv).trans
        (sheafHAddEquivChgUniv J ((v.sheafPullbackCocontinuous Ab.{u} J K).obj F) p U).symm))

/-- **Stacks 0DBZ.** Cohomology over an object of one simplicial component agrees with cohomology
over the corresponding object of the total site, with coefficients restricted to that component.

The restriction is the pullback of sheaves along the cocontinuous component inclusion. This is
Stacks 03YU statement 2 — `Stacks.Cohomology.BiggerSite.cohomologyObjIso`, read at an arbitrary
`Ext` universe as `cohomologyObjIsoExtUniv` — applied to the component inclusion, whose exactness
hypothesis is Stacks 09WG (7),
`Stacks.Sites.ComponentSumFormula.preservesMonomorphisms_sheafPullback_componentFunctor`. -/
@[stacks 0DBZ]
def cohomologyObj_iso_component
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) (U : S.component n)
    [HasSheafify S.totalTopology Ab.{u}]
    [HasSheafify (S.componentTopology n) Ab.{u}]
    [HasExt.{w} (Sheaf S.totalTopology Ab.{u})]
    [HasExt.{w} (Sheaf (S.componentTopology n) Ab.{u})]
    (F : Sheaf S.totalTopology Ab.{u}) (p : ℕ) :
    Sheaf.H'.{w, u, u} F p ((SimplicialSiteSituation.componentFunctor S n).obj U) ≅
      Sheaf.H'.{w, u, u}
        (((SimplicialSiteSituation.componentFunctor S n).sheafPullbackCocontinuous
          Ab.{u} (S.componentTopology n) S.totalTopology).obj F) p U :=
  cohomologyObjIsoExtUniv (S.componentTopology n) S.totalTopology
    (SimplicialSiteSituation.componentFunctor S n) F p U

end Stacks.Cohomology.SimplicialComponent

end
