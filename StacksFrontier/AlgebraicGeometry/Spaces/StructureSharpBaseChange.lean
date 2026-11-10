module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Étale base change for the structure map of a morphism of algebraic spaces

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  The two sides of the ordinary statement of Stacks 03LX for the direct image of
modules are transports of `𝒪_X`-modules along the two composite functors of sheaves of sets
around the square, and
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardEtaleBaseChange.lean`
reduces that statement to a single compatibility of the structure maps of Stacks 03G8: that
`(f')^♯` corresponds, under the sheaf-of-sets base-change isomorphism of Stacks 03LR, part (1),
to the étale restriction of `f^♯`.  It carries that compatibility as the named hypothesis
`hsharp` of `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp`.

This file proves that compatibility and so makes the ordinary statement of Stacks 03LX
unconditional.

The proof computes both sides on chart sections.  The sections of the right-hand transported
sheaf over an étale scheme chart `V` of `Y'` are the sections of `f_*𝒪_X` over the chart `g ∘ V`
of `Y`, that is — after reindexing along the Beck–Chevalley isomorphism of the square — a
section of `𝒪_X` over the algebraic space `X' ×_{Y'} V` read over `X`, and such a section is
determined by its restrictions to the étale scheme charts of `X'` above `X' ×_{Y'} V`.  On such
a chart `U'` both sides are pullback of regular functions along the morphism of schemes
`U' ⟶ V` that the chart induces; for the left-hand side that is the construction of `(f')^♯`,
for the right-hand side it is the construction of `f^♯` applied to the chart `i ∘ U'` of `X`
above `X ×_Y (g ∘ V)`, and the two induced morphisms of schemes agree because the
Beck–Chevalley isomorphism is compatible with the cartesian projections.  That last step is the
only place the square is used.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate` is the mate, across the comparison
  equivalences of Stacks 03G1, of the equality of the two composites of étale restriction of
  sheaves of sets with restriction along the comparison functor.
* `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` is **Stacks 03LX for the
  ordinary direct image**, unconditionally.

## Main results

* `AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap` is the
  base-change compatibility of the structure maps of Stacks 03G8, which is exactly the
  hypothesis `hsharp` of
  `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp`.
* `AlgebraicGeometry.Space.structureSharpSet_comp_smallEtaleSetPushforwardBaseChangeIso` is the
  same statement on underlying sheaves of sets, which is where all the content is.
* `AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso_hom_app` computes the
  base-change isomorphism of Stacks 03LR, part (1) on chart sections, and
  `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare_projection` is its geometric input: the
  Beck–Chevalley isomorphism of the square commutes with the cartesian projections.
* `AlgebraicGeometry.Space.counitIso_hom_app_structureSharpSet` computes the chart projections
  of the structure map of Stacks 03G8 in the form the structure map is stated in, rather than in
  the Kan-extension form of
  `AlgebraicGeometry.Space.chartProjection_structureMapApp`.
* `AlgebraicGeometry.Space.chartBaseChangeMap_baseChangeSquare` and
  `AlgebraicGeometry.Space.chartPullback_baseChangeSquare` are the chartwise statement: a chart
  of `X'` above `X' ×_{Y'} V`, read through the square as a chart of `X` above `X ×_Y (g ∘ V)`,
  induces the same morphism of schemes to `V`.

## Implementation notes

**Why no attribute on the compatibility itself.**  Stacks 03G8 asserts the existence of the
morphism of small étale ringed topoi of a morphism of algebraic spaces together with its
compatibility with composition — which is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` — and its agreement with the
construction for schemes.  It does not assert any base-change compatibility, and Stacks 03LR is
a statement about sheaves of sets, so
`AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap` carries no attribute.
What it earns is the attribute on
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, with a part string, because the
higher direct images of Stacks 03LX are still absent: they need enough injectives in
`AlgebraicGeometry.Space.Modules`, which this development does not have.

**Where the five factors go.**  The base-change isomorphism
`AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso` is a composite of five
isomorphisms: the comparison of restriction along `i` with its conjugate, two instances of
`CategoryTheory.Equivalence.conjugateCompIso`, the spaces-étale statement, and the comparison of
restriction along `g` with its conjugate.  The last two cancel outright by the triangle identity
of the comparison equivalence at `Y`
(`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso_unit_cancel`); the first two merge
into `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate`; and the middle one is
reindexing along the Beck–Chevalley isomorphism, because restriction along a composite of
functors of sites is the composite of the restrictions on the nose.  What is left of the
quasi-inverses of the comparison equivalences — which are `CategoryTheory.Functor.inv`, hence
`Classical.choose` — is a single counit, and
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit` evaluates the comparison
against it.

**Elaboration.**  Every rewrite is performed as a `congrArg` against an explicitly typed
function rather than with `rw`: the objects involved are only definitionally equal, say
`(smallEtaleSetRestriction i hi).obj 𝒪_X` versus `𝒪_{X'}`, and
`spacesEtaleSetRestriction g hg ⋙ smallEtaleComparisonRestriction Y'` versus
`smallEtaleComparisonRestriction Y ⋙ smallEtaleSetRestriction g hg` — so a rewrite that
abstracts one of them produces a motive which is not type-correct at `implicit` transparency,
and the unifier that is then asked to reconcile the two spellings unfolds the quasi-inverse of
the comparison equivalence and does not terminate.  Two `congrArg` functions need their binder
type written out for the same reason.  No `set_option` appears in this file.

**Universes.**  Everything is at the universe `u` of the structure rings: that is the universe
at which `AlgebraicGeometry.Space.smallEtaleDirectImage` and hence
`AlgebraicGeometry.Space.structureSharp` exist, and the module universe of
`AlgebraicGeometry.Space.modulePushforward` is `u` as well.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction of sheaves of sets as a conjugate, on sections -/

section Conj

/-- A functor sends a pair of mutually inverse composites to an identity composite. -/
private theorem map_comp_map_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {a : X ⟶ Y} {b : Y ⟶ X} (h : a ≫ b = 𝟙 X) : F.map a ≫ F.map b = 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_id]

variable {U V : AlgebraicSpaces B S hS}

/-- The comparison of `AlgebraicGeometry.Space.smallEtaleSetRestriction` with its conjugate is
restriction of the inverse counit of the comparison equivalence of Stacks 03G1: the unitors,
the associator and the comparison of the two composite restriction functors all have identity
components. -/
theorem smallEtaleSetRestrictionConjIso_hom_app (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P =
      (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.inv.app P) := rfl

/-- The inverse comparison is restriction of the counit of the comparison equivalence of
Stacks 03G1. -/
theorem smallEtaleSetRestrictionConjIso_inv_app (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleSetRestrictionConjIso B S hS h hh).inv.app P =
      (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P) := rfl

/-- **The mate of the comparison of étale restriction with spaces-étale restriction.**  It
compares reading a sheaf of sets on the small étale site of `V` on the spaces-étale site and then
restricting along spaces-étale postcomposition with an étale `h : U ⟶ V`, with restricting first
along small étale postcomposition.

The two composite restriction functors are equal on the nose
(`AlgebraicGeometry.Space.spacesEtaleSetRestriction_comp_comparisonRestriction`, itself the
site-level `AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`), and this is the
mate of that equality across the comparison equivalences of Stacks 03G1: the counit at `V`
followed by the inverse unit at `U`.

Both factors are isomorphisms, so this morphism is one too, and it is natural in `P`; neither is
recorded, because neither is used below — what is used is its single component together with
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate_counit`.  Mathlib's
`CategoryTheory.mateEquiv` would construct the natural transformation in one line and would then
supply that lemma as `CategoryTheory.unit_mateEquiv_symm`; the term below is not definitionally
the mate so adopting it means redoing that proof. -/
noncomputable def smallEtaleSetRestrictionConjMate (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
        ((smallEtaleSetRestriction B S hS h hh).obj P) ⟶
      (spacesEtaleSetRestriction B S hS h hh).obj
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P) :=
  (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
      ((smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P) ≫
    (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
      ((spacesEtaleSetRestriction B S hS h hh).obj
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P))

/-- **The comparison is compatible with the counits of Stacks 03G1.**  Restricting
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate` along the comparison functor of `U`
and following it with the restriction of the counit at `V` gives the counit at
`(smallEtaleSetRestriction h hh).obj P`.

This is what makes the comparison compute on chart sections: on the chart `h ∘ U'` of `V`
obtained from a chart `U'` of `U`, it is the identity of the sections of `P`.  The proof is the
naturality of the counit at `U` together with the triangle identity, the remaining factor being
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso_hom_app`. -/
theorem smallEtaleSetRestrictionConjMate_counit (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS U).map
          (smallEtaleSetRestrictionConjMate B S hS h hh P) ≫
        (smallEtaleSetRestriction B S hS h hh).map
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P) =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj P) := by
  have hpsi : (smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P ≫
        (smallEtaleSetRestriction B S hS h hh).map
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P) =
      𝟙 ((smallEtaleSetRestriction B S hS h hh).obj P) :=
    map_comp_map_eq_id (smallEtaleSetRestriction B S hS h hh)
      ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.inv_hom_id_app P)
  refine Eq.trans (congrArg (fun m ↦ m ≫ (smallEtaleSetRestriction B S hS h hh).map
      ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P))
    ((smallEtaleComparisonRestriction B S hS U).map_comp
      ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
        ((smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P))
      ((smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.inv.app
        ((spacesEtaleSetRestriction B S hS h hh).obj
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P))))) ?_
  refine Eq.trans (congrArg (fun m ↦
      ((smallEtaleComparisonRestriction B S hS U).map
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
            ((smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P)) ≫ m) ≫
        (smallEtaleSetRestriction B S hS h hh).map
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P))
    (restriction_map_unitIso_inv B S hS U
      ((spacesEtaleSetRestriction B S hS h hh).obj
        ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P)))) ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (smallEtaleSetRestriction B S hS h hh).map
      ((smallEtaleComparisonRestriction B S hS V).asEquivalence.counitIso.hom.app P))
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.naturality
      ((smallEtaleSetRestrictionConjIso B S hS h hh).hom.app P))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact (congrArg (fun m ↦
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
        ((smallEtaleSetRestriction B S hS h hh).obj P) ≫ m) hpsi).trans (Category.comp_id _)

end Conj

/-- The counit of the comparison equivalence of Stacks 03G1 is injective on sections: it is an
isomorphism of sheaves of sets. -/
theorem counitIso_app_injective (X : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (T : (SmallEtale B S hS X.1)ᵒᵖ)
    {a b : ((smallEtaleComparisonRestriction B S hS X).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P)).obj.obj T}
    (hab : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
          P).hom.app T a =
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
          P).hom.app T b) :
    a = b := by
  have h1 : ∀ y, ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.inv.app
        P).hom.app T
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
        P).hom.app T y) = y := fun y ↦
    congrArg (fun m ↦ m.hom.app T y)
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom_inv_id_app P)
  exact ((h1 a).symm.trans (congrArg
    (fun y ↦ ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.inv.app
      P).hom.app T y) hab)).trans (h1 b)

/-! ### The chart projections of the structure map -/

/-- **The chart projections of the structure map of Stacks 03G8.**  Restricting
`AlgebraicGeometry.Space.structureSharpSet` to an étale scheme chart of `X` above `X ×_Y V` and
reading it through the counit of the comparison equivalence of Stacks 03G1 is pullback of
regular functions along the induced morphism of charts.

This is `AlgebraicGeometry.Space.chartProjection_structureMapApp` transported from the
Kan-extension form of the direct image to the form the structure map is stated in, by
`AlgebraicGeometry.Space.restriction_map_ranIso_inv_comp_counitIso`. -/
theorem counitIso_hom_app_structureSharpSet {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (W : SmallEtale B S hS V.1)
    (j : StructuredArrow (op (chartBaseChange B S hS h W)) (comparisonFunctor B S hS U).op)
    (x : (structureSetSheaf B S hS V).obj.obj (op W)) :
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          (structureSetSheaf B S hS U)).hom.app j.right
        (((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            (structureSetSheaf B S hS U)).obj.map j.hom
          ((structureSharpSet B S hS h).hom.app (op W) x)) =
      chartPullback B S hS h W j x := by
  have e0 : (structureSharpSet B S hS h).hom.app (op W) x =
      ((smallEtaleComparisonRanIso B S hS U).inv.app
        (structureSetSheaf B S hS U)).hom.app
        (op (chartBaseChange B S hS h W)) (structureMapApp B S hS h W x) :=
    congrArg (fun m ↦ m.hom.app (op W) x) (structureSharpSet_eq B S hS h)
  have e1 : ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
          (structureSetSheaf B S hS U)).obj.map j.hom
        (((smallEtaleComparisonRanIso B S hS U).inv.app
          (structureSetSheaf B S hS U)).hom.app
          (op (chartBaseChange B S hS h W)) (structureMapApp B S hS h W x)) =
      ((smallEtaleComparisonRanIso B S hS U).inv.app
          (structureSetSheaf B S hS U)).hom.app
        ((comparisonFunctor B S hS U).op.obj j.right)
        (((smallEtaleComparisonRan B S hS U).obj (structureSetSheaf B S hS U)).obj.map j.hom
          (structureMapApp B S hS h W x)) :=
    (NatTrans.naturality_apply _ j.hom _).symm
  have e2 : ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          (structureSetSheaf B S hS U)).hom.app j.right
        (((smallEtaleComparisonRanIso B S hS U).inv.app
            (structureSetSheaf B S hS U)).hom.app
          ((comparisonFunctor B S hS U).op.obj j.right)
          (((smallEtaleComparisonRan B S hS U).obj (structureSetSheaf B S hS U)).obj.map j.hom
            (structureMapApp B S hS h W x))) =
      ((comparisonAdjunction B S hS U).counit.app (structureSetSheaf B S hS U)).hom.app j.right
        (((smallEtaleComparisonRan B S hS U).obj (structureSetSheaf B S hS U)).obj.map j.hom
          (structureMapApp B S hS h W x)) :=
    congrArg (fun m ↦ m.hom.app j.right
        (((smallEtaleComparisonRan B S hS U).obj (structureSetSheaf B S hS U)).obj.map j.hom
          (structureMapApp B S hS h W x)))
      (restriction_map_ranIso_inv_comp_counitIso B S hS U (structureSetSheaf B S hS U))
  refine Eq.trans ?_ (chartProjection_structureMapApp B S hS h W j x)
  refine Eq.trans (congrArg (fun y ↦
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
          (structureSetSheaf B S hS U)).hom.app j.right
        (((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj
            (structureSetSheaf B S hS U)).obj.map j.hom y)) e0) ?_
  exact (congrArg (fun y ↦
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.counitIso.hom.app
      (structureSetSheaf B S hS U)).hom.app j.right y) e1).trans e2

/-! ### The Beck-Chevalley square and the chart morphisms -/

section Square

variable {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` is the Beck-Chevalley isomorphism of
the cartesian square: it was obtained from it by cancelling the fully faithful inclusion of the
étale objects into the slice, so including it again returns that isomorphism. -/
theorem spacesEtaleBaseChangeSquare_inclusion (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (W : SpacesEtale B S hS Y') :
    (SpacesEtale.inclusion B S hS X).map
        ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app W) =
      (Over.beckChevalleyIso sq).hom.app ((SpacesEtale.inclusion B S hS Y').obj W) :=
  (SpacesEtale.inclusion B S hS X).map_preimage _

/-- **The square of Stacks 03LR is compatible with the cartesian projections.**  Going along
`AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` from `X' ×_{Y'} W`, read over `X`, to
`X ×_Y (g ∘ W)` and then projecting to `g ∘ W` is the projection of `X' ×_{Y'} W` to `W`.

Both projections are first projections of chosen fibre products, and the isomorphism is the
comparison `CategoryTheory.IsPullback.isoPullback` of the pasting of the two cartesian squares
with the chosen fibre product, so this is
`CategoryTheory.IsPullback.isoPullback_hom_fst`. -/
theorem spacesEtaleBaseChangeSquare_projection (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (W : SpacesEtale B S hS Y') :
    (SpacesEtale.toSpaces B S hS X).map
          ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app W) ≫
        (spacesBaseChange B S hS f).projection.app
          ((spacesEtalePostcomp B S hS g hg).obj W) =
      (spacesBaseChange B S hS f').projection.app W := by
  have h2 := congrArg (fun m ↦ m.left)
    (spacesEtaleBaseChangeSquare_inclusion B S hS i f' f g sq hg W)
  simp only [Over.beckChevalleyIso, NatIso.ofComponents_hom_app, Over.beckChevalleyObjIso,
    Over.isoMk_hom_left] at h2
  refine Eq.trans (congrArg (fun m ↦ m ≫ (spacesBaseChange B S hS f).projection.app
    ((spacesEtalePostcomp B S hS g hg).obj W)) h2) ?_
  exact IsPullback.isoPullback_hom_fst _

/-- **The chart morphism of a base change.**  Let `V` be an étale scheme chart of `Y'` and let
`U'` be an étale scheme chart of `X'` above `X' ×_{Y'} V`.  Then `U'`, read through
`AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` as an étale scheme chart of `X` above
`X ×_Y (g ∘ V)`, induces on `V` the same morphism of schemes as `U'` does on `V` for `f'`.

This is the geometric content of the base-change compatibility of the structure maps: the two
cartesian projections agree by
`AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare_projection`, and spaces-étale
postcomposition leaves the underlying algebraic spaces and morphisms unchanged. -/
theorem chartBaseChangeMap_baseChangeSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hi : IsEtale B S hS i.hom) (V : SmallEtale B S hS Y'.1)
    (k : StructuredArrow (op (chartBaseChange B S hS f' V))
      (comparisonFunctor B S hS X').op) :
    chartBaseChangeMap B S hS f ((smallEtalePostcomp B S hS g hg).obj V)
        (StructuredArrow.mk (Y := op ((smallEtalePostcomp B S hS i hi).obj k.right.unop))
          ((spacesEtalePostcomp B S hS i hi).map k.hom.unop ≫
            (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
              ((comparisonFunctor B S hS Y').obj V)).op) =
      chartBaseChangeMap B S hS f' V k := by
  have key : (SpacesEtale.toSpaces B S hS X).map
          ((spacesEtalePostcomp B S hS i hi).map k.hom.unop ≫
            (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
              ((comparisonFunctor B S hS Y').obj V)) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj ((smallEtalePostcomp B S hS g hg).obj V)) =
      (SpacesEtale.toSpaces B S hS X').map k.hom.unop ≫
        (spacesBaseChange B S hS f').projection.app
          ((comparisonFunctor B S hS Y').obj V) := by
    refine Eq.trans (congrArg (fun m ↦ m ≫ (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj ((smallEtalePostcomp B S hS g hg).obj V)))
      ((SpacesEtale.toSpaces B S hS X).map_comp
        ((spacesEtalePostcomp B S hS i hi).map k.hom.unop)
        ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
          ((comparisonFunctor B S hS Y').obj V)))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map
        ((spacesEtalePostcomp B S hS i hi).map k.hom.unop) ≫ m)
      (spacesEtaleBaseChangeSquare_projection B S hS i f' f g sq hg
        ((comparisonFunctor B S hS Y').obj V))
  exact yoneda.map_injective ((yoneda_map_chartBaseChangeMap B S hS f _ _).trans
    ((congrArg (fun m ↦ m.hom) key).trans (yoneda_map_chartBaseChangeMap B S hS f' V k).symm))

/-- Pullback of regular functions along the two chart morphisms of
`AlgebraicGeometry.Space.chartBaseChangeMap_baseChangeSquare` agree. -/
theorem chartPullback_baseChangeSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hi : IsEtale B S hS i.hom) (V : SmallEtale B S hS Y'.1)
    (k : StructuredArrow (op (chartBaseChange B S hS f' V))
      (comparisonFunctor B S hS X').op)
    (x : (structureSetSheaf B S hS Y').obj.obj (op V)) :
    chartPullback B S hS f ((smallEtalePostcomp B S hS g hg).obj V)
        (StructuredArrow.mk (Y := op ((smallEtalePostcomp B S hS i hi).obj k.right.unop))
          ((spacesEtalePostcomp B S hS i hi).map k.hom.unop ≫
            (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
              ((comparisonFunctor B S hS Y').obj V)).op) x =
      chartPullback B S hS f' V k x :=
  congrArg (fun m ↦ ((forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) x)
    (chartBaseChangeMap_baseChangeSquare B S hS i f' f g sq hg hi V k)

end Square

/-! ### The base-change isomorphism of Stacks 03LR on sections -/

section BaseChange

variable {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Stacks 03LR, part (1) on the spaces-étale sites, on sections.**  Both sides of
`AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso` are restriction along a composite of
functors of sites, so the comparison is reindexing along the inverse of the Beck-Chevalley
isomorphism of the square. -/
theorem spacesSetPushforwardBaseChangeIso_hom_app (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (Z : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (W : SpacesEtale B S hS Y')
    (z : ((spacesEtaleSetRestriction B S hS i
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
          spacesSetBaseChange B S hS f').obj Z).obj.obj (op W)) :
    ((spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app Z).hom.app (op W) z =
      Z.obj.map ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).inv.app W).op z := rfl

/-- The last two factors of `AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso`
cancel: they are the restriction along small étale postcomposition with `g` of the two sides of
the triangle identity of the comparison equivalence of Stacks 03G1 at `Y`. -/
theorem smallEtaleSetRestrictionConjIso_unit_cancel (hg : IsEtale B S hS g.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (spacesEtaleSetRestriction B S hS g hg ⋙
          smallEtaleComparisonRestriction B S hS Y').map
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.hom.app
          ((spacesSetBaseChange B S hS f).obj
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
      (smallEtaleSetRestrictionConjIso B S hS g hg).inv.app
        ((smallEtaleDirectImage B S hS f).obj P) =
    𝟙 ((smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg).obj P) := by
  refine Eq.trans (congrArg (fun m ↦
      (spacesEtaleSetRestriction B S hS g hg ⋙
            smallEtaleComparisonRestriction B S hS Y').map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.hom.app
            ((spacesSetBaseChange B S hS f).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫ m)
    (smallEtaleSetRestrictionConjIso_inv_app B S hS g hg
      ((smallEtaleDirectImage B S hS f).obj P))) ?_
  exact map_comp_map_eq_id (smallEtaleSetRestriction B S hS g hg)
    ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.functor_unitIso_comp
      ((spacesSetBaseChange B S hS f).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P)))

/-- The five factors of `AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso`, written
out: the comparison of the restriction along `i` with its conjugate, the two conjugation
comparisons, the spaces-étale statement, and the comparison of the restriction along `g` with
its conjugate.  Composition and `CategoryTheory.Category.assoc` are pointwise in these sheaf
categories, so this holds by `rfl`. -/
theorem smallEtaleSetPushforwardBaseChangeIso_hom_app_split (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hi : IsEtale B S hS i.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app P =
      ((smallEtaleDirectImage B S hS f').map
            ((smallEtaleSetRestrictionConjIso B S hS i hi).hom.app P) ≫
          (spacesSetBaseChange B S hS f' ⋙
              smallEtaleComparisonRestriction B S hS Y').map
            ((smallEtaleComparisonRestriction B S hS X').asEquivalence.unitIso.inv.app
              ((spacesEtaleSetRestriction B S hS i hi).obj
                ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
          (smallEtaleComparisonRestriction B S hS Y').map
            ((spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
        ((spacesEtaleSetRestriction B S hS g hg ⋙
              smallEtaleComparisonRestriction B S hS Y').map
            ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.hom.app
              ((spacesSetBaseChange B S hS f).obj
                ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
          (smallEtaleSetRestrictionConjIso B S hS g hg).inv.app
            ((smallEtaleDirectImage B S hS f).obj P)) := rfl

/-- **Stacks 03LR, part (1) on the small étale sites, on sections.**  On the sections over an
étale scheme chart `V` of `Y'`, the base-change isomorphism is the canonical comparison
`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjMate` followed by reindexing along the
Beck-Chevalley isomorphism of the square.

The two conjugation comparisons at `Y` cancel against the comparison of the restriction along
`g` with its conjugate
(`AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso_unit_cancel`), and the remaining three
factors are, on sections, exactly that comparison followed by the spaces-étale statement. -/
theorem smallEtaleSetPushforwardBaseChangeIso_hom_app (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hi : IsEtale B S hS i.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y'.1)
    (w : ((smallEtaleSetRestriction B S hS i hi ⋙
        smallEtaleDirectImage B S hS f').obj P).obj.obj (op V)) :
    ((smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app P).hom.app
        (op V) w =
      ((spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P)).hom.app
        (op ((comparisonFunctor B S hS Y').obj V))
        ((smallEtaleSetRestrictionConjMate B S hS i hi P).hom.app
          (op (chartBaseChange B S hS f' V)) w) := by
  have h1 : (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app P =
      (smallEtaleDirectImage B S hS f').map
          ((smallEtaleSetRestrictionConjIso B S hS i hi).hom.app P) ≫
        (spacesSetBaseChange B S hS f' ⋙
            smallEtaleComparisonRestriction B S hS Y').map
          ((smallEtaleComparisonRestriction B S hS X').asEquivalence.unitIso.inv.app
            ((spacesEtaleSetRestriction B S hS i hi).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P))) ≫
        (smallEtaleComparisonRestriction B S hS Y').map
          ((spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P)) := by
    refine (smallEtaleSetPushforwardBaseChangeIso_hom_app_split B S hS i f' f g sq hg
      hi P).trans ?_
    refine Eq.trans (congrArg (fun m ↦ _ ≫ m)
      (smallEtaleSetRestrictionConjIso_unit_cancel B S hS f g hg P)) ?_
    exact Category.comp_id _
  exact congrArg (fun m : (smallEtaleSetRestriction B S hS i hi ⋙
        smallEtaleDirectImage B S hS f').obj P ⟶
      (smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg).obj P ↦
    m.hom.app (op V) w) h1

/-! ### The base-change compatibility of the structure maps -/

/-- **The base-change compatibility of the structure map of Stacks 03G8, on sheaves of sets.**
The structure map of `f'`, followed by the base-change isomorphism of Stacks 03LR, part (1), is
the étale restriction along `g` of the structure map of `f`.

Both sides are morphisms into the restriction along `g` of the direct image along `f` of the
structure sheaf of `X`.  Over an étale scheme chart `V` of `Y'` the sections of that sheaf are
the sections of the direct image over `g ∘ V`, hence — after reindexing along the
Beck-Chevalley isomorphism — a section of the structure sheaf of `X` over the algebraic space
`X' ×_{Y'} V`, and such a section is determined by its restrictions to the étale scheme charts
of `X'` above `X' ×_{Y'} V`
(`AlgebraicGeometry.Space.spacesEtale_section_ext`).  On each such chart `U'` both sides are
pullback of regular functions along the induced morphism of schemes `U' ⟶ V`: for the left-hand
side by `AlgebraicGeometry.Space.counitIso_hom_app_structureSharpSet` for `f'`, for the
right-hand side by the same lemma for `f` together with
`AlgebraicGeometry.Space.chartPullback_baseChangeSquare`, which is where the cartesianness of
the square enters. -/
theorem structureSharpSet_comp_smallEtaleSetPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (hi : IsEtale B S hS i.hom) :
    structureSharpSet B S hS f' ≫
        (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app
          (structureSetSheaf B S hS X) =
      (smallEtaleSetRestriction B S hS g hg).map (structureSharpSet B S hS f) := by
  refine Sheaf.hom_ext_sections (fun V x ↦ ?_)
  have hkey : (smallEtaleSetRestrictionConjMate B S hS i hi
          (structureSetSheaf B S hS X)).hom.app
        (op (chartBaseChange B S hS f' V.unop))
        ((structureSharpSet B S hS f').hom.app V x) =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
          (structureSetSheaf B S hS X)).obj.map
        ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
          ((comparisonFunctor B S hS Y').obj V.unop)).op
        ((structureSharpSet B S hS f).hom.app
          (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) x) := by
    refine spacesEtale_section_ext B S hS X' (chartBaseChange B S hS f' V.unop)
      ((spacesEtaleSetRestriction B S hS i hi).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
          (structureSetSheaf B S hS X))) (fun k ↦ ?_)
    refine counitIso_app_injective B S hS X (structureSetSheaf B S hS X)
      (op ((smallEtalePostcomp B S hS i hi).obj k.right.unop)) ?_
    have hL : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
            (structureSetSheaf B S hS X)).hom.app
          (op ((smallEtalePostcomp B S hS i hi).obj k.right.unop))
          (((spacesEtaleSetRestriction B S hS i hi).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
                (structureSetSheaf B S hS X))).obj.map k.hom
            ((smallEtaleSetRestrictionConjMate B S hS i hi
                (structureSetSheaf B S hS X)).hom.app
              (op (chartBaseChange B S hS f' V.unop))
              ((structureSharpSet B S hS f').hom.app V x))) =
        chartPullback B S hS f' V.unop k x := by
      refine Eq.trans (congrArg (fun y ↦
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
            (structureSetSheaf B S hS X)).hom.app
          (op ((smallEtalePostcomp B S hS i hi).obj k.right.unop)) y)
        (NatTrans.naturality_apply
          (smallEtaleSetRestrictionConjMate B S hS i hi
            (structureSetSheaf B S hS X)).hom k.hom
          ((structureSharpSet B S hS f').hom.app V x)).symm) ?_
      refine Eq.trans (congrArg (fun m : (smallEtaleComparisonRestriction B S hS X').obj
            ((smallEtaleComparisonRestriction B S hS X').asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS i hi).obj
                (structureSetSheaf B S hS X))) ⟶
          (smallEtaleSetRestriction B S hS i hi).obj (structureSetSheaf B S hS X) ↦
        m.hom.app k.right
          (((smallEtaleComparisonRestriction B S hS X').asEquivalence.inverse.obj
              ((smallEtaleSetRestriction B S hS i hi).obj
                (structureSetSheaf B S hS X))).obj.map k.hom
            ((structureSharpSet B S hS f').hom.app V x)))
        (smallEtaleSetRestrictionConjMate_counit B S hS i hi
          (structureSetSheaf B S hS X))) ?_
      exact counitIso_hom_app_structureSharpSet B S hS f' V.unop k x
    have hR : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
            (structureSetSheaf B S hS X)).hom.app
          (op ((smallEtalePostcomp B S hS i hi).obj k.right.unop))
          (((spacesEtaleSetRestriction B S hS i hi).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
                (structureSetSheaf B S hS X))).obj.map k.hom
            (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
                (structureSetSheaf B S hS X)).obj.map
              ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
                ((comparisonFunctor B S hS Y').obj V.unop)).op
              ((structureSharpSet B S hS f).hom.app
                (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) x))) =
        chartPullback B S hS f' V.unop k x := by
      refine Eq.trans (congrArg (fun y ↦
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app
            (structureSetSheaf B S hS X)).hom.app
          (op ((smallEtalePostcomp B S hS i hi).obj k.right.unop)) y)
        (Functor.map_comp_apply
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
            (structureSetSheaf B S hS X)).obj
          ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
            ((comparisonFunctor B S hS Y').obj V.unop)).op
          ((spacesEtalePostcomp B S hS i hi).map k.hom.unop).op
          ((structureSharpSet B S hS f).hom.app
            (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) x)).symm) ?_
      refine Eq.trans (counitIso_hom_app_structureSharpSet B S hS f
        ((smallEtalePostcomp B S hS g hg).obj V.unop)
        (StructuredArrow.mk (Y := op ((smallEtalePostcomp B S hS i hi).obj k.right.unop))
          ((spacesEtalePostcomp B S hS i hi).map k.hom.unop ≫
            (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
              ((comparisonFunctor B S hS Y').obj V.unop)).op) x) ?_
      exact chartPullback_baseChangeSquare B S hS i f' f g sq hg hi V.unop k x
    exact hL.trans hR.symm
  refine Eq.trans (smallEtaleSetPushforwardBaseChangeIso_hom_app B S hS i f' f g sq hg hi
    (structureSetSheaf B S hS X) V.unop ((structureSharpSet B S hS f').hom.app V x)) ?_
  refine Eq.trans (spacesSetPushforwardBaseChangeIso_hom_app B S hS i f' f g sq hg
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
      (structureSetSheaf B S hS X)) ((comparisonFunctor B S hS Y').obj V.unop) _) ?_
  refine Eq.trans (congrArg (fun y ↦
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
        (structureSetSheaf B S hS X)).obj.map
      ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).inv.app
        ((comparisonFunctor B S hS Y').obj V.unop)).op y) hkey) ?_
  refine Eq.trans (Functor.map_comp_apply
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
      (structureSetSheaf B S hS X)).obj
    ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom.app
      ((comparisonFunctor B S hS Y').obj V.unop)).op
    ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).inv.app
      ((comparisonFunctor B S hS Y').obj V.unop)).op
    ((structureSharpSet B S hS f).hom.app
      (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) x)).symm ?_
  refine Eq.trans (congrArg (fun m ↦
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
        (structureSetSheaf B S hS X)).obj.map m
      ((structureSharpSet B S hS f).hom.app
        (op ((smallEtalePostcomp B S hS g hg).obj V.unop)) x))
    (congrArg Quiver.Hom.op ((spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).inv_hom_id_app
      ((comparisonFunctor B S hS Y').obj V.unop)))) ?_
  exact ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
    (structureSetSheaf B S hS X)).obj.map_id_apply _ _

end BaseChange

/-! ### The ring-level statement and Stacks 03LX for the ordinary direct image -/

section Ring

variable {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The comparison of the étale restriction of the structure sheaf with the structure sheaf is
the identity on underlying sheaves of sets. -/
theorem ringSheafMap_etaleStructureRingIso_inv (hi : IsEtale B S hS i.hom) :
    (sheafCompose (SmallEtale.topology B S hS X'.1) (forget RingCat.{u})).map
        (etaleStructureRingIso B S hS i hi).inv =
      𝟙 (structureSetSheaf B S hS X') := rfl

/-- The comparison of `f'_*𝒪_{X'}` with the iterated transport of `𝒪_X` is the identity on
underlying sheaves of sets: it is the direct image of the previous comparison. -/
theorem ringSheafMap_etaleBaseChangeRingComparison_inv (hi : IsEtale B S hS i.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (etaleBaseChangeRingComparison B S hS i f' hi).inv =
      𝟙 ((smallEtaleDirectImage B S hS f').obj (structureSetSheaf B S hS X')) :=
  (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS Y'.1)
    (smallEtaleDirectImage B S hS f')
    (etaleStructureRingIso B S hS i hi).inv).trans
    ((congrArg (smallEtaleDirectImage B S hS f').map
        (ringSheafMap_etaleStructureRingIso_inv B S hS i hi)).trans
      ((smallEtaleDirectImage B S hS f').map_id _))

/-- The comparison of the iterated transport of `𝒪_X` with the transport along the composite is
the identity on underlying sheaves of sets. -/
theorem ringSheafMap_etaleBaseChangeRingCompIso_hom (hi : IsEtale B S hS i.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (etaleBaseChangeRingCompIso B S hS i f' hi).hom =
      𝟙 ((smallEtaleDirectImage B S hS f').obj (structureSetSheaf B S hS X')) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **`AlgebraicGeometry.Space.baseChangeStructureSharp` is the structure map of `f'`.**  On
underlying sheaves of sets the two ring comparisons it is composed of are identities, so it is
`AlgebraicGeometry.Space.structureSharpSet` of `f'`. -/
theorem ringSheafMap_baseChangeStructureSharp (hi : IsEtale B S hS i.hom) :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (baseChangeStructureSharp B S hS i f' hi) =
      structureSharpSet B S hS f' :=
  ((sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map_comp
      (structureSharp B S hS f' ≫ (etaleBaseChangeRingComparison B S hS i f' hi).inv)
      (etaleBaseChangeRingCompIso B S hS i f' hi).hom).trans
    (((congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS Y'.1)
            (forget RingCat.{u})).map
          (structureSharp B S hS f' ≫ (etaleBaseChangeRingComparison B S hS i f' hi).inv) ≫ m)
        (ringSheafMap_etaleBaseChangeRingCompIso_hom B S hS i f' hi)).trans
      (Category.comp_id ((sheafCompose (SmallEtale.topology B S hS Y'.1)
        (forget RingCat.{u})).map
        (structureSharp B S hS f' ≫ (etaleBaseChangeRingComparison B S hS i f' hi).inv)))).trans
      (((sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map_comp
          (structureSharp B S hS f') (etaleBaseChangeRingComparison B S hS i f' hi).inv).trans
        ((congrArg (fun m ↦ structureSharpSet B S hS f' ≫ m)
            (ringSheafMap_etaleBaseChangeRingComparison_inv B S hS i f' hi)).trans
          (Category.comp_id (structureSharpSet B S hS f')))))

/-- **The base-change compatibility of the structure maps of Stacks 03G8.**  For a cartesian
square

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

of algebraic spaces over a scheme `S` contained in a big fppf site `B`, with `g` étale, the
structure map of `f'` — read through the two ring comparisons as a structure map for the
transport of `𝒪_X` along `(-)|_{X'} ⋙ f'_*` — corresponds, under the comparison of the two
transported structure sheaves induced by Stacks 03LR, part (1), to the étale restriction along
`g` of the structure map of `f`.

This is exactly the hypothesis `hsharp` of
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp`, so it makes the
ordinary statement of Stacks 03LX unconditional; see
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`.

Forgetting the ring structures is faithful, and after forgetting them the two ring comparisons
become identities, so the statement is
`AlgebraicGeometry.Space.structureSharpSet_comp_smallEtaleSetPushforwardBaseChangeIso`.

The statement is **not** part of Stacks 03G8, which asserts the existence of the morphism of
ringed topoi together with its compatibility with composition and its agreement with the
construction for schemes, and it is not part of Stacks 03LR either, which is about sheaves of
sets; so it carries no attribute of its own. -/
theorem baseChangeStructureSharp_comp_baseChangeRingMap (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    baseChangeStructureSharp B S hS i f'
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ≫
        baseChangeRingMap B S hS i f' f g sq hg =
      (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f) := by
  apply (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map_injective
  refine Eq.trans ((sheafCompose (SmallEtale.topology B S hS Y'.1)
    (forget RingCat.{u})).map_comp
      (baseChangeStructureSharp B S hS i f'
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (baseChangeRingMap B S hS i f' f g sq hg)) ?_
  refine Eq.trans (congrArg (fun p ↦ p ≫ (sheafCompose (SmallEtale.topology B S hS Y'.1)
      (forget RingCat.{u})).map (baseChangeRingMap B S hS i f' f g sq hg))
    (ringSheafMap_baseChangeStructureSharp B S hS i f'
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))) ?_
  refine Eq.trans (congrArg (fun q ↦ structureSharpSet B S hS f' ≫ q)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y'.1)
      (structureRingSheaf B S hS X)
      (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom)) ?_
  exact structureSharpSet_comp_smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)

/-- **Stacks 03LX, the ordinary direct image, unconditionally.**  Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Then for every `𝒪_X`-module `F`

`f'_*(F|_{X'}) = (f_*F)|_{Y'}`

in `Mod(𝒪_{Y'})`, naturally in `F`.

This is `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp` with its
hypothesis discharged by
`AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap`.  The higher direct
images of Stacks 03LX are not treated, so the attribute carries a part string; the footnote is
`AlgebraicGeometry.Space.modulePullbackSquareIso`.

The restriction `(-)|_{X'}` is read here as `AlgebraicGeometry.Space.etaleModulePullback`,
restriction of modules along small étale postcomposition, which is the reading of the ordinary
clause; the footnote is proved in the inverse-image reading instead, for the reason recorded in
its own docstring.

Inherited caveat.  The source asserts an equality, and this isomorphism has the right endpoints
but is **not** proved to be the adjunction mate of the inverse-image identification around the
square: that is already the standing in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardBaseChange.lean`, whose
implementation notes record it for
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso`, and the same applies to the
`Type u` instance of Stacks 03LR, part (1) that this isomorphism is built from.

The module universe is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePushforward` exists. -/
@[stacks 03LX "the ordinary direct image"]
noncomputable def modulePushforwardEtaleBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        modulePushforward B S hS f' ≅
      modulePushforward B S hS f ⋙ etaleModulePullback B S hS g hg :=
  modulePushforwardEtaleBaseChangeIsoOfStructureSharp B S hS i f' f g sq hg
    (baseChangeStructureSharp_comp_baseChangeRingMap B S hS i f' f g sq hg)

end Ring

end AlgebraicGeometry.Space

end
