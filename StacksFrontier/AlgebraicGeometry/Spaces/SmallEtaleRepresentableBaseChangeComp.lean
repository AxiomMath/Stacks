module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Chart base change of a representable algebraic space is compatible with composition

`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` identifies, for a morphism
`g : T' ⟶ T` of the big fppf category over `S`, base change of étale scheme charts along the
represented morphism of algebraic spaces with base change of schemes along `g`, across the
identification `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` of the small étale site
of `yoneda.obj U` with the small étale site of the scheme underlying `U`.  This file proves that
those identifications paste: for `h : T'' ⟶ T'` and `g : T' ⟶ T`, pasting the square of `h`
against the square of `g` and contracting the two base changes on each side gives the square of
`h ≫ g`.

Both sides are morphisms into a chosen fibre product of schemes, so the equality is checked on
the two cartesian projections.  The projection to `T''` is automatic, both sides being morphisms
over `T''`; the projection to the chart is the triangle of cartesian projections
`AlgebraicGeometry.Space.toOver_map_chartBaseChangeCompComparison_comp_snd`, read through the
two representability squares.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeChartFactoredCompIso` is
  `AlgebraicGeometry.Space.smallBaseChangeChartCompIso` at a chosen factorisation `h ≫ g = k` of
  the composite, which is what is needed when the composite arrow is presented by a term that is
  only provably, not syntactically, equal to `h ≫ g`.

## Main results

* `AlgebraicGeometry.Space.representedSpaceMap_comp`: the morphisms of algebraic spaces
  represented by a composite compose.
* `AlgebraicGeometry.Space.representedSmallEtaleBaseChange_hom_app_comp_fst`: the comparison of
  the two base changes at a chart, followed by the cartesian projection to the chart, is the
  cartesian projection of the representability witness.
* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_comp`: **chart base change of a
  representable algebraic space is compatible with composition**, as an equality of
  isomorphisms of functors of small étale sites.

## Implementation notes

The morphism of algebraic spaces represented by `h ≫ g` is only *provably* the composite of the
morphisms represented by `h` and by `g` — `yoneda.map (h ≫ g)` and
`yoneda.map h ≫ yoneda.map g` are not syntactically equal — so the base-changed chart below the
composite cannot be compared with the iterated base-changed chart by the existing
`AlgebraicGeometry.Space.smallBaseChangeChartCompIso`, whose composite is the literal `h ≫ g`.
Each statement about the composite is therefore proved in the factored form, at a variable `k`
with `hk : h ≫ g = k`, by `subst hk`; the representability witness is a proposition, so after
the substitution the witness supplied for `k` is the one the unfactored statement quantifies
over and no transport remains.  This is the idiom of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`.

The proof of the chart identity is written as explicit applications of `Eq.trans` and
`congrArg` rather than with `rw` or `simp`: the base-changed chart has two definitionally equal
spellings — as an object of the small étale site of the scheme underlying `T''` and as the chosen
fibre product of schemes — and the syntactic matching of `rw` and of `simp`'s discrimination tree
does not see through them, while the unifier of `refine` does.

No tag is registered.  Stacks 03G2, part (4) is tagged on the base change of charts
`AlgebraicGeometry.Space.smallBaseChange` itself, and
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` carries no tag either; what is
added here is that this identification is functorial in the morphism.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Chart base change at a factorisation of the composite -/

section Factored

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C) (k : D ⟶ C)
    (hk : h ≫ g = k)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrepk : yoneda.relativelyRepresentable k.hom)

/-- The comparison of base change of étale scheme charts along a chosen factorisation
`h ≫ g = k` of the composite with the iterated base change.

This is `AlgebraicGeometry.Space.smallBaseChangeChartCompIso` transported along the
factorisation; see the implementation notes for why the transport is needed. -/
noncomputable def smallBaseChangeChartFactoredCompIso :
    smallBaseChange B S hS k hrepk ≅
      smallBaseChange B S hS g hrepg ⋙ smallBaseChange B S hS h hreph := by
  subst hk
  exact smallBaseChangeChartCompIso B S hS h g hreph hrepg hrepk

/-- **The structure maps of base change of étale scheme charts compose**, at a chosen
factorisation of the composite: this is
`AlgebraicGeometry.Space.smallBaseChangeSharp_comparisonComp` transported along the
factorisation, in the shape `SheafOfModules.pushforwardCongr₂` consumes. -/
theorem smallBaseChangeSharp_factoredComparisonComp :
    SheafOfModules.comparisonComp (smallBaseChangeSharp B S hS g hrepg)
          (smallBaseChangeSharp B S hS h hreph) ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (smallBaseChangeChartFactoredCompIso B S hS h g k hk hreph hrepg hrepk).hom
            RingCat.{u} (SmallEtale.topology B S hS C.1) (SmallEtale.topology B S hS D.1)).app
          (smallEtaleRingSheaf B S hS D.1 D.2) =
      smallBaseChangeSharp B S hS k hrepk := by
  subst hk
  exact smallBaseChangeSharp_comparisonComp B S hS h g hreph hrepg hrepk

/-- **The triangle of cartesian projections**, at a chosen factorisation of the composite: the
comparison of the base-changed chart of `k` with the iterated base-changed chart, followed by the
two cartesian projections, is the cartesian projection of `k`.

This is `AlgebraicGeometry.Space.toOver_map_chartBaseChangeCompComparison_comp_snd` transported
along the factorisation. -/
theorem toOver_map_chartBaseChangeFactoredCompComparison_comp_snd
    (V : SmallEtale B S hS C.1) :
    (SmallEtale.toOver B S hS D.1).map
          ((smallBaseChangeChartFactoredCompIso B S hS h g k hk hreph hrepg hrepk).hom.app V) ≫
        hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom ≫ hrepg.snd V.1.hom =
      hrepk.snd V.1.hom := by
  subst hk
  exact toOver_map_chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrepk V

end Factored

/-! ### The composition law of the two base changes -/

section RepComp

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- **The morphisms of representable algebraic spaces represented by a composite compose.**
`AlgebraicGeometry.Space.representedSpaceMap` is the Yoneda image, and `yoneda` is a functor. -/
theorem representedSpaceMap_comp :
    representedSpaceMap B S hS h ≫ representedSpaceMap B S hS g =
      representedSpaceMap B S hS (h ≫ g) :=
  ObjectProperty.hom_ext _ (yoneda.map_comp h g).symm

/-- **The comparison of the two base changes at a chart, followed by the cartesian projection to
the chart.**  Over an étale chart `V` of `yoneda.obj T` the comparison of the chart base change
with the chosen fibre product of schemes carries the projection of the chosen fibre product to
the projection of the representability witness; this is the defining property of the comparison
of two fibre products of the same cospan. -/
theorem representedSmallEtaleBaseChange_hom_app_comp_fst
    (V : SmallEtale B S hS (yoneda.obj T)) :
    ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app V).hom.left ≫
        pullback.fst (yonedaEquiv V.1.hom).left g.left = (hg.snd V.1.hom).left :=
  (isPullback_representedChart_schemes B S hS g hg V).isoIsPullback_hom_fst _ _ _

/-- **Chart base change of a representable algebraic space is compatible with composition, at a
chart.**  Over an étale chart `V` of `yoneda.obj T` both routes from the iterated base-changed
chart `(V ×_T T') ×_{T'} T''` to the base-changed chart `V ×_T T''` of schemes are morphisms
into a chosen fibre product, so they agree as soon as their two cartesian projections do: the
projection to `T''` holds because both are morphisms over `T''`, and the projection to `V` is
the triangle of cartesian projections of the charts. -/
theorem representedSmallEtaleBaseChange_comp_component
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (representedSmallEtaleEquivalence B S hS T'').functor.map
          ((smallBaseChangeChartFactoredCompIso B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
            (representedSpaceMap_comp B S hS h g) hh hg hhg).hom.app V) ≫
        (representedSmallEtaleBaseChangeIso B S hS h hh).hom.app
          ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V) ≫
        (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) h.left).map
          ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app V) ≫
        (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
            (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left
            (h ≫ g).left rfl).hom.app
          ((representedSmallEtaleEquivalence B S hS T).functor.obj V) =
      (representedSmallEtaleBaseChangeIso B S hS (h ≫ g) hhg).hom.app V := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine pullback.hom_ext ?_ ?_
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
      (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst
        (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left (h ≫ g).left rfl
        ((representedSmallEtaleEquivalence B S hS T).functor.obj V))) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z ≫ _) (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
      (representedSmallEtaleBaseChange_hom_app_comp_fst B S hS g hg V)) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun z => _ ≫ z ≫ _)
      (representedSmallEtaleBaseChange_hom_app_comp_fst B S hS h hh
        ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V))) ?_
    refine Eq.trans ?_
      (representedSmallEtaleBaseChange_hom_app_comp_fst B S hS (h ≫ g) hhg V).symm
    exact congrArg Over.Hom.left
      (toOver_map_chartBaseChangeFactoredCompComparison_comp_snd B S hS
        (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
        (representedSpaceMap B S hS (h ≫ g)) (representedSpaceMap_comp B S hS h g) hh hg hhg V)
  · exact (Over.w _).trans (Over.w _).symm

/-- **Chart base change of a representable algebraic space is compatible with composition.**
For `h : T'' ⟶ T'` and `g : T' ⟶ T` of the big fppf category over `S`, contracting the two chart
base changes, pasting the square of `h` against the square of `g` and contracting the two base
changes of schemes is the square of `h ≫ g`.

Both sides are isomorphisms of functors into the small étale site of the scheme underlying
`T''`, so the equality is checked at a chart, where it is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChange_comp_component`. -/
theorem representedSmallEtaleBaseChangeIso_comp :
    Functor.isoWhiskerRight
          (smallBaseChangeChartFactoredCompIso B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
            (representedSpaceMap_comp B S hS h g) hh hg hhg)
          ((representedSmallEtaleEquivalence B S hS T'').functor) ≪≫
        Functor.isoWhiskerLeft
          (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
          (representedSmallEtaleBaseChangeIso B S hS h hh) ≪≫
        Functor.isoWhiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg)
          (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) h.left) ≪≫
        Functor.isoWhiskerLeft ((representedSmallEtaleEquivalence B S hS T).functor)
          (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
            (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left
            (h ≫ g).left rfl) =
      representedSmallEtaleBaseChangeIso B S hS (h ≫ g) hhg :=
  Iso.ext (NatTrans.ext (funext fun V =>
    representedSmallEtaleBaseChange_comp_component B S hS h g hh hg hhg V))

end RepComp

end AlgebraicGeometry.Space

end
