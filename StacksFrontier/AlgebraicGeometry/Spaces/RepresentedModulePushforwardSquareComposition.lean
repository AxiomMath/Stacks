module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCongrComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartFactoredComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardSquareComp
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonConjugate

/-!
# The square of small étale ringed sites of a representable morphism, composed

For a morphism `g : T' ⟶ T` of the big fppf category over `S`,
`AlgebraicGeometry.Space.representedStructureMapRing_square` says that the two routes round the
square of small étale ringed sites — the identification of the site of `yoneda.obj T` with the
site of the scheme underlying `T` followed by base change of schemes, and base change of étale
scheme charts followed by the identification for `T'` — carry the structure sheaf of `T` to the
structure sheaf of `T'` by the same map.  This file proves that those squares are compatible
with composition, and uses that to compose
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, the comparison of the two
direct images of sheaves of modules round the square.

## Main results

* `AlgebraicGeometry.Space.representedStructureMapRing_square_schemeComp`,
  `AlgebraicGeometry.Space.representedStructureMapRing_square_whiskerRight`,
  `AlgebraicGeometry.Space.representedStructureMapRing_square_whiskerLeft` and
  `AlgebraicGeometry.Space.representedStructureMapRing_square_chartComp`: **the composition
  compatibility of `AlgebraicGeometry.Space.representedStructureMapRing_square`.**  The sites
  level composition law
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_eq_factoredComp` decomposes the
  comparison of the two routes along a composite into four factors; these are the four
  structure-map compatibilities, one per factor, that the transport of a direct image of sheaves
  of modules along each factor asks for.
* `AlgebraicGeometry.Space.representedStructureMapRing_squareTransport_comp`: **the transport
  of the direct image of sheaves of modules round the square is compatible with composition** —
  the middle factor of `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which is
  where the content of that comparison's composition law sits.
* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_factoredComp`: the sites level
  composition law with the two base changes of schemes spelled through the abbreviations of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedQuasicoherent.lean`.

## Implementation notes

Every statement is at a composite presented by a separate morphism `hgc` together with a
factorisation `h ≫ g = hgc`, which is the form in which the sites level law
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_eq_factoredComp` arrives and the form a
consumer holding a composite of the site under another name can use.  The chart side is written
at `AlgebraicGeometry.Space.representedSpaceMap` throughout and the two spellings of the
composite are reconciled once, by `AlgebraicGeometry.Space.representedSpaceMap_comp_eq`, in the
arguments of the factorised comparisons.

The four compatibilities are instances of the two whiskering compatibilities of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/PushforwardComparisonWhiskering.lean`,
applied to the two base compatibilities — the structure-map composition law of base change of
schemes, `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp`, and
that of base change of charts,
`AlgebraicGeometry.Space.smallBaseChangeSharp_factoredCompInv` — and to
`AlgebraicGeometry.Space.representedStructureMapRing_square` itself at the two factors.  The two
readings of the structure map of a composite of three morphisms of ringed sites are equal by
`rfl` (`Stacks.SheafOfModules.comparisonComp_assoc`), which is what lets the compatibility
produced by one of the two whiskering lemmas be the hypothesis of the other.

The composite functors of sites occurring here need their continuity in whichever bracketing the
comparison of the two routes presents them, and the two bracketings of one composite are
definitionally equal but not equal at the transparency instance resolution uses.  Both are
therefore recorded, as theorems made local instances, and assembled by passing the component
instances positionally to `CategoryTheory.Functor.isContinuous_comp` — for the reason given in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`.

## What the composition law for the comparison of the two direct images still owes

`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` is a four-fold composite.  Its
second factor's composition law is
`AlgebraicGeometry.Space.representedStructureMapRing_squareTransport_comp` here; its fourth
factor's is `AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`; and the
two-categorical assembly of the two into a law for the whole composite is
`Stacks.CategoryTheory.squareIsoCompOfChart`, whose `hstep` hypothesis is the law for the first
three factors together.

What is left is exactly the bookkeeping of the first and third factors, which are the two
`CategoryTheory.SheafOfModules.pushforwardComp`.  Writing `a` and `c` for them and
`A ≪≫ B ≪≫ C ≪≫ D` for the four transports above, `hstep` asks for
`a ≪≫ (A ≪≫ B ≪≫ C ≪≫ D) ≪≫ c` to be rearranged as the four whiskerings
`Ψ`, `Φ'_g`, `Φ'_h`, `Θ'` of the statement, each of which is itself a `pushforwardComp`
sandwich.  Telescoping it needs, at plain variables: the two whiskering identities of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/PushforwardComparisonWhiskering.lean`
conjugated by the `pushforwardComp` on either side; the interchangeability of the two readings
`pushforwardComp θ (comparisonComp α β)` and `pushforwardComp (comparisonComp θ α) β` of a
threefold composite's comparison; and Mathlib's `SheafOfModules.pushforward_assoc`, which is
what cancels the three residual pairs of whiskered `pushforwardComp`s.

That it has to be done at plain variables, and in particular that no `pushforwardComp` may be
cancelled against `CategoryTheory.Iso.refl` at a geometric instantiation, is the measurement
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartFactoredComposition.lean`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T'' T' T : BigFppfOver B S hS}

/-! ### Continuity of the composite functors of sites -/

/-- Composition of continuous functors, with the two continuity instances passed positionally. -/
private theorem isContinuous_comp_of {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E} (hF : F.IsContinuous J K) (hG : G.IsContinuous K L) :
    (F ⋙ G).IsContinuous J L :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _ hF hG

/-- Base change of étale scheme charts along `g` and then along `h` is continuous. -/
theorem isContinuous_smallBaseChange_comp_smallBaseChange (h : T'' ⟶ T') (g : T' ⟶ T)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g)) :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS h) hh).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T'')) :=
  isContinuous_comp_of
    (isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
    (isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS h) hh)

attribute [local instance] isContinuous_smallBaseChange_comp_smallBaseChange

/-- Base change of charts twice, then the identification of the small étale site of
`yoneda.obj T''` with that of the scheme underlying `T''`, is continuous. -/
theorem isContinuous_smallBaseChangeComp_comp_representedEquiv (h : T'' ⟶ T') (g : T' ⟶ T)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g)) :
    ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
          smallBaseChange B S hS (representedSpaceMap B S hS h) hh) ⋙
        (representedSmallEtaleEquivalence B S hS T'').functor).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_smallBaseChange_comp_smallBaseChange B S hS h g hh hg)
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS T'')

/-- The same composite with the other bracketing: base change of charts along `g`, then base
change along `h` followed by the identification of the two sites of `T''`. -/
theorem isContinuous_smallBaseChange_comp_smallBaseChangeRepresentedEquiv (h : T'' ⟶ T')
    (g : T' ⟶ T) (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g)) :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        (smallBaseChange B S hS (representedSpaceMap B S hS h) hh ⋙
          (representedSmallEtaleEquivalence B S hS T'').functor)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
    (isContinuous_smallBaseChange_comp_representedEquiv B S hS h hh)

/-- Base change of charts along `g`, then the identification of the two sites of `T'`, then base
change of schemes along `h`, is continuous. -/
theorem isContinuous_smallBaseChange_comp_representedEquivSchemeBaseChange (h : T'' ⟶ T')
    (g : T' ⟶ T) (hg : yoneda.relativelyRepresentable (yoneda.map g)) :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        ((representedSmallEtaleEquivalence B S hS T').functor ⋙
          representedSchemeBaseChange B S hS h)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
    (isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS h)

/-- The same composite with the other bracketing. -/
theorem isContinuous_smallBaseChangeRepresentedEquiv_comp_schemeBaseChange (h : T'' ⟶ T')
    (g : T' ⟶ T) (hg : yoneda.relativelyRepresentable (yoneda.map g)) :
    ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
          (representedSmallEtaleEquivalence B S hS T').functor) ⋙
        representedSchemeBaseChange B S hS h).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_smallBaseChange_comp_representedEquiv B S hS g hg)
    (isContinuous_representedSchemeBaseChange B S hS h)

/-- The identification of the two sites of `T`, then base change of schemes along `g`, then base
change of schemes along `h`, is continuous. -/
theorem isContinuous_representedEquivSchemeBaseChange_comp_schemeBaseChange (h : T'' ⟶ T')
    (g : T' ⟶ T) :
    (((representedSmallEtaleEquivalence B S hS T).functor ⋙
          representedSchemeBaseChange B S hS g) ⋙
        representedSchemeBaseChange B S hS h).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS g)
    (isContinuous_representedSchemeBaseChange B S hS h)

/-- The same composite with the other bracketing.  The inner composite is spelled as
`AlgebraicGeometry.smallEtaleBaseChange` rather than through the abbreviation
`AlgebraicGeometry.Space.representedSchemeBaseChange`, because that is the spelling in which the
structure-map composition law of base change of schemes presents it, and the two spellings of
the scheme underlying an object of the big fppf category are not equal at the transparency
instance resolution uses. -/
theorem isContinuous_representedEquiv_comp_schemeBaseChangeComp (h : T'' ⟶ T') (g : T' ⟶ T) :
    ((representedSmallEtaleEquivalence B S hS T).functor ⋙
        (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left ⋙
          _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
            h.left)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (_root_.AlgebraicGeometry.SmallEtale.isContinuous_smallEtaleBaseChange_comp
      (associatedBigEtaleSite B) h.left g.left)

/-- The identification of the two sites of `T` followed by base change of schemes along `g` and
then along `h`, with the two base changes spelled through the abbreviation. -/
theorem isContinuous_representedEquiv_comp_representedSchemeBaseChangeComp (h : T'' ⟶ T')
    (g : T' ⟶ T) :
    ((representedSmallEtaleEquivalence B S hS T).functor ⋙
        (representedSchemeBaseChange B S hS g ⋙
          representedSchemeBaseChange B S hS h)).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (isContinuous_representedSchemeBaseChange_comp B S hS h g)

/-- `AlgebraicGeometry.Space.isContinuous_representedEquivSchemeBaseChange_comp_schemeBaseChange`
with the outer base change of schemes spelled as `AlgebraicGeometry.smallEtaleBaseChange`, which
is the spelling in which the sites level composition law presents it. -/
theorem isContinuous_representedEquivSchemeBaseChangeComp_comp_smallEtaleBaseChange
    (h : T'' ⟶ T') (g : T' ⟶ T) :
    (((representedSmallEtaleEquivalence B S hS T).functor ⋙
          _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left) ⋙
        _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
          h.left).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  isContinuous_comp_of
    (isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS g)
    (isContinuous_representedSchemeBaseChange B S hS h)

attribute [local instance]
  isContinuous_representedEquivSchemeBaseChangeComp_comp_smallEtaleBaseChange

attribute [local instance] isContinuous_representedEquiv_comp_representedSchemeBaseChangeComp

attribute [local instance] isContinuous_smallBaseChangeComp_comp_representedEquiv
  isContinuous_smallBaseChange_comp_smallBaseChangeRepresentedEquiv
  isContinuous_smallBaseChange_comp_representedEquivSchemeBaseChange
  isContinuous_smallBaseChangeRepresentedEquiv_comp_schemeBaseChange
  isContinuous_representedEquivSchemeBaseChange_comp_schemeBaseChange
  isContinuous_representedEquiv_comp_schemeBaseChangeComp

/-! ### The composition comparison of base change of schemes, respelled -/

/-- The composition comparison `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` of base
change of schemes, with the three small étale sites of schemes spelled as the identification of
the small étale site of a representable algebraic space spells them.

The two spellings of the scheme underlying an object of the big fppf category over `S` are
definitionally equal, but not equal at the transparency instance resolution uses; ascribing the
comparison to the spelling used throughout this file, once, keeps every statement below in one
spelling.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`. -/
noncomputable abbrev representedSchemeBaseChange_factoredCompIso (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc) :
    representedSchemeBaseChange B S hS g ⋙ representedSchemeBaseChange B S hS h ≅
      representedSchemeBaseChange B S hS hgc :=
  _root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso (associatedBigEtaleSite B)
    T''.left T'.left T.left h.left g.left hgc.left (congrArg (fun m : T'' ⟶ T => m.left) w)

/-! ### The composition compatibility of the square -/

section Comp

variable (h : T'' ⟶ T') (g : T' ⟶ T) (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hc : yoneda.relativelyRepresentable (yoneda.map hgc))

/-- **The structure maps of base change of schemes compose, inside the square.**  This is the
compatibility that the last factor of the sites level composition law — the composition
comparison of base change of schemes, whiskered with the identification of the two sites of
`T` — asks of the transport of a direct image of sheaves of modules. -/
theorem representedStructureMapRing_square_schemeComp :
    SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
          (representedSchemeStructureMapRing B S hS hgc) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Functor.whiskerLeft (representedSmallEtaleEquivalence B S hS T).functor
            (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w).hom) RingCat.{u}
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSchemeSmallEtaleTopology B S hS T'')).app
          (representedSchemeStructureSheaf B S hS T'') =
      SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
        (SheafOfModules.comparisonComp (representedSchemeStructureMapRing B S hS g)
          (representedSchemeStructureMapRing B S hS h)) :=
  Stacks.SheafOfModules.comparisonComp_natTrans_whiskerLeft _ _
    (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp
      (associatedBigEtaleSite B) h.left g.left hgc.left
      (congrArg (fun m : T'' ⟶ T => m.left) w))

/-- **The square for `g`, whiskered with base change of schemes along `h`.**  This is the
compatibility that the third factor of the sites level composition law asks of the transport of
a direct image of sheaves of modules. -/
theorem representedStructureMapRing_square_whiskerRight :
    SheafOfModules.comparisonComp
          (SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS g))
          (representedSchemeStructureMapRing B S hS h) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Functor.whiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg).hom
            (representedSchemeBaseChange B S hS h)) RingCat.{u}
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSchemeSmallEtaleTopology B S hS T'')).app
          (representedSchemeStructureSheaf B S hS T'') =
      SheafOfModules.comparisonComp
        (SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
          (representedEquivSharp B S hS T'))
        (representedSchemeStructureMapRing B S hS h) :=
  Stacks.SheafOfModules.comparisonComp_natTrans_whiskerRight _ _
    (representedStructureMapRing_square B S hS g hg)

/-- **The square for `h`, whiskered with base change of charts along `g`.**  This is the
compatibility that the second factor of the sites level composition law asks of the transport of
a direct image of sheaves of modules. -/
theorem representedStructureMapRing_square_whiskerLeft :
    SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
          (SheafOfModules.comparisonComp (representedEquivSharp B S hS T')
            (representedSchemeStructureMapRing B S hS h)) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Functor.whiskerLeft (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
            (representedSmallEtaleBaseChangeIso B S hS h hh).hom) RingCat.{u}
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSchemeSmallEtaleTopology B S hS T'')).app
          (representedSchemeStructureSheaf B S hS T'') =
      SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
        (SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS h) hh)
          (representedEquivSharp B S hS T'')) :=
  Stacks.SheafOfModules.comparisonComp_natTrans_whiskerLeft _ _
    (representedStructureMapRing_square B S hS h hh)

/-- **The structure maps of base change of charts compose, inside the square.**  This is the
compatibility that the first factor of the sites level composition law — the composition
comparison of chart base change, whiskered with the identification of the two sites of `T''` —
asks of the transport of a direct image of sheaves of modules. -/
theorem representedStructureMapRing_square_chartComp :
    SheafOfModules.comparisonComp
          (SheafOfModules.comparisonComp
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS h) hh))
          (representedEquivSharp B S hS T'') ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (Functor.whiskerRight
            (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
              (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
              (representedSpaceMap_comp_eq B S hS h g hgc w)).inv
            (representedSmallEtaleEquivalence B S hS T'').functor) RingCat.{u}
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSchemeSmallEtaleTopology B S hS T'')).app
          (representedSchemeStructureSheaf B S hS T'') =
      SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS hgc) hc)
        (representedEquivSharp B S hS T'') :=
  Stacks.SheafOfModules.comparisonComp_natTrans_whiskerRight _ _
    (smallBaseChangeSharp_factoredCompInv B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))

/-- `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_eq_factoredComp` with the two base
changes of schemes spelled through the abbreviations
`AlgebraicGeometry.Space.representedSchemeBaseChange` and
`AlgebraicGeometry.Space.representedSchemeBaseChange_factoredCompIso`.

The same statement, the abbreviations being reducible; it is restated so that the implicit
arguments of the whiskerings are the ones for which this file records the continuity of the
composite functors of sites.  See the implementation notes. -/
theorem representedSmallEtaleBaseChangeIso_factoredComp :
    representedSmallEtaleBaseChangeIso B S hS hgc hc =
      (Functor.isoWhiskerRight
          (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
            (representedSpaceMap_comp_eq B S hS h g hgc w))
          (representedSmallEtaleEquivalence B S hS T'').functor).symm ≪≫
        Functor.isoWhiskerLeft (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
            (representedSmallEtaleBaseChangeIso B S hS h hh) ≪≫
          Functor.isoWhiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg)
              (representedSchemeBaseChange B S hS h) ≪≫
            Functor.isoWhiskerLeft (representedSmallEtaleEquivalence B S hS T).functor
              (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w) :=
  representedSmallEtaleBaseChangeIso_eq_factoredComp B S hS h g hgc w hh hg hc

/-! ### The transport of the direct image, composed -/

/-- **The transport of the direct image of sheaves of modules round the square of small étale
ringed sites is compatible with composition.**  The transport along the comparison of the two
routes for `hgc` is the composite of the four transports along the four factors into which the
sites level law `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_eq_factoredComp`
decomposes that comparison, each with the structure-map compatibility of its own factor.

This is `Stacks.SheafOfModules.pushforwardCongr₂_comp_four` instantiated at those four factors;
the four compatibilities are the ones above.  It is the middle factor of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which is where the content of
that comparison's composition law sits: its other three factors are
`CategoryTheory.SheafOfModules.pushforwardComp`, whose coherence is Mathlib's
`SheafOfModules.pushforward_assoc`, and the chart identification, whose composition law is
`AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`. -/
theorem representedStructureMapRing_squareTransport_comp :
    SheafOfModules.pushforwardCongr₂.{u} _
        (representedSmallEtaleBaseChangeIso B S hS hgc hc)
        (representedStructureMapRing_square B S hS hgc hc) =
      SheafOfModules.pushforwardCongr₂.{u} _
          (Functor.isoWhiskerLeft (representedSmallEtaleEquivalence B S hS T).functor
            (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w))
          (representedStructureMapRing_square_schemeComp B S hS h g hgc w) ≪≫
        SheafOfModules.pushforwardCongr₂.{u} _
            (Functor.isoWhiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg)
              (representedSchemeBaseChange B S hS h))
            (representedStructureMapRing_square_whiskerRight B S hS h g hg) ≪≫
          SheafOfModules.pushforwardCongr₂.{u} _
              (Functor.isoWhiskerLeft
                (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
                (representedSmallEtaleBaseChangeIso B S hS h hh))
              (representedStructureMapRing_square_whiskerLeft B S hS h g hh hg) ≪≫
            SheafOfModules.pushforwardCongr₂.{u} _
              (Functor.isoWhiskerRight
                (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
                  (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
                  (representedSpaceMap_comp_eq B S hS h g hgc w))
                (representedSmallEtaleEquivalence B S hS T'').functor).symm
              (representedStructureMapRing_square_chartComp B S hS h g hgc w hh hg hc) :=
  Stacks.SheafOfModules.pushforwardCongr₂_comp_four.{u} _ _ _ _ _
    (representedSmallEtaleBaseChangeIso_factoredComp B S hS h g hgc w hh hg hc).symm
    (representedStructureMapRing_square_schemeComp B S hS h g hgc w)
    (representedStructureMapRing_square_whiskerRight B S hS h g hg)
    (representedStructureMapRing_square_whiskerLeft B S hS h g hh hg)
    (representedStructureMapRing_square_chartComp B S hS h g hgc w hh hg hc)
    (representedStructureMapRing_square B S hS hgc hc)

end Comp

end AlgebraicGeometry.Space

end
