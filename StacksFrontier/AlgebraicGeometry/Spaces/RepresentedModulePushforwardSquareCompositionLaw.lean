module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PushforwardSquareComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardSquareComposition
public import StacksFrontier.CategoryTheory.SquareIsoChartComposition

/-!
# The comparison of the two direct images round the square of a representable morphism composes

For a morphism `g : T' ⟶ T` of the big fppf category over `S`,
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` compares the two direct images
of sheaves of modules round the square of small étale ringed sites of the represented morphism
of algebraic spaces: taking the direct image along base change of schemes and reading the result
on the small étale site of `yoneda.obj T`, against reading a module on the small étale site of
`yoneda.obj T'` and taking the direct image of Stacks 03LU.  This file proves that those
comparisons are compatible with composition.

## Main definitions

* `AlgebraicGeometry.Space.representedSchemeModulePushforwardFactoredCompIso`: the composition
  comparison of the direct images of modules along base change of schemes, at a composite
  presented by a separate morphism together with a factorisation.
* `AlgebraicGeometry.Space.representedSquareThreeFactorIso` and
  `AlgebraicGeometry.Space.representedSquareThreeFactorIso'`: the first three factors of
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, that is the comparison of the
  two direct images with the chart-base-change direct image *not* yet read as the direct image
  of Stacks 03LU, in its two spellings.

## Main results

* `AlgebraicGeometry.Space.representedSquareThreeFactorIso_comp`: **the comparison of the two
  direct images, before the chart identification, is compatible with composition.**
* `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_factoredComp`: **the comparison of
  the two direct images of sheaves of modules round the square of small étale ringed sites of a
  representable morphism is compatible with composition.**

## Implementation notes

The two comparisons are assembled by the two generic engines and nothing is restated at the
geometric instantiation: `Stacks.SheafOfModules.pushforwardSquareIso_step_of_data` supplies the
law for the first three factors from the transport law
`AlgebraicGeometry.Space.representedStructureMapRing_squareTransport_comp` together with the four
comparisons of the index functors and their eight structure-map compatibilities, and
`Stacks.CategoryTheory.squareIsoCompOfChart` reads that law through the chart identification
using `AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`.

Each statement is at a composite presented by a separate morphism `hgc` together with a
factorisation `h ≫ g = hgc`, the form in which the inputs arrive and the form a consumer
holding a composite of the site under another name can use; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardSquareComposition.lean`.  The
section there headed *What the composition law for the comparison of the two direct images still
owes* is discharged by this file.

Three things keep the two composition laws inside the heartbeat budget of one declaration;
without them the step law verifies only at 4,000,000 heartbeats.

* **The twenty-three continuity instances of the generic step law are passed by name.**  Left to
  instance resolution they are sought at the spellings the composite square presents — the
  algebraic space as the anonymous constructor `⟨yoneda.obj U, _⟩` that
  `AlgebraicGeometry.Space.representedSpaceMap` has for its source, and the small étale site of
  the underlying scheme through `CategoryTheory.Over.left` rather than through
  `AlgebraicGeometry.BigFppfOver.toScheme` — and the existing instances, stated at the other
  spelling of each, are not found, because the two spellings are definitionally equal but not
  equal at the transparency instance resolution uses.  Supplied by name, no search runs and each
  is checked against the required type by that definitional equality instead.
* **Both spellings of the three-factor comparison are named.**  The step law is stated with the
  identification of the small étale sites spelled as
  `CategoryTheory.SheafOfModules.pushforward` of `AlgebraicGeometry.Space.representedEquivSharp`,
  which is how the step law's `CategoryTheory.SheafOfModules.pushforwardComp` factors present it;
  the chart reading is stated with it spelled as the functor of
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, which is how
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` presents it.  Deciding that the
  two agree unfolds `CategoryTheory.SheafOfModules.pushforward` some ten thousand times at these
  sites; naming both pays it once, in
  `AlgebraicGeometry.Space.representedSquareThreeFactorIso'`, rather than inside each assembly.
* **`attribute [local irreducible]`**, per section.  The step law needs
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and
  `AlgebraicGeometry.Space.smallBaseChange` opaque — the unifier otherwise normalises objects of
  the small étale site, through `CategoryTheory.Over.iteratedSliceEquiv` and the
  `Classical.choose` inside `CategoryTheory.Functor.relativelyRepresentable.pullback`.  The chart
  reading needs those, the three structure sheaves, and the direct image of Stacks 03LU with its
  comparisons: it uses all of them only symbolically.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange
  isContinuous_smallBaseChange_comp
  isContinuous_smallBaseChange_comp_smallBaseChange
  isContinuous_smallBaseChangeComp_comp_representedEquiv
  isContinuous_smallBaseChange_comp_smallBaseChangeRepresentedEquiv
  isContinuous_smallBaseChange_comp_representedEquivSchemeBaseChange
  isContinuous_smallBaseChangeRepresentedEquiv_comp_schemeBaseChange
  isContinuous_representedEquivSchemeBaseChange_comp_schemeBaseChange
  isContinuous_representedEquiv_comp_schemeBaseChangeComp
  isContinuous_representedSchemeBaseChange_comp
  isContinuous_representedEquiv_comp_representedSchemeBaseChangeComp
  isContinuous_representedEquivSchemeBaseChangeComp_comp_smallEtaleBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T'' T' T : BigFppfOver B S hS}

/-! ### The direct images along base change of schemes, composed -/

/-- **The direct images of modules along base change of schemes compose**, at a composite
presented by a separate morphism together with a factorisation, and in the direction a comparison
of the two routes round the square consumes it.

This is the `Ψ` of `Stacks.CategoryTheory.squareIsoCompOfChart` for the square of small étale
ringed sites of a representable morphism. -/
noncomputable def representedSchemeModulePushforwardFactoredCompIso (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc) :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS hgc) ≅
      SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h) ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) :=
  SheafOfModules.pushforwardCongr₂.{u} _
      (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w)
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp
        (associatedBigEtaleSite B) h.left g.left hgc.left
        (congrArg (fun m : T'' ⟶ T => m.left) w)) ≪≫
    (SheafOfModules.pushforwardComp.{u} (representedSchemeStructureMapRing B S hS g)
      (representedSchemeStructureMapRing B S hS h)).symm

/-- `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardFactoredCompIso` read as the
composite it is defined to be.  Supplied as its own declaration so that a consumer passing it to
a generic lemma matches the composite syntactically, rather than unfolding the definition inside
a larger elaboration. -/
theorem smallBaseChangeModulePushforwardFactoredCompIso_eq {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg) :
    smallBaseChangeModulePushforwardFactoredCompIso B S hS f g fg hf hg hfg w =
      SheafOfModules.pushforwardComp.{u} (smallBaseChangeSharp B S hS g hg)
          (smallBaseChangeSharp B S hS f hf) ≪≫
        SheafOfModules.pushforwardCongr₂.{u}
          (SheafOfModules.comparisonComp (smallBaseChangeSharp B S hS g hg)
            (smallBaseChangeSharp B S hS f hf))
          (smallBaseChange_factoredComp B S hS f g fg hf hg hfg w).symm
          (smallBaseChangeSharp_factoredCompInv B S hS f g fg hf hg hfg w) :=
  rfl

/-- `AlgebraicGeometry.Space.representedSchemeModulePushforwardFactoredCompIso` read as the
composite it is defined to be. -/
theorem representedSchemeModulePushforwardFactoredCompIso_eq (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc) :
    representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w =
      SheafOfModules.pushforwardCongr₂.{u} (representedSchemeStructureMapRing B S hS hgc)
          (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w)
          (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp
            (associatedBigEtaleSite B) h.left g.left hgc.left
            (congrArg (fun m : T'' ⟶ T => m.left) w)) ≪≫
        (SheafOfModules.pushforwardComp.{u} (representedSchemeStructureMapRing B S hS g)
          (representedSchemeStructureMapRing B S hS h)).symm :=
  rfl

/-! ### The comparison before the chart identification -/

section Three

variable (g : T' ⟶ T) (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The two routes round the square of small étale ringed sites have the same direct image of
modules**, with the chart-base-change direct image left as it is rather than read as the direct
image of Stacks 03LU.

These are the first three factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which is this comparison
followed by `AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
noncomputable def representedSquareThreeFactorIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T) ≅
      SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T') ⋙
        SheafOfModules.pushforward.{u}
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) :=
  SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS g hg)
      (representedStructureMapRing_square B S hS g hg) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')).symm

/-- `AlgebraicGeometry.Space.representedSquareThreeFactorIso` read as the composite it is
defined to be. -/
theorem representedSquareThreeFactorIso_eq :
    representedSquareThreeFactorIso B S hS g hg =
      SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
          (representedSchemeStructureMapRing B S hS g) ≪≫
        SheafOfModules.pushforwardCongr₂.{u}
            (SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
              (representedSchemeStructureMapRing B S hS g))
            (representedSmallEtaleBaseChangeIso B S hS g hg)
            (representedStructureMapRing_square B S hS g hg) ≪≫
          (SheafOfModules.pushforwardComp.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
            (representedEquivSharp B S hS T')).symm :=
  rfl

/-- `AlgebraicGeometry.Space.representedSquareThreeFactorIso` with the identifications of the
small étale sites spelled as the functors of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and the chart-base-change direct
image through `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.

The same isomorphism, each pair of spellings being definitionally equal; both are named because
deciding that definitional equality is affordable once and not repeatedly — see the
implementation notes. -/
noncomputable def representedSquareThreeFactorIso' :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS g) hg :=
  representedSquareThreeFactorIso B S hS g hg

/-- `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` is the comparison before the
chart identification, followed by that identification. -/
theorem representedModulePushforwardSquareIso_eq_threeFactor :
    representedModulePushforwardSquareIso B S hS g hg =
      representedSquareThreeFactorIso' B S hS g hg ≪≫
        Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
          (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).symm :=
  Stacks.CategoryTheory.trans_four_assoc _ _ _ _

end Three

/-! ### The composition law before the chart identification -/

section Comp

attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange

variable (h : T'' ⟶ T') (g : T' ⟶ T) (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hc : yoneda.relativelyRepresentable (yoneda.map hgc))

/-- **The comparison of the two direct images of sheaves of modules round the square of small
étale ringed sites, before the chart identification, is compatible with composition.**

This is `Stacks.SheafOfModules.pushforwardSquareIso_step_of_data` at the square of a
representable morphism.  Its transport hypothesis is
`AlgebraicGeometry.Space.representedStructureMapRing_squareTransport_comp`, its four comparisons
of index functors are the two sites' composition comparisons and the comparisons of the two
routes for `g` and for `h`, and its eight structure-map compatibilities are the existing squares;
so nothing is restated here.

**The six structure sheaves of the step law are passed by name**, and each side of the square is
passed in one spelling: the two routes meet at the structure sheaves of the small étale sites of
the representable algebraic spaces, which this development writes both as
`AlgebraicGeometry.Space.representedStructureRingSheaf`, through
`Stacks.SheafOfModules.Tensor.ringSheaf`, and as
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, through `CategoryTheory.sheafCompose` of the
forgetful functor — the same sheaf of rings, `AlgebraicGeometry.Space.ringedSite_ringSheaf_eq`,
but equal only once the first of those is unfolded, and it is a plain `def`.  Left to inference
the step law's `RD₀`, `RD₁`, `RD₂` are fixed at one spelling by
`AlgebraicGeometry.Space.representedEquivSharp` and demanded at the other by
`AlgebraicGeometry.Space.smallBaseChangeSharp`, and the comparison is then re-decided inside
every `CategoryTheory.SheafOfModules.pushforward` of the assembly, which exhausts the heartbeat
budget.  Named, it is decided once, on the sheaves of rings themselves. -/
theorem representedSquareThreeFactorIso_comp :
    representedSquareThreeFactorIso B S hS hgc hc =
      Functor.isoWhiskerRight
          (representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w)
          (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)) ≪≫
        Functor.isoWhiskerLeft
            (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h))
            (representedSquareThreeFactorIso B S hS g hg) ≪≫
          Functor.isoWhiskerRight (representedSquareThreeFactorIso B S hS h hh)
              (SheafOfModules.pushforward.{u}
                (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)) ≪≫
            Functor.isoWhiskerLeft
              (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T''))
              (smallBaseChangeModulePushforwardFactoredCompIso B S hS
                (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
                (representedSpaceMap B S hS hgc) hh hg hc
                (representedSpaceMap_comp_eq B S hS h g hgc w)) :=
  Stacks.SheafOfModules.pushforwardSquareIso_step_of_data.{u}
    (RC₀ := representedSchemeStructureSheaf B S hS T'')
    (RC₁ := representedSchemeStructureSheaf B S hS T')
    (RC₂ := representedSchemeStructureSheaf B S hS T)
    (RD₀ := smallEtaleRingSheaf B S hS (yoneda.obj T'')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T''))
    (RD₁ := smallEtaleRingSheaf B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'))
    (RD₂ := smallEtaleRingSheaf B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
    (ie₀ := isContinuous_representedSmallEtaleEquivalence_functor B S hS T'')
    (ie₁ := isContinuous_representedSmallEtaleEquivalence_functor B S hS T')
    (ie₂ := isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (ib := isContinuous_representedSchemeBaseChange B S hS hgc)
    (ib₁ := isContinuous_representedSchemeBaseChange B S hS h)
    (ib₂ := isContinuous_representedSchemeBaseChange B S hS g)
    (ik := isContinuous_representedSmallBaseChange B S hS hgc hc)
    (ik₁ := isContinuous_representedSmallBaseChange B S hS h hh)
    (ik₂ := isContinuous_representedSmallBaseChange B S hS g hg)
    (ieb := isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS hgc)
    (ike := isContinuous_smallBaseChange_comp_representedEquiv B S hS hgc hc)
    (ibb := isContinuous_representedSchemeBaseChange_comp B S hS h g)
    (iebb := isContinuous_representedEquiv_comp_representedSchemeBaseChangeComp B S hS h g)
    (ieb₂ := isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS g)
    (iebb' := isContinuous_representedEquivSchemeBaseChange_comp_schemeBaseChange B S hS h g)
    (ike₁ := isContinuous_smallBaseChange_comp_representedEquiv B S hS g hg)
    (ikeb := isContinuous_smallBaseChangeRepresentedEquiv_comp_schemeBaseChange B S hS h g hg)
    (ieb₁ := isContinuous_representedEquiv_comp_smallEtaleBaseChange B S hS h)
    (ikeb' := isContinuous_smallBaseChange_comp_representedEquivSchemeBaseChange B S hS h g hg)
    (ike₀ := isContinuous_smallBaseChange_comp_representedEquiv B S hS h hh)
    (ikke := isContinuous_smallBaseChange_comp_smallBaseChangeRepresentedEquiv B S hS h g hh hg)
    (ikk := isContinuous_smallBaseChange_comp_smallBaseChange B S hS h g hh hg)
    (ikke' := isContinuous_smallBaseChangeComp_comp_representedEquiv B S hS h g hh hg)
    (representedSchemeBaseChange_factoredCompIso B S hS h g hgc w)
    (representedSmallEtaleBaseChangeIso B S hS g hg)
    (representedSmallEtaleBaseChangeIso B S hS h hh)
    (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))
    (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_factoredComparisonComp
      (associatedBigEtaleSite B) h.left g.left hgc.left
      (congrArg (fun m : T'' ⟶ T => m.left) w))
    (representedStructureMapRing_square B S hS g hg)
    (representedStructureMapRing_square B S hS h hh)
    (smallBaseChangeSharp_factoredCompInv B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))
    (representedStructureMapRing_square_schemeComp B S hS h g hgc w)
    (representedStructureMapRing_square_whiskerRight B S hS h g hg)
    (representedStructureMapRing_square_whiskerLeft B S hS h g hh hg)
    (representedStructureMapRing_square_chartComp B S hS h g hgc w hh hg hc)
    (Φc := representedSquareThreeFactorIso B S hS hgc hc)
    (Φg := representedSquareThreeFactorIso B S hS g hg)
    (Φh := representedSquareThreeFactorIso B S hS h hh)
    (Ψ := representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w)
    (Θ := smallBaseChangeModulePushforwardFactoredCompIso B S hS
      (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
      (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))
    (representedSquareThreeFactorIso_eq B S hS hgc hc)
    (representedSquareThreeFactorIso_eq B S hS g hg)
    (representedSquareThreeFactorIso_eq B S hS h hh)
    (representedSchemeModulePushforwardFactoredCompIso_eq B S hS h g hgc w)
    (smallBaseChangeModulePushforwardFactoredCompIso_eq B S hS
      (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
      (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))
    (representedStructureMapRing_squareTransport_comp B S hS h g hgc w hh hg hc)

end Comp

/-! ### The composition law -/

section Law

variable (h : T'' ⟶ T') (g : T' ⟶ T) (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hc : yoneda.relativelyRepresentable (yoneda.map hgc))

/-- `AlgebraicGeometry.Space.representedSquareThreeFactorIso_comp` with the three identifications
of the small étale sites spelled as the functors of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and the chart-base-change direct
image through `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which is how
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` spells them.

The same statement, the two spellings of each functor being definitionally equal; it is restated
so that the composition law below supplies it with no conversion of its own. -/
theorem representedSquareThreeFactorIso_comp_moduleEquivalence :
    representedSquareThreeFactorIso' B S hS hgc hc =
      Functor.isoWhiskerRight
          (representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w)
          ((representedSmallEtaleModuleEquivalence B S hS T).functor) ≪≫
        Functor.isoWhiskerLeft
            (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h))
            (representedSquareThreeFactorIso' B S hS g hg) ≪≫
          Functor.isoWhiskerRight (representedSquareThreeFactorIso' B S hS h hh)
              (smallBaseChangeModulePushforward.{u, u} B S hS
                (representedSpaceMap B S hS g) hg) ≪≫
            Functor.isoWhiskerLeft
              ((representedSmallEtaleModuleEquivalence B S hS T'').functor)
              (smallBaseChangeModulePushforwardFactoredCompIso B S hS
                (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
                (representedSpaceMap B S hS hgc) hh hg hc
                (representedSpaceMap_comp_eq B S hS h g hgc w)) :=
  representedSquareThreeFactorIso_comp B S hS h g hgc w hh hg hc

section Chart

attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange structureSheaf
  structureSheaf' structurePresheaf modulePushforward modulePushforwardCompIso
  modulePushforwardFactoredCompIso modulePushforwardChartIso
  representedModulePushforwardSquareIso representedSquareThreeFactorIso'
  representedSchemeModulePushforwardFactoredCompIso

/-- **The comparison of the two direct images of sheaves of modules round the square of small
étale ringed sites of a representable morphism is compatible with composition.**

Whiskering the comparison for `g` with the direct image along base change of schemes for `h`,
then the comparison for `h` with the direct image of Stacks 03LU along `g`, then the composition
comparison of the direct images of Stacks 03LU, is the composition comparison of the direct
images along base change of schemes followed by the comparison for the composite `hgc`.

The proof reads the composition law before the chart identification,
`AlgebraicGeometry.Space.representedSquareThreeFactorIso_comp`, through that identification; the
two-categorical bookkeeping is `Stacks.CategoryTheory.squareIsoCompOfChart` and the
compatibility of the chart identification with composition is
`AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`. -/
theorem representedModulePushforwardSquareIso_factoredComp :
    Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h))
          (representedModulePushforwardSquareIso B S hS g hg) ≪≫
        Functor.isoWhiskerRight (representedModulePushforwardSquareIso B S hS h hh)
            (modulePushforward B S hS (representedSpaceMap B S hS g)) ≪≫
          Functor.isoWhiskerLeft
            ((representedSmallEtaleModuleEquivalence B S hS T'').functor)
            (modulePushforwardFactoredCompIso B S hS (representedSpaceMap B S hS h)
              (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc)
              (representedSpaceMap_comp_eq B S hS h g hgc w)) =
      Functor.isoWhiskerRight
          (representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w).symm
          ((representedSmallEtaleModuleEquivalence B S hS T).functor) ≪≫
        representedModulePushforwardSquareIso B S hS hgc hc :=
  Stacks.CategoryTheory.squareIsoCompOfChart
    (representedSchemeModulePushforwardFactoredCompIso B S hS h g hgc w)
    (representedModulePushforwardSquareIso_eq_threeFactor B S hS h hh)
    (representedModulePushforwardSquareIso_eq_threeFactor B S hS g hg)
    (representedModulePushforwardSquareIso_eq_threeFactor B S hS hgc hc)
    (representedSquareThreeFactorIso_comp_moduleEquivalence B S hS h g hgc w hh hg hc)
    (modulePushforwardChartIso_symm_factoredComp B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
      (representedSpaceMap_comp_eq B S hS h g hgc w))

end Chart

end Law

end AlgebraicGeometry.Space

end
