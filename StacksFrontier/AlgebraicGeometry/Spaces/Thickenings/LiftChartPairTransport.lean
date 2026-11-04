module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLinearMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafSiteTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PreimageBaseChangeChart

/-!
# The acting sheaf of a chart-restricted lifting problem is the transported one at that chart

Let `Z ⊂ X'` be a thickening of algebraic spaces over a scheme `S` contained in a big fppf site
`C`, let `q : Y ⟶ Bb` be a morphism, let `a : Z ⟶ Y` be a morphism over `Bb` and let `U'` be an
étale scheme chart of `X'`.

`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairDifference` restricts the whole
lifting problem along `U'` and produces the difference of two lifts there as a **global** section
of the acting sheaf of the *restricted* problem — a sheaf of modules on the small étale site of
`Z.preimage (chartToSpace U').hom`.  A
`AlgebraicGeometry.Space.LiftDifferenceFamily`, however, takes its values in the sections of
`AlgebraicGeometry.Space.liftActionSheafTransport` over `U'` — a **local** section, at the chart
`U'`, of a sheaf on the small étale site of `X'`.

This file identifies the two.

## Main results

* `AlgebraicGeometry.Space.liftActionSheafChartSectionsEquiv`: **the global sections of the
  acting sheaf of the lifting problem restricted along `U'` are the sections of the transported
  acting sheaf over `U'`.**  Stated for an arbitrary morphism `a'` of the restricted problem
  together with the hypothesis that it is `a` precomposed with the projection of the restricted
  thickening, which is what a lift over `U'` satisfies.

## Implementation notes

**The five links of the chain, and where each comes from.**  Both sides are read as hom-sets of
modules and then compared term by term:

1. `AlgebraicGeometry.Space.smallEtaleInternalHomSectionsEquiv` reads the global sections of the
   restricted problem's acting sheaf as morphisms `a'^*Ω_{Y/Bb} ⟶ 𝒞_{Z_{U'}/U'}`;
2. `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv` ([Stacks Project, Tag
   0E8H] behind it) reads the sections of the original problem's acting sheaf at the
   base-changed chart as morphisms of the inverse images of `a^*Ω_{Y/Bb}` and `𝒞_{Z/X'}` to the
   chart space;
3. `AlgebraicGeometry.Space.preimageChartIso` identifies the two spaces those two hom-sets live
   over — the restricted thickening and the base-changed chart's space;
4. `AlgebraicGeometry.Space.isEquivalence_modulePullback_of_iso` turns that isomorphism of spaces
   into a bijection of hom-sets of modules, pullback along an isomorphism being fully faithful;
5. `AlgebraicGeometry.Space.modulePullbackCompIso` ([Stacks Project, Tag 03LU]) and
   `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` ([Stacks Project, Tag 04CO])
   identify the two source and the two target modules.

**The source module needs no étale hypothesis and the target one needs exactly the chart's.**
The differentials half is pure pseudofunctoriality of the inverse image: by hypothesis
`a' = p ≫ a` for `p` the projection of the restricted thickening, so `a'^*` is `p^*a^*` and
nothing geometric is used.  The conormal half is where étaleness enters, through
`AlgebraicGeometry.Space.isEtale_chartToSpace` — and the chart morphism of an object of the small
étale site is étale by definition, so this is not a hypothesis either.

**Everything is taken at OBJECT level.**  Each of the three module comparisons is applied at the
one module it is needed at, by `CategoryTheory.NatIso.app`, rather than composed as an
isomorphism of functors; `AlgebraicGeometry.Space.liftActionSheafTransport_obj` is `rfl`, so no
transport of the sheaf itself is performed at all.

**The equality `a' = p ≫ a` is a hypothesis rather than a construction** so that this file does
not have to mention a lift. For a lift over `U'` it is
`AlgebraicGeometry.Space.inclusion_comp_chartLiftHom` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartPairDifference`, read as an equation
of morphisms of algebraic spaces by `CategoryTheory.ObjectProperty.hom_ext`, which is how
`AlgebraicGeometry.Space.chartLiftDifferenceFamily` supplies it.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {Bb X' Y : AlgebraicSpaces C S hS} (Z : ClosedSubspaces C S hS X'.1)
  (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
  (aZ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
  (U' : SmallEtale C S hS X'.1)

/-! ### The projection of the restricted thickening through the base-changed chart -/

/-- **The projection of the restricted thickening factors through the base-changed chart.**  This
is `AlgebraicGeometry.Space.preimageChartIso_hom_chartToSpace` read as an equation of morphisms
of algebraic spaces rather than of presheaves. -/
theorem preimageProjection_eq_preimageChartIso_comp :
    preimageProjection C S hS (chartToSpace C S hS X' U') Z =
      (preimageChartIso C S hS Z.1 hG U').hom ≫
        chartToSpace C S hS (IsThickening.space C S hS hG)
          ((thickeningChartBaseChange C S hS hG).obj U') :=
  ObjectProperty.hom_ext _
    (preimageChartIso_hom_chartToSpace C S hS Z.1 hG U').symm

/-- **The inverse image along the projection of the restricted thickening is the two-step inverse
image through the base-changed chart**, for an *arbitrary* `𝒪_Z`-module. -/
def modulePullbackPreimageProjectionIso
    (A : Modules.{u, u} C S hS Z.1.toFunctor Z.2.1) :
    (modulePullback C S hS
        (preimageProjection C S hS (chartToSpace C S hS X' U') Z)).obj A ≅
      (modulePullback C S hS (preimageChartIso C S hS Z.1 hG U').hom).obj
        ((modulePullback C S hS
            (chartToSpace C S hS (IsThickening.space C S hS hG)
              ((thickeningChartBaseChange C S hS hG).obj U'))).obj A) :=
  (eqToIso (congrArg (modulePullback C S hS)
      (preimageProjection_eq_preimageChartIso_comp C S hS Z hG U'))).app A
    ≪≫ ((modulePullbackCompIso C S hS (preimageChartIso C S hS Z.1 hG U').hom
          (chartToSpace C S hS (IsThickening.space C S hS hG)
            ((thickeningChartBaseChange C S hS hG).obj U'))).app A).symm

/-! ### The two modules of the restricted problem -/

/-- **The source module of the restricted problem is the original one, pulled back to the
base-changed chart.**  The inverse image of `Ω_{Y/Bb}` along the restricted problem's morphism
`a'` is the inverse image of `a^*Ω_{Y/Bb}` along the comparison and the structure morphism of the
base-changed chart — pure pseudofunctoriality of the inverse image, by
`AlgebraicGeometry.Space.modulePullbackCompIso`, with no geometry. -/
def chartPullbackDifferentialsIso
    (a' : (⟨(Z.1.preimage (chartToSpace C S hS X' U').hom).toFunctor,
        (isClosedSubspace_preimage C S hS (chartToSpace C S hS X' U').hom Z.1 X'.2
          (chartSpace C S hS X' U').2 Z.2).1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (ha' : a' = preimageProjection C S hS (chartToSpace C S hS X' U') Z ≫ aZ) :
    (modulePullback C S hS a').obj (sheafOfDifferentials C S hS q) ≅
      (modulePullback C S hS (preimageChartIso C S hS Z.1 hG U').hom).obj
        ((modulePullback C S hS
            (chartToSpace C S hS (IsThickening.space C S hS hG)
              ((thickeningChartBaseChange C S hS hG).obj U'))).obj
          ((modulePullback C S hS aZ).obj (sheafOfDifferentials C S hS q))) :=
  (eqToIso (congrArg (modulePullback C S hS) ha')).app (sheafOfDifferentials C S hS q)
    ≪≫ ((modulePullbackCompIso C S hS
          (preimageProjection C S hS (chartToSpace C S hS X' U') Z) aZ).app
        (sheafOfDifferentials C S hS q)).symm
    ≪≫ modulePullbackPreimageProjectionIso C S hS Z hG U'
      ((modulePullback C S hS aZ).obj (sheafOfDifferentials C S hS q))

/-- **The target module of the restricted problem is the original conormal module, pulled back to
the base-changed chart.**  The conormal module of the restricted thickening is the inverse image
of `𝒞_{Z/X'}` along the projection, by [Stacks Project, Tag 04CO] at the chart morphism — which
is étale by `AlgebraicGeometry.Space.isEtale_chartToSpace`, so no hypothesis is carried — and
that projection factors through the base-changed chart. -/
def chartPullbackConormalIso :
    conormalModule C S hS (chartSpace C S hS X' U')
        (preimageSubspace C S hS (chartToSpace C S hS X' U') Z) ≅
      (modulePullback C S hS (preimageChartIso C S hS Z.1 hG U').hom).obj
        ((modulePullback C S hS
            (chartToSpace C S hS (IsThickening.space C S hS hG)
              ((thickeningChartBaseChange C S hS hG).obj U'))).obj
          (conormalModule C S hS X' Z)) :=
  (conormalModuleEtaleRestrictionIso C S hS (chartToSpace C S hS X' U')
      (isEtale_chartToSpace C S hS X' U') Z).symm
    ≪≫ modulePullbackPreimageProjectionIso C S hS Z hG U' (conormalModule C S hS X' Z)

/-! ### The identification of the two homes -/

/-- **The global sections of the acting sheaf of the lifting problem restricted along `U'` are
the sections of the transported acting sheaf over `U'`.**

The hypothesis `ha'` says the restricted problem's morphism is `a` precomposed with the
projection of the restricted thickening, which is what a lift over `U'` satisfies by
`AlgebraicGeometry.Space.inclusion_comp_chartLiftHom`. -/
def liftActionSheafChartSectionsEquiv
    (a' : (⟨(Z.1.preimage (chartToSpace C S hS X' U').hom).toFunctor,
        (isClosedSubspace_preimage C S hS (chartToSpace C S hS X' U').hom Z.1 X'.2
          (chartSpace C S hS X' U').2 Z.2).1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (ha' : a' = preimageProjection C S hS (chartToSpace C S hS X' U') Z ≫ aZ) :
    (liftActionSheaf C S hS
        (preimageSubspace C S hS (chartToSpace C S hS X' U') Z) q a').sections ≃
      (liftActionSheafTransport C S hS Z hG q aZ).obj.obj (op U') :=
  haveI := isEquivalence_modulePullback_of_iso C S hS (preimageChartIso C S hS Z.1 hG U')
  (smallEtaleInternalHomSectionsEquiv C S hS
      (preimageSubspace C S hS (chartToSpace C S hS X' U') Z).1.toFunctor
      (preimageSubspace C S hS (chartToSpace C S hS X' U') Z).2.1 _ _).trans
    (((Iso.homCongr (chartPullbackDifferentialsIso C S hS Z hG q aZ U' a' ha')
          (chartPullbackConormalIso C S hS Z hG U')).trans
        (Functor.FullyFaithful.ofFullyFaithful
          (modulePullback C S hS
            (preimageChartIso C S hS Z.1 hG U').hom)).homEquiv.symm).trans
      (smallEtaleInternalHomChartPullbackHomEquiv C S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
        ((modulePullback C S hS aZ).obj (sheafOfDifferentials C S hS q))
        (conormalModule C S hS X' Z)
        ((thickeningChartBaseChange C S hS hG).obj U')).symm)

end AlgebraicGeometry.Space

end
