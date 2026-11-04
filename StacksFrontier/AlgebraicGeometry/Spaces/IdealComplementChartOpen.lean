module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitOverComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# A Zariski open of a chart off the support is an étale chart of the open complement

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site which is cartesian on affine charts, let
`U = X ∖ V(ℐ)` be the open complement of `AlgebraicGeometry.Space.idealComplement`, and let `A`
be an étale scheme chart of `X`.

The scheme of `A` carries the Zariski sheaf of ideals
`AlgebraicGeometry.Space.idealSheafDataOfChart`, whose support is a closed subset; Stacks 01YB is
stated over the complement of that support.  **This file identifies that complement as the
transport of `U` to the chart**: a Zariski open `V` of the chart's scheme contained in the
complement of the support cuts out an étale chart of `X` which *factors through `U`*, and the
resulting étale chart of `U` is carried back to `AlgebraicGeometry.Space.openChart … A V` on the
nose, not merely up to isomorphism.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_idealComplementι`: the point set of `U` is the unit
  locus of `ℐ`.
* `AlgebraicGeometry.Space.mem_idealUnitLocus_of_le_support_compl`: **the image in `X` of an
  étale chart cut out by a Zariski open off the support lies in the unit locus of `ℐ`.**  This is
  the geometric content: off the support an affine neighbourhood carries the unit ideal of
  sections of `ℐ`, by `ChartIdealSheafSupport`, and the chart it cuts out witnesses membership in
  the unit locus.
* `AlgebraicGeometry.Space.exists_hom_comp_idealComplementι_eq`: **such a chart factors through
  `U`**, by Stacks 03IE.
* `AlgebraicGeometry.Space.exists_pc_eq_openChart`: **it is the image under postcomposition with
  `j : U ⟶ X` of an étale chart of `U`, by an equality of charts.**  This is the statement the
  reduction of Stacks 07UM to a chart consumes: the sections of `𝒢|_U` over that chart of `U` are
  *the same object* as the sections of `𝒢` over `AlgebraicGeometry.Space.openChart … A V`.

## Implementation notes

**The factorization is upgraded to an étale chart of `U` by cancellation, not by a base change.**
A morphism `g : h_{V} ⟶ U` with `g ≫ j` étale after every representable base change is itself
such, which is the unconditional
`AlgebraicGeometry.Space.presheaf_etale_of_postcomp`; the hypothesis on `j` is that it is étale
after every representable base change, and `j` is an open immersion, so
`AlgebraicGeometry.Space.presheaf_etale_of_isOpenImmersion` supplies it.  Nothing about
quasi-coherence or Noetherianness enters.

**Why the resulting equality of charts is an equality.**  An object of the small étale site is a
`CategoryTheory.CostructuredArrow` together with a *proposition*, and
`AlgebraicGeometry.Space.smallEtalePostcomp` acts on it by composing the structure morphism with
`j`.  So the chart built from the factorization has structure morphism `g ≫ j`, which the
factorization says *is* the structure morphism of `AlgebraicGeometry.Space.openChart … A V`; the
two full-subcategory objects are therefore equal, by
`CategoryTheory.ObjectProperty.FullSubcategory.ext`.  This is the same mechanism as
`AlgebraicGeometry.Space.smallEtalePostcomp_chartOfHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/IdealPowerSupport.lean`.

**Points are compared through the representable comparison bijection.**  Two points of the site
with the same image are identified by `AlgebraicGeometry.Space.injective_pointsToScheme`, and the
comparison is natural in the site object by
`AlgebraicGeometry.Space.pointsToScheme_pointsMap_yoneda`; that is how a point of the chart cut
out by `V` and a point of the chart cut out by an affine neighbourhood of its image are seen to
have the same image in `X`.

**Only one direction is proved.**  That a Zariski open off the support cuts out a chart of `U` is
what the transport of a morphism defined on `U` to the chart needs.  The converse — that a
Zariski open whose chart factors through `U` lies off the support — is not here; see the report
accompanying this file.  It would need the sections of `ℐ` over an étale chart on which `ℐ` is
the unit ideal to be compared with the ideal of an affine open of the chart's scheme *below* it,
that is, a descent of the unit ideal from an étale chart to a Zariski open, which the library
does not have.

No declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to
an étale chart, not an assertion of any tag, and Stacks 03IE is already covered in the tree.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)

/-! ### The point set of the open complement -/

/-- **The point set of `U = X ∖ V(ℐ)` is the unit locus of `ℐ`.**  The open complement is the
open subspace attached to the unit locus, so this is the defining property of
`AlgebraicGeometry.Space.openSubspaceOfPoints`. -/
theorem range_pointsMap_idealComplementι :
    Set.range (pointsMap B S hS (idealComplement B S hS X I).1
        (idealComplementι B S hS X I).hom) = idealUnitLocus B S hS X I :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS (idealUnitLocus B S hS X I)

/-- The inclusion of `U = X ∖ V(ℐ)` is étale after every representable base change, being an
open immersion. -/
theorem presheaf_etale_idealComplementι :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (idealComplementι B S hS X I).hom :=
  presheaf_etale_of_isOpenImmersion B S hS
    (isOpenSubspace_idealComplementSubfunctor B S hS X I).2

/-! ### A Zariski open off the support maps into the unit locus -/

variable (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The image in `X` of the étale chart cut out by a Zariski open of a chart's scheme lying off
the support of the chartwise sheaf of ideals is contained in the unit locus of `ℐ`.**

A point of that chart has an image in the chart's scheme which lies in the open, hence off the
support, hence inside an affine open over which `ℐ` is the whole structure sheaf; the chart which
*that* affine open cuts out witnesses membership in the unit locus, and the two charts have the
same image point in `X` because both factor through `A` and their points agree there. -/
theorem mem_idealUnitLocus_of_le_support_compl (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).Opens}
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens))
    (y : points B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V)))) :
    pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V)))
        (openChart B S hS X.1 A V).1.hom y ∈ idealUnitLocus B S hS X I := by
  -- the image in the chart's scheme of the given point
  set p := pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V)) y with hp
  -- the points of the scheme of `A` coming from the chart cut out by an open `W` are those in `W`
  have hr : ∀ W : (chartScheme A).Opens, Set.range ((BigFppfOver.toScheme B S hS).map
      (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) W)) = W := fun W => by
    rw [toScheme_map_openSubHom]
    exact Scheme.Opens.range_ι W
  set x := (BigFppfOver.toScheme B S hS).map
    (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V) p with hx
  have hxV : x ∈ V := (hr V).le ⟨p, rfl⟩
  -- an affine neighbourhood of it on which `ℐ` is the whole structure sheaf
  obtain ⟨V₀, hxV₀, hV₀⟩ :=
    (mem_support_compl_iff_exists_affineOpen B S hS X I hI A x).1 (hV hxV)
  obtain ⟨q, hq⟩ := (hr V₀.1).ge hxV₀
  -- the chart it cuts out has the same image point in `X`
  refine ⟨openChart B S hS X.1 A V₀.1, hV₀,
    (pointsEquivScheme B S hS
      ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V₀.1))).symm q, ?_⟩
  have key : pointsMap B S hS _
        (yoneda.map (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V₀.1))
        ((pointsEquivScheme B S hS
          ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V₀.1))).symm q) =
      pointsMap B S hS _
        (yoneda.map (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V)) y := by
    refine injective_pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A) ?_
    refine Eq.trans (pointsToScheme_pointsMap_yoneda B S hS
      (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V₀.1) _) ?_
    refine Eq.trans ?_ (pointsToScheme_pointsMap_yoneda B S hS
      (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V) y).symm
    refine Eq.trans (congrArg ((BigFppfOver.toScheme B S hS).map
      (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V₀.1))
      ((pointsEquivScheme B S hS
        ((SmallEtale.toOver B S hS X.1).obj
          (openChart B S hS X.1 A V₀.1))).apply_symm_apply q)) ?_
    exact hq.trans hx
  refine Eq.trans (pointsMap_comp_apply B S hS
    (yoneda.map (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V₀.1)) A.1.hom _) ?_
  refine Eq.trans (congrArg (pointsMap B S hS _ A.1.hom) key) ?_
  exact (pointsMap_comp_apply B S hS
    (yoneda.map (openSubHom ((SmallEtale.toOver B S hS X.1).obj A) V)) A.1.hom y).symm

/-! ### The factorization through the open complement -/

/-- **An étale chart cut out by a Zariski open off the support factors through
`U = X ∖ V(ℐ)`.**  This is Stacks 03IE applied to the containment of point sets of
`AlgebraicGeometry.Space.mem_idealUnitLocus_of_le_support_compl`. -/
theorem exists_hom_comp_idealComplementι_eq (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).Opens}
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    ∃ g : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V)) ⟶
        (idealComplement B S hS X I).1,
      g ≫ (idealComplementι B S hS X I).hom = (openChart B S hS X.1 A V).1.hom := by
  refine (factorsThrough_openSubspace_iff_points B S hS X.2
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (idealComplementSubfunctor B S hS X I)
    (isOpenSubspace_idealComplementSubfunctor B S hS X I)
    (openChart B S hS X.1 A V).1.hom).2 ?_
  rintro z ⟨y, rfl⟩
  exact (range_pointsMap_ι_openSubspaceOfPoints B S hS (idealUnitLocus B S hS X I)).ge
    (mem_idealUnitLocus_of_le_support_compl B S hS X I hI A hV y)

/-- **A Zariski open of a chart's scheme lying off the support of the chartwise sheaf of ideals
cuts out an étale chart of `U = X ∖ V(ℐ)`**, and postcomposing that chart with `j : U ⟶ X`
returns `AlgebraicGeometry.Space.openChart … A V` *on the nose*.

This is the identification the reduction of Stacks 07UM to a chart consumes: the sections of a
module restricted to `U` over the chart of `U` produced here are the sections of the module over
the étale chart which `V` cuts out, with no comparison isomorphism in between. -/
theorem exists_pc_eq_openChart (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).Opens}
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    ∃ P : SmallEtale B S hS (idealComplement B S hS X I).1,
      pc B S hS X I P = openChart B S hS X.1 A V := by
  obtain ⟨g, hg⟩ := exists_hom_comp_idealComplementι_eq B S hS X I hI A hV
  refine ⟨⟨CostructuredArrow.mk g, ?_⟩, ?_⟩
  · exact presheaf_etale_of_postcomp B S hS (presheaf_etale_idealComplementι B S hS X I)
      (openChart B S hS X.1 A V).property hg
  · exact ObjectProperty.FullSubcategory.ext
      (congrArg (fun α : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
          (openChart B S hS X.1 A V)) ⟶ X.1 =>
        (CostructuredArrow.mk α : CostructuredArrow yoneda X.1)) hg)

end AlgebraicGeometry.Space

end
