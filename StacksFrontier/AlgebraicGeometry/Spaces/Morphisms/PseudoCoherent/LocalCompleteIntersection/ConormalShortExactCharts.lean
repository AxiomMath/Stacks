module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSchemeChartExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningCompositionComplex

/-!
# The conormal sequence of a composition of formally unramified morphisms, chart by chart

`AlgebraicGeometry.Space.shortExact_iff_mono_universalThickeningCompConormalLeftMap` of the module
`ConormalShortExact` of this directory states Stacks 06CC for the conormal sequence
`0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of formally unramified morphisms `Z ⟶ Y ⟶ X`
through its two named arrows, granting the vanishing of their composite as `hzero`.
This file takes the sequence instead as the short complex of
`AlgebraicGeometry.Space.universalThickeningConormalMap_comp_conormalMap_eq_zero`: its two
arrows and the vanishing of their composite are all read off that one theorem, clause (2) of
Stacks 06BF, so `hzero` is not needed.  It then proves that each clause of the short exactness
descends from one étale scheme chart surjective on points, which is the shape in which the case
of schemes, Stacks 06BA, would deliver it.

## Main results

* `AlgebraicGeometry.Space.mono_universalThickeningCompConormalLeftMap_of_chart'`: injectivity
  of the left-hand arrow descends from one étale chart surjective on points.
* `AlgebraicGeometry.Space.exact_universalThickeningConormalMapComp_of_chart`: the same for
  exactness at the middle term `𝒞_{Z/X}`.
* `AlgebraicGeometry.Space.exact_universalThickeningCompConormalSequence_of_forall_chart`: the
  same with the chart discharged from the scheme atlas of the space.
* `AlgebraicGeometry.Space.shortExact_iff_mono_universalThickeningCompConormalLeftMap'`: granted
  exactness at `𝒞_{Z/X}`, short exactness of the sequence is exactly injectivity of its
  left-hand arrow.
* `AlgebraicGeometry.Space.shortExact_universalThickeningCompConormalSequence_of_chart`: short
  exactness of the sequence descends from one étale scheme chart surjective on points.
* `AlgebraicGeometry.Space.universalThickeningCompConormalSequence_shortExact'`: Stacks 06CC,
  granting exactness at the middle term and the injectivity of the left-hand arrow.

## Implementation notes

The two arrows of the sequence are large terms, and two independently elaborated spellings of
either one cannot be compared within the heartbeat budget; every statement below therefore
writes the short complex out in full, so that one elaboration of each arrow serves all of them.

## References

* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-! ### Injectivity of the left-hand arrow, the case of schemes -/

/-- **The injectivity clause descends from an étale chart.**  Injectivity of the left-hand arrow
of the conormal sequence of the composition after inverse image along one étale scheme chart
surjective on points gives it on the algebraic space, by
`mono_modulePullback_schemeChart_iff`.  This is the shape in which a reduction of the clause of
Stacks 06CC to the case of schemes, Stacks 06BA, would deliver it. -/
public theorem mono_universalThickeningCompConormalLeftMap_of_chart'
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hm : Mono ((modulePullback B S hS (ObjectProperty.homMk a :
        schemeSpace U ⟶ universalThickeningCompConormalBase B S hS i hZ hY hfac)).map
      (ShortComplex.mk _ _
        (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f)) :
    Mono (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f :=
  (mono_modulePullback_schemeChart_iff B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f
    U a haEtale haSurj).mp hm

/-! ### Exactness at the middle term, the case of schemes -/

/-- **Exactness at `𝒞_{Z/X}` descends from an étale chart.**  If the inverse image of the
conormal sequence of the composition along one étale scheme chart of the space it lives on,
surjective on points, is exact, then the sequence is exact.

This is `AlgebraicGeometry.Space.exact_of_exact_modulePullback_schemeChart` at this complex, and
it is the shape in which a reduction to the case of schemes would deliver the one clause of
Stacks 06BD, Stacks 06BF and Stacks 06CC that is missing — the hypothesis `hmid` below, which
every statement of this file that needs exactness in the middle takes as an input.  It is the
companion of `AlgebraicGeometry.Space.mono_universalThickeningCompConormalLeftMap_of_chart'` for
the middle clause rather than the left one, and it asks strictly less of the chart than
`AlgebraicGeometry.Space.shortExact_universalThickeningCompConormalSequence_of_chart`, which
needs the injectivity at the left term as well.

What is still missing to use it is the comparison named in the section *What is carried* of the
module `ConormalShortExact` of this directory: nothing identifies the inverse image of this
sequence along a scheme chart with the sequence of schemes whose middle exactness
`Stacks.Thickenings.transitivityConormalShortComplex_exact` carries. -/
public theorem exact_universalThickeningConormalMapComp_of_chart
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : ((modulePullback B S hS (ObjectProperty.homMk a :
          schemeSpace U ⟶
            universalThickeningCompConormalBase B S hS i hZ hY hfac)).mapShortComplex.obj
        (ShortComplex.mk _ _
          (universalThickeningConormalMap_comp_conormalMap_eq_zero
            B S hS i hZ hY hfac))).Exact) :
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero
        B S hS i hZ hY hfac)).Exact :=
  exact_of_exact_modulePullback_schemeChart B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac))
    U a haEtale haSurj h

/-- **Exactness at `𝒞_{Z/X}` needs no chart to be exhibited.**  If the inverse image of the
conormal sequence of the composition is exact along *every* étale scheme chart of the space it
lives on which is surjective on points, then the sequence is exact. -/
public theorem exact_universalThickeningCompConormalSequence_of_forall_chart
    (h : ∀ (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1),
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      ((modulePullback B S hS (ObjectProperty.homMk a :
            schemeSpace U ⟶
              universalThickeningCompConormalBase B S hS i hZ hY hfac)).mapShortComplex.obj
          (ShortComplex.mk _ _
            (universalThickeningConormalMap_comp_conormalMap_eq_zero
              B S hS i hZ hY hfac))).Exact) :
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero
        B S hS i hZ hY hfac)).Exact := by
  obtain ⟨U, a, haSurj, haEtale⟩ :=
    (universalThickeningCompConormalBase B S hS i hZ hY hfac).2.exists_atlas
  exact exact_universalThickeningConormalMapComp_of_chart B S hS i hZ hY hfac U a
    haEtale haSurj (h U a haEtale haSurj)

/-! ### Short exactness -/

/-- Granted exactness at `𝒞_{Z/X}`, the conormal sequence of the composition is short exact
exactly when its left-hand arrow is injective.  The vanishing of the composite is the `zero`
field of the complex, that is clause (2) of Stacks 06BF, and the epimorphism at the right term
is the other half of that clause, `AlgebraicGeometry.Space.epi_conormalMap_comp`. -/
public theorem shortExact_iff_mono_universalThickeningCompConormalLeftMap'
    (hmid : (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).Exact) :
    (ShortComplex.mk _ _
        (universalThickeningConormalMap_comp_conormalMap_eq_zero
          B S hS i hZ hY hfac)).ShortExact ↔
      Mono (ShortComplex.mk _ _
        (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f := by
  have hepi : Epi (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).g :=
    epi_conormalMap_comp B S hS i hZ hY hfac
  exact ⟨fun h => h.mono_f, fun h => ShortComplex.ShortExact.mk' hmid h hepi⟩

/-- **Short exactness of the conormal sequence descends from an étale chart.**  If the inverse
image of the sequence along one étale scheme chart of the space it lives on, surjective on
points, is short exact, then the sequence is short exact — with neither `hmid` nor `hmono`
granted.

This is `AlgebraicGeometry.Space.shortExact_of_shortExact_modulePullback_schemeChart` at this
complex, and it is the shape in which the case of schemes delivers the whole of Stacks 06CC:
`Stacks.Thickenings.transitivityConormalShortComplex_shortExact` is
`@[stacks 06BA "the conormal sequence of Stacks 06AE is short exact"]`.  What is still missing
to use it is the comparison named in the section *What is carried* of the
module `ConormalShortExact` of this directory. -/
public theorem shortExact_universalThickeningCompConormalSequence_of_chart
    (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ (universalThickeningCompConormalBase B S hS i hZ hY hfac).1)
    (haEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : ((modulePullback B S hS (ObjectProperty.homMk a :
          schemeSpace U ⟶
            universalThickeningCompConormalBase B S hS i hZ hY hfac)).mapShortComplex.obj
        (ShortComplex.mk _ _
          (universalThickeningConormalMap_comp_conormalMap_eq_zero
            B S hS i hZ hY hfac))).ShortExact) :
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero
        B S hS i hZ hY hfac)).ShortExact :=
  shortExact_of_shortExact_modulePullback_schemeChart B S hS
    (X := universalThickeningCompConormalBase B S hS i hZ hY hfac)
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac))
    U a haEtale haSurj h

/-- **Stacks 06CC.**  For formally unramified morphisms `Z ⟶ Y ⟶ X` of algebraic spaces over `S`
with `Z ⟶ Y` a local complete intersection morphism, the conormal sequence
`0 ⟶ i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of Stacks 06BD is short exact. -/
public theorem universalThickeningCompConormalSequence_shortExact'
    (hlci : IsLocalCompleteIntersection B S hS i)
    (hmid : (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).Exact)
    (hmono : IsLocalCompleteIntersection B S hS i →
      Mono (ShortComplex.mk _ _
        (universalThickeningConormalMap_comp_conormalMap_eq_zero B S hS i hZ hY hfac)).f) :
    (ShortComplex.mk _ _
      (universalThickeningConormalMap_comp_conormalMap_eq_zero
        B S hS i hZ hY hfac)).ShortExact :=
  (shortExact_iff_mono_universalThickeningCompConormalLeftMap' B S hS i hZ hY hfac hmid).mpr
    (hmono hlci)

end AlgebraicGeometry.Space

end
