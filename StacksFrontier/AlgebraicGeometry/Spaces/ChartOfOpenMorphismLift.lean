module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen

/-!
# Functoriality of the chart of an open off the support

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)` be the
open complement `AlgebraicGeometry.Space.idealComplement` and let `A` be an étale scheme chart of
`X`.  `AlgebraicGeometry.Space.exists_pc_eq_openChart` says that a Zariski open `V` of the
chart's scheme lying off the support of the chartwise sheaf of ideals cuts out an étale chart of
`U` whose postcomposition with `j : U ⟶ X` is `AlgebraicGeometry.Space.openChart … A V` on the
nose.  It is an *existence* statement about one open, and says nothing about an inclusion
`V' ≤ V` of two of them.

This file supplies the functoriality.  Postcomposition along `j` is **full** as soon as `j` is a
monomorphism, so every morphism of étale charts of `X` between two charts that come from `U` is
the postcomposition of a morphism of charts of `U`; choosing a chart of `U` for each open off the
support then gives a family of charts of `U` indexed by those opens, and the inclusion of two
such opens lifts to a morphism of the corresponding charts of `U`.

## Main definitions

* `AlgebraicGeometry.Space.pcMap`: postcomposition with `j : U ⟶ X` on a morphism of étale
  charts of `U`, the morphism-level counterpart of `AlgebraicGeometry.Space.pc`.
* `AlgebraicGeometry.Space.idealComplementChart`: **the étale chart of `U` cut out by a Zariski
  open of a chart's scheme lying off the support**, chosen out of
  `AlgebraicGeometry.Space.exists_pc_eq_openChart`.
* `AlgebraicGeometry.Space.idealComplementChartHom`: **the morphism of charts of `U` lifting the
  inclusion of the charts of `X` cut out by an inclusion of opens** — the functoriality of the
  previous definition in the open.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtalePostcomp_map_eq` and
  `AlgebraicGeometry.Space.full_smallEtalePostcomp`: **postcomposition along a monomorphic étale
  morphism of algebraic spaces is full**.  This is the lift, and it is pure cancellation.
* `AlgebraicGeometry.Space.mono_idealComplementι_hom`: the inclusion of `U = X ∖ V(ℐ)` is a
  monomorphism of presheaves, being the inclusion of a subfunctor.
* `AlgebraicGeometry.Space.exists_pcMap_eq` and
  `AlgebraicGeometry.Space.exists_pcMap_eq_of_pc_eq`: **a morphism of étale charts of `X` between
  two charts that come from `U` comes from a morphism of charts of `U`** — in the second form
  transported along two equalities identifying the postcompositions with charts spelled however
  the consumer spells them.
* `AlgebraicGeometry.Space.pc_idealComplementChart`: the chosen chart of `U` postcomposes to the
  étale chart which the open cuts out.
* `AlgebraicGeometry.Space.pcMap_idealComplementChartHom`: **postcomposing the lifted morphism
  gives `AlgebraicGeometry.Space.openChartHomOfLE`**, transported along the two chart equalities;
  and `AlgebraicGeometry.Space.exists_pcMap_idealComplementChartHom_eq` is the same for an
  arbitrary morphism of relabelled charts.  This is the naturality datum which the transport to a
  chart of a morphism of modules defined on `U` consumes.

## Implementation notes

**The lift is cancellation of a monomorphism, nothing more.**  An object of the small étale site
of `X` is a `CategoryTheory.CostructuredArrow` together with a proposition, and a morphism of two
of them is a morphism of the underlying objects of the big fppf site of `S` together with a
commuting triangle; postcomposition along `j` changes only the structure morphism, by composing
it with `j`.  So a morphism of the postcompositions already carries the data of a candidate
morphism upstairs, and the only thing to check is its triangle over `U`, which becomes the
triangle over `X` after composing with `j` — that is `CategoryTheory.cancel_mono`.

**The relabelling of the target charts is a parameter, not a rewrite.**  The chart of `X` which
an open cuts out has two spellings — `AlgebraicGeometry.Space.openChart` and
`AlgebraicGeometry.Space.openChartOfComparison` — which are equal but not definitionally so, and
module-level statements use the second.  `AlgebraicGeometry.Space.exists_pcMap_eq_of_pc_eq` and
`AlgebraicGeometry.Space.exists_pcMap_idealComplementChartHom_eq` therefore take the two charts and
the morphism between them as parameters with equations: a consumer at either spelling supplies
its own equalities and never has to rewrite inside a `CategoryTheory.eqToHom`, where each
occurrence would be a fresh definitional check of the comparison equivalences.

**The family is indexed by the open together with its containment in the complement of the
support**, that containment being what `AlgebraicGeometry.Space.exists_pc_eq_openChart` needs.
For an inclusion `V' ≤ V` of opens contained in the complement the containment of `V'` is
deduced, so that both ends of the lifted morphism are members of the same family and no chart has
to be chosen twice.

No hypothesis beyond the one `AlgebraicGeometry.Space.exists_pc_eq_openChart` carries is used,
and no declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM
to an étale chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Postcomposition along a monomorphism is full -/

section Postcomp

variable {X Y : AlgebraicSpaces B S hS}

/-- **A morphism of the postcompositions of two étale charts of `X` along a monomorphic étale
morphism `f : X ⟶ Y` is the postcomposition of a morphism of those charts.**

The morphism of the underlying objects of the big fppf site of `S` is the one the given morphism
already carries; its triangle over `X` is the triangle over `Y` with `f` cancelled. -/
theorem exists_smallEtalePostcomp_map_eq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hmono : Mono f.hom) {P Q : SmallEtale B S hS X.1}
    (a : (smallEtalePostcomp B S hS f hf).obj P ⟶ (smallEtalePostcomp B S hS f hf).obj Q) :
    ∃ l : P ⟶ Q, (smallEtalePostcomp B S hS f hf).map l = a := by
  have := hmono
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk a.hom.left ?_), ?_⟩
  · exact (cancel_mono f.hom).1
      ((Category.assoc _ _ _).trans (CostructuredArrow.w a.hom))
  · apply ObjectProperty.hom_ext
    exact CostructuredArrow.hom_ext _ _ rfl

/-- **Postcomposition along a monomorphic étale morphism of algebraic spaces is a full functor of
small étale sites.** -/
theorem full_smallEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hmono : Mono f.hom) :
    (smallEtalePostcomp B S hS f hf).Full :=
  ⟨fun a => exists_smallEtalePostcomp_map_eq B S hS f hf hmono a⟩

end Postcomp

variable (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)

/-! ### Lifting a morphism of charts along the inclusion of the open complement -/

/-- The inclusion `j : U ⟶ X` of `U = X ∖ V(ℐ)` is a monomorphism of presheaves, being the
inclusion of a subfunctor. -/
theorem mono_idealComplementι_hom : Mono (idealComplementι B S hS X I).hom :=
  inferInstanceAs (Mono (idealComplementSubfunctor B S hS X I).ι)

/-- Postcomposition with `j : U ⟶ X` on a morphism of étale charts of `U = X ∖ V(ℐ)`, the
morphism-level counterpart of `AlgebraicGeometry.Space.pc`. -/
abbrev pcMap {P Q : SmallEtale B S hS (idealComplement B S hS X I).1} (l : P ⟶ Q) :
    pc B S hS X I P ⟶ pc B S hS X I Q :=
  (smallEtalePostcomp B S hS (idealComplementι B S hS X I)
    (isEtale_idealComplementι B S hS X I)).map l

/-- **A morphism of étale charts of `X` between two charts that come from `U = X ∖ V(ℐ)` comes
from a morphism of charts of `U`**: `AlgebraicGeometry.Space.full_smallEtalePostcomp` at the
inclusion of the open complement, which is a monomorphism. -/
theorem exists_pcMap_eq {P Q : SmallEtale B S hS (idealComplement B S hS X I).1}
    (a : pc B S hS X I P ⟶ pc B S hS X I Q) :
    ∃ l : P ⟶ Q, pcMap B S hS X I l = a :=
  exists_smallEtalePostcomp_map_eq B S hS (idealComplementι B S hS X I)
    (isEtale_idealComplementι B S hS X I) (mono_idealComplementι_hom B S hS X I) a

/-- **The lift of a morphism of étale charts of `X` whose two ends are identified with
postcompositions of charts of `U = X ∖ V(ℐ)`.**

The two charts of `X` and the morphism between them are parameters with equations, so that a
consumer spelling those charts in any way — in particular at
`AlgebraicGeometry.Space.openChartOfComparison`, where the module-level statements live — can use
this without rewriting inside the `CategoryTheory.eqToHom`s. -/
theorem exists_pcMap_eq_of_pc_eq {P' P : SmallEtale B S hS (idealComplement B S hS X I).1}
    {Q' Q : SmallEtale B S hS X.1} (hP' : pc B S hS X I P' = Q')
    (hP : pc B S hS X I P = Q) (k : Q' ⟶ Q) :
    ∃ l : P' ⟶ P, pcMap B S hS X I l = eqToHom hP' ≫ k ≫ eqToHom hP.symm :=
  exists_pcMap_eq B S hS X I _

/-! ### The family of charts of the open complement -/

variable (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The étale chart of `U = X ∖ V(ℐ)` cut out by a Zariski open of a chart's scheme lying off
the support of the chartwise sheaf of ideals**, chosen out of
`AlgebraicGeometry.Space.exists_pc_eq_openChart`. -/
def idealComplementChart (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    SmallEtale B S hS (idealComplement B S hS X I).1 :=
  (exists_pc_eq_openChart B S hS X I hI A hV).choose

/-- The chosen chart of `U = X ∖ V(ℐ)` postcomposes with `j : U ⟶ X` to the étale chart of `X`
which the open cuts out. -/
theorem pc_idealComplementChart (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    pc B S hS X I (idealComplementChart B S hS X I hI A V hV) = openChart B S hS X.1 A V :=
  (exists_pc_eq_openChart B S hS X I hI A hV).choose_spec

/-- **The lift to the charts of `U = X ∖ V(ℐ)` of a morphism between two relabellings of the
charts of `X` cut out by an inclusion of Zariski opens off the support.**

Taking `Q' = openChart … A V'`, `Q = openChart … A V` and `k` the inclusion gives
`AlgebraicGeometry.Space.idealComplementChartHom`; taking the relabelling to
`AlgebraicGeometry.Space.openChartOfComparison` and `k` the induced morphism of charts there
gives the datum a transport of modules to the chart's scheme needs. -/
theorem exists_pcMap_idealComplementChartHom_eq (A : SmallEtale B S hS X.1)
    {V' V : (chartScheme A).Opens} (h : V' ≤ V)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens))
    {Q' Q : SmallEtale B S hS X.1} (hQ' : openChart B S hS X.1 A V' = Q')
    (hQ : openChart B S hS X.1 A V = Q) (k : Q' ⟶ Q) :
    ∃ l : idealComplementChart B S hS X I hI A V' (h.trans hV) ⟶
        idealComplementChart B S hS X I hI A V hV,
      pcMap B S hS X I l =
        eqToHom ((pc_idealComplementChart B S hS X I hI A V' (h.trans hV)).trans hQ') ≫ k ≫
          eqToHom ((pc_idealComplementChart B S hS X I hI A V hV).trans hQ).symm :=
  exists_pcMap_eq_of_pc_eq B S hS X I
    ((pc_idealComplementChart B S hS X I hI A V' (h.trans hV)).trans hQ')
    ((pc_idealComplementChart B S hS X I hI A V hV).trans hQ) k

/-- **The morphism of étale charts of `U = X ∖ V(ℐ)` lifting the inclusion of the charts of `X`
cut out by an inclusion of Zariski opens off the support**: the functoriality in the open of the
family `AlgebraicGeometry.Space.idealComplementChart`. -/
def idealComplementChartHom (A : SmallEtale B S hS X.1) {V' V : (chartScheme A).Opens} (h : V' ≤ V)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    idealComplementChart B S hS X I hI A V' (h.trans hV) ⟶
      idealComplementChart B S hS X I hI A V hV :=
  (exists_pcMap_idealComplementChartHom_eq B S hS X I hI A h hV rfl rfl
    (openChartHomOfLE B S hS X.1 A h)).choose

/-- **Postcomposing the lifted morphism with `j : U ⟶ X` gives
`AlgebraicGeometry.Space.openChartHomOfLE`**, transported along the two chart equalities of
`AlgebraicGeometry.Space.pc_idealComplementChart`. -/
theorem pcMap_idealComplementChartHom (A : SmallEtale B S hS X.1) {V' V : (chartScheme A).Opens}
    (h : V' ≤ V)
    (hV : V ≤ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens)) :
    pcMap B S hS X I (idealComplementChartHom B S hS X I hI A h hV) =
      eqToHom (pc_idealComplementChart B S hS X I hI A V' (h.trans hV)) ≫
        openChartHomOfLE B S hS X.1 A h ≫
          eqToHom (pc_idealComplementChart B S hS X I hI A V hV).symm :=
  (exists_pcMap_idealComplementChartHom_eq B S hS X I hI A h hV rfl rfl
    (openChartHomOfLE B S hS X.1 A h)).choose_spec

end AlgebraicGeometry.Space

end
