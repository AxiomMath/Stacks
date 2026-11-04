module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison

/-!
# The morphism of an étale chart as a relocalized morphism of ringed topoi

Let `S` be a scheme and let

```
  U --g--> V
  |        |
  p        q
  v        v
  X --f--> Y
```

be a commutative diagram of algebraic spaces over `S` with `p` and `q` étale, and let
`c : U ⟶ V ×_Y X` be the arrow corresponding to `g`. Stacks 04M4 compares the morphism of
ringed topoi of `g` with the morphism `(f_c, f_c^♯)` that Stacks 04J1 builds from the morphism
of ringed *sites* `(f_{spaces,étale}, f^♯)`, through the identifications of Stacks 04LZ; Stacks
04J9 compares that same `(f_c, f_c^♯)` with the morphism `(f_s, f_s^♯)` that Stacks 04J8 builds
from the morphism of ringed *topoi* and the induced map `s : h_U ⟶ f^{-1}h_V`, through the
identifications of Stacks 04J3. Pasting the two comparisons exhibits the morphism of an étale
chart, on spaces-étale ringed topoi, as a relocalized morphism in the sense of Stacks 04J8. This
file records that pasting, for an abstract pair of chart identifications and granted the
comparisons that Stacks 04J9 is stated with. Stacks 04M5 itself, at the small étale ringed topoi
of the scheme charts, is `AlgebraicGeometry.Space.chartRelocalizedTwoIso`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.ChartRelocalizedTwoIsoStatement`: for a morphism of ringed
  sites, identifications of the localizations of its source and target at `U` and at `V` with
  ringed sites of their own, and a morphism between the latter two, the assertion that this
  morphism is 2-isomorphic to the relocalized morphism of Stacks 04J8.
* `AlgebraicGeometry.RingedSite.Hom.chartRelocalizedTwoIsoStatement`: that assertion holds as
  soon as the localization square of Stacks 04J1 commutes through the two identifications, the
  comparison of Stacks 04J1 with Stacks 04J8 being supplied by Stacks 04J9.
* `AlgebraicGeometry.Space.nonempty_spacesEtaleChartRelocalizedTwoIso`: the spaces-étale form of
  the chart comparison, obtained from the previous statement with the commuting square supplied
  by Stacks 04M4.

## Implementation notes

The hypotheses that Stacks 04J9 is stated with are bundled as
`AlgebraicGeometry.RingedSite.Hom.RelocalizedComparisonData`: the comparisons of Stacks 04J5
and of Stacks 04J7 read as 2-isomorphisms of ringed topoi, and the compatibility of each with
the pair of diagrams it compares. The comparison `Phi` of the identification of Stacks 04LZ at
the chart `V` with the identification of Stacks 04J3 at `V`, together with its 2-isomorphism
`chartLocalization`, is also an argument. The conclusion is the commuting square precomposed
with the identification `iu` at the chart `U`, since Stacks 04LZ is a morphism of ringed sites
from the localization to the chart rather than an equivalence.

## References

* [Stacks Project, Tag 04M5](https://stacks.math.columbia.edu/tag/04M5)
* [Stacks Project, Tag 04M4](https://stacks.math.columbia.edu/tag/04M4)
* [Stacks Project, Tag 04J9](https://stacks.math.columbia.edu/tag/04J9)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V : Y.C} {U : X.C}
  (c : U ⟶ f.u.obj V) [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u]

/-- The hypotheses that Stacks 04J9 is stated with: the comparisons of Stacks 04J5 and of
Stacks 04J7 read as 2-isomorphisms of ringed topoi, and the compatibility of each with the pair
of diagrams it compares. -/
structure Hom.RelocalizedComparisonData where
  /-- Stacks 04J5 as a 2-isomorphism of ringed topoi: the two relocalizations agree. -/
  relocComparison : AlgebraicGeometry.RingedToposHom.TwoIso
    (A := ringedTopos (X.over U))
    (B := RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := ringedTopos (X.over (f.u.obj V)))
      (Z := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (f.compareMid V) (X.relocalizationRingedToposHom c))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (Z := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
      (representableLocalizationRingedMorphism X U))
  /-- Stacks 04J7 as a 2-isomorphism of ringed topoi: the two localized morphisms agree. -/
  locComparison : AlgebraicGeometry.RingedToposHom.TwoIso
    (A := ringedTopos (X.over (f.u.obj V)))
    (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
      (Y := ringedTopos (Y.over V))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (f.ringedToposHom.localized (representableSheaf Y V)) (f.compareMid V))
  /-- The comparison of Stacks 04J5 is compatible with the relocalization triangle of
  Stacks 04IY and that of Stacks 04J4. -/
  hRelocTriangles : f.relocTriangleCompareSite c =
    f.relocTriangleCompareTopos c relocComparison
  /-- The comparison of Stacks 04J7 is compatible with the localization square of Stacks 04J0
  and that of Stacks 04IF. -/
  hLocSquares : f.locSquareCompareSite V = f.locSquareCompareTopos V locComparison

variable {Cu Cv : RingedSite.{u, u, u}}
  (iu : AlgebraicGeometry.RingedToposHom (ringedTopos (X.over U)) (ringedTopos Cu))
  (iv : AlgebraicGeometry.RingedToposHom (ringedTopos (Y.over V)) (ringedTopos Cv))
  (gc : AlgebraicGeometry.RingedToposHom (ringedTopos Cu) (ringedTopos Cv))
  (Phi : AlgebraicGeometry.RingedToposHom (ringedTopos Cv)
    (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)))

/-- **The chart comparison on ringed sites**, for a morphism of ringed sites `f` together with
identifications `iu`, `iv` of the localizations of its source at `U` and of its target at `V`
with ringed sites `Cu`, `Cv` of their own: the morphism `gc` from `Cu` to `Cv`, read through
`Phi` and `iu`, is 2-isomorphic to the relocalized morphism `(f_s, f_s^♯)` of Stacks 04J8, read
through the identification of Stacks 04J3 at `U`. -/
def Hom.ChartRelocalizedTwoIsoStatement : Prop :=
  Nonempty (AlgebraicGeometry.RingedToposHom.TwoIso
    (A := ringedTopos (X.over U))
    (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := ringedTopos Cu)
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos Cu) (Y := ringedTopos Cv)
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        Phi gc)
      iu)
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (f.ringedToposHom.relocalized (f.relocalizationSheafMap c))
      (representableLocalizationRingedMorphism X U)))

omit [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u] in
/-- **Stacks 04M5**, as the pasting of a commuting chart square with Stacks 04J9. If the
localization square of Stacks 04J1 commutes through the chart identifications `iu` and `iv`,
and if the identification of Stacks 04J3 at `V` factors through `iv` and `Phi`, then `gc` read
through `Phi` and `iu` is 2-isomorphic to the relocalized morphism of Stacks 04J8. -/
theorem Hom.chartRelocalizedTwoIsoStatement
    (data : f.RelocalizedComparisonData c)
    (chartSquare : AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (X.over U)) (B := ringedTopos Cv)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (Y.over V)) (Z := ringedTopos Cv) iv (f.relocalized c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos Cu) (Z := ringedTopos Cv) gc iu))
    (chartLocalization : AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (Y.over V))
      (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (representableLocalizationRingedMorphism Y V)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (Y.over V))
        (Y := ringedTopos Cv)
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        Phi iv)) :
    f.ChartRelocalizedTwoIsoStatement c iu gc Phi := by
  obtain ⟨beta, -⟩ := f.exists_relocalizedComparison c data.relocComparison
    data.locComparison data.hRelocTriangles data.hLocSquares
  exact ⟨(AlgebraicGeometry.RingedToposHom.TwoIso.associator
        (A := ringedTopos (X.over U)) (B := ringedTopos Cu) (C := ringedTopos Cv)
        (D := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        iu gc Phi).symm.trans
    ((chartSquare.symm.whiskerRight Phi).trans
      ((AlgebraicGeometry.RingedToposHom.TwoIso.associator
            (A := ringedTopos (X.over U)) (B := ringedTopos (Y.over V))
            (C := ringedTopos Cv)
            (D := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
            (f.relocalized c) iv Phi).trans
        ((AlgebraicGeometry.RingedToposHom.TwoIso.whiskerLeft (f.relocalized c)
          chartLocalization.symm).trans beta)))⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y U V : AlgebraicSpaces B S hS}

/-- Base change of étale algebraic spaces preserves finite limits: the identity chart is
terminal on both sides and the spaces-étale site has fibre products. This is the flatness
hypothesis under which Stacks 04J9 is stated. -/
noncomputable instance preservesFiniteLimits_spacesEtaleRingedSiteHom_u (f : X ⟶ Y) :
    PreservesFiniteLimits (spacesEtaleRingedSiteHom B S hS f).u := by
  rw [spacesEtaleRingedSiteHom_u]
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (spacesBaseChange B S hS f).functor :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal _
      (SpacesEtale.isTerminal_idObj B S hS Y) (isTerminal_spacesBaseChange_idObj B S hS f)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

variable (f : X ⟶ Y) (g : U ⟶ V) (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    (q : V ⟶ Y) (hq : IsEtale B S hS q.hom)
    (c : etaleObject B S hS p hp ⟶
      (spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq))
    (hc : comparisonSpaceHom B S hS f p hp q hq c ≫
      (spacesBaseChange B S hS f).projection.app (etaleObject B S hS q hq) = g)

include hc

/-- **The chart comparison on spaces-étale ringed topoi.** Read through a comparison `Phi` of the
chart `V` with the localization of `Y` at `V` and through the identification of Stacks 04LZ at
the chart `U`, the morphism of ringed topoi `(g_{spaces,étale}, g^♯)` is 2-isomorphic to the
morphism `(f_s, f_s^♯)` that Stacks 04J8 builds from `(f_{spaces,étale}, f^♯)` and the map
`s : h_U ⟶ f^{-1}h_V` corresponding to `g`, read through the identification of Stacks 04J3 at
`U`, granted the comparisons in `data` and `chartLocalization`. Stacks 04M5 itself is
`AlgebraicGeometry.Space.chartRelocalizedTwoIso`. -/
theorem nonempty_spacesEtaleChartRelocalizedTwoIso
    (Phi : RingedToposHom
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (spacesEtaleRingedSite B S hS V))
      (RingedTopos.localizedRingedTopos
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (spacesEtaleRingedSite B S hS Y))
        (RingedSite.representableSheaf (spacesEtaleRingedSite B S hS Y)
          (etaleObject B S hS q hq))))
    (data : (spacesEtaleRingedSiteHom B S hS f).RelocalizedComparisonData c)
    (chartLocalization : RingedToposHom.TwoIso
      (A := RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        ((spacesEtaleRingedSite B S hS Y).over (etaleObject B S hS q hq)))
      (B := RingedTopos.localizedRingedTopos
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (spacesEtaleRingedSite B S hS Y))
        (RingedSite.representableSheaf (spacesEtaleRingedSite B S hS Y)
          (etaleObject B S hS q hq)))
      (RingedSite.representableLocalizationRingedMorphism (spacesEtaleRingedSite B S hS Y)
        (etaleObject B S hS q hq))
      (RingedToposHom.comp
        (X := RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          ((spacesEtaleRingedSite B S hS Y).over (etaleObject B S hS q hq)))
        (Y := RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (spacesEtaleRingedSite B S hS V))
        (Z := RingedTopos.localizedRingedTopos
          (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (spacesEtaleRingedSite B S hS Y))
          (RingedSite.representableSheaf (spacesEtaleRingedSite B S hS Y)
            (etaleObject B S hS q hq)))
        Phi (spacesEtaleLocalizationRingedSiteHom B S hS q hq).ringedToposHom)) :
    (spacesEtaleRingedSiteHom B S hS f).ChartRelocalizedTwoIsoStatement c
      (spacesEtaleLocalizationRingedSiteHom B S hS p hp).ringedToposHom
      (spacesEtaleRingedSiteHom B S hS g).ringedToposHom Phi :=
  (spacesEtaleRingedSiteHom B S hS f).chartRelocalizedTwoIsoStatement c
    (spacesEtaleLocalizationRingedSiteHom B S hS p hp).ringedToposHom
    (spacesEtaleLocalizationRingedSiteHom B S hS q hq).ringedToposHom
    (spacesEtaleRingedSiteHom B S hS g).ringedToposHom Phi data
    (spacesEtaleRelocalizedTwoIso B S hS f g p hp q hq c hc) chartLocalization

end AlgebraicGeometry.Space

end
