module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction

/-!
# A nonempty étale chart of an algebraic space over a scheme of the site

Let `U` be an object of the big fppf site of `S` and let `X` be an algebraic space over the
scheme `U.left.1` underlying it. This file produces, from surjectivity and local finite
presentation of the structural morphism of `X` — in the form Stacks 03YK states them, as
properties of the morphism of algebraic spaces over `S` obtained from `X` by the forward functor
of Stacks 04SG — an étale chart `T ⟶ X` whose underlying scheme is **nonempty** and whose
structure morphism `T ⟶ U.left.1` is **locally of finite presentation** as a morphism of schemes.

This is the second and third step of the proof of Stacks 06DA: the fibre `X_y` of a 1-morphism
over an object `y` of the target is surjective and locally of finite presentation over the base,
so it is nonempty, and a nonempty scheme étale over it is locally of finite presentation over the
base by Stacks 03XP.

The passage between the two bases is purely bookkeeping. Nonemptiness is a statement about the
point set of Stacks 03BU, and the point set is unchanged by the lower-shriek extension
(`AlgebraicGeometry.Space.pointsRelocalize_bijective`); local finite presentation is an
every-étale-chart condition, and those are unchanged by it as well
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`).

## Main definitions

* `AlgebraicGeometry.Space.toTerminalHom`: the structure morphism of an object of the big fppf
  site of `V`, read as a morphism to the terminal object of that site.

## Main results

* `AlgebraicGeometry.Space.prop_inclusion_map_hom_of_holdsOnEveryEtaleChart`: a property of
  scheme morphisms tested on every étale chart of the structural morphism of an algebraic space
  holds for the structure morphism of every étale chart of it.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff`: an every-étale-chart
  condition on the structural morphism of Stacks 04SG is the same condition on the structural
  morphism over the smaller base.
* `AlgebraicGeometry.Space.nonempty_points_of_isSurjective_algebraicSpaceMap`: the point set of
  an algebraic space over `U.left.1` with surjective structural morphism is nonempty.
* `AlgebraicGeometry.Space.exists_nonempty_etaleChart_locallyOfFinitePresentation`: the chart.

## Implementation notes

The terminal object of the big fppf site of `V` is `Over.mk (𝟙 (B.obj hV))`, and the structural
morphism of an algebraic space to it is `AlgebraicGeometry.Space.toYonedaId`. An étale chart of
that structural morphism is a commuting square whose chart of the target is the identity of the
terminal object, and the morphism of the site filling it is the structure morphism of the chart of
the source — which is what turns the every-étale-chart condition into a statement about that
structure morphism.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (V : Scheme.{u}) (hV : B.Contains V)

/-! ### The structure morphism of an object of the site, read into the site -/

/-- The structure morphism of an object of the big fppf site of `V`, read as a morphism to the
terminal object of that site. -/
def toTerminalHom (T : BigFppfOver B V hV) : T ⟶ Over.mk (𝟙 (B.obj hV)) :=
  Over.homMk T.hom

/-- The underlying morphism of schemes of `toTerminalHom B V hV T` is the structure morphism of
`T`. -/
@[simp]
theorem toScheme_map_toTerminalHom (T : BigFppfOver B V hV) :
    (BigFppfOver.toScheme B V hV).map (toTerminalHom B V hV T) = B.inclusion.map T.hom :=
  rfl

/-- Every étale chart of an algebraic space fills a commuting square of étale charts of its
structural morphism, the chart of the target being the identity of the terminal object: the
morphism of the site filling it is the structure morphism of the chart. -/
theorem yoneda_map_toTerminalHom_eq {X : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B V hV) (φ : yoneda.obj T ⟶ X) :
    yoneda.map (toTerminalHom B V hV T) = φ ≫ toYonedaId B V hV X := by
  ext Z s
  refine Over.OverMorphism.ext ?_
  show Over.Hom.left (s ≫ toTerminalHom B V hV T) = (unop Z).hom
  rw [Over.comp_left]
  exact Over.w s

/-- **A property of scheme morphisms tested on every étale chart of the structural morphism of an
algebraic space over `V` holds for the structure morphism of each of its étale charts.** -/
theorem prop_inclusion_map_hom_of_holdsOnEveryEtaleChart (P : MorphismProperty Scheme.{u})
    {X : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u}
    (hX : HoldsOnEveryEtaleChart B V hV P (toYonedaId B V hV X))
    (T : BigFppfOver B V hV) (φ : yoneda.obj T ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B V hV)).presheaf φ) :
    P (B.inclusion.map T.hom) :=
  prop_toScheme_map_of_holdsOnEveryEtaleChart B V hV hX φ hφ
    (yoneda_map_toTerminalHom_eq B V hV T φ)

/-! ### A nonempty étale chart -/

/-- **An algebraic space over `V` with a point has a nonempty étale chart.** This is
Stacks 04N5, `AlgebraicGeometry.Space.exists_etale_chart_at_point`, with the field-valued point of
the chart read as a point of its underlying scheme by Stacks 03BV. -/
theorem exists_nonempty_etaleChart {X : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B V hV X) (x : points B V hV X) :
    ∃ (T : BigFppfOver B V hV) (φ : yoneda.obj T ⟶ X),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B V hV)).presheaf φ ∧
      Nonempty ((BigFppfOver.toScheme B V hV).obj T) := by
  obtain ⟨T, φ, hφ, p, -⟩ := exists_etale_chart_at_point B V hV X hX x
  exact ⟨T, φ, hφ, ⟨pointsEquivScheme B V hV T (p.class B V hV (yoneda.obj T))⟩⟩

/-! ### The two bases -/

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- **An every-étale-chart condition on the structural morphism of Stacks 04SG is the same
condition over the smaller base.** Both sides are the condition on the structural morphism of the
lower-shriek extension, which does not depend on the base. -/
theorem holdsOnEveryEtaleChart_algebraicSpaceMap_iff (P : MorphismProperty Scheme.{u})
    (U : BigFppfOver B S hS) (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B U.left.1 U.left.2 X) :
    HoldsOnEveryEtaleChart B S hS P
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom ↔
      HoldsOnEveryEtaleChart B U.left.1 U.left.2 P (toYonedaId B U.left.1 U.left.2 X) := by
  have h1 : HoldsOnEveryEtaleChart B S hS P
        ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app ⟨X, hX⟩ ≫
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩).1.hom) ↔
      HoldsOnEveryEtaleChart B S hS P
        (((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩).1.hom) :=
    holdsOnEveryEtaleChart_iso_comp_iff B S hS P _ _
  rw [relocalizeToYoneda_eq B U.left.1 S U.left.2 hS U.hom ⟨X, hX⟩] at h1
  exact h1.symm.trans
    (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom P X)

/-- **The point set of an algebraic space over `U.left.1` whose structural morphism is surjective
is nonempty**, provided the scheme underlying `U` is. The structural morphism is the one of
Stacks 04SG, and the comparison of the two point sets is
`AlgebraicGeometry.Space.pointsRelocalize_bijective`. -/
theorem nonempty_points_of_isSurjective_algebraicSpaceMap
    (U : BigFppfOver B S hS) (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B U.left.1 U.left.2 X)
    (hsurj : IsSurjective B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom)
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj U)) :
    Nonempty (points B U.left.1 U.left.2 X) := by
  obtain ⟨v⟩ := hne
  obtain ⟨z, -⟩ := hsurj ((pointsEquivScheme B S hS (Over.mk U.hom)).symm v)
  have hz := pointsHomeomorphOfIso B S hS
    ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨X, hX⟩) z
  exact ⟨(pointsRelocalize_surjective B U.left.1 S U.left.2 hS U.hom X hz).choose⟩

/-- **The second and third steps of the proof of Stacks 06DA.** An algebraic space over the scheme
underlying an object `U` of the big fppf site of `S`, whose structural morphism of Stacks 04SG is
surjective and locally of finite presentation, has an étale chart whose underlying scheme is
nonempty and whose structure morphism to `U.left.1` is locally of finite presentation.

The space is nonempty because its structural morphism is surjective and `U` is nonempty; a chart
through one of its points is nonempty; and local finite presentation of the structure morphism of
that chart is the every-étale-chart condition of Stacks 03XP applied to the square the chart
fills. -/
theorem exists_nonempty_etaleChart_locallyOfFinitePresentation
    (U : BigFppfOver B S hS) (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B U.left.1 U.left.2 X)
    (hsurj : IsSurjective B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom)
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ (T : BigFppfOver B U.left.1 U.left.2) (φ : yoneda.obj T ⟶ X),
      IsEtale B U.left.1 U.left.2 φ ∧
      Nonempty ((BigFppfOver.toScheme B U.left.1 U.left.2).obj T) ∧
      LocallyOfFinitePresentation (B.inclusion.map T.hom) := by
  obtain ⟨x⟩ := nonempty_points_of_isSurjective_algebraicSpaceMap B S hS U X hX hsurj hne
  obtain ⟨T, φ, hφ, hTne⟩ := exists_nonempty_etaleChart B U.left.1 U.left.2 hX x
  refine ⟨T, φ, isEtale_of_presheaf_etale B U.left.1 U.left.2 hφ, hTne, ?_⟩
  exact prop_inclusion_map_hom_of_holdsOnEveryEtaleChart B U.left.1 U.left.2 _
    ((holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS _ U X hX).mp hlfp) T φ hφ

end AlgebraicGeometry.Space

end
