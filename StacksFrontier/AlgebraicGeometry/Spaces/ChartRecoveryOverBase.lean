module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelocalizedBaseTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRecoveryOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# Stacks 04KL for a single pair of étale charts

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, let `ψ` be
a locally ringed morphism of their small étale ringed topoi which is 2-compatible with the
structure morphisms to `AlgebraicGeometry.Space.baseSpace`, let `T` be an étale scheme chart of
`X`, let `V` be one of `Y` with affine underlying scheme, and let `s : h_T ⟶ ψ⁻¹h_V` be a section.
Then the relocalized morphism of [Stacks Project, Tag 04J8] attached to `s`, conjugated into a
morphism of the small étale ringed topoi of the two charts, is induced by a morphism `T ⟶ V` of the
big fppf site over `S`, that is, a morphism over `S`.

## Main results

* `AlgebraicGeometry.Space.chartToSpace_comp_toBaseSpace`: the structure morphism of a chart to the
  base is the one represented by the terminal morphism of the site.
* `AlgebraicGeometry.Space.exists_chartHom_twoIso_chartRelocalized`: [Stacks Project, Tag 04KL] for
  a single pair of étale charts, the second of which is affine.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an étale chart to the base is represented by the terminal morphism of
the site. -/
theorem chartToSpace_comp_toBaseSpace (Y : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Y.1) :
    chartToSpace B S hS Y V ≫ toBaseSpace B S hS Y =
      representedSpaceMap B S hS
        (Over.mkIdTerminal.from (chartFppfObject B S hS Y V)) :=
  ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _)

variable (X Y : AlgebraicSpaces B S hS)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (T : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (s : smallEtaleChartSheaf B S hS X T ⟶
      ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y V))

/-- `AlgebraicGeometry.Space.chartRelocalized`, with the two chart spaces presented as the
representable algebraic spaces of the charts' objects of the site. -/
noncomputable def chartRelocalizedRepresented :
    RingedToposHom
      (smallEtaleRingedTopos B S hS (schemeSpace (chartFppfObject B S hS X T)))
      (smallEtaleRingedTopos B S hS (schemeSpace (chartFppfObject B S hS Y V))) :=
  chartRelocalized B S hS X Y ψ T V s

/-- `AlgebraicGeometry.Space.isLocallyRinged_chartRelocalized` in the representable
presentation. -/
theorem isLocallyRinged_chartRelocalizedRepresented (hψ : ψ.IsLocallyRinged) :
    (chartRelocalizedRepresented B S hS X Y ψ T V s).IsLocallyRinged :=
  isLocallyRinged_chartRelocalized B S hS X Y ψ T V s hψ

/-- `AlgebraicGeometry.Space.chartRelocalizedBaseTwoIso` over the base, with the two composite
structure morphisms presented as the ones represented by the terminal morphisms of the site. -/
noncomputable def chartRelocalizedRepresentedBaseTwoIso
    (hc : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X))) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS
          (Over.mkIdTerminal.from (chartFppfObject B S hS Y V))))
        (chartRelocalizedRepresented B S hS X Y ψ T V s))
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS
        (Over.mkIdTerminal.from (chartFppfObject B S hS X T)))) := by
  rw [← chartToSpace_comp_toBaseSpace B S hS Y V, ← chartToSpace_comp_toBaseSpace B S hS X T]
  exact chartRelocalizedBaseTwoIso B S hS X Y ψ T V s
    (toBaseSpace B S hS X) (toBaseSpace B S hS Y) hc

/-- [Stacks Project, Tag 04KL] for a single pair of étale charts: let `ψ` be a locally ringed
morphism of the small étale ringed topoi of `X` and `Y` which is 2-compatible with the structure
morphisms to `AlgebraicGeometry.Space.baseSpace`, let `T` be an étale scheme chart of `X`, let `V`
be one of `Y` whose underlying scheme is affine, and let `s : h_T ⟶ ψ⁻¹h_V` be a section. Then the
conjugated relocalized morphism of [Stacks Project, Tag 04J8] attached to `s` is induced by a
morphism `T ⟶ V` of the big fppf site over `S`, that is, over `S`. -/
theorem exists_chartHom_twoIso_chartRelocalized (hψ : ψ.IsLocallyRinged)
    (hV : IsAffineOver B S hS (chartFppfObject B S hS Y V))
    (hc : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X))) :
    ∃ g : chartFppfObject B S hS X T ⟶ chartFppfObject B S hS Y V,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (chartRelocalizedRepresented B S hS X Y ψ T V s)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))) :=
  exists_hom_twoIso_of_isLocallyRinged_of_twoIso B S hS
    (Over.mkIdTerminal.from (chartFppfObject B S hS X T))
    (Over.mkIdTerminal.from (chartFppfObject B S hS Y V))
    (chartRelocalizedRepresented B S hS X Y ψ T V s) hV
    (isLocallyRinged_chartRelocalizedRepresented B S hS X Y ψ T V s hψ)
    (chartRelocalizedRepresentedBaseTwoIso B S hS X Y ψ T V s hc)

end AlgebraicGeometry.Space

end
