module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelocalizedTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction

/-!
# The chartwise relocalized morphism is compatible with the structure morphisms to the base

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, let
`ψ` be a morphism of their small étale ringed topoi which is 2-compatible with structure
morphisms `pX : X ⟶ A` and `pY : Y ⟶ A` to a third algebraic space, let `T` be an étale scheme
chart of `X`, `V` one of `Y`, and `s : h_T ⟶ ψ⁻¹h_V` a section.

`AlgebraicGeometry.Space.chartRelocalizedRestrictionTwoIso` says the conjugated relocalized
morphism `ρ` of [Stacks Project, Tag 04J8] fits the square relating it to `ψ`. This file pushes
that square down to `A`: `ρ` is 2-compatible with the two composite structure morphisms
`T ⟶ X ⟶ A` and `V ⟶ Y ⟶ A`.

This is the form [Stacks Project, Tag 04KL] consumes.  The morphism of schemes that
[Stacks Project, Tag 04I6] produces out of `ρ` is an *absolute* morphism, while the gluing needs
one over `A`; the 2-compatibility recorded here is what identifies its composite with the
structure morphism of `V` and so exhibits it as a morphism over `A`.

## Main results

* `AlgebraicGeometry.Space.chartRelocalizedBaseTwoIso`: the 2-compatibility of the conjugated
  relocalized morphism with the composite structure morphisms to `A`.

## Implementation notes

The construction is the 2-isomorphism calculus of [Stacks Project, Tag 03G2] part (3) and
nothing else: two instances of `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`
fuse each pair of structure morphisms, two associators move the brackets, and
`AlgebraicGeometry.Space.twoIsoSmallEtaleRestrictionRingedToposHom` converts between the two
presentations of the morphism of ringed topoi of an étale morphism, which is what lets the
chart morphisms of `AlgebraicGeometry.Space.chartRelocalizedRestrictionTwoIso` — stated with
restriction as their inverse image — be fused with the structure morphisms.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (T : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (s : smallEtaleChartSheaf B S hS X T ⟶
      ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y V))

/-- **The chartwise comparison square with both chart morphisms presented by Stacks 03G8.**

This is `AlgebraicGeometry.Space.chartRelocalizedRestrictionTwoIso` with the two restriction
presentations of the chart morphisms replaced by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, which is the presentation that fuses with a
structure morphism. -/
noncomputable def chartRelocalizedChartTwoIso :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V))
        (chartRelocalized B S hS X Y ψ T V s))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X T))) :=
  (RingedToposHom.TwoIso.whiskerLeft (chartRelocalized B S hS X Y ψ T V s)
      (twoIsoSmallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V))).trans
    ((chartRelocalizedRestrictionTwoIso B S hS X Y ψ T V s).trans
      (RingedToposHom.TwoIso.whiskerRight
        (twoIsoSmallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS X T)
          (isEtale_chartToSpace B S hS X T)).symm ψ))

/-- **The conjugated relocalized morphism is 2-compatible with the structure morphisms to the
base.**  If `ψ` is 2-compatible with `pX : X ⟶ A` and `pY : Y ⟶ A`, then the conjugated
relocalized morphism `ρ` of [Stacks Project, Tag 04J8] attached to a section
`s : h_T ⟶ ψ⁻¹h_V` is 2-compatible with the composite structure morphisms `T ⟶ X ⟶ A` and
`V ⟶ Y ⟶ A`.

This is the hypothesis in the shape the recovery of a morphism *over the base* needs: the
morphism of schemes that [Stacks Project, Tag 04I6] produces from `ρ` is absolute, and this
square is what pins its composite with the structure morphism of the chart of `Y` to the
structure morphism of the chart of `X`. -/
noncomputable def chartRelocalizedBaseTwoIso {A : AlgebraicSpaces B S hS}
    (pX : X ⟶ A) (pY : Y ⟶ A)
    (hc : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS pY) ψ)
      (smallEtaleRingedToposHom B S hS pX)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V ≫ pY))
        (chartRelocalized B S hS X Y ψ T V s))
      (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X T ≫ pX)) :=
  (RingedToposHom.TwoIso.whiskerLeft (chartRelocalized B S hS X Y ψ T V s)
      (smallEtaleRingedToposHom_compTwoIso B S hS
        (chartToSpace B S hS Y V) pY).symm).trans
    ((RingedToposHom.TwoIso.associator (chartRelocalized B S hS X Y ψ T V s)
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V))
        (smallEtaleRingedToposHom B S hS pY)).symm.trans
      ((RingedToposHom.TwoIso.whiskerRight
          (chartRelocalizedChartTwoIso B S hS X Y ψ T V s)
          (smallEtaleRingedToposHom B S hS pY)).trans
        ((RingedToposHom.TwoIso.associator
            (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X T)) ψ
            (smallEtaleRingedToposHom B S hS pY)).trans
          ((RingedToposHom.TwoIso.whiskerLeft
              (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X T)) hc).trans
            (smallEtaleRingedToposHom_compTwoIso B S hS
              (chartToSpace B S hS X T) pX)))))

end AlgebraicGeometry.Space

end
