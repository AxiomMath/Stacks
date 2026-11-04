module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# Covering a chart of the target by charts whose base change along an affine morphism is affine

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, affine in the sense of Stacks 03WF. Every étale scheme chart `V` of `Y`
carries a covering presieve whose members `W` are affine charts and whose base changes
`W ×_Y X` along `f` are affine charts of `X`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.affineChartPresieve`: the presieve on an étale chart
  consisting of every arrow whose source chart has affine underlying scheme.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.generate_affineChartPresieve_mem`: that presieve generates
  a covering sieve: every étale chart is covered by its affine charts.
* `AlgebraicGeometry.Space.exists_presieve_isAffine_smallBaseChange`: for an affine morphism
  `f : X ⟶ Y` and a chart `V` of `Y`, a covering presieve of `V` whose members are affine and
  have affine base change along `f`.
* `AlgebraicGeometry.Space.isAffineHom_smallBaseChangeChartMap` and
  `AlgebraicGeometry.Space.relativelyRepresentable_smallBaseChangeChartMap`: the base change
  `f' : V ×_Y X ⟶ V` of an affine `f` to a chart of `Y` is again affine, and hence representable.
* `AlgebraicGeometry.Space.exists_presieve_isAffine_smallBaseChange_chartMap`: the same covering
  presieve statement for that base change `f'` in place of `f`.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Every étale chart is covered by its affine charts -/

/-- The presieve on an étale chart `V` of `F` consisting of every arrow into `V` whose source
chart has affine underlying scheme. -/
def SmallEtale.affineChartPresieve (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (V : SmallEtale B S hS F) : Presieve V :=
  fun {W} _ ↦ IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)

/-- Every étale chart of an algebraic space is covered by its affine charts: the presieve of
arrows with affine source generates a covering sieve. -/
theorem SmallEtale.generate_affineChartPresieve_mem (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (V : SmallEtale B S hS F) :
    Sieve.generate (SmallEtale.affineChartPresieve B S hS F V) ∈
      SmallEtale.topology B S hS F V := by
  obtain ⟨I, Y, a, hYaff, hmem, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F V
  refine GrothendieckTopology.superset_covering _ ?_ hmem
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun j ↦ ⟨Y j, 𝟙 _, a j, hYaff j, Category.id_comp _⟩

/-! ### Affine base change along an affine morphism -/

/-- Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over `S` which is affine in the
sense of Stacks 03WF, and let `V` be an étale scheme chart of `Y`.  Then `V` carries a covering
presieve each of whose members `W` is an affine chart of `Y` and whose base change `W ×_Y X`
along `f` — the chart of `X` formed by `AlgebraicGeometry.Space.smallBaseChange` as in
Stacks 03G2, part (4) — is an affine chart of `X`. -/
theorem exists_presieve_isAffine_smallBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    ∃ R : Presieve V, Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 V ∧
      ∀ ⦃W : SmallEtale B S hS Y.1⦄ (g : W ⟶ V), R g →
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
          IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
            ((smallBaseChange B S hS f hf).obj W)) :=
  ⟨SmallEtale.affineChartPresieve B S hS Y.1 V,
    SmallEtale.generate_affineChartPresieve_mem B S hS Y.1 V,
    fun _ _ hW ↦ ⟨hW, isAffine_smallBaseChange_obj B S hS f hf haff _ hW⟩⟩

/-! ### The base change of `f` to a chart of `Y` -/

/-- The base change `f' : V ×_Y X ⟶ V` of an affine morphism
`f : X ⟶ Y` of algebraic spaces to an étale scheme chart `V` of `Y` is again affine. -/
theorem isAffineHom_smallBaseChangeChartMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    IsAffineHom B S hS (smallBaseChangeChartMap B S hS f hf V).hom :=
  IsAffineHom.of_isPullback (hf.isPullback V.1.hom) haff

/-- The base change `f' : V ×_Y X ⟶ V` of an affine morphism of algebraic spaces to an étale
scheme chart of the target is representable. -/
theorem relativelyRepresentable_smallBaseChangeChartMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    yoneda.relativelyRepresentable (smallBaseChangeChartMap B S hS f hf V).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _
    (isAffineHom_smallBaseChangeChartMap B S hS f hf haff V)

/-- For an affine `f : X ⟶ Y`, an étale chart `V` of `Y` and an étale chart `V'` of the chart space
of `V`, the chart `V'` carries a covering presieve whose members are affine charts of that chart
space and whose base changes along `f' : V ×_Y X ⟶ V` are affine charts of the chart space of
`V ×_Y X`. -/
theorem exists_presieve_isAffine_smallBaseChange_chartMap {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : SmallEtale B S hS Y.1)
    (V' : SmallEtale B S hS (chartSpace B S hS Y V).1) :
    ∃ R : Presieve V',
      Sieve.generate R ∈ SmallEtale.topology B S hS (chartSpace B S hS Y V).1 V' ∧
        ∀ ⦃W : SmallEtale B S hS (chartSpace B S hS Y V).1⦄ (g : W ⟶ V'), R g →
          IsAffine ((SmallEtale.toOver B S hS (chartSpace B S hS Y V).1 ⋙
              BigFppfOver.toScheme B S hS).obj W) ∧
            IsAffine ((SmallEtale.toOver B S hS
                (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).1 ⋙
                BigFppfOver.toScheme B S hS).obj
              ((smallBaseChange B S hS (smallBaseChangeChartMap B S hS f hf V)
                (relativelyRepresentable_smallBaseChangeChartMap B S hS f hf haff V)).obj W)) :=
  exists_presieve_isAffine_smallBaseChange B S hS (smallBaseChangeChartMap B S hS f hf V)
    (relativelyRepresentable_smallBaseChangeChartMap B S hS f hf haff V)
    (isAffineHom_smallBaseChangeChartMap B S hS f hf haff V) V'

end AlgebraicGeometry.Space

end
