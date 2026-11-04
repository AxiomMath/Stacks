module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The comparison of Stacks 03LU on chart sections

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`, and let `M` be an `𝒪_Z`-module.  The comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU identifies `f^*g^*M` with
`(f ≫ g)^*M`.  This file computes it on the canonical sections
`AlgebraicGeometry.Space.modulePullbackChartSection`: over a chart diagram over `f ≫ g` which
factors as a chart diagram over `f` followed by one over `g`, the comparison carries the chart
section of the chart section to the chart section of the composite diagram.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_modulePullbackCompIso_inv`: the chartwise
  transpose of the inverse comparison is the composite, in the sense of
  `AlgebraicGeometry.Space.ModuleFMap.compOfIso`, of the chartwise transposes of the two
  identities.
* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_chartSection`: **the chart formula of the
  inverse comparison of Stacks 03LU.**  The forward direction is
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_chartSection_comp`.

## Implementation notes

The proof never unfolds the comparison.  Both sides of the transpose identity are images under
the chart correspondence of Stacks 03G4 of morphisms `M ⟶ (f ≫ g)_*(f^*g^*M)`, and those two
morphisms are the unit of the composite adjunction, once through
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` and once by the
definition of the composite adjunction.  The chart formula is then
`AlgebraicGeometry.Space.ModuleFMap.compOfIso_app`, whose hypothesis on the comparison of direct
images is `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- The first transpose of the identity of an inverse image is the unit of the adjunction. -/
theorem moduleFMapHom_modulePullbackHomFMap_id {X' Y' : AlgebraicSpaces B S hS} (h : X' ⟶ Y')
    (N : Modules.{u, u} B S hS Y'.1 Y'.2) :
    moduleFMapHom B S hS h ((modulePullback B S hS h).obj N) N
        (modulePullbackHomFMap B S hS h N _ (𝟙 _)) =
      (modulePullbackAdjunction B S hS h).unit.app N :=
  ((modulePushforwardHomEquiv B S hS h _ N).symm_apply_apply _).trans
    (Adjunction.homEquiv_id _ N)

/-- The first transpose of the inverse comparison of Stacks 03LU is the unit of the composite
adjunction, written out: the unit along `g`, the direct image along `g` of the unit along `f`,
and the comparison of direct images. -/
theorem homEquiv_modulePullbackCompIso_inv :
    (modulePullbackAdjunction B S hS (f ≫ g)).homEquiv M _
        ((modulePullbackCompIso B S hS f g).inv.app M) =
      (modulePullbackAdjunction B S hS g).unit.app M ≫
        (modulePushforward B S hS g).map
          ((modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj M)) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj M) := by
  have h := homEquiv_modulePullbackCompIso_inv_app_comp B S hS f g M _ (𝟙 _)
  have e : ((modulePullbackAdjunction B S hS f).homEquiv ((modulePullback B S hS g).obj M)
      ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj M))
        (𝟙 ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj M)) =
      (modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj M) :=
    Adjunction.homEquiv_id _ _
  rw [Category.comp_id, e, Adjunction.homEquiv_unit (modulePullbackAdjunction B S hS g),
    Category.assoc] at h
  exact h

/-- **The chartwise transpose of the inverse comparison of Stacks 03LU** is the composite of the
chartwise transposes of the identities of `g^*M` and of `f^*g^*M`. -/
theorem modulePullbackHomFMap_modulePullbackCompIso_inv :
    modulePullbackHomFMap B S hS (f ≫ g) M _ ((modulePullbackCompIso B S hS f g).inv.app M) =
      ModuleFMap.compOfIso B S hS f g _ _ M
        (modulePullbackHomFMap B S hS g M _ (𝟙 _))
        (modulePullbackHomFMap B S hS f ((modulePullback B S hS g).obj M) _ (𝟙 _))
        (modulePushforwardCompIso B S hS f g) := by
  refine congrArg (modulePushforwardHomFMap B S hS (f ≫ g) _ M) ?_
  refine (homEquiv_modulePullbackCompIso_inv B S hS f g M).trans ?_
  refine Eq.trans ?_ (moduleFMapCompHom_eq B S hS f g _ _ M _ _ _).symm
  rw [moduleFMapHom_modulePullbackHomFMap_id B S hS g M]
  exact congrArg (fun t ↦ (modulePullbackAdjunction B S hS g).unit.app M ≫
      (modulePushforward B S hS g).map t ≫ (modulePushforwardCompIso B S hS f g).hom.app
        ((modulePullback B S hS g ⋙ modulePullback B S hS f).obj M))
    (moduleFMapHom_modulePullbackHomFMap_id B S hS f ((modulePullback B S hS g).obj M)).symm

variable {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- **The chart formula of the comparison of Stacks 03LU, inverse direction.**  Over a chart
diagram over `f ≫ g` which factors through an étale chart `V` of `Y`, the inverse comparison
carries the chart section of `s` to the chart section along `f` of the chart section along `g`
of `s`. -/
theorem modulePullbackCompIso_inv_chartSection (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).inv.app M).val.app (op U)
        (modulePullbackChartSection B S hS (f ≫ g) M
          (ChartDiagram.comp B S hS f g a b ha hb) s) =
      modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
        (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s) := by
  have h := ModuleFMap.compOfIso_app B S hS f g a b ha hb _ _ M
    (modulePullbackHomFMap B S hS g M _ (𝟙 _))
    (modulePullbackHomFMap B S hS f ((modulePullback B S hS g).obj M) _ (𝟙 _))
    (modulePushforwardCompIso B S hS f g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g _) s
  have h1 := modulePullbackHomFMap_app B S hS (f ≫ g) M _
    ((modulePullbackCompIso B S hS f g).inv.app M) (ChartDiagram.comp B S hS f g a b ha hb) s
  have h2 := modulePullbackHomFMap_app B S hS g M _ (𝟙 _) ⟨V, W, b, hb⟩ s
  have h3 := modulePullbackHomFMap_app B S hS f ((modulePullback B S hS g).obj M) _ (𝟙 _)
    ⟨U, V, a, ha⟩ (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)
  have e1 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (f ≫ g) M
    (ChartDiagram.comp B S hS f g a b ha hb) s
  have e2 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s
  have e3 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f
    ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
    (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)
  rw [modulePullbackHomFMap_modulePullbackCompIso_inv] at h1
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  refine h1.symm.trans (h.trans ?_)
  rw [h2]
  exact h3

end AlgebraicGeometry.Space

end
