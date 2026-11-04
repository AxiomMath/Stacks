module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# The comparison of `g⁻¹h_V` with the chart maps over a morphism of algebraic spaces

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces `X` and `Y`
over a base `S` which is a terminal scheme (in Stacks 04KL, `S = Spec ℤ`).  For an affine
étale chart `V` of `Y`, a section `s` over an étale chart `U` of `X` of `g⁻¹h_V` gives a
morphism of schemes `f_s : U ⟶ V` (`AlgebraicGeometry.Space.chartSchemeHom`), which is a
morphism of the big fppf site of `S` because `S` is terminal.  When a morphism of algebraic
spaces `f : X ⟶ Y` is compatible with all the `f_s`, sending `s` to `f_s` is a map of
presheaves from `g⁻¹h_V` to the presheaf `AlgebraicGeometry.Space.chartFiber` of chart maps
over `f` with target `V`.  This is the comparison through which the proof of Stacks 04KL
identifies `(g, g♯)` with `(f_small, f♯)`.

## Main definitions

* `AlgebraicGeometry.Space.chartOverHom`: `f_s` as a morphism of the big fppf site.
* `AlgebraicGeometry.Space.IsChartCompatible`: the compatibility of `f` with every `f_s`.
* `AlgebraicGeometry.Space.invRepComparison`: the map of presheaves `g⁻¹h_V ⟶ chartFiber f V`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (hS₀ : IsTerminal S)
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

attribute [local instance] smallEtaleTopology_subcanonical

/-- `f_s`, as a morphism of the big fppf site of the terminal scheme `S`. -/
def chartOverHom (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    U.obj.left ⟶ V.obj.left :=
  BigFppfOver.homOfCompEq B S hS (chartSchemeHom g V U s) (hS₀.hom_ext _ _)

@[simp]
theorem toScheme_map_chartOverHom (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (BigFppfOver.toScheme B S hS).map (chartOverHom hS₀ g V U s) = chartSchemeHom g V U s :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

/-- `f_s` as a morphism of the big fppf site is natural in the chart of the source. -/
theorem chartOverHom_restrict (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) (s : (invRep g V).obj.obj (op U)) :
    chartOverHom hS₀ g V U' ((invRep g V).obj.map i.op s) =
      i.hom.left ≫ chartOverHom hS₀ g V U s := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_chartOverHom, toScheme_map_chartOverHom,
    chartSchemeHom_restrict]

/-- `f_s` as a morphism of the big fppf site is natural in the chart of the target. -/
theorem chartOverHom_map (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V)] [IsAffine (chartSch V')]
    (c : V' ⟶ V) (s' : (invRep g V').obj.obj (op U)) :
    chartOverHom hS₀ g V U ((g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s') =
      chartOverHom hS₀ g V' U s' ≫ c.hom.left := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_chartOverHom, toScheme_map_chartOverHom,
    chartSchemeHom_map]

/-- A morphism `f : X ⟶ Y` of algebraic spaces is *compatible with the charts of `g`* when for
every affine étale chart `V` of `Y`, every étale chart `U` of `X` and every section `s` over
`U` of `g⁻¹h_V`, the square `U ⟶ X ⟶ Y`, `U ⟶ V ⟶ Y` with `U ⟶ V` equal to `f_s` commutes. -/
def IsChartCompatible (f : X ⟶ Y) : Prop :=
  ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)),
    U.obj.hom ≫ f.hom = yoneda.map (chartOverHom hS₀ g V U s) ≫ V.obj.hom

variable {hS₀ g}

/-- **The comparison `g⁻¹h_V ⟶ chartFiber f V`** for a morphism `f` compatible with the charts
of `g` and an affine étale chart `V` of `Y`: a section `s` goes to `f_s`. -/
def invRepComparison {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f) (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] :
    (invRep g V).obj ⟶ (chartFiber B S hS f V).toFunctor where
  app U := ↾fun s ↦ ⟨chartOverHom hS₀ g V U.unop s, hf V U.unop s⟩
  naturality U U' i := by
    ext s
    apply Subtype.ext
    exact chartOverHom_restrict hS₀ g V i.unop s

@[simp]
theorem invRepComparison_app_val {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    ((invRepComparison hf V).app (op U) s).val = chartOverHom hS₀ g V U s :=
  rfl

end AlgebraicGeometry.Space
