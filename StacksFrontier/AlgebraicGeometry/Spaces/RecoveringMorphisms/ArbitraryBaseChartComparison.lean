module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartComparison

/-!
# The chart comparison of Stacks 04KL over an arbitrary base scheme

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces `X` and `Y`
over a base scheme `S`.  For an affine étale chart `V` of `Y`, a section `s` over an étale chart
`U` of `X` of `g⁻¹h_V` gives a morphism of schemes `f_s : U ⟶ V`
(`AlgebraicGeometry.Space.chartSchemeHom`).  To read `f_s` as a morphism of the big fppf site of
`S` it has to commute with the structure morphisms of the two charts to `S`; that condition on
`(g, g♯)` is `AlgebraicGeometry.Space.IsChartOverBase`, and it is automatic when `S` is terminal
(`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal`), which is the case of Stacks 04KL,
`S = Spec ℤ`.

The proof of Stacks 04KL in `StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/` is
stated over a terminal base `S` (a hypothesis `hS₀ : IsTerminal S`), and terminality is used
there at exactly one point: to know that `f_s` is over `S`
(`AlgebraicGeometry.Space.chartOverHom`).  This file and its siblings `ArbitraryBaseTwoIso`,
`ArbitraryBaseStalk` and `ArbitraryBaseMain` restate the steps of that proof whose statements
mention the chart morphisms over the base, carrying `IsChartOverBase g` in place of
`IsTerminal S`; every step which does not mention them is reused as it stands.  The restated
declarations live in the namespace `AlgebraicGeometry.Space.OverBase`, under the names of the
steps they generalize.

## Main definitions

* `AlgebraicGeometry.Space.IsChartOverBase`: the condition that every `f_s` commute with the
  structure morphisms of the charts to the base scheme.
* `AlgebraicGeometry.Space.OverBase.chartOverHom`: `f_s` as a morphism of the big fppf site.
* `AlgebraicGeometry.Space.OverBase.IsChartCompatible`: the compatibility of a morphism
  `f : X ⟶ Y` with every `f_s`.
* `AlgebraicGeometry.Space.OverBase.invRepComparison`: the map of presheaves
  `g⁻¹h_V ⟶ chartFiber f V`.

## Main results

* `AlgebraicGeometry.Space.isChartOverBase_of_isTerminal`: over a terminal base scheme every
  morphism of the small étale ringed topoi has its chart morphisms over the base.

## Implementation notes

The condition `AlgebraicGeometry.Space.IsChartOverBase` is a proposition, and
`AlgebraicGeometry.BigFppfOver.homOfCompEq` consumes it as a proof of an equality of morphisms of
schemes, so `AlgebraicGeometry.Space.OverBase.chartOverHom` does not depend on which proof it is
given: at the proof supplied by `AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` it is
`AlgebraicGeometry.Space.chartOverHom` (`AlgebraicGeometry.Space.OverBase.chartOverHom_eq`), and
compatibility with the charts is `AlgebraicGeometry.Space.IsChartCompatible`
(`AlgebraicGeometry.Space.OverBase.isChartCompatible_iff`).

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

/-- **The chart morphisms of `(g, g♯)` are over the base.** Every morphism of schemes
`f_s : U ⟶ V` attached to an affine étale chart `V` of `Y`, an étale chart `U` of `X` and a
section `s` over `U` of `g⁻¹h_V` commutes with the structure morphisms of the two charts to the
base scheme `S`. -/
def IsChartOverBase
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)) :
    Prop :=
  ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)),
    chartSchemeHom g V U s ≫ B.inclusion.map V.obj.left.hom =
      B.inclusion.map U.obj.left.hom

/-- **Over a terminal base scheme the chart morphisms are over the base for free**, there being
only one morphism to `S` out of any scheme. -/
theorem isChartOverBase_of_isTerminal (hS₀ : IsTerminal S)
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)) :
    IsChartOverBase g :=
  fun _ _ _ _ ↦ hS₀.hom_ext _ _

namespace OverBase

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  (hb : IsChartOverBase g)

/-- `f_s`, as a morphism of the big fppf site of `S`. -/
def chartOverHom (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    U.obj.left ⟶ V.obj.left :=
  BigFppfOver.homOfCompEq B S hS (chartSchemeHom g V U s) (hb V U s)

/-- The underlying morphism of schemes of `chartOverHom hb V U s` is `f_s`. -/
@[simp]
theorem toScheme_map_chartOverHom (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (BigFppfOver.toScheme B S hS).map (chartOverHom hb V U s) = chartSchemeHom g V U s :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

/-- `f_s` as a morphism of the big fppf site is natural in the chart of the source. -/
theorem chartOverHom_restrict (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) (s : (invRep g V).obj.obj (op U)) :
    chartOverHom hb V U' ((invRep g V).obj.map i.op s) =
      i.hom.left ≫ chartOverHom hb V U s := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_chartOverHom, toScheme_map_chartOverHom,
    chartSchemeHom_restrict]

/-- `f_s` as a morphism of the big fppf site is natural in the chart of the target. -/
theorem chartOverHom_map (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V)] [IsAffine (chartSch V')]
    (c : V' ⟶ V) (s' : (invRep g V').obj.obj (op U)) :
    chartOverHom hb V U ((g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s') =
      chartOverHom hb V' U s' ≫ c.hom.left := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_chartOverHom, toScheme_map_chartOverHom,
    chartSchemeHom_map]

/-- A morphism `f : X ⟶ Y` of algebraic spaces is *compatible with the charts of `g`* when for
every affine étale chart `V` of `Y`, every étale chart `U` of `X` and every section `s` over
`U` of `g⁻¹h_V`, the square `U ⟶ X ⟶ Y`, `U ⟶ V ⟶ Y` with `U ⟶ V` equal to `f_s` commutes. -/
def IsChartCompatible (f : X ⟶ Y) : Prop :=
  ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)),
    U.obj.hom ≫ f.hom = yoneda.map (chartOverHom hb V U s) ≫ V.obj.hom

variable {hb}

/-- **The comparison `g⁻¹h_V ⟶ chartFiber f V`** for a morphism `f` compatible with the charts
of `g` and an affine étale chart `V` of `Y`: a section `s` goes to `f_s`. -/
def invRepComparison {f : X ⟶ Y} (hf : IsChartCompatible hb f) (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] :
    (invRep g V).obj ⟶ (chartFiber B S hS f V).toFunctor where
  app U := ↾fun s ↦ ⟨chartOverHom hb V U.unop s, hf V U.unop s⟩
  naturality U U' i := by
    ext s
    exact Subtype.ext (chartOverHom_restrict hb V i.unop s)

/-- The comparison `invRepComparison hf V` sends a section `s` over `U` to `f_s`. -/
@[simp]
theorem invRepComparison_app_val {f : X ⟶ Y} (hf : IsChartCompatible hb f)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    ((invRepComparison hf V).app (op U) s).val = chartOverHom hb V U s :=
  rfl

/-- Over a terminal base scheme, `f_s` as a morphism of the big fppf site is the one of the proof
of Stacks 04KL. -/
theorem chartOverHom_eq (hS₀ : IsTerminal S)
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    chartOverHom (isChartOverBase_of_isTerminal hS₀ g) V U s = Space.chartOverHom hS₀ g V U s :=
  rfl

/-- Over a terminal base scheme, compatibility with the charts of `g` is the compatibility of the
proof of Stacks 04KL. -/
theorem isChartCompatible_iff (hS₀ : IsTerminal S)
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (f : X ⟶ Y) :
    IsChartCompatible (isChartOverBase_of_isTerminal hS₀ g) f ↔ Space.IsChartCompatible hS₀ g f :=
  Iff.rfl

end OverBase

end AlgebraicGeometry.Space
