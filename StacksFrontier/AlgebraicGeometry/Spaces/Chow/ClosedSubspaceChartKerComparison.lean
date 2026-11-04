module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartMultiplicity
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeChartStalk

/-!
# The chart base change of a closed subspace is the subscheme its chart ideal sheaf cuts out

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site, let `Z ⊆ X` be a
closed subspace and let `V` be an étale scheme chart of `X`.  Two closed subschemes of the chart
scheme have been built out of `Z`:

* the chart base change `V ×_X Z`, which is an étale scheme chart of `Z` and whose projection
  `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartProj` to `V` is a closed immersion of
  schemes;
* the closed subscheme cut out by the quasi-coherent ideal sheaf
  `AlgebraicGeometry.Space.chartKer` of the chart, the kernel of that same base change.

**They are the same closed subscheme of the chart.**  The projection of the chart base change is
*literally* the morphism of schemes whose kernel `chartKer` is
(`AlgebraicGeometry.Space.ker_closedSubspaceBaseChangeChartProj`), so the only difference between
the two is the passage from a closed immersion to the closed subscheme its kernel cuts out, and
that passage is an isomorphism over the chart.  Consequently the multiplicity of Stacks 02QU of a
component is the same whichever of the two presentations it is read on.

The use is a coefficient comparison at a prime divisor.  The multiplicity `m_{W, Z}` of the
algebraic-space theory is read on the chart base change, by
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity`; the order of
vanishing of a local equation is read on the closed subscheme of an ideal sheaf, by
`Stacks.Chow.ord_eq_componentMultiplicity`, whose local-equation hypothesis the chart ideal sheaf
of a zero scheme satisfies by
`AlgebraicGeometry.Space.stalk_chartKer_zeroScheme_eq_span_germ`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartIsoChartKer`: the isomorphism, over the
  chart, of the chart base change `V ×_X Z` with the closed subscheme cut out by the chart ideal
  sheaf of `Z`.

## Main results

* `AlgebraicGeometry.Space.ker_closedSubspaceBaseChangeChartProj`: the kernel of the projection
  of the chart base change is the chart ideal sheaf.
* `AlgebraicGeometry.Space.componentMultiplicity_closedSubspaceBaseChangeChartProj_eq_chartKer`:
  **the two presentations have the same multiplicities**, at corresponding generic points.
* `AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity_chartKer`: the
  multiplicity `m_{W, Z}` of Stacks 0EE9 read on the closed subscheme of the chart ideal sheaf.
* `AlgebraicGeometry.Space.ord_eq_componentMultiplicity_closedSubspaceBaseChangeChartProj`: the
  order of vanishing of a local equation for `Z` at a codimension-one point of the chart is the
  multiplicity of that component of the chart base change.
* `AlgebraicGeometry.Space.ord_eq_closedSubspaceMultiplicity_zeroScheme`: for the zero scheme of
  a global section of an invertible module the two previous statements compose, with the local
  equation supplied by Stacks 0846.

## Implementation notes

`AlgebraicGeometry.Space.ker_closedSubspaceBaseChangeChartProj` holds by `rfl`.  Both sides are
built from the second projection of the representability datum of the inclusion of the closed
subspace: `AlgebraicGeometry.Space.chartKer` from the datum carried by the second component of
`AlgebraicGeometry.Space.ClosedSubspaces`, and the chart base change from the one carried by
`AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceHom`.  Those are two proofs of one
proposition, hence definitionally equal, so the two morphisms of schemes are the same morphism.
The mathematical content of the comparison is therefore only the universal property of a closed
immersion with a prescribed kernel, `AlgebraicGeometry.IsClosedImmersion.lift` together with
`AlgebraicGeometry.IsClosedImmersion.isIso_lift`.

The generic points of the two presentations are matched by `Stacks.Chow.genericPointsIso`, and
the multiplicity is carried across by `Stacks.Chow.componentMultiplicity_eq_of_iso`.

`AlgebraicGeometry.Space.ord_eq_componentMultiplicity_closedSubspaceBaseChangeChartProj` and
`AlgebraicGeometry.Space.ord_eq_closedSubspaceMultiplicity_zeroScheme` carry
`[AlgebraicGeometry.IsIntegral (chartScheme V)]` as an instance hypothesis, as
`Stacks.Chow.ord_eq_componentMultiplicity` does for its ambient scheme.  **It is a hypothesis,
not a consequence**: an étale chart of an integral algebraic space need not be integral, an étale
chart being free to be disconnected.  The development carries it the same way at
`AlgebraicGeometry.Space.PrimeDivisor.lift_chartMeromorphicFunctionFieldEquiv_eq` and
`AlgebraicGeometry.Space.chartMeromorphicToEtaleFractionRing`.

The point of the chart at which the order of vanishing is taken is presented as a variable `v`
together with the identity `hv` exhibiting it as the image of the generic point `ξ`, rather than
as the image itself: the local equation, its open neighbourhood and the codimension condition are
all conditions at that one point, and presenting it as a variable keeps them from having to be
transported one by one across the isomorphism of the two presentations.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.Chow

/-- **The multiplicity of a component of a closed subscheme depends only on the morphism.**  Two
closed immersions that are equal as morphisms have the same multiplicities, whichever instances
witness that they are closed immersions. -/
theorem componentMultiplicity_congr {X Z : AlgebraicGeometry.Scheme.{u}} {i j : Z ⟶ X}
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j] (h : i = j)
    (ξ : genericPoints Z) :
    componentMultiplicity i ξ = componentMultiplicity j ξ := by
  subst h; rfl

end Stacks.Chow

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two closed subschemes of the chart -/

/-- **The projection of the chart base change of a closed subspace is the base changed closed
immersion of `AlgebraicGeometry.Space.chartBaseChangeHom`.**  Both are the image under
`AlgebraicGeometry.BigFppfOver.toScheme` of the second projection of the representability datum
of the inclusion of the closed subspace. -/
theorem closedSubspaceBaseChangeChartProj_eq_chartBaseChangeHom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1) :
    closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V =
      chartBaseChangeHom B S hS X Z V :=
  rfl

/-- **The kernel of the projection of the chart base change is the chart ideal sheaf of the
closed subspace.**  This is the identification of the two closed subschemes of the chart, read on
ideal sheaves. -/
theorem ker_closedSubspaceBaseChangeChartProj (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1) :
    (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V).ker =
      chartKer B S hS X Z V.obj.hom :=
  rfl

/-- The closed subscheme cut out by the chart ideal sheaf has that ideal sheaf as the kernel of
its inclusion, which is the kernel of the projection of the chart base change. -/
theorem ker_subschemeι_chartKer_eq (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1) :
    (chartKer B S hS X Z V.obj.hom).subschemeι.ker =
      (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V).ker :=
  (Scheme.IdealSheafData.ker_subschemeι _).trans
    (ker_closedSubspaceBaseChangeChartProj B S hS X Z V).symm

/-- **The chart base change `V ×_X Z` of a closed subspace is the closed subscheme cut out by its
chart ideal sheaf**, as a closed subscheme of the chart: the two closed immersions into the chart
scheme have the same kernel, so a closed immersion with a prescribed kernel identifies their
sources. -/
def closedSubspaceBaseChangeChartIsoChartKer (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1) :
    chartScheme (closedSubspaceBaseChangeChart B S hS X.2 Z.1 Z.2 V) ≅
      (chartKer B S hS X Z V.obj.hom).subscheme :=
  haveI := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
  haveI := IsClosedImmersion.isIso_lift (chartKer B S hS X Z V.obj.hom).subschemeι
    (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V)
    (ker_subschemeι_chartKer_eq B S hS X Z V)
  asIso (IsClosedImmersion.lift (chartKer B S hS X Z V.obj.hom).subschemeι
    (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V)
    (ker_subschemeι_chartKer_eq B S hS X Z V).le)

/-- The identification of the chart base change with the closed subscheme of the chart ideal
sheaf is an identification *over the chart*. -/
theorem closedSubspaceBaseChangeChartIsoChartKer_hom_subschemeι (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1) :
    (closedSubspaceBaseChangeChartIsoChartKer B S hS X Z V).hom ≫
        (chartKer B S hS X Z V.obj.hom).subschemeι =
      closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V :=
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
  IsClosedImmersion.lift_fac _ _ _

/-- The identification of the two closed subschemes of the chart carries a generic point of the
chart base change to a point with the same image in the chart. -/
theorem subschemeι_genericPointsIso_closedSubspaceBaseChangeChartIsoChartKer
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (ξ : genericPoints (chartScheme (closedSubspaceBaseChangeChart B S hS X.2 Z.1 Z.2 V))) :
    (chartKer B S hS X Z V.obj.hom).subschemeι
        (Stacks.Chow.genericPointsIso
          (closedSubspaceBaseChangeChartIsoChartKer B S hS X Z V) ξ).1 =
      closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V ξ.1 := by
  conv_rhs =>
    rw [← closedSubspaceBaseChangeChartIsoChartKer_hom_subschemeι B S hS X Z V]
  rfl

/-! ### The multiplicities of the two closed subschemes -/

/-- **The multiplicity of Stacks 02QU is the same on the two presentations of the closed
subscheme of the chart.**  The multiplicity of a component of the chart base change `V ×_X Z`,
read through its projection to the chart, is the multiplicity of the corresponding component of
the closed subscheme cut out by the chart ideal sheaf of `Z`. -/
theorem componentMultiplicity_closedSubspaceBaseChangeChartProj_eq_chartKer
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    (ξ : genericPoints (chartScheme (closedSubspaceBaseChangeChart B S hS X.2 Z.1 Z.2 V))) :
    haveI := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
    Stacks.Chow.componentMultiplicity
        (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V) ξ =
      Stacks.Chow.componentMultiplicity (chartKer B S hS X Z V.obj.hom).subschemeι
        (Stacks.Chow.genericPointsIso
          (closedSubspaceBaseChangeChartIsoChartKer B S hS X Z V) ξ) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
  rw [← Stacks.Chow.componentMultiplicity_eq_of_iso (chartKer B S hS X Z V.obj.hom).subschemeι
    (closedSubspaceBaseChangeChartIsoChartKer B S hS X Z V) ξ]
  exact Stacks.Chow.componentMultiplicity_congr
    (closedSubspaceBaseChangeChartIsoChartKer_hom_subschemeι B S hS X Z V).symm ξ

/-- **The multiplicity `m_{W, Z}` of Stacks 0EE9 part (1), read on the closed subscheme cut out
by the chart ideal sheaf.**  This is
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity` transported to the
presentation of the closed subscheme of the chart that the multiplicity theory of schemes
consumes. -/
theorem closedSubspaceMultiplicity_eq_componentMultiplicity_chartKer
    (C : BaseSpaceDimensionSituation.{u})
    (X : AlgebraicSpaces C.site C.base C.base_mem)
    (Z : ClosedSubspaces C.site C.base C.base_mem X.1)
    (V : SmallEtale C.site C.base C.base_mem X.1)
    (W : IntegralClosedSubspace C.site C.base C.base_mem Z.1.toFunctor)
    (ξ : genericPoints (chartScheme
      (closedSubspaceBaseChangeChart C.site C.base C.base_mem X.2 Z.1 Z.2 V)))
    (hξ : chartSchemeToPoints C.site C.base C.base_mem Z.1.toFunctor
        (closedSubspaceBaseChangeChart C.site C.base C.base_mem X.2 Z.1 Z.2 V) ξ.1 =
      W.ambientGenericPoint C.site C.base C.base_mem) :
    closedSubspaceMultiplicity C Z.1 Z.2 W =
      Stacks.Chow.componentMultiplicity
        (chartKer C.site C.base C.base_mem X Z V.obj.hom).subschemeι
        (Stacks.Chow.genericPointsIso
          (closedSubspaceBaseChangeChartIsoChartKer C.site C.base C.base_mem X Z V) ξ) :=
  (closedSubspaceMultiplicity_eq_componentMultiplicity C X.2 Z.1 Z.2 V W ξ hξ).trans
    (componentMultiplicity_closedSubspaceBaseChangeChartProj_eq_chartKer
      C.site C.base C.base_mem X Z V ξ)

/-! ### The order of vanishing of a local equation on the chart -/

/-- **The order of vanishing of a local equation for a closed subspace at a codimension-one point
of a chart is the multiplicity of that component of the chart base change.**  Let `Z ⊆ X` be a
closed subspace, `V` an étale scheme chart of `X` whose chart scheme is integral and locally
Noetherian, `ξ` a generic point of the chart base change `V ×_X Z` lying over a point `v` of the
chart of codimension one, and `t` a regular function on an open neighbourhood of `v` generating
the stalk at `v` of the chart ideal sheaf of `Z`.  Then the order of vanishing at `v` of the
rational function `t` represents is the multiplicity of Stacks 02QU of that component of
`V ×_X Z ⊆ V`.

This is `Stacks.Chow.ord_eq_componentMultiplicity` read through the identification of the two
closed subschemes of the chart.  Integrality of the chart scheme is a hypothesis: an étale chart
of an integral algebraic space need not be integral. -/
theorem ord_eq_componentMultiplicity_closedSubspaceBaseChangeChartProj
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (V : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [AlgebraicGeometry.IsLocallyNoetherian (chartScheme V)]
    (ξ : genericPoints (chartScheme (closedSubspaceBaseChangeChart B S hS X.2 Z.1 Z.2 V)))
    (v : chartScheme V)
    (hv : closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V ξ.1 = v)
    (hco : Order.coheight v = 1) {O : (chartScheme V).Opens} [Nonempty O] (hvO : v ∈ O)
    (t : Γ(chartScheme V, O)) (ht : t ≠ 0)
    (hZt : AlgebraicGeometry.IdealSheafData.stalk (chartKer B S hS X Z V.obj.hom) v =
      Ideal.span {((chartScheme V).presheaf.germ O v hvO).hom t}) :
    haveI := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
    (chartScheme V).ord ((chartScheme V).germToFunctionField O t) v =
      Stacks.Chow.componentMultiplicity
        (closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V) ξ := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS X.2 Z.1 Z.2 V
  have : AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj V.obj.left) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (chartScheme V))
  have : AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj V.obj.left) :=
    inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian (chartScheme V))
  have hv' : (chartKer B S hS X Z V.obj.hom).subschemeι
      (Stacks.Chow.genericPointsIso
        (closedSubspaceBaseChangeChartIsoChartKer B S hS X Z V) ξ).1 = v :=
    (subschemeι_genericPointsIso_closedSubspaceBaseChangeChartIsoChartKer
      B S hS X Z V ξ).trans hv
  subst hv'
  rw [componentMultiplicity_closedSubspaceBaseChangeChartProj_eq_chartKer B S hS X Z V ξ]
  exact Stacks.Chow.ord_eq_componentMultiplicity (chartKer B S hS X Z V.obj.hom) _ hco hvO t ht
    hZt

/-- **The coefficient comparison on a chart, for the zero scheme of a global section of an
invertible module.**  Let `L` be an invertible `𝒪_X`-module, `s` a global section of `L`, and `V`
an affine étale chart of `X` on which `L` is free of rank one with generator `b` and coordinate
functional `l₀`, whose chart scheme is integral and locally Noetherian.  Let `W ⊆ Z(s)` be an
integral closed subspace and `ξ` a generic point of the chart `V ×_X Z(s)` of `Z(s)` lying over
the generic point of `W` and over a point `v` of the chart of codimension one.  Then the order of
vanishing at `v` of the rational function `l₀(s|_V)` is the multiplicity `m_{W, Z(s)}` of the
algebraic-space theory.

The local equation is Stacks 0846 part (4) read in the local rings of the chart
(`AlgebraicGeometry.Space.stalk_chartKer_zeroScheme_eq_span_germ`); the two readings of the
multiplicity are identified by
`AlgebraicGeometry.Space.ord_eq_componentMultiplicity_closedSubspaceBaseChangeChartProj` and
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity`. -/
theorem ord_eq_closedSubspaceMultiplicity_zeroScheme (C : BaseSpaceDimensionSituation.{u})
    (X : AlgebraicSpaces C.site C.base C.base_mem)
    (L : Modules.{u, u} C.site C.base C.base_mem X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings C.site C.base C.base_mem X)
      (structureRingSheaf C.site C.base C.base_mem X).property L)
    (s : L.sections) (V : SmallEtale C.site C.base C.base_mem X.1)
    [IsAffine (chartScheme V)] [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [AlgebraicGeometry.IsLocallyNoetherian (chartScheme V)]
    (b : ToType (L.val.obj (op V)))
    (l₀ : Module.Dual ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite C.site C.base C.base_mem X.1 X.2).O).obj.obj (op V))
      (L.val.obj (op V)))
    (hb : ∀ x, l₀ x • b = x)
    (W : IntegralClosedSubspace C.site C.base C.base_mem
      (zeroScheme C.site C.base C.base_mem X L s).1.toFunctor)
    (ξ : genericPoints (chartScheme (closedSubspaceBaseChangeChart C.site C.base C.base_mem X.2
      (zeroScheme C.site C.base C.base_mem X L s).1
      (zeroScheme C.site C.base C.base_mem X L s).2 V)))
    (hξ : chartSchemeToPoints C.site C.base C.base_mem
        (zeroScheme C.site C.base C.base_mem X L s).1.toFunctor
        (closedSubspaceBaseChangeChart C.site C.base C.base_mem X.2
          (zeroScheme C.site C.base C.base_mem X L s).1
          (zeroScheme C.site C.base C.base_mem X L s).2 V) ξ.1 =
      W.ambientGenericPoint C.site C.base C.base_mem)
    (v : chartScheme V)
    (hv : closedSubspaceBaseChangeChartProj C.site C.base C.base_mem X.2
      (zeroScheme C.site C.base C.base_mem X L s).1
      (zeroScheme C.site C.base C.base_mem X L s).2 V ξ.1 = v)
    (hco : Order.coheight v = 1)
    (ht : l₀ (s.eval (op V)) ≠ 0) :
    haveI : Nonempty ((⊤ : (chartScheme V).Opens) : Type u) := ⟨⟨v, trivial⟩⟩
    (chartScheme V).ord
        ((chartScheme V).germToFunctionField ⊤ (l₀ (s.eval (op V)))) v =
      closedSubspaceMultiplicity C (zeroScheme C.site C.base C.base_mem X L s).1
        (zeroScheme C.site C.base C.base_mem X L s).2 W := by
  have : Nonempty ((⊤ : (chartScheme V).Opens) : Type u) := ⟨⟨v, trivial⟩⟩
  rw [ord_eq_componentMultiplicity_closedSubspaceBaseChangeChartProj C.site C.base C.base_mem
      X (zeroScheme C.site C.base C.base_mem X L s) V ξ v hv hco (O := ⊤) trivial
      (l₀ (s.eval (op V))) ht
      (hv ▸ stalk_chartKer_zeroScheme_eq_span_germ C.site C.base C.base_mem X L hinv s V b l₀ hb
        (closedSubspaceBaseChangeChartProj C.site C.base C.base_mem X.2
          (zeroScheme C.site C.base C.base_mem X L s).1
          (zeroScheme C.site C.base C.base_mem X L s).2 V ξ.1))]
  exact (closedSubspaceMultiplicity_eq_componentMultiplicity C X.2
    (zeroScheme C.site C.base C.base_mem X L s).1
    (zeroScheme C.site C.base C.base_mem X L s).2 V W ξ hξ).symm

end AlgebraicGeometry.Space

end
