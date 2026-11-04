module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkNormalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartEtaleFractionRing

/-!
# The pullback of the chart ratio to `Spec(𝒪_{U, u})` is a unit regular function

Let `X` be a normal, locally Noetherian, integral, decent algebraic space over a scheme `S`, let
`ℒ` be an invertible `𝒪_X`-module free on `e` over an étale chart `V` of `X`, let `t` be a
meromorphic section of `ℒ` and let `Z ⊂ X` be a prime divisor with generic point `ξ`. If the
canonical ratio of `t` at `ξ` is the image of a unit of `𝒪^h_{X, ξ}` — the hypothesis of Stacks
0EPX — then over the charts of a covering sieve of the base change of `V` along
`j : Spec(𝒪_{U, u}) ⟶ X` the pullback of the ratio `t / e` is the image of a **unit regular
function**.

This is the second step of the flat-descent route of Stacks 0EPX, as the roadmap of
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassInjective.lean` records it. It joins
the first step,
`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericStalkCoefficient_of_isUnit`, to the
comparison of the two ratios over a common chart,
`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`,
and the join is arithmetic. Step one makes the coefficient `t / s_ξ` the image of a unit `a` of
`𝒪_{U, u}`; restriction carries `a` to a unit regular function on the chart `Q`, which
`AlgebraicGeometry.Space.meromorphicFunctionSheaf_map_algebraMap` — the naturality of
`𝒪 ⟶ 𝒦` at a morphism of charts — identifies with the restriction of the coefficient; the
comparison says that same restricted coefficient is a unit regular function times the pullback of
`t / e`, and cancelling that unit leaves the pullback the image of the product of two units.

`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartRatio` had no lemmas at all before this
file.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_baseChangeChartRatio`: over the
  charts of a covering sieve of the base-changed chart the pullback of the ratio `t / e` is the
  image of a unit regular function.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hX in
/-- **The pullback of the ratio `t / e` to `Spec(𝒪_{U, u})` is a unit regular function.** Let `ℒ`
be free on `e` over an étale chart `V` of `X` and let `t` be a meromorphic section of `ℒ` whose
canonical ratio at the generic point `ξ` of a prime divisor is the image of a unit of
`𝒪^h_{X, ξ}` — the hypothesis of Stacks 0EPX. Then over the charts of a covering sieve of the
base change of `V` along `j : Spec(𝒪_{U, u}) ⟶ X` the pullback
`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartRatio` of that ratio is the image of a unit
of the regular functions there.

This is step two of the flat-descent route of Stacks 0EPX. Step one
(`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericStalkCoefficient_of_isUnit`) makes
the coefficient `t / s_ξ` the image of a unit of `𝒪_{U, u}`; the comparison of the two ratios
(`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`)
makes the restriction of that coefficient a unit regular function times the pullback of `t / e`;
and `AlgebraicGeometry.Space.meromorphicFunctionSheaf_map_algebraMap` identifies the two readings
of the restricted unit, after which the comparison's own unit cancels. -/
theorem PrimeDivisor.exists_sieve_isUnit_baseChangeChartRatio (hNormal : IsNormal B S hS X)
    (t : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) (hv : IsUnit v)
    (hveq : Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) v) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ w : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2 Q, IsUnit w ∧
              Z.baseChangeChartRatio B S hS hX hdec L t V e hecompat hebij ι =
                algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2 Q)
                  ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                    (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)) w := by
  obtain ⟨a, ha, haeq⟩ := Z.exists_isUnit_genericStalkCoefficient_of_isUnit B S hS hX hdec hInt
    hN L hL hNormal t v hv hveq
  obtain ⟨T, hT, hcmp⟩ := Z.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio B S hS hX hdec
    L hL t V e hecompat hebij
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  obtain ⟨u, hu⟩ := hcmp ι hι
  set k : Q ⟶ Z.genericStalkChart B S hS hX hdec :=
    ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V) with hk
  set rA : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q :=
    (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).map k.op a with hrAdef
  have hrA : algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)
      ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)) rA =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map k.op).hom
        (Z.genericStalkCoefficient B S hS hX hdec L hL t) := by
    rw [haeq, hrAdef]
    exact (meromorphicFunctionSheaf_map_algebraMap B S hS
      (Z.genericStalkSpace B S hS hX hdec) k a).symm
  refine ⟨((u⁻¹ : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q)ˣ) :
        chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q) * rA,
    u⁻¹.isUnit.mul (ha.map _), ?_⟩
  rw [map_mul, hrA, hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-! ### Two further inputs of the descent along the flat leg -/

/-- **The morphism of schemes beneath the base change of a chart along
`j : Spec(𝒪_{U, u}) ⟶ X` is flat.** `j` is flat
(`AlgebraicGeometry.Space.PrimeDivisor.isFlat_genericStalkMorphism`), and
`AlgebraicGeometry.Space.IsFlat` is by definition flatness of the scheme morphism beneath *every*
commuting square of étale charts, of which
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeDiagram` is one.

This is what makes the stalk map of that morphism flat; being a stalk map it is also local, so it
is faithfully flat, which is what descends unit-ness of a fraction back to the chart of `X` in
the flat route of Stacks 0EPX. The ring map it induces on global functions is
`AlgebraicGeometry.Space.flat_chartDiagramRestrict_of_isFlat`, which extracts the same flatness
inline. -/
theorem PrimeDivisor.flat_genericStalkBaseChangeDiagram_g (V : SmallEtale B S hS X) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) := by
  set d := Z.genericStalkBaseChangeDiagram B S hS hX hdec V with hd
  exact Z.isFlat_genericStalkMorphism B S hS hX hdec d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom
    d.g d.U.property d.V.property d.comm.symm

/-- **The base change of a chart of `X` has a point over a *prescribed* point of that chart above
`ξ`, and over the closed point of `Spec(𝒪_{U, u})`.** Both the given point `z` of `chartScheme V`
and the closed point of `Spec(𝒪_{U, u})` lie over the generic point `ξ` of the prime divisor, so
the cartesian square defining the base change has a point over the pair, by Stacks 03H4
(`AlgebraicGeometry.Space.exists_points_of_isPullback`).

`AlgebraicGeometry.Space.PrimeDivisor.exists_mem_range_genericStalkBaseChangeChart` is the same
construction with `z` *chosen* from the hypothesis that `ξ` lies in the image of `V`, and with the
projection to `V` discarded. Both are needed here: the descent of the flat route reads the ratio
at a point of a chart of `Spec(𝒪_{U, u})` lying over the coheight-one point `z` at which the order
of vanishing is to be computed, and over the closed point, so that the stalk map it descends along
is the one at `z`. -/
theorem PrimeDivisor.exists_points_genericStalkBaseChangeChart (V : SmallEtale B S hS X)
    (z : chartScheme V) (hz : chartSchemeToPoints B S hS X V z = Z.genericPoint B S hS X) :
    ∃ p : chartScheme (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage
          (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) p =
        IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec) ∧
      (BigFppfOver.toScheme B S hS).map
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g p = z := by
  have hb : pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj V)
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj V)).symm z) = z :=
    (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj V)).apply_symm_apply z
  have hbgen : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj V)).symm z) =
      Z.genericPoint B S hS X :=
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X V z).symm.trans hz
  obtain ⟨q, hq⟩ := surjective_pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec)
    (IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec))
  obtain ⟨w, hw, hw2⟩ := exists_points_of_isPullback B S hS
    ((Z.representable_genericStalkMorphism B S hS hX hdec).isPullback V.obj.hom) q
    ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj V)).symm z)
    ((Z.pointsMap_genericStalkMorphism_eq_genericPoint B S hS hX hdec q hq).trans hbgen.symm)
  refine ⟨pointsToScheme B S hS _ w, ?_, ?_⟩
  · refine Eq.trans (pointsToScheme_pointsMap_yoneda B S hS (yoneda.preimage
      (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) w).symm ?_
    refine Eq.trans (congrArg (pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec))
      (congrArg (fun φ ↦ pointsMap B S hS _ φ w) (yoneda.map_preimage
        (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom))) ?_
    exact (congrArg (pointsToScheme B S hS (Z.genericStalkSpec B S hS hX hdec)) hw).trans hq
  · refine Eq.trans (pointsToScheme_pointsMap_yoneda B S hS
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g w).symm ?_
    exact (congrArg (pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj V)) hw2).trans hb

attribute [local instance] chartMeromorphicFunctionAlgebra

include hInt hN in
/-- **Stacks 0EN6, part (2) over an arbitrary affine chart of `Spec(𝒪_{U, u})`.** The meromorphic
functions over an affine chart of `Spec(𝒪_{U, u})` are the total ring of fractions of its regular
functions.

`AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericStalkMeromorphic` is this at the
identity chart, where the coefficient of Stacks 0EPR lives. An arbitrary affine chart is what the
flat route reads its comparison of the two ratios over, that comparison being made over a member
of a covering sieve of a base change and not over the identity chart; and being a localization is
what lets two maps out of those meromorphic functions be compared on regular functions alone. The
two hypotheses of Stacks 0EN6 hold of `Spec(𝒪_{U, u})` because its ring is reduced and
Noetherian. -/
theorem PrimeDivisor.isFractionRing_genericStalkChartMeromorphic
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (hW : IsAffine (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W)) :
    IsFractionRing ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op W))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op W)) :=
  isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.genericStalkSpace B S hS hX hdec)
    (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX hdec hInt)
    (Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN) W hW

end AlgebraicGeometry.Space

end
