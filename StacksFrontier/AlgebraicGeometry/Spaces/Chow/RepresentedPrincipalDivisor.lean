module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedChowSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedOrderOfVanishing

/-!
# Principal divisors on a represented integral space

In Situation 0EDT let `h_R → B` be a good space represented by an integral scheme `R`. The
principal divisor `div(f) = ∑ ord_Z(f) [Z]` of a nonzero rational function `f` of `h_R`, with the
orders of vanishing of Stacks 0ENL taken at the canonical embeddings of Stacks 0ENK, has at an
integral closed subspace `Z ⊆ h_R` the coefficient of the principal divisor, Divisors, Definition
02RJ and Chow Homology, Section 02RK, of the reading of `f` on `R` at the generic point of `Z`.
At a prime divisor this is the comparison of the two orders of vanishing,
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_representedFunctionFieldMap`; at any other
integral closed subspace both coefficients vanish, because the codimension of `Z` in `|h_R|` is
the codimension of its generic point in `R`.

## Main results

* `AlgebraicGeometry.Space.codimension_integralClosedSubspaceSupport_eq_coheight`: the
  codimension of an integral closed subspace of `h_R` is the codimension of its generic point in
  `R`.
* `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_eq_principalCycle`: the
  coefficients of `div(f)` on `h_R` are those of the principal divisor of the reading of `f` on
  `R`.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Order

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The codimension of an integral closed subspace `Z` of `h_U` in `|h_U|` is the codimension, in
`U`, of the generic point of `Z`. -/
theorem codimension_integralClosedSubspaceSupport_eq_coheight (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    codimension (integralClosedSubspaceSupport B S hS (isAlgebraicSpace_yoneda B S hS U) Z) =
      coheight (Z.schemeGenericPoint B S hS U) := by
  rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton,
    ← codimension_orderIsoOfHomeomorph (schemePointsHomeomorph B S hS U)]
  congr 1
  apply IrreducibleCloseds.ext
  rw [IrreducibleCloseds.coe_orderIsoOfHomeomorph, coe_integralClosedSubspaceSupport]
  exact Z.image_subspacePointSet B S hS U

variable (D : BaseSpaceDimensionSituation.{u}) {R : BigFppfOver D.site D.base D.base_mem}
    (sY : yoneda.obj R ⟶ D.space) (hY : D.IsGood sY)
    [IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R)]

/-- **Principal divisors on a represented integral space are principal divisors on the scheme.**
Let `h_R → B` be good with `R` integral, and let `f` be a nonzero rational function of `h_R`. At
the canonical embeddings of Stacks 0ENK, the coefficient of `div(f)` at an integral closed
subspace `Z ⊆ h_R` is the coefficient of the principal divisor of the reading of `f` on `R` at
the generic point of `Z`. -/
theorem principalDivisorCycleCoefficients_eq_principalCycle
    (f : (rationalFunctions D.site D.base D.base_mem (isAlgebraicSpace_yoneda _ _ _ R))ˣ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj R)) :
    haveI := isLocallyNoetherian_of_isGood_yoneda D sY hY
    letI E := genericFractionEmbedding D.site D.base D.base_mem hY.1
      (isDecentSpace_yoneda _ _ _ R) (isIntegralSpace_yoneda _ _ _ R)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    principalDivisorCycleCoefficients D sY hY (isDecentSpace_yoneda _ _ _ R) E.emb
        (f : rationalFunctions _ _ _ hY.1) (fun W => f.isUnit.map (E.emb W)) Z =
      Stacks.Chow.principalCycle ((BigFppfOver.toScheme D.site D.base D.base_mem).obj R)
        (representedFunctionFieldMap D.site D.base D.base_mem R f)
        (Z.schemeGenericPoint D.site D.base D.base_mem R) := by
  have := isLocallyNoetherian_of_isGood_yoneda D sY hY
  rw [Stacks.Chow.principalCycle_apply]
  unfold principalDivisorCycleCoefficients
  split_ifs with h
  · set P := Z.toPrimeDivisor D.site D.base D.base_mem hY.1 h
    have hgen : pointsToScheme D.site D.base D.base_mem R (P.genericPoint _ _ _ _) =
        Z.schemeGenericPoint D.site D.base D.base_mem R := by
      rw [PrimeDivisor.genericPoint_eq_of_isGenericPoint (hX := hY.1)
        (hdec := isDecentSpace_yoneda _ _ _ R) P (isGenericPoint_pointsMap_genericPoint D.site
          D.base D.base_mem hY.1 Z)]
      rfl
    rw [← hgen, ← PrimeDivisor.ord_eq_ord_representedFunctionFieldMap D.site D.base D.base_mem R
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) P f]
    rfl
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one]
    rwa [codimension_integralClosedSubspaceSupport_eq_coheight] at h

end AlgebraicGeometry.Space

end
