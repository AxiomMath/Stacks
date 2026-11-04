module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartBijective

/-!
# The target of the adic comparison, read over an affine chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals, let `M`, `N` be quasi-coherent `𝒪_X`-modules and let `V` be an
étale chart of `X` whose scheme is affine.  The target of the adic comparison of Stacks 08B6 is
the inverse system `𝓗om_{𝒪_X}(M, N / 𝓘 ^ n N)`, and this file reads its sections over `V`:

`𝓗om_{𝒪_X}(M, N / 𝓘 ^ k N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V) / 𝓘(V) ^ k N(V))`.

It is `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomChartEvaluation` at the pair
`M`, `N / 𝓘 ^ k N`, composed with the affine-chart computation of the sections of the adic
quotient — `AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π`, which together present them as an
ordinary quotient of modules.

The quasi-coherence of `N / 𝓘 ^ k N` which the first of those needs is proved here and is free:
the quotient is cartesian on affine charts by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerQuotient`, and cartesianness on
affine charts implies quasi-coherence by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` — the converse of
Descent, Proposition 03DX(2).

Together with `AlgebraicGeometry.Space.surjective_val_app_smallEtaleInternalHomAdicQuotient_π`
and `AlgebraicGeometry.Space.ker_val_app_smallEtaleInternalHomAdicQuotient_π`, which read the
*source* of the comparison over `V` as `𝓗(V) / 𝓘(V) ^ k 𝓗(V)`, this puts both sides of the
chartwise hypothesis `h0882` of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` in the form the commutative-algebra
comparison of Stacks 09BB is stated in.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowerQuotient` — **the adic quotient of a
  quasi-coherent module by a quasi-coherent sheaf of ideals is quasi-coherent.**
* `AlgebraicGeometry.Space.idealPowerQuotientChartSectionsLinearEquiv` — **the sections of
  `M / 𝓘 ^ k M` over an affine chart are `M(V) / 𝓘(V) ^ k M(V)`**, as a linear equivalence.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicTargetChartEquiv` — **the target-side
  reading** of the adic comparison over an affine chart.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)

/-- **The adic quotient `M / 𝓘 ^ k M` of a quasi-coherent module by a quasi-coherent sheaf of
ideals is quasi-coherent.**

Both `𝓘` and `M` are cartesian on affine charts by Descent, Proposition 03DX(2), hence so is the
quotient by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_idealPowerQuotient`, and
cartesianness on affine charts implies quasi-coherence.  No Noetherian or coherence hypothesis is
used. -/
theorem isQuasicoherentOnSite_idealPowerQuotient
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (k : ℕ) :
    (idealPowerQuotient B S hS X.1 X.2 𝓘 k M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_idealPowerQuotient B S hS X.1 X.2 𝓘
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) M
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 M hM) k)

/-- **The sections of `M / 𝓘 ^ k M` over an affine étale chart are `M(V) / 𝓘(V) ^ k M(V)`.**

The projection is surjective on the sections over an affine chart and its kernel there is
`𝓘(V) ^ k · M(V)`, so the first isomorphism theorem identifies the two. -/
def idealPowerQuotientChartSectionsLinearEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (k : ℕ) {V : SmallEtale B S hS X.1}
    (hV : IsAffine (chartScheme V)) :
    (M.val.obj (op V) ⧸ chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V) (M.val.obj (op V))))
        ≃ₗ[chartRing B S hS X.1 X.2 V]
      (idealPowerQuotient B S hS X.1 X.2 𝓘 k M).val.obj (op V) :=
  (Submodule.quotEquivOfEq _ _
        (ker_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) M
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 M hM)
          k hV)).symm.trans
    (LinearMap.quotKerEquivOfSurjective _
      (surjective_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) M
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 M hM) k hV))

/-- **The target of the adic comparison of Stacks 08B6, read over an affine étale chart:**

`𝓗om_{𝒪_X}(M, N / 𝓘 ^ k N)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V) / 𝓘(V) ^ k N(V))`.

The affine-chart reading of a section of the internal Hom
(`AlgebraicGeometry.Space.bijective_smallEtaleInternalHomChartEvaluation`) is a linear map into
the sections of `N / 𝓘 ^ k N` over the chart, and those are the ordinary quotient by
`AlgebraicGeometry.Space.idealPowerQuotientChartSectionsLinearEquiv`. -/
def smallEtaleInternalHomAdicTargetChartEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) :
    (smallEtaleInternalHom B S hS X.1 X.2 M
        (idealPowerQuotient B S hS X.1 X.2 𝓘 k N)).val.obj (op V) ≃
      (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V]
        (N.val.obj (op V) ⧸ chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V) (N.val.obj (op V))))) :=
  (Equiv.ofBijective _ (bijective_smallEtaleInternalHomChartEvaluation B S hS X M
      (idealPowerQuotient B S hS X.1 X.2 𝓘 k N) hM
      (isQuasicoherentOnSite_idealPowerQuotient B S hS X 𝓘 hI N hN k) V hV)).trans
    { toFun := fun f =>
        (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).symm.toLinearMap ∘ₗ f
      invFun := fun g =>
        (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).toLinearMap ∘ₗ g
      left_inv := fun _f => LinearMap.ext fun _x =>
        (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).apply_symm_apply _
      right_inv := fun _g => LinearMap.ext fun _x =>
        (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).symm_apply_apply _ }

end AlgebraicGeometry.Space

end
