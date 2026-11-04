module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAdicQuotientChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartBijective

/-!
# The source of the adic comparison, read over an affine chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals, let `M`, `N` be coherent `𝒪_X`-modules and write
`𝓗 = 𝓗om_{𝒪_X}(M, N)`.  The source of the adic comparison of Stacks 08B6 is the inverse system
`𝓗 / 𝓘 ^ n 𝓗`, and this file reads its sections over an affine étale chart `V`:

`(𝓗 / 𝓘 ^ k 𝓗)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V)) / 𝓘(V) ^ k Hom_{𝒪_X(V)}(M(V), N(V))`,

and shows that the reading carries the transition maps of the sheaf tower to the transition maps
of the module tower.

It is `AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv` at `𝓗` — whose
cartesianness on affine charts comes from the source's own hypotheses, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent` —
composed with the affine-chart reading of a section of the internal Hom as a linear map of the
sections, `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomChartEvaluation`.

Together with `AlgebraicGeometry.Space.smallEtaleInternalHomAdicTargetChartEquiv`, which does the
same for the target system `𝓗om(M, N / 𝓘 ^ n N)`, this puts both sides of the chartwise
hypothesis `h0882` of `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` in the form the
commutative-algebra comparison of Stacks 09BB is stated in,
`Stacks.AdicSystem.HomSections.homAdicComparisonSectionsMap`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluationLinearEquiv` — the affine-chart
  reading of a section of `𝓗`, as a linear equivalence.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicSourceChartEquiv` — **the source-side
  reading** of the adic comparison over an affine chart.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicSourceChartEquiv_π` — it sends the image of a
  section of `𝓗` under the projection to the class of its reading.
* `AlgebraicGeometry.Space.transition_smallEtaleInternalHomAdicSourceChartEquiv` — **it
  intertwines the transition maps.**

## Implementation notes

The `HasCokernels` hypothesis at the module universe `u + 1` of `𝓗` is supplied explicitly rather
than left to instance search: with it left to search the universe-polymorphic `Abelian` instance
for the modules is tried at `max (u + 1) ?w` and elaboration stops at the stuck constraint
`u + 1 =?= max (u + 1) ?w` rather than backtracking.

Everything is checked on the image of a section of `𝓗` under the projection, which exhausts the
sections of `𝓗 / 𝓘 ^ k 𝓗` over an affine chart by
`AlgebraicGeometry.Space.surjective_val_app_smallEtaleInternalHomAdicQuotient_π`.  On such a
section both transition maps are the identity on the reading, the sheaf one because the
projections compose and the module one because a class is fixed.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
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
    (M N : Modules.{u, u} B S hS X.1 X.2)

/-- **The affine-chart reading of a section of `𝓗om_{𝒪_X}(M, N)` as a linear equivalence:**

`𝓗om_{𝒪_X}(M, N)(V) ≃ₗ Hom_{𝒪_X(V)}(M(V), N(V))`.

The map is `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation`, which is linear by
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluationLinear` and bijective over an affine
chart by `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomChartEvaluation`. -/
def smallEtaleInternalHomChartEvaluationLinearEquiv (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) :
    (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ≃ₗ[chartRing B S hS X.1 X.2 V]
      (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) :=
  LinearEquiv.ofBijective
    (smallEtaleInternalHomChartEvaluationLinear B S hS X.1 X.2 M N V)
    (bijective_smallEtaleInternalHomChartEvaluation B S hS X M N hM hN V hV)

/-- The reading is `AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation`. -/
theorem smallEtaleInternalHomChartEvaluationLinearEquiv_apply (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    smallEtaleInternalHomChartEvaluationLinearEquiv B S hS X M N hM hN V hV α =
      smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α := rfl

/-- A linear equivalence of the sections carries `𝓘(V) ^ k` times the whole module to `𝓘(V) ^ k`
times the whole module. -/
theorem map_pow_chartSectionIdeal_smul_top (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (k : ℕ) :
    Submodule.map
        (smallEtaleInternalHomChartEvaluationLinearEquiv B S hS X M N hM hN V hV :
          (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) →ₗ[
            chartRing B S hS X.1 X.2 V]
          (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)))
        (chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
            ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)))) =
      chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
          (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V))) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2
    (smallEtaleInternalHomChartEvaluationLinearEquiv B S hS X M N hM hN V hV).surjective]

/-- **The affine-chart reading of a section of `𝓗om_{𝒪_X}(M, N)`, on the quotients by
`𝓘(V) ^ k`.** -/
def smallEtaleInternalHomChartEvaluationQuotientEquiv (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (k : ℕ) :
    ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ⧸
          chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
            (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
              ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))))
        ≃ₗ[chartRing B S hS X.1 X.2 V]
      ((M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) ⧸
        chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
            (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)))) :=
  Submodule.Quotient.equiv _ _
    (smallEtaleInternalHomChartEvaluationLinearEquiv B S hS X M N hM hN V hV)
    (map_pow_chartSectionIdeal_smul_top B S hS X 𝓘 M N hM hN V hV k)

/-- The reading on the quotients, on the class of a section.  By `rfl`. -/
theorem smallEtaleInternalHomChartEvaluationQuotientEquiv_mk (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (k : ℕ) (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N hM hN V hV k
        (Submodule.Quotient.mk α) =
      Submodule.Quotient.mk
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α) := rfl

/-- The reading on the quotients intertwines the transition maps of the two module towers.  Both
fix a class, so this is `rfl` on one. -/
theorem transition_smallEtaleInternalHomChartEvaluationQuotientEquiv
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) (k : ℕ)
    (w : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ⧸
      chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ (k + 1) •
        (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
          ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)))) :
    smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N hM hN V hV k
        (AdicCompletion.transitionMap (chartSectionIdeal B S hS X.1 X.2 𝓘 V)
          ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) (Nat.le_succ k) w) =
      AdicCompletion.transitionMap (chartSectionIdeal B S hS X.1 X.2 𝓘 V)
        (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) (Nat.le_succ k)
        (smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N hM hN V hV (k + 1) w) :=
  Stacks.AdicSystem.HomSections.transitionMap_quotientEquiv
    (chartSectionIdeal B S hS X.1 X.2 𝓘 V)
    (smallEtaleInternalHomChartEvaluationLinearEquiv B S hS X M N hM hN V hV)
    (map_pow_chartSectionIdeal_smul_top B S hS X 𝓘 M N hM hN V hV) k w

variable [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)]

/-- **The source of the adic comparison of Stacks 08B6, read over an affine étale chart:**

`(𝓗 / 𝓘 ^ k 𝓗)(V) ≃ Hom_{𝒪_X(V)}(M(V), N(V)) / 𝓘(V) ^ k Hom_{𝒪_X(V)}(M(V), N(V))`.

The sections of the adic quotient over an affine chart are the ordinary quotient of the sections
of `𝓗` by `AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv`, and the sections of
`𝓗` are the linear maps of the sections by
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluationQuotientEquiv`. -/
def smallEtaleInternalHomAdicSourceChartEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) :
    (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 k
          (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.obj (op V)
        ≃ₗ[chartRing B S hS X.1 X.2 V]
      ((M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) ⧸
        chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
            (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)))) :=
  (smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI)
        (smallEtaleInternalHom B S hS X.1 X.2 M N)
        (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS X.1 X.2 M N hM hN)
        k hV).symm.trans
    (smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N
      hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite V hV k)

/-- The source-side reading of a section of the adic quotient is the reading on the quotients of
any class of sections of `𝓗` that the identification sends to it. -/
private theorem smallEtaleInternalHomAdicSourceChartEquiv_eq_of_chartSectionsEquiv_eq
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (w : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V) ⧸
      chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
          ((smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))))
    (y : (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 k
      (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.obj (op V))
    (h : smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI)
        (smallEtaleInternalHom B S hS X.1 X.2 M N)
        (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS X.1 X.2 M N hM hN)
        k hV w = y) :
    smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN k hV y =
      smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N
        hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite V hV k w :=
  congrArg (smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N
      hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite V hV k)
    ((LinearEquiv.symm_apply_eq _).2 h.symm)

/-- **The source-side reading sends the image of a section of `𝓗` under the projection to the
class of its reading.** -/
theorem smallEtaleInternalHomAdicSourceChartEquiv_π
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V)) :
    smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN k hV
        ((smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 k
          (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.app (op V) α) =
      Submodule.Quotient.mk (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α) :=
  smallEtaleInternalHomAdicSourceChartEquiv_eq_of_chartSectionsEquiv_eq B S hS X 𝓘 M N hI hM hN
    k hV _ _
    (smallEtaleAdicQuotientChartSectionsEquiv_mk B S hS X.1 X.2 𝓘
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI)
      (smallEtaleInternalHom B S hS X.1 X.2 M N)
      (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS X.1 X.2 M N hM hN)
      k hV α)

/-- **The source-side reading intertwines the transition maps.**  The transition map
`(𝓗 / 𝓘 ^ (k + 1) 𝓗)(V) ⟶ (𝓗 / 𝓘 ^ k 𝓗)(V)` of the sheaf tower corresponds to Mathlib's
`AdicCompletion.transitionMap` on the quotients of `Hom_{𝒪_X(V)}(M(V), N(V))`. -/
theorem transition_smallEtaleInternalHomAdicSourceChartEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (y : (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (k + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.obj (op V)) :
    smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN k hV
        ((smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 k
          (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.app (op V) y) =
      AdicCompletion.transitionMap (chartSectionIdeal B S hS X.1 X.2 𝓘 V)
        (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V] N.val.obj (op V)) (Nat.le_succ k)
        (smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN (k + 1) hV y) := by
  have hw := LinearEquiv.apply_symm_apply
    (smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI)
      (smallEtaleInternalHom B S hS X.1 X.2 M N)
      (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS X.1 X.2 M N hM hN)
      (k + 1) hV) y
  exact (smallEtaleInternalHomAdicSourceChartEquiv_eq_of_chartSectionsEquiv_eq B S hS X 𝓘 M N hI
    hM hN k hV _ _
    ((congrArg (fun z => (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 k
        (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.app (op V) z) hw).symm.trans
      (transition_val_app_smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI)
        (smallEtaleInternalHom B S hS X.1 X.2 M N)
        (isCartesianOnAffineCharts_smallEtaleInternalHom_of_isCoherent B S hS X.1 X.2 M N hM hN)
        k hV _)).symm).trans
    (transition_smallEtaleInternalHomChartEvaluationQuotientEquiv B S hS X 𝓘 M N
      hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite V hV k _)

end AlgebraicGeometry.Space

end
