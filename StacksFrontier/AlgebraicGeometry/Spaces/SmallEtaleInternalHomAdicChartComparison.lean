module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsSuccTower
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicComparisonChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicSourceChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAdicTargetSections

/-!
# The adic comparison of Stacks 08B6 is bijective on the inverse limits over an affine chart

Let `X` be a Noetherian algebraic space over a scheme `S` of a big fppf site `B`, let `𝓘 ⊆ 𝒪_X` be
a quasi-coherent sheaf of ideals, let `M`, `N` be coherent `𝒪_X`-modules and write
`𝓗 = 𝓗om_{𝒪_X}(M, N)`.  Over an étale chart `V` whose scheme is affine and whose ring is
Noetherian, the comparison
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` is a bijection

`lim_n (𝓗 / 𝓘 ^ n 𝓗)(V) ≃ lim_n 𝓗om(M, N / 𝓘 ^ n N)(V)`,

which is the chartwise hypothesis `h0882` of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` over such a chart.

The proof is a change of coordinates and then the commutative algebra.  Both sides are read over
the chart — the source by
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicSourceChartEquiv` and the target by
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicTargetChartEquiv` — the comparison becomes the
module-theoretic one `Stacks.AdicSystem.HomSections.homAdicComparison` of Stacks 09BB, and
`Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap` says that one is bijective
on the inverse limits.  The transport is
`Stacks.SuccTower.bijective_sectionsMap_of_congr`, which needs the two readings only levelwise and
only as equivalences of types, together with their compatibility with the transition maps.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicQuotientTargetChartEquiv` — the target-side
  reading, at the `AlgebraicGeometry.Space.smallEtaleAdicQuotient` spelling.
* `AlgebraicGeometry.Space.transition_smallEtaleInternalHomAdicQuotientTargetChartEquiv` — **the
  target-side reading intertwines the transition maps.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp` —
  **the two comparisons agree** under the two readings.
* `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison` —
  **the comparison is bijective on the inverse limits of the sections over an affine chart.**

## Implementation notes

The index shift is carried in the open.  The sheaf towers of Stacks 08B6 are indexed
`n ↦ 𝓘 ^ (n + 1)` and the towers of Stacks 09BB `n ↦ I ^ n`, and the two are matched by
instantiating the readings at `n + 1`, which is visible in the statement of
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison` and in
the levelwise families fed to `Stacks.SuccTower.bijective_sectionsMap_of_congr`.  The step from a
tower indexed from level `1` to Mathlib's `AdicCompletion`, which is indexed from level `0`, is
`Stacks.SuccTower.sectionsShift` and is made inside
`Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap`; neither shift is left to a
definitional unfolding.

`AlgebraicGeometry.Space.idealPowerQuotientChartSectionsLinearEquiv` and
`AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv` are the same equivalence —
the first at the module universe of the schemes, the second at any — and they differ only in
positions which proof irrelevance collapses, so
`AlgebraicGeometry.Space.idealPowerQuotientChartSectionsLinearEquiv_eq` is `rfl`.  It is stated
rather than used implicitly, so that the transition compatibility proved once, at the general
universe, serves the target side too.

Two shapes are forced by the heartbeat budget and are not a matter of taste.  The section of
`𝓗 / 𝓘 ^ (n + 1) 𝓗` is universally quantified in the conclusion of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp` rather
than taken as a hypothesis, so that the reduction to the image of a section of `𝓗` is the
term-mode `Function.Surjective.forall`; destructing that surjectivity with `obtain` in front of
the goal instead exhausts the budget, although the same `obtain` in front of a trivial goal, and
the goal itself against a deliberately wrong proof, each cost nothing.  And the transport to the
inverse limits goes through `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_congr`, where
the inverse system is abstract, rather than through
`Stacks.SuccTower.bijective_sectionsMap_of_congr` directly: unifying
`AlgebraicGeometry.Space.adicSectionsAt` with the subtype of compatible sequences underneath
these concrete systems of internal homs is the same kind of unfolding and is likewise out of
budget.

Both `HasCokernels` hypotheses are explicit: the adic quotient of `N` lives in `Modules.{u, u}`
and the adic quotient of `𝓗` in `Modules.{u, u + 1}`, and with either left to instance search the
universe-polymorphic `Abelian` instance for the modules is tried at `max (u + 1) ?w` and
elaboration stops at a stuck universe constraint rather than backtracking.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
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
    [HasCokernels (Modules.{u, u} B S hS X.1 X.2)]
    [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)]

/-! ### The two spellings of the affine-chart sections of an adic quotient -/

omit [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)] in
/-- **The two spellings of the affine-chart sections of an adic quotient agree**, on the nose:
`AlgebraicGeometry.Space.idealPowerQuotientChartSectionsLinearEquiv` is
`AlgebraicGeometry.Space.smallEtaleAdicQuotientChartSectionsEquiv` at the module universe of the
schemes.  Both are the first isomorphism theorem for the same projection, and the hypotheses they
take differ only in positions which proof irrelevance collapses. -/
theorem idealPowerQuotientChartSectionsLinearEquiv_eq
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) :
    idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV =
      smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) N
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 N hN) k hV :=
  rfl

omit [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)] in
/-- The inverse of the affine-chart reading of the sections of `N / 𝓘 ^ k N` sends the image of a
section of `N` under the projection to its class. -/
theorem symm_idealPowerQuotientChartSectionsLinearEquiv_π
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) (y : N.val.obj (op V)) :
    (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).symm
        (((smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 k N).val.app (op V)).hom y) =
      Submodule.Quotient.mk y := by
  rw [idealPowerQuotientChartSectionsLinearEquiv_eq]
  exact (LinearEquiv.symm_apply_eq _).2
    (smallEtaleAdicQuotientChartSectionsEquiv_mk B S hS X.1 X.2 𝓘
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) N
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 N hN) k hV y).symm

omit [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)] in
/-- The inverse of the affine-chart reading intertwines the transition maps. -/
theorem symm_transition_idealPowerQuotientChartSectionsLinearEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (y : (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (k + 1) N).val.obj (op V)) :
    (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).symm
        (((smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 k N).val.app (op V)).hom y) =
      AdicCompletion.transitionMap (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (N.val.obj (op V))
        (Nat.le_succ k)
        ((idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN (k + 1) hV).symm y) := by
  rw [idealPowerQuotientChartSectionsLinearEquiv_eq]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  refine (congrArg (fun z => (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 k N).val.app
    (op V) z) (LinearEquiv.apply_symm_apply
      (smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) N
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 N hN)
        (k + 1) hV) y)).symm.trans ?_
  exact transition_val_app_smallEtaleAdicQuotientChartSectionsEquiv B S hS X.1 X.2 𝓘
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 _ hI) N
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite.{u} B S hS X.1 X.2 N hN) k hV _

/-! ### The target-side reading -/

/-- **The target of the adic comparison, read over an affine étale chart** — which is
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicTargetChartEquiv`, at the
`AlgebraicGeometry.Space.smallEtaleAdicQuotient` spelling of the quotient of `N`.

`AlgebraicGeometry.Space.idealPowerQuotient` and
`AlgebraicGeometry.Space.smallEtaleAdicQuotient` are the same `𝒪_X`-module at the module universe
of the schemes, the two subsheaves divided out being written down by the same formula; but they
are distinct constants, and identifying them is a definitional unfolding of two infima of sheaf
submodules.  It is done here, once, in a declaration where nothing else is going on, so that the
statements below cross no spelling. -/
def smallEtaleInternalHomAdicQuotientTargetChartEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) :
    (smallEtaleInternalHom B S hS X.1 X.2 M
        (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 k N)).val.obj (op V) ≃
      (M.val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V]
        (N.val.obj (op V) ⧸ chartSectionIdeal B S hS X.1 X.2 𝓘 V ^ k •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V) (N.val.obj (op V))))) :=
  smallEtaleInternalHomAdicTargetChartEquiv B S hS X 𝓘 hI M N hM hN k hV

omit [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)] in
/-- The target-side reading of a section, read off: it is the affine-chart evaluation of the
section followed by the inverse of the reading of the sections of `N / 𝓘 ^ k N`.  By `rfl`. -/
theorem smallEtaleInternalHomAdicQuotientTargetChartEquiv_apply
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M
      (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 k N)).val.obj (op V))
    (x : M.val.obj (op V)) :
    smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI hM hN k hV α x =
      (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N hN k hV).symm
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M
          (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 k N) V α x) := rfl

omit [HasCokernels (Modules.{u, u + 1} B S hS X.1 X.2)] in
/-- **The target-side reading intertwines the transition maps.**  Postcomposition on the internal
Hom with the transition map of the adic quotients of `N` corresponds to postcomposition with
Mathlib's `AdicCompletion.transitionMap` on the sections.

Stated pointwise rather than as an identity of linear maps: the `CategoryTheory.LinearMap.comp`
spelling of the right-hand side has to be unfolded against the reading of a section of the
internal Hom, and that is a definitional unfolding the elaborator does not finish. -/
theorem transition_smallEtaleInternalHomAdicQuotientTargetChartEquiv
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (k : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M
      (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (k + 1) N)).val.obj (op V))
    (x : M.val.obj (op V)) :
    smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI hM hN k hV
        ((smallEtaleInternalHomMapRight B S hS X.1 X.2 M
          (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 k N)).val.app (op V) α) x =
      AdicCompletion.transitionMap (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (N.val.obj (op V))
          (Nat.le_succ k)
        (smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI hM hN (k + 1)
          hV α x) := by
  simp only [smallEtaleInternalHomAdicQuotientTargetChartEquiv_apply,
    smallEtaleInternalHomChartEvaluation_smallEtaleInternalHomMapRight,
    symm_transition_idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 N hI hN k hV]


/-! ### The two comparisons agree -/

/-- **The sheaf-theoretic comparison of Stacks 08B6 and the module-theoretic comparison of
Stacks 09BB agree** under the two affine-chart readings, on the image of a section of `𝓗` under
the projection.

Both sides are `x ↦ [α(x)]`: on the sheaf side by
`AlgebraicGeometry.Space.smallEtaleInternalHomChartEvaluation_comparisonApp` and
`AlgebraicGeometry.Space.symm_idealPowerQuotientChartSectionsLinearEquiv_π`, on the module side by
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicSourceChartEquiv_π` and
`Stacks.AdicSystem.HomSections.homAdicComparison_mk`. -/
theorem smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp_π
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (n : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (α : (smallEtaleInternalHom B S hS X.1 X.2 M N).val.obj (op V))
    (x : M.val.obj (op V)) :
    smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI
          hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite (n + 1) hV
        ((smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N n).val.app (op V)
          ((smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 (n + 1)
            (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.app (op V) α)) x =
      Stacks.AdicSystem.HomSections.homAdicComparison
          (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (M.val.obj (op V)) (N.val.obj (op V)) (n + 1)
          (smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN (n + 1) hV
            ((smallEtaleAdicQuotientProjection B S hS X.1 X.2 𝓘 (n + 1)
              (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.app (op V) α)) x :=
  ((smallEtaleInternalHomAdicQuotientTargetChartEquiv_apply B S hS X 𝓘 M N hI
          hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite (n + 1) hV _ x).trans
      ((congrArg (fun z => (idealPowerQuotientChartSectionsLinearEquiv B S hS X 𝓘 hI N
              hN.toIsQuasicoherentOnSite (n + 1) hV).symm z)
          (smallEtaleInternalHomChartEvaluation_comparisonApp B S hS X.1 X.2 𝓘 M N n V α
            x)).trans
        (symm_idealPowerQuotientChartSectionsLinearEquiv_π B S hS X 𝓘 N hI
          hN.toIsQuasicoherentOnSite (n + 1) hV
          (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α x)))).trans
    ((congrArg (fun g => Stacks.AdicSystem.HomSections.homAdicComparison
          (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (M.val.obj (op V)) (N.val.obj (op V))
          (n + 1) g x)
        (smallEtaleInternalHomAdicSourceChartEquiv_π B S hS X 𝓘 M N hI hM hN (n + 1)
          hV α)).trans
      (Stacks.AdicSystem.HomSections.homAdicComparison_mk
        (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (M.val.obj (op V)) (N.val.obj (op V)) (n + 1)
        (smallEtaleInternalHomChartEvaluation B S hS X.1 X.2 M N V α) x)).symm

/-- **The sheaf-theoretic comparison of Stacks 08B6 and the module-theoretic comparison of
Stacks 09BB agree** under the two affine-chart readings.

The sections of `𝓗 / 𝓘 ^ (n + 1) 𝓗` over an affine chart are exhausted by the images of sections
of `𝓗` under the projection
(`AlgebraicGeometry.Space.surjective_val_app_smallEtaleInternalHomAdicQuotient_π`), and on such a
section both comparisons are `x ↦ [α(x)]` by
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp_π`.

The section is universally quantified in the conclusion rather than taken as a hypothesis, so
that the reduction to the image of a section is the term-mode
`Function.Surjective.forall`:  destructing the surjectivity with `obtain` in front of this goal
instead exhausts the heartbeat budget, the equality of the two readings being a goal whose
elaboration `Lean.Meta.isDefEq` does not get through twice. -/
theorem smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N) (n : ℕ)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V)) :
    ∀ z : (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N)).val.obj (op V),
    smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI
          hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite (n + 1) hV
        ((smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N n).val.app (op V) z) =
      Stacks.AdicSystem.HomSections.homAdicComparison
        (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (M.val.obj (op V)) (N.val.obj (op V)) (n + 1)
        (smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN (n + 1) hV z) :=
  (surjective_val_app_smallEtaleInternalHomAdicQuotient_π B S hS X.1 X.2 𝓘 M N hI hM hN (n + 1)
    hV).forall.2 fun α => LinearMap.ext fun x =>
      smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp_π B S hS X 𝓘 M N hI hM hN n
        hV α x

/-! ### The comparison is bijective on the inverse limits over an affine chart -/

/-- **The adic comparison of Stacks 08B6 is bijective on the inverse limits of the sections over
an affine étale chart whose ring is Noetherian:**

`lim_n (𝓗 / 𝓘 ^ n 𝓗)(V) ≃ lim_n 𝓗om(M, N / 𝓘 ^ n N)(V)`.

This is the chartwise hypothesis `h0882` of
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` over such a chart, and it is where the
source's Noetherian and coherence hypotheses are spent: the chart's ring is Noetherian and the
sections of `M` and of `N` over it are finite modules, which is what Stacks 09BB asks for.

Over the chart both towers become towers of modules — the source
`Hom_{𝒪(V)}(M(V), N(V)) / 𝓘(V) ^ n ·` and the target `Hom_{𝒪(V)}(M(V), N(V) / 𝓘(V) ^ n N(V))` —
the comparison becomes `Stacks.AdicSystem.HomSections.homAdicComparison`, and
`Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap` is the Artin--Rees
statement that it is bijective on the limits.  No finiteness of `𝓗(V)` is wanted: Stacks 09BB
builds the module of homomorphisms itself. -/
theorem bijective_adicSectionsMapAt_smallEtaleInternalHomAdicComparison
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hM : IsCoherent B S hS X.1 X.2 M) (hN : IsCoherent B S hS X.1 X.2 N)
    {V : SmallEtale B S hS X.1} (hV : IsAffine (chartScheme V))
    (hVN : IsNoetherianRing (chartRing B S hS X.1 X.2 V)) :
    Function.Bijective (adicSectionsMapAt B S hS X.1 X.2
      (fun n => smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS X.1 X.2 M N))
      (fun n => smallEtaleInternalHom B S hS X.1 X.2 M
        (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1)
        (smallEtaleInternalHom B S hS X.1 X.2 M N))
      (fun n => smallEtaleInternalHomMapRight B S hS X.1 X.2 M
        (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) N))
      (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N)
      (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M N) (op V)) := by
  have : IsNoetherianRing (chartRing B S hS X.1 X.2 V) := hVN
  have : Module.Finite (chartRing B S hS X.1 X.2 V) (M.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS X.1 X.2 M hM hV
  have : Module.Finite (chartRing B S hS X.1 X.2 V) (N.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS X.1 X.2 N hN hV
  exact bijective_adicSectionsMapAt_of_congr B S hS X.1 X.2
    (fun n => smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N))
    (fun n => smallEtaleInternalHom B S hS X.1 X.2 M
      (smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) N))
    (fun n => smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS X.1 X.2 M N))
    (fun n => smallEtaleInternalHomMapRight B S hS X.1 X.2 M
      (smallEtaleAdicQuotientTransition B S hS X.1 X.2 𝓘 (n + 1) N))
    (smallEtaleInternalHomAdicComparisonApp B S hS X.1 X.2 𝓘 M N)
    (smallEtaleInternalHomAdicComparison_compat B S hS X.1 X.2 𝓘 M N) (op V)
    (Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap
      (chartSectionIdeal B S hS X.1 X.2 𝓘 V) (M.val.obj (op V)) (N.val.obj (op V)))
    (fun n => (smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN (n + 1)
      hV).toEquiv)
    (fun n x => transition_smallEtaleInternalHomAdicSourceChartEquiv B S hS X 𝓘 M N hI hM hN
      (n + 1) hV x)
    (fun n => smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI
      hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite (n + 1) hV)
    (fun n y => LinearMap.ext fun x =>
      transition_smallEtaleInternalHomAdicQuotientTargetChartEquiv B S hS X 𝓘 M N hI
        hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite (n + 1) hV y x)
    (fun n => smallEtaleInternalHomAdicQuotientTargetChartEquiv_comparisonApp B S hS X 𝓘 M N hI
      hM hN n hV)

end AlgebraicGeometry.Space

end
