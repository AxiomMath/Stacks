module

public import StacksFrontier.RingTheory.NodalChart.Blowup

/-!
# Nondegeneracy of the blowup charts of the standard nodal model

The chart identifications of `StacksFrontier.RingTheory.NodalChart.Blowup` are existential
statements about a subalgebra of a localization, under a list of instance hypotheses. This file
exhibits concrete data satisfying every one of those hypotheses — the ring `ℤ`, the element `2`
and the exponent `3`, with the localizations taken at the respective denominators — and records
three things about it: that the charts are not trivial rings, that the exponent in the central
chart is *pinned* rather than incidental, and that the three chart theorems do apply at that
data.

The exponent control is the sharpest of the three. The two coordinates of the central chart of
`ℤ[x, y]/(xy - 2³)` multiply to `2¹`, and *not* to `2²`: the second would force `2 = 4` in `ℤ`,
because the structure map of the localization is injective. So the drop `n ↦ n - 2` in
`Stacks.nodalCentralChart_equiv` is not a statement that would survive perturbing the exponent.

## Main results

* `Stacks.nodalCentralFrac_zero_mul_one` — the product of the two central-chart coordinates is
  `π^(n-2)`: the exponent drop, read off the fractions themselves.
* `Stacks.nodalCentralChart_exponent_eq`, `Stacks.nodalCentralChart_exponent_ne` — the pinned
  exponent and its predicted failure, over `ℤ` at `π = 2` and `n = 3`.
* `Stacks.nodalChart_hypotheses_satisfiable_central`,
  `Stacks.nodalChart_hypotheses_satisfiable_x`,
  `Stacks.nodalChart_hypotheses_satisfiable_y` — the three chart theorems instantiated at that
  concrete data, so no instance hypothesis of theirs is unsatisfiable.
* `Stacks.nontrivial_nodalCentralChart` — the central chart is a nontrivial ring.
-/

@[expose] public noncomputable section

universe u

namespace Stacks

section Exponent

variable {R : Type u} [CommRing R] (π : R) (n : ℕ) (S : Type u) [CommRing S]
  [Algebra (nodalChartRing R (π ^ n)) S]
  [IsLocalization.Away (algebraMap R (nodalChartRing R (π ^ n)) π) S]
  [Algebra R S] [IsScalarTower R (nodalChartRing R (π ^ n)) S]

/-- **The exponent drop, on the fractions.** The two coordinates `x/π` and `y/π` of the central
blowup chart of `R[x, y]/(xy - πⁿ)` multiply to `π^(n-2)`. -/
public theorem nodalCentralFrac_zero_mul_one (hn : 2 ≤ n) :
    nodalCentralFrac π n S 0 * nodalCentralFrac π n S 1 = algebraMap R S (π ^ (n - 2)) := by
  calc nodalCentralFrac π n S 0 * nodalCentralFrac π n S 1
      = nodalCentralChartMap π n S hn
          (nodalGen R (π ^ (n - 2)) 0 * nodalGen R (π ^ (n - 2)) 1) := by
        rw [map_mul, nodalCentralChartMap_gen, nodalCentralChartMap_gen]
    _ = algebraMap R S (π ^ (n - 2)) := by
        rw [nodalGen_zero_mul_nodalGen_one, AlgHom.commutes]

end Exponent

section Control

/-- The standard nodal model `ℤ[x, y]/(xy - 2³)`: concrete data for the chart theorems. -/
public abbrev controlModel : Type := nodalChartRing ℤ ((2 : ℤ) ^ 3)

/-- The localization of `ℤ[x, y]/(xy - 2³)` away from `2`, the base of the central chart. -/
public abbrev controlCentralLoc : Type :=
  Localization.Away (algebraMap ℤ controlModel 2)

public theorem isDomain_controlModel : IsDomain controlModel :=
  isDomain_nodalChartRing (by norm_num)

/-- The structure map `ℤ → (ℤ[x, y]/(xy - 2³))_2` is injective, so an equation between images of
integers is an equation between integers. -/
public theorem injective_algebraMap_controlCentralLoc :
    Function.Injective (algebraMap ℤ controlCentralLoc) := by
  have _ : IsDomain controlModel := isDomain_controlModel
  have hne : algebraMap ℤ controlModel 2 ≠ 0 :=
    algebraMap_nodalChartRing_ne_zero ((2 : ℤ) ^ 3) (r := 2) (by norm_num)
  have h1 : Function.Injective (algebraMap controlModel controlCentralLoc) :=
    IsLocalization.injective (M := Submonoid.powers (algebraMap ℤ controlModel 2))
      controlCentralLoc (powers_le_nonZeroDivisors_of_noZeroDivisors hne)
  intro a b hab
  refine injective_algebraMap_nodalChartRing ((2 : ℤ) ^ 3) (h1 ?_)
  rw [← IsScalarTower.algebraMap_apply ℤ controlModel controlCentralLoc,
    ← IsScalarTower.algebraMap_apply ℤ controlModel controlCentralLoc]
  exact hab

/-- The two central-chart coordinates of `ℤ[x, y]/(xy - 2³)` multiply to `2¹`. -/
public theorem nodalCentralChart_exponent_eq :
    nodalCentralFrac (2 : ℤ) 3 controlCentralLoc 0 *
        nodalCentralFrac (2 : ℤ) 3 controlCentralLoc 1
      = algebraMap ℤ controlCentralLoc ((2 : ℤ) ^ 1) :=
  nodalCentralFrac_zero_mul_one (2 : ℤ) 3 controlCentralLoc (by norm_num)

/-- **Predicted failure.** They do *not* multiply to `2²`: the exponent `n - 2` of
`Stacks.nodalCentralChart_equiv` is pinned, not incidental. -/
public theorem nodalCentralChart_exponent_ne :
    nodalCentralFrac (2 : ℤ) 3 controlCentralLoc 0 *
        nodalCentralFrac (2 : ℤ) 3 controlCentralLoc 1
      ≠ algebraMap ℤ controlCentralLoc ((2 : ℤ) ^ 2) := by
  intro h
  have h2 : (2 : ℤ) ^ 1 = (2 : ℤ) ^ 2 :=
    injective_algebraMap_controlCentralLoc (nodalCentralChart_exponent_eq.symm.trans h)
  norm_num at h2

/-- The hypotheses of `Stacks.nodalCentralChart_equiv` are satisfiable: here is the statement at
`R = ℤ`, `π = 2`, `n = 3`. -/
public theorem nodalChart_hypotheses_satisfiable_central :
    ∃ e : ↥(nodalCentralChart (2 : ℤ) 3 controlCentralLoc) ≃+*
        nodalChartRing ℤ ((2 : ℤ) ^ (3 - 2)),
      (∀ r : ℤ, e (algebraMap controlModel
          ↥(nodalCentralChart (2 : ℤ) 3 controlCentralLoc) (algebraMap ℤ controlModel r))
        = algebraMap ℤ (nodalChartRing ℤ ((2 : ℤ) ^ (3 - 2))) r) ∧
      (∀ i : Fin 2,
        e (algebraMap controlModel ↥(nodalCentralChart (2 : ℤ) 3 controlCentralLoc)
            (nodalGen ℤ ((2 : ℤ) ^ 3) i))
          = algebraMap ℤ (nodalChartRing ℤ ((2 : ℤ) ^ (3 - 2))) 2 *
              nodalGen ℤ ((2 : ℤ) ^ (3 - 2)) i) :=
  nodalCentralChart_equiv (2 : ℤ) 3 controlCentralLoc (by norm_num) (by norm_num)

/-- The central chart is a nontrivial ring: the statement it satisfies is not vacuous for want of
elements. -/
public theorem nontrivial_nodalCentralChart :
    Nontrivial ↥(nodalCentralChart (2 : ℤ) 3 controlCentralLoc) := by
  obtain ⟨e, -, -⟩ := nodalChart_hypotheses_satisfiable_central
  have _ : IsDomain (nodalChartRing ℤ ((2 : ℤ) ^ (3 - 2))) :=
    isDomain_nodalChartRing (by norm_num)
  exact e.toEquiv.nontrivial

/-- The localization of `ℤ[x, y]/(xy - 2³)` away from `x`, the base of the `x`-chart. -/
public abbrev controlXLoc : Type := Localization.Away (nodalGen ℤ ((2 : ℤ) ^ 3) 0)

/-- The hypotheses of `Stacks.nodalXChart_equiv` are satisfiable. -/
public theorem nodalChart_hypotheses_satisfiable_x :
    ∃ e : ↥(nodalXChart (2 : ℤ) 3 controlXLoc) ≃+* nodalChartRing ℤ (2 : ℤ),
      (∀ r : ℤ, e (algebraMap controlModel ↥(nodalXChart (2 : ℤ) 3 controlXLoc)
          (algebraMap ℤ controlModel r)) = algebraMap ℤ (nodalChartRing ℤ (2 : ℤ)) r) ∧
      e (algebraMap controlModel ↥(nodalXChart (2 : ℤ) 3 controlXLoc)
          (nodalGen ℤ ((2 : ℤ) ^ 3) 0)) = nodalGen ℤ (2 : ℤ) 0 ∧
      e (algebraMap controlModel ↥(nodalXChart (2 : ℤ) 3 controlXLoc)
          (nodalGen ℤ ((2 : ℤ) ^ 3) 1))
        = nodalGen ℤ (2 : ℤ) 1 * algebraMap ℤ (nodalChartRing ℤ (2 : ℤ)) ((2 : ℤ) ^ (3 - 1)) :=
  nodalXChart_equiv (2 : ℤ) 3 controlXLoc (by norm_num) (by norm_num)

/-- The localization of `ℤ[x, y]/(xy - 2³)` away from `y`, the base of the `y`-chart. -/
public abbrev controlYLoc : Type := Localization.Away (nodalGen ℤ ((2 : ℤ) ^ 3) 1)

/-- The hypotheses of `Stacks.nodalYChart_equiv` are satisfiable. -/
public theorem nodalChart_hypotheses_satisfiable_y :
    ∃ e : ↥(nodalYChart (2 : ℤ) 3 controlYLoc) ≃+* nodalChartRing ℤ (2 : ℤ),
      (∀ r : ℤ, e (algebraMap controlModel ↥(nodalYChart (2 : ℤ) 3 controlYLoc)
          (algebraMap ℤ controlModel r)) = algebraMap ℤ (nodalChartRing ℤ (2 : ℤ)) r) ∧
      e (algebraMap controlModel ↥(nodalYChart (2 : ℤ) 3 controlYLoc)
          (nodalGen ℤ ((2 : ℤ) ^ 3) 1)) = nodalGen ℤ (2 : ℤ) 0 ∧
      e (algebraMap controlModel ↥(nodalYChart (2 : ℤ) 3 controlYLoc)
          (nodalGen ℤ ((2 : ℤ) ^ 3) 0))
        = nodalGen ℤ (2 : ℤ) 1 * algebraMap ℤ (nodalChartRing ℤ (2 : ℤ)) ((2 : ℤ) ^ (3 - 1)) :=
  nodalYChart_equiv (2 : ℤ) 3 controlYLoc (by norm_num) (by norm_num)

end Control

end Stacks

end
