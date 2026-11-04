module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0GJC with the statement of Tag 03SC discharged

`Stacks.EtaleCohomology.CurveTorsionCohomologyStatement` is the statement of [Stacks, Tag 03SC]
in the form taken as a hypothesis by the finiteness results for constant sheaves of modules on
curves. It holds (`Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds`, from the eight
statements of Situation 0A52 and the base case of Lemma 0A5B); this file draws from it the
unconditional form of [Stacks, Tag 0GJC], both parts in one statement.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.finite_etaleCohomology_constantSheaf`: **Tag 0GJC**,
  both parts, with nothing granted.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

namespace TorsionModules

-- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the module universe `u + 1` and its
-- unification against `ModuleCat.{max (u + 1) r}` fails with a universe error instead of
-- backtracking, so it is switched off here.
attribute [-instance] hasSheafifyEtale

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks Project, Tag 0GJC.** Let `Λ` be a Noetherian ring, `M` a finite `Λ`-module
annihilated by an integer `n > 0`, `k` an algebraically closed field and `X` a separated scheme of
finite type over `k` of dimension at most one. Then `H^q_étale(X, M̲)` is a finite `Λ`-module for
every `q`

1. if `n` is prime to the characteristic of `k`, and
2. if `X` is proper over `k`.

The two parts are the two sides of the disjunction `n.Coprime (ringExpChar k) ∨ IsProper π`; the
exponential characteristic makes the coprimality condition vacuous in characteristic zero, as in
the source. This is
`Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf` with its
input, the statement of Tag 03SC, discharged by
`Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds`. -/
@[stacks 0GJC "both parts: n prime to char(k), or X proper"]
theorem finite_etaleCohomology_constantSheaf
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (n : ℕ) (hn : 0 < n)
    (hM : ∀ m : M, n • m = 0) (hnp : n.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) :=
  module_finite_etaleCohomology_constantSheaf.{u, r} Λ curveTorsionCohomologyStatement_holds.{u, r}
    π hX M n hn hM hnp q

end TorsionModules

end Stacks.EtaleCohomology

end
