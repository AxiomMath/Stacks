module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.IntegralHomCohomologyCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the cohomology of `j_!M̲` on curves

Let `Λ` be a Noetherian ring, let `M` be a finite `Λ`-module annihilated by an integer `n > 0`,
let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
of dimension at most one, and let `j : U ⟶ X` be an open immersion. [Stacks, Tag 0GJF] says
that `H^q_étale(X, j_!M̲)` is a finite `Λ`-module for every `q`

1. if `n` is prime to the characteristic of `k`, and
2. if `X` is proper over `k`.

`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_constantSheaf`
proves this from two named inputs, Theorem 03SC (`h03SC`) and Lemma 0GJD (`h0GJD`). This file
discharges both and registers the tag.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_of_coprime` —
  **Stacks Tag 0GJF, part (1)**.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_of_isProper` —
  **Stacks Tag 0GJF, part (2)**.

## Implementation notes

* `h03SC` is `Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds`, the statement of
  Theorem 03SC proved from Situation 0A52's eight statements for torsion sheaves.
* `h0GJD` asks that a finite morphism `f` carry finiteness of `H^q(X, ℱ)` to finiteness of
  `H^q(Y, f_*ℱ)`. A finite morphism is integral, and for an integral morphism
  `Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso` identifies the
  two modules (Tag 03QP and the Leray collapse of Tag 0733), so finiteness transports along it.

The source's proof enlarges `U` to a dense open and applies Lemmas 0GJE and 0GJC; the base
proof used here instead runs the localization sequence of Tag 095L for the reduced closed
complement of `U` and applies Lemma 0GJC on `X` and on that complement. Either way the
statement is the source's.

As in the file of `Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds`, the global
instance `Stacks.EtaleCohomology.hasSheafifyEtale` (sheafification at the coefficient
universe `u + 1`) is switched off: tried for the coefficients `ModuleCat.{max (u + 1) r} Λ` it
leaves the unsolvable universe constraint `max r (u + 1) = u + 1` behind.

## References

* [Stacks Project, Tag 0GJF](https://stacks.math.columbia.edu/tag/0GJF)
* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
* [Stacks Project, Tag 0GJD](https://stacks.math.columbia.edu/tag/0GJD)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat

attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks Project, Tag 0GJF, part (1).** Let `Λ` be a Noetherian ring, let `M` be a finite
`Λ`-module annihilated by an integer `n > 0`, let `k` be an algebraically closed field, let `X`
be a separated scheme of finite type over `k` of dimension at most one, and let `j : U ⟶ X` be
an open immersion. If `n` is prime to the characteristic of `k`, then `H^q_étale(X, j_!M̲)` is a
finite `Λ`-module for every `q`.

Here `X` is a scheme with a separated, locally of finite type and quasi-compact structure
morphism `π : X ⟶ Spec k`, the dimension is the Krull dimension of the underlying space, `M̲` is
the constant sheaf of `Λ`-modules on `U_étale`, `j_!` is extension by zero and `H^q` is the
`q`-th right derived functor of global sections of sheaves of `Λ`-modules on `X_étale`. "Prime
to the characteristic" is read with the exponential characteristic, so that it is no condition
in characteristic zero. -/
@[stacks 0GJF "part (1): n prime to char(k)"]
theorem module_finite_cohomology_extensionByZero_of_coprime
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (n : ℕ) (hn : 0 < n)
    (hM : ∀ m : M, n • m = 0) (hnk : n.Coprime (ringExpChar k))
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :=
  module_finite_cohomology_extensionByZero_constantSheaf Λ
    curveTorsionCohomologyStatement_holds.{u, r}
    (by
      intros
      exact Module.Finite.equiv
        (moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ _ _ _).toLinearEquiv)
    π hX M n hn hM (Or.inl hnk) j q

/-- **Stacks Project, Tag 0GJF, part (2).** Let `Λ` be a Noetherian ring, let `M` be a finite
`Λ`-module annihilated by an integer `n > 0`, let `k` be an algebraically closed field, let `X`
be a separated scheme of finite type over `k` of dimension at most one, and let `j : U ⟶ X` be
an open immersion. If `X` is proper over `k`, then `H^q_étale(X, j_!M̲)` is a finite
`Λ`-module for every `q`.

Here `X` is a scheme with a separated, locally of finite type and quasi-compact structure
morphism `π : X ⟶ Spec k`, the dimension is the Krull dimension of the underlying space, `M̲` is
the constant sheaf of `Λ`-modules on `U_étale`, `j_!` is extension by zero and `H^q` is the
`q`-th right derived functor of global sections of sheaves of `Λ`-modules on `X_étale`. -/
@[stacks 0GJF "part (2): X proper over k"]
theorem module_finite_cohomology_extensionByZero_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsProper π]
    (hX : topologicalKrullDim X ≤ 1) (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M]
    (n : ℕ) (hn : 0 < n) (hM : ∀ m : M, n • m = 0)
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M))) :=
  module_finite_cohomology_extensionByZero_constantSheaf Λ
    curveTorsionCohomologyStatement_holds.{u, r}
    (by
      intros
      exact Module.Finite.equiv
        (moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ _ _ _).toLinearEquiv)
    π hX M n hn hM (Or.inr inferInstance) j q

end Stacks.EtaleCohomology.TorsionModules

end
