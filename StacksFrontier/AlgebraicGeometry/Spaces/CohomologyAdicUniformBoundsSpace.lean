module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CohomologyAdicUniformBoundsSpace

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAdicUniformBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Uniform bounds for the cohomology of the adic quotients of a coherent sheaf

In Situation 08AV — a Noetherian ring `A`, an ideal `I ⊆ A`, a proper morphism
`f : X ⟶ Spec A` of algebraic spaces and a coherent `𝒪_X`-module `F` — fix `p ≥ 0` and write
`M = Hᵖ(X, F)` and `Qₙ = Hᵖ(X, F / Iⁿ F)`.  [Stacks, Tag 08AY] has three clauses:

1. there is a `c₁ ≥ 0` with `ker (M ⟶ Qₙ) ⊆ Iⁿ⁻ᶜ¹ M` for all `n ≥ c₁`;
2. the inverse system `(Qₙ)` satisfies the Mittag-Leffler condition of [Stacks, Tag 02N0];
3. for every `n` there is a `c₂(n) ≥ n` with `im (Qₖ ⟶ Qₙ) = im (M ⟶ Qₙ)` for all `k ≥ c₂(n)`.

The algebraic part of the source's argument is carried out for abstract towers in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyAdicUniformBounds.lean`
(namespace `Stacks.AdicCohomologyBound`), from exactly the facts it uses as hypotheses.  This
file supplies those facts for the cohomology of an algebraic space: the long exact cohomology
sequences of `0 ⟶ Iⁿ F ⟶ F ⟶ F / Iⁿ F ⟶ 0` and their naturality in `n`, the uniform bounds of
[Stacks, Tag 08AX] for `Hᵖ` and `Hᵖ⁺¹`, and the finiteness of `Hᵖ⁺¹(X, Iⁿ F)`
([Stacks, Tag 08AS]); so the three clauses hold with nothing carried.

## Main definitions

This file defines nothing.  The statements below use the following definitions of the imported
module `StacksDraft.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.`
`CohomologyAdicUniformBoundsSpace`, which also proves the three clauses (namespace
`AlgebraicGeometry.Space.C1573`); this file restates them in the namespace
`AlgebraicGeometry.Space` and registers them.

* `AlgebraicGeometry.Space.C1573.idealQuotientTower`: the inverse system `n ↦ F / Iⁿ F`.
* `AlgebraicGeometry.Space.C1573.cohomologyIdealQuotientTower`: the inverse system
  `n ↦ Hᵖ(X, F / Iⁿ F)` of `A`-modules.
* `AlgebraicGeometry.Space.C1573.cohomologyIdealPowerDelta`: the connecting map
  `Hᵖ(X, F / Iⁿ F) ⟶ Hᵖ⁺¹(X, Iⁿ F)`.

## Main results

* `AlgebraicGeometry.Space.exists_ker_cohomologyIdealQuotientProj_le`,
  `AlgebraicGeometry.Space.isMittagLefflerCategorical_cohomologyIdealQuotientTower` and
  `AlgebraicGeometry.Space.exists_range_cohomologyIdealQuotientTr_eq`:
  **[Stacks, Tag 08AY]**, clauses (1), (2) and (3).

## Implementation notes

The threshold in clause (3) grows with `n`, as in the source: see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyAdicUniformBounds.lean`.

## References

* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

/-! ## The cohomology of an algebraic space -/

namespace AlgebraicGeometry.Space

open CategoryTheory.Limits Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] hasInjectiveResolutions_modules HasDerivedCategory.standard

section Situation

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA}

/-- **Stacks 08AY, clause (1).**  In Situation 08AV, for every `p` there is a `c₁ ≥ 0` such that
`ker (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F)) ⊆ Iⁿ⁻ᶜ¹ Hᵖ(X, F)` for all `n ≥ c₁`. -/
@[stacks 08AY "clause (1)"]
theorem exists_ker_cohomologyIdealQuotientProj_le [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      LinearMap.ker (C1573.cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p n) ≤
        I ^ (n - c₁) • (⊤ : Submodule A (cohomologyRes (baseRingHom A B hA X.1 X.2) p F)) :=
  C1573.exists_ker_cohomologyIdealQuotientProj_le f hf F I p

/-- **Stacks 08AY, clause (3).**  In Situation 08AV, for every `p` and every `n` there is a
`c₂(n) ≥ n` such that `im (Hᵖ(X, F / Iᵏ F) ⟶ Hᵖ(X, F / Iⁿ F)) = im (Hᵖ(X, F) ⟶ Hᵖ(X, F / Iⁿ F))`
for all `k ≥ c₂(n)`. -/
@[stacks 08AY "clause (3)"]
theorem exists_range_cohomologyIdealQuotientTr_eq [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p n : ℕ) :
    ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (C1573.cohomologyIdealQuotientTr (baseRingHom A B hA X.1 X.2) F I p h) =
        LinearMap.range (C1573.cohomologyIdealQuotientProj (baseRingHom A B hA X.1 X.2) F I p n) :=
  C1573.exists_range_cohomologyIdealQuotientTr_eq f hf F I p n

/-- **Stacks 08AY, clause (2).**  In Situation 08AV, for every `p` the inverse system
`(Hᵖ(X, F / Iⁿ F))ₙ` satisfies the Mittag-Leffler condition. -/
@[stacks 08AY "clause (2)"]
theorem isMittagLefflerCategorical_cohomologyIdealQuotientTower [IsNoetherianRing A]
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (I : Ideal A) (p : ℕ) :
    IsMittagLefflerCategorical
      (C1573.cohomologyIdealQuotientTower (baseRingHom A B hA X.1 X.2) F I p) :=
  C1573.isMittagLefflerCategorical_cohomologyIdealQuotientTower f hf F I p

end Situation

end AlgebraicGeometry.Space

end
