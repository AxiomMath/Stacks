module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for `Rf_!` (Stacks 0GL5)

Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact and quasi-separated schemes
and let `Λ` be a torsion ring. For `E` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`,
[Stacks, Tag 0GL5] asserts

`Rf_!E ⊗^L_Λ K = Rf_!(E ⊗^L_Λ f^{-1}K)`

in `D(Y_étale, Λ)`.

## Statement

`Rf_! = Rf̄_* ∘ j_!` is computed through a compactification `j : X ⟶ X̄` of `f` over `Y`, with
structure morphism `f̄ : X̄ ⟶ Y`, as everywhere in the repository
(`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`). The statement asserts that such a
compactification exists ([Stacks, Tag 0F41]) and that for **every** compactification `j` the
canonical map

`Rf_!E ⊗^L_Λ K ⟶ Rf_!(E ⊗^L_Λ f^{-1}K)`

of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedTensorMap` is an isomorphism. That map is
the projection map of [Stacks, Tag 0B56] for `f̄` at `j_!E`, followed by `Rf̄_*` of the
identification `j_!E ⊗^L_Λ f̄^{-1}K = j_!(E ⊗^L_Λ f^{-1}K)` of [Stacks, Tag 0GL1].

A torsion ring is one in which `n = 0` for some integer `n ≥ 1`.

## The proof

The source's. The identification of [Stacks, Tag 0GL1] is an isomorphism, so the map is
invertible as soon as the projection map of the proper morphism `f̄` is invertible at `(j_!E, K)`
(`Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedTensorMap_iff`); that projection map is
invertible exactly when the étale projection map of [Stacks, Tag 0943] is (both are read on the
constant ringed topoi), and that is [Stacks, Tag 0F0G]
(`Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isProper`).

## References

* [Stacks Project, Tag 0GL5](https://stacks.math.columbia.edu/tag/0GL5)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0GL5].** Let `f : X ⟶ Y` be a separated finite type morphism of quasi-compact
and quasi-separated schemes and let `Λ` be a torsion ring (`n = 0` in `Λ` for some `n ≥ 1`). Then
`f` has a compactification `j : X ⟶ X̄` over `Y`, and for every compactification `j`, every
`E ∈ D(X_étale, Λ)` and every `K ∈ D(Y_étale, Λ)` the canonical map
`Rf_!E ⊗^L_Λ K ⟶ Rf_!(E ⊗^L_Λ f^{-1}K)`, with `Rf_! = Rf̄_* ∘ j_!` computed through `j`, is an
isomorphism in `D(Y_étale, Λ)`. -/
@[stacks 0GL5]
theorem isIso_derivedLowerShriekUnboundedTensorMap (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n)
    (hΛ : (n : Λ) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (E : DerivedCategory (EtaleModules.{u, 0} Λ X))
        (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)),
        IsIso (derivedLowerShriekUnboundedTensorMap.{u, 0} Λ j E K) :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f, fun j E K =>
    (isIso_derivedLowerShriekUnboundedTensorMap_iff.{u, 0} Λ j E K).2
      ((isIso_etaleDerivedPushforwardTensorMap_iff.{u, 0} Λ j.toBase _ K).2
        ((isIso_etalePushforwardProjectionMap_iff.{u, 0} Λ j.toBase _ K).1
          (isIso_etalePushforwardProjectionMap_of_isProper Λ
            (fun a => isOfFinAddOrder_iff_nsmul_eq_zero.2
              ⟨n, hn, by rw [nsmul_eq_mul, hΛ, zero_mul]⟩) j.toBase _ K)))⟩

end Stacks.EtaleCohomology

end
