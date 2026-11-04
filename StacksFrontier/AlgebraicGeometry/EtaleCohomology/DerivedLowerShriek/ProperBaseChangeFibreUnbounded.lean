module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# The stalks of `Rf_!` on unbounded complexes (Stacks 0GK0)

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄` over `Y`, let
`Λ` be a torsion ring and let `ȳ : Spec k ⟶ Y` be a geometric point, with fibre
`X_ȳ = X ×_Y Spec k`. [Stacks, Tag 0GK0] asserts a canonical isomorphism
`(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ})` for `K ∈ D⁺_tors(X_étale, Λ)`, or for `K ∈ D(X_étale, Λ)` when
`Λ` is torsion. The first case is
`Stacks.EtaleCohomology.compactlySupportedCohomologyBaseChangeIso`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLowerShriek/ProperBaseChange.lean`). This
file does the second case: as in the source, it is the unbounded base change isomorphism for
`Rf_!` ([Stacks, Tag 0F7L],
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`) for the square of the fibre,
followed by `RΓ(Spec k, -)`, which for `k` separably closed is the stalk at `ȳ`.

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyUnboundedBaseChangeIso`: [Stacks, Tag 0GK0]
  on `D(X_étale, Λ)` for a torsion ring `Λ`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupUnboundedBaseChangeIso`: the same on
  cohomology modules, `H^q((Rf_! K)_ȳ) ≅ H^q_c(X_ȳ, K|_{X_ȳ})`.

## References

* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {k : Type u} [Field k]
  {X Y X' : Scheme.{u}} {f : X ⟶ Y} {g : Spec (.of k) ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Spec (.of k)} [LocallyOfFiniteType f'] [QuasiCompact f'] [IsSeparated f']
  (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **Stacks Project, Tag 0GK0**, the case of `D(X_étale, Λ)` for a torsion ring `Λ`. For a
cartesian square of schemes with `Y' = Spec k` (for instance a geometric point
`ȳ : Spec k ⟶ Y`, `k` separably closed), a compactification `j` of `X` over `Y`, a ring `Λ` with
`m = 0` in `Λ` for some `m > 0`, and an arbitrary `K ∈ D(X_étale, Λ)`:
`RΓ(Spec k, g⁻¹ Rf_! K)`, which for `k` separably closed is the stalk `(Rf_! K)_ȳ`, is the
compactly supported cohomology `RΓ_c(X', (g')⁻¹ K)` of the fibre `X' = X ×_Y Spec k`, computed
with the base change of `j`. Together with
`Stacks.EtaleCohomology.compactlySupportedCohomologyBaseChangeIso` (the case of
`D⁺_tors(X_étale, Λ)`) this is the whole tag. -/
@[stacks 0GK0 "(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ}) for K ∈ D(X_étale, Λ), Λ torsion",
  sga "4 XVII 5.2.2" "special case",
  sga "4 XVII 7.3.7" "special case",
  sga "4 XVIII 0.1" "special case",
  sga "4½ Arcata 4.5.4" "special case"]
def compactlySupportedCohomologyUnboundedBaseChangeIso
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).obj
        ((etaleModuleDerivedInverseImage.{u, 0} Λ g).obj
          ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K)) ≅
      (compactlySupportedCohomologyUnbounded.{u, 0} k f' (j.baseChange sq) Λ).obj
        ((etaleModuleDerivedInverseImage.{u, 0} Λ g').obj K) :=
  (etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).mapIso
    ((derivedLowerShriekUnboundedBaseChangeIso Λ hΛ sq j).app K)

/-- **Stacks Project, Tag 0GK0, on cohomology modules, on `D(X_étale, Λ)` for a torsion ring.**
Under the hypotheses of
`Stacks.EtaleCohomology.compactlySupportedCohomologyUnboundedBaseChangeIso`, for every `q`,
`H^q(RΓ(Spec k, g⁻¹ Rf_! K)) ≅ H^q_c(X', (g')⁻¹ K)`. -/
@[sga "4 XVII 7.3.7" "special case"]
def compactlySupportedCohomologyGroupUnboundedBaseChangeIso
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).obj
          ((etaleModuleDerivedInverseImage.{u, 0} Λ g).obj
            ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K))) ≅
      (compactlySupportedCohomologyGroupUnbounded.{u, 0} k f' (j.baseChange sq) Λ q).obj
        ((etaleModuleDerivedInverseImage.{u, 0} Λ g').obj K) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).mapIso
    (compactlySupportedCohomologyUnboundedBaseChangeIso Λ hΛ sq j K)

end Stacks.EtaleCohomology

end
