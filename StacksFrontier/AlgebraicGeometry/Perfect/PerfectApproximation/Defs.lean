module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-!
# Approximation by perfect complexes

Let `X` be a scheme, `T ⊆ X` a subset and `m` an integer. Approximation holds for the triple
`(T, E, m)`, where `E` is an object of the derived category of `𝒪_X`-modules, when there is a
perfect object `P` cohomologically supported on `T` together with a map `P ⟶ E` which is an
isomorphism on cohomology in every degree above `m` and an epimorphism on cohomology in
degree `m`.

The scheme `X` satisfies *approximation by perfect complexes* when for every closed subset `T`
with retrocompact complement there is an integer `r`, depending only on `T`, such that
approximation holds for `(T, E, m)` whenever `E` has quasi-coherent cohomology, is
`(m - r)`-pseudo-coherent, and has its cohomology supported on `T` in all degrees at
least `m - r`.

## Main definitions

* `AlgebraicGeometry.HasPerfectApproximation`: approximation holds for a triple `(T, E, m)`.
* `AlgebraicGeometry.HasApproximationByPerfectComplexes`: the scheme satisfies approximation by
  perfect complexes.

## Implementation notes

Both predicates are meaningful for an arbitrary subset and an arbitrary derived object, so
closedness and quasi-coherence are imposed by the statements that use them rather than by the
type of `AlgebraicGeometry.HasPerfectApproximation`. Support is the stalkwise cohomology-support
predicate `AlgebraicGeometry.CohomologySupportedOn`. Isomorphisms and surjections of cohomology
sheaves are expressed categorically by `CategoryTheory.IsIso` and `CategoryTheory.Epi`.

Both are abbreviations, so the existential data can be used directly by downstream statements
without a separate unfolding lemma. In the second definition the integer bound may depend on
the closed subset, but not on the derived object or on the approximation degree; support in
degrees at least `m - r` is spelled by vanishing of the cohomology stalks off the closed
subset, in the same form as `AlgebraicGeometry.CohomologySupportedOn`.

## References

* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Approximation holds for the triple `(T, E, m)`: there is a perfect object of the derived
category of `𝒪_X`-modules, cohomologically supported on `T`, mapping to `E` by a map which is an
isomorphism on cohomology in every degree above `m` and an epimorphism on cohomology in
degree `m`. -/
@[stacks 08EM]
abbrev HasPerfectApproximation (X : Scheme.{u}) (T : Set X)
    (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ) : Prop :=
  ∃ P : DerivedCategory.{u + 1} X.Modules,
    RingedSpace.IsPerfect (X := X.toRingedSpace) P ∧
      CohomologySupportedOn X.ringCatSheaf T P ∧
      ∃ α : P ⟶ E,
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor X.Modules i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor X.Modules m).map α)

/-- The scheme `X` satisfies approximation by perfect complexes: for every closed subset `T`
with retrocompact complement there is an integer `r` such that every sufficiently
pseudo-coherent derived object with quasi-coherent cohomology supported on `T` in high degrees
admits a perfect approximation. -/
@[stacks 08EN]
abbrev HasApproximationByPerfectComplexes (X : Scheme.{u}) : Prop :=
  ∀ T : Set X, IsClosed T → IsRetrocompact Tᶜ → ∃ r : ℤ,
    ∀ (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E (m - r) →
      (∀ (i : ℤ) (x : X), m - r ≤ i → x ∉ T →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) →
      HasPerfectApproximation X T E m

end AlgebraicGeometry

end
