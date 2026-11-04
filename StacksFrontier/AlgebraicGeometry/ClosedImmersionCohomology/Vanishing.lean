module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent

/-!
# Cohomological vanishing transfers along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes. Cohomology does not change along it
(`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`), and a coherent `𝒪_X`-module
annihilated by the kernel of the comorphism of `i` is the direct image of a coherent `𝒪_Z`-module
([Stacks, Tag 087T], `AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero`).
Combining the two, **the cohomology of a coherent module supported on a closed subscheme may be
computed on that subscheme**, so a vanishing theorem available on `Z` applies to it.

## Main results

* `Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_of_isZero_pushforward`: if `M` is the
  direct image of `G` then `H^n(X, M)` vanishes as soon as `H^n(Z, G)` does. No coherence and no
  Noetherian hypothesis.
* `Stacks.Cohomology.ClosedImmersion.exists_isCoherent_pushforward_iso_isZero_of_smul_eq_zero`:
  **the vanishing of `H^n(X, M)` may be checked on `Z`**, for a coherent `M` annihilated by the
  kernel of the comorphism.

## Implementation notes

The cohomology on `X` is a module over `Γ(X, ⊤)` and the cohomology on `Z` a module over
`Γ(Z, ⊤)`; the comparison isomorphism lands in the restriction of scalars along `i.appTop`.
Vanishing crosses that restriction because `ModuleCat.restrictScalars` does not change the
carrier, so `CategoryTheory.Limits.IsZero` is `Subsingleton` of the same type on both sides
(`ModuleCat.isZero_iff_subsingleton`).

Both statements are in Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, which is the
indexing `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward` is stated in.
`Stacks.DerivedIndexing.rightDerivedIso` translates them to the `ℤ`-indexed `rightDerivedPlus`.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ClosedImmersion

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Vanishing transfers along a closed immersion.** If the `𝒪_X`-module `M` is the direct image
of the `𝒪_Z`-module `G`, then `H^n(X, M)` vanishes as soon as `H^n(Z, G)` does: the two agree up
to restriction of scalars along `i.appTop`, which does not change the carrier. -/
public theorem isZero_rightDerived_of_isZero_pushforward
    [AlgebraicGeometry.IsClosedImmersion i] {M : X.Modules} (G : Z.Modules)
    (e : (AlgebraicGeometry.Scheme.Modules.pushforward i).obj G ≅ M) (n : ℕ)
    (hz : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections Z).rightDerived n).obj G)) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).obj M) := by
  have hrs : IsZero ((ModuleCat.restrictScalars i.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections Z).rightDerived n).obj G)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    rw [ModuleCat.isZero_iff_subsingleton] at hz
    exact hz
  have h1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)) :=
    hrs.of_iso (cohomologyObjIsoPushforward i G n)
  exact h1.of_iso
    ((((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).mapIso e).symm)

/-- **The cohomology of a coherent module supported on a closed subscheme may be computed on that
subscheme.** For `M` coherent on `X` and annihilated section by section by the kernel of the
comorphism of the closed immersion `i`, there is a coherent `𝒪_Z`-module `G` with
`i_* G ≅ M` whose vanishing in degree `n` forces that of `H^n(X, M)`.

This is the composite of [Stacks, Tag 087T] on the essential image of `i_*` with
`Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_of_isZero_pushforward`. It is the step by
which the `H¹`-vanishing on the exceptional line of [Stacks, Tag 0EXD] is applied to the graded
pieces of the `𝓘`-adic filtration, which live on the modification rather than on the line. -/
public theorem exists_isCoherent_pushforward_iso_isZero_of_smul_eq_zero
    [AlgebraicGeometry.IsClosedImmersion i] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsCoherent]
    (h : ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0)
    (n : ℕ) :
    ∃ G : Z.Modules, G.IsCoherent ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G ≅ M) ∧
      (IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections Z).rightDerived n).obj G) →
        IsZero
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).obj M)) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_smul_eq_zero i M h
  exact ⟨G, hG, ⟨e⟩, fun hz => isZero_rightDerived_of_isZero_pushforward i G e n hz⟩

end Stacks.Cohomology.ClosedImmersion

end
