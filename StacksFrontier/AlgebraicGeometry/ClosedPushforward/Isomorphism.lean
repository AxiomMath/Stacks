module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase

/-!
# Pushing forward along an isomorphism of schemes

For an isomorphism `f : Y ⟶ Z` of schemes the unit `N ⟶ f_*f^*N` of the pullback–pushforward
adjunction is an isomorphism, and consequently the global sections of `N` are the global
sections of `f^*N` with their scalars restricted along `f^\#`.

## Main results

* `Stacks.ClosedImmersion.unitIsoOfIsIso`: `N ≅ f_*f^*N` for `f` an isomorphism.
* `Stacks.ClosedImmersion.sectionsIsoPullbackOfIsIso`: `Γ(Z, N) ≅ Γ(Y, f^*N)`.

## Implementation notes

An isomorphism of schemes is a closed immersion whose ideal sheaf vanishes, so the first
statement is `Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero` ([Stacks, Tag 08KS]) with
its hypothesis discharged. The second statement composes it with
`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, under which the sections of a direct
image over the whole target are the sections of the source.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsIso f] (N : Z.Modules)

/-- For an isomorphism of schemes `f`, a section `a` of `𝒪_Z` over `U` with `f^\# a = 0`
annihilates every section of an `𝒪_Z`-module `N` over `U`. -/
theorem smul_eq_zero_of_isIso :
    ∀ (U : Z.Opens) (a : Γ(Z, U)), (f.app U).hom a = 0 → ∀ m : Γ(N, U), a • m = 0 := by
  intro U a ha m
  have : IsIso (f.app U) :=
    Scheme.Hom.isIso_app f U (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  obtain rfl : a = 0 :=
    (ConcreteCategory.bijective_of_isIso (f.app U)).1 (ha.trans (map_zero (f.app U).hom).symm)
  simp

/-- **Along an isomorphism of schemes the unit of `f^* ⊣ f_*` is an isomorphism**: `N ≅ f_*f^*N`
for every `𝒪_Z`-module `N`. -/
def unitIsoOfIsIso : N ≅ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) :=
  haveI := isIso_unit_app_of_smul_eq_zero f N (smul_eq_zero_of_isIso f N)
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)

/-- **Global sections are carried across an isomorphism of schemes by pullback**: `Γ(Z, N)` is
`Γ(Y, f^*N)` with its scalars restricted along `f^\# : Γ(Z, 𝒪_Z) ⟶ Γ(Y, 𝒪_Y)`. -/
def sectionsIsoPullbackOfIsIso :
    (Stacks.Cohomology.sectionsFunctor Z ⊤).obj N ≅
      (ModuleCat.restrictScalars f.appTop.hom).obj
        ((Stacks.Cohomology.sectionsFunctor Y ⊤).obj ((Scheme.Modules.pullback f).obj N)) :=
  (Stacks.Cohomology.sectionsFunctor Z ⊤).mapIso (unitIsoOfIsIso f N) ≪≫
    (Stacks.Cohomology.AffineBase.pushforwardSectionsIso f).app
      ((Scheme.Modules.pullback f).obj N)

end Stacks.ClosedImmersion

end
