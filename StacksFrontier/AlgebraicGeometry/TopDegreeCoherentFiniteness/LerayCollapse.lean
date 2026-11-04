module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic

/-!
# Cohomology over a field along a morphism with vanishing higher direct images

Let `π : Y ⟶ Z` be a morphism of schemes and `M` an `𝒪_Y`-module whose higher direct images
`Rᵠ π_* M` vanish for `q > 0`. The Leray spectral sequence ([Stacks, Tag 01F4]) then collapses:
`Hⁿ(Y, M) ≅ Hⁿ(Z, π_* M)`. This file records that isomorphism as an isomorphism of `k`-vector
spaces for a scheme `Z` over a field `k`.

The argument is the one of `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`
([Stacks, Tag 089W]) with its acyclicity input replaced: there the vanishing of the higher
direct images comes from `π` being affine and `M` quasi-coherent, here it is the hypothesis.

## Main definitions

* `AlgebraicGeometry.TopDegreeFiniteness.cohomologyIsoPushforwardOfRightAcyclic`: the comparison
  of `Γ(Z, ⊤)`-modules.
* `AlgebraicGeometry.TopDegreeFiniteness.cohomologyOverFieldPushforwardIsoOfRightAcyclic`: the
  comparison of `k`-vector spaces.

## Main results

* `TopDegreeFiniteness.finiteDimensional_cohomologyOverField_pushforward_of_isZero`: finite
  dimensionality transports from `Hⁿ(Y, M)` to `Hⁿ(Z, π_* M)` when the higher direct images of
  `M` vanish.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase (moduleGlobalSections)

universe u

namespace AlgebraicGeometry.TopDegreeFiniteness

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)

/-- **The collapse of the Leray spectral sequence at a module acyclic for the direct image**, as
modules over `Γ(Z, ⊤)`. If `M` is right acyclic for `π_*`, the cohomology of `M` on `Y`, with
scalars restricted along `π^♯`, is the cohomology of `π_* M` on `Z`. -/
def cohomologyIsoPushforwardOfRightAcyclic (M : Y.Modules)
    (hM : (Scheme.Modules.pushforward π).rightAcyclic M) (n : ℕ) :
    (ModuleCat.restrictScalars π.appTop.hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj M) ≅
      ((moduleGlobalSections Z).rightDerived n).obj ((Scheme.Modules.pushforward π).obj M) :=
  Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso π M n ≪≫
    Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso (Scheme.Modules.pushforward π)
      (moduleGlobalSections Z)
      (Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj π)
      M hM n

variable (k : Type u) [Field k]

/-- **The collapse of the Leray spectral sequence, over a field.** For `π : Y ⟶ Z`, a structure
morphism `g : Z ⟶ Spec k` and a module `M` on `Y` right acyclic for `π_*`, the `k`-linear
isomorphism `Hⁿ(Y, M) ≅ Hⁿ(Z, π_* M)`. -/
def cohomologyOverFieldPushforwardIsoOfRightAcyclic (g : Z ⟶ Spec (.of k)) (M : Y.Modules)
    (hM : (Scheme.Modules.pushforward π).rightAcyclic M) (n : ℕ) :
    cohomologyOverField k (π ≫ g) M n ≅
      cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) n :=
  ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom
      (π.app (⊤ : Z.Opens)).hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ g).appLE ⊤ ⊤ (by simp)).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, Scheme.Hom.appLE_comp_top π g (by simp) (by simp)]
        rfl) _ ≪≫
    (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (cohomologyIsoPushforwardOfRightAcyclic π M hM n)

/-- **Finite dimensionality transports along a morphism with vanishing higher direct images.**
If `Rᵠ π_* M = 0` for every `q > 0` and `Hⁿ(Y, M)` is finite-dimensional over `k`, so is
`Hⁿ(Z, π_* M)`. This is [Stacks, Tag 01F4] part (1) over `k`. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_isZero (g : Z ⟶ Spec (.of k))
    (M : Y.Modules)
    (hM : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward π).rightDerived q).obj M))
    (n : ℕ) (h : FiniteDimensional k (cohomologyOverField k (π ≫ g) M n)) :
    FiniteDimensional k (cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) n) :=
  Module.Finite.equiv (cohomologyOverFieldPushforwardIsoOfRightAcyclic π k g M
    ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ M).2 hM) n).toLinearEquiv

end AlgebraicGeometry.TopDegreeFiniteness

end
