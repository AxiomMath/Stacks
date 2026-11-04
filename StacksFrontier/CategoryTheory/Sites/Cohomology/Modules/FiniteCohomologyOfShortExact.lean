module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.Noetherian.Basic

/-!
# Finite cohomology in a short exact sequence of coefficient sheaves

Let `Λ` be a Noetherian ring and let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of
sheaves of `Λ`-modules on a site. If `H^q(ℱ₁)` and `H^q(ℱ₃)` are finite `Λ`-modules, then so is
`H^q(ℱ₂)`.

## Main results

* `Stacks.Cohomology.module_finite_cohomology_of_shortExact` — finiteness of the middle
  cohomology module.

## Implementation notes

Sheaves of `Λ`-modules are sheaves valued in `ModuleCat Λ`, and their cohomology is the right
derived functor of global sections. Only the exactness of `H^q(ℱ₁) ⟶ H^q(ℱ₂) ⟶ H^q(ℱ₃)` is
used, which is one segment of the long exact cohomology sequence
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`; nothing about the
underlying site enters, so the statement is for an arbitrary site. Over a Noetherian ring the
image of `H^q(ℱ₂)` in `H^q(ℱ₃)` is a submodule of a finite module, hence finite, and `H^q(ℱ₂)`
is an extension of it by a quotient of `H^q(ℱ₁)`.

## References

* [Stacks Project, Tag 0GJG](https://stacks.math.columbia.edu/tag/0GJG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w r

namespace Stacks.Cohomology

/-- **Stacks Project, Tag 0GJG.** In a short exact sequence of coefficient sheaves,
the middle sheaf has finite cohomology in degree `q` if both outer sheaves do. -/
@[stacks 0GJG]
public theorem module_finite_cohomology_of_shortExact
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify J (ModuleCat.{w} Λ)]
    [HasInjectiveResolutions (Sheaf J (ModuleCat.{w} Λ))]
    [HasGlobalSectionsFunctor J (ModuleCat.{w} Λ)]
    [(Sheaf.Γ J (ModuleCat.{w} Λ)).Additive]
    (S : ShortComplex (Sheaf J (ModuleCat.{w} Λ))) (hS : S.ShortExact)
    (q : ℕ)
    (h₁ : Module.Finite Λ (((Sheaf.Γ J (ModuleCat.{w} Λ)).rightDerived q).obj S.X₁))
    (h₃ : Module.Finite Λ (((Sheaf.Γ J (ModuleCat.{w} Λ)).rightDerived q).obj S.X₃)) :
    Module.Finite Λ (((Sheaf.Γ J (ModuleCat.{w} Λ)).rightDerived q).obj S.X₂) := by
  let : EnoughInjectives (Sheaf J (ModuleCat.{w} Λ)) := ⟨fun X => by
    let I := injectiveResolution X
    exact ⟨{ J := I.cocomplex.X 0
             injective := I.injective 0
             f := I.ι.f 0
             mono := mono_of_isLimit_fork I.isLimitKernelFork }⟩⟩
  let F := Sheaf.Γ J (ModuleCat.{w} Λ)
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  let : (F.rightDerived q).Additive := D.additive q
  let f := (F.rightDerived q).map S.f
  let g := (F.rightDerived q).map S.g
  have hrange : LinearMap.range f.hom = LinearMap.ker g.hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker (S.map (F.rightDerived q))).mp
      (D.exact_map hS q)
  let : IsNoetherian Λ ((F.rightDerived q).obj S.X₃) :=
    isNoetherian_of_isNoetherianRing_of_finite Λ _
  let : Module.Finite Λ (LinearMap.range g.hom) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.of_exact (R := Λ) (f := f.hom) (g := g.hom.rangeRestrict)
    (LinearMap.exact_iff.mpr ((LinearMap.ker_rangeRestrict _).trans hrange.symm))
    (by rw [← LinearMap.range_eq_top, LinearMap.range_rangeRestrict])

end Stacks.Cohomology

end
