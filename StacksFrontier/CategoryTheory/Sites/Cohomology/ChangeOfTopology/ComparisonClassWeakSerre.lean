module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison class on the finer site is a weak Serre subcategory

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in the situation of Stacks
0EZ3, let `X` be an object of `C` and write `ε_X : C_τ/X ⟶ C_{τ'}/X` for the change-of-topology
morphism. The class `𝒜_X ⊂ Ab(C_τ/X)` of Stacks 0EZ9 consists of the sheaves `ε_X^{-1}ℱ'` with
`ℱ'` in the given weak Serre class `𝒜'_X ⊂ Ab(C_{τ'}/X)`.

This file prepares the first assertion of Stacks 0EZG, that `𝒜_X` is again a weak Serre
subcategory, which is proved in `DerivedComparisonEquivalence`.

## Main results

* `Stacks.ComparingTopologies.kernelCoimageShortExact` and
  `Stacks.ComparingTopologies.coimageCokernelShortExact`: the two short exact sequences into
  which a map of an abelian category factors.
* `CohomologyComparison.abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre`: every
  sheaf of `𝒜_X` is right acyclic for `ε_{X,*}`.

## The argument

Membership in `𝒜_X` is detected by `ε_{X,*}` (`fineWeakSerre_iff_weakSerre_pushforward`), so the
closure properties of `𝒜_X` are transported from those of `𝒜'_X` along that functor. For
kernels this needs only left exactness of `ε_{X,*}`. For cokernels and extensions it needs
`ε_{X,*}` to carry a short exact sequence whose outer terms lie in `𝒜_X` to a short exact
sequence, which is Stacks 015D once those terms are right acyclic; and right acyclicity of a
sheaf of `𝒜_X` is exactly the vanishing condition `(V_n)` of the situation in every degree. A
cokernel is reached in two steps through the coimage, because the kernel of the map — which the
previous step has already placed in `𝒜_X` — is what makes the first of the two sequences
usable.

## Hypotheses

The statement below carries `hV : ∀ n, S.vanishingCondition n`; that condition is proved in
`HigherDirectImageVanishing` (`CohomologyComparison.vanishingCondition_all`), and the first
assertion of Stacks 0EZG, which uses it, is in `DerivedComparisonEquivalence`.

## References

* [Stacks Project, Tag 0EZG](https://stacks.math.columbia.edu/tag/0EZG)
* [Stacks Project, Tag 0EZ9](https://stacks.math.columbia.edu/tag/0EZ9)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

/-- The short complex `ker f ⟶ M ⟶ coim f`. -/
noncomputable abbrev kernelCoimageShortComplex
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    ShortComplex A :=
  ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (by simp)

/-- The short complex `ker f ⟶ M ⟶ coim f` is short exact. -/
theorem kernelCoimageShortExact
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    (kernelCoimageShortComplex f).ShortExact :=
  .mk' ((kernelCoimageShortComplex f).exact_of_g_is_cokernel
    (cokernelIsCokernel (kernel.ι f))) inferInstance inferInstance

/-- The short complex `coim f ⟶ N ⟶ coker f`. -/
noncomputable abbrev coimageCokernelShortComplex
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    ShortComplex A :=
  ShortComplex.mk (Abelian.factorThruCoimage f) (cokernel.π f) (by
    apply (cancel_epi (Abelian.coimage.π f)).1
    rw [← Category.assoc, Abelian.coimage.fac, cokernel.condition]
    simp)

/-- The short complex `coim f ⟶ N ⟶ coker f` is short exact. -/
theorem coimageCokernelShortExact
    {A : Type*} [Category A] [Abelian A] {M N : A} (f : M ⟶ N) :
    (coimageCokernelShortComplex f).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk f (cokernel.π f) (by simp))
      (S₂ := coimageCokernelShortComplex f)
      { τ₁ := Abelian.coimage.π f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [coimageCokernelShortComplex]
        comm₂₃ := by simp [coimageCokernelShortComplex] }).1
      (ShortComplex.exact_cokernel f)
  all_goals infer_instance

namespace CohomologyComparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A sheaf of `𝒜_X` is right acyclic for the change-of-topology direct image.** This is the
vanishing condition `(V_n)` of the situation of Stacks 0EZ3 in every degree, read through the
criterion of Stacks 015C for a left exact functor. -/
theorem abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre
    (S : CohomologyComparison C) (hV : ∀ n : ℕ, S.vanishingCondition n) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.fineWeakSerre X F) :
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightAcyclic F := by
  apply ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X) F).2
      inferInstance).mpr
  intro i hi
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ p F).1
    (hV p X F hF p (by exact_mod_cast hi) le_rfl)

end CohomologyComparison

end Stacks.ComparingTopologies

end
