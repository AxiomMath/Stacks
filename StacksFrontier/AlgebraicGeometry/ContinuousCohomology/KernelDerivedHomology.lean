module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteInternalHom
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariants
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeDual
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedHomologyDelta

/-!
# Derived continuous homology `LH₀(G, M)` in `D(Λ[[Q]])`

Let `Λ` be a finite ring, not necessarily commutative, and `π : Γ → Q` a continuous surjection of
profinite groups with kernel `G`. For a finite `Λ`-module `M` with a continuous action of `Γ`,
this file defines

`LH₀(G, M) = (RH⁰(G, M^∨))^∨ ∈ D(Λ[[Q]])`,

where `M^∨ = Hom(M, ℚ/ℤ)` is the character dual (a finite `Λᵐᵒᵖ`-module with continuous
`Γ`-action), `RH⁰(G, -) : D⁺(discrete Λᵐᵒᵖ-Γ-modules) ⥤ D⁺(discrete Λᵐᵒᵖ-Q-modules)` is the
derived functor of the `G`-invariants (`Stacks.GroupCohomology.derivedKernelInvariants`), and the
outer dual is the derived contragredient `Hom(-, ℚ/ℤ)` of discrete `Λᵐᵒᵖ`-`Q`-modules, which takes
values in modules over `(Λᵐᵒᵖ)ᵐᵒᵖ[[Q]] = Λ[[Q]]`
(`Stacks.ContinuousCohomology.derivedContragredient`).

## Why this is the source's `LH₀(G, M) = M ⊗^L_{Λ[[G]]} Λ` in `D(Λ[[Ẑ]])`

[Stacks, Tag 03VM] writes `LH₀(π₁(X_k̄, η̄), M(-1)) = M(-1) ⊗^L_{Λ[[π₁(X_k̄, η̄)]]} Λ` in
`D(Λ[[Ẑ]])`, `Ẑ = Gal(k̄/k)` for `k` finite. In the notes on homology of the source (`trace.tex`,
lines 3163–3188) the homology `H_i(G, M)` is the derived functor of the coinvariants on the
category of profinite (pseudocompact) continuous `G`-modules, which has enough projectives
(Section 03VI), identified with `Tor_i^{Λ[[G]]}(M, Λ)`, and there are derived functors `LH₀(G, -)`
with values in modules over `Γ / G`. The character dual `M ↦ M^∨` is an exact anti-equivalence
between profinite and discrete torsion modules ("trivial duality", Section 03VI) which exchanges
coinvariants and invariants, `((M^∨)^G)^∨ = M_G`, and projective profinite modules with injective
discrete ones. Hence the left derived functor of the coinvariants on profinite modules is the dual
of the right derived functor of the invariants on discrete modules, which is the definition here;
the residual action of `Γ / G = Q` is carried along, so the result is a complex of
`Λ[[Q]]`-modules. Its cohomology is `H^{-i}(LH₀(G, M)) = (Hⁱ(G, M^∨))^∨ = H_i(G, M)`
(`Stacks.ContinuousCohomology.kernelDerivedHomologyHomologyIso`).

The abstract `Tor` over the ring `Λ[[G]]` (`Stacks.GroupHomology.derivedCoinvariants`), the
source's identification `H_i(G, M) = Tor_i^{Λ[[G]]}(M, Λ)` read literally, is not used here.
`π₁(X_k̄, η̄)` of an affine curve in characteristic `p > 0` is not topologically finitely
generated, and then the square of the augmentation ideal `I` of `Λ[[G]]` need not be closed, so
the abstract `Tor₁ = I/I²` is larger than `H₁(G, Λ) = lim_U I_U / I_U²`: this happens for
`G = (ℤ/p)^ℕ` (`Stacks.GroupHomology.exists_forall_eval_mem_and_not_mem_augmentationIdealSq`).
For `G` topologically finitely generated the two agree in degree one with `M = Λ`
(`Stacks.GroupHomology.augmentationIdeal_comparison`).

## Main definitions

* `Stacks.ContinuousCohomology.kernelDerivedHomology`: `M ↦ LH₀(G, M)`.

## Main results

* `Stacks.ContinuousCohomology.kernelDerivedHomologyHomologyIso`: `H^{-n}(LH₀(G, M))` is the
  contragredient of `Rⁿ H⁰(G, -)(M^∨)`, naturally in `M`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace Stacks.ContinuousCohomology

open Stacks.GroupCohomology Stacks.GroupHomology

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for continuous discrete modules at the module universe of the group,
pinned. -/
local instance (priority := 3000) enoughInjectives_continuousModule_kernelDerivedHomology
    (Λ : Type) [Ring Λ] (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, w, w} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, w, 0} Λ G

variable (Λ : Type) [Ring Λ] [Finite Λ] {Γ : Type w} {Q : Type v} [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] (π : Γ →ₜ* Q) (hπ : Function.Surjective π)

/-- The ring isomorphism `Λ[[Q]] ≅ (Λᵐᵒᵖ)ᵐᵒᵖ[[Q]]`, along which the contragredient of a discrete
`Λᵐᵒᵖ`-module is read as a `Λ[[Q]]`-module. -/
def completedGroupAlgebraOpOp :
    CompletedGroupAlgebra Λ Q →+* CompletedGroupAlgebra Λᵐᵒᵖᵐᵒᵖ Q :=
  CompletedGroupAlgebra.mapCoeff (RingEquiv.opOp Λ).toRingHom

/-- **`M ↦ RH⁰(G, M^∨)`**, the derived invariants of the character dual, as a contravariant
functor into `D⁺` of discrete `Λᵐᵒᵖ`-`Q`-modules, read in the unbounded derived category. -/
def dualDerivedKernelInvariants :
    (FiniteTypeContinuousModule.{0, w, w} Λ Γ)ᵒᵖ ⥤
      DerivedCategory (Stacks.Injectives.ContinuousModule.{0, v, w} Λᵐᵒᵖ Q) :=
  let D₁ : (FiniteTypeContinuousModule.{0, w, w} Λ Γ)ᵒᵖ ⥤
      Stacks.Injectives.ContinuousModule.{0, w, w} Λᵐᵒᵖ Γ :=
    finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙ finiteTypeContinuousModuleι.{0, w, w} Λᵐᵒᵖ Γ
  let D₂ : Stacks.Injectives.ContinuousModule.{0, w, w} Λᵐᵒᵖ Γ ⥤
      DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, w, w} Λᵐᵒᵖ Γ) :=
    DerivedCategory.Plus.singleFunctor _ 0
  let D₃ : DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, w, w} Λᵐᵒᵖ Γ) ⥤
      DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{0, v, w} Λᵐᵒᵖ Q) :=
    derivedKernelInvariants.{0, w, v, w} Λᵐᵒᵖ π hπ
  D₁ ⋙ D₂ ⋙ D₃ ⋙ DerivedCategory.Plus.ι

/-- **The derived continuous homology `M ↦ LH₀(G, M) = (RH⁰(G, M^∨))^∨`** of finite `Λ`-modules
with a continuous `Γ`-action, `G` the kernel of `π`, valued in `D(Λ[[Q]])`. See the module
docstring for why this is the source's `M ⊗^L_{Λ[[G]]} Λ` with its residual action of `Q`. -/
def kernelDerivedHomology :
    FiniteTypeContinuousModule.{0, w, w} Λ Γ ⥤
      DerivedCategory (ModuleCat.{w} (CompletedGroupAlgebra Λ Q)) :=
  let L₁ : FiniteTypeContinuousModule.{0, w, w} Λ Γ ⥤
      (DerivedCategory (Stacks.Injectives.ContinuousModule.{0, v, w} Λᵐᵒᵖ Q))ᵒᵖ :=
    (dualDerivedKernelInvariants Λ π hπ).rightOp
  let L₂ : (DerivedCategory (Stacks.Injectives.ContinuousModule.{0, v, w} Λᵐᵒᵖ Q))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{w} (CompletedGroupAlgebra Λᵐᵒᵖᵐᵒᵖ Q)) :=
    derivedContragredient.{0, v, w} Λᵐᵒᵖ Q
  let L₃ : DerivedCategory (ModuleCat.{w} (CompletedGroupAlgebra Λᵐᵒᵖᵐᵒᵖ Q)) ⥤
      DerivedCategory (ModuleCat.{w} (CompletedGroupAlgebra Λ Q)) :=
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{v, v, w}
      (completedGroupAlgebraOpOp Λ (Q := Q))
    haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{v, v, w}
      (completedGroupAlgebraOpOp Λ (Q := Q))
    (ModuleCat.restrictScalars.{w} (completedGroupAlgebraOpOp Λ (Q := Q))).mapDerivedCategory
  L₁ ⋙ L₂ ⋙ L₃

/-- The cohomology of `RH⁰(G, M^∨)` in degree `n` is `Rⁿ H⁰(G, -)(M^∨)`. -/
def dualDerivedKernelInvariantsHomologyIso (n : ℕ) :
    dualDerivedKernelInvariants Λ π hπ ⋙
        DerivedCategory.homologyFunctor (Stacks.Injectives.ContinuousModule.{0, v, w} Λᵐᵒᵖ Q) n ≅
      finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙ finiteTypeContinuousModuleι.{0, w, w} Λᵐᵒᵖ Γ ⋙
        (kernelInvariantsFunctor.{0, w, v, w} Λᵐᵒᵖ π hπ).rightDerived n :=
  Functor.isoWhiskerLeft (finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙
      finiteTypeContinuousModuleι.{0, w, w} Λᵐᵒᵖ Γ)
    (Stacks.DerivedIndexing.rightDerivedIso
      (kernelInvariantsFunctor.{0, w, v, w} Λᵐᵒᵖ π hπ) n).symm

/-- **The cohomology of `LH₀(G, M)`**: `H^{-n}(LH₀(G, M)) ≅ (Rⁿ H⁰(G, -)(M^∨))^∨`, the
contragredient of the `n`-th continuous cohomology of `G` with coefficients in the discrete dual
`M^∨`, as `Λ[[Q]]`-modules, naturally in `M`. Forgetting the action of `Q` this is the homology
`H_n(G, M) = Hⁿ(G, M^∨)^∨` of [Stacks, Section 03VI]. -/
def kernelDerivedHomologyHomologyIso (n : ℕ) :
    kernelDerivedHomology Λ π hπ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{w} (CompletedGroupAlgebra Λ Q)) (-(n : ℤ)) ≅
      (finiteTypeContinuousModuleDual.{0, w, w} Λ Γ ⋙ finiteTypeContinuousModuleι.{0, w, w} Λᵐᵒᵖ Γ ⋙
        (kernelInvariantsFunctor.{0, w, v, w} Λᵐᵒᵖ π hπ).rightDerived n).rightOp ⋙
        contragredient.{0, v, w} Λᵐᵒᵖ Q ⋙ ModuleCat.restrictScalars (completedGroupAlgebraOpOp Λ) :=
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits.{v, v, w}
    (completedGroupAlgebraOpOp Λ (Q := Q))
  haveI := StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits.{v, v, w}
    (completedGroupAlgebraOpOp Λ (Q := Q))
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryHomologyFunctorIso
        (ModuleCat.restrictScalars.{w} (completedGroupAlgebraOpOp Λ (Q := Q)))
        (-(n : ℤ)))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (derivedContragredientHomologyIso.{0, v, w} Λᵐᵒᵖ Q (-(n : ℤ)) n (by omega)) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.rightOpComp _ _).symm ≪≫
        natIsoRightOp (dualDerivedKernelInvariantsHomologyIso Λ π hπ n).symm) _) _ ≪≫
    Functor.associator _ _ _

end Stacks.ContinuousCohomology

end
