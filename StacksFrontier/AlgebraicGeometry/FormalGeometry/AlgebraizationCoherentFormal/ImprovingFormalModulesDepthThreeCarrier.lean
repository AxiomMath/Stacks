module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeImprovementConditions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThreeCanonical
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoCarrier

/-!
# Improving coherent formal modules to depth three on `U`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`. Assume `A` has a dualizing complex, let `d ≥ cd(A, I)`, and let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)` satisfying the `(2, 2 + d)`-inequalities.

This file proves [Stacks, Tag 0EJG]: there is a map `(ℱₙ) ⟶ (ℱ''ₙ)` of inverse systems of
coherent `𝒪_U`-modules such that

1. `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` for all `y ∈ U ∩ Y`;
2. `(ℱ''ₙ)` is pro-isomorphic to an object `(ℋₙ)` of `Coh(U, I𝒪_U)`;
3. the induced morphism `(ℱₙ) ⟶ (ℋₙ)` of `Coh(U, I𝒪_U)` has kernel and cokernel annihilated by
   a power of `I`;
4. `H⁰(U, ℱ''ₙ)` and `H¹(U, ℱ''ₙ)` are finite `A`-modules for all `n`.

## Main results

* `Stacks.Algebraization.exists_proIso_coherentAdicSystem_depthThreeImprovedSystem`:
  [Stacks, Tag 0EJG].

## Implementation notes

The system `(ℱ''ₙ)` is `Stacks.Algebraization.depthThreeImprovedSystem`, the depth-two improvement
of [Stacks, Tag 0EJF] on `U` along `T = {δ^Y_Z ≤ 2}` and `T' = {δ^Y_Z ≤ 1}`. Conclusions (2) and
(3) are `Stacks.Algebraization.exists_proIso_coherentAdicSystem_canonicalImprovedSystem` applied on
`U`, whose hypotheses (a)-(e) are discharged in `DepthThreeImprovementConditions.lean` and
`DepthThreeImprovementInputs.lean` from the dualizing complex of `A`, the bound `cd(A, I) ≤ d` and
the `(2, 2 + d)`-inequalities. Conclusions (1) and (4) are proved in
`ImprovingFormalModulesDepthThreeCanonical.lean`. The kernel and cokernel in conclusion (3) are
given both in the abelian category `Coh(U, I𝒪_U)` and termwise in `𝒪_U`-modules
(`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower`).

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open Stacks.LocalCohomology

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **[Stacks, Tag 0EJG].** Let `A` have a dualizing complex, let `d ≥ cd(A, I)` and let
`(ℱₙ)` in `Coh(U, I𝒪_U)` satisfy the `(2, 2 + d)`-inequalities. Then there is a map
`(ℱₙ) ⟶ (ℱ''ₙ)` of inverse systems of coherent `𝒪_U`-modules with
(1) `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` on `U ∩ Y`, (2) `(ℱ''ₙ)` pro-isomorphic to an object
`(ℋₙ)` of `Coh(U, I𝒪_U)`, compatibly with the maps from `(ℱₙ)`, (3) the induced morphism
`(ℱₙ) ⟶ (ℋₙ)` with kernel and cokernel annihilated by a power of `I`, both in `Coh(U, I𝒪_U)`
and termwise, and (4) `Hᵖ(U, ℱ''ₙ)` a finite `A`-module for `p ≤ 1` and all `n`. -/
@[stacks 0EJG]
public theorem exists_proIso_coherentAdicSystem_depthThreeImprovedSystem
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (d : ℤ) (hd : cohomologicalDimension S.A S.I (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (h : SatisfiesDepthInequalities S F 2 (2 + d)) :
    ∃ (F'' : ℕᵒᵖ ⥤ S.U.toScheme.Modules) (τ : F.obj ⟶ F''),
      (∀ n : ℕᵒᵖ, (F''.obj n).IsCoherent) ∧
      (∀ (n : ℕᵒᵖ) (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
            (maximalIdeal (S.U.toScheme.presheaf.stalk y)) ((F''.obj n).presheaf.stalk y) +
          S.distanceToZ z) ∧
      (∃ (H : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
        (e : InverseSequence.ProIso F'' H.obj) (σ : F ⟶ H),
        (∀ n : ℕ, τ.app (op (e.α n)) ≫ e.φ n =
          F.obj.map (homOfLE (e.αle n)).op ≫ σ.hom.app (op n)) ∧
        (∃ c : ℕ, ∀ n : ℕ,
          idealPowerMultiple (idealOnOpen S) c ((kernel σ).obj.obj (op n)) = ⊥) ∧
        (∃ c : ℕ, ∀ n : ℕ,
          idealPowerMultiple (idealOnOpen S) c ((cokernel σ).obj.obj (op n)) = ⊥) ∧
        IsKernelCokernelAnnihilatedByPower (idealOnOpen S) σ.hom) ∧
      (∀ (n : ℕᵒᵖ) (p : ℕ), p ≤ 1 →
        Module.Finite S.A ((complementSheafCohomology S.A S.a p).obj (F''.obj n))) := by
  obtain ⟨-, -, H, e, σ, hcomp, hker, hcoker, hlev⟩ :=
    exists_proIso_coherentAdicSystem_canonicalImprovedSystem
      (S.hasDualizingComplexOnAffineCover_U hdual) F
      (S.stableUnderSpecialization_distanceToZSublevel 2)
      (S.stableUnderSpecialization_distanceToZSublevel 1)
      (S.distanceToZSublevel_subset_support 2)
      (fun y ⟨z, hyz, hz⟩ => ⟨z, hyz, hz.trans (by norm_num)⟩) d.toNat
      (fun y => (S.exists_affineOpen_cohomologicalDimension_idealOnOpen_le d hd y).imp
        fun _ hV => ⟨hV.1, hV.2 _⟩)
      (pos_completedStalkDepth_of_satisfiesDepthInequalities S F (2 + d) h)
      (completedStalkDepth_of_satisfiesDepthInequalities S F d hd h)
      (one_lt_completedStalkDepth_of_satisfiesDepthInequalities S F (2 + d) h)
      (S.forall_mem_distanceToZSublevel_two_of_isImmediateSpecialization hdual)
  exact ⟨depthThreeImprovedSystem S hdual F, toDepthThreeImprovedSystem S hdual F,
    isCoherent_depthThreeImprovedSystem_obj S hdual F,
    three_le_depth_add_distanceToZ_depthThreeImprovedSystem S hdual F,
    ⟨H, e, σ, hcomp, hker, hcoker, hlev⟩,
    finite_complementSheafCohomology_depthThreeImprovedSystem S hdual F⟩

end Stacks.Algebraization

end
