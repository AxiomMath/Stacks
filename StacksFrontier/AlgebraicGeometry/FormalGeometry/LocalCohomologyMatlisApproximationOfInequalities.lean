module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisDualModel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemEssentialConstancy

/-!
# Stacks 0EHK: approximating a local cohomology system by a Matlis dual

In Situation 0EHC, let `(M_n)` be an inverse system of `A`-modules as in Stacks 0DXT with
corresponding object `(ℱ_n)` of `Coh(U, I𝒪_U)`, let `d ≥ cd(A, I)` and `s ≥ 0`, and assume that
`A` is local with maximal ideal `𝔪 = 𝔞`, that `A` has a dualizing complex, and that `(ℱ_n)`
satisfies the `(s, s + d)`-inequalities. For an injective hull `E` of the residue field and
`i ≤ s` there are a finite `A`-module `N` annihilated by a power of `I` and, for `n ≫ 0`,
compatible maps `H^i_𝔪(M_n) → Hom_A(N, E)` with cokernels of finite length and kernels `K_n`
such that the image of `K_{n''} → K_{n'}` has finite length for `n'' ≫ n' ≫ 0`.

## Proof

This is the source's proof: a dualizing complex is normalized by a shift, the system
`Ext^{-i}_A(M_n, ω_A^∙)` (`Stacks.Algebraization.dualizingExtSystem`) is essentially constant
modulo finite length under the inequalities
(`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem`, the
localize-complete-and-bootstrap paragraphs of the source), and local duality with Matlis duality
turns that into the statement
(`Stacks.Algebraization.exists_matlisDual_approximation_of_isEssentiallyConstant`).

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EHK.** In the situation of Stacks 0EHC, let `(M_n)` be an inverse
system of `A`-modules as in Stacks 0DXT and let `(ℱ_n)` be the corresponding object of
`Coh(U, I𝒪_U)`. Let `d ≥ cd(A, I)` and `s ≥ 0` be integers, and assume that `A` is local with
maximal ideal `𝔪 = 𝔞`, that `A` has a dualizing complex, and that `(ℱ_n)` satisfies the
`(s, s + d)`-inequalities. Let `E` be an injective hull of the residue field of `A`. Then for
`i ≤ s` there is a finite `A`-module `N` annihilated by a power of `I` and, for `n ≫ 0`,
compatible maps `H^i_𝔪(M_n) → Hom_A(N, E)` whose cokernels have finite length and whose kernels
`K_n` form an inverse system in which the image of `K_{n''} → K_{n'}` has finite length for
`n'' ≫ n' ≫ 0`. -/
@[stacks 0EHK]
public theorem exists_matlisDual_approximation_localCohomologySystem_of_inequalities
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M) (d s : ℤ)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    (ιE : IsLocalRing.ResidueField S.A →ₗ[S.A] E) [Mono (ModuleCat.ofHom ιE)]
    (hιE : Module.IsInjectiveHull (ModuleCat.ofHom ιE))
    (hmaximal : IsLocalRing.maximalIdeal S.A = S.a)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hineq : SatisfiesDepthInequalities S
      (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hs : 0 ≤ s) :
    ∀ i : ℤ, i ≤ s →
      ∃ (N : ModuleCat.{u} S.A) (n₀ : ℕ)
        (φ : ∀ n : ℕ,
          (localCohomologySystem S M i).obj (op (n₀ + n)) →ₗ[S.A] (N →ₗ[S.A] E)),
        Module.Finite S.A N ∧
        (∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A N) = ⊥) ∧
        (∀ (m n : ℕ) (h : m ≤ n),
          φ m ∘ₗ ((localCohomologySystem S M i).map
            (homOfLE (Nat.add_le_add_left h n₀)).op).hom = φ n) ∧
        (∀ n : ℕ, IsFiniteLength S.A ((N →ₗ[S.A] E) ⧸ LinearMap.range (φ n))) ∧
        (∀ m : ℕ, ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
          IsFiniteLength S.A
            (Submodule.map ((localCohomologySystem S M i).map
              (homOfLE (Nat.add_le_add_left hmn n₀)).op).hom (LinearMap.ker (φ n)))) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal S.A))
  obtain ⟨K, hK⟩ := hdualizing
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} K hK
  exact exists_matlisDual_approximation_of_isEssentiallyConstant S M hM d s E ιE hιE hmaximal f hf
    (K⟦-m⟧) hm hineq hcd hs
    (isEssentiallyConstantModFiniteLength_dualizingExtSystem S M hmaximal hM d s (K⟦-m⟧) hm hineq
      hcd)

end Stacks.Algebraization

end
