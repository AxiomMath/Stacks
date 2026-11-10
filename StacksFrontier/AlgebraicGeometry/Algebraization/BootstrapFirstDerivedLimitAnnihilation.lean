module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapStableImageShift
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniformStableImage
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerFirstDerivedLimit

/-!
# Part (7) of Stacks 0EFY at a general specialization-stable locus

In Situation [Stacks, Tag 0EFU], for `n ≥ m₀` let

`Aₙ = ker(H^s_T(M/IⁿM) ⟶ H^s_T(M/I^{m₀}M))`.

If the stable-image assertion of [Stacks, Tag 0EFX] holds at `m₀`, the system `{Aₙ}` is
Mittag-Leffler, and so `I^{m₀}` annihilates `R¹lim H^s_T(M/IⁿM)`: this is part (7) of
[Stacks, Tag 0EFY] at a general specialization-stable `T`. Together with the other six parts it
gives [Stacks, Tag 0EFY] at a general specialization-stable `T`, with one `m₀` for all seven parts.

## Main results

* `Stacks.LocalCohomology.isMittagLefflerCategorical_adicTowerCollapseKernelTower_of_stableImage` —
  the Mittag-Leffler condition for `{Aₙ}` from the stable-image assertion of [Stacks, Tag 0EFX].
* `Stacks.Algebraization.exists_smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero` — part
  (7) of [Stacks, Tag 0EFY] at a general specialization-stable `T`.
* `Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons` — all seven parts of
  [Stacks, Tag 0EFY] at a general specialization-stable `T`, at one and the same `m₀`.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Two submodules of a subsingleton module are equal. -/
private theorem submodule_eq_of_subsingleton {X : ModuleCat.{u} A} [Subsingleton X]
    (P Q : Submodule A X) : P = Q :=
  le_antisymm
    (fun x _ => by rw [Subsingleton.elim x 0]; exact Q.zero_mem)
    (fun x _ => by rw [Subsingleton.elim x 0]; exact P.zero_mem)

/-- If the stable-image assertion of [Stacks, Tag 0EFX] for `H^{s+1}_T` holds at `m₀`, the
subsystem `Aₙ = ker(H^s_T(M/IⁿM) ⟶ H^s_T(M/I^{m₀}M))`, `n ≥ m₀`, is Mittag-Leffler: for `n ≥ m₀`
and all large `k` the image of `Aₖ ⟶ Aₙ` is `Aₙ ∩ image(H^s_T(M) ⟶ H^s_T(M/IⁿM))`. -/
theorem isMittagLefflerCategorical_adicTowerCollapseKernelTower_of_stableImage
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (s : ℤ) (m₀ : ℕ)
    (hstab : HasStableImageIdealPowerCohomology.{u, u} T I M (s + 1) m₀) :
    IsMittagLefflerCategorical (adicTowerCollapseKernelTower.{u, u} T I M s m₀) := by
  classical
  refine isMittagLefflerCategorical_of_range_eq_submodule
    (adicTowerCollapseKernelTower.{u, u} T I M s m₀)
    (fun i => if h : m₀ ≤ i then Classical.choose (hstab i h) else i)
    (fun i => by
      by_cases h : m₀ ≤ i
      · rw [dite_eq_left h]
        exact Classical.choose (Classical.choose_spec (hstab i h))
      · rw [dite_eq_right h])
    (fun i => Submodule.comap (adicTowerCollapseKernel.{u, u} T I M s m₀ i).subtype
      (LinearMap.range ((localCohomologyAdicCone.{u, u} A T I s M).π.app (op i)).hom))
    ?_
  intro i k hbk hik
  by_cases hm₀i : m₀ ≤ i
  · have hc := Classical.choose_spec (Classical.choose_spec (hstab i hm₀i))
    have hck : Classical.choose (hstab i hm₀i) ≤ k := by rwa [dite_eq_left hm₀i] at hbk
    have hm₀k : m₀ ≤ k := hm₀i.trans hik
    rw [range_adicTowerCollapseKernelTower_map_eq.{u, u} T I M s m₀ hm₀i hik]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy⟩ := hx
      have hyker : ((localCohomologyAdicTower.{u, u} A T I s M).map
          (homOfLE hm₀k).op).hom y = 0 := by
        rw [← inverseSystem_transition_comp_apply.{u, u}
          (localCohomologyAdicTower.{u, u} A T I s M) hm₀i hik y, hy]
        exact (mem_adicTowerCollapseKernel_iff.{u, u} T I M s m₀ hm₀i x.val).mp x.property
      have hnatap : ∀ {a b : ℕ} (hab : a ≤ b)
          (w : (localCohomologyAdicTower.{u, u} A T I s M).obj (op b)),
          (localCohomologyδ.{u, u} T (idealPowerShortComplex_shortExact.{u, u} I M a) s (s + 1)
              rfl).hom
            (((localCohomologyAdicTower.{u, u} A T I s M).map (homOfLE hab).op).hom w) =
          ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
            ((idealPowerTower.{u, u} I M).map (homOfLE hab).op)).hom
            ((localCohomologyδ.{u, u} T
              (idealPowerShortComplex_shortExact.{u, u} I M b) s (s + 1) rfl).hom w) :=
        fun hab w => ConcreteCategory.congr_hom
          (localCohomologyδ_idealPowerShortComplex_naturality.{u, u} T I M s (s + 1) rfl hab) w
      have hdm₀ : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
          ((idealPowerTower.{u, u} I M).map (homOfLE hm₀k).op)).hom
          ((localCohomologyδ.{u, u} T
            (idealPowerShortComplex_shortExact.{u, u} I M k) s (s + 1) rfl).hom y) = 0 := by
        rw [← hnatap hm₀k y, hyker]
        exact map_zero _
      have hdi : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
          ((idealPowerTower.{u, u} I M).map (homOfLE hik).op)).hom
          ((localCohomologyδ.{u, u} T
            (idealPowerShortComplex_shortExact.{u, u} I M k) s (s + 1) rfl).hom y) = 0 :=
        hc k hck _ (LinearMap.mem_ker.2 ((inverseSystem_transition_comp_apply.{u, u}
          (idealPowerTower.{u, u} I M ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)) hm₀i hik _).trans hdm₀))
      have hδx : (localCohomologyδ.{u, u} T
          (idealPowerShortComplex_shortExact.{u, u} I M i) s (s + 1) rfl).hom
          ((adicTowerCollapseKernel.{u, u} T I M s m₀ i).subtype x) = 0 := by
        rwa [← hy, hnatap hik y]
      exact (ShortComplex.moduleCat_exact_iff _).mp
        (localCohomology_exact₃.{u, u} T
          (idealPowerShortComplex_shortExact.{u, u} I M i) s (s + 1) rfl) _ hδx
    · obtain ⟨z, hz⟩ := hx
      exact ⟨((localCohomologyAdicCone.{u, u} A T I s M).π.app (op k)).hom z,
        (ConcreteCategory.congr_hom
          ((localCohomologyAdicCone.{u, u} A T I s M).w (homOfLE hik).op) z).trans hz⟩
  · have : Subsingleton ((adicTowerCollapseKernelTower.{u, u} T I M s m₀).obj (op i)) := by
      change Subsingleton ↥(adicTowerCollapseKernel.{u, u} T I M s m₀ i)
      rw [adicTowerCollapseKernel_of_lt.{u, u} T I M s m₀ hm₀i]
      infer_instance
    exact submodule_eq_of_subsingleton _ _

end Stacks.LocalCohomology

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- Stable images at `m₀` make `I^{m₀}` annihilate `R¹lim H^s_T(M/IⁿM)`. -/
private theorem smul_id_firstDerivedLimit_eq_zero_of_stableImage {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A) (s : ℤ) (m₀ : ℕ)
    (hstab : HasStableImageIdealPowerCohomology.{u, u} T I M (s + 1) m₀) :
    ∀ a ∈ I ^ m₀, a • 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, u} T I M s) = 0 :=
  fun _ ha =>
    smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_of_isMittagLeffler.{u, u} T I M s m₀
      (isMittagLefflerCategorical_adicTowerCollapseKernelTower_of_stableImage T I M s m₀ hstab) ha

/-- In Situation [Stacks, Tag 0EFU], at a general specialization-stable `T`, there is an integer
`m₀` such that every element of `I^{m₀}` annihilates `R¹lim H^s_T(M/IⁿM)`. -/
@[stacks 0EFY "part (7) at a general specialization-stable T in Situation 0EFU: I^{m₀} \
annihilates R¹lim Hˢ_T(M/IⁿM)"]
theorem exists_smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero
    (S : BootstrapSituation.{u, u, u}) :
    ∃ m₀ : ℕ, ∀ a ∈ S.I ^ m₀,
      a • 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, u} S.T S.I
        (ModuleCat.of S.A S.M) S.s) = 0 := by
  obtain ⟨m₀, hm₀⟩ := exists_hasStableImageIdealPowerCohomology S
  exact ⟨m₀, fun a ha => smul_id_firstDerivedLimit_eq_zero_of_stableImage S.T S.I _ S.s m₀ hm₀ a ha⟩

/-- At a general specialization-stable `T`, in Situation [Stacks, Tag 0EFU] there is an integer
`m₀ ≥ 0` such that

1. `H^i_T(M) ⟶ H^i_T(M/IⁿM)` is injective for all `i ≤ s` and `n ≥ m₀`;
2. `{H^i_T(M/IⁿM)}` satisfies the Mittag-Leffler condition for `i < s`;
3. `{H^i_T(I^{m₀}M/I^{n+m₀}M)}` satisfies the Mittag-Leffler condition for `i ≤ s`;
4. `H^i_T(M) ⟶ lim H^i_T(M/IⁿM)` is an isomorphism for `i < s`;
5. `H^s_T(I^{m₀}M) ⟶ lim H^s_T(I^{m₀}M/I^{n+m₀}M)` is an isomorphism;
6. `H^s_T(M) ⟶ lim H^s_T(M/IⁿM)` is injective with cokernel killed by `I^{m₀}`; and
7. `R¹lim H^s_T(M/IⁿM)` is killed by `I^{m₀}`.

Parts (3) and (5) are the source's statements for the subquotients `I^{m₀}M/IⁿM`, `n ≥ m₀`, read
along the cofinal shift `n ↦ n + m₀`, the `n`-th term of the tower of adic quotients of `I^{m₀}M`
being `I^{m₀}M/I^{n+m₀}M` (`Stacks.Algebraization.map_subtype_pow_smul_top`); the limits and the
transition maps are the same. -/
@[stacks 0EFY]
theorem exists_bound_adicLocalCohomologyComparisons (S : BootstrapSituation.{u, u, u}) :
    ∃ m₀ : ℕ,
      (∀ i ≤ S.s, ∀ n : ℕ, m₀ ≤ n →
        Function.Injective ((localCohomologyAdicCone.{u, u} S.A S.T S.I i
          (ModuleCat.of S.A S.M)).π.app (op n)).hom) ∧
      (∀ i : ℤ, i + 1 ≤ S.s → IsMittagLefflerCategorical
        (localCohomologyAdicTower.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))) ∧
      (∀ i ≤ S.s, IsMittagLefflerCategorical (localCohomologyAdicTower.{u, u} S.A S.T S.I i
        (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))) ∧
      (∀ i : ℤ, i + 1 ≤ S.s → IsIso (limit.lift
        (localCohomologyAdicTower.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M))
        (localCohomologyAdicCone.{u, u} S.A S.T S.I i (ModuleCat.of S.A S.M)))) ∧
      IsIso (limit.lift
        (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))
        (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s
          (ModuleCat.of S.A ↥(S.I ^ m₀ • (⊤ : Submodule S.A S.M))))) ∧
      (Function.Injective (limit.lift
          (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))
          (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))).hom ∧
        ∀ a ∈ S.I ^ m₀, ∀ z : (limit (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s
            (ModuleCat.of S.A S.M)) : ModuleCat.{u} S.A),
          a • z ∈ LinearMap.range (limit.lift
            (localCohomologyAdicTower.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))
            (localCohomologyAdicCone.{u, u} S.A S.T S.I S.s (ModuleCat.of S.A S.M))).hom) ∧
      (∀ a ∈ S.I ^ m₀, a • 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, u} S.T S.I
        (ModuleCat.of S.A S.M) S.s) = 0) := by
  obtain ⟨m₁, h₁, -, -⟩ := exists_forall_injective_and_isMittagLeffler_and_isIso_limitLift S
  obtain ⟨m₂, hstab⟩ := exists_hasStableImageIdealPowerCohomology S
  obtain ⟨m₃, h₆inj, h₆⟩ := exists_injective_limitLift_and_smul_mem_range S
  have hst := hstab.mono.{u, u} ((le_max_left m₂ m₃).trans (le_max_right m₁ _))
  exact ⟨max m₁ (max m₂ m₃), fun i hi n hn => h₁ i hi n ((le_max_left _ _).trans hn),
    fun i hi => isMittagLefflerCategorical_localCohomologyAdicTower S i hi,
    fun i hi =>
      isMittagLefflerCategorical_localCohomologyAdicTower_idealPowerSubmodule S _ hst i hi,
    fun i hi => isIso_limitLift_localCohomologyAdicCone S i hi,
    isIso_limitLift_localCohomologyAdicCone_idealPowerSubmodule S _ hst,
    ⟨h₆inj, fun a ha => h₆ a (Ideal.pow_le_pow_right
      ((le_max_right m₂ m₃).trans (le_max_right _ _)) ha)⟩,
    fun a ha => smul_id_firstDerivedLimit_eq_zero_of_stableImage S.T S.I _ S.s _ hst a ha⟩

end Stacks.Algebraization

end
