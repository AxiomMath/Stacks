module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProPDevissage

/-!
# Dimension shifting for `ℓ`-power torsion coefficients

Let `G` be a profinite group and `ℓ` a natural number. Every discrete `G`-module `M` embeds into
the module `Coind_1^G M` of locally constant functions `G → M`, coinduced from the trivial
subgroup; this module has no higher cohomology (Shapiro's lemma), and it is `ℓ`-power torsion
when `M` is. The long exact sequence of cohomology of `0 → M → Coind_1^G M → Q → 0` therefore
gives `H^{q + 1}(G, M) = 0` as soon as `H^q(G, Q) = 0`. Consequently, if `Hⁿ(G, M) = 0` for every
`ℓ`-power torsion discrete `G`-module `M`, then `H^q(G, M) = 0` for every `q ≥ n` and every such
`M`.

For an absolute Galois group `G = Gal(Kˢᵉᵖ/K)`, the module `Coind_1^G M` corresponds to the sheaf
`f_* f⁻¹ 𝓕` on the small étale site of `Spec K`, where `f : Spec Kˢᵉᵖ → Spec K`; the sequence
above is the one used in [Stacks, Tag 0DV9].

## Main definitions

* `Stacks.GroupCohomology.coinductionBotShortComplex`: the short exact sequence
  `0 → M → Coind_1^G M → Q → 0`.

## Main results

* `Stacks.GroupCohomology.coinductionBotShortComplex_shortExact`: it is short exact.
* `Stacks.GroupCohomology.subsingleton_ext_succ_of_forall`: dimension shifting by one.
* `Stacks.GroupCohomology.subsingleton_ext_of_le`: vanishing in degree `n` for all `ℓ`-power
  torsion modules propagates to all degrees `q ≥ n`.

## References

* [Stacks Project, Tag 0DV9](https://stacks.math.columbia.edu/tag/0DV9)
* [J.-P. Serre, *Galois cohomology*, I.3.3][serre1997galois]
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v w

namespace Stacks.GroupCohomology

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

section ShortComplex

variable (M : ContinuousGModule.{v, max v w} G)

/-- The module `Coind_1^G M` coinduced from the restriction of `M` to the trivial subgroup. -/
abbrev coinductionBot : ContinuousGModule.{v, max v w} G :=
  (coinduction.{v, w} (⊥ : Subgroup G)).obj
    ((restriction.{v, v, max v w} (⊥ : Subgroup G).subtype continuous_subtype_val).obj M)

/-- The embedding `M ⟶ Coind_1^G M`, the unit of restriction–coinduction. -/
abbrev coinductionBotUnit : M ⟶ coinductionBot.{v, w} M :=
  (restrictionCoinductionAdjunction.{v, w} (⊥ : Subgroup G)).unit.app M

/-- The image of `m` under `M ⟶ Coind_1^G M` takes the value `m` at `1`. -/
lemma coinductionBotUnit_apply_one (m : M.obj.obj.V) :
    ((coinductionBotUnit.{v, w} M).hom.hom.hom.hom m :
      coinductionCarrier (⊥ : Subgroup G) _).1 1 = m :=
  (restrictionCoinductionAdjunction_unit_app_apply M m 1).trans (ρ_one_apply M m)

/-- The embedding `M ⟶ Coind_1^G M` is injective. -/
lemma coinductionBotUnit_injective :
    Function.Injective (coinductionBotUnit.{v, w} M).hom.hom.hom.hom := fun m m' h ↦ by
  rw [← coinductionBotUnit_apply_one M m, ← coinductionBotUnit_apply_one M m', h]

/-- The image of `M` in `Coind_1^G M`. -/
def coinductionBotRange : AddSubgroup (coinductionBot.{v, w} M).obj.obj.V :=
  (coinductionBotUnit.{v, w} M).hom.hom.hom.hom.toAddMonoidHom.range

/-- The image of `M` in `Coind_1^G M` is stable under the action of `G`. -/
lemma coinductionBotRange_stable : ∀ g, ∀ a ∈ coinductionBotRange.{v, w} M,
    ((coinductionBot.{v, w} M).obj.obj.ρ g).hom a ∈ coinductionBotRange.{v, w} M := by
  rintro g _ ⟨m, rfl⟩
  exact ⟨(M.obj.obj.ρ g).hom m, hom_comm (coinductionBotUnit.{v, w} M) g m⟩

/-- The short complex `0 → M → Coind_1^G M → Q → 0`. -/
def coinductionBotShortComplex : ShortComplex (ContinuousGModule.{v, max v w} G) :=
  ShortComplex.mk (coinductionBotUnit.{v, w} M)
    (quotObjπ _ _ (coinductionBotRange_stable.{v, w} M))
    (hom_ext fun m ↦ (QuotientAddGroup.eq_zero_iff (N := coinductionBotRange.{v, w} M) _).mpr
      ⟨m, rfl⟩)

/-- The sequence `0 → M → Coind_1^G M → Q → 0` is short exact. -/
theorem coinductionBotShortComplex_shortExact :
    (coinductionBotShortComplex.{v, w} M).ShortExact :=
  shortExact_of_function_exact _ (coinductionBotUnit_injective.{v, w} M)
    (quotObjπ_surjective _ _ (coinductionBotRange_stable.{v, w} M)) fun y ↦ by
      show (QuotientAddGroup.mk y : _ ⧸ coinductionBotRange.{v, w} M) = 0 ↔ y ∈ Set.range _
      exact QuotientAddGroup.eq_zero_iff (N := coinductionBotRange.{v, w} M) y

/-- The quotient `Coind_1^G M / M` of an `ℓ`-power torsion module is `ℓ`-power torsion. -/
lemma exists_pow_smul_coinductionBotShortComplex_X₃_eq_zero {ℓ : ℕ}
    (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)
    (y : (coinductionBotShortComplex.{v, w} M).X₃.obj.obj.V) : ∃ k : ℕ, ℓ ^ k • y = 0 :=
  quotObj_exists_pow_smul_eq_zero _ _ _ (exists_pow_smul_coinduction_eq_zero hM) y

end ShortComplex

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup G))]

/-- **Dimension shifting.** If `H^q(G, Q)` vanishes for every `ℓ`-power torsion discrete
`G`-module `Q`, then so does `H^{q + 1}(G, M)` for every `ℓ`-power torsion discrete `G`-module
`M`. -/
theorem subsingleton_ext_succ_of_forall {ℓ q : ℕ}
    (h : ∀ Q : ContinuousGModule.{v, max v w} G, (∀ x : Q.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) →
      Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) Q q))
    (M : ContinuousGModule.{v, max v w} G) (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M (q + 1)) := by
  have hS := coinductionBotShortComplex_shortExact.{v, w} M
  have hQ := h _ (exists_pow_smul_coinductionBotShortComplex_X₃_eq_zero.{v, w} M hM)
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨d, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS c
    (ext_coinduction_bot_eq_zero.{v, w} _ q _) rfl
  rw [Subsingleton.elim d 0, Abelian.Ext.zero_comp]
  rfl

/-- **Vanishing propagates upwards.** If `Hⁿ(G, M)` vanishes for every `ℓ`-power torsion
discrete `G`-module `M`, then `H^q(G, M)` vanishes for every `q ≥ n` and every such `M`. -/
theorem subsingleton_ext_of_le {ℓ n : ℕ}
    (h : ∀ M : ContinuousGModule.{v, max v w} G, (∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) →
      Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M n))
    {q : ℕ} (hq : n ≤ q) (M : ContinuousGModule.{v, max v w} G)
    (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M q) := by
  induction q, hq using Nat.le_induction generalizing M with
  | base => exact h M hM
  | succ q _ ih => exact subsingleton_ext_succ_of_forall.{v, w} ih M hM

end Stacks.GroupCohomology

end
