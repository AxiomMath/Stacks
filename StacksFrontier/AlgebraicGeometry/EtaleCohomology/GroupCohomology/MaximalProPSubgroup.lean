module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProPDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDimensionShifting

/-!
# Cohomological vanishing and maximal pro-`ℓ` subgroups

Let `ℓ` be a prime, `G` a profinite group and `H ⊆ G` a maximal pro-`ℓ` subgroup. Then
`Hⁿ(G, M) = 0` for every `ℓ`-power torsion discrete `G`-module `M` if and only if
`Hⁿ(H, ℤ/ℓℤ) = 0`. This is the group-theoretic content of [Stacks, Tag 0DV8]; the statement for
the étale cohomology of fields is deduced from it in
`AlgebraicGeometry.subsingleton_sheafH_iff_of_isMaximalProPSubgroup`.

* If `Hⁿ(H, ℤ/ℓℤ) = 0`, then `Hⁿ(H, M) = 0` for every `ℓ`-power torsion `M`, since `H` is a
  profinite pro-`ℓ` group (`Stacks.GroupCohomology.subsingleton_ext_of_isProPGroup`), and
  `Hⁿ(G, M)` injects into `Hⁿ(H, M)` because every open subgroup of `G` containing `H` has index
  prime to `ℓ` (`IsMaximalProPSubgroup.not_dvd_index` and
  `Stacks.GroupCohomology.subsingleton_ext_of_subsingleton_ext_restriction`).
* Conversely `Hⁿ(H, ℤ/ℓℤ) = Hⁿ(G, Coind_H^G ℤ/ℓℤ)` by Shapiro's lemma, and the coinduced module is
  `ℓ`-torsion.

Since vanishing in degree `n` for all `ℓ`-power torsion modules propagates to all degrees `q ≥ n`
(`Stacks.GroupCohomology.subsingleton_ext_of_le`), the same condition `Hⁿ(H, ℤ/ℓℤ) = 0` is
equivalent to the vanishing of `H^q(G, M)` for all `q ≥ n` and all `ℓ`-power torsion `M`; this
is the group-theoretic content of [Stacks, Tag 0DV9].

## Main results

* `Stacks.GroupCohomology.subsingleton_ext_iff_of_isMaximalProPSubgroup`: the equivalence.
* `Stacks.GroupCohomology.forall_le_subsingleton_ext_iff_of_isMaximalProPSubgroup`: the
  equivalence for all degrees `q ≥ n`.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [Stacks Project, Tag 0DV9](https://stacks.math.columbia.edu/tag/0DV9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v w

namespace Stacks.GroupCohomology

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {H : Subgroup G}

/-- A closed subgroup of a compact group is compact. -/
lemma compactSpace_of_isClosed (hH : IsClosed (H : Set G)) : CompactSpace H :=
  isCompact_iff_compactSpace.mp hH.isCompact

/-- **Stacks Project, Tag 0DV8, group-theoretic form.** Let `H` be a maximal pro-`ℓ` subgroup of
a profinite group `G`. Then `Hⁿ(G, M)` vanishes for every `ℓ`-power torsion discrete `G`-module
`M` if and only if `Hⁿ(H, ℤ/ℓℤ)` vanishes. -/
theorem subsingleton_ext_iff_of_isMaximalProPSubgroup (hH : IsMaximalProPSubgroup ℓ H) (n : ℕ)
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} H)]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup H))] :
    (∀ M : ContinuousGModule.{v, max v w} G, (∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) →
      Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M n)) ↔
      Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ))
        (trivialGModule.{v, max v w} H (ULift.{max v w} (ZMod ℓ))) n) := by
  refine ⟨fun h ↦ ?_, fun h M hM ↦ ?_⟩
  · have htors : ∀ x : ((coinduction.{v, w} H).obj
        (trivialGModule.{v, max v w} H (ULift.{max v w} (ZMod ℓ)))).obj.obj.V,
        ∃ k : ℕ, ℓ ^ k • x = 0 :=
      exists_pow_smul_coinduction_eq_zero fun a ↦ ⟨1, by
        show ℓ ^ 1 • (a : ULift.{max v w} (ZMod ℓ)) = 0
        obtain ⟨a⟩ := a
        exact ULift.ext (show ℓ ^ 1 • a = 0 by simp)⟩
    have := h _ htors
    exact (shapiroAddEquiv.{v, w} H _ n).injective.subsingleton
  · have : CompactSpace H := compactSpace_of_isClosed hH.prop.1
    have hRes : Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ))
        ((restriction H.subtype continuous_subtype_val).obj M) n) :=
      subsingleton_ext_of_isProPGroup.{v, w} hH.prop.2 n _ hM
    exact subsingleton_ext_of_subsingleton_ext_restriction.{v, w}
      (fun U hU hHU ↦ ((hℓ.out.coprime_iff_not_dvd).mpr (hH.not_dvd_index hU hHU)).symm) hM n

/-- **Stacks Project, Tag 0DV9, group-theoretic form.** Let `H` be a maximal pro-`ℓ` subgroup of
a profinite group `G`. Then `H^q(G, M)` vanishes for every `q ≥ n` and every `ℓ`-power torsion
discrete `G`-module `M` if and only if `Hⁿ(H, ℤ/ℓℤ)` vanishes. -/
theorem forall_le_subsingleton_ext_iff_of_isMaximalProPSubgroup (hH : IsMaximalProPSubgroup ℓ H)
    (n : ℕ) [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} H)]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup H))]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup G))] :
    (∀ q, n ≤ q → ∀ M : ContinuousGModule.{v, max v w} G,
      (∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) →
        Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M q)) ↔
      Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ))
        (trivialGModule.{v, max v w} H (ULift.{max v w} (ZMod ℓ))) n) := by
  rw [← subsingleton_ext_iff_of_isMaximalProPSubgroup.{v, w} hH n]
  exact ⟨fun h ↦ h n le_rfl, fun h _ hq ↦ subsingleton_ext_of_le.{v, w} h hq⟩

end Stacks.GroupCohomology

end
