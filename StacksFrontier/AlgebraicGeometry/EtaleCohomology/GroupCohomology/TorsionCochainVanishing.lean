module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.PrimeTorsionCochains

/-!
# The degree-two cochain statement for a torsion module

For a profinite group `G` whose open subgroups all satisfy the degree-two cochain statement with
values in `ℤ/p` with the trivial action — for every prime `p`, over the open subgroups of some
open normal subgroup of index prime to `p` — every locally constant `2`-cocycle of `G` with
values in a torsion discrete module is a coboundary.

## Main definitions

* `Stacks.GroupCohomology.HasPrimeBase`: for every prime `p`, some open normal subgroup of index
  prime to `p` all of whose open subgroups satisfy the degree-two cochain statement with values
  in `ℤ/p` with the trivial action.

## Main results

* `Stacks.GroupCohomology.vanishesTwo_of_finite`: the statement for a finite discrete module.
* `Stacks.GroupCohomology.vanishesTwo_of_isTorsion`: the statement for a torsion discrete module.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): part (2), of which this
  is the cochain-level content.
-/

@[expose] public section

open groupCohomology

universe u v

namespace Stacks.GroupCohomology

section Torsion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- For every prime `p` there is an open normal subgroup of index prime to `p` such that the
degree-two cochain statement with values in `ℤ/p` with the trivial action holds over each of its
open subgroups. -/
def HasPrimeBase (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ p : ℕ, p.Prime → ∃ V : Subgroup G, V.Normal ∧ IsOpen (V : Set G) ∧ ¬ p ∣ V.index ∧
    ∀ U : OpenSubgroup G, (U : Subgroup G) ≤ V → VanishesTwo ↥U (TrivialMod p)

/-- The degree-two cochain statement holds for every finite discrete module of cardinality at most
`n`. -/
theorem vanishesTwo_of_finite (hbase : HasPrimeBase G) :
    ∀ (n : ℕ) {A : Type v} [AddCommGroup A] [DistribMulAction G A] [Finite A],
      HasOpenStabilizers G A → Nat.card A ≤ n → VanishesTwo G A := by
  intro n
  induction n with
  | zero =>
      intro A _ _ _ _ hcard
      exact absurd hcard (by simpa using Nat.card_pos.ne')
  | succ n ih =>
      intro A _ _ _ hA hcard
      by_cases htriv : ∀ a : A, a = 0
      · intro F _ _
        refine ⟨fun _ ↦ 0, IsLocallyConstant.const 0, ?_⟩
        funext q
        rw [htriv (F q)]
        simp [dOne]
      · obtain ⟨a₁, ha₁⟩ : ∃ a : A, a ≠ 0 := by simpa using htriv
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
          (Finite.one_lt_card_iff_nontrivial.mpr (nontrivial_of_ne a₁ 0 ha₁)).ne'
        have : Fact p.Prime := ⟨hp⟩
        set N : AddSubgroup A :=
          { carrier := {a : A | p • a = 0}
            zero_mem' := by simp
            add_mem' := fun {a b} ha hb ↦ by
              simp only [Set.mem_ofPred_eq, smul_add] at *
              rw [ha, hb, add_zero]
            neg_mem' := fun {a} ha ↦ by
              simp only [Set.mem_ofPred_eq, smul_neg] at *
              rw [ha, neg_zero] } with hNdef
        have hNmem : ∀ a : A, a ∈ N ↔ p • a = 0 := fun a ↦ Iff.rfl
        have hNstable : ∀ (g : G), ∀ a ∈ N, g • a ∈ N := fun g a ha ↦
          (hNmem _).2 (by rw [smul_comm p g a, (hNmem a).1 ha, smul_zero])
        let := subDistribMulAction N hNstable
        let := quotDistribMulAction N hNstable
        have : Finite ↥N := Subtype.finite
        have : Fintype A := Fintype.ofFinite A
        have hpdvd' : p ∣ Fintype.card A := by rwa [Nat.card_eq_fintype_card] at hpdvd
        obtain ⟨a₀, ha₀⟩ := exists_prime_addOrderOf_dvd_card p hpdvd'
        have ha₀mem : a₀ ∈ N := (hNmem a₀).2 (by rw [← ha₀]; exact addOrderOf_nsmul_eq_zero a₀)
        have ha₀ne : (⟨a₀, ha₀mem⟩ : ↥N) ≠ 0 := fun hc ↦ by
          rw [show a₀ = 0 by simpa using congrArg Subtype.val hc, addOrderOf_zero] at ha₀
          exact hp.ne_one ha₀.symm
        obtain ⟨V, hVnorm, hVopen, hVp, hVbase⟩ := hbase p hp
        have := hVnorm
        have hNvan : VanishesTwo G ↥N :=
          vanishesTwo_of_killed_by_prime hp V hVopen hVp hVbase
            (hasOpenStabilizers_sub N hNstable hA)
            (fun x ↦ Subtype.ext (by simpa using (hNmem (x : A)).1 x.2))
        have hcardN : 1 < Nat.card ↥N :=
          Finite.one_lt_card_iff_nontrivial.mpr (nontrivial_of_ne _ 0 ha₀ne)
        have hmul : Nat.card ↥N * N.index = Nat.card A := AddSubgroup.card_mul_index N
        have hindexpos : 0 < N.index := Nat.card_pos
        have hcardq : Nat.card (A ⧸ N) ≤ n := by
          have h2 : Nat.card (A ⧸ N) = N.index := rfl
          nlinarith [hmul, hcardN, hindexpos, hcard]
        have hQvan : VanishesTwo G (A ⧸ N) :=
          ih (A := A ⧸ N) (hasOpenStabilizers_quot N hNstable hA) hcardq
        exact vanishesTwo_of_shortExact hA (AddSubgroup.subtype N) Subtype.val_injective
          (subDistribMulAction_smul_coe N hNstable) (QuotientAddGroup.mk' N)
          (QuotientAddGroup.mk'_surjective N)
          (fun h m ↦ (quotDistribMulAction_smul_mk N hNstable h m).symm)
          (fun z hz ↦ ⟨⟨z, (QuotientAddGroup.eq_zero_iff z).1 hz⟩, rfl⟩) hNvan hQvan

/-- The degree-two cochain statement holds for every torsion discrete module. -/
theorem vanishesTwo_of_isTorsion (hbase : HasPrimeBase G) {M : Type v} [AddCommGroup M]
    [DistribMulAction G M] (hM : HasOpenStabilizers G M)
    (htor : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n • m = 0) : VanishesTwo G M := by
  intro F hFlc hF
  obtain ⟨N, hNfin, hNstable, hNsub⟩ :=
    exists_finite_stable_addSubgroup hM htor hFlc.range_finite
  let := subDistribMulAction N hNstable
  have : Finite ↥N := hNfin.to_subtype
  have hmem : ∀ q : G × G, F q ∈ N := fun q ↦ hNsub (Set.mem_range_self q)
  set F' : G × G → ↥N := fun q ↦ ⟨F q, hmem q⟩ with hF'def
  have hF'lc : IsLocallyConstant F' :=
    IsLocallyConstant.desc _ (fun z : ↥N ↦ (z : M)) hFlc Subtype.val_injective
  have hF'coc : IsCocycle₂ F' := fun g h j ↦ Subtype.ext <| by
    simpa only [AddSubgroup.coe_add, subDistribMulAction_smul_coe N hNstable, hF'def] using
      hF g h j
  obtain ⟨x', hx'lc, hx'⟩ := vanishesTwo_of_finite hbase (Nat.card ↥N)
    (hasOpenStabilizers_sub N hNstable hM) le_rfl F' hF'lc hF'coc
  refine ⟨fun g ↦ (x' g : M), hx'lc.comp (fun z : ↥N ↦ (z : M)), ?_⟩
  funext q
  have h3 : ((dOne x' q : ↥N) : M) = dOne (fun g ↦ (x' g : M)) q := by
    obtain ⟨g₁, g₂⟩ := q
    simp only [dOne_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub,
      subDistribMulAction_smul_coe N hNstable]
  rw [← h3, congrFun hx' q]

end Torsion

end Stacks.GroupCohomology

end
