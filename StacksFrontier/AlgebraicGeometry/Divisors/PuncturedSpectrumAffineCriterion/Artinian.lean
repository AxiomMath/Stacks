module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Two finiteness lemmas for torsion modules over a Noetherian local ring

Let `R` be a Noetherian local ring with maximal ideal `𝔪`.  A finitely generated `R`-module each
of whose elements is killed by a power of every element of `𝔪` is supported at the closed point,
hence has finite length; this is `Stacks.Divisors.isArtinian_of_forall_exists_pow_smul_eq_zero`.

The second lemma is the engine of the finiteness statement behind Stacks Tag 0BCR.  Let `M` be an
`R`-module over any commutative ring and `f : R` an element such that every element of `M` is
killed by a power of `f`.  If the `f`-torsion `M[f]` is Artinian, then `M = M[fⁿ] + fM` for a
single exponent `n`, namely one at which the descending chain `fⁿM ∩ M[f]` of submodules of the
Artinian module `M[f]` is stationary: if `fⁿq ∈ fⁿ⁺¹M`, say `fⁿq = fⁿ⁺¹w`, then `q - fw` is
killed by `fⁿ`, which lets one descend from `M[fⁿ⁺¹]` to `M[fⁿ]` modulo `fM`.

## Main results

* `Stacks.Divisors.isArtinian_of_forall_exists_pow_smul_eq_zero`
* `Stacks.Divisors.exists_forall_eq_add_smul_of_isArtinian_torsionBy`

## References

* [Stacks Project, Tag 0BCR](https://stacks.math.columbia.edu/tag/0BCR)
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Stacks.Divisors

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `fⁿ` kills `x` then so does every higher power of `f`. -/
private theorem pow_smul_eq_zero_of_le {f : R} {x : M} {n m : ℕ} (hnm : n ≤ m)
    (hx : f ^ n • x = 0) : f ^ m • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

/-- A finitely generated module over a Noetherian local ring all of whose elements are killed by
a power of every element of the maximal ideal is an Artinian module: its annihilator has radical
the maximal ideal, so it is a finitely generated module over an Artinian quotient of `R`. -/
theorem isArtinian_of_forall_exists_pow_smul_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M]
    (h : ∀ g ∈ maximalIdeal R, ∀ x : M, ∃ N : ℕ, g ^ N • x = 0) :
    IsArtinian R M := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite R M›
  -- Every element of `𝔪` has a power in the annihilator of `M`.
  have hrad : maximalIdeal R ≤ (Module.annihilator R M).radical := by
    intro g hg
    choose N hN using fun x : M => h g hg x
    refine ⟨s.sup N, ?_⟩
    rw [Module.mem_annihilator]
    have hgen : ∀ x ∈ s, g ^ s.sup N • x = 0 := by
      intro x hx
      exact pow_smul_eq_zero_of_le (Finset.le_sup (f := N) hx) (hN x)
    intro x
    have : x ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_comm, hy, smul_zero]
  by_cases htop : Module.annihilator R M = ⊤
  · have : Subsingleton M := Module.annihilator_eq_top_iff.mp htop
    infer_instance
  -- The quotient of `R` by the annihilator is a Noetherian local ring whose maximal ideal is
  -- nilpotent, hence Artinian, and `M` is a finitely generated module over it.
  have hnt : Nontrivial (R ⧸ Module.annihilator R M) := Ideal.Quotient.nontrivial_iff.mpr htop
  have hloc : IsLocalRing (R ⧸ Module.annihilator R M) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hmle : maximalIdeal (R ⧸ Module.annihilator R M) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (Module.annihilator R M)) := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    by_contra hr
    exact IsLocalRing.notMem_maximalIdeal.mpr
      ((IsLocalRing.notMem_maximalIdeal.mp hr).map (Ideal.Quotient.mk _)) hx
  have hnilp : IsNilpotent (maximalIdeal (R ⧸ Module.annihilator R M)) := by
    refine ⟨k, le_antisymm ?_ bot_le⟩
    calc maximalIdeal (R ⧸ Module.annihilator R M) ^ k
        ≤ ((maximalIdeal R).map (Ideal.Quotient.mk _)) ^ k := Ideal.pow_right_mono hmle k
      _ = (maximalIdeal R ^ k).map (Ideal.Quotient.mk _) := (Ideal.map_pow _ _ k).symm
      _ ≤ (Module.annihilator R M).map (Ideal.Quotient.mk _) := Ideal.map_mono hk
      _ = ⊥ := Ideal.map_quotient_self _
  have : IsNoetherianRing (R ⧸ Module.annihilator R M) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk (Module.annihilator R M))
      Ideal.Quotient.mk_surjective
  have : IsArtinianRing (R ⧸ Module.annihilator R M) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr hnilp
  let _ := Module.quotientAnnihilator (R := R) (M := M)
  have : Module.Finite (R ⧸ Module.annihilator R M) M :=
    Module.Finite.of_restrictScalars_finite R _ M
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ Module.annihilator R M)
    Ideal.Quotient.mk_surjective

/-- Let `f : R` act on `M` with every element killed by some power of `f`, and suppose the
`f`-torsion of `M` is Artinian.  Then there is a single exponent `n` with `M = M[fⁿ] + fM`.

The exponent is one at which the descending chain `fⁿM ∩ M[f]` of submodules of the Artinian
module `M[f]` is stationary: if `fⁿq ∈ fⁿ⁺¹M`, say `fⁿq = fⁿ⁺¹w`, then `q - fw` is killed by
`fⁿ`, which lets one descend from `M[fⁿ⁺¹]` to `M[fⁿ]` modulo `fM`. -/
theorem exists_forall_eq_add_smul_of_isArtinian_torsionBy (f : R)
    (htor : ∀ q : M, ∃ n : ℕ, f ^ n • q = 0)
    (hart : IsArtinian R (Submodule.torsionBy R M f)) :
    ∃ n : ℕ, ∀ q : M, ∃ q' : M, f ^ n • q' = 0 ∧ ∃ w : M, q = q' + f • w := by
  set D : ℕ → Submodule R (Submodule.torsionBy R M f) := fun n =>
    (LinearMap.range (LinearMap.lsmul R M (f ^ n))).comap
      (Submodule.torsionBy R M f).subtype with hD
  have hanti : Antitone D := by
    intro i j hij x hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨f ^ (j - i) • y, by
      rw [← hy]; simp only [LinearMap.lsmul_apply, smul_smul, ← pow_add]
      rw [Nat.add_sub_cancel' hij]⟩
  obtain ⟨-, ⟨n₀, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Set.range D) ⟨D 0, 0, rfl⟩
  have hstab : ∀ n, n₀ ≤ n → D n = D n₀ :=
    fun n hn => eq_of_le_of_not_lt (hanti hn) (hmin _ ⟨n, rfl⟩)
  refine ⟨n₀, fun q => ?_⟩
  suffices key : ∀ n (q : M), f ^ n • q = 0 → ∃ q' : M, f ^ n₀ • q' = 0 ∧ ∃ w : M, q = q' + f • w by
    obtain ⟨n, hn⟩ := htor q
    exact key n q hn
  intro n
  induction n with
  | zero => exact fun q hq => ⟨q, by simp [(by simpa using hq : q = 0)], 0, by simp⟩
  | succ k ih =>
    intro q hq
    rcases lt_or_ge k n₀ with hk | hk
    · exact ⟨q, pow_smul_eq_zero_of_le (Nat.succ_le_of_lt hk) hq, 0, by simp⟩
    · have hmem : f ^ k • q ∈ Submodule.torsionBy R M f := by
        rw [Submodule.mem_torsionBy_iff, smul_smul, ← pow_succ']
        exact hq
      have hDk : (⟨f ^ k • q, hmem⟩ : Submodule.torsionBy R M f) ∈ D k := ⟨q, rfl⟩
      rw [hstab k hk, ← hstab (k + 1) (hk.trans (Nat.le_succ k))] at hDk
      obtain ⟨w, hw⟩ := hDk
      obtain ⟨q', hq', v, hv⟩ := ih (q - f • w) (by
        have : f ^ k • (f • w) = f ^ k • q := by
          rw [smul_smul, ← pow_succ]; exact hw
        rw [smul_sub, this, sub_self])
      exact ⟨q', hq', v + w, by rw [smul_add, ← add_assoc, ← hv, sub_add_cancel]⟩

end Stacks.Divisors
