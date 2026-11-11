module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# A countable ring with a projective direct sum of locally free modules, not locally free

Let `R` be the countable ring of eventually constant sequences `ℕ → 𝔽₂` and let `εₙ ∈ R` be the
indicator sequence of the index `n`.  Each ideal `εₙ R` is a direct summand of `R`, hence finite
and projective, hence finite locally free, and so the direct sum `M = ⨁ₙ εₙ R` is projective.
It is not locally free: if `g ∈ R` is nonzero at infinitely many indices then every element of
`M_g` is annihilated by some `εₙ` that is nonzero in `R_g`, whereas a basis vector of a nonzero
free module is annihilated by no nonzero scalar; and the `g` vanishing off a finite set form a
proper ideal, so those standard opens alone cannot cover `Spec R`.

## Main results

* `Stacks.Examples.exists_countable_projective_directSum_isFiniteLocallyFree_not_isLocallyFree`:
  over a countable ring there is a countable direct sum of finite locally free modules which is
  projective and not locally free.

## Implementation notes

This is the countable form of the first of the two examples of the source section, the one whose
summands have rank between zero and one: `εₙ R` has rank one at the primes avoiding `εₙ` and
rank zero at the others, so the summands are finite locally free but not of constant rank one.
The source's second example, whose summands are invertible, is a colimit of tensor products of
coordinate rings of punctured curves over `ℚ`. The rank-one statement uses the punctured conic
`u² + v² = 1` for every factor, and replaces the Chern classes of the source by a mod-two Euler
characteristic; see `StacksFrontier.Examples.Algebra.RankOneSumNotLocallyFree.Reduction`.

## References

* [Stacks Project, Tag 05WH](https://stacks.math.columbia.edu/tag/05WH)
* [Stacks Project, Tag 05WJ](https://stacks.math.columbia.edu/tag/05WJ)
-/

@[expose] public section

namespace Stacks.Examples

universe u

open Filter

/-! ### The countable ring of eventually constant `𝔽₂`-sequences -/

/-- The ring `R` of eventually constant sequences `ℕ → 𝔽₂`, a countable subring of the ring of
all such sequences. -/
private def evConstSeq : Subring (ℕ → ULift.{u} (ZMod 2)) where
  carrier := {f | EventuallyConst f cofinite}
  zero_mem' := EventuallyConst.const 0
  one_mem' := EventuallyConst.const 1
  add_mem' := fun ha hb => ha.add hb
  neg_mem' := fun ha => ha.neg
  mul_mem' := fun ha hb => ha.mul hb

/-- The underlying type of the ring of eventually constant `𝔽₂`-sequences. -/
private abbrev EvSeq := ↥evConstSeq.{u}

/-- Evaluation at an index, as a ring homomorphism on eventually constant sequences. -/
private def coordHom (k : ℕ) : EvSeq.{u} →+* ULift.{u} (ZMod 2) :=
  (Pi.evalRingHom (fun _ : ℕ => ULift.{u} (ZMod 2)) k).comp evConstSeq.subtype

private lemma ext_coord {x y : EvSeq.{u}} (h : ∀ k, coordHom k x = coordHom k y) : x = y :=
  Subtype.ext (funext h)

private lemma countable_evSeq : Countable EvSeq.{u} := by
  have : Countable (ULift.{u} (ZMod 2)) := Countable.of_equiv (ZMod 2) Equiv.ulift.symm
  have hsub : {f : ℕ → ULift.{u} (ZMod 2) | EventuallyConst f cofinite} ⊆
      ⋃ p : Finset ℕ × ULift.{u} (ZMod 2), {f | ∀ k ∉ p.1, f k = p.2} := by
    intro f hf
    obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hf
    have hfin : {k : ℕ | ¬ f k = c}.Finite := Filter.eventually_cofinite.mp hc
    refine Set.mem_iUnion.mpr ⟨⟨hfin.toFinset, c⟩, fun k hk => ?_⟩
    by_contra hne
    exact hk (hfin.mem_toFinset.mpr hne)
  have hcount : {f : ℕ → ULift.{u} (ZMod 2) | EventuallyConst f cofinite}.Countable := by
    refine Set.Countable.mono hsub (Set.countable_iUnion fun p => Set.Finite.countable ?_)
    rw [← Set.finite_coe_iff]
    refine Finite.of_injective
      (fun f => fun k : ↥p.1 => (f : ℕ → ULift.{u} (ZMod 2)) (k : ℕ)) ?_
    intro f1 f2 h
    refine Subtype.ext (funext fun k => ?_)
    by_cases hk : k ∈ p.1
    · exact congrFun h ⟨k, hk⟩
    · rw [f1.2 k hk, f2.2 k hk]
  exact hcount.to_subtype

private lemma pow_ne_zero_of_ne_zero {a : ULift.{u} (ZMod 2)} (ha : a ≠ 0) (k : ℕ) :
    a ^ k ≠ 0 := by
  intro hk
  have hd : ULift.ringEquiv (R := ZMod 2) a ≠ 0 := by
    intro h
    exact ha ((ULift.ringEquiv (R := ZMod 2)).injective (by rw [h, map_zero]))
  have h1 : (ULift.ringEquiv (R := ZMod 2) a) ^ k = 0 := by
    rw [← map_pow, hk, map_zero]
  rw [(by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) _ hd, one_pow] at h1
  exact absurd h1 (by decide)

/-! ### The orthogonal idempotents -/

/-- The idempotent `εₙ ∈ R`: the indicator sequence of the single index `n`. -/
private def unitIdem (n : ℕ) : EvSeq.{u} :=
  ⟨fun k => if k = n then 1 else 0, by
    change EventuallyConst (fun k => if k = n then (1 : ULift.{u} (ZMod 2)) else 0) cofinite
    rw [Filter.eventuallyConst_iff_exists_eventuallyEq]
    refine ⟨0, Filter.eventually_cofinite.mpr ((Set.finite_singleton n).subset ?_)⟩
    intro k hk
    refine Set.mem_singleton_iff.mpr ?_
    by_contra hkn
    exact hk (by simp [hkn])⟩

private lemma coordHom_unitIdem_self (n : ℕ) : coordHom n (unitIdem.{u} n) = 1 := by
  simp [coordHom, unitIdem]

private lemma coordHom_unitIdem_of_ne {k n : ℕ} (h : k ≠ n) :
    coordHom k (unitIdem.{u} n) = 0 := by
  simp [coordHom, unitIdem, h]

private lemma unitIdem_idem (n : ℕ) : IsIdempotentElem (unitIdem.{u} n) := by
  refine ext_coord fun k => ?_
  rw [map_mul]
  by_cases h : k = n
  · subst h; rw [coordHom_unitIdem_self, one_mul]
  · rw [coordHom_unitIdem_of_ne h, mul_zero]

private lemma unitIdem_mul_unitIdem {m n : ℕ} (h : m ≠ n) :
    unitIdem.{u} m * unitIdem.{u} n = 0 := by
  refine ext_coord fun k => ?_
  rw [map_mul, map_zero]
  by_cases hk : k = m
  · subst hk; rw [coordHom_unitIdem_of_ne h, mul_zero]
  · rw [coordHom_unitIdem_of_ne hk, zero_mul]

/-! ### The sequences vanishing off a finite set -/

/-- The ideal of sequences vanishing off a finite set of indices. -/
private def evZeroIdeal : Ideal EvSeq.{u} where
  carrier := {x | ∀ᶠ k in cofinite, coordHom k x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ∀ᶠ k in cofinite, coordHom k (a + b) = 0
    filter_upwards [ha, hb] with k hk hk'
    simp [map_add, hk, hk']
  smul_mem' := by
    intro c a ha
    change ∀ᶠ k in cofinite, coordHom k (c • a) = 0
    filter_upwards [ha] with k hk
    simp [smul_eq_mul, map_mul, hk]

private lemma one_notMem_evZeroIdeal : (1 : EvSeq.{u}) ∉ evZeroIdeal.{u} := by
  intro h
  have h' : {k : ℕ | ¬ coordHom k (1 : EvSeq.{u}) = 0}.Finite := Filter.eventually_cofinite.mp h
  have huniv : {k : ℕ | ¬ coordHom k (1 : EvSeq.{u}) = 0} = Set.univ := by
    ext k
    simp
  rw [huniv] at h'
  exact Set.infinite_univ h'

private lemma infinite_support_of_notMem {g : EvSeq.{u}} (hg : g ∉ evZeroIdeal.{u}) :
    {k : ℕ | coordHom k g ≠ 0}.Infinite :=
  fun hfin => hg (Filter.eventually_cofinite.mpr hfin)

/-! ### The summands -/

/-- The ideal `εₙ R`, the direct summand of `R` cut out by the idempotent `εₙ`. -/
private abbrev summandIdeal (n : ℕ) : Ideal EvSeq.{u} := Ideal.span {unitIdem.{u} n}

/-- The direct sum `M = ⨁ₙ εₙ R`. -/
private abbrev totalModule : Type u := DirectSum ℕ fun n => ↥(summandIdeal.{u} n)

private lemma unitIdem_mul_of_mem {n : ℕ} {x : EvSeq.{u}} (hx : x ∈ summandIdeal.{u} n) :
    unitIdem.{u} n * x = x := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [← mul_assoc, (unitIdem_idem n).eq]

private lemma unitIdem_mul_of_mem_ne {m n : ℕ} (h : m ≠ n) {x : EvSeq.{u}}
    (hx : x ∈ summandIdeal.{u} n) : unitIdem.{u} m * x = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [← mul_assoc, unitIdem_mul_unitIdem h, zero_mul]

private lemma finite_summandIdeal (n : ℕ) :
    Module.Finite EvSeq.{u} ↥(summandIdeal.{u} n) :=
  Module.Finite.of_fg (Submodule.fg_span_singleton _)

private lemma projective_summandIdeal (n : ℕ) :
    Module.Projective EvSeq.{u} ↥(summandIdeal.{u} n) := by
  let s : EvSeq.{u} →ₗ[EvSeq.{u}] ↥(summandIdeal.{u} n) :=
    { toFun := fun r => ⟨unitIdem.{u} n * r, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)⟩
      map_add' := fun a b => Subtype.ext (by simp [mul_add])
      map_smul' := fun a b => Subtype.ext (by simp [smul_eq_mul, mul_left_comm]) }
  refine Module.Projective.of_split (Submodule.subtype _) s ?_
  exact LinearMap.ext fun x => Subtype.ext (unitIdem_mul_of_mem x.2)

/-- A finite projective module is finite locally free; this is Stacks 00NX. -/
private theorem isFiniteLocallyFree_of_finite_projective {R : Type u} [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.IsFiniteLocallyFree R M := by
  have h2 : Module.Finite R M ∧ Module.Projective R M := ⟨inferInstance, inferInstance⟩
  obtain ⟨s, hs, hfree⟩ := ((Module.finite_projective_tfae R M).out 2 7).mp h2
  unfold Module.IsFiniteLocallyFree
  exact ⟨s, Subtype.val, by simpa using hs, fun f => hfree f.1 f.2⟩

/-! ### Failure of local freeness -/

/-- A nonzero module in which every element is annihilated by a nonzero scalar is not free. -/
private theorem not_free_of_forall_exists_smul_eq_zero {A N : Type*} [Semiring A]
    [AddCommMonoid N] [Module A N] [Nontrivial N]
    (h : ∀ x : N, ∃ a : A, a ≠ 0 ∧ a • x = 0) : ¬ Module.Free A N := by
  intro hfree
  have : Module.Free A N := hfree
  let b := Module.Free.chooseBasis A N
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex A N) with hι | hne
  · exact (not_subsingleton N) ⟨fun x y => b.repr.injective (Finsupp.ext fun j => isEmptyElim j)⟩
  · obtain ⟨i⟩ := hne
    obtain ⟨a, ha, hax⟩ := h (b i)
    have h1 : b.repr (a • b i) = 0 := by rw [hax, map_zero]
    rw [map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] at h1
    exact ha (Finsupp.single_eq_zero.mp h1)

/-- A power of `g` does not kill `εₙ` when `g` is nonzero at the index `n`. -/
private lemma mul_unitIdem_ne_zero_of_mem_powers {g u : EvSeq.{u}} {n : ℕ}
    (hg : coordHom n g ≠ 0) (hu : u ∈ Submonoid.powers g) : u * unitIdem.{u} n ≠ 0 := by
  obtain ⟨k, rfl⟩ := hu
  intro h
  have h' := congrArg (coordHom n) h
  rw [map_mul, map_pow, coordHom_unitIdem_self, mul_one, map_zero] at h'
  exact pow_ne_zero_of_ne_zero hg k h'

private lemma unitIdem_smul_eq_zero {m : totalModule.{u}} {n : ℕ} (hn : m n = 0) :
    unitIdem.{u} n • m = 0 := by
  refine DFinsupp.ext fun j => ?_
  rw [DFinsupp.smul_apply, DFinsupp.zero_apply]
  by_cases h : j = n
  · subst h; rw [hn, smul_zero]
  · refine Subtype.ext ?_
    simpa [smul_eq_mul] using unitIdem_mul_of_mem_ne (Ne.symm h) (m j).2

private theorem not_free_localization {g : EvSeq.{u}} (hg : g ∉ evZeroIdeal.{u}) :
    ¬ Module.Free (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) totalModule.{u}) := by
  classical
  have hinf := infinite_support_of_notMem hg
  have : Nontrivial (LocalizedModule (Submonoid.powers g) totalModule.{u}) := by
    obtain ⟨n, hn⟩ := hinf.nonempty
    refine ⟨LocalizedModule.mk (DirectSum.lof EvSeq.{u} ℕ
      (fun m => ↥(summandIdeal.{u} m)) n ⟨unitIdem.{u} n, Ideal.mem_span_singleton_self _⟩) 1,
      0, ?_⟩
    intro hzero
    rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g), LocalizedModule.mk_eq] at hzero
    obtain ⟨u, hu⟩ := hzero
    simp only [one_smul, smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul] at hu
    have hz := congrArg (DirectSum.component EvSeq.{u} ℕ (fun m => ↥(summandIdeal.{u} m)) n) hu
    rw [DirectSum.component.lof_self, map_zero] at hz
    have hz' : (u : EvSeq.{u}) * unitIdem.{u} n = 0 := by
      simpa [smul_eq_mul] using congrArg Subtype.val hz
    exact mul_unitIdem_ne_zero_of_mem_powers hn u.2 hz'
  refine not_free_of_forall_exists_smul_eq_zero fun x => ?_
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨n, hn, hmn⟩ := hinf.exists_notMem_finite (DFinsupp.finite_support m)
    refine ⟨algebraMap EvSeq.{u} (Localization.Away g) (unitIdem.{u} n), ?_, ?_⟩
    · rw [Ne, IsLocalization.map_eq_zero_iff (Submonoid.powers g)]
      rintro ⟨u, hu⟩
      exact mul_unitIdem_ne_zero_of_mem_powers hn u.2 hu
    · rw [algebraMap_smul, LocalizedModule.smul'_mk,
        unitIdem_smul_eq_zero (not_not.mp hmn), LocalizedModule.zero_mk]

private theorem not_isLocallyFree_totalModule :
    ¬ Module.IsLocallyFree EvSeq.{u} totalModule.{u} := by
  rintro ⟨ι, f, hspan, hfree⟩
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ evZeroIdeal.{u} := by
    by_contra h
    refine one_notMem_evZeroIdeal.{u} ?_
    have hle : Ideal.span (Set.range f) ≤ evZeroIdeal.{u} :=
      Ideal.span_le.mpr (by
        rintro x ⟨j, rfl⟩
        exact not_not.mp fun hj => h ⟨j, hj⟩)
    rw [hspan] at hle
    exact hle Submodule.mem_top
  exact not_free_localization hi (hfree i)

/-! ### The example -/

/-- There is a countable ring `R` and a projective `R`-module which is a direct sum of countably
many finite locally free modules but is not itself locally free.

The summands `εₙ R` have rank one at the primes avoiding `εₙ` and rank zero at the others, so
they are finite locally free but not of rank one. The rank-one statement of Stacks 05WL is in
`StacksFrontier.Examples.Algebra.RankOneSumNotLocallyFree.Reduction`. -/
theorem exists_countable_projective_directSum_isFiniteLocallyFree_not_isLocallyFree :
    ∃ (R : Type u) (hR : CommRing R),
      letI : CommRing R := hR
      Countable R ∧
        ∃ L : ℕ → ModuleCat.{u} R,
          (∀ n, Module.IsFiniteLocallyFree R (L n)) ∧
            Module.Projective R (DirectSum ℕ fun n => L n) ∧
              ¬ Module.IsLocallyFree R (DirectSum ℕ fun n => L n) := by
  refine ⟨EvSeq.{u}, inferInstance, countable_evSeq.{u}, fun n => ModuleCat.of _
    ↥(summandIdeal.{u} n), fun n => ?_, ?_, not_isLocallyFree_totalModule.{u}⟩
  · have := finite_summandIdeal.{u} n
    have := projective_summandIdeal.{u} n
    exact isFiniteLocallyFree_of_finite_projective _
  · exact Module.Projective.directSum_iff.mpr projective_summandIdeal.{u}

end Stacks.Examples

end
