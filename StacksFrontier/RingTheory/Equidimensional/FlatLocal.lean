module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Stacks Tag 0AW4 (Lemma 15.111.3)

Let `A → B` be a flat local map of Noetherian local rings with `B` catenary and
`Spec(B)` equidimensional. Then (1) `Spec(B / pB)` is equidimensional for every
prime `p ⊆ A`, and (2) `A` is catenary and `Spec(A)` is equidimensional.

## Main statements

* `flat_local_catenary_equidim_fibre`: Stacks 0AW4 (1), the fibre is equidimensional.
* `specEquidimensional_iff_equidimensional`: the reusable bridge identifying this module's
  `SpecEquidimensional R` with the project-wide `TopologicalSpace.Equidimensional (PrimeSpectrum
    R)`.
* `specEquidimensional_quotients_and_isCatenary_of_flat_local`: the two clauses above, recombined
  into the single conjunction the Stacks source states, phrased with
  `TopologicalSpace.Equidimensional`.
* `flat_local_catenary_equidim_base`: Stacks 0AW4 (2), the base is catenary and equidimensional.

## Proof outline

Catenarity of `Spec B` makes `coheight` drop by exactly one along covering pairs, and with
equidimensionality this gives `height Q + coheight Q = dim B` for every prime `Q` of `B`. A prime
`Q` minimal over `pB` lies over `p` by going down, and has `height Q = height p` by the height
formula for flat maps (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), which gives (1).
Comparing the height formula at the closed points for `A → B` and for `A ⧸ p → B ⧸ pB` gives
`height p + dim (A ⧸ p) = dim A`; applied to `A ⧸ p` this shows `p ↦ dim (A ⧸ p)` is a dimension
function, so `A` is catenary (Stacks 02IA), and applied to minimal primes that `A` is
equidimensional.
-/

/-- `Spec(R)` is *equidimensional*: all minimal primes give quotient rings of equal
Krull dimension. -/
@[ega "0 16.1.4", ega "IV 5.1.12" "partial", ega "IV 7.1.2"]
def SpecEquidimensional (R : Type*) [CommRing R] : Prop :=
  ∀ p ∈ minimalPrimes R, ∀ q ∈ minimalPrimes R,
    ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ q)

/-- The coheight of a prime `P` equals the Krull dimension of the quotient
`R ⧸ P`. -/
lemma coheight_eq_ringKrullDim_quotient {R : Type*} [CommRing R] (P : PrimeSpectrum R) :
    (Order.coheight P : WithBot ℕ∞) = ringKrullDim (R ⧸ P.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

namespace FlatLocalCatenary

open Order TopologicalSpace

variable {B : Type*} [CommRing B]

/-- The irreducible closed set `V(p)`. -/
noncomputable abbrev vIC (p : PrimeSpectrum B) : IrreducibleCloseds (PrimeSpectrum B) :=
  OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds B p)

lemma vIC_lt_iff {p q : PrimeSpectrum B} : vIC q < vIC p ↔ p < q := by
  rw [OrderDual.ofDual_lt_ofDual, OrderIso.lt_iff_lt]

lemma vIC_le_iff {p q : PrimeSpectrum B} : vIC q ≤ vIC p ↔ p ≤ q := by
  rw [OrderDual.ofDual_le_ofDual, OrderIso.le_iff_le]

lemma vIC_covBy_iff {p q : PrimeSpectrum B} : vIC q ⋖ vIC p ↔ p ⋖ q := by
  rw [ofDual_covBy_ofDual_iff, apply_covBy_apply_iff]

/-- A covering chain of primes, reversed and pushed to irreducible closed sets. -/
noncomputable def icChain (s : CovChain B) : LTSeries (IrreducibleCloseds (PrimeSpectrum B)) :=
  LTSeries.mk s.length (fun i => vIC (s (Fin.rev i))) (by
    intro i j hij
    have h := (covToLT s).strictMono (Fin.rev_lt_rev.mpr hij)
    exact vIC_lt_iff.mpr h)

lemma icChain_length (s : CovChain B) : (icChain s).length = s.length := rfl

lemma icChain_isMaximal (s : CovChain B) :
    IrreducibleClosedsCodim.IsMaximalChain (icChain s) (vIC s.last) (vIC s.head) := by
  refine ⟨?_, ?_, ?_⟩
  · change vIC (s (Fin.rev 0)) = _
    rw [Fin.rev_zero]; rfl
  · change vIC (s (Fin.rev (Fin.last _))) = _
    rw [Fin.rev_last]; rfl
  · intro (i : Fin s.length)
    change vIC (s (Fin.rev i.castSucc)) ⋖ vIC (s (Fin.rev i.succ))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact vIC_covBy_iff.mpr (s.step (Fin.rev i))

/-- In a Noetherian local ring with catenary spectrum, coheight is cover-additive. -/
lemma coheight_covBy_of_isCatenarySpace [IsNoetherianRing B] [IsLocalRing B]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum B))
    (x y : PrimeSpectrum B) (hxy : x ⋖ y) : coheight x = coheight y + 1 := by
  obtain ⟨sy, syhead, sylast, sylen⟩ := exists_covchain_top y
  obtain ⟨sx, sxhead, sxlast, sxlen⟩ := exists_covchain_top x
  have hcons : (x, sy.head) ∈ {(a, b) : PrimeSpectrum B × PrimeSpectrum B | a ⋖ b} := by
    simpa [syhead] using hxy
  set sx' : CovChain B := sy.cons x hcons with hsx'
  have hx'head : sx'.head = x := RelSeries.head_cons _ _ _
  have hx'last : sx'.last = ⊤ := by rw [hsx', RelSeries.last_cons]; exact sylast
  have hle : vIC (⊤ : PrimeSpectrum B) ≤ vIC x := vIC_le_iff.mpr le_top
  have h1 := (hcat _ _ hle).2 (icChain sx) (by
    have := icChain_isMaximal sx; rwa [sxhead, sxlast] at this)
  have h2 := (hcat _ _ hle).2 (icChain sx') (by
    have := icChain_isMaximal sx'; rwa [hx'head, hx'last] at this)
  rw [icChain_length, sxlen] at h1
  rw [icChain_length, hsx', RelSeries.cons_length] at h2
  rw [h1, ← h2]; push_cast; rw [sylen]

/-- Coheight of a prime is the dimension of the quotient, as an `ℕ∞` equation. -/
lemma coheight_eq_of_quot {B : Type*} [CommRing B] (I : Ideal B) (Q : PrimeSpectrum B)
    (hIQ : I ≤ Q.asIdeal) (Q' : PrimeSpectrum (B ⧸ I))
    (hQ' : Q'.asIdeal = Q.asIdeal.map (Ideal.Quotient.mk I)) :
    coheight Q' = coheight Q := by
  have h1 := coheight_eq_ringKrullDim_quotient Q'
  have h2 := coheight_eq_ringKrullDim_quotient Q
  rw [hQ', ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIQ)] at h1
  exact_mod_cast h1.trans h2.symm

/-- Telescoping along a covering chain when coheight is cover-additive. -/
lemma coheight_head_eq {B : Type*} [CommRing B]
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (s : CovChain B) : coheight s.head = coheight s.last + s.length := by
  induction s using RelSeries.inductionOn with
  | singleton x => simp
  | cons p x hx ih =>
    rw [RelSeries.head_cons, RelSeries.last_cons, RelSeries.cons_length, hcov x p.head hx, ih]
    push_cast; ring

/-- In a Noetherian local ring, every prime has finite height. -/
lemma height_ne_top_of_isLocalRing [IsNoetherianRing B] [IsLocalRing B] (Q : PrimeSpectrum B) :
    height Q ≠ ⊤ := by
  have h1 : (height Q : WithBot ℕ∞) ≤ ringKrullDim B := height_le_krullDim Q
  have h2 : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  intro h; rw [h] at h1; exact (lt_of_le_of_lt h1 h2).ne rfl

lemma wf_instances [IsNoetherianRing B] [IsLocalRing B] :
    WellFoundedLT (PrimeSpectrum B) ∧ WellFoundedGT (PrimeSpectrum B) := by
  have hgt : WellFoundedGT (PrimeSpectrum B) := by
    apply WellFounded.onFun (f := PrimeSpectrum.asIdeal) (r := (· > ·))
    exact (wellFounded_gt : WellFounded (· > · : Ideal B → Ideal B → Prop))
  have hfd : FiniteDimensionalOrder (PrimeSpectrum B) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
    exact ⟨(Order.bot_lt_krullDim).ne', ringKrullDim_lt_top.ne⟩
  exact ⟨SetRel.IsWellFounded.of_finiteDimensional
    {(a, b) : PrimeSpectrum B × PrimeSpectrum B | a < b}, hgt⟩

/-- A covering chain between any two comparable primes of a Noetherian local ring. -/
lemma exists_covChain [IsNoetherianRing B] [IsLocalRing B] (p q : PrimeSpectrum B)
    (hpq : p ≤ q) : ∃ t : CovChain B, t.head = p ∧ t.last = q := by
  obtain ⟨_, _⟩ := wf_instances (B := B)
  rcases hpq.eq_or_lt with rfl | hlt
  · exact ⟨RelSeries.singleton _ p, rfl, rfl⟩
  · let s0 : LTSeries (PrimeSpectrum B) := LTSeries.mk 1 ![p, q] (by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    obtain ⟨t, i, hti, hi0, hilast⟩ := LTSeries.exists_relSeries_covBy s0
    refine ⟨t, ?_, ?_⟩
    · have h := congrFun hti 0
      simp only [Function.comp_apply, hi0] at h
      exact h
    · have h := congrFun hti (Fin.last _)
      simp only [Function.comp_apply, hilast] at h
      exact h

/-- Coheight of minimal primes, under equidimensionality, is independent of the prime. -/
lemma coheight_minimal_eq (heq : SpecEquidimensional B) (q q' : PrimeSpectrum B)
    (hq : q.asIdeal ∈ minimalPrimes B) (hq' : q'.asIdeal ∈ minimalPrimes B) :
    coheight q = coheight q' := by
  have h := heq _ hq _ hq'
  rw [← coheight_eq_ringKrullDim_quotient, ← coheight_eq_ringKrullDim_quotient] at h
  exact_mod_cast h

lemma exists_minimal_le (x : PrimeSpectrum B) :
    ∃ q : PrimeSpectrum B, q.asIdeal ∈ minimalPrimes B ∧ q ≤ x := by
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := x.asIdeal)
    bot_le
  exact ⟨⟨q, hq.1.1⟩, hq, hqx⟩

/-- **L1.** In a Noetherian local ring with cover-additive coheight and equidimensional spectrum,
`height Q + coheight Q` is the common coheight of the minimal primes. -/
lemma height_add_coheight_eq [IsNoetherianRing B] [IsLocalRing B]
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (heq : SpecEquidimensional B) (Q q0 : PrimeSpectrum B) (hq0 : q0.asIdeal ∈ minimalPrimes B) :
    height Q + coheight Q = coheight q0 := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (height_ne_top_of_isLocalRing Q)
    obtain ⟨l, hllast, hllen⟩ := exists_series_of_le_height Q (n := n) hn.le
    obtain ⟨sQ, sQhead, sQlast, sQlen⟩ := exists_covchain_top Q
    have hconn : l.last = (covToLT sQ).head := by rw [covToLT_head, sQhead, hllast]
    have hlen := length_le_coheight_head (p := l.smash (covToLT sQ) hconn)
    rw [RelSeries.smash_length, RelSeries.head_smash, covToLT_length] at hlen
    obtain ⟨q1, hq1, hq1le⟩ := exists_minimal_le l.head
    calc height Q + coheight Q = (l.length : ℕ∞) + (sQ.length : ℕ∞) := by rw [hllen, ← hn, sQlen]
      _ ≤ coheight l.head := by exact_mod_cast hlen
      _ ≤ coheight q1 := coheight_anti hq1le
      _ = coheight q0 := coheight_minimal_eq heq q1 q0 hq1 hq0
  · obtain ⟨q1, hq1, hq1le⟩ := exists_minimal_le Q
    obtain ⟨t, thead, tlast⟩ := exists_covChain q1 Q hq1le
    have htele := coheight_head_eq hcov t
    rw [thead, tlast] at htele
    have hth : (t.length : ℕ∞) ≤ height Q := by
      have := length_le_height_last (p := covToLT t)
      rwa [covToLT_length, show (covToLT t).last = t.last from covToLT_apply t _, tlast] at this
    rw [← coheight_minimal_eq heq q1 q0 hq1 hq0, htele, add_comm]
    gcongr


section flat

variable {A : Type*} [CommRing A] [Algebra A B]

/-- A prime minimal over `pB` lies over `p` (going down for flat maps). -/
lemma liesOver_of_mem_minimalPrimes [Module.Flat A B] (p : Ideal A) [p.IsPrime] (Q : Ideal B)
    (hQ : Q ∈ (p.map (algebraMap A B)).minimalPrimes) : Q.LiesOver p := by
  have hQp : Q.IsPrime := hQ.1.1
  have hle : p ≤ Q.under A := Ideal.map_le_iff_le_comap.mp hQ.1.2
  refine ⟨?_⟩
  by_contra hne
  obtain ⟨P, hPQ, hP, hPo⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle hne)
  have hmap : p.map (algebraMap A B) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]; exact (Ideal.LiesOver.over (P := P) (p := p)).le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hmap⟩ hPQ
  have : P = Q := le_antisymm hPQ hQP
  subst this
  exact hne hPo.over

lemma map_mem_minimalPrimes_quot (I Q : Ideal B) (hQ : Q ∈ I.minimalPrimes) :
    Q.map (Ideal.Quotient.mk I) ∈ minimalPrimes (B ⧸ I) := by
  rw [Ideal.minimalPrimes_eq_comap] at hQ
  obtain ⟨P, hP, rfl⟩ := hQ
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- A prime minimal over `pB` has the height of `p`. -/
lemma height_eq_of_mem_minimalPrimes [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (Q : Ideal B)
    (hQ : Q ∈ (p.map (algebraMap A B)).minimalPrimes) : Q.height = p.height := by
  have : Q.IsPrime := hQ.1.1
  have := liesOver_of_mem_minimalPrimes p Q hQ
  have hmin := map_mem_minimalPrimes_quot _ Q hQ
  have : (Q.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).IsPrime := hmin.1.1
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q,
    Ideal.height_eq_zero_iff.mpr hmin, add_zero]

end flat


variable {B : Type*} [CommRing B]

/-- Primes of `B ⧸ I` pulled back to `B`. -/
abbrev pb (I : Ideal B) (x : PrimeSpectrum (B ⧸ I)) : PrimeSpectrum B :=
  ⟨x.asIdeal.comap (Ideal.Quotient.mk I), Ideal.comap_isPrime _ _⟩

lemma pb_le_iff (I : Ideal B) {x y : PrimeSpectrum (B ⧸ I)} : pb I x ≤ pb I y ↔ x ≤ y := by
  change x.asIdeal.comap _ ≤ y.asIdeal.comap _ ↔ x.asIdeal ≤ y.asIdeal
  exact Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _

lemma pb_lt_iff (I : Ideal B) {x y : PrimeSpectrum (B ⧸ I)} : pb I x < pb I y ↔ x < y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, pb_le_iff, pb_le_iff]

lemma map_pb (I : Ideal B) (x : PrimeSpectrum (B ⧸ I)) :
    (pb I x).asIdeal.map (Ideal.Quotient.mk I) = x.asIdeal :=
  Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

lemma le_pb (I : Ideal B) (x : PrimeSpectrum (B ⧸ I)) : I ≤ (pb I x).asIdeal := by
  intro a ha
  change Ideal.Quotient.mk I a ∈ x.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact zero_mem _

lemma coheight_pb (I : Ideal B) (x : PrimeSpectrum (B ⧸ I)) :
    coheight x = coheight (pb I x) :=
  coheight_eq_of_quot I (pb I x) (le_pb I x) x (map_pb I x).symm

/-- **C.** Cover-additivity of coheight passes to quotients. -/
lemma hcov_quot (I : Ideal B)
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1) :
    ∀ x y : PrimeSpectrum (B ⧸ I), x ⋖ y → coheight x = coheight y + 1 := by
  intro x y hxy
  rw [coheight_pb I x, coheight_pb I y]
  refine hcov _ _ ⟨(pb_lt_iff I).mpr hxy.1, fun z hxz hzy => ?_⟩
  have hIz : I ≤ z.asIdeal := (le_pb I x).trans hxz.le
  let z' : PrimeSpectrum (B ⧸ I) :=
    ⟨z.asIdeal.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
  have hz : pb I z' = z := by
    ext1
    change (z.asIdeal.map _).comap _ = _
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIz]
  rw [← hz] at hxz hzy
  exact hxy.2 ((pb_lt_iff I).mp hxz) ((pb_lt_iff I).mp hzy)

variable {A : Type*} [CommRing A] [Algebra A B]

/-- Finiteness of the height of a prime of a Noetherian local ring. -/
@[ega "IV 5.1.6" "partial"]
lemma ideal_height_ne_top [IsNoetherianRing A] [IsLocalRing A] (p : Ideal A) [p.IsPrime] :
    p.height ≠ ⊤ := by
  have h1 : (p.height : WithBot ℕ∞) ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
  intro h
  have h2 := h1.trans_lt ringKrullDim_lt_top
  rw [h] at h2
  exact lt_irrefl _ h2

/-- For `Q` minimal over `pB`: `height p + coheight Q` is the common coheight of minimal primes. -/
lemma height_add_coheight_of_mem_minimalPrimes [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing B] [Module.Flat A B]
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (hequi : SpecEquidimensional B) (p : Ideal A) [p.IsPrime] (q0 : PrimeSpectrum B)
    (hq0 : q0.asIdeal ∈ minimalPrimes B) (Q : Ideal B)
    (hQ : Q ∈ (p.map (algebraMap A B)).minimalPrimes) :
    p.height + coheight (⟨Q, hQ.1.1⟩ : PrimeSpectrum B) = coheight q0 := by
  have h := height_add_coheight_eq hcov hequi ⟨Q, hQ.1.1⟩ q0 hq0
  rwa [← PrimeSpectrum.height_eq_orderHeight, height_eq_of_mem_minimalPrimes p Q hQ] at h

/-- The dimension of `(B ⧸ I) ⧸ P` is the coheight of the pulled-back prime. -/
lemma ringKrullDim_quot_quot (I : Ideal B) (P : Ideal (B ⧸ I)) (hP : P ∈ minimalPrimes (B ⧸ I)) :
    ∃ hQ : P.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes,
      ringKrullDim ((B ⧸ I) ⧸ P) =
        coheight (⟨P.comap (Ideal.Quotient.mk I), hQ.1.1⟩ : PrimeSpectrum B) := by
  have hQ : P.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hP, rfl⟩
  refine ⟨hQ, ?_⟩
  rw [coheight_eq_ringKrullDim_quotient]
  conv_lhs => rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P]
  exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQ.1.2)

/-- **Part (1), core form** (cover-additive coheight instead of catenary). -/
lemma equidim_fibre [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Module.Flat A B]
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (hequi : SpecEquidimensional B) (p : Ideal A) [p.IsPrime] :
    SpecEquidimensional (B ⧸ p.map (algebraMap A B)) := by
  obtain ⟨q0, hq0, -⟩ := exists_minimal_le (⊤ : PrimeSpectrum B)
  intro P1 hP1 P2 hP2
  obtain ⟨hQ1, e1⟩ := ringKrullDim_quot_quot _ P1 hP1
  obtain ⟨hQ2, e2⟩ := ringKrullDim_quot_quot _ P2 hP2
  rw [e1, e2]
  have := (height_add_coheight_of_mem_minimalPrimes hcov hequi p q0 hq0 _ hQ1).trans
    (height_add_coheight_of_mem_minimalPrimes hcov hequi p q0 hq0 _ hQ2).symm
  exact_mod_cast WithTop.add_left_cancel (ideal_height_ne_top p) this


section L2

open IsLocalRing

/-- The image of the maximal ideal in a quotient of a local ring is its maximal ideal. -/
lemma map_maximalIdeal_quot [IsLocalRing B] (J : Ideal B) [IsLocalRing (B ⧸ J)] :
    (maximalIdeal B).map (Ideal.Quotient.mk J) = maximalIdeal (B ⧸ J) := by
  have h : (maximalIdeal (B ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

lemma quot_nontrivial_of_le [IsLocalRing B] {J : Ideal B} (hJ : J ≤ maximalIdeal B) :
    Nontrivial (B ⧸ J) :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ)

/-- The quotient of a local ring by an ideal inside the maximal ideal is local. -/
private lemma isLocalRing_quot_of_le [IsLocalRing B] {J : Ideal B} (hJ : J ≤ maximalIdeal B) :
    IsLocalRing (B ⧸ J) :=
  have := quot_nontrivial_of_le hJ
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The fibre term of the height formula at the closed point. -/
lemma height_top_eq_add [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Module.Flat A B] (hlo : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A) :
    height (⊤ : PrimeSpectrum B) = height (⊤ : PrimeSpectrum A) +
      ((maximalIdeal B).map
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).height := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) := ⟨hlo.symm⟩
  rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight]
  exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)


/-- The fibre term, as the dimension of the closed fibre. -/
lemma fibre_height_eq [IsLocalRing B] (K : Ideal B) (hK : K ≤ maximalIdeal B) :
    (((maximalIdeal B).map (Ideal.Quotient.mk K)).height : WithBot ℕ∞) = ringKrullDim (B ⧸ K) := by
  have := isLocalRing_quot_of_le hK
  rw [map_maximalIdeal_quot, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]

lemma algebraMap_quot_comp (p : Ideal A) :
    (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B))).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk (p.map (algebraMap A B))).comp (algebraMap A B) :=
  RingHom.ext Ideal.Quotient.algebraMap_quotient_map_quotient

/-- Flatness passes to the quotient `A ⧸ p → B ⧸ pB`. -/
lemma flat_quot [Module.Flat A B] (p : Ideal A) :
    Module.Flat (A ⧸ p) (B ⧸ p.map (algebraMap A B)) := by
  have := Module.Flat.baseChange A (A ⧸ p) B
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p).toLinearEquiv

/-- The quotient map `A ⧸ p → B ⧸ pB` of a local map is local on maximal ideals. -/
lemma comap_maximalIdeal_quot [IsLocalRing A] [IsLocalRing B]
    (hlo : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A) (p : Ideal A)
    [IsLocalRing (A ⧸ p)] [IsLocalRing (B ⧸ p.map (algebraMap A B))] :
    (maximalIdeal (B ⧸ p.map (algebraMap A B))).comap
      (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B))) = maximalIdeal (A ⧸ p) := by
  have hmB : (maximalIdeal (B ⧸ p.map (algebraMap A B))).comap
      (Ideal.Quotient.mk (p.map (algebraMap A B))) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top)) ?_
  rw [← map_maximalIdeal_quot p, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
    algebraMap_quot_comp, ← Ideal.comap_comap, hmB, hlo]

/-- The height of the closed point of `Spec (A ⧸ x)` is the coheight of `x`. -/
private lemma height_top_quot_aux (x : PrimeSpectrum A) [IsLocalRing (A ⧸ x.asIdeal)] :
    height (⊤ : PrimeSpectrum (A ⧸ x.asIdeal)) = coheight x := by
  have h1 := coheight_eq_ringKrullDim_quotient x
  have h2 := height_top_eq_krullDim (α := PrimeSpectrum (A ⧸ x.asIdeal))
  exact_mod_cast h2.trans h1.symm

/-- **L2.** Under the hypotheses of 0FlatLocalCatenary (with cover-additive coheight on `Spec B`),
`height P + coheight P = dim A` for every prime `P` of `A`. -/
lemma height_add_coheight_base [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A]
    [IsLocalRing B] [Module.Flat A B]
    (hlo : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A)
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (hequi : SpecEquidimensional B) (P : PrimeSpectrum A) :
    height P + coheight P = height (⊤ : PrimeSpectrum A) := by
  set p := P.asIdeal with hpdef
  set I := p.map (algebraMap A B) with hIdef
  set J := (maximalIdeal A).map (algebraMap A B) with hJdef
  have hJB : J ≤ maximalIdeal B := by rw [hJdef, Ideal.map_le_iff_le_comap, hlo]
  have hIJ : I ≤ J := Ideal.map_mono (le_maximalIdeal P.2.ne_top)
  have hIB := hIJ.trans hJB
  have := isLocalRing_quot_of_le hIB
  have := isLocalRing_quot_of_le (le_maximalIdeal P.2.ne_top)
  have : Module.Flat (A ⧸ p) (B ⧸ I) := flat_quot p
  -- (a) the prime `Q` minimal over `pB`
  obtain ⟨q0, hq0, -⟩ := exists_minimal_le (⊤ : PrimeSpectrum B)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le (J := maximalIdeal B) hIB
  have ha := height_add_coheight_of_mem_minimalPrimes hcov hequi p q0 hq0 Q hQ
  have hpP : p.height = height P := PrimeSpectrum.height_eq_orderHeight P
  rw [hpP] at ha
  have ha' := height_add_coheight_eq hcov hequi ⊤ q0 hq0
  rw [coheight_top, add_zero] at ha'
  -- (c) the same computation in `B ⧸ pB`
  have hQb : Q.map (Ideal.Quotient.mk I) ∈ minimalPrimes (B ⧸ I) :=
    map_mem_minimalPrimes_quot I Q hQ
  have hc := height_add_coheight_eq (hcov_quot I hcov) (equidim_fibre hcov hequi p) ⊤
    ⟨_, hQb.1.1⟩ hQb
  rw [coheight_top, add_zero, coheight_eq_of_quot I ⟨Q, hQ.1.1⟩ hQ.1.2 ⟨_, hQb.1.1⟩ rfl] at hc
  -- (d) the height formula for `A ⧸ p → B ⧸ pB`
  have hlo' := comap_maximalIdeal_quot hlo p
  have hd := height_top_eq_add hlo'
  have hb := height_top_eq_add hlo
  -- the two closed fibres agree
  have hJbar : (maximalIdeal (A ⧸ p)).map (algebraMap (A ⧸ p) (B ⧸ I)) =
      J.map (Ideal.Quotient.mk I) := by
    rw [← map_maximalIdeal_quot p, Ideal.map_map, algebraMap_quot_comp, ← Ideal.map_map]
  have hJbarB : (maximalIdeal (A ⧸ p)).map (algebraMap (A ⧸ p) (B ⧸ I)) ≤ maximalIdeal (B ⧸ I) := by
    rw [hJbar, ← map_maximalIdeal_quot I]; exact Ideal.map_mono hJB
  have hf : ((maximalIdeal (B ⧸ I)).map (Ideal.Quotient.mk
      ((maximalIdeal (A ⧸ p)).map (algebraMap (A ⧸ p) (B ⧸ I))))).height =
      ((maximalIdeal B).map (Ideal.Quotient.mk J)).height := by
    have h1 := fibre_height_eq _ hJbarB
    have h2 := fibre_height_eq J hJB
    have h3 : ringKrullDim ((B ⧸ I) ⧸ (maximalIdeal (A ⧸ p)).map (algebraMap (A ⧸ p) (B ⧸ I))) =
        ringKrullDim (B ⧸ J) := by
      rw [hJbar]; exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIJ)
    rw [h3] at h1
    exact_mod_cast h1.trans h2.symm
  -- (e) `dim (A ⧸ p) = coheight P`
  have he : height (⊤ : PrimeSpectrum (A ⧸ p)) = coheight P := height_top_quot_aux P
  rw [hf, he, hc] at hd
  rw [hb] at ha'
  have hfin : ((maximalIdeal B).map (Ideal.Quotient.mk J)).height ≠ ⊤ := by
    intro h; apply height_ne_top_of_isLocalRing (⊤ : PrimeSpectrum B); rw [hb, h, add_top]
  rw [hd, ← ha', ← add_assoc] at ha
  exact WithTop.add_right_cancel hfin ha


/-- A prime of `A` containing `x`, as a prime of `A ⧸ x`. -/
abbrev pushQ (x y : PrimeSpectrum A) (hxy : x ≤ y) : PrimeSpectrum (A ⧸ x.asIdeal) :=
  ⟨y.asIdeal.map (Ideal.Quotient.mk x.asIdeal), Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hxy)⟩

lemma pb_pushQ (x y : PrimeSpectrum A) (hxy : x ≤ y) : pb x.asIdeal (pushQ x y hxy) = y := by
  ext1
  change (y.asIdeal.map _).comap _ = _
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hxy]

/-- If `x ⋖ y` then the image of `y` in `Spec (A ⧸ x)` has height one. -/
lemma height_pushQ_of_covBy (x y : PrimeSpectrum A) (hxy : x ⋖ y) :
    height (pushQ x y hxy.le) = 1 := by
  set I := x.asIdeal
  have hlt : pushQ x x le_rfl < pushQ x y hxy.le := by
    rw [← pb_lt_iff I, pb_pushQ, pb_pushQ]; exact hxy.1
  apply le_antisymm
  · rw [height_le_iff]
    intro l hl
    by_contra hcon
    rw [not_le] at hcon
    have hn : 2 ≤ l.length := by exact_mod_cast (show (1 : ℕ∞) < l.length from hcon)
    set n := l.length
    let i0 : Fin (n + 1) := ⟨n - 2, by omega⟩
    let i1 : Fin (n + 1) := ⟨n - 1, by omega⟩
    have h01 : l i0 < l i1 := l.strictMono (by simp only [Fin.lt_def, i0, i1]; omega)
    have h1l : l i1 < l.last := l.strictMono (by simp only [Fin.lt_def, i1, Fin.val_last]; omega)
    have hA : x < pb I (l i1) :=
      lt_of_le_of_lt (le_pb I (l i0)) ((pb_lt_iff I).mpr h01)
    have hB : pb I (l i1) < y := by
      rw [← pb_pushQ x y hxy.le]; exact (pb_lt_iff I).mpr (h1l.trans_le hl)
    exact hxy.2 hA hB
  · let s0 : LTSeries (PrimeSpectrum (A ⧸ I)) := LTSeries.mk 1 ![pushQ x x le_rfl, pushQ x y hxy.le]
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    have := length_le_height_last (p := s0)
    exact this

/-- `dim (A ⧸ x) = coheight x`, stated in `Spec (A ⧸ x)`. -/
lemma height_top_quot (x : PrimeSpectrum A) [IsLocalRing (A ⧸ x.asIdeal)] :
    height (⊤ : PrimeSpectrum (A ⧸ x.asIdeal)) = coheight x :=
  height_top_quot_aux x

/-- Coheight is cover-additive on `Spec A` (the key step of 0FlatLocalCatenary (2)). -/
lemma coheight_covBy_base [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A]
    [IsLocalRing B] [Module.Flat A B]
    (hlo : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A)
    (hcov : ∀ x y : PrimeSpectrum B, x ⋖ y → coheight x = coheight y + 1)
    (hequi : SpecEquidimensional B) (x y : PrimeSpectrum A) (hxy : x ⋖ y) :
    coheight x = coheight y + 1 := by
  set p := x.asIdeal with hpdef
  set I := p.map (algebraMap A B) with hIdef
  have hIB : I ≤ maximalIdeal B := by
    rw [hIdef, Ideal.map_le_iff_le_comap, hlo]; exact le_maximalIdeal x.2.ne_top
  have := isLocalRing_quot_of_le hIB
  have := isLocalRing_quot_of_le (le_maximalIdeal x.2.ne_top)
  have : Module.Flat (A ⧸ p) (B ⧸ I) := flat_quot p
  have hlo' := comap_maximalIdeal_quot hlo p
  have h := height_add_coheight_base hlo' (hcov_quot I hcov) (equidim_fibre hcov hequi p)
    (pushQ x y hxy.le)
  rw [height_pushQ_of_covBy x y hxy, height_top_quot x, coheight_pb p, pb_pushQ] at h
  rw [← h, add_comm]

/-- `Spec A` is sober in the sense of `StacksSober`. -/
lemma stacksSober_primeSpectrum : StacksSober (PrimeSpectrum A) :=
  stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩

end L2

end FlatLocalCatenary

open FlatLocalCatenary Order

/-- **Stacks 0AW4 (1).** For a flat local map `A → B` of Noetherian local rings with
`B` catenary and `Spec(B)` equidimensional, the fibre `Spec(B / pB)` is
equidimensional for every prime `p ⊆ A`. -/
@[stacks 0AW4 "(1)", ega "IV 7.1.3" "(ii) 'in particular'"]
theorem flat_local_catenary_equidim_fibre (A B : Type*) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum B))
    (hequi : SpecEquidimensional B)
    (p : Ideal A) [p.IsPrime] :
    SpecEquidimensional (B ⧸ p.map (algebraMap A B)) := by
  exact equidim_fibre (coheight_covBy_of_isCatenarySpace hcat) hequi p

/-- **Stacks 0AW4 (2).** For a flat local map `A → B` of Noetherian local rings with
`B` catenary and `Spec(B)` equidimensional, the base `A` is catenary and `Spec(A)`
is equidimensional. -/
@[stacks 0AW4 "(2)", ega "IV 7.1.3" "(i)", ega "IV 7.8.3" "(x)", ega "IV 7.8.4" "partial"]
theorem flat_local_catenary_equidim_base (A B : Type*) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum B))
    (hequi : SpecEquidimensional B) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) ∧ SpecEquidimensional A := by
  have hcov := coheight_covBy_of_isCatenarySpace hcat
  have hlo := IsLocalRing.maximalIdeal_comap (algebraMap A B)
  refine ⟨(isCatenarySpace_and_topCodim_eq_of_isDimensionFunction _ stacksSober_primeSpectrum
    deltaDim ⟨?_, ?_⟩).1, ?_⟩
  · exact fun x y h hne => deltaDim_lt_of_specializes x y h hne
  · intro x y himm
    have hxy : x ⋖ y := (immediateSpec_iff_covby x y).mp himm
    exact (deltaDim_eq_iff_coheight x y).mpr (coheight_covBy_base hlo hcov hequi x y hxy)
  · intro p hp q hq
    have hL : ∀ P : PrimeSpectrum A, P.asIdeal ∈ minimalPrimes A →
        coheight P = height (⊤ : PrimeSpectrum A) := by
      intro P hP
      have h0 : height P = 0 := by
        rw [← PrimeSpectrum.height_eq_orderHeight]; exact Ideal.height_eq_zero_iff.mpr hP
      have := height_add_coheight_base hlo hcov hequi P
      rwa [h0, zero_add] at this
    have e1 := coheight_eq_ringKrullDim_quotient (⟨p, hp.1.1⟩ : PrimeSpectrum A)
    have e2 := coheight_eq_ringKrullDim_quotient (⟨q, hq.1.1⟩ : PrimeSpectrum A)
    change _ = ringKrullDim (A ⧸ p) at e1
    change _ = ringKrullDim (A ⧸ q) at e2
    rw [← e1, ← e2, hL _ hp, hL _ hq]

section EquidimensionalBridge

open TopologicalSpace PrimeSpectrum



/-- The dimension of the closed subset `V(I) ⊆ Spec R` is the Krull dimension of `R ⧸ I`. -/
theorem topologicalKrullDim_zeroLocus {R : Type*} [CommRing R] (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let e : PrimeSpectrum (R ⧸ I) ≃ₜ (PrimeSpectrum.zeroLocus (I : Set R)) :=
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).toHomeomorph.trans (Homeomorph.setCongr hrange)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]

/-- `SpecEquidimensional R` is exactly topological equidimensionality of `Spec R`. -/
theorem specEquidimensional_iff_equidimensional {R : Type*} [CommRing R] :
    SpecEquidimensional R ↔ Equidimensional (PrimeSpectrum R) := by
  constructor
  · intro h Z hZ W hW
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes R] at hZ hW
    obtain ⟨p, hp, rfl⟩ := hZ
    obtain ⟨q, hq, rfl⟩ := hW
    simp only [Function.comp_apply]
    rw [topologicalKrullDim_zeroLocus, topologicalKrullDim_zeroLocus]
    exact h p hp q hq
  · intro h p hp q hq
    have hpp : p.IsPrime := hp.1.1
    have hqp : q.IsPrime := hq.1.1
    have h' := h (PrimeSpectrum.zeroLocus (p : Set R))
        (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
          (by simp only [hpp.radical]; exact hp))
        (PrimeSpectrum.zeroLocus (q : Set R))
        (PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
          (by simp only [hqp.radical]; exact hq))
    rwa [topologicalKrullDim_zeroLocus, topologicalKrullDim_zeroLocus] at h'

/-- **Faithful coverage of Stacks 0AW4.** Main's two clauses
`flat_local_catenary_equidim_fibre` and `flat_local_catenary_equidim_base`, which are stated with
`SpecEquidimensional`, together yield the source's single conjunction stated with
`TopologicalSpace.Equidimensional`. -/
@[ega "IV 7.1.3"]
theorem specEquidimensional_quotients_and_isCatenary_of_flat_local
    (A : Type*) (B : Type*) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum B))
    (hequi : Equidimensional (PrimeSpectrum B)) :
    (∀ p : Ideal A, p.IsPrime →
      Equidimensional (PrimeSpectrum (B ⧸ p.map (algebraMap A B)))) ∧
      IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) ∧
      Equidimensional (PrimeSpectrum A) := by
  have hspec : SpecEquidimensional B := specEquidimensional_iff_equidimensional.mpr hequi
  obtain ⟨hcatA, hequiA⟩ := flat_local_catenary_equidim_base A B hcat hspec
  refine ⟨fun p hp => ?_, hcatA, specEquidimensional_iff_equidimensional.mp hequiA⟩
  have := hp
  exact specEquidimensional_iff_equidimensional.mp
    (flat_local_catenary_equidim_fibre A B hcat hspec p)

end EquidimensionalBridge
