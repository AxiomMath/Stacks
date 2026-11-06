module

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Artinian.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ArtinianIdempotents

/-!
# Products of local rings over a henselian local ring

Lifting of idempotents of the closed fibre over a henselian local ring, the decomposition of a
module-finite algebra as a finite product of local rings (`exists_algEquiv_pi_isLocalRing`), and
the decomposition of a finite type algebra as `(Π i, Aᵢ) × B` (Stacks Tag 04GJ,
`exists_algEquiv_prod_of_henselianLocalRing`).
-/

@[expose] public section

universe u v

/-- An element lying in every maximal ideal lies in the Jacobson radical of `⊥`. -/
private theorem mem_jacobson_bot_of_forall_isMaximal {S : Type*} [CommRing S] {x : S}
    (h : ∀ M : Ideal S, M.IsMaximal → x ∈ M) : x ∈ (⊥ : Ideal S).jacobson := by
  rw [Ideal.jacobson, Submodule.mem_sInf]
  intro M hM
  simp only [Set.mem_ofPred_eq] at hM
  exact h M hM.right

/-- An idempotent of the closed fibre is the join of the primitive idempotents at the finitely
many primes it avoids, so it lifts as soon as those primitives do. For `A` module-finite over the
local ring `R`, given that each prime `q` over `𝔪` carries a lifted primitive idempotent `g_q ∈ A`
— the conclusion of `reduction_of_isolating_idem`, taken here as the hypothesis `hprim` — every
idempotent `x̄` of the closed fibre `Ā = A/𝔪A` lifts to an idempotent `e ∈ A` with `mk e = x̄`.

The closed fibre `Ā` is Artinian (`closedFibre_isArtinian'`) with finite discrete spectrum, and
its primes correspond to the primes `q` of `A` over `𝔪` (tag 00E5). The idempotent `x̄` is the
indicator of the finite set `Q₁ := {q over 𝔪 : x̄ ∉ image of q}` (tags 00EE, 00EC). For each
`q ∈ Q₁`, `hprim q` gives the primitive idempotent `g_q ∈ A` whose reduction is the indicator of
`{q}`; joining these, `e := ⨆_{q ∈ Q₁} g_q` as in `combine_isolating_idempotents`. Then `mk e` and
`x̄` are idempotents of `Ā` with the same image at every prime, hence equal, since idempotents of
an Artinian ring are determined by their residues. -/
lemma fibre_idempotent_lift_of_primitive
    (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (hprim : ∀ (q : Ideal A), q.IsPrime → q.LiesOver (IsLocalRing.maximalIdeal R) →
      ∃ g : A, IsIdempotentElem g ∧ g ∉ q ∧
        ∀ (q' : Ideal A), q'.IsPrime → q'.LiesOver (IsLocalRing.maximalIdeal R) → q' ≠ q → g ∈ q')
    (ex : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (hex : IsIdempotentElem ex) :
    ∃ e : A, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) e = ex := by
  -- On the Artinian closed fibre, ex corresponds to a finite set Q₁ of primes (tags 00EE, 00EC,
  -- 00E5); joining the per-prime lifts `hprim q` over Q₁ produces e with mk e = ex, since
  -- idempotents of an Artinian ring are determined by their residues.
  classical
  set π := Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) with hπ
  show ∃ e : A, IsIdempotentElem e ∧ π e = ex
  -- Ā = A/𝔪A is Artinian.
  have hart : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    closedFibre_isArtinian' R A
  -- Every maximal ideal `m` of `Ā` pulls back to a prime of `A` lying over `𝔪`.
  have hcomap_prime_lo : ∀ (m : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))),
      m.IsMaximal →
      (Ideal.comap π m).IsPrime ∧ (Ideal.comap π m).LiesOver (IsLocalRing.maximalIdeal R) := by
    intro m hm
    have : m.IsPrime := hm.isPrime
    have hqp : (Ideal.comap π m).IsPrime := Ideal.comap_isPrime _ m
    refine ⟨hqp, ?_⟩
    have h𝔪Aq : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ Ideal.comap π m := by
      intro y hy
      rw [Ideal.mem_comap]
      have hz : π y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
      rw [hz]; exact m.zero_mem
    constructor
    have h1 : (IsLocalRing.maximalIdeal R) ≤ Ideal.under R (Ideal.comap π m) := by
      rw [Ideal.under_def]
      refine le_trans ?_ (Ideal.comap_mono h𝔪Aq)
      exact Ideal.le_comap_map
    have hmax := IsLocalRing.maximalIdeal.isMaximal R
    have hne : (Ideal.under R (Ideal.comap π m)) ≠ ⊤ := by
      rw [Ideal.under_def]
      intro htop
      apply (Ideal.comap π m).ne_top_iff_one.mp (Ideal.IsPrime.ne_top hqp)
      have h1mem : (1:R) ∈ (Ideal.comap π m).comap (algebraMap R A) := htop ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1mem
      exact h1mem
    exact hmax.eq_of_le hne h1
  -- The (finite) index set: maximal ideals of `Ā`.
  have hMaxFin : {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) |
      I.IsMaximal}.Finite :=
    IsArtinianRing.setOfPred_isMaximal_finite
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
  -- Choose, for each maximal `m` of `Ā`, a primitive idempotent `G m ∈ A` supported at
  -- `comap π m`: so `G m ∉ comap π m`, i.e. `π (G m) ∉ m`, while `G m ∈ comap π m'` for every
  -- other maximal ideal `m'`.
  have hchoice : ∀ (m : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))), m.IsMaximal
      →
      ∃ g : A, IsIdempotentElem g ∧ g ∉ Ideal.comap π m ∧
        ∀ (q' : Ideal A), q'.IsPrime → q'.LiesOver (IsLocalRing.maximalIdeal R) →
          q' ≠ Ideal.comap π m → g ∈ q' := by
    intro m hm
    obtain ⟨hqp, hlo⟩ := hcomap_prime_lo m hm
    exact hprim (Ideal.comap π m) hqp hlo
  choose G hGidem hGnotin hGother using
    (fun (m : {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) // I.IsMaximal}) =>
      hchoice m.val m.property)
  -- The avoided set: maximal ideals `m` of `Ā` at which `ex ∉ m` (where `ex` restricts to `1`).
  -- Finite, so packaged as a `Finset` of the (finite) subtype of maximal ideals.
  have : Finite {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) // I.IsMaximal}
      :=
    hMaxFin.to_subtype
  have : Fintype {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) //
      I.IsMaximal} :=
    Fintype.ofFinite _
  set S : Finset {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) // I.IsMaximal}
      :=
    Finset.univ.filter (fun m => ex ∉ m.val) with hS
  -- The hom-aware join over `S` of the chosen primitive idempotents.
  -- Membership of `π e` in a prime `p` of `Ā` ⇔ all `π (G m) ∈ p` for `m ∈ S`.
  obtain ⟨e, heidem, hechar⟩ :
      ∃ e : A, IsIdempotentElem e ∧
        (∀ (p : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))), p.IsPrime →
          (π e ∈ p ↔ ∀ m ∈ S, π (G m) ∈ p)) := by
    clear hchoice hcomap_prime_lo
    induction S using Finset.induction with
    | empty =>
      refine ⟨0, IsIdempotentElem.zero, ?_⟩
      intro p hp; simp
    | @insert m₀ s' hnotin IH =>
      obtain ⟨e', he'idem, he'mem⟩ := IH
      have hbidem : IsIdempotentElem (G m₀) := hGidem m₀
      refine ⟨e' + G m₀ - e' * G m₀, ?_, ?_⟩
      · have h1 : e'*e' = e' := he'idem
        have h2 : G m₀ * G m₀ = G m₀ := hbidem
        show (e' + G m₀ - e'*G m₀)*(e' + G m₀ - e'*G m₀) = e' + G m₀ - e'*G m₀
        linear_combination (1 - 2*G m₀ + G m₀*G m₀) * h1 + (1 - 2*e' + e'*e') * h2 +
          (G m₀ - G m₀*G m₀) * h1
      · intro p hp
        set f' := π e' with hf'
        set b := π (G m₀) with hb
        have hf'idem : f' * f' = f' := by rw [hf', ← map_mul]; exact congrArg π he'idem
        have hbidem' : b * b = b := by rw [hb, ← map_mul]; exact congrArg π hbidem
        have hexpand : π (e' + G m₀ - e' * G m₀) = f' + b - f' * b := by
          simp [hf', hb, map_sub, map_add, map_mul]
        rw [hexpand]
        constructor
        · intro hmem i hi
          have hf'p : f' ∈ p := by
            have he : f' = f' * (f' + b - f'*b) := by linear_combination (b-1)*hf'idem
            rw [he]; exact Ideal.mul_mem_left _ _ hmem
          have hbp : b ∈ p := by
            have he : b = b * (f' + b - f'*b) := by linear_combination (f'-1)*hbidem'
            rw [he]; exact Ideal.mul_mem_left _ _ hmem
          rcases Finset.mem_insert.mp hi with h | h
          · subst h; exact hbp
          · exact (he'mem p hp).mp hf'p i h
        · intro hall
          have hf'p : f' ∈ p :=
            (he'mem p hp).mpr (fun i hi => hall i (Finset.mem_insert_of_mem hi))
          have hbp : b ∈ p := hall m₀ (Finset.mem_insert_self _ _)
          have he : f' + b - f'*b = f' + (b - f'*b) := by ring
          rw [he]
          exact Ideal.add_mem _ hf'p (Ideal.sub_mem _ hbp (Ideal.mul_mem_left _ _ hbp))
  refine ⟨e, heidem, ?_⟩
  -- It remains to show `π e = ex`. Both are idempotents; their difference is nilpotent because it
  -- lies in every maximal ideal of the Artinian ring `Ā` (= the nilradical = Jacobson radical).
  have hexidem : ex * ex = ex := hex
  -- comap π injective (π surjective): distinct maximals give distinct primes of `A`.
  have hcomap_inj : Function.Injective (Ideal.comap π) :=
    Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
  -- For an idempotent `x` and prime `p` of `Ā`, `x ∈ p ∨ 1 - x ∈ p` (image is `0` or `1`).
  have hidem01 : ∀ (x : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)), x * x = x →
      ∀ (p : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))), p.IsPrime →
      (x ∈ p ∨ (1 - x) ∈ p) := by
    intro x hx p hp
    have hprod : x * (1 - x) ∈ p := by
      have hz : x * (1 - x) = 0 := by linear_combination -hx
      rw [hz]; exact p.zero_mem
    exact hp.mem_or_mem hprod
  -- The crucial agreement at every maximal ideal `n` of `Ā`: `π e ∈ n ↔ ex ∈ n`.
  have hagree : ∀ (n : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))), n.IsMaximal →
      (π e ∈ n ↔ ex ∈ n) := by
    intro n hn
    have : n.IsPrime := hn.isPrime
    -- `π (G m) ∈ n ↔ n ≠ m`  (the indicator at `m`).
    have hindicator : ∀ (m : {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) //
        I.IsMaximal}),
        (π (G m) ∈ n ↔ n ≠ m.val) := by
      intro m
      constructor
      · intro hmem hnm
        -- if n = m then π (G m) ∈ m contradicts G m ∉ comap π m
        apply hGnotin m
        rw [Ideal.mem_comap]
        rw [← hnm] at *
        exact hmem
      · intro hnm
        -- n ≠ m : comap π n ≠ comap π m (injective), both prime over 𝔪, so G m ∈ comap π n
        have : n.IsPrime := hn.isPrime
        obtain ⟨hnp, hnlo⟩ := hcomap_prime_lo n hn
        have hne : Ideal.comap π n ≠ Ideal.comap π m.val := fun h => hnm (hcomap_inj h)
        have : G m ∈ Ideal.comap π n := hGother m (Ideal.comap π n) hnp hnlo hne
        rwa [Ideal.mem_comap] at this
    -- Now compute both sides via the join characterization.
    rw [hechar n hn.isPrime]
    -- `(∀ m ∈ S, π (G m) ∈ n) ↔ ex ∈ n`
    constructor
    · intro hforall
      -- Suppose `ex ∉ n`. Then `⟨n, hn⟩ ∈ S`, so `π (G ⟨n,hn⟩) ∈ n`, but indicator says `n ≠ n`.
      by_contra hexn
      have hmemS : (⟨n, hn⟩ : {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) //
          I.IsMaximal}) ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hexn⟩
      have := hforall ⟨n, hn⟩ hmemS
      exact ((hindicator ⟨n, hn⟩).mp this) rfl
    · intro hexn m hmS
      -- `ex ∈ n`. For `m ∈ S` we have `ex ∉ m.val`, so `m.val ≠ n`, hence `n ≠ m.val`, and the
      -- indicator gives membership.
      rw [hS, Finset.mem_filter] at hmS
      exact (hindicator m).mpr fun h => hmS.right (h ▸ hexn)
  -- From agreement at all maximals: `π e - ex` lies in every maximal ideal = Jacobson(⊥),
  -- nilpotent.
  have hsub_all_max : ∀ (p : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))),
      p.IsMaximal → (π e - ex) ∈ p := by
    intro p hpmax
    have : p.IsPrime := hpmax.isPrime
    -- both `π e, ex` are `0` or `1` in `Ā/p`; agreement ⇒ difference ∈ p.
    have hpe := hidem01 (π e) (by rw [← map_mul]; exact congrArg π heidem) p hpmax.isPrime
    have hpex := hidem01 ex hexidem p hpmax.isPrime
    have hiff := hagree p hpmax
    have hfalse : ∀ x, x ∈ p → 1 - x ∈ p → False := fun x hx h1x => hpmax.ne_top
      (Ideal.eq_top_of_isUnit_mem p (by simpa using Ideal.add_mem p hx h1x) isUnit_one)
    rcases hpe with h1 | h1 <;> rcases hpex with h2 | h2
    · exact Ideal.sub_mem _ h1 h2
    · exact (hfalse ex (hiff.mp h1) h2).elim
    · exact (hfalse (π e) (hiff.mpr h2) h1).elim
    · -- both `1 - π e, 1 - ex ∈ p` ⇒ their difference `ex - π e ∈ p` ⇒ `π e - ex ∈ p`.
      have hd : (1 - π e) - (1 - ex) ∈ p := Ideal.sub_mem _ h1 h2
      have heq : (1 - π e) - (1 - ex) = -(π e - ex) := by ring
      rw [heq] at hd
      simpa using (Ideal.neg_mem_iff p).mp hd
  have hsub_mem_jac : (π e - ex) ∈
      (⊥ : Ideal (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))).jacobson := by
    exact mem_jacobson_bot_of_forall_isMaximal hsub_all_max
  have hnil : IsNilpotent (π e - ex) := by
    obtain ⟨k, hk⟩ := (IsArtinianRing.isNilpotent_jacobson_bot
      (R := A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)))
    exact ⟨k, by
      have hmem := Ideal.pow_mem_pow hsub_mem_jac k
      rw [hk] at hmem
      simpa using hmem⟩
  have hfinal : π e = ex :=
    eq_of_isNilpotent_sub_of_isIdempotentElem (heidem.map π) hex hnil
  exact hfinal

/-- Lifting a single idempotent over a henselian local ring. For `A` module-finite over the
henselian local ring `R`, every idempotent `ex` of the closed fibre `A/𝔪A` lifts to an idempotent
`e ∈ A` with `mk e = ex`.

The lift goes by étale descent rather than by polynomial Hensel lifting: single-variable Newton
iteration does not produce the factorization form of Hensel's lemma from the bare monic root form
over a non-complete henselian local ring. Instead:
* `reduction_of_isolating_idem` combines Stacks 00UJ
  (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`) with
  `henselian_etale_residue_point_section` to produce, for each prime `q` of `A` over `𝔪`, a lifted
  primitive idempotent `g_q ∈ A` supported at `q`, i.e. `g_q ∉ q` and `g_q ∈ q'` for `q' ≠ q`.
* `fibre_idempotent_lift_of_primitive` then uses that the closed fibre is Artinian: `ex` is the
  join of the indicators at the finite set of primes it avoids, and those lift and join to `e`. -/
lemma henselian_lift_single_idem
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (ex : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (hex : IsIdempotentElem ex) :
    ∃ e : A, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) e = ex := by
  -- The per-prime primitive lift `reduction_of_isolating_idem` feeds the Artinian indicator-join
  -- assembly `fibre_idempotent_lift_of_primitive`.
  refine fibre_idempotent_lift_of_primitive R A (fun q hq hlo => ?_) ex hex
  have : q.IsPrime := hq
  have : q.LiesOver (IsLocalRing.maximalIdeal R) := hlo
  exact reduction_of_isolating_idem R A q

/-- A complete orthogonal idempotent family lifts as soon as single idempotents do. Given that
every idempotent of the closed fibre `A/𝔪A` lifts to an idempotent of `A` — the per-element
conclusion of `henselian_lift_single_idem`, taken here as the hypothesis `hsingle` — a whole
complete orthogonal idempotent family `ē : Fin n → A/𝔪A` lifts to a complete orthogonal family
`e : Fin n → A` reducing to `ē`.

This is the orthogonalization step, mirroring the structure of
`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` with `hsingle` in place of the
nilpotent-kernel input. Induct on `n`: lift the first idempotent `e₀` via `hsingle`, lift the
remaining family by induction inside the complement corner `(1-e₀)·A`, and orthogonalize the
lifts by the corner adjustment `e' := (1 - e₂) * b`. Completeness `∑ eᵢ = 1` and orthogonality
`eᵢeⱼ = 0` transfer from `ē` through the surjection, since `mk` is a ring hom with
`mk eᵢ = ēᵢ`. -/
lemma henselian_lift_coi_of_single
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (hsingle : ∀ ex : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A),
      IsIdempotentElem ex → ∃ e : A, IsIdempotentElem e ∧
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) e = ex)
    {n : ℕ} (ē : Fin n → A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (hē : CompleteOrthogonalIdempotents ē) :
    ∃ e : Fin n → A, CompleteOrthogonalIdempotents e ∧
      ∀ i, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) (e i) = ē i := by
  -- Orthogonalization assembly: induct on n, lift first idempotent via `hsingle`, recurse in the
  -- complement corner, orthogonalize. Mirrors
  -- `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`.
  set I := (IsLocalRing.maximalIdeal R).map (algebraMap R A) with hI
  set f := Ideal.Quotient.mk I with hf
  -- orthogonalizing single lift building block (the analogue of
  -- `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`, but using `hsingle` for the lift and
  -- the explicit corner adjustment `e' := (1 - e₂) * b` for orthogonality — no nilpotency needed).
  have key : ∀ (c₁ : A ⧸ I), IsIdempotentElem c₁ → ∀ (e₂ : A), IsIdempotentElem e₂ →
      c₁ * f e₂ = 0 →
      ∃ e' : A, IsIdempotentElem e' ∧ f e' = c₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
    intro c₁ hc₁ e₂ he₂ h0
    obtain ⟨b, hb, hfb⟩ := hsingle c₁ hc₁
    have he2 : (1 - e₂) * e₂ = 0 := by
      have := he₂.eq; rw [sub_mul, one_mul, this, sub_self]
    refine ⟨(1 - e₂) * b, ?_, ?_, ?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (1 - e₂) * b * ((1 - e₂) * b)
          = ((1 - e₂) * (1 - e₂)) * (b * b) := by ring
        _ = (1 - e₂) * b := by rw [he₂.one_sub.eq, hb.eq]
    · rw [map_mul, map_sub, map_one, hfb, sub_mul, one_mul]
      have : f e₂ * c₁ = 0 := by rw [mul_comm]; exact h0
      rw [this, sub_zero]
    · calc (1 - e₂) * b * e₂ = b * ((1 - e₂) * e₂) := by ring
        _ = 0 := by rw [he2, mul_zero]
    · calc e₂ * ((1 - e₂) * b) = b * ((1 - e₂) * e₂) := by ring
        _ = 0 := by rw [he2, mul_zero]
  -- orthogonal idempotents lift (mirror `OrthogonalIdempotents.lift_of_isNilpotent_ker_aux`)
  have orthoAux : ∀ {m : ℕ} {e : Fin m → A ⧸ I}, OrthogonalIdempotents e →
      ∃ e' : Fin m → A, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
    intro m
    induction m with
    | zero => intro e he; exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
    | succ m IH =>
      intro e he
      obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb m))
      have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
      obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
        key _ (he.idem 0) _ h₁.isIdempotentElem_sum
          (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv m).toEmbedding, funext fun i ↦ ?_⟩
      obtain ⟨_ | i, rfl⟩ := (finSuccEquiv m).symm.surjective i
      · simpa [hf] using h₄
      · simpa [hf] using h₂' i
  -- Subsingleton transfer (Nakayama): if `A/I` is subsingleton then `A` is subsingleton.
  -- (`I = 𝔪A = ⊤`, `A` finite over local `R`, `𝔪 ≤ jacobson R`, so `A = 0` by Nakayama.)
  have hsub : Subsingleton (A ⧸ I) → Subsingleton A := by
    intro hquot
    have htop : I = ⊤ := by rw [← Ideal.Quotient.subsingleton_iff]; exact hquot
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Module.subsingleton R A
    · have hsmul : (⊤ : Submodule R A) ≤ (IsLocalRing.maximalIdeal R) • ⊤ := by
        rw [Ideal.smul_top_eq_map, ← hI, htop]; intro x _; trivial
      have hfg : (⊤ : Submodule R A).FG := Module.Finite.fg_top
      have hjac : (IsLocalRing.maximalIdeal R) ≤ (⊥ : Ideal R).jacobson := by
        rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have hbot : (⊤ : Submodule R A) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hsmul hjac
      exact (Submodule.subsingleton_iff R).mp (subsingleton_iff_bot_eq_top.mp hbot.symm)
  -- complete orthogonal lift (mirror `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux`)
  have coiLift : ∀ {m : ℕ} {e : Fin m → A ⧸ I}, CompleteOrthogonalIdempotents e →
      ∃ e' : Fin m → A, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
    intro m e hcoi
    rcases subsingleton_or_nontrivial A with hA | hA
    · refine ⟨fun i ↦ Classical.choose (Ideal.Quotient.mk_surjective (e i)), .of_subsingleton, ?_⟩
      exact funext fun i ↦ Subsingleton.elim _ _
    · obtain _ | m := m
      · exfalso
        have hss : Subsingleton (A ⧸ I) := by
          have h1 : (0 : A ⧸ I) = 1 := by simpa using hcoi.complete
          exact subsingleton_of_zero_eq_one h1
        exact (not_subsingleton A) (hsub hss)
      · obtain ⟨e', h₁, h₂⟩ := orthoAux hcoi.toOrthogonalIdempotents
        have heq (i : _) : f (e' i) = e i := congr_fun h₂ i
        set g : Option (Fin m) → A :=
          (fun o => Option.elim o (1 - ∑ i, (e' ∘ (Fin.succEmb m)) i) (e' ∘ (Fin.succEmb
              m))) with hg
        refine ⟨g ∘ (finSuccEquiv m),
          (CompleteOrthogonalIdempotents.equiv (finSuccEquiv m)).mpr
            (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i ↦
                ?_⟩
        cases i using Fin.cases with
        | zero => simp [Function.comp, hg, heq, Fin.sum_univ_succ, ← hcoi.complete]
        | succ i => simp [Function.comp, hg, heq]
  obtain ⟨e, he, heq⟩ := coiLift hē
  exact ⟨e, he, fun i ↦ congr_fun heq i⟩

/-- Lifting a complete orthogonal idempotent family. For `A` module-finite over the henselian
local ring `R`, any complete orthogonal idempotent family `ē : Fin n → A/𝔪A` of the closed fibre
lifts to a complete orthogonal idempotent family `e : Fin n → A` reducing to `ē` mod `𝔪A`.

This is the only place where henselianness of `R` is used. The kernel `𝔪A` of `A ↠ A/𝔪A` is not
nilpotent in general, so the nilpotent-kernel lift
`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` does not apply.

It suffices to lift a single idempotent of `A/𝔪A`, which is `henselian_lift_single_idem`; the
family is then assembled by the orthogonalization of `henselian_lift_coi_of_single`. -/
@[sga "1 I 6.2" "partial"]
lemma henselian_lift_coi
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    {n : ℕ} (ē : Fin n → A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (hē : CompleteOrthogonalIdempotents ē) :
    ∃ e : Fin n → A, CompleteOrthogonalIdempotents e ∧
      ∀ i, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) (e i) = ē i := by
  -- The single-idempotent lift `henselian_lift_single_idem` feeds the orthogonalization assembly
  -- `henselian_lift_coi_of_single`.
  exact henselian_lift_coi_of_single R A
    (fun ex hex => henselian_lift_single_idem R A ex hex) ē hē

-- needed: `lifted_factor_isLocalRing`'s `simpa using ht` for surjectivity of `g` needs defeq
-- to unfold the composed `Ideal.Quotient.mk` maps behind `mkS`.
set_option backward.isDefEq.respectTransparency false in
/-- A lifted factor is local. If `e ∈ A` lifts an idempotent `ē` of the closed fibre `A/𝔪A`, so
`mk e = ē`, and the fibre's corner `(A/𝔪A) ⧸ span{1 - ē}` is local, then the corner
`A ⧸ span{1 - e}` of `A` is local. Here `A` is module-finite over the local ring `R`.

Write `A₁ := A ⧸ span{1 - e}`. Its closed fibre is `A₁ ⧸ 𝔪A₁ ≅ (A/𝔪A) ⧸ span{1 - ē}`, since
reduction commutes with passing to the idempotent corner and `ē = mk e`, and this is local by
hypothesis. Being a quotient of `A`, the ring `A₁` is module-finite and hence integral over the
local `R` (`Algebra.IsIntegral.of_finite`), so by lying over every maximal ideal of `A₁` contracts
to `𝔪` and therefore contains `𝔪A₁`. Maximal ideals of `A₁` thus correspond to those of the local
closed fibre, of which there is exactly one. -/
@[sga "3 V 4.1.2" "(F), special case", sga "3 XXIV 8.1.2" "partial"]
lemma lifted_factor_isLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (e : A) (ē : A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (hmk : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) e = ē)
    (hloc : IsLocalRing ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸ Ideal.span {1 -
        ē})) :
    IsLocalRing (A ⧸ Ideal.span {1 - e}) := by
  classical
  have : IsLocalRing ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸ Ideal.span {1 -
      ē}) := hloc
  set I1 : Ideal A := Ideal.span {(1:A) - e} with hI1
  set mkS : A →+* (A ⧸ I1) := Ideal.Quotient.mk I1 with hmkS
  set mkM : A →+* (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) with hmkM
  set qK : (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) →+*
      ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸ Ideal.span {(1 : _) - ē}) :=
    Ideal.Quotient.mk (Ideal.span {(1 : _) - ē}) with hqK
  set g0 : A →+* _ := qK.comp mkM with hg0
  have hsub : I1 ≤ RingHom.ker g0 := by
    rw [hI1, Ideal.span_le]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, RingHom.mem_ker, hg0, RingHom.comp_apply]
    have h1 : mkM (1 - e) = 1 - ē := by rw [map_sub, map_one, hmk]
    rw [h1, hqK, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  set g : (A ⧸ I1) →+* _ := Ideal.Quotient.lift _ g0 hsub with hg
  have hg0surj : Function.Surjective g0 := by
    rw [hg0]; exact Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hgsurj : Function.Surjective g := by
    rw [hg]; intro z; obtain ⟨t, ht⟩ := hg0surj z
    exact ⟨mkS t, by rw [hmkS] at *; simpa using ht⟩
  -- integrality + lying over: every maximal of A⧸I1 contains 𝔪·(A⧸I1)
  have : Module.Finite R (A ⧸ I1) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom R A (A ⧸ I1)).toLinearMap
      (Ideal.Quotient.mk_surjective)
  have : Algebra.IsIntegral R (A ⧸ I1) := Algebra.IsIntegral.of_finite R (A ⧸ I1)
  have hmax : ∀ (M : Ideal (A ⧸ I1)), M.IsMaximal →
      (IsLocalRing.maximalIdeal R).map (algebraMap R (A ⧸ I1)) ≤ M := by
    intro M hM
    have hcomap : Ideal.comap (algebraMap R (A ⧸ I1)) M = IsLocalRing.maximalIdeal R := by
      have := hM
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) M)
    rw [Ideal.map_le_iff_le_comap, hcomap]
  -- mkS of an element of 𝔪A lands in jacobson ⊥
  have hmkSjac : ∀ m ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A),
      mkS m ∈ (⊥ : Ideal (A ⧸ I1)).jacobson := by
    intro m hm
    have hmem : mkS m ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (A ⧸ I1)) := by
      have hmapmap : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).map mkS
          = (IsLocalRing.maximalIdeal R).map (algebraMap R (A ⧸ I1)) := by
        rw [Ideal.map_map, hmkS]; rfl
      rw [← hmapmap]; exact Ideal.mem_map_of_mem mkS hm
    exact mem_jacobson_bot_of_forall_isMaximal fun M hM => hmax M hM hmem
  -- kernel of g sits in jacobson ⊥
  have hkerjac : ∀ x ∈ RingHom.ker g, x ∈ (⊥ : Ideal (A ⧸ I1)).jacobson := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨t, rfl⟩ : ∃ t, mkS t = x := by rw [hmkS]; exact Ideal.Quotient.mk_surjective x
    have hgt : g0 t = 0 := by
      have heq : g (mkS t) = g0 t := by rw [hg, hmkS]; rfl
      rw [heq] at hx; exact hx
    have hmkMt : mkM t ∈ Ideal.span {(1 : _) - ē} := by
      rw [hg0, RingHom.comp_apply] at hgt
      rwa [hqK, Ideal.Quotient.eq_zero_iff_mem] at hgt
    rw [Ideal.mem_span_singleton] at hmkMt
    obtain ⟨c, hc⟩ := hmkMt
    obtain ⟨c', rfl⟩ : ∃ c', mkM c' = c := by rw [hmkM]; exact Ideal.Quotient.mk_surjective c
    have hmem𝔪 : t - c' * (1 - e) ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
      have : mkM (t - c' * (1 - e)) = 0 := by
        rw [map_sub, hc, map_mul, map_sub, map_one, hmk]; ring
      rwa [hmkM, Ideal.Quotient.eq_zero_iff_mem] at this
    have hmkScancel : mkS (c' * (1 - e)) = 0 := by
      rw [map_mul]
      have : mkS (1 - e) = 0 := by
        rw [hmkS, Ideal.Quotient.eq_zero_iff_mem, hI1]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [this, mul_zero]
    have hmkSeq : mkS t = mkS (t - c' * (1 - e)) := by rw [map_sub, hmkScancel, sub_zero]
    rw [hmkSeq]
    exact hmkSjac _ hmem𝔪
  -- A⧸I1 is local: g surjects onto local K with kernel in the Jacobson radical
  have : Nontrivial (A ⧸ I1) := hgsurj.nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have reflect : ∀ (a : A ⧸ I1), IsUnit (g a) → IsUnit a := by
    intro a h
    obtain ⟨b, hb⟩ := hgsurj (↑h.unit⁻¹)
    have hab : g (a * b) = 1 := by
      rw [map_mul, hb]
      exact h.mul_val_inv
    have hker : (a * b - 1) ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, map_sub, hab, map_one, sub_self]
    have hunit : IsUnit (a * b) := by
      have hj := hkerjac _ hker
      have := (Ideal.mem_jacobson_bot.mp hj) 1
      simpa using this
    exact isUnit_of_mul_isUnit_left hunit
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (g a) with h | h
  · exact Or.inl (reflect a h)
  · exact Or.inr (reflect (1 - a) (by simpa using h))

/-- A complete orthogonal idempotent family of `A` with local corners: for `A` module-finite over
the henselian local ring `R`, there is a complete orthogonal idempotent family `e : Fin n → A`
such that each corner `A ⧸ span{1 - eᵢ}` is local.

This combines `closedFibre_isArtinian'`, `artinian_coi_local`, `henselian_lift_coi` and
`lifted_factor_isLocalRing`; `exists_algEquiv_pi_isLocalRing` then reads the product decomposition
off it via `CompleteOrthogonalIdempotents.bijective_pi`. -/
@[ega "IV 18.5.11" "(F), partial",
  ega "IV 18.5.9" "(ii), necessity",
  sga "3 VIIB 2.9" "Finite-dimensional case",
  sga "3 XV 3.9" "partial",
  sga "4 VIII 4.1" "(i)"]
lemma exists_completeOrthogonalIdempotents_lift
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (n : ℕ) (e : Fin n → A), CompleteOrthogonalIdempotents e ∧
      ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i}) := by
  have hart : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    closedFibre_isArtinian' R A
  obtain ⟨n, ē, hē, hēloc⟩ :=
    artinian_coi_local (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
  obtain ⟨e, he, hmk⟩ := henselian_lift_coi R A ē hē
  exact ⟨n, e, he, fun i => lifted_factor_isLocalRing R A (e i) (ē i) (hmk i) (hēloc i)⟩

/-- Part (10) of Stacks 04GG: a module-finite algebra `A` over a henselian local ring `R`
decomposes as a finite product `∏ i : Fin n, Af i` of `R`-algebras, each local and module-finite
over `R`. -/
@[ega "IV 18.5.9" "(ii), necessity", sga "4 VIII 4.1" "(i), forward direction"]
theorem exists_algEquiv_pi_isLocalRing (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (n : ℕ) (Af : Fin n → Type (max u v)) (_ : ∀ i, CommRing (Af i))
      (_ : ∀ i, Algebra R (Af i)),
      (∀ i, IsLocalRing (Af i)) ∧ (∀ i, Module.Finite R (Af i)) ∧
      Nonempty (A ≃ₐ[R] (∀ i, Af i)) := by
  -- The decomposition comes from `exists_completeOrthogonalIdempotents_lift`, which chains:
  --  * `closedFibre_isArtinian'` — the closed fibre `A/𝔪A` is Artinian.
  --  * `artinian_coi_local` — an Artinian ring has complete orthogonal idempotents with local
  --    corners.
  --  * `henselian_lift_coi` — the henselian lift of that idempotent family to `A`.
  --  * `lifted_factor_isLocalRing` — each lifted corner of `A` is local.
  -- The product iso is then read off from `CompleteOrthogonalIdempotents.bijective_pi`.
  obtain ⟨n, e, hco, hloc⟩ := exists_completeOrthogonalIdempotents_lift R A
  refine ⟨n, fun i => A ⧸ Ideal.span {1 - e i}, inferInstance, inferInstance, hloc, ?_, ?_⟩
  · -- each factor is module-finite over R (quotient of the module-finite A)
    intro i
    exact Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})).toLinearMap
      Ideal.Quotient.mk_surjective
  · -- assemble the product iso from the complete orthogonal idempotents
    let φ : A →ₐ[R] (∀ i, A ⧸ Ideal.span {1 - e i}) :=
      AlgHom.pi (fun i => Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))
    have hbij : Function.Bijective φ := by
      have hbij := hco.bijective_pi
      convert hbij using 1
      rfl
    exact ⟨AlgEquiv.ofBijective φ hbij⟩

/-- Stacks Tag 04GJ (Lemma 10.153.5). A finite type algebra over a henselian local ring
decomposes, up to `R`-algebra isomorphism, as a finite product of local algebras finite
over `R`, times an algebra `B` that is not quasi-finite at any prime lying over the
maximal ideal of `R`. -/
@[stacks 04GJ, ega "IV 18.5.9" "more general", sga "4 VIII 4.1" "(ii)"]
theorem exists_algEquiv_prod_of_henselianLocalRing (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (A : Fin n → Type (max u v)) (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra R (A i)),
      (∀ i, IsLocalRing (A i)) ∧ (∀ i, Module.Finite R (A i)) ∧
      ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
        (∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮.LiesOver (IsLocalRing.maximalIdeal R) →
          ¬ Algebra.QuasiFiniteAt R 𝔮) ∧
        Nonempty (S ≃ₐ[R] (∀ i, A i) × B) := by
  -- 1. Apply part (11): obtain `A`, `B` with `Module.Finite R A`, the not-quasi-finite
  --    condition on `B`, and `eAB : S ≃ₐ[R] A × B`.
  obtain ⟨A, _, _, B, _, _, hAfin, hBnqf, ⟨eAB⟩⟩ := exists_prod_finite_not_quasiFiniteAt R S
  -- 2. Apply part (10) to the module-finite `A`: obtain `n`, `Af : Fin n → _` local and
  --    module-finite, and `eA : A ≃ₐ[R] ∀ i, Af i`.
  obtain ⟨n, Af, _, _, hloc, hAffin, ⟨eA⟩⟩ := exists_algEquiv_pi_isLocalRing R A
  -- 3. Assemble: `S ≃ₐ[R] A × B ≃ₐ[R] (∀ i, Af i) × B`.
  refine ⟨n, Af, inferInstance, inferInstance, hloc, hAffin, B, inferInstance,
    inferInstance, hBnqf, ⟨eAB.trans (eA.prodCongr (AlgEquiv.refl))⟩⟩

end
