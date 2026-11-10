module

import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.EtaleSectionIdempotent

/-!
# The finite part of a finite type algebra over a henselian local ring

Combining corner idempotents into one idempotent whose component is finite over `R` and whose
complement is not quasi-finite at any prime over `m`; complete orthogonal idempotents of the
closed fibre of a module-finite algebra; Hensel factorization over `R` and the lift of
idempotents along `m·B` for `B` module-finite over `R`.
-/

section

universe u

@[expose] public section

open IsLocalRing

/-- A quotient of `S ⧸ I` by an ideal containing the image of `B` is module-finite over `R`
whenever `S ⧸ span {B}` is. -/
private theorem finite_quotient_quotient_of_mem {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal S) (B : S) (J : Ideal (S ⧸ I)) (hB : Ideal.Quotient.mk I B ∈ J)
    [Module.Finite R (S ⧸ Ideal.span {B})] : Module.Finite R ((S ⧸ I) ⧸ J) := by
  let π : S →ₐ[R] ((S ⧸ I) ⧸ J) := (Ideal.Quotient.mkₐ R J).comp (Ideal.Quotient.mkₐ R I)
  have hkill : ∀ a ∈ Ideal.span ({B} : Set S), π a = 0 := by
    intro a ha
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have hπB : π B = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hB
    rw [map_mul, hπB, zero_mul]
  let φ := Ideal.Quotient.liftₐ (Ideal.span {B}) π hkill
  have hsurj : Function.Surjective φ := fun y =>
    let ⟨x, hx⟩ := (Ideal.Quotient.mk_surjective (I := J)).comp
      (Ideal.Quotient.mk_surjective (I := I)) y
    ⟨Ideal.Quotient.mk _ x, hx⟩
  exact Module.Finite.of_surjective φ.toLinearMap hsurj

-- needed: `exists_isIdempotentElem_finite_notMem_of_finite` cannot synthesize
-- `Module.Finite R (S ⧸ Ideal.span {1})` unless the span unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Combining a finite family of corner idempotents.** Given a finite set `T` of primes
of `S` and, for each `q ∈ T`, an idempotent `cf q ∉ q` whose corner `S ⧸ span {1 - cf q}` is
module-finite over `R`, the "join" idempotent `c = ⋁_{q∈T} cf q` (so that
`1 - c = ∏ (1 - cf q)`) is idempotent, has corner `S ⧸ span {1 - c}` module-finite over `R`
(a finite product of the corners), and satisfies `c ∉ q` for every `q ∈ T`: in the residue
field `κ(q)`, the boolean join of idempotents one of which (`cf q`) is `1` equals `1`.

The proof inducts over the finite set using `e ⋁ f = e + f - e*f` and
`1 - (e ⋁ f) = (1-e)(1-f)` (`IsIdempotentElem.one_sub`); the corner of the join is
isomorphic to the product of the corners via the orthogonalization
`d_i = c_i ∏_{k<i}(1-c_k)` (`Module.Finite.pi`, `Module.Finite.of_surjective`), and the
`c ∉ q` claim is the boolean identity `x ⋁ 1 = 1` in the field `κ(q)`. -/
theorem exists_isIdempotentElem_finite_notMem_of_finite (R : Type) [CommRing R] (S : Type)
    [CommRing S] [Algebra R S]
    (T : Set (Ideal S)) (hT : T.Finite) (cf : ∀ q ∈ T, S)
    (hidem : ∀ q (hq : q ∈ T), IsIdempotentElem (cf q hq)) (hout : ∀ q (hq : q ∈ T), cf q hq ∉ q)
    (hfin : ∀ q (hq : q ∈ T), Module.Finite R (S ⧸ Ideal.span {1 - cf q hq})) :
    ∃ (c : S),
      IsIdempotentElem c ∧ Module.Finite R (S ⧸ Ideal.span {1 - c}) ∧ (∀ q ∈ T, c ∉ q) := by
  classical
  have hfin' : Fintype T := hT.fintype
  set g : T → S := fun q => 1 - cf q.val q.property
  have hgidem : ∀ q : T, IsIdempotentElem (g q) := fun q => (hidem q.val q.property).one_sub
  have hgfin : ∀ q : T, Module.Finite R (S ⧸ Ideal.span {g q}) := fun q => hfin q.val q.property
  -- two-idempotent finiteness step
  have hstep :
    ∀ A B : S,
      IsIdempotentElem A →
        IsIdempotentElem B →
        Module.Finite R (S ⧸ Ideal.span {A}) →
        Module.Finite R (S ⧸ Ideal.span {B}) → Module.Finite R (S ⧸ Ideal.span {A * B}) := by
    intro A B hA hB hfA hfB
    let I : Ideal S := Ideal.span {A * B}
    let mkI : S →ₐ[R] (S ⧸ I) := Ideal.Quotient.mkₐ R I
    have heA : IsIdempotentElem (mkI A) := by
      change mkI A * mkI A = mkI A
      rw [← map_mul, hA.eq]
    have heA' : IsIdempotentElem (1 - mkI A) := heA.one_sub
    have hsum : mkI A + (1 - mkI A) = 1 := by ring
    have hprod : mkI A * (1 - mkI A) = 0 := by rw [mul_sub, mul_one, heA.eq, sub_self]
    let E := AlgEquiv.prodQuotientOfIsIdempotentElem R heA heA' hsum hprod
    have hABzero : mkI (A * B) = 0 := by
      change Ideal.Quotient.mk I (A * B) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hfac1 : Module.Finite R ((S ⧸ I) ⧸ Ideal.span ({mkI A} : Set (S ⧸ I))) :=
      finite_quotient_quotient_of_mem I A _ (Ideal.subset_span rfl)
    have hfac2 : Module.Finite R ((S ⧸ I) ⧸ Ideal.span ({1 - mkI A} : Set (S ⧸ I))) := by
      refine finite_quotient_quotient_of_mem I B _ ?_
      have h : mkI B = (1 - mkI A) * mkI B + mkI (A * B) := by rw [map_mul]; ring
      rw [show Ideal.Quotient.mk I B = mkI B from rfl, h, hABzero, add_zero]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hprodfin :
      Module.Finite R
        (((S ⧸ I) ⧸ Ideal.span ({mkI A} : Set (S ⧸ I))) ×
          ((S ⧸ I) ⧸ Ideal.span ({1 - mkI A} : Set (S ⧸ I)))) :=
      Module.Finite.prod
    exact Module.Finite.equiv E.symm.toLinearEquiv
  have hprodidem : ∀ s : Finset T, IsIdempotentElem (∏ q ∈ s, g q) := fun s =>
    Finset.prod_induction g IsIdempotentElem (fun a b ha hb => ha.mul hb) IsIdempotentElem.one
      (fun q _ => hgidem q)
  -- induction over Finsets of T
  have hind : ∀ s : Finset T, Module.Finite R (S ⧸ Ideal.span {∏ q ∈ s, g q}) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      have hsub : Subsingleton (S ⧸ Ideal.span ({(1 : S)} : Set S)) := by
        rw [Ideal.span_singleton_one]
        infer_instance
      infer_instance
    | insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      exact hstep (g j) (∏ q ∈ s, g q) (hgidem j) (hprodidem s) (hgfin j) ih
  -- assemble
  set P : S := ∏ q : T, g q with hP
  have hPidem : IsIdempotentElem P := hprodidem Finset.univ
  refine ⟨1 - P, hPidem.one_sub, ?_, ?_⟩
  · have : (1 : S) - (1 - P) = P := by ring
    rw [this]
    have := hind Finset.univ
    rwa [show (∏ q ∈ (Finset.univ : Finset T), g q) = P from rfl] at this
  · intro q hq hmem
    have hPcf : P * cf q hq = 0 := by
      rw [hP]
      have hmemu : (⟨q, hq⟩ : T) ∈ (Finset.univ : Finset T) := Finset.mem_univ _
      rw [← Finset.prod_erase_mul (Finset.univ : Finset T) g hmemu]
      have hz : g ⟨q, hq⟩ * cf q hq = 0 := by
        change (1 - cf q hq) * cf q hq = 0
        rw [sub_mul, one_mul, (hidem q hq).eq, sub_self]
      rw [mul_assoc, hz, mul_zero]
    have hcfeq : cf q hq = (1 - P) * cf q hq := by rw [sub_mul, one_mul, hPcf, sub_zero]
    have : cf q hq ∈ q := by
      rw [hcfeq]
      exact Ideal.mul_mem_right _ _ hmem
    exact hout q hq this

/-- **The complement carries no quasi-finite prime.** If `c : S` is an idempotent lying
OUTSIDE every quasi-finite prime of `S` over `m`, then the complement
`B = S ⧸ span {1 - (1 - c)} = S ⧸ span {c}` has NO quasi-finite prime over `m`.

A prime `q` of `B = S/cS` over `m` corresponds, by the quotient prime correspondence on
`V(cS)`, to a prime `q'` of `S` with `c ∈ q'`, still lying over `m`. The localizations
agree: `B_q ≅ S_{q'}/(c)`, but in the LOCAL ring `S_{q'}` the idempotent `c` lies in the
maximal ideal `q' S_{q'}` and hence must be `0`, since the Jacobson radical contains no
nonzero idempotent. So `B_q ≅ S_{q'}`, and quasi-finiteness at `q` over `R` gives
quasi-finiteness at `q'` over `R`. Then `q'` is a quasi-finite prime over `m`, so by
hypothesis `c ∉ q'`, contradicting `c ∈ q'`. -/
theorem not_quasiFiniteAt_quotient_of_idempotent_notMem (R : Type) [CommRing R] [IsLocalRing R] (S :
  Type)
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (c : S) (hc : IsIdempotentElem c)
    (hcout :
      ∀ (q : Ideal S) (hq : q.IsPrime),
        q.LiesOver (maximalIdeal R) → (@Algebra.QuasiFiniteAt R S _ _ _ q hq) → c ∉ q) :
    ∀ (q : Ideal (S ⧸ Ideal.span {1 - (1 - c)})) (hq : q.IsPrime),
      q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R _ _ _ _ q hq := by
  -- The argument runs through the localization: an idempotent in the maximal ideal of the
  -- local ring `S_{q'}` is `0`. (For `c = 1` the complement `B` is the zero ring.)
  intro q hq hlo hqf
  set B' := S ⧸ Ideal.span {1 - (1 - c)} with hB'
  have hone : IsIdempotentElem (1 - c) := hc.one_sub
  have hloc : IsLocalization.Away (1 - c) B' :=
    IsLocalization.Away.quotient_of_isIdempotentElem hone
  set q' := q.comap (algebraMap S B') with hq'def
  have hq'p : q'.IsPrime := Ideal.comap_isPrime _ _
  have hM : IsLocalization.AtPrime (Localization.AtPrime q) q' :=
    @IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S _
      (Submonoid.powers (1 - c)) B' _ _ (Localization.AtPrime q) _ _ _ _ hloc q hq _
  have eS : Localization.AtPrime q' ≃ₐ[S] Localization.AtPrime q :=
    IsLocalization.algEquiv q'.primeCompl (Localization.AtPrime q') (Localization.AtPrime q)
  have eR : Localization.AtPrime q' ≃ₐ[R] Localization.AtPrime q := AlgEquiv.restrictScalars R eS
  have hqf' : Algebra.QuasiFinite R (Localization.AtPrime q') :=
    (Algebra.QuasiFinite.iff_of_algEquiv eR).mpr hqf
  have hQFq' : @Algebra.QuasiFiniteAt R S _ _ _ q' hq'p := hqf'
  have hlo' : q'.LiesOver (maximalIdeal R) := by
    refine ⟨?_⟩
    have htower : (algebraMap R B') = (algebraMap S B').comp (algebraMap R S) :=
      IsScalarTower.algebraMap_eq R S B'
    have hunder : Ideal.under R q' = Ideal.under R q := by
      change (q.comap (algebraMap S B')).comap (algebraMap R S) = q.comap (algebraMap R B')
      rw [Ideal.comap_comap, ← htower]
    rw [hunder]
    exact hlo.over
  have hcin : c ∈ q' := by
    rw [hq'def, Ideal.mem_comap]
    have hmem : c ∈ Ideal.span {1 - (1 - c)} := by
      have : (1 : S) - (1 - c) = c := by ring
      rw [this]; exact Ideal.mem_span_singleton_self c
    have : (algebraMap S B') c = 0 := by
      rw [Ideal.Quotient.algebraMap_eq]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [this]
    exact q.zero_mem
  exact hcout q' hq'p hlo' hQFq' hcin

/-- **Assembly of the clopen split from per-point henselian descents** (the topological and
combinatorial half of Stacks 04GE). Given the per-point descent as a hypothesis — every
quasi-finite prime `q` of `S` over `m` admits an idempotent `c ∈ S` with `c ∉ q` and `S·c`
module-finite over `R` — there is a single idempotent `c` whose component `S·c` is finite
over `R` and whose complement `B = S·(1-c) = S ⧸ span {1 - (1 - c)}` has NO quasi-finite
prime over `m`.

The three steps are:
* (finiteness of the locus) The closed fibre `S̄ = S/mS` is of finite type over the field
  `κ`, and its quasi-finite-over-`κ` points are finitely many isolated closed points, i.e.
  clopen singletons (`Algebra.QuasiFiniteAt.isClopen_singleton` over the Artinian base `κ`).
  Pulling back along `S → S̄`, the quasi-finite-over-`m` primes of `S` form a finite set
  `{q₁, …, qᵣ}`.
* (per-point descent and orthogonalization) Apply `descent` at each `qᵢ` to get idempotents
  `cᵢ ∈ S` with `cᵢ ∉ qᵢ` and `S·cᵢ` finite over `R`; orthogonalize and combine them into
  one idempotent `c` with `S·c` finite over `R` (a finite product of `R`-finite factors)
  and `c ∉ qᵢ` for all `i`.
* (complement) The complement `B = S·(1-c)` has closed fibre omitting all the
  quasi-finite-over-`κ` points, and quasi-finiteness is a *fibrewise* condition
  (`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`), so `B` has no quasi-finite prime
  over `m`. -/
theorem exists_isIdempotentElem_finite_complement_not_quasiFiniteAt (R : Type) [CommRing R]
  [HenselianLocalRing R] (S : Type)
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (descent :
      ∀ (q : Ideal S) (hq : q.IsPrime),
        q.LiesOver (maximalIdeal R) →
          @Algebra.QuasiFiniteAt R S _ _ _ q hq →
          ∃ (c : S), IsIdempotentElem c ∧ c ∉ q ∧ Module.Finite R (S ⧸ Ideal.span {1 - c})) :
    ∃ (c : S),
      IsIdempotentElem c ∧
        Module.Finite R (S ⧸ Ideal.span {1 - c}) ∧
        (∀ (q : Ideal (S ⧸ Ideal.span {1 - (1 - c)})) (hq : q.IsPrime),
          q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R _ _ _ _ q hq) := by
  -- The quasi-finite locus over `m` is finite
  -- (`finite_setOf_quasiFiniteAt_liesOver_maximalIdeal`); `descent` gives a corner idempotent
  -- at each of its points; combining them (`exists_isIdempotentElem_finite_notMem_of_finite`)
  -- yields one `c` whose corner is `R`-finite and which avoids every quasi-finite prime, and
  -- its complement then carries no quasi-finite prime
  -- (`not_quasiFiniteAt_quotient_of_idempotent_notMem`).
  classical
  set T : Set (Ideal S) :=
    {q : Ideal S |
      q.IsPrime ∧
        q.LiesOver (maximalIdeal R) ∧ ∀ hq : q.IsPrime, @Algebra.QuasiFiniteAt R S _ _ _ q hq} with
    hTdef
  have hTfin : T.Finite := finite_setOf_quasiFiniteAt_liesOver_maximalIdeal R S
  have hdat :
    ∀ q ∈ T, ∃ (c : S), IsIdempotentElem c ∧ c ∉ q ∧ Module.Finite R (S ⧸ Ideal.span {1 - c}) := by
    intro q hq
    obtain ⟨hqp, hqo, hqf⟩ := hq
    exact descent q hqp hqo (hqf hqp)
  choose cf hcf_idem hcf_out hcf_fin using hdat
  obtain ⟨c, hc_idem, hc_fin, hc_out⟩ :=
    exists_isIdempotentElem_finite_notMem_of_finite R S T hTfin cf hcf_idem hcf_out hcf_fin
  have hcout :
    ∀ (q : Ideal S) (hq : q.IsPrime),
      q.LiesOver (maximalIdeal R) → (@Algebra.QuasiFiniteAt R S _ _ _ q hq) → c ∉ q := by
    intro q hqp hqo hqf
    have hqT : q ∈ T := ⟨hqp, hqo, fun _ => hqf⟩
    exact hc_out q hqT
  exact ⟨c, hc_idem, hc_fin, not_quasiFiniteAt_quotient_of_idempotent_notMem R S c hc_idem hcout⟩

/-- **Henselian split-off of the finite part** (the first half of Stacks 04GE). For
`(R, m, κ)` henselian local and `S` of finite type over `R`, there is an idempotent `c : S`
whose factor `S·c = S ⧸ span {1 - c}` is module-FINITE over `R`, and whose complementary
factor `B = S·(1-c) = S ⧸ span {1 - (1 - c)} = S ⧸ span {c}` has NO quasi-finite prime over
`m`.

The split must be made in the CLOSED FIBRE and then descended; `qfLocus R S` is not itself
clopen in `Spec S` (already for `R = S = ℤ₂`), so no clopen subset of `Spec S` may be
claimed directly.
* (fibre) `S̄ = S/mS = S ⊗_R κ` is of finite type over the FIELD `κ`. Its quasi-finite
  points are finitely many isolated closed points `q̄₁, …, q̄ᵣ`, and `T = {q̄ᵢ}` is CLOPEN
  in `Spec S̄` (over a field, hence Artinian, base: `QuasiFiniteAt.isClopen_singleton`, with
  finiteness from `quasiFiniteAt_iff_isOpen_singleton_fiber`). This produces an idempotent
  `c̄ ∈ S̄` with `basicOpen c̄ = T`
  (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`).
* (descent, where henselianness is used) For each `q̄ᵢ`, that is for
  each quasi-finite prime `q` of `S` over `m`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (Stacks 00UK) gives an étale
  `R'`, a prime `P | m` with `κ ≅ κ(P)` a BIJECTIVE residue map, and an idempotent
  `e ∈ R' ⊗ S` with `Module.Finite R' (Localization.Away e)` cutting out exactly `q`.
  Henselianness (a pointed étale neighborhood has a section `R' → R`) descends `e` to an
  honest idempotent `c ∈ S` with `S·c` FINITE over `R`.
* (assembly) Combine the finitely many descended idempotents — orthogonal, since the
  isolated points are distinct — into one `c`. The complement `B = S·(1-c)` has closed
  fibre `S̄·(1-c̄)`, which contains none of the quasi-finite-over-`κ` points, so, quasi-
  finiteness being a fibrewise condition, `B` has no quasi-finite prime over `m`. -/
theorem exists_isIdempotentElem_finite_and_not_quasiFiniteAt (R : Type) [CommRing R]
  [HenselianLocalRing R] (S : Type) [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (c : S),
      IsIdempotentElem c ∧
        Module.Finite R (S ⧸ Ideal.span {1 - c}) ∧
        (∀ (q : Ideal (S ⧸ Ideal.span {1 - (1 - c)})) (hq : q.IsPrime),
          q.LiesOver (maximalIdeal R) → ¬@Algebra.QuasiFiniteAt R _ _ _ _ q hq) := by
  exact exists_isIdempotentElem_finite_complement_not_quasiFiniteAt R S fun q hq hover hqf =>
    @exists_isIdempotentElem_notMem_finite_of_quasiFiniteAt R _ _ S _ _ _ q hq hover hqf

/-! ## Decomposing a module-finite algebra over a henselian local ring

The results in this section prove that a module-finite algebra over a henselian local ring
is a finite product of local finite factors, and transport that decomposition back below an
idempotent of `S`. The crux is that idempotents lift along the kernel `mA`, which is *not*
nilpotent; that is the henselian-pair property of `(A, mA)` (Stacks 04GG/09XI), and it
rests in turn on the Hensel factorization of monic polynomials over `R`.
-/

/-- **Artinian closed fibre.** The closed fibre
`Ā = A ⧸ mA` of a module-finite `R`-algebra `A` over a local ring `R` is a finite
`κ`-dimensional algebra, hence Artinian; therefore it carries a COMPLETE orthogonal
idempotent system `eb : Fin n → Ā` with each factor `Ā ⧸ span {1 - eb i}` LOCAL
(the local Artinian factors of `Ā ≅ ∏ local Artinian`, Stacks 00JA).

Since `Module.Finite R A`, the fibre `Ā = A ⧸ mA` is a finite-dimensional
`κ = R ⧸ m`-algebra, hence `IsArtinianRing Ā`. Its Jacobson radical is nilpotent
(`IsArtinianRing.isNilpotent_jacobson_bot`) and `Ā ⧸ rad` is a finite product of fields
carrying a complete orthogonal idempotent system, which lifts along the nilpotent radical
via `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`. Each primitive factor is local
Artinian. No henselianness is needed; this is pure Artinian theory. -/
@[sga "3 VIIB 2.9" "Finite-dimensional case"]
theorem closedFibre_completeOrthogonalIdempotents (R : Type) [CommRing R] [IsLocalRing R]
    (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ (n : ℕ) (eb : Fin n → (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))),
      CompleteOrthogonalIdempotents eb ∧
        (∀ i,
          IsLocalRing
            ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ⧸
              Ideal.span {1 - eb i})) := by
  -- The structure theorem (Stacks 00JA): Ā = A/mA is finite-dimensional over κ, hence
  -- Artinian, hence a finite product of local rings, hence carries a complete orthogonal
  -- idempotent system with local factors.
  classical
  -- Step 1: closed fibre is Artinian
  have hArt : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) := by
    set m := IsLocalRing.maximalIdeal R with hm
    set mA := m.map (algebraMap R A) with hmA
    have hle : m ≤ mA.comap (algebraMap R A) := by
      rw [hmA]; exact Ideal.le_comap_map
    let : Algebra (R ⧸ m) (A ⧸ mA) := (Ideal.quotientMap mA (algebraMap R A) hle).toAlgebra
    have : (m).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    have htower : IsScalarTower R (R ⧸ m) (A ⧸ mA) := by
      refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
      change
        (algebraMap R (A ⧸ mA)) x =
          (Ideal.quotientMap mA (algebraMap R A) hle) (Ideal.Quotient.mk m x)
      rw [Ideal.quotientMap_mk]; rfl
    have hfinR : Module.Finite R (A ⧸ mA) := Module.Finite.quotient R mA
    have hfin : Module.Finite (R ⧸ m) (A ⧸ mA) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ m) (A ⧸ mA)
    have : IsArtinianRing (R ⧸ m) := inferInstance
    have : Algebra.FiniteType (R ⧸ m) (A ⧸ mA) := Module.Finite.finiteType _
    exact (Module.finite_iff_isArtinianRing (R ⧸ m) (A ⧸ mA)).mp hfin
  -- The conclusion is exactly `artinian_coi_local` for the closed fibre.
  exact artinian_coi_local _

/-- **The extended maximal ideal lies in the Jacobson radical.** For `A` module-finite,
hence integral, over a local ring `R`, the extended maximal ideal `mA := m·A` is contained
in the Jacobson radical of `A`: every maximal ideal of `A` lies over `m` by lying-over for
integral extensions, and hence contains `mA`. The ingredients are
`Algebra.IsIntegral.of_finite`, the `Ideal.under` lying-over machinery and locality of
`R`. -/
@[ega "0 10.3.1.2" "partial"]
theorem mA_le_jacobson (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ Ideal.jacobson (⊥ : Ideal A) := by
  have hint : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [show (⊥ : Ideal A).jacobson = sInf {J : Ideal A | J.IsMaximal} from by
      rw [Ideal.jacobson]; congr 1; ext J; simp [bot_le]]
  apply le_sInf
  intro Q hQ
  simp only [Set.mem_ofPred_eq] at hQ
  rw [Ideal.map_le_iff_le_comap]
  have hmax : (Q.comap (algebraMap R A)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) Q
  rw [IsLocalRing.eq_maximalIdeal hmax]

/-- **Units lift from the closed fibre.** An element of `A` whose image in the closed fibre
`A ⧸ mA` is a unit is itself a unit in `A`, since a unit modulo an ideal contained in the
Jacobson radical is a unit. The ingredients are `mA_le_jacobson` and
`Ideal.isUnit_of_sub_one_mem_jacobson_bot`. -/
theorem isUnit_of_isUnit_mk (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (b : A)
    (hb : IsUnit ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))) b)) :
    IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨v, hv⟩ :=
    Ideal.Quotient.mk_surjective ((↑u⁻¹ : (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))))
  have hjac : (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ Ideal.jacobson (⊥ : Ideal A) :=
    mA_le_jacobson R A
  have hsub : (1 : A) - b * v ∈ Ideal.jacobson (⊥ : Ideal A) := by
    apply hjac
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, map_one, map_mul, ← hu, hv]
    rw [Units.mul_inv]
    simp
  have hunit : IsUnit (b * v) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot (b * v)
    have heq : (b * v) - 1 = -((1 : A) - b * v) := by ring
    rw [heq]
    exact neg_mem hsub
  exact isUnit_of_mul_isUnit_left hunit

-- needed: `hensel_factorization_over_R`'s `rw` on `Ideal.ResidueField.mapₐ` only matches with
-- its proof argument unfolded at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **Hensel FACTORIZATION form over `R`** (Stacks Tag 04GG). Let `R` be henselian local
with residue field `κ`. If a monic `p ∈ R[X]` reduces mod `m` to a product `p̄ = g₀·h₀` of
two COPRIME monic polynomials over `κ`, then `p` factors as `p = g·h` with `g, h ∈ R[X]`
monic, lifting `g₀` and `h₀`.

This is the factorization characterization of henselian local rings, equivalent to
the single-root form `HenselianLocalRing.is_henselian`.

The proof is by étale descent:
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`
(`Mathlib.RingTheory.Polynomial.UniversalFactorizationRing`) gives a coprime monic
factorization of `p` over a new étale `R`-algebra `R'` carrying a residue-field isomorphism;
`henselian_etale_exists_section` produces a section `R' → R` from henselianness; and the
factorization is pushed back down to `R[X]`, with coprimality giving uniqueness and hence
preservation of degrees. -/
@[ega "IV 18.5.13" "partial", sga "4 VIII 4.1" "(iv)"]
theorem hensel_factorization_over_R (R : Type u) [CommRing R] [HenselianLocalRing R]
    (p : Polynomial R) (hp : p.Monic) (g₀ h₀ : Polynomial (ResidueField R)) (hg₀ : g₀.Monic)
    (hh₀ : h₀.Monic) (hfac : p.map (residue R) = g₀ * h₀) (hcop : IsCoprime g₀ h₀) :
    ∃ g h : Polynomial R,
      g.Monic ∧ h.Monic ∧ p = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ := by
  -- Monicity makes the residue map preserve degrees (`1 ↦ 1 ≠ 0` over the field `κ`), so
  -- `deg g₀ + deg h₀ = deg p`, the lifts are monic of the same degrees, and their
  -- reductions equal `g₀` and `h₀` exactly.
  -- Étale descent: bridge `κ = R/m ≅ (m).ResidueField`, transport the residue factorization,
  -- apply the universal étale-factorization lemma to get an étale `R`-algebra `R'` with a
  -- prime `Q` over `m` and monic coprime `g', h'` lifting `g₀, h₀`; then
  -- `henselian_etale_exists_section` gives an `R`-algebra section `σ₀ : R' → R` with
  -- `ker σ₀ ≤ Q`, and `g', h'` are pushed down along `σ₀`. The residue conditions follow
  -- from the residue field map `τ : Q.ResidueField → κ` induced by `σ₀`.
  obtain ⟨e, he⟩ :
    ∃ e : ResidueField R ≃+* (maximalIdeal R).ResidueField,
      ∀ r : R, e (residue R r) = algebraMap R (maximalIdeal R).ResidueField r :=
    ⟨IsLocalization.AtPrime.equivQuotMaximalIdeal (maximalIdeal R)
        (Localization.AtPrime (maximalIdeal R)) |>.toRingEquiv,
      fun r => rfl⟩
  set g₀' : Polynomial (maximalIdeal R).ResidueField := g₀.map e.toRingHom with hg₀'def
  set h₀' : Polynomial (maximalIdeal R).ResidueField := h₀.map e.toRingHom with hh₀'def
  have hg₀'mon : g₀'.Monic := hg₀.map _
  have hh₀'mon : h₀'.Monic := hh₀.map _
  have hcop' : IsCoprime g₀' h₀' := (Polynomial.isCoprime_map e.toRingHom).mpr hcop
  have hbridge : (e.toRingHom.comp (residue R)) = algebraMap R (maximalIdeal R).ResidueField := by
    ext x; exact he x
  have hfac' : p.map (algebraMap R (maximalIdeal R).ResidueField) = g₀' * h₀' := by
    rw [hg₀'def, hh₀'def, ← Polynomial.map_mul, ← hfac, Polynomial.map_map, hbridge]
  obtain ⟨R', _, _, _, Q, _, _, g', h', hbij, hg'mon, hh'mon, hmapfac, hcop'', hg'res, hh'res⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime (maximalIdeal R) p
      g₀' h₀' hp hg₀'mon hh₀'mon hfac' hcop'
  obtain ⟨σ₀, hker⟩ := henselian_etale_exists_section R R' Q hbij
  have hQ : Q = (maximalIdeal R).comap σ₀.toRingHom := by
    have hQover : maximalIdeal R = Q.comap (algebraMap R R') := Ideal.LiesOver.over
    have hdiff : ∀ y : R', y - algebraMap R R' (σ₀ y) ∈ Q := by
      intro y; apply hker; rw [RingHom.mem_ker]; simp [σ₀.commutes]
    apply le_antisymm
    · intro y hy
      rw [Ideal.mem_comap]; change σ₀ y ∈ maximalIdeal R
      rw [hQover, Ideal.mem_comap]
      have : algebraMap R R' (σ₀ y) = y - (y - algebraMap R R' (σ₀ y)) := by ring
      rw [this]; exact Q.sub_mem hy (hdiff y)
    · intro y hy
      rw [Ideal.mem_comap] at hy
      have hmem : algebraMap R R' (σ₀ y) ∈ Q := by
        rw [hQover, Ideal.mem_comap] at hy; exact hy
      have : y = (y - algebraMap R R' (σ₀ y)) + algebraMap R R' (σ₀ y) := by ring
      rw [this]; exact Q.add_mem (hdiff y) hmem
  have residue_cond :
    ∀ (gg₀ : Polynomial (ResidueField R)) (gg' : Polynomial R'),
      (gg₀.map e.toRingHom).map
            (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
                (Ideal.LiesOver.over)).toRingHom =
          gg'.map (algebraMap R' Q.ResidueField) →
        (gg'.map σ₀.toRingHom).map (residue R) = gg₀ := by
    intro gg₀ gg' hgres
    set τ : Q.ResidueField →+* ResidueField R :=
      (e.symm.toRingHom).comp (Ideal.ResidueField.map Q (maximalIdeal R) σ₀.toRingHom hQ) with hτ
    have hcond1 : ∀ y : R', τ (algebraMap R' Q.ResidueField y) = residue R (σ₀ y) := by
      intro y
      rw [hτ]
      change
        e.symm
            (Ideal.ResidueField.map Q (maximalIdeal R) σ₀.toRingHom hQ
              (algebraMap R' Q.ResidueField y)) =
          _
      rw [Ideal.ResidueField.map_algebraMap, ← he]
      exact e.symm_apply_apply _
    have hcond2 :
      τ.comp
          (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
              (Ideal.LiesOver.over)).toRingHom =
        e.symm.toRingHom := by
      apply Ideal.ResidueField.ringHom_ext
      ext r
      change
        τ
            ((Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R') (Ideal.LiesOver.over))
              (algebraMap R (maximalIdeal R).ResidueField r)) =
          e.symm (algebraMap R (maximalIdeal R).ResidueField r)
      rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
      change τ (algebraMap R' Q.ResidueField ((Algebra.ofId R R') r)) = _
      have hofId : (Algebra.ofId R R') r = algebraMap R R' r := rfl
      rw [hofId, hcond1 (algebraMap R R' r), σ₀.commutes, ← he]
      exact (e.symm_apply_apply _).symm ▸ rfl
    rw [Polynomial.map_map]
    have hcomp : (residue R).comp σ₀.toRingHom = τ.comp (algebraMap R' Q.ResidueField) := by
      ext y; exact (hcond1 y).symm
    rw [hcomp, ← Polynomial.map_map, ← hgres, Polynomial.map_map, hcond2, Polynomial.map_map]
    have hee : (e.symm.toRingHom).comp e.toRingHom = RingHom.id _ := by
      ext x; simp
    rw [hee, Polynomial.map_id]
  refine ⟨g'.map σ₀.toRingHom, h'.map σ₀.toRingHom, hg'mon.map _, hh'mon.map _, ?_, ?_, ?_⟩
  · have key : (p.map (algebraMap R R')).map σ₀.toRingHom = p := by
      rw [Polynomial.map_map]
      have : (σ₀.toRingHom.comp (algebraMap R R')) = RingHom.id R := by
        ext r; exact σ₀.commutes r
      rw [this, Polynomial.map_id]
    rw [← key, hmapfac, Polynomial.map_mul]
  · exact residue_cond g₀ g' hg'res
  · exact residue_cond h₀ h' hh'res

open Polynomial IsLocalRing in
private theorem hensel_idempotent_lift_of_finite_aux (R : Type) [CommRing R] [HenselianLocalRing R]
    (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (b : B)
    (hb : b * b - b ∈ ((maximalIdeal R).map (algebraMap R B)))
    (Hfact :
      ∀ (p : Polynomial R),
        p.Monic →
          ∀ (g₀ h₀ : Polynomial (ResidueField R)),
            g₀.Monic →
              h₀.Monic →
              p.map (residue R) = g₀ * h₀ →
              IsCoprime g₀ h₀ →
              ∃ g h : Polynomial R,
                g.Monic ∧ h.Monic ∧ p = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀) :
    ∃ e : B, e * e = e ∧ e - b ∈ ((maximalIdeal R).map (algebraMap R B)) := by
  classical
  set mB : Ideal B := (maximalIdeal R).map (algebraMap R B) with hmB
  set π : B →+* (B ⧸ mB) := Ideal.Quotient.mk mB with hπ
  have hle : maximalIdeal R ≤ RingHom.ker (π.comp (algebraMap R B)) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  set ψ : ResidueField R →+* (B ⧸ mB) :=
    Ideal.Quotient.lift (maximalIdeal R) (π.comp (algebraMap R B))
      (fun x hx => by
        rw [← RingHom.mem_ker]; exact hle hx) with
    hψ
  have hcompat : ∀ r : R, ψ (residue R r) = π (algebraMap R B r) := fun r => rfl
  set bbar := π b with hbbar
  have key : ∀ q : Polynomial R, π (aeval b q) = eval₂ ψ bbar (q.map (residue R)) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a => simp [hcompat a]
    | add p q hp hq => simp [hp, hq]
    | monomial n a ih =>
      simp only [map_mul, map_pow, aeval_C, aeval_X, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hcompat, hbbar]
  have hbidem : bbar * bbar = bbar := by
    have h0 : π (b * b - b) = 0 := by
      rw [hπ, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    rw [map_sub, map_mul] at h0
    change π b * π b = π b
    linear_combination h0
  have evalIdem :
    ∀ q : Polynomial (ResidueField R),
      eval₂ ψ bbar q = ψ (q.eval 0) * (1 - bbar) + ψ (q.eval 1) * bbar := by
    intro q
    have hxn : ∀ n : ℕ, bbar ^ (n + 1) = bbar := by
      intro n;
      induction n with
      | zero => simp
      | succ k ihk => rw [pow_succ, ihk, hbidem]
    induction q using Polynomial.induction_on with
    | C a =>
      simp; ring
    | add p q hp hq =>
      rw [eval₂_add, hp, hq]; simp only [eval_add, map_add]; ring
    | monomial n a ih =>
      rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hxn n]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [zero_pow (Nat.succ_ne_zero n), one_pow, mul_zero, mul_one, map_zero, zero_mul, zero_add]
  -- monic annihilator
  obtain ⟨p, hpmon, hpz⟩ := IsIntegral.of_finite R b
  set p' : Polynomial R := p * (X * (X - 1)) with hp'def
  have hXX1mon : (X * (X - 1) : Polynomial R).Monic := by
    have h1 : (X - 1 : Polynomial R) = X - C 1 := by simp
    rw [h1]; exact (monic_X).mul (monic_X_sub_C 1)
  have hp'mon : p'.Monic := hpmon.mul hXX1mon
  have hp'z : aeval b p' = 0 := by
    rw [hp'def]
    simp only [map_mul, map_sub, map_one, aeval_X]
    have : (aeval b) p = 0 := hpz
    rw [this, zero_mul]
  -- P over κ
  set P : Polynomial (ResidueField R) := p'.map (residue R) with hPdef
  have hPmon : P.Monic := hp'mon.map _
  have hPeq : P = (p.map (residue R)) * (X * (X - 1)) := by
    rw [hPdef, hp'def]; simp [Polynomial.map_mul]
  have hXdvd : (X : Polynomial (ResidueField R)) ∣ P := by
    rw [hPeq]; exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  have hX1dvd : (X - 1 : Polynomial (ResidueField R)) ∣ P := by
    rw [hPeq]; exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  -- SPLIT
  obtain ⟨G₀, H₀, hG₀mon, hH₀mon, hPfac, hcop0, hG₀1, hH₀0⟩ :
    ∃ G₀ H₀ : Polynomial (ResidueField R),
      G₀.Monic ∧ H₀.Monic ∧ P = G₀ * H₀ ∧ IsCoprime G₀ H₀ ∧ G₀.eval 1 = 0 ∧ H₀.eval 0 = 0 :=
    by
    have hP0 : P ≠ 0 := hPmon.ne_zero
    set k := P.rootMultiplicity 1 with hk
    obtain ⟨q, hPq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 1
    have hC1 : (X - C (1 : ResidueField R)) = (X - 1 : Polynomial (ResidueField R)) := by simp
    rw [hC1] at hPq hndvd
    have hmonG : ((X - 1 : Polynomial (ResidueField R)) ^ k).Monic := by
      rw [← hC1]; exact (monic_X_sub_C 1).pow k
    have hmonq : q.Monic := by
      have h2 := hPmon; rw [hPq] at h2; exact hmonG.of_mul_monic_left h2
    have hirr : Irreducible (X - 1 : Polynomial (ResidueField R)) := by
      have := Polynomial.irreducible_X_sub_C (1 : ResidueField R); rwa [hC1] at this
    have hcop1 : IsCoprime (X - 1 : Polynomial (ResidueField R)) q :=
      (hirr.coprime_iff_not_dvd).mpr hndvd
    refine ⟨(X - 1) ^ k, q, hmonG, hmonq, hPq, hcop1.pow_left, ?_, ?_⟩
    · have hk1 : 1 ≤ k := by
        rw [hk];
        exact
          (Polynomial.le_rootMultiplicity_iff hP0).mpr
            (by
              rw [pow_one, hC1]; exact hX1dvd)
      simp only [eval_pow, eval_sub, eval_X, eval_one, sub_self]
      exact zero_pow (by omega)
    · have hXcop : IsCoprime (X : Polynomial (ResidueField R)) ((X - 1) ^ k) := by
        have h0 : (X : Polynomial (ResidueField R)) = X - C 0 := by simp
        have h1 : (X - 1 : Polynomial (ResidueField R)) = X - C 1 := hC1.symm
        have : IsCoprime (X - C (0 : ResidueField R)) (X - C (1 : ResidueField R)) :=
          Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by simp)
        rw [← h0, ← h1] at this
        exact this.pow_right
      have hXq : (X : Polynomial (ResidueField R)) ∣ q := by
        have hXP : (X : Polynomial (ResidueField R)) ∣ (X - 1) ^ k * q := by
          rw [← hPq]; exact hXdvd
        exact (hXcop.dvd_of_dvd_mul_left hXP)
      have hr : q.IsRoot 0 := by
        rw [← Polynomial.dvd_iff_isRoot]; simpa using hXq
      simpa [Polynomial.IsRoot] using hr
  -- FACTORIZATION over R
  obtain ⟨G, H, hGmon, hHmon, hGH, hGres, hHres⟩ := Hfact p' hp'mon G₀ H₀ hG₀mon hH₀mon hPfac hcop0
  -- coprime lift
  have hcopRH : IsCoprime G H := by
    have hcop0' : IsCoprime (G.map (residue R)) (H.map (residue R)) := by
      rw [hGres, hHres]; exact hcop0
    rw [← Polynomial.isUnit_resultant_iff_isCoprime hGmon, ←
      IsLocalRing.residue_ne_zero_iff_isUnit]
    have hGd : (G.map (residue R)).natDegree = G.natDegree := hGmon.natDegree_map _
    have hHd : (H.map (residue R)).natDegree = H.natDegree := hHmon.natDegree_map _
    have hmap : (G.map (residue R)).resultant (H.map (residue R)) = residue R (G.resultant H) := by
      have := Polynomial.resultant_map_map G H G.natDegree H.natDegree (residue R)
      rw [show
          (G.map (residue R)).resultant (H.map (residue R)) =
            (G.map (residue R)).resultant (H.map (residue R)) G.natDegree H.natDegree
          from by rw [hGd, hHd]]
      exact this
    rw [← hmap]
    have : IsUnit ((G.map (residue R)).resultant (H.map (residue R))) := by
      rw [Polynomial.isUnit_resultant_iff_isCoprime (hGmon.map _)]; exact hcop0'
    exact this.ne_zero
  -- Bézout
  obtain ⟨s, t, hbez⟩ := hcopRH
  -- evaluate at b
  set e₁ := aeval b G with he₁
  set e₂ := aeval b H with he₂
  set s' := aeval b s with hs'
  set t' := aeval b t with ht'
  have he₁e₂ : e₁ * e₂ = 0 := by
    rw [he₁, he₂, ← map_mul, ← hGH]; exact hp'z
  have hbezb : s' * e₁ + t' * e₂ = 1 := by
    have : aeval b (s * G + t * H) = aeval b (1 : Polynomial R) := by rw [hbez]
    simpa [map_add, map_mul, hs', ht', he₁, he₂] using this
  set e := t' * e₂ with hedef
  have h1e : 1 - e = s' * e₁ := by linear_combination -hbezb
  have hidem : e * e = e := by
    have hz : e * (1 - e) = s' * t' * (e₁ * e₂) := by
      rw [h1e, hedef]; ring
    rw [he₁e₂, mul_zero] at hz
    linear_combination -hz
  refine ⟨e, hidem, ?_⟩
  -- residue match: π e = π b
  rw [← Ideal.Quotient.eq_zero_iff_mem (I := mB), ← hπ, map_sub, sub_eq_zero]
  change π e = bbar
  -- π e₂ = ψ (H₀.eval 1) * bbar
  have hπe₂ : π e₂ = ψ (H₀.eval 1) * bbar := by
    rw [he₂, key H, hHres, evalIdem H₀, hH₀0, map_zero, zero_mul, zero_add]
  -- π t' = ψ(t̄.eval0)(1-bbar) + ψ(t̄.eval1)bbar
  have hπt' :
    π t' =
      ψ ((t.map (residue R)).eval 0) * (1 - bbar) + ψ ((t.map (residue R)).eval 1) * bbar := by
    rw [ht', key t, evalIdem (t.map (residue R))]
  -- coefficient identity: t̄.eval 1 * H₀.eval 1 = 1
  have hcoef : (t.map (residue R)).eval 1 * H₀.eval 1 = 1 := by
    have hbezκ : (s.map (residue R)) * G₀ + (t.map (residue R)) * H₀ = 1 := by
      have h := congrArg (Polynomial.map (residue R)) hbez
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hGres, hHres,
        Polynomial.map_one] at h
      exact h
    have := congrArg (Polynomial.eval (1 : ResidueField R)) hbezκ
    simp only [eval_add, eval_mul, eval_one] at this
    rw [hG₀1, mul_zero, zero_add] at this
    exact this
  -- combine
  rw [hedef, map_mul, hπe₂, hπt']
  set t0 := ψ ((t.map (residue R)).eval 0) with ht0
  set t1 := ψ ((t.map (residue R)).eval 1) with ht1
  set h1 := ψ (H₀.eval 1) with hh1
  have hmul : (1 - bbar) * bbar = 0 := by rw [sub_mul, one_mul, hbidem, sub_self]
  have hth : t1 * h1 = 1 := by rw [ht1, hh1, ← map_mul, hcoef, map_one]
  have hterm1 : t0 * (1 - bbar) * (h1 * bbar) = 0 := by
    have : t0 * (1 - bbar) * (h1 * bbar) = (t0 * h1) * ((1 - bbar) * bbar) := by ring
    rw [this, hmul, mul_zero]
  have hterm2 : t1 * bbar * (h1 * bbar) = bbar := by
    have : t1 * bbar * (h1 * bbar) = (t1 * h1) * (bbar * bbar) := by ring
    rw [this, hth, hbidem, one_mul]
  rw [add_mul, hterm1, hterm2, zero_add]

/-- **Idempotent lifting in a finite algebra over a henselian local ring.** For `B`
module-finite, hence integral, over henselian local `R`, with `mB := m·B`: given `b : B` with
`b² - b ∈ mB` (an *approximate* idempotent), there is a genuine idempotent `e : B` with
`e - b ∈ mB`.

This is derived from the Hensel FACTORIZATION form over `R`
(`hensel_factorization_over_R`). The element `b` is integral over `R`
(`Algebra.IsIntegral.of_finite`), so fix a monic `p ∈ R[T]` with `p(b) = 0`. Its image
`b̄ ∈ B̄ := B/mB` is idempotent, and `B̄`
is a finite, hence Artinian, `κ`-algebra, so `p̄ = p.map (residue R)` annihilates the
idempotent `b̄`. Splitting off `T(T-1)`, the reduction `p̄` therefore admits a COPRIME monic
factorization `p̄ = G₀·H₀` over `κ`, with `G₀` carrying the `b̄ = 0` spectrum and `H₀` the
`b̄ = 1` spectrum — concretely `p̄ = T^a·(T-1)^c` up to the radical, the two factors coprime
because `T` and `T - 1` are. Applying `hensel_factorization_over_R` to `p, G₀, H₀` yields
monic `G, H ∈ R[T]` with `p = G·H`, `Ḡ = G₀` and `H̄ = H₀`. These are coprime over `R`
(coprime mod `m ⊆ Jac R`, so the resultant is a unit and Bézout gives `sG + tH = 1`).
Evaluating at `b` gives `G(b)H(b) = 0` and `s(b)G(b) + t(b)H(b) = 1`, so `e := t(b)·H(b)` is
idempotent in `B` with `e - b ∈ mB`, matching the spectra of `b̄`. -/
theorem hensel_idempotent_lift_of_finite (R : Type) [CommRing R] [HenselianLocalRing R] (B : Type)
    [CommRing B] [Algebra R B] [Module.Finite R B] (b : B)
    (hb : b * b - b ∈ ((maximalIdeal R).map (algebraMap R B))) :
    ∃ e : B, e * e = e ∧ e - b ∈ ((maximalIdeal R).map (algebraMap R B)) := by
  -- The idempotent lift along `mB` for `B` finite over henselian local `R`
  -- (Stacks 09XI/04GG). The interesting case is `B = R[x]/(x²-x-p)`, where the coprime
  -- split `x·(x-1)` mod `m` produces an idempotent that is not visible in `B` itself.
  exact
    hensel_idempotent_lift_of_finite_aux R B b hb
      (fun p hp g₀ h₀ hg₀ hh₀ hfac hcop =>
        hensel_factorization_over_R R p hp g₀ h₀ hg₀ hh₀ hfac hcop)

end
end
