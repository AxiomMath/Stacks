module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Algebra.Order.Sub.Unbundled.Hom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Noetherian complete local rings: quotients and finite algebras

This file defines `IsNoetherianCompleteLocalRing R`: `R` is Noetherian, local, and complete with
respect to its maximal ideal. It shows that the quotient of such a ring by a proper ideal is again
one (`quotient_isNoetherianCompleteLocalRing`), lifts complete orthogonal idempotents along a
complete ring, and deduces that a finite algebra over a Noetherian complete local ring is a finite
product of Noetherian complete local rings (`finite_isProduct_isNoetherianCompleteLocalRing`).

## References

* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
-/

@[expose] public section

universe u v

/-- A *Noetherian complete local ring* is a commutative ring `R` that is
Noetherian, local (with a unique maximal ideal, nontrivial), and complete with
respect to the maximal-ideal-adic topology. -/
@[ega "0 7.1.2" "special case",
  ega "0 7.1.9" "special case",
  ega "III 5.1.1" "special case",
  sga "2 X 2.1",
  sga "3 XX 1.10",
  sga "7 VI 1.15" "partial",
  sga "7 VI 5.11" "partial"]
structure IsNoetherianCompleteLocalRing (R : Type*) [CommRing R] : Prop where
  /-- `R` is Noetherian. -/
  isNoetherian : IsNoetherianRing R
  /-- `R` is local (unique maximal ideal, nontrivial). -/
  isLocal : IsLocalRing R
  /-- `R` is complete with respect to the maximal-ideal-adic topology. -/
  isComplete : @IsAdicComplete R _ (@IsLocalRing.maximalIdeal R _ isLocal) R _ _

/-- A sequence whose `n`-th increment lies in `I ^ n` is `I`-adically Cauchy: for `m ≤ n`,
`g n - g m ∈ I ^ m`. -/
theorem sub_mem_pow_of_succ_sub_mem_pow {R : Type*} [CommRing R] {I : Ideal R}
    {g a : ℕ → R} (hg : ∀ n, g (n + 1) = g n + a n) (ha : ∀ n, a n ∈ I ^ n) {m n : ℕ}
    (hmn : m ≤ n) : g n - g m ∈ I ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    rw [hg, add_sub_right_comm]
    exact add_mem ih (Ideal.pow_le_pow_right hmk (ha k))

/-- The target of a surjective ring map out of an `I`-adically precomplete ring is
`I.map f`-adically precomplete. -/
theorem isPrecomplete_map_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} [IsPrecomplete I R] {f : R →+* S} (hf : Function.Surjective f) :
    IsPrecomplete (I.map f) S := by
  refine ⟨fun {x} hx => ?_⟩
  have hlift : ∀ n : ℕ, ∃ b ∈ I ^ n, f b = x (n + 1) - x n := by
    intro n
    have h := (I.map f ^ n).neg_mem (by simpa [SModEq.sub_mem] using hx n.le_succ)
    rwa [neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective f hf] at h
  choose a ha hfa using hlift
  obtain ⟨b, hb⟩ := hf (x 0)
  let g : ℕ → R := fun n => Nat.rec b (fun k gk => gk + a k) n
  have hg : ∀ n, g (n + 1) = g n + a n := fun _ => rfl
  have hfg : ∀ n, f (g n) = x n := by
    intro n
    induction n with
    | zero => exact hb
    | succ k ih => rw [hg, map_add, ih, hfa, add_sub_cancel]
  obtain ⟨L, hL⟩ := ‹IsPrecomplete I R›.prec (f := g) fun {m n} hmn => by
    simpa [SModEq.sub_mem] using (I ^ m).neg_mem (sub_mem_pow_of_succ_sub_mem_pow hg ha hmn)
  refine ⟨f L, fun n => ?_⟩
  have h : g n - L ∈ I ^ n := by simpa [SModEq.sub_mem] using hL n
  simpa [SModEq.sub_mem, ← hfg n, ← Ideal.map_pow] using Ideal.mem_map_of_mem f h

/-- If `R` is a Noetherian complete local ring and `J` is a proper ideal of `R`, then the
quotient `R / J` is again a Noetherian complete local ring. -/
@[stacks 0325, ega "0 20.7.20" "special case", ega "IV 18.5.16" "special case"]
theorem quotient_isNoetherianCompleteLocalRing
    {R : Type*} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    (J : Ideal R) (hJ : J ≠ ⊤) :
    IsNoetherianCompleteLocalRing (R ⧸ J) := by
  have : IsLocalRing R := hR.isLocal
  have : IsNoetherianRing R := hR.isNoetherian
  have : Nontrivial (R ⧸ J) := (Ideal.Quotient.nontrivial_iff).mpr hJ
  have hloc : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (R ⧸ J) := inferInstance
  have hadic : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
    have := hR.isComplete
    have := isPrecomplete_map_of_surjective (I := IsLocalRing.maximalIdeal R)
      (Ideal.Quotient.mk_surjective (I := J))
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at this
    exact ⟨⟩
  exact ⟨inferInstance, hloc, hadic⟩

/-- A finite algebra `S` over a Noetherian complete local ring `R` is complete with respect to
the `m`-adic topology of the base, where `m = maximalIdeal R`; that is, `S` is
`(m·S)`-adically complete. -/
@[ega "0 7.4.2" "special case",
  ega "0 7.7.8" "A = B",
  ega "0 7.8.1" "special case",
  ega "IV 18.5.16" "special case"]
private lemma finite_isAdicComplete_of_complete
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete
      (Ideal.map (algebraMap R S) (@IsLocalRing.maximalIdeal R _ hR.isLocal)) S := by
  have hlocR : IsLocalRing R := hR.isLocal
  have hnoethR : IsNoetherianRing R := hR.isNoetherian
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hR.isComplete
  set m : Ideal R := IsLocalRing.maximalIdeal R with hm
  rw [IsAdicComplete.map_algebraMap_iff m S]
  have hHaus : IsHausdorff m S := by
    have hjac : m ≤ (⊥ : Ideal R).jacobson := IsLocalRing.maximalIdeal_le_jacobson ⊥
    have hbot : (⨅ i, m ^ i • (⊤ : Submodule R S)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson m hjac
    refine ⟨fun x hx => ?_⟩
    have hmem : x ∈ (⨅ i, m ^ i • (⊤ : Submodule R S)) := by
      rw [Submodule.mem_iInf]
      intro n
      have := hx n
      rw [SModEq.sub_mem] at this
      simpa using this
    rw [hbot] at hmem
    simpa using hmem
  have hSurj : Function.Surjective (AdicCompletion.of m S) := by
    have hRb : Function.Bijective (AdicCompletion.of m R) :=
      AdicCompletion.of_bijective_iff.mpr ‹_›
    intro y
    obtain ⟨t, ht⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite m S y
    have hrange : ∀ s : TensorProduct R (AdicCompletion m R) S,
        AdicCompletion.ofTensorProduct m S s ∈ LinearMap.range (AdicCompletion.of m S) := by
      intro s
      induction s using TensorProduct.inductionOn with
      | tmul r x =>
          obtain ⟨r0, hr0⟩ := hRb.surjective r
          rw [AdicCompletion.ofTensorProduct_tmul, ← hr0]
          exact ⟨r0 • x, by rw [map_smul]; rfl⟩
      | add a b ha hb =>
          rw [map_add]
          exact (LinearMap.range (AdicCompletion.of m S)).add_mem ha hb
    obtain ⟨x, hx⟩ := hrange t
    exact ⟨x, by rw [hx, ht]⟩
  rw [← AdicCompletion.of_bijective_iff]
  exact ⟨AdicCompletion.of_injective_iff.mpr hHaus, hSurj⟩

/-!
### Lifting idempotents along a complete ring

Along a `J`-adically complete ring `S`, a complete orthogonal idempotents family on the quotient
`S ⧸ J` lifts to one on `S`.
-/

/-- The class modulo `J^(n+1)` is the image of the class modulo `J^(n+2)` under `factorPow`. -/
private theorem mk_eq_factorPow_mk {S : Type*} [CommRing S] (J : Ideal S) {n : ℕ} (y : S) :
    (Ideal.Quotient.mk (J^(n+1))) y
      = (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))) ((Ideal.Quotient.mk (J^(n+2))) y) := by
  simp [Ideal.Quotient.factorPow]

/-- The transition kernel `S ⧸ J^(n+2) → S ⧸ J^(n+1)` is nilpotent (square-zero). -/
private theorem ker_nilp {S : Type*} [CommRing S] (J : Ideal S) (n : ℕ) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))), IsNilpotent x := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  have hxe : (Ideal.Quotient.mk (J^(n+1))) y = 0 := by
    rw [mk_eq_factorPow_mk]
    exact hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at hxe
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega) : (J^(n+1))^2 ≤ J^(n+2))
    (Ideal.pow_mem_pow hxe 2)

/-- `Ideal.Quotient.factorPow` is surjective. -/
private theorem factorPow_surj {S : Type*} [CommRing S] (J : Ideal S) {m n : ℕ} (h : n ≤ m) :
    Function.Surjective (Ideal.Quotient.factorPow J h) := by
  intro x; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ y, by simp [Ideal.Quotient.factorPow]⟩

/-- A compatible inverse system of COI families on `S ⧸ J^(n+1)`, built by
nilpotently lifting one step at a time. -/
private noncomputable def coiSeq {S : Type*} [CommRing S] (J : Ideal S) {k : ℕ}
    (ē : Fin k → S ⧸ J ^ 1) (hē : CompleteOrthogonalIdempotents ē) :
    (n : ℕ) → {f : Fin k → S ⧸ J^(n+1) // CompleteOrthogonalIdempotents f } :=
  Nat.rec ⟨ē, hē⟩
    (fun n prev =>
      let hlift := prev.property.lift_of_isNilpotent_ker
        (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))) (ker_nilp J n)
        (fun i => (factorPow_surj J (Nat.le_succ (n+1))) (prev.val i))
      ⟨hlift.choose, hlift.choose_spec.left⟩)

/-- The COI system `coiSeq` is compatible under the transition maps `factorPow`. -/
private theorem coiSeq_compat {S : Type*} [CommRing S] (J : Ideal S) {k : ℕ}
    (ē : Fin k → S ⧸ J ^ 1) (hē : CompleteOrthogonalIdempotents ē) (n : ℕ) (i : Fin k) :
    (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))) ((coiSeq J ē hē (n+1)).1 i)
      = (coiSeq J ē hē n).1 i := by
  have hlift := (coiSeq J ē hē n).property.lift_of_isNilpotent_ker
    (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))) (ker_nilp J n)
    (fun i => (factorPow_surj J (Nat.le_succ (n+1))) ((coiSeq J ē hē n).val i))
  change (Ideal.Quotient.factorPow J (Nat.le_succ (n+1))) (hlift.choose i)
      = (coiSeq J ē hē n).1 i
  exact congrFun hlift.choose_spec.right i

/-- Congruence modulo `I ^ n • ⊤` in a ring is membership of the difference in `I ^ n`. -/
private theorem smodEq_pow_smul_top_iff {S : Type*} [CommRing S] (I : Ideal S) (n : ℕ)
    (x y : S) : (x ≡ y [SMOD I ^ n • (⊤ : Submodule S S)]) ↔ (x - y ∈ I ^ n) := by
  rw [SModEq.sub_mem]; simp

/-- A compatible family `c n ∈ S ⧸ J^(n+1)` lifts to an element `L ∈ S` (using
completeness of `S`). -/
private theorem compat_limit {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S]
    (c : (n : ℕ) → S ⧸ J ^ (n + 1))
    (hc : ∀ n, (Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))) (c (n + 1)) = c n) :
    ∃ L : S, ∀ n, (Ideal.Quotient.mk (J^(n+1))) L = c n := by
  choose rep hrep using fun n => Ideal.Quotient.mk_surjective (c n)
  have hinc : ∀ n, rep (n+1) - rep n ∈ J^(n+1) := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    have key : (Ideal.Quotient.mk (J^(n+1))) (rep (n+1))
        = (Ideal.Quotient.mk (J^(n+1))) (rep n) := by
      rw [mk_eq_factorPow_mk, hrep, hc, hrep]
    rw [key, sub_self]
  have hmemf : ∀ {a b : ℕ}, a ≤ b → rep b - rep a ∈ J ^ a := by
    intro a b hab
    induction b with
    | zero => interval_cases a; simp
    | succ m ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hab) with h | h
        · have ham : a ≤ m := Nat.lt_succ_iff.mp h
          have : rep (m+1) - rep a = (rep (m+1) - rep m) + (rep m - rep a) := by ring
          rw [this]
          exact (J^a).add_mem (Ideal.pow_le_pow_right (Nat.le_succ_of_le ham) (hinc m)) (ih ham)
        · subst h; simp
  have hcauchy : ∀ {a b : ℕ}, a ≤ b → rep a ≡ rep b [SMOD J^a • (⊤ : Submodule S S)] := by
    intro a b hab
    rw [smodEq_pow_smul_top_iff, show rep a - rep b = -(rep b - rep a) by ring]
    exact (J^a).neg_mem (hmemf hab)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsAdicComplete J S›.toIsPrecomplete hcauchy
  refine ⟨L, fun n => ?_⟩
  have hLn : rep (n+1) - L ∈ J ^ (n+1) := (smodEq_pow_smul_top_iff J _ _ _).mp (hL (n+1))
  have heq : (Ideal.Quotient.mk (J^(n+1))) L = (Ideal.Quotient.mk (J^(n+1))) (rep (n+1)) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
      show L - rep (n+1) = -(rep (n+1) - L) by ring]
    exact (J^(n+1)).neg_mem hLn
  rw [heq, mk_eq_factorPow_mk, hrep, hc]

/-- Equality in `S` from equality modulo every `J^(n+1)` (Hausdorff). -/
private theorem haus_eq {S : Type*} [CommRing S] (J : Ideal S) [IsHausdorff J S] (x y : S)
    (h : ∀ n, (Ideal.Quotient.mk (J ^ (n + 1))) x
      = (Ideal.Quotient.mk (J ^ (n + 1))) y) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := J)]
  intro n
  rw [SModEq.sub_mem]
  cases n with
  | zero => simp
  | succ m =>
      have := h m
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at this
      simpa using this

/-- Idempotent lifting along a complete ring: for a `J`-adically complete
ring `S`, any complete orthogonal idempotents family on `S ⧸ J` lifts to a
complete orthogonal idempotents family on `S` mapping onto it. -/
private theorem coi_lift {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S] {k : ℕ}
    (ē : Fin k → S ⧸ J) (hē : CompleteOrthogonalIdempotents ē) :
    ∃ e : Fin k → S, CompleteOrthogonalIdempotents e ∧
      ∀ i, (Ideal.Quotient.mk J) (e i) = ē i := by
  classical
  let φ : (S ⧸ J ^ 1) ≃+* (S ⧸ J) :=
    Ideal.quotientEquiv (J^1) J (RingEquiv.refl S) (by rw [pow_one]; simp)
  have hφmk : ∀ x : S, φ ((Ideal.Quotient.mk (J^1)) x) = (Ideal.Quotient.mk J) x :=
    fun x => by simp [φ]
  let e1 : Fin k → S ⧸ J ^ 1 := fun i => φ.symm (ē i)
  have he1 : CompleteOrthogonalIdempotents e1 := hē.map φ.symm.toRingHom
  have hlimit : ∀ i, ∃ L : S,
      ∀ n, (Ideal.Quotient.mk (J^(n+1))) L = (coiSeq J e1 he1 n).val i :=
    fun i => compat_limit J _ fun n => coiSeq_compat J e1 he1 n i
  choose e he using hlimit
  refine ⟨e, ?_, ?_⟩
  · have : IsHausdorff J S := ‹IsAdicComplete J S›.toIsHausdorff
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      apply haus_eq J
      intro n
      have hi := he i n
      change (Ideal.Quotient.mk (J^(n+1))) ((e i) * (e i)) = (Ideal.Quotient.mk (J^(n+1))) (e i)
      calc (Ideal.Quotient.mk (J^(n+1))) ((e i) * (e i))
          = (Ideal.Quotient.mk (J^(n+1))) (e i) * (Ideal.Quotient.mk (J^(n+1))) (e i) := by
            rw [map_mul]
        _ = (coiSeq J e1 he1 n).val i * (coiSeq J e1 he1 n).val i := by rw [hi]
        _ = (coiSeq J e1 he1 n).val i := (coiSeq J e1 he1 n).property.idem i
        _ = (Ideal.Quotient.mk (J^(n+1))) (e i) := by rw [hi]
    · intro i j hij
      apply haus_eq J
      intro n
      have hi := he i n
      have hj := he j n
      have hortho : ((coiSeq J e1 he1 n).val i) * ((coiSeq J e1 he1 n).val j) = 0 :=
        (coiSeq J e1 he1 n).property.ortho hij
      change (Ideal.Quotient.mk (J^(n+1))) ((e i) * (e j)) = (Ideal.Quotient.mk (J^(n+1))) 0
      rw [map_zero, map_mul, hi, hj, hortho]
    · apply haus_eq J
      intro n
      have hcompl : ∑ i, (coiSeq J e1 he1 n).val i = 1 :=
        (coiSeq J e1 he1 n).property.complete
      rw [map_one, map_sum]
      rw [show (∑ i, (Ideal.Quotient.mk (J^(n+1))) (e i))
          = ∑ i, (coiSeq J e1 he1 n).val i from
        Finset.sum_congr rfl (fun i _ => he i n)]
      exact hcompl
  · intro i
    have h0 := he i 0
    have hrfl : (coiSeq J e1 he1 0).val i = e1 i := rfl
    rw [hrfl] at h0
    have hh : φ ((Ideal.Quotient.mk (J^1)) (e i)) = φ (e1 i) := by rw [h0]
    rw [hφmk] at hh
    rw [hh]
    change φ (φ.symm (ē i)) = ē i
    simp

/-!
### Finite complete extensions decompose as products

A ring `S`, finite over a Noetherian complete local ring `R` and complete for the `m`-adic
topology of the base, is a finite product of Noetherian complete local rings: it carries a
complete orthogonal idempotents family `e` whose factor rings `S ⧸ span {1 - e i}` are local
(`S3a_exists_coi_with_local_factors`) and complete for their maximal ideals
(`S3b_factor_isAdicComplete`).
-/

-- needed: `S3a_pi_single_factor_local`'s quotient-of-product manipulations only close
-- when defeq may unfold `Pi.single`/`Ideal.span` past the default transparency
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- For a product `∏ T j` of commutative rings with `T i` local, the COI factor
`(∏ T j) ⧸ span{1 - Pi.single i 1}` is local (it is `≅ T i`). -/
private lemma S3a_pi_single_factor_local (ι : Type*) [DecidableEq ι]
    (T : ι → Type*) [∀ i, CommRing (T i)] (i : ι) [hl : IsLocalRing (T i)] :
    IsLocalRing ((∀ j, T j) ⧸ Ideal.span {1 - (Pi.single i 1 : ∀ j, T j)}) := by
  set P := ∀ j, T j
  have hker : Ideal.span {1 - (Pi.single i 1 : P)} = RingHom.ker (Pi.evalRingHom T i) := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp [Pi.single_eq_same]
    · intro y hy
      rw [RingHom.mem_ker] at hy
      rw [Ideal.mem_span_singleton]
      refine ⟨y, ?_⟩
      ext j
      by_cases hj : j = i
      · subst hj; simp [Pi.evalRingHom] at hy; simp [hy]
      · simp [hj]
  rw [hker]
  let f : (P ⧸ RingHom.ker (Pi.evalRingHom T i)) ≃+* T i :=
    RingHom.quotientKerEquivOfSurjective (f := Pi.evalRingHom T i)
      (fun x => ⟨Pi.single i x, by simp [Pi.evalRingHom, Pi.single_eq_same]⟩)
  exact RingEquiv.isLocalRing f.symm

open Classical in
/-- Transport a complete orthogonal idempotents family with local factors across
a ring isomorphism. -/
private lemma S3a_coi_local_transfer {A P : Type*} [CommRing A] [CommRing P]
    {ι : Type*} [Fintype ι] (φ : A ≃+* P) (ē : ι → P)
    (hcoi : CompleteOrthogonalIdempotents ē)
    (hloc : ∀ i, IsLocalRing (P ⧸ Ideal.span {1 - ē i})) :
    ∃ e : ι → A, CompleteOrthogonalIdempotents e ∧
      ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i}) := by
  refine ⟨fun i => φ.symm (ē i), hcoi.map φ.symm.toRingHom, fun i => ?_⟩
  have hmap : Ideal.map φ (Ideal.span {1 - φ.symm (ē i)}) = Ideal.span {1 - ē i} := by
    simp [Ideal.map_span, Set.image_singleton]
  exact (Ideal.quotientEquiv _ _ φ hmap.symm).symm.isLocalRing

/-- If `I ≤ jacobson ⊥` and `mk I r` is a unit, then `r` is a unit. -/
private lemma S3a_isUnit_of_isUnit_quot {A : Type*} [CommRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson) (r : A)
    (h : IsUnit (Ideal.Quotient.mk I r)) : IsUnit r := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑h.unit⁻¹ : A ⧸ I)
  have hrs : Ideal.Quotient.mk I (r * s) = 1 := by
    rw [map_mul, hs]
    exact h.unit.mul_inv
  have hmem : r * s - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hrs, map_one, sub_self]
  exact isUnit_of_mul_isUnit_left (by simpa using Ideal.mem_jacobson_bot.mp (hI hmem) 1)

/-- A ring `A` whose quotient by an ideal `I ≤ jacobson` is local, is itself local. -/
private lemma S3a_local_of_quot_le_jacobson (A : Type*) [CommRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson) [IsLocalRing (A ⧸ I)] : IsLocalRing A := by
  have : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk I a) with h | h
  · left
    exact S3a_isUnit_of_isUnit_quot I hI a h
  · right
    have : IsUnit (Ideal.Quotient.mk I (1 - a)) := by rwa [map_sub, map_one]
    exact S3a_isUnit_of_isUnit_quot I hI (1 - a) this

/-- A nilpotent ideal is contained in the Jacobson radical. -/
private lemma S3a_nilpotent_le_jacobson (A : Type*) [CommRing A] (N : Ideal A) (h : IsNilpotent N) :
    N ≤ (⊥ : Ideal A).jacobson := by
  obtain ⟨n, hn⟩ := h
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxnil : IsNilpotent x := ⟨n, by
    have : x ^ n ∈ N ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this; simpa using this⟩
  have hxy : IsNilpotent (x * y) := Commute.isNilpotent_mul_right (Commute.all _ _) hxnil
  exact hxy.isUnit_add_one

/-- Locality of a COI factor transfers along a quotient by a `≤ jacobson` ideal. -/
private lemma S3a_local_factor_of_le_jacobson {A : Type*} [CommRing A] (N : Ideal A)
    (hN : N ≤ (⊥ : Ideal A).jacobson)
    (a : A) [IsLocalRing ((A ⧸ N) ⧸ Ideal.span {1 - Ideal.Quotient.mk N a})] :
    IsLocalRing (A ⧸ Ideal.span {1 - a}) := by
  set C := A ⧸ Ideal.span {1 - a} with hC
  set I : Ideal C := Ideal.map (Ideal.Quotient.mk (Ideal.span {1 - a})) N with hI
  have hImap : Ideal.map (Ideal.Quotient.mk (Ideal.span ({1-a}:Set A))) (⊥:Ideal A).jacobson
      ≤ (⊥ : Ideal C).jacobson := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.mem_jacobson_bot] at hx
    have h := (hx y0).map (Ideal.Quotient.mk (Ideal.span ({1-a}:Set A)))
    rw [map_add, map_mul, map_one] at h
    exact h
  have hIle : I ≤ (⊥ : Ideal C).jacobson := le_trans (Ideal.map_mono hN) hImap
  have e1 : (C ⧸ I) ≃+* A ⧸ (Ideal.span {1 - a} ⊔ N) :=
    DoubleQuot.quotQuotEquivQuotSup (Ideal.span {1 - a}) N
  have hspaneq : Ideal.span {1 - Ideal.Quotient.mk N a}
      = Ideal.map (Ideal.Quotient.mk N) (Ideal.span {1 - a}) := by
    rw [Ideal.map_span]; congr 1; simp [Set.image_singleton, map_sub, map_one]
  have e2 : ((A ⧸ N) ⧸ Ideal.span {1 - Ideal.Quotient.mk N a})
      ≃+* A ⧸ (N ⊔ Ideal.span {1 - a}) := by
    rw [hspaneq]; exact DoubleQuot.quotQuotEquivQuotSup N (Ideal.span {1 - a})
  have hsup : N ⊔ Ideal.span {1 - a} = Ideal.span {1 - a} ⊔ N := sup_comm _ _
  rw [hsup] at e2
  have : IsLocalRing (C ⧸ I) := RingEquiv.isLocalRing (e1.trans e2.symm).symm
  exact S3a_local_of_quot_le_jacobson C I hIle

open Classical in
/-- A commutative Artinian ring carries a `Fin k`-indexed complete orthogonal idempotents
family whose factor rings are each local. -/
@[ega "I 6.2.2" "special case", sga "3 VIIB 0.1.1" "partial"]
private lemma S3a_artinian_coi_fin {A : Type*} [CommRing A] [IsArtinianRing A] :
    ∃ (k : ℕ) (e : Fin k → A), CompleteOrthogonalIdempotents e ∧
      ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - e i}) := by
  set N : Ideal A := nilradical A with hN
  set B := A ⧸ N with hB
  have hred : IsReduced B :=
    (Ideal.isRadical_iff_quotient_reduced N).mp
      (show N.IsRadical from Ideal.radical_isRadical ⊥)
  have : IsArtinianRing B := inferInstance
  have : Finite (MaximalSpectrum B) := IsArtinianRing.instFiniteMaximalSpectrum B
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I => Ideal.Quotient.field I.asIdeal
  let : ∀ I : MaximalSpectrum B, IsLocalRing (B ⧸ I.asIdeal) := fun I => Field.instIsLocalRing _
  let φ : B ≃+* (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) := (IsArtinianRing.equivPi B).toRingEquiv
  have hcoiP : CompleteOrthogonalIdempotents
      (fun I : MaximalSpectrum B => (Pi.single I 1 : ∀ J : MaximalSpectrum B, B ⧸ J.asIdeal)) :=
    CompleteOrthogonalIdempotents.single _
  have hlocP : ∀ I : MaximalSpectrum B,
      IsLocalRing ((∀ J : MaximalSpectrum B, B ⧸ J.asIdeal) ⧸
        Ideal.span {1 - (Pi.single I 1 : ∀ J : MaximalSpectrum B, B ⧸ J.asIdeal)}) :=
    fun I => S3a_pi_single_factor_local _ (fun J => B ⧸ J.asIdeal) I
  obtain ⟨ēB, hēB, hlocB⟩ := S3a_coi_local_transfer φ _ hcoiP hlocP
  obtain ⟨ē, hē, hēeq⟩ := hēB.lift_of_isNilpotent_ker (Ideal.Quotient.mk N)
    (fun x hx => by rwa [Ideal.mk_ker] at hx) (fun i => Ideal.Quotient.mk_surjective (ēB i))
  have hlocA : ∀ I : MaximalSpectrum B, IsLocalRing (A ⧸ Ideal.span {1 - ē I}) := by
    intro I
    have heqi : Ideal.Quotient.mk N (ē I) = ēB I := congrFun hēeq I
    have : IsLocalRing ((A ⧸ N) ⧸ Ideal.span {1 - Ideal.Quotient.mk N (ē I)}) := by
      rw [heqi]
      exact hlocB I
    exact S3a_local_factor_of_le_jacobson N
      (S3a_nilpotent_le_jacobson A N IsArtinianRing.isNilpotent_nilradical) (ē I)
  let σ : Fin (Fintype.card (MaximalSpectrum B)) ≃ MaximalSpectrum B :=
    (Fintype.equivFin (MaximalSpectrum B)).symm
  exact ⟨_, ē ∘ σ, (CompleteOrthogonalIdempotents.equiv σ).mpr hē, fun i => hlocA (σ i)⟩

/-- The closed fibre `S ⧸ m·S` of a finite algebra `S` over a local ring `R` is Artinian. -/
lemma isArtinianRing_quotient_map_maximalIdeal {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  let : Algebra (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) _

/-- A ring `S`, finite over the complete local ring `R` and `m·S`-adically complete, carries a
complete orthogonal idempotents family whose factor rings `S ⧸ span{1 - eᵢ}` are each
local. -/
private lemma S3a_exists_coi_with_local_factors
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (hcomplete : IsAdicComplete
      (Ideal.map (algebraMap R S) (@IsLocalRing.maximalIdeal R _ hR.isLocal)) S) :
    ∃ (k : ℕ) (e : Fin k → S), CompleteOrthogonalIdempotents e ∧
      ∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i}) := by
  have hlocR : IsLocalRing R := hR.isLocal
  have hnoethR : IsNoetherianRing R := hR.isNoetherian
  set mR : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal with hmR
  set J : Ideal S := Ideal.map (algebraMap R S) mR with hJ
  have : IsAdicComplete J S := hcomplete
  have : IsArtinianRing (S ⧸ J) := isArtinianRing_quotient_map_maximalIdeal
  obtain ⟨k, ē, hē, hlocFib⟩ := S3a_artinian_coi_fin (A := S ⧸ J)
  obtain ⟨e, hecoi, heq⟩ := coi_lift J ē hē
  refine ⟨k, e, hecoi, ?_⟩
  intro i
  have hJjac : J ≤ (⊥ : Ideal S).jacobson := IsAdicComplete.le_jacobson_bot J
  have : IsLocalRing ((S ⧸ J) ⧸ Ideal.span {1 - Ideal.Quotient.mk J (e i)}) := by
    rw [heq i]; exact hlocFib i
  exact S3a_local_factor_of_le_jacobson J hJjac (e i)

/-- For a finite `R`-algebra `S` over the Noetherian complete local ring `R` and `e : Fin k → S`,
the factor ring `S ⧸ span{1 - eᵢ}`, when local, is complete for its own maximal-ideal-adic
topology. -/
private lemma S3b_factor_isAdicComplete
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    {k : ℕ} (e : Fin k → S) (i : Fin k)
    [IsLocalRing (S ⧸ Ideal.span {1 - e i})] :
    IsAdicComplete (IsLocalRing.maximalIdeal (S ⧸ Ideal.span {1 - e i}))
      (S ⧸ Ideal.span {1 - e i}) := by
  have hlocR : IsLocalRing R := hR.isLocal
  set F : Type v := S ⧸ Ideal.span {1 - e i} with hF
  set mR : Ideal R := @IsLocalRing.maximalIdeal R _ hR.isLocal with hmR
  have : Module.Finite R F :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R _)
  have hFcomplete : IsAdicComplete (Ideal.map (algebraMap R F) mR) F :=
    finite_isAdicComplete_of_complete hR
  set JF : Ideal F := Ideal.map (algebraMap R F) mR with hJFdef
  have : IsAdicComplete JF F := hFcomplete
  set mF : Ideal F := IsLocalRing.maximalIdeal F with hmF
  have hJFle : JF ≤ mF := by
    have h1 : JF ≤ (⊥ : Ideal F).jacobson := IsAdicComplete.le_jacobson_bot JF
    have h2 : (⊥ : Ideal F).jacobson = mF :=
      IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top
    rw [h2] at h1; exact h1
  have hArt : IsArtinianRing (F ⧸ JF) := isArtinianRing_quotient_map_maximalIdeal
  have hpow : ∃ N, mF ^ N ≤ JF := by
    have : Nontrivial (F ⧸ JF) := by
      have hne : JF ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal F).ne_top hJFle
      exact Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (F ⧸ JF) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk JF) Ideal.Quotient.mk_surjective
    have hjacM : (⊥ : Ideal (F ⧸ JF)).jacobson = Ideal.map (Ideal.Quotient.mk JF) mF := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact (IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk JF) Ideal.Quotient.mk_surjective).symm
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := F ⧸ JF)
    refine ⟨N, ?_⟩
    rw [hjacM, ← Ideal.map_pow] at hN
    have hle := (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk JF)).mp hN
    rwa [Ideal.mk_ker] at hle
  obtain ⟨N, hJI⟩ := hpow
  clear hFcomplete hArt
  set N1 : ℕ := N + 1 with hN1
  have hJI1 : mF ^ N1 ≤ JF := le_trans (Ideal.pow_le_pow_right (by omega)) hJI
  have hN1pos : 0 < N1 := by omega
  have hJpow : ∀ n : ℕ, mF ^ (N1 * n) ≤ JF ^ n := by
    intro n; rw [pow_mul]; exact Ideal.pow_right_mono hJI1 n
  have hnle : ∀ n : ℕ, n ≤ N1 * n := by
    intro n; calc n = 1 * n := by ring
      _ ≤ N1 * n := Nat.mul_le_mul_right n hN1pos
  have hHaus : IsHausdorff mF F := by
    refine ⟨fun x hx => ?_⟩
    have hxI : ∀ n, x ≡ 0 [SMOD JF ^ n • (⊤ : Submodule F F)] := by
      intro n
      rw [smodEq_pow_smul_top_iff]
      have hmem := hx (N1 * n)
      rw [smodEq_pow_smul_top_iff] at hmem
      have hmem' : x - 0 ∈ mF ^ (N1 * n) := hmem
      exact hJpow n hmem'
    exact ‹IsAdicComplete JF F›.toIsHausdorff.haus x hxI
  have hPrec : IsPrecomplete mF F := by
    refine ⟨fun f hf => ?_⟩
    have hgcauchy : ∀ {a b : ℕ}, a ≤ b →
        f (N1*a) ≡ f (N1*b) [SMOD JF ^ a • (⊤ : Submodule F F)] := by
      intro a b hab
      rw [smodEq_pow_smul_top_iff]
      have hle : N1 * a ≤ N1 * b := Nat.mul_le_mul_left N1 hab
      have hmem := hf hle
      rw [smodEq_pow_smul_top_iff] at hmem
      exact hJpow a hmem
    obtain ⟨L, hL⟩ := ‹IsAdicComplete JF F›.toIsPrecomplete.prec hgcauchy
    refine ⟨L, fun n => ?_⟩
    rw [smodEq_pow_smul_top_iff]
    have h1 : f n - f (N1*n) ∈ mF ^ n := by
      have hmem := hf (hnle n)
      rw [smodEq_pow_smul_top_iff] at hmem
      exact hmem
    have h2 : f (N1*n) - L ∈ mF ^ n := by
      have hmem := hL n
      rw [smodEq_pow_smul_top_iff] at hmem
      exact (Ideal.pow_right_mono hJFle n) hmem
    have heq : f n - L = (f n - f (N1*n)) + (f (N1*n) - L) := by ring
    rw [heq]
    exact (mF^n).add_mem h1 h2
  exact IsAdicComplete.mk

private lemma decompose_complete_finite_into_product
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (hcomplete : IsAdicComplete
      (Ideal.map (algebraMap R S) (@IsLocalRing.maximalIdeal R _ hR.isLocal)) S) :
    ∃ (m : ℕ) (T : Fin m → Type v) (_ : ∀ i, CommRing (T i)),
      (∀ i, IsNoetherianCompleteLocalRing (T i)) ∧
      Nonempty (S ≃+* (Π i, T i)) := by
  have : IsNoetherianRing R := hR.isNoetherian
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  obtain ⟨k, e, hcoi, hloc⟩ := S3a_exists_coi_with_local_factors hR hcomplete
  refine ⟨k, fun i => S ⧸ Ideal.span {1 - e i}, fun i => inferInstance, ?_, ?_⟩
  · intro i
    have := hloc i
    have : IsNoetherianRing (S ⧸ Ideal.span {1 - e i}) := inferInstance
    have hcfac : IsAdicComplete (IsLocalRing.maximalIdeal (S ⧸ Ideal.span {1 - e i}))
        (S ⧸ Ideal.span {1 - e i}) := S3b_factor_isAdicComplete hR e i
    exact ⟨inferInstance, hloc i, hcfac⟩
  · exact ⟨RingEquiv.ofBijective _ hcoi.bijective_pi⟩

/-- If `R` is a Noetherian complete local ring and `R → S` is a finite ring map, then `S` is a
finite product of Noetherian complete local rings: there exist finitely many rings
`T 0, ..., T (m-1)`, each a Noetherian complete local ring, together with a ring isomorphism
`S ≃+* Π i, T i`. -/
@[stacks 0325,
  ega "0 22.3.1" "special case",
  ega "IV 18.5.9" "(ii), special case",
  ega "IV 5.4.3" "special case",
  sga "1 III 1.4" "special case",
  sga "3 VIIB 0.1.1" "special case",
  sga "3 XV 1.5" "partial",
  sga "3 XV 3.9",
  sga "4 VIII 4.1" "(i), special case"]
theorem finite_isProduct_isNoetherianCompleteLocalRing
    {R : Type u} [CommRing R] (hR : IsNoetherianCompleteLocalRing R)
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (m : ℕ) (T : Fin m → Type v) (_ : ∀ i, CommRing (T i)),
      (∀ i, IsNoetherianCompleteLocalRing (T i)) ∧
      Nonempty (S ≃+* (Π i, T i)) := by
  exact decompose_complete_finite_into_product hR (finite_isAdicComplete_of_complete hR)
