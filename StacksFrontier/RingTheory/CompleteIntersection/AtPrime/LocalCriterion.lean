module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Spectrum.Prime.Codimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complete intersection criterion at a prime: the local criterion

The local half of the complete intersection criterion: the conormal module of a weakly regular
sequence is free of rank its length (`Ideal.free_and_finrank_cotangent_of_isWeaklyRegular`); a
proper ideal of a Noetherian local ring and its conormal module need the same number of generators
(`Ideal.spanFinrank_top_cotangent_eq_spanFinrank`); the four equivalent conditions over a
Cohen-Macaulay local ring (`Module.IsMaximalCohenMacaulay.tfae_spanFinrank_cotangent`) and the
closing assertion (`Module.IsMaximalCohenMacaulay.isRegular_of_sup_mul_eq`); the dimension of the
quotient of a localization (`ringKrullDim_quotient_map_ker_eq_height`); and items (2) and (5) of
the criterion (`Algebra.Generators.spanFinrank_ker_map_le_iff_exists_isRegular`).

See `StacksFrontier.RingTheory.CompleteIntersection.AtPrime` for the overview and references.
-/

@[expose] public section

universe u v w

open IsLocalRing RingTheory.Sequence

/-! ### Relations among a weakly regular sequence -/

variable {A : Type*} [CommRing A]

private theorem getD_mem_ofList (l : List A) {i : ℕ} (h : i < l.length) :
    l.getD i 0 ∈ Ideal.ofList l := by
  rw [List.getD_eq_getElem l 0 h]
  exact Ideal.subset_span (List.getElem_mem h)

private theorem exists_sum_eq_of_mem_ofList {A : Type*} [CommRing A] (l : List A) {x : A}
    (hx : x ∈ Ideal.ofList l) :
    ∃ d : ℕ → A, x = ∑ i ∈ Finset.range l.length, d i * l.getD i 0 := by
  classical
  have hset : {y | y ∈ l} = Set.range (fun i : Fin l.length => l.get i) := by
    ext y
    simp [List.mem_iff_get]
  rw [Ideal.ofList, hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx
  refine ⟨fun i ↦ (List.ofFn c).getD i 0, ?_⟩
  rw [← hc, ← Fin.sum_univ_eq_sum_range
    (fun i ↦ (List.ofFn c).getD i 0 * l.getD i 0) l.length]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, List.getD_eq_getElem l 0 i.2,
    List.getD_eq_getElem _ 0 (by simp), List.getElem_ofFn]
  rfl

private theorem sum_range_mem_ofList {A : Type*} [CommRing A] (l : List A) (d : ℕ → A) :
    ∑ i ∈ Finset.range l.length, d i * l.getD i 0 ∈ Ideal.ofList l :=
  Submodule.sum_mem _ fun _i hi ↦
    Ideal.mul_mem_left _ _ (getD_mem_ofList l (Finset.mem_range.1 hi))

/-- **The relations among a weakly regular sequence are trivial modulo the ideal it generates.**
If `r₀, …, r_{n-1}` is a weakly regular sequence in `A` and `∑ aᵢ rᵢ = 0`, then every coefficient
`aᵢ` already lies in the ideal `(r₀, …, r_{n-1})`. -/
private theorem mem_ofList_of_sum_eq_zero {A : Type*} [CommRing A] :
    ∀ (rs : List A), IsWeaklyRegular A rs →
      ∀ (a : ℕ → A), ∑ i ∈ Finset.range rs.length, a i * rs.getD i 0 = 0 →
        ∀ i < rs.length, a i ∈ Ideal.ofList rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro _ a _ i hi; simp at hi
  | append_singleton init g ih =>
    intro hw a hsum i hi
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hw
    obtain ⟨hinit, hg⟩ := hw
    have hlen : (init ++ [g]).length = init.length + 1 := by simp
    have hget : ∀ j, j < init.length → (init ++ [g]).getD j 0 = init.getD j 0 := by
      intro j hj
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getD_eq_getElem _ 0 hj,
        List.getElem_append_left hj]
    have hgetlast : (init ++ [g]).getD init.length 0 = g := by
      rw [List.getD_eq_getElem _ 0 (by simp)]; simp
    rw [hlen, Finset.sum_range_succ, hgetlast] at hsum
    have heq : ∑ j ∈ Finset.range init.length, a j * (init ++ [g]).getD j 0
        = ∑ j ∈ Finset.range init.length, a j * init.getD j 0 :=
      Finset.sum_congr rfl fun j hj ↦ by rw [hget j (Finset.mem_range.1 hj)]
    rw [heq] at hsum
    have hmemg : a init.length * g ∈ Ideal.ofList init := by
      have hrw : a init.length * g = -∑ j ∈ Finset.range init.length, a j * init.getD j 0 := by
        linear_combination hsum
      rw [hrw]
      exact neg_mem (sum_range_mem_ofList init a)
    have hpeq : (Ideal.ofList init : Ideal A) • (⊤ : Submodule A A)
        = (Ideal.ofList init).restrictScalars A := by simp
    have hb : a init.length ∈ Ideal.ofList init := by
      have h0 : g • (Ideal.ofList init • (⊤ : Submodule A A)).mkQ (a init.length) = 0 := by
        rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hpeq]
        rw [smul_eq_mul, mul_comm]
        exact hmemg
      have h1 : (Ideal.ofList init • (⊤ : Submodule A A)).mkQ (a init.length) = 0 := by
        refine hg ?_
        show g • _ = g • (0 : A ⧸ (Ideal.ofList init • (⊤ : Submodule A A)))
        rw [smul_zero]
        exact h0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hpeq] at h1
      exact h1
    obtain ⟨d, hd⟩ := exists_sum_eq_of_mem_ofList init hb
    have hsum2 : ∑ j ∈ Finset.range init.length, (a j + g * d j) * init.getD j 0 = 0 := by
      have : ∑ j ∈ Finset.range init.length, (a j + g * d j) * init.getD j 0
          = (∑ j ∈ Finset.range init.length, a j * init.getD j 0)
            + g * ∑ j ∈ Finset.range init.length, d j * init.getD j 0 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [this, ← hd]
      linear_combination hsum
    have key := ih hinit (fun j ↦ a j + g * d j) hsum2
    have hle : Ideal.ofList init ≤ Ideal.ofList (init ++ [g]) := by
      rw [Ideal.ofList_append]; exact le_sup_left
    have hgmem : g ∈ Ideal.ofList (init ++ [g]) := Ideal.subset_span (by simp)
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · have h2 := key i h
      have : a i = (a i + g * d i) - g * d i := by ring
      rw [this]
      exact sub_mem (hle h2) (Ideal.mul_mem_right _ _ hgmem)
    · rw [h]; exact hle hb

section Conormal

variable (rs : List A)

/-- The `i`-th member of `rs`, as an element of the ideal it generates. -/
private def crsGen (i : Fin rs.length) : (Ideal.ofList rs) :=
  ⟨rs[(i : ℕ)], Ideal.subset_span (List.getElem_mem i.2)⟩

/-- The surjection `Aⁿ → (r₀, …, r_{n-1})` given by the sequence. -/
private noncomputable def crsPsi : (Fin rs.length → A) →ₗ[A] (Ideal.ofList rs) :=
  Fintype.linearCombination A (crsGen rs)

private theorem crsPsi_apply_coe (a : Fin rs.length → A) :
    ((crsPsi rs a : Ideal.ofList rs) : A) = ∑ i, a i * rs[(i : ℕ)] := by
  rw [crsPsi, Fintype.linearCombination_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ by simp [crsGen, smul_eq_mul]

private theorem crsPsi_surjective : Function.Surjective (crsPsi rs) := by
  intro y
  obtain ⟨d, hd⟩ := exists_sum_eq_of_mem_ofList rs y.2
  refine ⟨fun i ↦ d (i : ℕ), Subtype.ext ?_⟩
  rw [crsPsi_apply_coe, hd, ← Fin.sum_univ_eq_sum_range (fun i ↦ d i * rs.getD i 0) rs.length]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [List.getD_eq_getElem rs 0 i.2]


private theorem mem_of_mem_smul_top_pi {J : Ideal A} {n : ℕ} {a : Fin n → A}
    (h : a ∈ J • (⊤ : Submodule A (Fin n → A))) (i : Fin n) : a i ∈ J := by
  refine Submodule.smul_induction_on (p := fun x ↦ x i ∈ J) h ?_ ?_
  · intro r hr b _
    show r • b i ∈ J
    rw [smul_eq_mul]
    exact J.mul_mem_right _ hr
  · intro x y hx hy
    show x i + y i ∈ J
    exact add_mem hx hy

private theorem mem_smul_top_pi_of_forall {J : Ideal A} {n : ℕ} {a : Fin n → A}
    (h : ∀ i, a i ∈ J) : a ∈ J • (⊤ : Submodule A (Fin n → A)) := by
  have ha : a = ∑ i, a i • (Pi.single i 1 : Fin n → A) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ha]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (h i) Submodule.mem_top

private theorem crsKer_le (hrs : IsWeaklyRegular A rs) :
    LinearMap.ker (crsPsi rs) ≤ Ideal.ofList rs • (⊤ : Submodule A (Fin rs.length → A)) := by
  classical
  intro a ha
  refine mem_smul_top_pi_of_forall fun i ↦ ?_
  have hb : ∀ j : Fin rs.length, (List.ofFn a).getD (j : ℕ) 0 = a j := fun j ↦ by
    rw [List.getD_eq_getElem _ 0 (by simp), List.getElem_ofFn]
  have h0 : ∑ j ∈ Finset.range rs.length,
      (List.ofFn a).getD j 0 * rs.getD j 0 = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (List.ofFn a).getD j 0 * rs.getD j 0) rs.length]
    rw [Finset.sum_congr rfl fun j _ ↦ by rw [hb j, List.getD_eq_getElem rs 0 j.2],
      ← crsPsi_apply_coe]
    rw [LinearMap.mem_ker] at ha
    rw [ha]
    rfl
  have hmem := mem_ofList_of_sum_eq_zero rs hrs _ h0 (i : ℕ) i.2
  rwa [hb i] at hmem

/-- **The conormal module of a weakly regular sequence is free of rank its length.**
If `rs = r₀, …, r_{n-1}` is a weakly regular sequence in `A` generating a proper ideal `J`, then
`J/J²` is a free `A/J`-module of rank `n`. -/
@[sga "3 III 4.6.1" "I/I² is free of rank d",
  sga "4½ Cycle 2.2.1" "partial",
  sga "7 VI 4.14" "partial"]
theorem Ideal.free_and_finrank_cotangent_of_isWeaklyRegular (hrs : IsWeaklyRegular A rs)
    (hne : Ideal.ofList rs ≠ ⊤) :
    Module.Free (A ⧸ Ideal.ofList rs) (Ideal.ofList rs).Cotangent ∧
      Module.finrank (A ⧸ Ideal.ofList rs) (Ideal.ofList rs).Cotangent = rs.length := by
  classical
  have hnt : Nontrivial (A ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr hne
  set J : Ideal A := Ideal.ofList rs with hJ
  set w : Fin rs.length → J.Cotangent := fun i ↦ J.toCotangent (crsGen rs i) with hw
  set φ : (Fin rs.length → (A ⧸ J)) →ₗ[A ⧸ J] J.Cotangent :=
    Fintype.linearCombination (A ⧸ J) w with hφ
  have hker : LinearMap.ker J.toCotangent = (J • ⊤ : Submodule A J) := Submodule.ker_mkQ _
  have hcomp : ∀ a : Fin rs.length → A,
      J.toCotangent (crsPsi rs a) = ∑ i, a i • w i := by
    intro a
    rw [crsPsi, Fintype.linearCombination_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hw]
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, rfl⟩ := J.toCotangent_surjective x
    obtain ⟨a, rfl⟩ := crsPsi_surjective rs y
    refine ⟨fun i ↦ Ideal.Quotient.mk J (a i), ?_⟩
    rw [hφ, Fintype.linearCombination_apply, hcomp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker, hφ, Fintype.linearCombination_apply] at hc
    choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := J) (c i)
    have hca : ∑ i, c i • w i = ∑ i, a i • w i :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [← ha i, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    rw [hca, ← hcomp] at hc
    have hmem : crsPsi rs a ∈ (J • ⊤ : Submodule A J) := by
      rw [← hker, LinearMap.mem_ker]; exact hc
    have hmap : Submodule.map (crsPsi rs) (J • (⊤ : Submodule A (Fin rs.length → A)))
        = (J • ⊤ : Submodule A J) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (crsPsi_surjective rs)]
    rw [← hmap] at hmem
    obtain ⟨b, hbmem, hbeq⟩ := hmem
    have hsub : a - b ∈ J • (⊤ : Submodule A (Fin rs.length → A)) := by
      refine crsKer_le rs hrs ?_
      rw [LinearMap.mem_ker, map_sub, hbeq, sub_self]
    have hamem : a ∈ J • (⊤ : Submodule A (Fin rs.length → A)) := by
      have : a = (a - b) + b := by ring_nf
      rw [this]; exact add_mem hsub hbmem
    funext i
    show c i = 0
    rw [← ha i, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_mem_smul_top_pi hamem i
  refine ⟨Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩), ?_⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi,
    Fintype.card_fin]

end Conormal

/-! ### Minimal generators of an ideal and of its conormal module -/

/-- **Over a Noetherian local ring, a proper ideal and its conormal module need the same number of
generators.** For `I ≠ ⊤`, the minimal number of generators of `I/I²` as an `A/I`-module equals the
minimal number of generators of `I` as an ideal of `A`.

Both sides are Nakayama's lemma: the minimal number of generators of `I` is the dimension of
`I/𝔪I`, and `I² ⊆ 𝔪I` because `I ⊆ 𝔪`, so reducing `I/I²` modulo the maximal ideal of `A/I` gives
`I/𝔪I` again. -/
theorem Ideal.spanFinrank_top_cotangent_eq_spanFinrank {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    (⊤ : Submodule (A ⧸ I) I.Cotangent).spanFinrank = I.spanFinrank := by
  classical
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  have hfgI : (⊤ : Submodule A I).FG := IsNoetherian.noetherian _
  have hjac : I ≤ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hI
  have hker : LinearMap.ker I.toCotangent = (I • ⊤ : Submodule A I) := Submodule.ker_mkQ _
  have key : ∀ u : Set I, Submodule.span (A ⧸ I) (I.toCotangent '' u) = ⊤ ↔
      Submodule.span A u = ⊤ := by
    intro u
    rw [← Submodule.restrictScalars_eq_top_iff A (A ⧸ I), Submodule.restrictScalars_span A _ hsurj,
      ← Submodule.map_span, LinearMap.map_eq_top_iff I.toCotangent_range, hker]
    constructor
    · intro h
      exact le_antisymm le_top
        (Submodule.le_of_le_smul_of_le_jacobson_bot hfgI hjac h.ge)
    · intro h; rw [h]; simp
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hcard, hspan⟩ := hfgI.exists_span_finset_card_eq_spanFinrank
    have h1 : Submodule.span (A ⧸ I) (I.toCotangent '' (u : Set I)) = ⊤ := (key _).2 hspan
    calc (⊤ : Submodule (A ⧸ I) I.Cotangent).spanFinrank
        = (Submodule.span (A ⧸ I) (I.toCotangent '' (u : Set I))).spanFinrank := by rw [h1]
      _ ≤ (I.toCotangent '' (u : Set I)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (u.finite_toSet.image _)
      _ ≤ (u : Set I).ncard := Set.ncard_image_le u.finite_toSet
      _ = I.spanFinrank := by
          rw [Set.ncard_coe_finset, hcard, Submodule.spanFinrank_top]
  · have hfin : Module.Finite A I.Cotangent :=
      Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
    have hfin' : Module.Finite (A ⧸ I) I.Cotangent :=
      Module.Finite.of_restrictScalars_finite A _ _
    obtain ⟨t, hcard, hspan⟩ :=
      (Module.Finite.fg_top (R := A ⧸ I) (M := I.Cotangent)).exists_span_finset_card_eq_spanFinrank
    set f := Function.surjInv I.toCotangent_surjective with hf
    have himg : I.toCotangent '' (f '' (t : Set I.Cotangent)) = (t : Set I.Cotangent) := by
      rw [Set.image_image]
      simp [hf, Function.surjInv_eq]
    have h1 : Submodule.span A (f '' (t : Set I.Cotangent)) = ⊤ := (key _).1 (by rw [himg, hspan])
    calc I.spanFinrank = (⊤ : Submodule A I).spanFinrank := (Submodule.spanFinrank_top I).symm
      _ = (Submodule.span A (f '' (t : Set I.Cotangent))).spanFinrank := by rw [h1]
      _ ≤ (f '' (t : Set I.Cotangent)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (t.finite_toSet.image _)
      _ ≤ (t : Set I.Cotangent).ncard := Set.ncard_image_le t.finite_toSet
      _ = (⊤ : Submodule (A ⧸ I) I.Cotangent).spanFinrank := by
          rw [Set.ncard_coe_finset, hcard]




/-! ### Dimension bookkeeping in `WithBot ℕ∞` -/

/-- The Krull dimension of a Noetherian local ring is a natural number. -/
private theorem exists_natCast_ringKrullDim (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1
    (Ideal.height_ne_top_of_isPrime (I := maximalIdeal A))
  refine ⟨d, ?_⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
  rfl

private theorem natCast_le_of_add_le_add {d : WithBot ℕ∞} {m n : ℕ}
    (hd : ∃ e : ℕ, d = (e : WithBot ℕ∞)) (h : d + (m : WithBot ℕ∞) ≤ d + (n : WithBot ℕ∞)) :
    m ≤ n := by
  obtain ⟨e, rfl⟩ := hd
  have h' : ((e + m : ℕ) : WithBot ℕ∞) ≤ ((e + n : ℕ) : WithBot ℕ∞) := by push_cast; exact h
  rw [show ((e + m : ℕ) : WithBot ℕ∞) = (((e + m : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast,
    show ((e + n : ℕ) : WithBot ℕ∞) = (((e + n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast,
    WithBot.coe_le_coe, Nat.cast_le] at h'
  omega

private theorem natCast_eq_of_add_eq_add {d : WithBot ℕ∞} {m n : ℕ}
    (hd : ∃ e : ℕ, d = (e : WithBot ℕ∞)) (h : d + (m : WithBot ℕ∞) = d + (n : WithBot ℕ∞)) :
    m = n :=
  le_antisymm (natCast_le_of_add_le_add hd h.le) (natCast_le_of_add_le_add hd h.ge)

/-! ### The local criterion -/

/-- **A list of `c` elements generating a proper ideal `I` with `dim (A/I) + c = dim A` in a
Cohen-Macaulay local ring is a regular sequence.** -/
theorem Module.IsMaximalCohenMacaulay.isRegular_of_ofList_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Module.IsMaximalCohenMacaulay A A) {I : Ideal A} (hI : I ≠ ⊤) {c : ℕ}
    (hc : ringKrullDim (A ⧸ I) + (c : WithBot ℕ∞) = ringKrullDim A)
    {rs : List A} (hrs : Ideal.ofList rs = I) (hlen : rs.length = c) : IsRegular A rs := by
  refine ((hA.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim rs ?_).1).mpr ?_
  · intro x hx
    exact IsLocalRing.le_maximalIdeal hI (hrs ▸ Ideal.subset_span hx)
  · rw [hrs, hlen]; exact hc

/-- **A regular sequence generating a proper ideal `I` with `dim (A/I) + c = dim A` in a local ring
has length `c`.** -/
theorem RingTheory.Sequence.IsRegular.length_eq_of_ofList_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {I : Ideal A} {c : ℕ}
    (hc : ringKrullDim (A ⧸ I) + (c : WithBot ℕ∞) = ringKrullDim A)
    {rs : List A} (hrs : IsRegular A rs) (hrsI : Ideal.ofList rs = I) : rs.length = c := by
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro h
    refine hrs.top_ne_smul ?_
    have hsm : Ideal.ofList rs • (⊤ : Submodule A A)
        = (Ideal.ofList rs).restrictScalars A := by simp
    rw [hsm, h]
    rfl
  have hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (hrsI ▸ hne)
  have hlq : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have h1 := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hrs
  rw [hrsI, ← hc] at h1
  exact natCast_eq_of_add_eq_add (exists_natCast_ringKrullDim (A ⧸ I)) h1

/-- **The local form of the complete intersection criterion.**

Let `(A, 𝔪)` be a Noetherian local Cohen-Macaulay ring and let `I ⊆ A` be a proper ideal whose
quotient has dimension `dim A - c`, written additively as `dim (A/I) + c = dim A`. Then the
following are equivalent: `I` is generated by `c` elements; the conormal module `I/I²` is
generated by `c` elements over `A/I`; `I/I²` is free of rank `c` over `A/I`; and `I` is generated
by a regular sequence. -/
@[sga "3 III 4.6.1" "I/I² is free of rank d"]
theorem Module.IsMaximalCohenMacaulay.tfae_spanFinrank_cotangent
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Module.IsMaximalCohenMacaulay A A) {I : Ideal A} (hI : I ≠ ⊤) (c : ℕ)
    (hc : ringKrullDim (A ⧸ I) + (c : WithBot ℕ∞) = ringKrullDim A) :
    List.TFAE
      [I.spanFinrank ≤ c,
        (⊤ : Submodule (A ⧸ I) I.Cotangent).spanFinrank ≤ c,
        Module.Free (A ⧸ I) I.Cotangent ∧ Module.finrank (A ⧸ I) I.Cotangent = c,
        ∃ rs : List A, IsRegular A rs ∧ Ideal.ofList rs = I] := by
  classical
  have hIm : I ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hI
  have hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hlq : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hdAI : ∃ e : ℕ, ringKrullDim (A ⧸ I) = (e : WithBot ℕ∞) :=
    exists_natCast_ringKrullDim (A ⧸ I)
  have hge : c ≤ I.spanFinrank := by
    have h1 : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (I.spanFinrank : WithBot ℕ∞) :=
      ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
        (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal]; exact hIm)
    rw [← hc] at h1
    exact natCast_le_of_add_le_add hdAI h1
  tfae_have 1 → 4 := by
    intro h
    obtain ⟨s, hcard, hspan⟩ :=
      (IsNoetherian.noetherian I).exists_span_finset_card_eq_spanFinrank
    have hofList : Ideal.ofList s.toList = I := by
      rw [Ideal.ofList, show {x | x ∈ s.toList} = (s : Set A) by ext x; simp]
      exact hspan
    have hlen : s.toList.length = c := by
      rw [Finset.length_toList, hcard]
      exact le_antisymm h hge
    exact ⟨s.toList, hA.isRegular_of_ofList_eq hI hc hofList hlen, hofList⟩
  tfae_have 4 → 3 := by
    rintro ⟨rs, hrs, hrsI⟩
    have hne : Ideal.ofList rs ≠ ⊤ := by rw [hrsI]; exact hI
    have hfree := Ideal.free_and_finrank_cotangent_of_isWeaklyRegular rs hrs.toIsWeaklyRegular hne
    rw [hrsI] at hfree
    exact ⟨hfree.1, hfree.2.trans (hrs.length_eq_of_ofList_eq hc hrsI)⟩
  tfae_have 3 → 2 := by
    rintro ⟨hfree, hrank⟩
    have := hfree
    rw [← Module.finrank_eq_spanFinrank_of_free (R := A ⧸ I) (M := I.Cotangent), hrank]
  tfae_have 2 → 1 := by
    intro h
    rwa [Ideal.spanFinrank_top_cotangent_eq_spanFinrank I hI] at h
  tfae_finish


/-- **The closing assertion of the complete intersection criterion, in local form.** In a
Cohen-Macaulay local ring `(A, 𝔪)`, if `I` is a proper ideal with `dim (A/I) + c = dim A`, then any
`c` elements of `I` generating `I/𝔪I` form a regular sequence. -/
theorem Module.IsMaximalCohenMacaulay.isRegular_of_sup_mul_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Module.IsMaximalCohenMacaulay A A) {I : Ideal A} (hI : I ≠ ⊤) {c : ℕ}
    (hc : ringKrullDim (A ⧸ I) + (c : WithBot ℕ∞) = ringKrullDim A)
    {rs : List A} (hlen : rs.length = c)
    (hsup : Ideal.ofList rs ⊔ maximalIdeal A * I = I) : IsRegular A rs := by
  have hjac : maximalIdeal A ≤ (⊥ : Ideal A).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top).ge
  have hle : I ≤ Ideal.ofList rs := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hjac ?_
    rw [Ideal.smul_eq_mul]
    exact hsup.ge
  exact hA.isRegular_of_ofList_eq hI hc (le_antisymm (le_trans le_sup_left hsup.le) hle) hlen


/-! ### The localization of a quotient -/

/-- **The Krull dimension of the quotient of a localization.** Let `f : R → T` be a surjection,
`q ⊆ T` a prime and `A` a localization of `R` at `q' = f⁻¹(q)`. Then `A / (ker f)·A` is a
localization of `T` at `q`, so its Krull dimension is the height of `q`. -/
theorem ringKrullDim_quotient_map_ker_eq_height
    {R : Type*} [CommRing R] {T : Type*} [CommRing T] (f : R →+* T) (hf : Function.Surjective f)
    (q : Ideal T) [q.IsPrime] (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization.AtPrime A (q.comap f)] :
    ringKrullDim (A ⧸ (RingHom.ker f).map (algebraMap R A)) = (q.height : WithBot ℕ∞) := by
  let e : R ⧸ RingHom.ker f ≃+* T := RingHom.quotientKerEquivOfSurjective hf
  let Q : Ideal (R ⧸ RingHom.ker f) := q.comap e.toRingHom
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hmemQ : ∀ x : R, Ideal.Quotient.mk (RingHom.ker f) x ∈ Q ↔ f x ∈ q := by
    intro x
    show e (Ideal.Quotient.mk (RingHom.ker f) x) ∈ q ↔ f x ∈ q
    rw [show e (Ideal.Quotient.mk (RingHom.ker f) x) = f x from
      RingHom.quotientKerEquivOfSurjective_apply_mk hf x]
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ RingHom.ker f) (q.comap f).primeCompl
      = Q.primeCompl := by
    rw [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq]
    ext y
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Ideal.Quotient.mk (RingHom.ker f) x ∉ Q
      rw [hmemQ]
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, fun hx ↦ hy ((hmemQ x).2 hx), rfl⟩
  have hloc : IsLocalization.AtPrime (A ⧸ (RingHom.ker f).map (algebraMap R A)) Q := by
    rw [IsLocalization.AtPrime, ← hsub]
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q
    (A ⧸ (RingHom.ker f).map (algebraMap R A))]
  exact congrArg _ (RingEquiv.height_comap e q)


/-! ### Items (2) and (5) -/

/-- **The equivalence of items (2) and (5), together with the closing assertion.**

Let `k` be a field, let `S = k[x_i]/I` be a presented `k`-algebra with finitely many variables, let
`q` be a prime of `S`, let `q'` be the corresponding prime of `k[x_i]`, and let `c` be the
codimension, `height q' = height q + c`. Then the ideal `I_{q'}` of `A = k[x_i]_{q'}` can be
generated by `c` elements if and only if it can be generated by a regular sequence; and any `c`
elements of `I_{q'}` generating `I_{q'}/q'I_{q'}` form a regular sequence. -/
@[stacks 00SC "The equivalence of items (2) and (5) is the first conjunct, and the closing
assertion of the lemma — that any `c` elements of `I_{𝔮'}` generating `I_{𝔮'}/𝔮'I_{𝔮'}` form a
regular sequence — is the second. The five equivalent conditions themselves are
`Algebra.Generators.tfae_isGlobalCompleteIntersection_away`, which carries this tag as well; this
declaration is on the covering set for the closing assertion."]
theorem Algebra.Generators.spanFinrank_ker_map_le_iff_exists_isRegular
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {ι : Type w} [Finite ι] (P : Algebra.Generators k S ι)
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))] :
    (Submodule.spanFinrank (P.ker.map (algebraMap P.Ring A)) ≤ c ↔
        ∃ rs : List A, IsRegular A rs ∧
          Ideal.ofList rs = P.ker.map (algebraMap P.Ring A)) ∧
      ∀ rs : List A, rs.length = c →
        Ideal.ofList rs ⊔ (q.comap (algebraMap P.Ring S)).map (algebraMap P.Ring A) *
            P.ker.map (algebraMap P.Ring A) = P.ker.map (algebraMap P.Ring A) →
          IsRegular A rs := by
  have hrl : IsRegularLocalRing A :=
    IsRegularRing.isRegularLocalRing_of_isLocalization
      (q.comap (algebraMap P.Ring S)) A
  have hA : Module.IsMaximalCohenMacaulay A A :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay A).2
  have hkerf : P.ker = RingHom.ker (algebraMap P.Ring S) := rfl
  have hdim : ringKrullDim (A ⧸ P.ker.map (algebraMap P.Ring A)) = (q.height : WithBot ℕ∞) := by
    rw [hkerf]
    exact ringKrullDim_quotient_map_ker_eq_height (algebraMap P.Ring S)
      P.algebraMap_surjective q A
  have hdimA : ringKrullDim A = ((q.comap (algebraMap P.Ring S)).height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ A
  have hI : P.ker.map (algebraMap P.Ring A) ≠ ⊤ := by
    intro h
    rw [h] at hdim
    have hsub : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim.symm (by simp)
  have hcA : ringKrullDim (A ⧸ P.ker.map (algebraMap P.Ring A))
      + (c : WithBot ℕ∞) = ringKrullDim A := by
    rw [hdim, hdimA, hc]
    push_cast
    rfl
  have hmax : (q.comap (algebraMap P.Ring S)).map (algebraMap P.Ring A) = maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (q.comap (algebraMap P.Ring S)) A
  refine ⟨?_, fun rs hlen hsup ↦ ?_⟩
  · exact ((hA.tfae_spanFinrank_cotangent hI c hcA).out 1 4)
  · rw [hmax] at hsup
    exact hA.isRegular_of_sup_mul_eq hI hcA hlen hsup

end
