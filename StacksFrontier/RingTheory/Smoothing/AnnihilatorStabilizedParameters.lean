module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Sequence.Powers
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Sequence.Regular.Permutation
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Smoothing.EssentiallySmoothEnlargement
public import StacksFrontier.RingTheory.Smoothing.OgomaKernelStabilization

/-!
# Stabilizing the annihilators of a rescaled regular system of parameters

Two rescaling results for a regular system of parameters, over the polynomial ring and over the
ring itself.

Let `P` be a Noetherian ring and `p ⊂ P` a prime with `P_p` regular local of dimension `d`, and
let `π₁, …, π_d ∈ P` map to a regular system of parameters of `P_p`. In the polynomial ring
`R = P[t₁, …, t_d]` put `γ_i = π_i t_i`. Rescaling the `π_i` by elements of `P \ p` one can
arrange that in `R ⧸ (γ₁ ^ e, …, γ_{i-1} ^ e)` the annihilator of `γ_i` agrees with the
annihilator of `γ_i ^ 2`, for every `i`.

Let now `k` be a field of characteristic `p > 0`, let `Λ` be a Noetherian `k`-algebra, let
`q ⊂ Λ` be a prime with `Λ_q` regular local of dimension `d`, let `a_1, …, a_r ∈ Λ` with
`q ^ N Λ_q ⊆ (a_1, …, a_r)Λ_q`, and let `D` be an Artinian local ring with a flat local map
`D → Λ_q/q^nΛ_q` whose image contains the reductions of the `a_j` and of parameters
`π_1, …, π_d ∈ q` lifting a regular system of parameters of `Λ_q`. Then the `π_i` may be
rescaled by elements `δ_i` of `Λ \ q` inside an essentially smooth Artinian enlargement `D'` of
`D` so that `(δ_i π_i) ^ (2N)` is an explicit combination of the `a_j` with coefficients
reducing into `D'`, the annihilators of `δ_i π_i` and of `(δ_i π_i) ^ 2` agree in
`Λ ⧸ ((δ_1 π_1) ^ e, …, (δ_{i-1} π_{i-1}) ^ e)`, and each `δ_i` reduces into `D'`.

## Main definitions

* `Stacks.Smoothing.scaledVariable`: the element `γ_i = π_i t_i` of `P[t₁, …, t_d]`.
* `Stacks.Smoothing.truncatedLocalization`: the ring `Λ_q/q^nΛ_q`.

## Main results

* `Stacks.Smoothing.exists_annihilator_scaledVariable_sq_eq`: the first statement above.
* `Stacks.Smoothing.exists_essentiallySmooth_enlargement_annihilator_sq_eq`: the second.

## Implementation notes

The engine is assembled in reusable form. `isRegular_ofFn_scaledVariable` produces the regular
sequence `γ₁, …, γ_d` in `P_p[t₁, …, t_d]` from a regular system of parameters of `P_p`;
`isSMulRegular_quotient_span_prev_pow_of_isRegular` turns a regular sequence into the
nonzerodivisor statements for the prefix powers;
`exists_mem_annihilator_sq_eq_of_isSMulRegular_localizedModule` descends an annihilator equality
from a localization at the cost of one rescaling; and
`exists_mem_pow_mul_eq_sum_of_localization_rel` clears denominators in a relation
`x ^ M = Σ_j a_j b_j` holding in a localization, producing a single `s` for which both
`μ_j = s ^ M b_j` and `(s x) ^ M = Σ_j a_j μ_j` hold.

Iterating the enlargement needs essential smoothness to be transitive, which is
`isEssentiallySmooth_comp`; the existential form of essential finite presentation used by
`IsEssentiallyOfFinitePresentation` and by `RingHom.EssentiallyOfFinitePresentation` agree in a
single universe, so Stacks 07DS applies.

## References

* [Stacks Project, Tag 07FW](https://stacks.math.columbia.edu/tag/07FW)
* [Stacks Project, Tag 07FX](https://stacks.math.columbia.edu/tag/07FX)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u

open RingTheory.Sequence

/-! ### Descending an annihilator equality from a localization -/

/-- If the image of `a` is a nonzerodivisor on `B ⧸ J B` for a localization `B` of `Λ` at `S`,
then `a` is a nonzerodivisor on the localized module `S⁻¹(Λ ⧸ J)`. -/
theorem isSMulRegular_localizedModule_quotient_of_isSMulRegular_map
    {Λ : Type*} [CommRing Λ] (S : Submonoid Λ) (B : Type*) [CommRing B] [Algebra Λ B]
    [IsLocalization S B] (J : Ideal Λ) (a : Λ)
    (h : IsSMulRegular (B ⧸ Ideal.map (algebraMap Λ B) J) (algebraMap Λ B a)) :
    IsSMulRegular (LocalizedModule S (Λ ⧸ J)) a := by
  have hJ : Submodule.localized' B S (Algebra.linearMap Λ B) J = Ideal.map (algebraMap Λ B) J :=
    Ideal.localized'_eq_map B S J
  have hquot : IsSMulRegular (B ⧸ Submodule.localized' B S (Algebra.linearMap Λ B) J) a :=
    (((Submodule.quotEquivOfEq _ _ hJ).restrictScalars Λ).isSMulRegular_congr a).mpr
      (h.of_map (algebraMap Λ B) fun m => IsScalarTower.algebraMap_smul B a m)
  exact ((IsLocalizedModule.linearEquiv S (J.toLocalizedQuotient' B S (Algebra.linearMap Λ B))
    (LocalizedModule.mkLinearMap S (Λ ⧸ J))).isSMulRegular_congr a).mp hquot

/-- Ogoma's lemma in annihilator form: if `a` is a nonzerodivisor on the localized module
`S⁻¹(Λ ⧸ J)`, then after rescaling `a` by a suitable element of `S` the annihilators of `a` and
of `a ^ 2` in `Λ ⧸ J` coincide. -/
theorem exists_mem_annihilator_sq_eq_of_isSMulRegular_localizedModule
    {Λ : Type*} [CommRing Λ] [IsNoetherianRing Λ] (S : Submonoid Λ) (J : Ideal Λ) (a : Λ)
    (h : IsSMulRegular (LocalizedModule S (Λ ⧸ J)) a) :
    ∃ s ∈ S, ∀ m : ℕ, 0 < m → ∀ x : Λ ⧸ J,
      x * Ideal.Quotient.mk J (s ^ m * a) = 0 ↔
        x * Ideal.Quotient.mk J ((s ^ m * a) ^ 2) = 0 := by
  have hker : LinearMap.ker (LinearMap.lsmul Λ (LocalizedModule S (Λ ⧸ J)) a) =
      LinearMap.ker (LinearMap.lsmul Λ (LocalizedModule S (Λ ⧸ J)) (a ^ 2)) := by
    rw [(isSMulRegular_iff_ker_lsmul_eq_bot _ _).mp h,
      (isSMulRegular_iff_ker_lsmul_eq_bot _ _).mp (h.pow 2)]
  obtain ⟨s, hs, H⟩ := ogoma_ker_eq_of_localization (M := Λ ⧸ J) S a hker
  refine ⟨s, hs, fun m hm x => ?_⟩
  have hx := SetLike.ext_iff.mp (H m hm) x
  change (s ^ m * a) • x = 0 ↔ ((s ^ m * a) ^ 2) • x = 0 at hx
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm] using hx

/-! ### Prefix powers of a regular sequence -/

/-- If `a₀, …, a_{d-1}` is a regular sequence on a ring `R` and `e > 0`, then `a_i` is a
nonzerodivisor on `R ⧸ (a₀ ^ e, …, a_{i-1} ^ e)`. -/
theorem isSMulRegular_quotient_span_prev_pow_of_isRegular
    {R : Type*} [CommRing R] {d : ℕ} (a : Fin d → R) (hreg : IsRegular R (List.ofFn a))
    {e : ℕ} (he : 0 < e) (i : Fin d) :
    IsSMulRegular (R ⧸ Ideal.span
      (Set.range fun j : Fin i.1 => a (j.castLE (Nat.le_of_lt i.2)) ^ e)) (a i) := by
  have hzip : (List.ofFn a).zipWith (· ^ ·) (List.ofFn fun _ : Fin d => e) =
      List.ofFn fun j => a j ^ e := by
    apply List.ext_getElem <;> simp
  have hpow := (isRegular_zipWith_pow_iff R (rs := List.ofFn a)
    (es := List.ofFn fun _ : Fin d => e) (by simp)
    (by intro k hk; simpa using (List.mem_ofFn.mp hk).choose_spec ▸ he)).mpr hreg
  rw [hzip] at hpow
  have hi := hpow.regular_mod_prev i.1 (by simp)
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt i.2) fun j => a j ^ e,
    Ideal.ofList_ofFn] at hi
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hi
  simp only [List.getElem_ofFn] at hi
  exact (IsSMulRegular.pow_iff he).mp hi

/-! ### The sequence `π_i t_i` in a polynomial ring -/

/-- The element `γ_i = π_i t_i` of the polynomial ring `P[t₁, …, t_d]`, for a `d`-tuple `π` of
elements of `P`. -/
noncomputable def scaledVariable {P : Type u} [CommRing P] {d : ℕ} (π : Fin d → P) (i : Fin d) :
    MvPolynomial (Fin d) P :=
  MvPolynomial.C (π i) * MvPolynomial.X i

/-- The element `scaledVariable π i` equals `C (π i) * X i`. -/
@[simp]
lemma scaledVariable_apply {P : Type u} [CommRing P] {d : ℕ} (π : Fin d → P) (i : Fin d) :
    scaledVariable π i = MvPolynomial.C (π i) * MvPolynomial.X i := rfl

/-- A tuple of `d = dim B` elements spanning the maximal ideal of a regular local ring `B` is,
in any order, a regular sequence on `B`. -/
@[ega "IV 19.7.3" "partial"]
theorem isRegular_of_perm_ofFn_of_span_eq_maximalIdeal {B : Type*} [CommRing B]
    [IsRegularLocalRing B] {d : ℕ} (a : Fin d → B)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal B)
    (hd : ringKrullDim B = d) {l : List B} (hl : l.Perm (List.ofFn a)) : IsRegular B l := by
  have hdim : (IsLocalRing.maximalIdeal B).spanFinrank = d := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)).trans hd
  have hofList : Ideal.ofList l = IsLocalRing.maximalIdeal B := by
    refine Eq.trans (congrArg Ideal.span (Set.ext fun x => ?_)) ((Ideal.ofList_ofFn a).trans hspan)
    exact hl.mem_iff
  exact ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    B).1 l hofList (by rw [hl.length_eq, List.length_ofFn, hdim])).1

/-- **Stacks 07DW for a regular system of parameters.** If `a₀, …, a_{d-1}` span the maximal
ideal of a regular local ring `B` of dimension `d`, then `a₀ t₀, …, a_{d-1} t_{d-1}` is a
regular sequence on the polynomial ring `B[t₀, …, t_{d-1}]`. -/
theorem isRegular_ofFn_scaledVariable {B : Type u} [CommRing B] [IsRegularLocalRing B] {d : ℕ}
    (a : Fin d → B) (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal B)
    (hd : ringKrullDim B = d) :
    IsRegular (MvPolynomial (Fin d) B) (List.ofFn (scaledVariable a)) := by
  classical
  set fs : List B := List.ofFn a with hfs
  have hlen : fs.length = d := List.length_ofFn
  have hproper : Ideal.span {x | x ∈ fs} ≠ ⊤ := by
    have h : Ideal.ofList fs = IsLocalRing.maximalIdeal B := (Ideal.ofList_ofFn a).trans hspan
    rw [show Ideal.span {x | x ∈ fs} = Ideal.ofList fs from rfl, h]
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  -- Stacks 07DW turns the permutation-invariant regularity of `a` into regularity of `polySeq`.
  have h3 : IsRegular (MvPolynomial (Fin fs.length) B) (polySeq fs) :=
    ((tfae_isRegular_perm_sublist_polySeq fs hproper).out 1 3).mp fun l hl =>
      isRegular_of_perm_ofFn_of_span_eq_maximalIdeal a hspan hd hl
  -- Transport along the renaming `Fin fs.length ≃ Fin d`.
  set φ : MvPolynomial (Fin fs.length) B ≃+* MvPolynomial (Fin d) B :=
    (MvPolynomial.renameEquiv B (finCongr hlen)).toRingEquiv with hφ
  have hcongr : IsRegular (MvPolynomial (Fin d) B) ((polySeq fs).map φ) := by
    refine (AddEquiv.isRegular_congr (e := φ.toAddEquiv)
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => ?_))).mp h3
    change φ (r * x) = φ r * φ x
    exact map_mul φ r x
  have himage : (polySeq fs).map φ = List.ofFn (scaledVariable a) := by
    refine List.ext_getElem (by simp [polySeq, hlen]) fun k h1 h2 => ?_
    simp only [List.getElem_map, polySeq, List.getElem_ofFn] at *
    simp only [hφ, scaledVariable, List.get_eq_getElem, MvPolynomial.renameEquiv_apply,
      AlgEquiv.coe_toRingEquiv, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
      finCongr_apply, Fin.cast_mk]
    simp [hfs]
  rwa [himage] at hcongr

/-! ### Stabilizing the annihilators -/

/-- Updating a tuple at `t` does not change its entries before position `t`. -/
private theorem update_castLE_of_le {X : Type*} {d : ℕ} (f : Fin d → X) (t : Fin d) (v : X)
    (l : Fin d) (hl : l.1 ≤ t.1) (j : Fin l.1) :
    Function.update f t v (j.castLE (Nat.le_of_lt l.2)) = f (j.castLE (Nat.le_of_lt l.2)) :=
  Function.update_of_ne (fun h => by have := congrArg Fin.val h; simp at this; omega) _ _

/-- Ogoma's lemma for a tuple `ρ` in `Λ` whose image in a localization `B` of `Λ` at `S` is a
regular sequence: `ρ_i` may be rescaled by a power of a single `s ∈ S` so that the annihilators of
the result and of its square agree in `Λ ⧸ (ρ_0 ^ e, …, ρ_{i-1} ^ e)`. -/
private theorem exists_mem_annihilator_sq_eq_of_isRegular_map {Λ : Type*} [CommRing Λ]
    [IsNoetherianRing Λ] (S : Submonoid Λ) (B : Type*) [CommRing B] [Algebra Λ B]
    [IsLocalization S B] {d : ℕ} (ρ : Fin d → Λ)
    (hreg : IsRegular B (List.ofFn fun l => algebraMap Λ B (ρ l))) {e : ℕ} (he : 0 < e)
    (i : Fin d) :
    ∃ s ∈ S, ∀ m : ℕ, 0 < m →
      ∀ x : Λ ⧸ Ideal.span (Set.range fun j : Fin i.1 =>
          ρ (j.castLE (Nat.le_of_lt i.2)) ^ e),
        x * Ideal.Quotient.mk _ (s ^ m * ρ i) = 0 ↔
          x * Ideal.Quotient.mk _ ((s ^ m * ρ i) ^ 2) = 0 := by
  refine exists_mem_annihilator_sq_eq_of_isSMulRegular_localizedModule S _ _ ?_
  refine isSMulRegular_localizedModule_quotient_of_isSMulRegular_map S B _ _ ?_
  have hJ : Ideal.map (algebraMap Λ B) (Ideal.span
        (Set.range fun j : Fin i.1 => ρ (j.castLE (Nat.le_of_lt i.2)) ^ e)) =
      Ideal.span (Set.range fun j : Fin i.1 =>
        algebraMap Λ B (ρ (j.castLE (Nat.le_of_lt i.2))) ^ e) := by
    simp only [Ideal.map_span, ← Set.range_comp, Function.comp_def, map_pow]
  rw [hJ]
  exact isSMulRegular_quotient_span_prev_pow_of_isRegular _ hreg he i

/-- **Stacks 07FW.** Let `P` be a Noetherian ring, let `p ⊂ P` be a prime such that `P_p` is a
regular local ring of dimension `d`, and let `π₁, …, π_d ∈ P` map to a regular system of
parameters of `P_p`. For every `e > 0` the `π_i` may be rescaled by elements of `P \ p`, which
leaves them a regular system of parameters, so that in `R ⧸ (γ₁ ^ e, …, γ_{i-1} ^ e)` the
annihilator of `γ_i` is the annihilator of `γ_i ^ 2`, where `R = P[t₁, …, t_d]` and
`γ_i = π_i t_i`. -/
@[stacks 07FW "the source's `R = k[y_1, …, y_m]` is an arbitrary Noetherian ring `P`, and the \
data of (07FU) — the lifts of a regular system of parameters of `P_p` — are the hypotheses on \
`π`; `γ_i = π_i t_i` is `scaledVariable π i`"]
theorem exists_annihilator_scaledVariable_sq_eq {P : Type u} [CommRing P] [IsNoetherianRing P]
    (p : Ideal P) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] {d : ℕ}
    (hd : ringKrullDim (Localization.AtPrime p) = d) (π : Fin d → P)
    (hspan : Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime p) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p))
    {e : ℕ} (he : 0 < e) :
    ∃ π' : Fin d → P, (∀ i, ∃ s ∈ p.primeCompl, π' i = s * π i) ∧
      Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime p) (π' i)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      ∀ i : Fin d, ∀ x : MvPolynomial (Fin d) P ⧸ Ideal.span (Set.range fun j : Fin i.1 =>
          scaledVariable π' (j.castLE (Nat.le_of_lt i.2)) ^ e),
        x * Ideal.Quotient.mk _ (scaledVariable π' i) = 0 ↔
          x * Ideal.Quotient.mk _ (scaledVariable π' i ^ 2) = 0 := by
  classical
  set B := Localization.AtPrime p with hB
  set f := algebraMap P B with hf
  set R := MvPolynomial (Fin d) P with hR
  let instAlg : Algebra R (MvPolynomial (Fin d) B) := MvPolynomial.algebraMvPolynomial
  have instLoc : IsLocalization (p.primeCompl.map (MvPolynomial.C (σ := Fin d)))
      (MvPolynomial (Fin d) B) := MvPolynomial.isLocalization p.primeCompl B
  set T : Submonoid R := p.primeCompl.map (MvPolynomial.C (σ := Fin d)) with hT
  -- The structure map `R → B[t]` sends `γ_i` built from `π` to `γ_i` built from `f ∘ π`.
  have hmapC (x : P) : algebraMap R (MvPolynomial (Fin d) B) (MvPolynomial.C x) =
      MvPolynomial.C (f x) := by
    change MvPolynomial.map (algebraMap P B) (MvPolynomial.C x) = _
    simp [hf]
  have hmapX (i : Fin d) : algebraMap R (MvPolynomial (Fin d) B) (MvPolynomial.X i) =
      MvPolynomial.X i := by
    change MvPolynomial.map (algebraMap P B) (MvPolynomial.X i) = _
    simp
  have hmapγ (ρ : Fin d → P) (i : Fin d) :
      algebraMap R (MvPolynomial (Fin d) B) (scaledVariable ρ i) =
        scaledVariable (fun l => f (ρ l)) i := by
    simp only [scaledVariable, map_mul, hmapC, hmapX]
  -- Install the annihilator condition for the first `k` indices, by induction on `k`.
  have H : ∀ k ≤ d, ∃ π' : Fin d → P, (∀ i, ∃ s ∈ p.primeCompl, π' i = s * π i) ∧
      Ideal.span (Set.range fun i => f (π' i)) = IsLocalRing.maximalIdeal B ∧
      (∀ i : Fin d, i.1 < k → ∀ x : R ⧸ Ideal.span (Set.range fun j : Fin i.1 =>
          scaledVariable π' (j.castLE (Nat.le_of_lt i.2)) ^ e),
        x * Ideal.Quotient.mk _ (scaledVariable π' i) = 0 ↔
          x * Ideal.Quotient.mk _ (scaledVariable π' i ^ 2) = 0) := by
    intro k
    induction k with
    | zero =>
      exact fun _ => ⟨π, fun i => ⟨1, p.primeCompl.one_mem, (one_mul _).symm⟩, hspan,
        fun i hi => (Nat.not_lt_zero _ hi).elim⟩
    | succ k ih =>
      intro hk
      obtain ⟨π', hrescale, hspan', hann⟩ := ih (by omega)
      set t : Fin d := ⟨k, by omega⟩
      have htval : (t : ℕ) = k := rfl
      -- `γ_t` is a nonzerodivisor on `B[t] ⧸ J B[t]`, hence Ogoma's lemma applies.
      have hregB : IsRegular (MvPolynomial (Fin d) B)
          (List.ofFn fun l => algebraMap R (MvPolynomial (Fin d) B) (scaledVariable π' l)) := by
        simp only [hmapγ]
        exact isRegular_ofFn_scaledVariable _ hspan' hd
      obtain ⟨s, hsT, hsa⟩ := exists_mem_annihilator_sq_eq_of_isRegular_map T
        (MvPolynomial (Fin d) B) (scaledVariable π') hregB he t
      obtain ⟨s₀, hs₀, hs₀eq⟩ := hsT
      -- Rescaling `π'_t` by `s₀` turns `s * γ_t` into the new `γ_t`.
      set π'' := Function.update π' t (s₀ * π' t) with hπ''
      have hpres (j : Fin d) (hj : j ≠ t) : π'' j = π' j := by simp [hπ'', hj]
      have hγt : scaledVariable π'' t = s ^ 1 * scaledVariable π' t := by
        simp only [hπ'', Function.update_self, scaledVariable_apply, ← hs₀eq, map_mul, pow_one]
        ring
      have hprefix (i : Fin d) (hi : i.1 ≤ k) :
          (fun j : Fin i.1 => scaledVariable π'' (j.castLE (Nat.le_of_lt i.2)) ^ e) =
          (fun j : Fin i.1 => scaledVariable π' (j.castLE (Nat.le_of_lt i.2)) ^ e) := by
        funext j
        simp only [scaledVariable_apply, hπ'', update_castLE_of_le π' t _ i hi j]
      refine ⟨π'', ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = t
        · subst j
          obtain ⟨s₁, hs₁, hs₁eq⟩ := hrescale t
          exact ⟨s₀ * s₁, p.primeCompl.mul_mem hs₀ hs₁, by
            simp only [hπ'', Function.update_self, hs₁eq]; ring⟩
        · rw [hpres j hj]; exact hrescale j
      · calc
          Ideal.span (Set.range fun i => f (π'' i)) =
              Ideal.span (Set.range fun i => f (π' i)) := by
            rw [Ideal.span_range_eq_iSup, Ideal.span_range_eq_iSup]
            refine iSup_congr fun j => ?_
            by_cases hj : j = t
            · subst j
              simpa only [hπ'', Function.update_self, map_mul] using
                Ideal.span_singleton_mul_left_unit (IsLocalization.map_units B ⟨s₀, hs₀⟩)
                  (f (π' t))
            · rw [hpres j hj]
          _ = IsLocalRing.maximalIdeal B := hspan'
      · intro i hi
        by_cases hik : i.1 < k
        · have hit : i ≠ t := fun hcon => by
            have h1 : (i : ℕ) = (t : ℕ) := congrArg Fin.val hcon
            omega
          have hupd : scaledVariable π'' i = scaledVariable π' i := by
            simp only [scaledVariable_apply, hpres i hit]
          rw [hprefix i (by omega), hupd]
          exact hann i hik
        · have hit : i = t := Fin.ext (by omega)
          subst i
          rw [hprefix t le_rfl]
          intro x
          simpa only [hγt, mul_pow, pow_one] using hsa 1 Nat.one_pos x
  obtain ⟨π', hrescale, hspan', hann⟩ := H d le_rfl
  exact ⟨π', hrescale, hspan', fun i => hann i i.2⟩

/-! ### Ingredients for the enlargement induction -/

/-- A flat local homomorphism of local rings is faithfully flat. -/
theorem faithfullyFlat_of_flat_of_isLocalHom {D L : Type u} [CommRing D] [CommRing L]
    [IsLocalRing D] [IsLocalRing L] (g : D →+* L) [IsLocalHom g] (hg : RingHom.Flat g) :
    g.FaithfullyFlat := by
  let := g.toAlgebra
  have hflat : Module.Flat D L := hg
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal D L).mpr ⟨hflat, fun I hI hcon => ?_⟩
  have hle : I • (⊤ : Submodule D L) ≤
      (IsLocalRing.maximalIdeal L).restrictScalars D := by
    refine Submodule.smul_le.mpr fun y hy z _ => ?_
    have hynu : ¬ IsUnit (g y) := fun hu =>
      (IsLocalRing.mem_maximalIdeal y).mp (IsLocalRing.le_maximalIdeal hI hy)
        (IsLocalHom.map_nonunit y hu)
    exact (IsLocalRing.maximalIdeal L).mul_mem_right z
      ((IsLocalRing.mem_maximalIdeal (g y)).mpr hynu)
  have hmem : (1 : L) ∈ I • (⊤ : Submodule D L) := by rw [hcon]; exact Submodule.mem_top
  have h1 : (1 : L) ∈ (IsLocalRing.maximalIdeal L).restrictScalars D := hle hmem
  exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- An element of the product of an ideal `K` with the ideal generated by `a₁, …, a_r` is a
combination `Σ_j a_j c_j` with every coefficient `c_j` in `K`. -/
theorem exists_sum_eq_of_mem_mul_span_range {A : Type*} [CommRing A] (K : Ideal A) {r : ℕ}
    (a : Fin r → A) {x : A} (hx : x ∈ K * Ideal.span (Set.range a)) :
    ∃ c : Fin r → A, (∀ j, c j ∈ K) ∧ x = ∑ j, a j * c j := by
  classical
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hn
    refine ⟨fun j => m * g j, fun j => K.mul_mem_right _ hm, ?_⟩
    rw [← hg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro y z ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    refine ⟨c + c', fun j => K.add_mem (hc j) (hc' j), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_add]

/-- A common factor can be pulled out of the coefficients of a combination `Σ_j a_j c y_j`. -/
private theorem sum_mul_mul_eq_mul_sum {A : Type*} [CommRing A] {r : ℕ} (a y : Fin r → A) (c : A) :
    ∑ j, a j * (c * y j) = c * ∑ j, a j * y j := by
  simp only [Finset.mul_sum, mul_left_comm]

/-- **Clearing denominators in a power relation.** Suppose `x ^ M = Σ_j a_j b_j` holds in a
localization `S⁻¹Λ`, with `M > 0`. Then there are `s ∈ S` and `μ_1, …, μ_r ∈ Λ` such that
`μ_j = s ^ M b_j` in `S⁻¹Λ` while `(s x) ^ M = Σ_j a_j μ_j` already holds in `Λ`. -/
theorem exists_mem_pow_mul_eq_sum_of_localization_rel {Λ : Type*} [CommRing Λ] (S : Submonoid Λ)
    (L : Type*) [CommRing L] [Algebra Λ L] [IsLocalization S L] {r M : ℕ} (hM : 0 < M)
    (a : Fin r → Λ) (x : Λ) (b : Fin r → L)
    (hrel : algebraMap Λ L x ^ M = ∑ j, algebraMap Λ L (a j) * b j) :
    ∃ s ∈ S, ∃ μ : Fin r → Λ,
      (∀ j, algebraMap Λ L (μ j) = algebraMap Λ L s ^ M * b j) ∧
      (s * x) ^ M = ∑ j, a j * μ j := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  -- Put the `b_j` over a common denominator `v ∈ S`.
  obtain ⟨v, hv⟩ := IsLocalization.exist_integer_multiples S Finset.univ b
  have hint : ∀ j, ∃ w : Λ, algebraMap Λ L w = algebraMap Λ L (v : Λ) * b j := by
    intro j
    obtain ⟨w, hw⟩ := hv j (Finset.mem_univ j)
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose w hw using hint
  -- The relation becomes an equality of images, hence holds in `Λ` after one more factor.
  have himg : algebraMap Λ L ((v : Λ) * x ^ (M' + 1)) = algebraMap Λ L (∑ j, a j * w j) := by
    rw [map_mul, map_pow, hrel, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hw j]; ring
  obtain ⟨v', hv'⟩ := IsLocalization.exists_of_eq (M := S) himg
  refine ⟨(v' : Λ) * (v : Λ), S.mul_mem v'.2 v.2,
    fun j => (v' : Λ) ^ (M' + 1) * (v : Λ) ^ M' * w j, fun j => ?_, ?_⟩
  · rw [map_mul, map_mul, map_pow, map_pow, hw j, map_mul]
    ring
  · rw [sum_mul_mul_eq_mul_sum]
    linear_combination ((v' : Λ) ^ M' * (v : Λ) ^ M') * hv'

/-- Essential smoothness is preserved by composition. -/
theorem isEssentiallySmooth_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {g : R →+* S} {h : S →+* T} (hg : g.IsEssentiallySmooth) (hh : h.IsEssentiallySmooth) :
    (h.comp g).IsEssentiallySmooth := by
  let := g.toAlgebra
  let := h.toAlgebra
  let := (h.comp g).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨⟨A, _, _, _, M, _, _, _⟩, hgs⟩ := hg
  obtain ⟨⟨B, _, _, _, M', _, _, _⟩, hhs⟩ := hh
  have hfp : (h.comp g).EssentiallyOfFinitePresentation :=
    essFinitePresentation_comp (f := g) (g := h)
      ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, M,
        inferInstance⟩
      ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, M',
        inferInstance⟩
  obtain ⟨A', _, _, _, _, _, M'', _⟩ := hfp
  exact ⟨⟨A', inferInstance, inferInstance, inferInstance, M'', inferInstance, inferInstance,
    inferInstance⟩, Algebra.FormallySmooth.comp R S T⟩

/-! ### The relation `π ^ (2N) = Σ_j a_j b_j` with coefficients visible in the enlargement -/

/-- The Artinian local ring `Λ_𝔮/𝔮ⁿΛ_𝔮` of Situation 07F7. -/
abbrev truncatedLocalization (Λ : Type u) [CommRing Λ] (q : Ideal Λ) [q.IsPrime] (n : ℕ) :
    Type u :=
  Localization.AtPrime q ⧸ Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n)

/-- The structure map `Λ → Λ_q/q^nΛ_q` is `Λ → Λ_q` followed by the quotient map. -/
private theorem algebraMap_truncatedLocalization_apply {Λ : Type u} [CommRing Λ] (q : Ideal Λ)
    [q.IsPrime] (n : ℕ) (y : Λ) :
    algebraMap Λ (truncatedLocalization Λ q n) y =
      Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n))
        (algebraMap Λ (Localization.AtPrime q) y) := by
  rw [IsScalarTower.algebraMap_apply Λ (Localization.AtPrime q) (truncatedLocalization Λ q n),
    Ideal.Quotient.algebraMap_eq]

/-- Let `x ∈ q` and suppose `q ^ N Λ_q ⊆ (a_1, …, a_r) Λ_q` with `N ≤ n`. If `x` and the `a_j`
reduce in `Λ_q/q^n Λ_q` into the image of a local ring `D'` mapping to `Λ_q/q^n Λ_q` by a flat
local homomorphism, then `x ^ (2N) = Σ_j a_j b_j` in `Λ_q` for coefficients `b_j` that again
reduce into the image of `D'`. -/
private theorem exists_pow_eq_sum_coeff_mem_range
    {Λ : Type u} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] {N n r : ℕ} (hn : N ≤ n)
    (a : Fin r → Λ)
    (hqN : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ N) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) (Ideal.span (Set.range a)))
    [IsLocalRing (truncatedLocalization Λ q n)]
    {D' : Type u} [CommRing D'] [IsLocalRing D']
    (b' : D' →+* truncatedLocalization Λ q n) [IsLocalHom b'] (hfl : RingHom.Flat b')
    {x : Λ} (hx : x ∈ q)
    (hxD : ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) x)
    (haD : ∀ j, ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) (a j)) :
    ∃ bb : Fin r → Localization.AtPrime q,
      algebraMap Λ (Localization.AtPrime q) x ^ (2 * N) =
          ∑ j, algebraMap Λ (Localization.AtPrime q) (a j) * bb j ∧
      ∀ j, ∃ w : D', b' w =
        Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n)) (bb j) := by
  classical
  set g := algebraMap Λ (Localization.AtPrime q) with hg
  set Iq := Ideal.map g (q ^ n) with hIq
  set red := Ideal.Quotient.mk Iq with hred
  set hbar := algebraMap Λ (truncatedLocalization Λ q n) with hhbar
  have hbar_eq (y : Λ) : hbar y = red (g y) := algebraMap_truncatedLocalization_apply q n y
  -- `(a_1, …, a_r) Λ_q` is the span of the images of the `a_j`.
  have hspanmap : Ideal.map g (Ideal.span (Set.range a)) =
      Ideal.span (Set.range fun j => g (a j)) := by
    rw [Ideal.map_span, ← Set.range_comp, Function.comp_def]
  -- `x ^ N` lies in that ideal.
  have hpow : g x ^ N ∈ Ideal.span (Set.range fun j => g (a j)) := by
    have h0 : x ^ N ∈ q ^ N := Ideal.pow_mem_pow hx N
    have h1 := hqN (Ideal.mem_map_of_mem g h0)
    rw [hspanmap] at h1
    rwa [map_pow] at h1
  obtain ⟨wx, hwx⟩ := hxD
  choose wa hwa using haD
  -- `x ^ N` has a preimage in `D'` lying in the ideal generated by the preimages of the `a_j`.
  have hmemmap : b' (wx ^ N) ∈ Ideal.map b' (Ideal.span (Set.range wa)) := by
    have hmapb : Ideal.map b' (Ideal.span (Set.range wa)) =
        Ideal.span (Set.range fun j => hbar (a j)) := by
      rw [Ideal.map_span, ← Set.range_comp, Function.comp_def]
      exact congrArg Ideal.span (congrArg Set.range (funext hwa))
    have himg : Ideal.span (Set.range fun j => hbar (a j)) =
        Ideal.map red (Ideal.span (Set.range fun j => g (a j))) := by
      rw [Ideal.map_span, ← Set.range_comp, Function.comp_def]
      exact congrArg Ideal.span (congrArg Set.range (funext fun j => hbar_eq (a j)))
    rw [hmapb, himg, map_pow, hwx, hbar_eq, ← map_pow]
    exact Ideal.mem_map_of_mem _ hpow
  have hy : wx ^ N ∈ Ideal.span (Set.range wa) := by
    have hcm := faithfullyFlat_comap_map_eq b'
      (faithfullyFlat_of_flat_of_isLocalHom b' hfl) (Ideal.span (Set.range wa))
    exact hcm ▸ Ideal.mem_comap.mpr hmemmap
  obtain ⟨dd, hdd⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
  -- Lift the images `b' (dd j)` to `Λ_q`.
  have hlift : ∀ j, ∃ u : Localization.AtPrime q, red u = b' (dd j) :=
    fun j => Ideal.Quotient.mk_surjective (b' (dd j))
  choose cc hcc using hlift
  -- The error term lies in `q ^ n Λ_q`.
  have herr : g x ^ N - ∑ j, g (a j) * cc j ∈ Iq := by
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    have hx1 : red (g x ^ N) = b' (wx ^ N) := by
      rw [map_pow, ← hbar_eq, ← hwx, ← map_pow b' wx N]
    have h1 : red (g x ^ N) = ∑ j, hbar (a j) * b' (dd j) := by
      rw [hx1, ← hdd, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hwa j, mul_comm]
    rw [map_sub, map_sum, h1]
    refine sub_eq_zero_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, hcc j, ← hbar_eq]
  -- Split the error term along the `a_j`, with coefficients in `q ^ (n - N) Λ_q`.
  have hle : Iq ≤ Ideal.map g (q ^ (n - N)) * Ideal.span (Set.range fun j => g (a j)) := by
    have hqq : q ^ n = q ^ (n - N) * q ^ N := by
      rw [← pow_add]
      congr 1
      omega
    rw [hIq, hqq, Ideal.map_mul]
    exact Ideal.mul_mono le_rfl (hqN.trans hspanmap.le)
  obtain ⟨cc', hcc'K, hcc'eq⟩ :=
    exists_sum_eq_of_mem_mul_span_range (A := Localization.AtPrime q)
      (Ideal.map g (q ^ (n - N))) (fun j => g (a j))
      (x := g x ^ N - ∑ j, g (a j) * cc j) (hle herr)
  refine ⟨fun j => g x ^ N * (cc j + cc' j), ?_, fun j => ⟨wx ^ N * dd j, ?_⟩⟩
  · rw [sum_mul_mul_eq_mul_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← hcc'eq, two_mul, pow_add]
    ring
  · -- The `q ^ (n - N)` part dies in `Λ_q/q^nΛ_q`.
    have hkill : red (g x ^ N * cc' j) = 0 := by
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      have hmul : Ideal.map g (q ^ N) * Ideal.map g (q ^ (n - N)) ≤ Iq := by
        rw [hIq, ← Ideal.map_mul, ← pow_add]
        exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      refine hmul (Ideal.mul_mem_mul ?_ (hcc'K j))
      have h0 : x ^ N ∈ q ^ N := Ideal.pow_mem_pow hx N
      rw [← map_pow]
      exact Ideal.mem_map_of_mem g h0
    have hx1 : b' (wx ^ N) = red (g x ^ N) := by
      rw [map_pow, hwx, hbar_eq, ← map_pow]
    have hrhs : red (g x ^ N * (cc j + cc' j)) = red (g x ^ N) * b' (dd j) := by
      rw [mul_add, map_add, hkill, add_zero, map_mul, hcc j]
    rw [map_mul, hx1, hrhs]

/-! ### Scaling the parameters inside an essentially smooth enlargement -/

/-- The identity is essentially smooth. -/
private lemma isEssentiallySmooth_id (D : Type u) [CommRing D] :
    (RingHom.id D).IsEssentiallySmooth :=
  RingHom.IsEssentiallySmooth.of_etale (R := D) (S := D)

/-- Multiplying the members of a tuple by elements of `Λ \ q` does not change the ideal its
image generates in `Λ_q`. -/
private lemma span_range_map_mul_eq {Λ : Type*} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] {d : ℕ}
    (u π : Fin d → Λ) (hu : ∀ i, u i ∈ q.primeCompl) :
    Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (u i * π i)) =
      Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) := by
  rw [Ideal.span_range_eq_iSup, Ideal.span_range_eq_iSup]
  refine iSup_congr fun i => ?_
  rw [map_mul]
  exact Ideal.span_singleton_mul_left_unit (IsLocalization.map_units _ ⟨u i, hu i⟩) _

/-- If `b' ∘ c = b`, anything in the image of `b` is in the image of `b'`. -/
private theorem exists_eq_of_comp_eq {D D' T : Type*} [Semiring D] [Semiring D'] [Semiring T]
    {c : D →+* D'} {b' : D' →+* T} {b : D →+* T} (hcomp : b'.comp c = b) {y : T}
    (hy : ∃ w, b w = y) : ∃ w, b' w = y := by
  obtain ⟨w, hw⟩ := hy
  exact ⟨c w, by rw [← hw, ← hcomp, RingHom.comp_apply]⟩

/-- **Stacks 07FX.** In the situation of Stacks 07FJ, with `N ≤ n`, `q ^ N Λ_q ⊆ (a_1, …, a_r)Λ_q`
and `π_1, …, π_d ∈ q` lifting a regular system of parameters of `Λ_q`, suppose the `a_j` and the
`π_i` reduce in `Λ_q/q^nΛ_q` into the image of an Artinian local ring `D` mapping to
`Λ_q/q^nΛ_q` by a flat local homomorphism. Then there are `δ_1, …, δ_d ∈ Λ \ q` and a
factorization `D → D' → Λ_q/q^nΛ_q` with `D'` Artinian local, `D → D'` essentially smooth and
`D' → Λ_q/q^nΛ_q` flat and local, such that, writing `π'_i = δ_i π_i`:
`(π'_i)^{2N} = Σ_j a_j λ_{ij}` in `Λ` with every `λ_{ij}` reducing into the image of `D'`; the
annihilator of `π'_i` in `Λ ⧸ ((π'_1)^e, …, (π'_{i-1})^e)` is the annihilator of `(π'_i)^2`; and
every `δ_i` reduces into the image of `D'`. -/
@[stacks 07FX "the data of (07FT) — the Artinian local `D`, the flat local `D → Λ_q/q^nΛ_q`, \
and the memberships of the generators of `A` — are hypotheses, as are the lifts of (07FU); \
`H_{A/k}Λ` is the ideal generated by the images `a_1, …, a_r` and `(a)` is stated as the \
relation in `Λ` together with the reduction of each `λ_{ij}` into the image of `D'`"]
theorem exists_essentiallySmooth_enlargement_annihilator_sq_eq
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Algebra k Λ]
    (q : Ideal Λ) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    {d r N n e : ℕ} (hd : ringKrullDim (Localization.AtPrime q) = d)
    (hN : 0 < N) (hn : N ≤ n) (he : 0 < e)
    [IsLocalRing (truncatedLocalization Λ q n)] [IsArtinianRing (truncatedLocalization Λ q n)]
    (a : Fin r → Λ)
    (hqN : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ N) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) (Ideal.span (Set.range a)))
    (π : Fin d → Λ) (hπq : ∀ i, π i ∈ q)
    (hπspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    {D : Type u} [CommRing D] [IsLocalRing D] [IsArtinianRing D]
    (b : D →+* truncatedLocalization Λ q n) [IsLocalHom b] (hb : RingHom.Flat b)
    (haD : ∀ j, ∃ w : D, b w = algebraMap Λ (truncatedLocalization Λ q n) (a j))
    (hπD : ∀ i, ∃ w : D, b w = algebraMap Λ (truncatedLocalization Λ q n) (π i)) :
    ∃ (δ : Fin d → Λ) (lam : Fin d → Fin r → Λ) (D' : Type u) (_ : CommRing D')
      (_ : IsLocalRing D') (_ : IsArtinianRing D') (c : D →+* D')
      (b' : D' →+* truncatedLocalization Λ q n) (_ : IsLocalHom c) (_ : IsLocalHom b'),
      c.IsEssentiallySmooth ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
      (∀ i, δ i ∈ q.primeCompl) ∧
      (∀ i, (δ i * π i) ^ (2 * N) = ∑ j, a j * lam i j) ∧
      (∀ i j, ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) (lam i j)) ∧
      (∀ i, ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) (δ i)) ∧
      (∀ i : Fin d, ∀ x : Λ ⧸ Ideal.span (Set.range fun j : Fin i.1 =>
          (δ (j.castLE (Nat.le_of_lt i.2)) * π (j.castLE (Nat.le_of_lt i.2))) ^ e),
        x * Ideal.Quotient.mk _ (δ i * π i) = 0 ↔
          x * Ideal.Quotient.mk _ ((δ i * π i) ^ 2) = 0) := by
  classical
  have hbarmk := algebraMap_truncatedLocalization_apply q n
  -- Choose `δ_i` and the enlargement one index at a time.
  have H : ∀ kk, kk ≤ d → ∃ (δ : Fin d → Λ) (lam : Fin d → Fin r → Λ) (D' : Type u)
      (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D') (c : D →+* D')
      (b' : D' →+* truncatedLocalization Λ q n) (_ : IsLocalHom c) (_ : IsLocalHom b'),
      c.IsEssentiallySmooth ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
      (∀ i, δ i ∈ q.primeCompl) ∧
      (∀ i : Fin d, i.1 < kk → (δ i * π i) ^ (2 * N) = ∑ j, a j * lam i j) ∧
      (∀ i j, ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) (lam i j)) ∧
      (∀ i, ∃ w : D', b' w = algebraMap Λ (truncatedLocalization Λ q n) (δ i)) ∧
      (∀ i : Fin d, i.1 < kk → ∀ x : Λ ⧸ Ideal.span (Set.range fun j : Fin i.1 =>
          (δ (j.castLE (Nat.le_of_lt i.2)) * π (j.castLE (Nat.le_of_lt i.2))) ^ e),
        x * Ideal.Quotient.mk _ (δ i * π i) = 0 ↔
          x * Ideal.Quotient.mk _ ((δ i * π i) ^ 2) = 0) := by
    intro kk
    induction kk with
    | zero =>
      exact fun _ => ⟨fun _ => 1, fun _ _ => 0, D, inferInstance, inferInstance, inferInstance,
        RingHom.id D, b, inferInstance, inferInstance, isEssentiallySmooth_id D, hb,
        b.comp_id, fun _ => q.primeCompl.one_mem,
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i j => ⟨0, by simp⟩,
        fun i => ⟨1, by simp⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ kk ih =>
      intro hk
      obtain ⟨δ, lam, D', hcr, hlr, har, c, b', hlc, hlb, hess, hflat, hcomp, hδq, hA,
        hlamD, hδD, hB⟩ := ih (by omega)
      set t : Fin d := ⟨kk, by omega⟩
      have htval : (t : ℕ) = kk := rfl
      have hlt (i : Fin d) (hi : i.1 < kk + 1) (hit : i ≠ t) : i.1 < kk := by
        have : i.1 ≠ kk := fun hcon => hit (Fin.ext (by omega))
        omega
      -- The relation `π_t ^ (2N) = Σ_j a_j bb_j` over `Λ_q`, with the `bb_j` visible in `D'`.
      obtain ⟨bb, hbbrel, hbbD⟩ := exists_pow_eq_sum_coeff_mem_range q hn a hqN b' hflat
        (hπq t) (exists_eq_of_comp_eq hcomp (hπD t))
        fun j => exists_eq_of_comp_eq hcomp (haD j)
      -- Clear denominators.
      obtain ⟨s, hs, μ, hμloc, hμrel⟩ := exists_mem_pow_mul_eq_sum_of_localization_rel
        q.primeCompl (Localization.AtPrime q) (by omega : 0 < 2 * N) a (π t) bb hbbrel
      -- Enlarge `D'` so that a power of `s` becomes visible.
      obtain ⟨Q₀, D₁, hcr₁, hlr₁, har₁, c₁, b₁, hlc₁, hlb₁, hQ₀, hess₁, hflat₁, hcomp₁,
        ws, hws⟩ :=
        exists_essentiallySmooth_enlargement_containing_pow k p hp Λ q n b' hflat s
      obtain ⟨Q, rfl⟩ : ∃ Q, Q₀ = Q + 1 := ⟨Q₀ - 1, by omega⟩
      -- The rescaled parameter `s ^ (Q+1) π_t` and its coefficients.
      have hs₁mem : s ^ (Q + 1) ∈ q.primeCompl := q.primeCompl.pow_mem hs _
      have hμ₁rel : (s ^ (Q + 1) * π t) ^ (2 * N) =
          ∑ j, a j * (s ^ (2 * N * Q) * μ j) := by
        have hsplit : (s ^ (Q + 1) * π t) ^ (2 * N) =
            s ^ (2 * N * Q) * (s * π t) ^ (2 * N) := by
          rw [mul_pow, mul_pow, ← pow_mul,
            show (Q + 1) * (2 * N) = 2 * N * Q + 2 * N by ring, pow_add, mul_assoc]
        rw [sum_mul_mul_eq_mul_sum, ← hμrel, hsplit]
      have hμ₁loc (j : Fin r) :
          algebraMap Λ (Localization.AtPrime q) (s ^ (2 * N * Q) * μ j) =
            algebraMap Λ (Localization.AtPrime q) (s ^ (Q + 1)) ^ (2 * N) * bb j := by
        have h2 : algebraMap Λ (Localization.AtPrime q) (s ^ (Q + 1)) ^ (2 * N) =
            algebraMap Λ (Localization.AtPrime q) s ^ (2 * N * Q) *
              algebraMap Λ (Localization.AtPrime q) s ^ (2 * N) := by
          rw [map_pow, ← pow_mul,
            show (Q + 1) * (2 * N) = 2 * N * Q + 2 * N by ring, pow_add]
        rw [map_mul, map_pow, hμloc j, h2]
        ring
      have hμ₁D (j : Fin r) : ∃ w : D₁, b₁ w = algebraMap Λ (truncatedLocalization Λ q n)
          (s ^ (2 * N * Q) * μ j) := by
        obtain ⟨wb, h1⟩ := exists_eq_of_comp_eq hcomp₁ (hbbD j)
        refine ⟨ws ^ (2 * N) * wb, ?_⟩
        have h3 : algebraMap Λ (truncatedLocalization Λ q n) (s ^ (2 * N * Q) * μ j) =
            algebraMap Λ (truncatedLocalization Λ q n) (s ^ (Q + 1)) ^ (2 * N) *
              Ideal.Quotient.mk
                (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n)) (bb j) := by
          rw [hbarmk (s ^ (2 * N * Q) * μ j), hμ₁loc j, map_mul, hbarmk (s ^ (Q + 1)), map_pow]
        rw [map_mul, map_pow, hws, h1, h3]
      -- The regular sequence and Ogoma's lemma.
      have hu₁mem : ∀ i, Function.update δ t (s ^ (Q + 1)) i ∈ q.primeCompl := by
        intro i
        by_cases hi : i = t
        · subst i; rw [Function.update_self]; exact hs₁mem
        · rw [Function.update_of_ne hi]; exact hδq i
      have hρspan := (span_range_map_mul_eq q (Function.update δ t (s ^ (Q + 1))) π
        hu₁mem).trans hπspan
      obtain ⟨s', hs', hogoma⟩ := exists_mem_annihilator_sq_eq_of_isRegular_map q.primeCompl
        (Localization.AtPrime q) (fun i => Function.update δ t (s ^ (Q + 1)) i * π i)
        (isRegular_of_perm_ofFn_of_span_eq_maximalIdeal _ hρspan hd (List.Perm.refl _)) he t
      -- Enlarge once more so that a power of `s'` becomes visible.
      obtain ⟨Q₁, D₂, hcr₂, hlr₂, har₂, c₂, b₂, hlc₂, hlb₂, hQ₁, hess₂, hflat₂, hcomp₂,
        ws', hws'⟩ :=
        exists_essentiallySmooth_enlargement_containing_pow k p hp Λ q n b₁ hflat₁ s'
      -- Assemble the new data.
      refine ⟨Function.update δ t (s' ^ Q₁ * s ^ (Q + 1)),
        Function.update lam t (fun j => (s' ^ Q₁) ^ (2 * N) * (s ^ (2 * N * Q) * μ j)),
        D₂, hcr₂, hlr₂, har₂, c₂.comp (c₁.comp c), b₂, ?_, hlb₂,
        isEssentiallySmooth_comp (isEssentiallySmooth_comp hess hess₁) hess₂,
        hflat₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact RingHom.isLocalHom_comp _ _
      · rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, hcomp₂, hcomp₁, hcomp]
      · intro i
        by_cases hi : i = t
        · subst i
          rw [Function.update_self]
          exact q.primeCompl.mul_mem (q.primeCompl.pow_mem hs' _) hs₁mem
        · rw [Function.update_of_ne hi]; exact hδq i
      · -- clause (a)
        intro i hi
        by_cases hit : i = t
        · subst i
          simp only [Function.update_self]
          rw [sum_mul_mul_eq_mul_sum, ← hμ₁rel, mul_assoc, mul_pow]
        · rw [Function.update_of_ne hit, Function.update_of_ne hit]
          exact hA i (hlt i hi hit)
      · -- the `λ_{ij}` are visible in `D₂`
        intro i j
        by_cases hit : i = t
        · subst i
          simp only [Function.update_self]
          obtain ⟨w, hw⟩ := exists_eq_of_comp_eq hcomp₂ (hμ₁D j)
          refine ⟨ws' ^ (2 * N) * w, ?_⟩
          rw [map_mul, map_pow, hws', hw, ← map_pow, ← map_mul]
        · rw [Function.update_of_ne hit]
          exact exists_eq_of_comp_eq hcomp₂ (exists_eq_of_comp_eq hcomp₁ (hlamD i j))
      · -- the `δ_i` are visible in `D₂`
        intro i
        by_cases hit : i = t
        · subst i
          simp only [Function.update_self]
          obtain ⟨w, h1⟩ := exists_eq_of_comp_eq hcomp₂ ⟨ws, hws⟩
          refine ⟨ws' * w, ?_⟩
          rw [map_mul, hws', h1, ← map_mul]
        · rw [Function.update_of_ne hit]
          exact exists_eq_of_comp_eq hcomp₂ (exists_eq_of_comp_eq hcomp₁ (hδD i))
      · -- clause (b)
        intro i hi
        have hprefix (v : Λ) (l : Fin d) (hl : l.1 ≤ kk) :
            (fun j : Fin l.1 => (Function.update δ t v
                (j.castLE (Nat.le_of_lt l.2)) * π (j.castLE (Nat.le_of_lt l.2))) ^ e) =
            (fun j : Fin l.1 => (δ (j.castLE (Nat.le_of_lt l.2)) *
                π (j.castLE (Nat.le_of_lt l.2))) ^ e) := by
          funext j
          rw [update_castLE_of_le δ t v l hl j]
        by_cases hit : i = t
        · subst i
          rw [hprefix _ t le_rfl, Function.update_self]
          intro x
          have hρt : s' ^ Q₁ * (Function.update δ t (s ^ (Q + 1)) t * π t) =
              s' ^ Q₁ * s ^ (Q + 1) * π t := by
            rw [Function.update_self, mul_assoc]
          have := hogoma Q₁ hQ₁
          rw [hprefix _ t le_rfl] at this
          simpa only [hρt] using this x
        · rw [hprefix _ i (by omega), Function.update_of_ne hit]
          exact hB i (hlt i hi hit)
  obtain ⟨δ, lam, D', hcr, hlr, har, c, b', hlc, hlb, hess, hflat, hcomp, hδq, hA, hlamD,
    hδD, hB⟩ := H d le_rfl
  exact ⟨δ, lam, D', hcr, hlr, har, c, b', hlc, hlb, hess, hflat, hcomp, hδq,
    fun i => hA i i.2, hlamD, hδD, fun i => hB i i.2⟩

end Stacks.Smoothing

end
