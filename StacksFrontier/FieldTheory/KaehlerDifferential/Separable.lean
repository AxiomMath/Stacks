module


public import StacksFrontier.FieldTheory.Separable.Defs
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Kaehler.BaseChange
import StacksFrontier.RingTheory.Kaehler.PerfectField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separability of a field extension is injectivity on absolute differentials

Let `K/k` be an extension of fields. Then `K` is separable over `k` — every subextension of `K/k`
that is finitely generated over `k` has a transcendence basis over which it is separable
algebraic — if and only if the canonical map `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective.

## Main results

* `Algebra.isSeparableExtension_iff_injective_mapBaseChange`: a field extension `K/k` is separable
  if and only if `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective.

## References

* [StacksProject 031X](https://stacks.math.columbia.edu/tag/031X)
-/

@[expose] public section

universe u v

@[expose] public section

namespace Stacks.KaehlerDifferential.Separability

open scoped TensorProduct



/-! ### Naturality of `mapBaseChange` in the upper field -/

section Naturality

variable (k A B : Type*) [Field k] [Field A] [Field B] [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B]

/-- The `k`-linear map `A ⊗[k] Ω[k⁄ℤ] → B ⊗[k] Ω[k⁄ℤ]` induced by the inclusion `A → B`. -/
private noncomputable abbrev incl : A ⊗[k] Ω[k⁄ℤ] →ₗ[k] B ⊗[k] Ω[k⁄ℤ] :=
  LinearMap.rTensor Ω[k⁄ℤ] (IsScalarTower.toAlgHom k A B).toLinearMap

private lemma injective_incl : Function.Injective (incl k A B) :=
  Module.Flat.rTensor_preserves_injective_linearMap _
    (FaithfulSMul.algebraMap_injective A B)

private lemma map_map (y : Ω[k⁄ℤ]) :
    KaehlerDifferential.map ℤ ℤ A B (KaehlerDifferential.map ℤ ℤ k A y) =
      KaehlerDifferential.map ℤ ℤ k B y := by
  have h : y ∈ (⊤ : Submodule k Ω[k⁄ℤ]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at h
  induction h using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp [← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

private lemma mapBaseChange_incl (ξ : A ⊗[k] Ω[k⁄ℤ]) :
    KaehlerDifferential.mapBaseChange ℤ k B (incl k A B ξ) =
      KaehlerDifferential.map ℤ ℤ A B (KaehlerDifferential.mapBaseChange ℤ k A ξ) := by
  induction ξ with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp only [incl, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom', KaehlerDifferential.mapBaseChange_tmul,
        LinearMap.map_smul_of_tower, map_map]
      rw [algebraMap_smul]

/-- Injectivity of `mapBaseChange` passes to a subextension. -/
private lemma injective_mapBaseChange_of_le
    (h : Function.Injective (KaehlerDifferential.mapBaseChange ℤ k B)) :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k A) := by
  have h2 : Function.Injective
      (KaehlerDifferential.map ℤ ℤ A B ∘ KaehlerDifferential.mapBaseChange ℤ k A) := by
    intro x y hxy
    simp only [Function.comp_apply] at hxy
    refine injective_incl k A B (h ?_)
    rw [mapBaseChange_incl, mapBaseChange_incl, hxy]
  exact h2.of_comp

end Naturality

/-! ### Separably generated extensions -/

/-- A separably generated field extension is formally smooth. -/
private lemma formallySmooth_of_isSeparablyGenerated (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparablyGenerated k K] : Algebra.FormallySmooth k K := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.exists_isTranscendenceBasis_and_isSeparable (k := k) (K := K)
  have hr : Set.range ((↑) : s → K) = (s : Set K) := Subtype.range_coe
  rw [← hr] at hsep
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- For a separably generated extension the canonical map `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is
(split) injective. -/
@[ega "0 20.6.3" "special case"]
private lemma injective_mapBaseChange_of_isSeparablyGenerated (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparablyGenerated k K] :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) := by
  have := formallySmooth_of_isSeparablyGenerated k K
  obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange ℤ k K
  intro x y hxy
  have := congr($hr x)
  have h2 := congr($hr y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this h2
  rw [← this, ← h2, hxy]

/-! ### Vanishing of `d` on `p`-th powers, and `p`-th powers from vanishing `d` -/

private lemma D_pow_char_eq_zero {K : Type*} [Field K] (p : ℕ) [CharP K p] (x : K) :
    KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

/-- An element of a field of characteristic `p` whose absolute differential vanishes is a `p`-th
power. -/
@[ega "0 21.4.4" "Necessity, partial", ega "0 21.5.3" "partial"]
private lemma exists_pow_eq_of_D_eq_zero {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {a : k} (h : KaehlerDifferential.D ℤ k a = 0) : ∃ b : k, b ^ p = a := by
  let : Algebra (ZMod p) k := ZMod.algebra _ _
  rw [← KaehlerDifferential.D_eq_zero_iff_exists_pow_eq (k := ZMod p) p a]
  simpa using congrArg (KaehlerDifferential.map ℤ (ZMod p) k k) h

/-! ### Linear independence of the left factors of a tensor -/

/-- If the left factors of a finite sum of tensors are linearly independent, and the sum vanishes,
then all right factors vanish. -/
private lemma eq_zero_of_sum_tmul_eq_zero {k V M ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] (t : Finset ι) (y : ι → V)
    (hy : ∀ g : ι → k, (∑ i ∈ t, g i • y i) = 0 → ∀ i ∈ t, g i = 0)
    (ω : ι → M) (h : (∑ i ∈ t, y i ⊗ₜ[k] ω i) = 0) {j : ι} (hj : j ∈ t) : ω j = 0 := by
  classical
  have hli : LinearIndependent k (fun x : (t : Set ι) ↦ y x) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have : (∑ x ∈ t, (fun z ↦ if hz : z ∈ t then g ⟨z, hz⟩ else 0) x • y x) = 0 := by
      rw [← Finset.sum_coe_sort t]
      simpa using hg
    simpa using hy _ this i.1 i.2
  have hinj : Function.Injective
      (LinearMap.rTensor M (Finsupp.linearCombination k (fun x : (t : Set ι) ↦ y x))) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hli
  have h0 : (∑ i : (t : Set ι), (Finsupp.single i (1 : k)) ⊗ₜ[k] ω i) = 0 := by
    refine hinj ?_
    simp only [map_sum, LinearMap.rTensor_tmul, Finsupp.linearCombination_single, one_smul,
      map_zero]
    exact (Finset.sum_coe_sort t fun x ↦ y x ⊗ₜ[k] ω x).trans h
  have := congrArg (fun x ↦ TensorProduct.finsuppScalarLeft k M (t : Set ι) x ⟨j, hj⟩) h0
  simpa [TensorProduct.finsuppScalarLeft_apply_tmul_apply, Finsupp.single_apply] using this

/-! ### MacLane's criterion -/

/-- The inductive step of MacLane's criterion: if `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective and `k`
has characteristic `p`, then a relation `∑ g x • x ^ p = 0` between the `p`-th powers of finitely
many `k`-linearly independent elements of `K` is trivial. -/
private lemma eq_zero_of_sum_smul_pow_eq_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K)) (s : Finset K)
    (hs : LinearIndepOn k _root_.id (s : Set K)) :
    ∀ (n : ℕ) (t : Finset K), t.card ≤ n → (t : Set K) ⊆ (s : Set K) → ∀ g : K → k,
      (∑ x ∈ t, g x • x ^ p) = 0 → ∀ x ∈ t, g x = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.ne_zero
  have : ExpChar K p := .prime hp
  have hterm : ∀ (x : K) (a : k), KaehlerDifferential.D ℤ K (a • x ^ p) =
      x ^ p • KaehlerDifferential.D ℤ K (algebraMap k K a) := by
    intro x a
    rw [Algebra.smul_def, Derivation.leibniz, D_pow_char_eq_zero p x, smul_zero, zero_add]
  intro n
  induction n with
  | zero =>
      intro t htcard _ g _ x hx
      rw [Nat.le_zero, Finset.card_eq_zero] at htcard
      simp [htcard] at hx
  | succ n IH =>
      intro t htcard hts g hg x₀ hx₀
      by_contra hne
      set c : K → k := fun x ↦ (g x₀)⁻¹ * g x with hc
      have hc0 : c x₀ = 1 := inv_mul_cancel₀ hne
      have hsum : (∑ x ∈ t, c x • x ^ p) = 0 := by
        simp only [hc, mul_smul, ← Finset.smul_sum, hg, smul_zero]
      have key : KaehlerDifferential.mapBaseChange ℤ k K
          (∑ x ∈ t.erase x₀, (x ^ p) ⊗ₜ[k] KaehlerDifferential.D ℤ k (c x)) = 0 := by
        rw [Finset.sum_erase _ (by simp [hc0]), map_sum]
        simp only [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, ← hterm]
        rw [← map_sum, hsum, map_zero]
      have hind : ∀ g' : K → k, (∑ x ∈ t.erase x₀, g' x • x ^ p) = 0 →
          ∀ x ∈ t.erase x₀, g' x = 0 :=
        IH (t.erase x₀) (by rw [Finset.card_erase_of_mem hx₀]; omega)
          (fun x hx ↦ hts (Finset.erase_subset _ _ hx))
      have hD : ∀ x ∈ t.erase x₀, KaehlerDifferential.D ℤ k (c x) = 0 := by
        have h0 : (∑ x ∈ t.erase x₀, (x ^ p) ⊗ₜ[k] KaehlerDifferential.D ℤ k (c x)) = 0 :=
          h (by rw [key, map_zero])
        exact fun x hx ↦ eq_zero_of_sum_tmul_eq_zero (t.erase x₀) (fun x : K ↦ x ^ p) hind
          (fun x ↦ KaehlerDifferential.D ℤ k (c x)) h0 hx
      have hpow : ∀ x ∈ t, ∃ b : k, b ^ p = c x := by
        intro x hx
        rcases eq_or_ne x x₀ with rfl | hxx
        · exact ⟨1, by simp [hc0]⟩
        · exact exists_pow_eq_of_D_eq_zero p (hD x (Finset.mem_erase.mpr ⟨hxx, hx⟩))
      choose! b hb using hpow
      have hzero : (∑ x ∈ t, b x • x) ^ p = 0 := by
        rw [sum_pow_char, ← hsum]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rw [Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow, hb x hx]
      have hb0 : ∀ x ∈ t, b x = 0 :=
        linearIndepOn_iff'.mp hs t b hts (by simpa using pow_eq_zero_iff hp.ne_zero |>.mp hzero)
      have := hb x₀ hx₀
      rw [hb0 x₀ hx₀, zero_pow hp.ne_zero, hc0] at this
      exact zero_ne_one this

/-- If `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective and `k` has characteristic `p`, then the `p`-th
powers of a `k`-linearly independent subset of `K` are `k`-linearly independent. -/
private lemma linearIndepOn_pow_of_injective_mapBaseChange {k K : Type*} [Field k] [Field K]
    [Algebra k K] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K)) (s : Finset K)
    (hs : LinearIndepOn k _root_.id (s : Set K)) : LinearIndepOn k (· ^ p) (s : Set K) :=
  linearIndepOn_iff'.mpr fun t g hts hg x hx ↦
    eq_zero_of_sum_smul_pow_eq_zero p h s hs t.card t le_rfl hts g hg x hx

/-! ### Descent of a relation to a finitely generated subextension -/

section Descent

/-- The `A`-linear map `(A →₀ A) → (B →₀ B)` induced by `algebraMap A B` on both the index set and
the coefficients. -/
private noncomputable abbrev finsuppMap (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    (A →₀ A) →ₗ[A] (B →₀ B) :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
    (Finsupp.lmapDomain A A (algebraMap A B))

private lemma finsuppMap_single {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (a x : A) :
    finsuppMap A B (Finsupp.single a x) =
      Finsupp.single (algebraMap A B a) (algebraMap A B x) := by
  simp [finsuppMap]

private lemma injective_finsuppMap (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Injective (algebraMap A B)) : Function.Injective (finsuppMap A B) := by
  intro x y hxy
  simp only [finsuppMap, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.lmapDomain_apply] at hxy
  exact Finsupp.mapDomain_injective h (Finsupp.mapRange_injective _ (map_zero _) h hxy)

private lemma finsuppMap_comp (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra C B] [Algebra A B] [IsScalarTower A C B] (f : A →₀ A) :
    finsuppMap C B (finsuppMap A C f) = finsuppMap A B f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single a b =>
      rw [finsuppMap_single, finsuppMap_single, finsuppMap_single,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- For a relation `x` in the presentation of `Ω_{B/𝐙}` there is a finite subset `E` of `B` such
that `x` is the image of a relation in the presentation of `Ω_{C/𝐙}` for every ring `C` over which
`B` is an algebra and whose image in `B` contains `E`. -/
private lemma exists_finset_descends {B : Type v} [Field B] {x : B →₀ B}
    (hx : x ∈ KaehlerDifferential.kerTotal ℤ B) :
    ∃ E : Finset B, ∀ (C : Type v) [CommRing C] [Algebra C B],
      (↑E ⊆ Set.range (algebraMap C B)) →
        ∃ y ∈ KaehlerDifferential.kerTotal ℤ C, finsuppMap C B y = x := by
  classical
  rw [KaehlerDifferential.kerTotal] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      rcases hz with (⟨⟨a, b⟩, rfl⟩ | ⟨⟨a, b⟩, rfl⟩) | ⟨n, rfl⟩
      rotate_right
      · exact ⟨∅, fun C _ _ _ => ⟨Finsupp.single (algebraMap ℤ C n) 1,
          Submodule.subset_span (Or.inr ⟨n, rfl⟩), by simp [finsuppMap_single]⟩⟩
      all_goals
        refine ⟨{a, b}, fun C _ _ hEC => ?_⟩
        obtain ⟨a', rfl⟩ : a ∈ Set.range (algebraMap C B) := hEC (by simp)
        obtain ⟨b', rfl⟩ : b ∈ Set.range (algebraMap C B) := hEC (by simp)
      · exact ⟨_, Submodule.subset_span (Or.inl (Or.inl ⟨(a', b'), rfl⟩)), by
          simp only [map_sub, map_add, finsuppMap_single, map_one]⟩
      · exact ⟨_, Submodule.subset_span (Or.inl (Or.inr ⟨(a', b'), rfl⟩)), by
          simp only [map_sub, map_add, finsuppMap_single, map_one, map_mul]⟩
  | zero => exact ⟨∅, fun C _ _ _ => ⟨0, zero_mem _, map_zero _⟩⟩
  | add z w _ _ hz hw =>
      obtain ⟨E₁, h₁⟩ := hz
      obtain ⟨E₂, h₂⟩ := hw
      refine ⟨E₁ ∪ E₂, fun C _ _ hEC => ?_⟩
      rw [Finset.coe_union, Set.union_subset_iff] at hEC
      obtain ⟨y₁, hy₁, hy₁'⟩ := h₁ C hEC.1
      obtain ⟨y₂, hy₂, hy₂'⟩ := h₂ C hEC.2
      exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, hy₁', hy₂']⟩
  | smul c z _ hz =>
      obtain ⟨E₁, h₁⟩ := hz
      refine ⟨insert c E₁, fun C _ _ hEC => ?_⟩
      rw [Finset.coe_insert, Set.insert_subset_iff] at hEC
      obtain ⟨c', rfl⟩ := hEC.1
      obtain ⟨y₁, hy₁, hy₁'⟩ := h₁ C hEC.2
      exact ⟨c' • y₁, Submodule.smul_mem _ _ hy₁, by rw [map_smul, hy₁', algebraMap_smul]⟩

/-- If a differential of `A` dies in `Ω_{B/𝐙}`, it dies already in `Ω_{C/𝐙}` for every intermediate
field `C` whose image in `B` contains a suitable finite subset of `B`. -/
private lemma exists_finset_map_eq_zero {A : Type u} {B : Type v} [Field A] [Field B] [Algebra A B]
    (η : Ω[A⁄ℤ]) (h : KaehlerDifferential.map ℤ ℤ A B η = 0) :
    ∃ E : Finset B, ∀ (C : Type v) [Field C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
      (↑E ⊆ Set.range (algebraMap C B)) → KaehlerDifferential.map ℤ ℤ A C η = 0 := by
  rw [← LinearMap.mem_ker, KaehlerDifferential.ker_map] at h
  obtain ⟨f, hf, hfη⟩ := h
  rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.restrictScalars_mem] at hf
  obtain ⟨E, hE⟩ := exists_finset_descends hf
  refine ⟨E, fun C _ _ _ _ hEC => ?_⟩
  obtain ⟨y, hy, hy'⟩ := hE C hEC
  rw [← LinearMap.mem_ker, KaehlerDifferential.ker_map]
  refine ⟨f, ?_, hfη⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.restrictScalars_mem]
  have hfy : finsuppMap A C f = y :=
    injective_finsuppMap C B (FaithfulSMul.algebraMap_injective C B)
      (by rw [finsuppMap_comp, hy'])
  rwa [hfy]

end Descent

/-! ### The two implications -/

@[ega "0 20.6.3" "Sufficiency"]
private lemma isSeparableExtension_of_injective_mapBaseChange (k K : Type*) [Field k] [Field K]
    [Algebra k K] (h : Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K)) :
    Algebra.IsSeparableExtension k K := by
  refine ⟨fun K' _ ↦ ?_⟩
  have h' : Function.Injective (KaehlerDifferential.mapBaseChange ℤ k ↥K') :=
    injective_mapBaseChange_of_le k ↥K' K h
  refine ⟨?_⟩
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨t, ht, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k ↥K'
    exact ⟨(t : Set ↥K'), ht, hsep⟩
  · have : ExpChar k p := .prime hp.out
    have : CharP ↥K' p := .of_ringHom_of_ne_zero (algebraMap k ↥K') p hp.out.ne_zero
    obtain ⟨t, ht, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
        (k := k) (K := ↥K') p hp.out
        (fun s hs ↦ linearIndepOn_pow_of_injective_mapBaseChange p h' s hs)
    exact ⟨(t : Set ↥K'), ht, hsep⟩

@[ega "0 20.6.3" "Necessity"]
private lemma injective_mapBaseChange_of_isSeparableExtension (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparableExtension k K] :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  rw [LinearMap.mem_ker] at hξ
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset ξ
  set s : Finset K := T.image Prod.fst with hs
  set K' : IntermediateField k K := IntermediateField.adjoin k (s : Set K) with hK'
  have hmem : ∀ x ∈ s, x ∈ K' := fun x hx ↦ IntermediateField.subset_adjoin k _ hx
  set ξ' : ↥K' ⊗[k] Ω[k⁄ℤ] :=
    ∑ i ∈ T.attach,
      (⟨i.1.1, hmem _ (Finset.mem_image_of_mem Prod.fst i.2)⟩ : ↥K') ⊗ₜ[k] i.1.2 with hξ'
  have hincl : incl k ↥K' K ξ' = ξ := by
    rw [hξ', map_sum, hT, ← Finset.sum_attach T fun i ↦ i.1 ⊗ₜ[k] i.2]
    rfl
  set η : Ω[↥K'⁄ℤ] := KaehlerDifferential.mapBaseChange ℤ k ↥K' ξ' with hη
  have hηK : KaehlerDifferential.map ℤ ℤ ↥K' K η = 0 := by
    rw [hη, ← mapBaseChange_incl k ↥K' K ξ', hincl, hξ]
  obtain ⟨E, hE⟩ := exists_finset_map_eq_zero η hηK
  set K'' : IntermediateField k K := IntermediateField.adjoin k ((s ∪ E : Finset K) : Set K)
    with hK''
  have hle : K' ≤ K'' :=
    IntermediateField.adjoin.mono k _ _ (by simp)
  let : Algebra ↥K' ↥K'' := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower ↥K' ↥K'' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k ↥K' ↥K'' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.EssFiniteType k ↥K'' := IntermediateField.essFiniteType_iff.mpr ⟨s ∪ E, rfl⟩
  have hErange : (↑E : Set K) ⊆ Set.range (algebraMap ↥K'' K) := fun x hx ↦
    ⟨⟨x, IntermediateField.subset_adjoin k _ (by simpa using Or.inr hx)⟩, rfl⟩
  have h2 := hE ↥K'' hErange
  have h3 : incl k ↥K' ↥K'' ξ' = 0 :=
    injective_mapBaseChange_of_isSeparablyGenerated k ↥K'' (by
      rw [mapBaseChange_incl k ↥K' ↥K'' ξ', ← hη, h2, map_zero])
  have h4 : ξ' = 0 := injective_incl k ↥K' ↥K'' (by rw [h3, map_zero])
  rw [← hincl, h4, map_zero]

/-! ### Stacks Tag 031X -/

/-- A field extension `K/k` is separable in the sense of `Algebra.IsSeparableExtension` if and only
if the canonical map `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective. -/
public theorem solution (k K : Type*) [Field k] [Field K] [Algebra k K] :
    Algebra.IsSeparableExtension k K ↔
      Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) :=
  ⟨fun _ ↦ injective_mapBaseChange_of_isSeparableExtension k K,
    isSeparableExtension_of_injective_mapBaseChange k K⟩

end Stacks.KaehlerDifferential.Separability

end

@[expose] public section

/-- A field extension `K/k` is separable in the sense of `Algebra.IsSeparableExtension` if and only
if the canonical map `K ⊗_k Ω_{k/𝐙} → Ω_{K/𝐙}` is injective. -/
@[stacks 031X "Differentials are taken over `𝐙`, which for a field of characteristic `p` is the
source's `𝐅_p`, and the characteristic hypothesis is dropped: both conditions hold outright in
characteristic zero, and the consumers (Lemmas 031Y, 0321 and Proposition 0322) are stated for all
characteristics. See the module docstring.", ega "0 20.6.3"]
public theorem Algebra.isSeparableExtension_iff_injective_mapBaseChange (k K : Type*) [Field k]
    [Field K] [Algebra k K] :
    Algebra.IsSeparableExtension k K ↔
      Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) :=
  Stacks.KaehlerDifferential.Separability.solution k K

end
