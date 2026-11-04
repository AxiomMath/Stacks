module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# Exactness of the glueing complex at its second term

Let `R → S` be flat, inducing an isomorphism `R / I ≅ S / IS` for `I = (f₁, …, f_t)`, and let
`M` be an `R`-module. `FormalGlueing.glueingComplex_exact` shows that the glueing complex

`M → (M ⊗[R] S) × ∏ i, M_{f i} → (∏ i, (M ⊗[R] S)_{f i}) × (∏ i < j, M_{f i f j}) → ⋯`

is exact at its first two terms. This file proves exactness at the third term: a pair
`(a, b)` with `δ a = b ⊗ 1` and `δ b = 0` lies in the image of `FormalGlueing.glueingBeta`.

The proof is the comparison of Čech cohomology of `M` and of `M ⊗[R] S` on the cover of
`D(I)` by the `D(f i)`: the cohomology classes of the Čech complex of `M` are `I`-power torsion,
the Čech complex of `M ⊗[R] S` is the base change of that of `M`, and base change does not change
an `I`-power torsion module.

## Main results

* `FormalGlueing.exists_pow_smul_eq_glueingDifferential`: every two-cocycle becomes a coboundary
  after multiplication by a power of any `f i`.
* `FormalGlueing.glueingComplex_exact_two`: exactness of the glueing complex at its third term.
-/

@[expose] public section

namespace FormalGlueing

open TensorProduct Cech

universe u v w w'

open _root_.IPowerTorsion (unitMap)

section Torsion

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If `x` is a torsion class modulo the range of `φ` and `x ⊗ 1` is the image of some `y`,
then `x` is in the range of `φ`, and `y` differs from the corresponding base change by an
element coming from the kernel of `φ`. -/
private lemma exists_lift_of_torsion_quotient
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M : Type w} {N : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    (x : N) (hx : ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n,
      a • (LinearMap.range φ).mkQ x = 0)
    (y : M ⊗[R] S) (hy : φ.rTensor S y = unitMap R S N x) :
    ∃ m : M, φ m = x ∧ ∃ w : LinearMap.ker φ ⊗[R] S,
      y - unitMap R S M m = (LinearMap.ker φ).subtype.rTensor S w := by
  let := hflat
  let q := (LinearMap.range φ).mkQ
  have hqφ : q.comp φ = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩
  have hqx : unitMap R S (N ⧸ LinearMap.range φ) (q x) = 0 := by
    calc
      _ = q.rTensor S (unitMap R S N x) := by simp [unitMap]
      _ = q.rTensor S (φ.rTensor S y) := by rw [hy]
      _ = 0 := by rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hqφ]; simp
  have hx0 := unitMap_eq_zero_of_torsion I hflat hq (q x) hx hqx
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  have hd : φ.rTensor S (y - unitMap R S M m) = 0 := by
    rw [map_sub, hy]
    simp [unitMap, hm]
  obtain ⟨z, hz⟩ := (Module.Flat.rTensor_exact S φ.exact_subtype_ker_map)
    (y - unitMap R S M m) |>.mp hd
  exact ⟨m, hm, z, hz.symm⟩

/-- An element of `Z ⊗[R] S` is the sum of a base change of an element of `Z` and of an
element coming from `M ⊗[R] S`, as soon as `Z / M` is `I`-power torsion. -/
private lemma exists_decomp_of_torsion_coker
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M : Type w} {Z : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup Z] [Module R Z] (φ : M →ₗ[R] Z)
    (htors : IsIPowerTorsion R (Z ⧸ LinearMap.range φ) I)
    (w : Z ⊗[R] S) :
    ∃ y : M ⊗[R] S, ∃ z : Z, w = φ.rTensor S y + unitMap R S Z z := by
  let q := (LinearMap.range φ).mkQ
  obtain ⟨c, hc⟩ := (unitMap_bijective_of_torsion I hflat hq _ htors).2 (q.rTensor S w)
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ c
  have hex : Function.Exact (φ.rTensor S) (q.rTensor S) :=
    rTensor_exact S (LinearMap.exact_map_mkQ_range φ) (Submodule.mkQ_surjective _)
  have h0 : q.rTensor S (w - unitMap R S Z z) = 0 := by
    rw [map_sub, ← hc]
    simp [unitMap, q]
  obtain ⟨y, hy⟩ := (hex _).mp h0
  exact ⟨y, z, by rw [hy]; abel⟩

end Torsion

section Localization

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The base change comparison is natural with respect to the Čech transition maps. -/
private lemma localizationTensorEquiv_cechι
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type v) [AddCommGroup N] [Module R N] {s t : Finset (Fin r)} (h : s ⊆ t)
    (x : cechMod f M s) (n : N) :
    localizationTensorEquiv (cechSub f t) M N (cechι f M h x ⊗ₜ n) =
      cechι f (M ⊗[R] N) h (localizationTensorEquiv (cechSub f s) M N (x ⊗ₜ n)) := by
  have hlin : ((localizationTensorEquiv (cechSub f t) M N).toLinearMap ∘ₗ
      (TensorProduct.mk R _ N).flip n ∘ₗ cechι f M h) =
      (cechι f (M ⊗[R] N) h ∘ₗ (localizationTensorEquiv (cechSub f s) M N).toLinearMap ∘ₗ
        (TensorProduct.mk R _ N).flip n) := by
    refine IsLocalizedModule.ext (cechSub f s) (LocalizedModule.mkLinearMap (cechSub f s) M)
      (isUnit_algebraMap f (M ⊗[R] N) h (LocalizedModule.mkLinearMap (cechSub f t) _)) ?_
    ext m
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.flip_apply]
    rw [cechι_mk, localizationTensorEquiv_mk_tmul, localizationTensorEquiv_mk_tmul, cechι_mk]
  exact LinearMap.congr_fun hlin x

private lemma glueingTermTensorEquiv_tmul
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type v) [AddCommGroup N] [Module R N] (p : ℕ) (x : GlueingTerm f M p) (n : N)
    (s : {s : Finset (Fin r) // s.card = p}) :
    glueingTermTensorEquiv f M N p (x ⊗ₜ n) s =
      localizationTensorEquiv (cechSub f s.val) M N (x s ⊗ₜ n) := by
  simp [glueingTermTensorEquiv]

private lemma glueingTermTensorEquiv_unitMap
    (M : Type w) [AddCommGroup M] [Module R M]
    (S : Type v) [CommRing S] [Algebra R S] (p : ℕ) (x : GlueingTerm f M p) :
    glueingTermTensorEquiv f M S p (unitMap R S _ x) = localizationTensorMap S f M p x := by
  funext s
  simp [glueingTermTensorEquiv, unitMap, localizationTensorMap,
    localizationTensorEquiv_unit]

/-- The components of the Čech differential. -/
public lemma glueingDifferential_apply_component {M : Type w} [AddCommGroup M] [Module R M]
    (p : ℕ) (x : GlueingTerm f M p) (T : {s : Finset (Fin r) // s.card = p + 1}) :
    glueingDifferential f M p x T = ∑ k ∈ T.1.attach,
      cechSign T.1 k • cechι f M (show (eraseIndex p T k).1 ⊆ T.1 from Finset.erase_subset _ _)
        (x (eraseIndex p T k)) := by
  simp only [glueingDifferential, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

/-- The base change comparison intertwines the Čech differentials. -/
private lemma glueingTermTensorEquiv_differential
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type v) [AddCommGroup N] [Module R N] (p : ℕ) (z : GlueingTerm f M p ⊗[R] N) :
    glueingTermTensorEquiv f M N (p + 1) ((glueingDifferential f M p).rTensor N z) =
      glueingDifferential f (M ⊗[R] N) p (glueingTermTensorEquiv f M N p z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n =>
    funext T
    rw [LinearMap.rTensor_tmul, glueingTermTensorEquiv_tmul, glueingDifferential_apply_component,
      glueingDifferential_apply_component, TensorProduct.sum_tmul, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show ∀ (c : ℤ) (y : cechMod f M T.1), (c • y) ⊗ₜ[R] n = c • (y ⊗ₜ[R] n) from
      fun c y ↦ map_zsmul ((TensorProduct.mk R (cechMod f M T.1) N).flip n) c y,
      map_zsmul, glueingTermTensorEquiv_tmul]
    congr 1
    exact localizationTensorEquiv_cechι f M N _ _ n
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Localization

section Cocycles

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Elements of the submonoid of a subset act injectively on the localization at a larger
subset. -/
private lemma smul_injective_cechMod {s t : Finset (Fin r)} (h : s ⊆ t) (c : R)
    (hc : c ∈ cechSub f s) : Function.Injective (fun x : cechMod f M t ↦ c • x) :=
  ((Module.End.isUnit_iff _).mp
    (isUnit_algebraMap f M h (LocalizedModule.mkLinearMap (cechSub f t) M) ⟨c, hc⟩)).1

private lemma prod_insert_dvd (a : Fin r) (s : Finset (Fin r)) :
    ∏ i ∈ insert a s, f i ∣ f a * ∏ i ∈ s, f i := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    exact dvd_mul_left _ _
  · rw [Finset.prod_insert ha]

/-- The kernel of the transition map `M_s → M_t`, `t ⊆ insert a s`, is `f a`-power torsion. -/
public lemma exists_pow_smul_eq_zero_of_cechι_eq_zero (a : Fin r) {s t : Finset (Fin r)}
    (h : s ⊆ t) (ht : t ⊆ insert a s) (z : cechMod f M s) (hz : cechι f M h z = 0) :
    ∃ n : ℕ, f a ^ n • z = 0 := by
  obtain ⟨⟨m, c⟩, hmc⟩ := IsLocalizedModule.surj (cechSub f s)
    (LocalizedModule.mkLinearMap (cechSub f s) M) z
  simp only at hmc
  have h1 : LocalizedModule.mkLinearMap (cechSub f t) M m = 0 := by
    rw [← cechι_mk f M h, ← hmc, Submonoid.smul_def, map_smul, hz, smul_zero]
  obtain ⟨⟨d, hd⟩, hdm⟩ := (IsLocalizedModule.eq_zero_iff (cechSub f t)
    (LocalizedModule.mkLinearMap (cechSub f t) M)).mp h1
  obtain ⟨n, rfl⟩ := hd
  simp only [Submonoid.smul_def] at hdm
  obtain ⟨q, hq⟩ := prod_insert_dvd f a s
  obtain ⟨q', hq'⟩ := Finset.prod_dvd_prod_of_subset _ _ f ht
  have hkill : (∏ i ∈ s, f i) ^ n • (f a ^ n • m) = 0 := by
    rw [smul_smul, ← mul_pow, mul_comm, hq, hq', show
      ((∏ i ∈ t, f i) * q' * q) ^ n = (q' * q) ^ n * (∏ i ∈ t, f i) ^ n by ring,
      mul_smul, hdm, smul_zero]
  have h2 : LocalizedModule.mkLinearMap (cechSub f s) M (f a ^ n • m) = 0 :=
    (IsLocalizedModule.eq_zero_iff (cechSub f s) _).mpr ⟨⟨_, n, rfl⟩, hkill⟩
  refine ⟨n, smul_injective_cechMod f (le_refl s) c.1 c.2 ?_⟩
  simp only [smul_zero]
  rw [smul_comm, ← Submonoid.smul_def, hmc, ← map_smul, h2]

/-- Every element of `M_{insert a s}` is, up to a power of `f a`, the image of an element of
`M_s`. -/
public lemma exists_cechι_eq_pow_smul (a : Fin r) (s : Finset (Fin r))
    (w : cechMod f M (insert a s)) :
    ∃ e : ℕ, ∃ z : cechMod f M s, cechι f M (Finset.subset_insert a s) z = f a ^ e • w := by
  obtain ⟨⟨m, c⟩, hmc⟩ := IsLocalizedModule.surj (cechSub f (insert a s))
    (LocalizedModule.mkLinearMap (cechSub f (insert a s)) M) w
  obtain ⟨e, he⟩ := c.2
  simp only at hmc
  obtain ⟨q, hq⟩ := prod_insert_dvd f a s
  let u : cechSub f s := ⟨(∏ i ∈ s, f i) ^ e, e, rfl⟩
  refine ⟨e, LocalizedModule.mk (q ^ e • m) u, ?_⟩
  have hmk : (∏ i ∈ s, f i) ^ e • LocalizedModule.mk (q ^ e • m) u =
      LocalizedModule.mkLinearMap (cechSub f s) M (q ^ e • m) := by
    rw [LocalizedModule.smul'_mk]
    show LocalizedModule.mk (u • (q ^ e • m)) u = _
    rw [LocalizedModule.mk_cancel]
    rfl
  apply smul_injective_cechMod f (Finset.subset_insert a s) ((∏ i ∈ s, f i) ^ e) ⟨e, rfl⟩
  simp only
  rw [← map_smul, hmk, cechι_mk, map_smul, ← hmc, Submonoid.smul_def, ← he, smul_smul,
    smul_smul, show q ^ e * (∏ i ∈ insert a s, f i) ^ e = (∏ i ∈ s, f i) ^ e * f a ^ e by
      rw [← mul_pow, ← mul_pow, mul_comm q, ← hq, mul_comm]]

/-- On a three-element index set `{i, j, l}` with `i < j < l`, the Čech differential of a
degree-two term is the alternating sum of the restrictions of its components at
`{j, l}`, `{i, l}` and `{i, j}`. -/
public theorem glueingDifferential_two_apply (x : GlueingTerm f M 2)
    (T : {s : Finset (Fin r) // s.card = 3}) {i j l : Fin r} (hij : i < j) (hjl : j < l)
    (hT : T.1 = {i, j, l}) (u₁ u₂ u₃ : {s : Finset (Fin r) // s.card = 2})
    (h₁ : u₁.1 = {j, l}) (h₂ : u₂.1 = {i, l}) (h₃ : u₃.1 = {i, j})
    (hs₁ : u₁.1 ⊆ T.1) (hs₂ : u₂.1 ⊆ T.1) (hs₃ : u₃.1 ⊆ T.1) :
    glueingDifferential f M 2 x T =
      cechι f M hs₁ (x u₁) - cechι f M hs₂ (x u₂) + cechι f M hs₃ (x u₃) := by
  obtain ⟨T, hT3⟩ := T
  simp only at hT
  subst hT
  let a : ({i, j, l} : Finset (Fin r)) := ⟨i, by simp⟩
  let b : ({i, j, l} : Finset (Fin r)) := ⟨j, by simp⟩
  let c : ({i, j, l} : Finset (Fin r)) := ⟨l, by simp⟩
  have hab : a ≠ b := fun h ↦ (ne_of_lt hij) (congrArg Subtype.val h)
  have hac : a ≠ c := fun h ↦ (hij.trans hjl).ne (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h ↦ (ne_of_lt hjl) (congrArg Subtype.val h)
  have hTa : ({i, j, l} : Finset (Fin r)).attach = {a, b, c} := by
    ext k
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases k with ⟨k, hk⟩
    rcases (show k = i ∨ k = j ∨ k = l by simpa using hk) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hsi : cechSign ({i, j, l} : Finset (Fin r)) i = 1 := by
    have : ({i, j, l} : Finset (Fin r)).filter (· < i) = ∅ := by
      ext k; simp; omega
    simp [cechSign, this]
  have hsj : cechSign ({i, j, l} : Finset (Fin r)) j = -1 := by
    have : ({i, j, l} : Finset (Fin r)).filter (· < j) = {i} := by
      ext k; simp; omega
    simp [cechSign, this]
  have hsl : cechSign ({i, j, l} : Finset (Fin r)) l = 1 := by
    have : ({i, j, l} : Finset (Fin r)).filter (· < l) = {i, j} := by
      ext k; simp; omega
    simp [cechSign, this, Finset.card_pair (ne_of_lt hij)]
  rw [glueingDifferential_apply_component]
  simp only
  rw [hTa, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  have ea : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ a).1 = u₁.1 := by
    rw [h₁]; ext k; simp [eraseIndex, a]; omega
  have eb : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ b).1 = u₂.1 := by
    rw [h₂]; ext k; simp [eraseIndex, b]; omega
  have ec : (eraseIndex 2 ⟨{i, j, l}, hT3⟩ c).1 = u₃.1 := by
    rw [h₃]; ext k; simp [eraseIndex, c]; omega
  rw [restricted_component_congr f x (Subtype.ext ea) _ hs₁,
    restricted_component_congr f x (Subtype.ext eb) _ hs₂,
    restricted_component_congr f x (Subtype.ext ec) _ hs₃]
  simp only [a, b, c, hsi, hsj, hsl, one_smul, neg_smul]
  abel

private lemma cechSign_pair_of_lt {a j : Fin r} (h : a < j) :
    cechSign (insert a ({j} : Finset (Fin r))) a = 1 := by
  have : (insert a ({j} : Finset (Fin r))).filter (· < a) = ∅ := by
    ext k; simp; omega
  simp [cechSign, this]

private lemma cechSign_pair_of_gt {a j : Fin r} (h : j < a) :
    cechSign (insert a ({j} : Finset (Fin r))) a = -1 := by
  have : (insert a ({j} : Finset (Fin r))).filter (· < a) = {j} := by
    ext k; simp; omega
  simp [cechSign, this]

private lemma cechι_pair_eq_of_cocycle (b : GlueingTerm f M 2)
    (T : {s : Finset (Fin r) // s.card = 3}) (hcoc : glueingDifferential f M 2 b T = 0)
    {a i j : Fin r} (hij : i < j) (hai : a ≠ i) (haj : a ≠ j) (hT : T.1 = insert a {i, j})
    (u uaj uai : {s : Finset (Fin r) // s.card = 2}) (hu : u.1 = {i, j})
    (huaj : uaj.1 = insert a {j}) (huai : uai.1 = insert a {i})
    (hsub : u.1 ⊆ T.1) (saj : uaj.1 ⊆ T.1) (sai : uai.1 ⊆ T.1) :
    cechι f M hsub (b u) = cechSign (insert a {j}) a • cechι f M saj (b uaj) -
      cechSign (insert a {i}) a • cechι f M sai (b uai) := by
  rcases lt_or_gt_of_ne (Ne.symm hai) with hia | hai'
  · rcases lt_or_gt_of_ne (Ne.symm haj) with hja | haj'
    · rw [cechSign_pair_of_gt hia, cechSign_pair_of_gt hja]
      rw [glueingDifferential_two_apply f b T hij hja
        (by rw [hT]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        uaj uai u (huaj.trans (Finset.pair_comm a j)) (huai.trans (Finset.pair_comm a i)) hu
        saj sai hsub] at hcoc
      simp only [neg_smul, one_smul]
      rw [← sub_eq_zero, ← hcoc]
      abel
    · rw [cechSign_pair_of_gt hia, cechSign_pair_of_lt haj']
      rw [glueingDifferential_two_apply f b T hia haj'
        (by rw [hT]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        uaj u uai huaj hu (huai.trans (Finset.pair_comm a i)) saj hsub sai] at hcoc
      simp only [neg_smul, one_smul]
      rw [← sub_eq_zero, ← neg_eq_zero, ← hcoc]
      abel
  · rw [cechSign_pair_of_lt hai', cechSign_pair_of_lt (hai'.trans hij)]
    rw [glueingDifferential_two_apply f b T hai' hij hT u uaj uai hu huaj huai
      hsub saj sai] at hcoc
    simp only [one_smul]
    rw [← sub_eq_zero, ← hcoc]
    abel

private lemma cocycle_component_torsion_of_ne (b : GlueingTerm f M 2)
    (hb : glueingDifferential f M 2 b = 0) (a : Fin r) (E : ℕ)
    (z' : ∀ s : {s : Finset (Fin r) // s.card = 1}, a ∉ s.1 → cechMod f M s.1)
    (hz' : ∀ (s : {s : Finset (Fin r) // s.card = 1}) (h : a ∉ s.1)
      (u : {s : Finset (Fin r) // s.card = 2})
      (_ : u.1 = insert a s.1) (hsub : s.1 ⊆ u.1),
      cechι f M hsub (z' s h) = f a ^ E • b u)
    (y : GlueingTerm f M 1)
    (hy : ∀ s, y s = if h : a ∈ s.1 then 0 else cechSign (insert a s.1) a • z' s h)
    {i j : Fin r} (hij : i < j) (ht2 : ({i, j} : Finset (Fin r)).card = 2) (hai : a ≠ i)
    (haj : a ≠ j) (hsj : ({j} : Finset (Fin r)) ⊆ {i, j}) (hsi : ({i} : Finset (Fin r)) ⊆ {i, j}) :
    ∃ m : ℕ, f a ^ m • (cechι f M hsj (y (singletonIndex j)) -
      cechι f M hsi (y (singletonIndex i)) - f a ^ E • b ⟨{i, j}, ht2⟩) = 0 := by
  have hat : a ∉ ({i, j} : Finset (Fin r)) := by simp [hai, haj]
  have hi : a ∉ ({i} : Finset (Fin r)) := by simpa using hai
  have hj : a ∉ ({j} : Finset (Fin r)) := by simpa using haj
  obtain ⟨T, hT⟩ : ∃ T : {s : Finset (Fin r) // s.card = 3}, T.1 = insert a {i, j} :=
    ⟨⟨insert a {i, j}, by rw [Finset.card_insert_of_notMem hat, ht2]⟩, rfl⟩
  have hsub : ({i, j} : Finset (Fin r)) ⊆ T.1 := hT ▸ Finset.subset_insert _ _
  have hk : ∀ k ∈ ({i, j} : Finset (Fin r)), a ≠ k →
      ∃ u : {s : Finset (Fin r) // s.card = 2}, u.1 = insert a {k} ∧
        ∃ (sa : u.1 ⊆ T.1) (sk : ({k} : Finset (Fin r)) ⊆ T.1),
          cechι f M sk (y (singletonIndex k)) =
            cechSign (insert a {k}) a • f a ^ E • cechι f M sa (b u) := by
    intro k hkm hak
    have hk : a ∉ ({k} : Finset (Fin r)) := by simpa using hak
    obtain ⟨u, hu⟩ : ∃ u : {s : Finset (Fin r) // s.card = 2}, u.1 = insert a {k} :=
      ⟨⟨insert a {k}, by rw [Finset.card_insert_of_notMem hk, Finset.card_singleton]⟩, rfl⟩
    have sa : u.1 ⊆ T.1 := by
      rw [hT, hu]
      exact Finset.insert_subset_insert a (Finset.singleton_subset_iff.mpr hkm)
    have sk : ({k} : Finset (Fin r)) ⊆ T.1 := by
      rw [hT]
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem hkm)
    refine ⟨u, hu, sa, sk, ?_⟩
    rw [hy, dif_neg hk, map_zsmul, ← cechι_cechι f M (hu ▸ Finset.subset_insert a {k}) sa,
      hz' (singletonIndex k) hk u hu, map_smul]
  obtain ⟨uaj, huaj, saj, sj, hzj⟩ := hk j (by simp) haj
  obtain ⟨uai, huai, sai, si, hzi⟩ := hk i (by simp) hai
  refine exists_pow_smul_eq_zero_of_cechι_eq_zero f a hsub (le_of_eq hT) _ ?_
  rw [map_sub, map_sub, map_smul, cechι_cechι, cechι_cechι, hzi, hzj,
    cechι_pair_eq_of_cocycle f b T (congrFun hb T) hij hai haj hT ⟨{i, j}, ht2⟩
      uaj uai rfl huaj huai hsub saj sai, smul_sub,
    smul_comm (f a ^ E) (cechSign (insert a {j}) a) (cechι f M saj (b uaj)),
    smul_comm (f a ^ E) (cechSign (insert a {i}) a) (cechι f M sai (b uai)), sub_self]

private lemma cocycle_component_torsion (b : GlueingTerm f M 2)
    (hb : glueingDifferential f M 2 b = 0) (a : Fin r) (E : ℕ)
    (z' : ∀ s : {s : Finset (Fin r) // s.card = 1}, a ∉ s.1 → cechMod f M s.1)
    (hz' : ∀ (s : {s : Finset (Fin r) // s.card = 1}) (h : a ∉ s.1)
      (u : {s : Finset (Fin r) // s.card = 2})
      (_ : u.1 = insert a s.1) (hsub : s.1 ⊆ u.1),
      cechι f M hsub (z' s h) = f a ^ E • b u)
    (y : GlueingTerm f M 1)
    (hy : ∀ s, y s = if h : a ∈ s.1 then 0 else cechSign (insert a s.1) a • z' s h) :
    ∀ i j : Fin r, i < j → ∀ t : {s : Finset (Fin r) // s.card = 2}, t.1 = {i, j} →
      ∃ m : ℕ, f a ^ m • (glueingDifferential f M 1 y t - f a ^ E • b t) = 0 := by
  classical
  intro i j hij t ht
  obtain ⟨t, ht2⟩ := t
  simp only at ht
  subst ht
  rw [glueingDifferential_apply_pair f y hij]
  have hyi : a ∈ ({i} : Finset (Fin r)) → y (singletonIndex i) = 0 := fun h ↦ by rw [hy, dif_pos h]
  have hyj : a ∈ ({j} : Finset (Fin r)) → y (singletonIndex j) = 0 := fun h ↦ by rw [hy, dif_pos h]
  by_cases hai : a = i
  · subst hai
    refine ⟨0, ?_⟩
    have hj : a ∉ ({j} : Finset (Fin r)) := by simpa using (ne_of_lt hij)
    have hyj' : y (singletonIndex j) = z' (singletonIndex j) hj := by
      simp only [hy, dif_neg hj, cechSign_pair_of_lt hij, one_smul]
    rw [hyi (by simp), hyj', map_zero, sub_zero,
      hz' (singletonIndex j) hj ⟨{a, j}, ht2⟩ rfl, sub_self, smul_zero]
  by_cases haj : a = j
  · subst haj
    refine ⟨0, ?_⟩
    have hi : a ∉ ({i} : Finset (Fin r)) := by simpa using (ne_of_lt hij).symm
    have hyi' : y (singletonIndex i) = -z' (singletonIndex i) hi := by
      simp only [hy, dif_neg hi, cechSign_pair_of_gt hij, neg_smul, one_smul]
    rw [hyj (by simp), hyi', map_zero, map_neg, zero_sub, neg_neg,
      hz' (singletonIndex i) hi ⟨{i, a}, ht2⟩ (Finset.pair_comm _ _), sub_self, smul_zero]
  exact cocycle_component_torsion_of_ne f b hb a E z' hz' y hy hij ht2 hai haj _ _

/-- Every Čech two-cocycle becomes a coboundary after multiplication by a power of any `f a`. -/
public theorem exists_pow_smul_eq_glueingDifferential (b : GlueingTerm f M 2)
    (hb : glueingDifferential f M 2 b = 0) (a : Fin r) :
    ∃ n : ℕ, ∃ y : GlueingTerm f M 1, f a ^ n • b = glueingDifferential f M 1 y := by
  classical
  have hA : ∀ s : {s : Finset (Fin r) // s.card = 1}, ∀ ha : a ∉ s.1, ∃ e : ℕ,
      ∃ z : cechMod f M s.1, cechι f M (Finset.subset_insert a s.1) z =
        f a ^ e • b ⟨insert a s.1, by rw [Finset.card_insert_of_notMem ha, s.2]⟩ :=
    fun s ha ↦ exists_cechι_eq_pow_smul f a s.1 _
  choose e z hz using hA
  let E : ℕ := ∑ s : {s : Finset (Fin r) // s.card = 1}, if h : a ∈ s.1 then 0 else e s h
  have heE : ∀ (s : {s : Finset (Fin r) // s.card = 1}) (h : a ∉ s.1), e s h ≤ E :=
    fun s h ↦ by
      simpa only [dif_neg h] using Finset.single_le_sum
        (f := fun s : {s : Finset (Fin r) // s.card = 1} ↦ if h : a ∈ s.1 then 0 else e s h)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ s)
  let z' : ∀ s : {s : Finset (Fin r) // s.card = 1}, a ∉ s.1 → cechMod f M s.1 :=
    fun s h ↦ f a ^ (E - e s h) • z s h
  have hz' : ∀ (s : {s : Finset (Fin r) // s.card = 1}) (h : a ∉ s.1)
      (u : {s : Finset (Fin r) // s.card = 2})
      (_ : u.1 = insert a s.1) (hsub : s.1 ⊆ u.1),
      cechι f M hsub (z' s h) = f a ^ E • b u := by
    intro s h u hu hsub
    obtain ⟨u, hu2⟩ := u
    simp only at hu
    subst hu
    simp only [z', map_smul, hz, smul_smul, ← pow_add, Nat.sub_add_cancel (heE s h)]
  let y : GlueingTerm f M 1 := fun s ↦
    if h : a ∈ s.1 then 0 else cechSign (insert a s.1) a • z' s h
  have key := cocycle_component_torsion f b hb a E z' hz' y (fun _ ↦ rfl)
  have key' : ∀ t : {s : Finset (Fin r) // s.card = 2},
      ∃ m : ℕ, f a ^ m • (glueingDifferential f M 1 y t - f a ^ E • b t) = 0 := by
    intro t
    obtain ⟨i, j, hij, ht⟩ := Finset.card_eq_two.mp t.2
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h t ht
    · exact key j i h t (ht.trans (Finset.pair_comm i j))
  choose m hm using key'
  let K : ℕ := ∑ t, m t
  have hK : f a ^ K • (glueingDifferential f M 1 y - f a ^ E • b) = 0 := by
    funext t
    have hle : m t ≤ K := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)
    show f a ^ K • (glueingDifferential f M 1 y t - f a ^ E • b t) = 0
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hm t, smul_zero]
  refine ⟨K + E, f a ^ K • y, ?_⟩
  rw [smul_sub, sub_eq_zero] at hK
  rw [map_smul, pow_add, mul_smul, hK]

end Cocycles

section Main

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M]

private lemma glueingDifferential_localizationDiagonal (m : M) :
    glueingDifferential f M 1 (localizationDiagonal f M m) = 0 := by
  simpa [glueingBeta, glueingAlpha] using
    congrArg Prod.snd (LinearMap.congr_fun (glueingBeta_comp_glueingAlpha R f M) m)

/-- **Exactness of the glueing complex at its third term.** If `R → S` is flat and induces an
isomorphism modulo the ideal generated by `f`, then every pair `(a, b)` with `δ a = b ⊗ 1` and
`δ b = 0` is the image under `FormalGlueing.glueingBeta` of a pair `(y, x)`, that is
`a = (y / 1 - x_i ⊗ 1)_i` and `b = (x_i - x_j)_{i < j}`. -/
public theorem glueingComplex_exact_two
    (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (a : GlueingTerm f (M ⊗[R] S) 1) (b : GlueingTerm f M 2)
    (hab : glueingDifferential f (M ⊗[R] S) 1 a = localizationTensorMap S f M 2 b)
    (hb : glueingDifferential f M 2 b = 0) :
    ∃ yx, glueingBeta S f M yx = (a, b) := by
  classical
  let I := Ideal.span (Set.range f)
  let ã := (glueingTermTensorEquiv f M S 1).symm a
  have hã : (glueingDifferential f M 1).rTensor S ã = unitMap R S _ b := by
    apply (glueingTermTensorEquiv f M S 2).injective
    rw [glueingTermTensorEquiv_differential, glueingTermTensorEquiv_unitMap,
      LinearEquiv.apply_symm_apply, hab]
  have htors : ∃ n : ℕ, 0 < n ∧ ∀ c ∈ I ^ n,
      c • (LinearMap.range (glueingDifferential f M 1)).mkQ b = 0 := by
    apply exists_pow_annihilator_of_generators
    intro i
    obtain ⟨n, y, hy⟩ := exists_pow_smul_eq_glueingDifferential f b hb i
    exact ⟨n, by rw [← map_smul, hy]; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩⟩
  obtain ⟨m, hm, w, hw⟩ := exists_lift_of_torsion_quotient I hflat hq
    (glueingDifferential f M 1) b htors ã hã
  let Z := LinearMap.ker (glueingDifferential f M 1)
  let diag' : M →ₗ[R] Z := (localizationDiagonal f M).codRestrict Z
    (fun x ↦ glueingDifferential_localizationDiagonal R f M x)
  have htorsZ : IsIPowerTorsion R (Z ⧸ LinearMap.range diag') I := by
    intro c
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ c
    obtain ⟨n, hn, hz⟩ := cocycle_class_torsion f z.1 z.2
    refine ⟨n, hn, fun c hc ↦ ?_⟩
    have hzc := hz c hc
    rw [← map_smul] at hzc
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzc
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, Subtype.ext hx⟩
  obtain ⟨y₀, z, hyz⟩ := exists_decomp_of_torsion_coker I hflat hq diag' htorsZ w
  have hdiag : Z.subtype ∘ₗ diag' = localizationDiagonal f M := rfl
  have hã' : ã = unitMap R S _ (m + z.1) + (localizationDiagonal f M).rTensor S y₀ := by
    have hã2 : ã = unitMap R S _ m + (Z.subtype.rTensor S) w := by rw [← hw]; abel
    have hu : (Z.subtype.rTensor S) (unitMap R S Z z) = unitMap R S _ z.1 := by simp [unitMap]
    have hd : (Z.subtype.rTensor S) ((diag'.rTensor S) y₀) =
        (localizationDiagonal f M).rTensor S y₀ := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hdiag]
    rw [hã2, hyz, map_add, hd, hu, map_add]
    abel
  refine ⟨(y₀, -(m + z.1)), Prod.ext ?_ ?_⟩
  · have ha : a = glueingTermTensorEquiv f M S 1 ã := by simp [ã]
    show localizationDiagonal f (M ⊗[R] S) y₀ - localizationTensorMap S f M 1 (-(m + z.1)) = a
    rw [ha, hã', map_add, glueingTermTensorEquiv_unitMap, glueingTermTensorEquiv_diagonal, map_neg]
    abel
  · show -(glueingDifferential f M 1 (-(m + z.1))) = b
    rw [map_neg, neg_neg, map_add, hm, LinearMap.mem_ker.mp z.2, add_zero]

end Main

end FormalGlueing

end
