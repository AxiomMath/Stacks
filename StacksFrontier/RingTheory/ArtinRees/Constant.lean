module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange

/-!
# Stability of the Artin-Rees constant

Let `A` be a ring and `I ⊆ A` an ideal. An integer `c ≥ 0` works for an `A`-linear map
`f : M → N` in the Artin-Rees lemma if `f(M) ∩ Iⁿ N ⊆ f(Iⁿ⁻ᶜ M)` for all `n ≥ c`, where `Iⁿ N` is
the submodule `Iⁿ • ⊤`. This file proves that such a constant exists whenever `A` is Noetherian
and `N` is finite, and that it is stable under small perturbations of an exact complex and under
flat base change.

## Main definitions

* `IsArtinReesConstant`: `c` works for `f` in the Artin-Rees lemma with respect to `I`.
* `CongruentModPow`: `f ≡ f' (mod Iⁿ)`, i.e. the range of `f - f'` lies in `Iⁿ • ⊤`.

## Main results

* `exists_isArtinReesConstant`: over a Noetherian ring, every linear map whose target is a finite
  module admits a constant that works for it in the Artin-Rees lemma.
* `isArtinReesConstant_of_congr`: a constant that works for the two maps of an exact complex works
  for the second map of any complex congruent to it modulo `I^{c+1}`. This half of
  `artinRees_stability` needs neither Noetherianity nor `I ⊆ rad(A)`.
* `map_pow_smul_top_le`: a linear map whose range lies in `I ^ t • ⊤` carries `I ^ s • ⊤` into
  `I ^ (s + t) • ⊤`.
* `artinRees_stability`: for `A` Noetherian, `I ⊆ rad(A)` and `M` finite, if
  `L --f--> M --g--> N` is exact and `c` works for both `f` and `g`, then for every complex
  `L --f'--> M --g'--> N` with `f' ≡ f` and `g' ≡ g` modulo `I^{c+1}`, the constant `c` works for
  `g'` and the primed complex is exact as well.
* `artinRees_baseChange`: if `A → B` is a flat ring map and `c` works for `f` with respect
  to `I`, then `c` works for `f ⊗ 1` with respect to `IB`.

## References

* [Stacks Project, Tag 07VE](https://stacks.math.columbia.edu/tag/07VE)
* [Stacks Project, Tag 07VG](https://stacks.math.columbia.edu/tag/07VG)
-/

@[expose] public section

/-- `c` works for `f : M → N` in the Artin-Rees lemma with respect to `I`:
`f(M) ∩ I^n N ⊆ f(I^{n-c} M)` for all `n ≥ c`. Here `f(M)` is `LinearMap.range f`,
`I^n N` is `(I^n) • ⊤`, and `f(I^{n-c} M)` is `Submodule.map f ((I^{n-c}) • ⊤)`. -/
def IsArtinReesConstant {A : Type*} [CommRing A] (I : Ideal A) {M N : Type*} [AddCommMonoid M]
    [AddCommMonoid N] [Module A M] [Module A N] (f : M →ₗ[A] N) (c : ℕ) : Prop :=
  ∀ n ≥ c, (LinearMap.range f) ⊓ ((I ^ n) • (⊤ : Submodule A N))
    ≤ Submodule.map f ((I ^ (n - c)) • (⊤ : Submodule A M))

/-- A smaller power of `I` gives a larger submodule `I ^ n • ⊤`. -/
private theorem pow_smul_top_anti {A : Type*} [CommRing A] (I : Ideal A) {M : Type*}
    [AddCommMonoid M] [Module A M] {m n : ℕ} (h : m ≤ n) :
    (I ^ n) • (⊤ : Submodule A M) ≤ (I ^ m) • (⊤ : Submodule A M) :=
  Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl

/-- A constant that works for `f` in the Artin-Rees lemma may be enlarged. -/
theorem IsArtinReesConstant.mono {A : Type*} [CommRing A] {I : Ideal A} {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N] {f : M →ₗ[A] N} {c c' : ℕ}
    (hf : IsArtinReesConstant I f c) (hcc' : c ≤ c') : IsArtinReesConstant I f c' := fun n hn =>
  (hf n (hcc'.trans hn)).trans <| Submodule.map_mono <| pow_smul_top_anti I (by omega)

/-- If `c` works for `f` in the Artin-Rees lemma and `n ≥ c`, then an element of `f(M)` that lies
in `I^n N` already lies in `f(I^{n-c} M)`. -/
theorem IsArtinReesConstant.mem_map {A : Type*} [CommRing A] {I : Ideal A} {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N] {f : M →ₗ[A] N} {c n : ℕ}
    (hf : IsArtinReesConstant I f c) (hn : c ≤ n) {x : M}
    (hx : f x ∈ (I ^ n) • (⊤ : Submodule A N)) :
    f x ∈ Submodule.map f ((I ^ (n - c)) • (⊤ : Submodule A M)) :=
  hf n hn ⟨⟨x, rfl⟩, hx⟩

/-- **Existence of an Artin-Rees constant.** Over a Noetherian ring `A`, every `A`-linear map
`f : M → N` whose target is a finite module admits a `c` that works for it in the Artin-Rees
lemma with respect to any ideal `I`: `f(M) ∩ I^n N ⊆ f(I^{n-c} M)` for all `n ≥ c`. -/
theorem exists_isArtinReesConstant {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type*} [AddCommMonoid M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A N] (f : M →ₗ[A] N) : ∃ c, IsArtinReesConstant I f c := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := N) I (LinearMap.range f)
  refine ⟨c, fun n hn => ?_⟩
  -- Artin-Rees for the submodule `f(M) ⊆ N` turns the intersection into `I^{n-c} (I^c N ∩ f(M))`,
  -- which lies in `I^{n-c} f(M) = f(I^{n-c} M)`.
  rw [inf_comm, hc n hn, Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_mono le_rfl inf_le_right

/-- `f ≡ f' (mod I^n M)`, i.e. `(f - f')(L) ⊆ I^n • ⊤`. -/
def CongruentModPow {A : Type*} [CommRing A] (I : Ideal A) {L M : Type*} [AddCommGroup L]
    [AddCommGroup M] [Module A L] [Module A M] (f f' : L →ₗ[A] M) (n : ℕ) : Prop :=
  LinearMap.range (f - f') ≤ (I ^ n) • (⊤ : Submodule A M)

namespace CongruentModPow

variable {A : Type*} [CommRing A] {I : Ideal A} {L M : Type*} [AddCommGroup L] [AddCommGroup M]
  [Module A L] [Module A M] {f f' : L →ₗ[A] M} {m n : ℕ}

/-- Every map is congruent to itself modulo any power of `I`. -/
theorem refl (I : Ideal A) (f : L →ₗ[A] M) (n : ℕ) : CongruentModPow I f f n := by
  simp [CongruentModPow]

/-- Congruence modulo a power of `I` is symmetric. -/
theorem symm (h : CongruentModPow I f f' n) : CongruentModPow I f' f n := by
  rw [CongruentModPow, ← neg_sub, LinearMap.range_neg]
  exact h

/-- Congruence modulo a power of `I` is transitive. -/
theorem trans {f'' : L →ₗ[A] M} (h : CongruentModPow I f f' n)
    (h' : CongruentModPow I f' f'' n) : CongruentModPow I f f'' n := by
  change LinearMap.range (f - f'') ≤ (I ^ n) • (⊤ : Submodule A M)
  rw [← sub_add_sub_cancel f f' f'']
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (h ⟨x, rfl⟩) (h' ⟨x, rfl⟩)

/-- Congruence modulo `I ^ n` implies congruence modulo any smaller power of `I`. -/
theorem mono (h : CongruentModPow I f f' n) (hmn : m ≤ n) : CongruentModPow I f f' m :=
  le_trans h (pow_smul_top_anti I hmn)

end CongruentModPow

/-- If a linear map has range inside `I ^ t • ⊤`, it carries `I ^ s • ⊤` into `I ^ (s + t) • ⊤`.
With `t = 0` this is the statement that any linear map carries `I ^ s • ⊤` into `I ^ s • ⊤`. -/
theorem map_pow_smul_top_le {A : Type*} [CommRing A] {I : Ideal A} {P Q : Type*}
    [AddCommMonoid P] [AddCommMonoid Q] [Module A P] [Module A Q] (f : P →ₗ[A] Q) {s t : ℕ}
    (hf : LinearMap.range f ≤ (I ^ t) • (⊤ : Submodule A Q)) :
    Submodule.map f ((I ^ s) • (⊤ : Submodule A P)) ≤ (I ^ (s + t)) • (⊤ : Submodule A Q) := by
  rw [Submodule.map_smul'', Submodule.map_top, pow_add, Submodule.mul_smul]
  exact Submodule.smul_mono le_rfl hf

/-- The approximation step behind `artinRees_stability`: if `c` works for `f` and `g`, the complex
`L --f--> M --g--> N` is exact and the primed maps agree with the originals modulo `I^{c+1}`, then
for `n ≥ c` every `m : M` with `g' m ∈ I^n N` differs by an element of `f'(L)` from one of
`I^{n-c} M`. Neither Noetherianity nor a Jacobson radical hypothesis enters. -/
theorem comap_pow_smul_top_le_sup {A : Type*} [CommRing A] (I : Ideal A) {L M N : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module A L] [Module A M] [Module A N]
    (f f' : L →ₗ[A] M) (g g' : M →ₗ[A] N) (c : ℕ) (hS'c : g'.comp f' = 0)
    (hf : IsArtinReesConstant I f c) (hg : IsArtinReesConstant I g c)
    (hexact : LinearMap.ker g = LinearMap.range f)
    (hff' : CongruentModPow I f f' (c + 1)) (hgg' : CongruentModPow I g g' (c + 1))
    {n : ℕ} (hn : c ≤ n) :
    Submodule.comap g' ((I ^ n) • (⊤ : Submodule A N))
      ≤ LinearMap.range f' ⊔ (I ^ (n - c)) • (⊤ : Submodule A M) := by
  have hgf' : ∀ l : L, g' (f' l) = 0 := fun l => by
    rw [← LinearMap.comp_apply, hS'c, LinearMap.zero_apply]
  have step : ∀ r : ℕ, r + c + 1 ≤ n → ∀ m : M, m ∈ (I^r) • (⊤ : Submodule A M) →
      g' m ∈ (I^n) • (⊤ : Submodule A N) →
      ∃ b₀ : L, ∃ z : M, m = f' b₀ + z ∧ z ∈ (I^(r+1)) • (⊤ : Submodule A M) := by
    intro r hrn m hm hgm
    have hgmN : g m ∈ (I^(r+c+1)) • (⊤ : Submodule A N) := by
      rw [show g m = g' m + (g - g') m by simp]
      exact Submodule.add_mem _ (pow_smul_top_anti I hrn hgm)
        (map_pow_smul_top_le (g - g') hgg' (Submodule.mem_map_of_mem hm))
    have hge : g m ∈ Submodule.map g ((I^(r+1)) • (⊤ : Submodule A M)) := by
      have h := hg.mem_map (n := r + c + 1) (by omega) hgmN
      rwa [show r + c + 1 - c = r + 1 by omega] at h
    obtain ⟨a₁, ha₁, hga₁⟩ := hge
    have hker : m - a₁ ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, hga₁, sub_self]
    rw [hexact] at hker
    obtain ⟨b, hb⟩ := hker
    have hfbr : f b ∈ (I^r) • (⊤ : Submodule A M) := by
      rw [hb]
      apply Submodule.sub_mem _ hm
      exact pow_smul_top_anti I (by omega) ha₁
    obtain ⟨b', hb', hffb⟩ : ∃ b' : L, f b' = m - a₁ ∧
        (f - f') b' ∈ (I^(r+1)) • (⊤ : Submodule A M) := by
      by_cases hrc2 : c ≤ r
      · obtain ⟨b₀, hb₀, hfb₀⟩ := hf.mem_map hrc2 hfbr
        have h := map_pow_smul_top_le (f - f') hff' (Submodule.mem_map_of_mem hb₀)
        rw [show r - c + (c + 1) = r + 1 by omega] at h
        exact ⟨b₀, hfb₀.trans hb, h⟩
      · exact ⟨b, hb, pow_smul_top_anti I (by omega) (hff' ⟨b, rfl⟩)⟩
    refine ⟨b', a₁ + (f - f') b', ?_, Submodule.add_mem _ ha₁ hffb⟩
    rw [LinearMap.sub_apply, hb']
    abel
  have aux_07ve : ∀ d : ℕ, d ≤ n - c → ∀ m : M, g' m ∈ (I^n) • (⊤ : Submodule A N) →
      m ∈ (I^((n-c)-d)) • (⊤ : Submodule A M) →
      m ∈ LinearMap.range f' ⊔ (I^(n-c)) • (⊤ : Submodule A M) := by
    intro d
    induction d with
    | zero =>
      intro _ m _ hm
      simp only [Nat.sub_zero] at hm
      exact Submodule.mem_sup_right hm
    | succ d ih =>
      intro hd1 m hgm hm
      have hlt : ((n-c)-(d+1)) + c + 1 ≤ n := by omega
      obtain ⟨b₀, z, heq, hz⟩ := step ((n-c)-(d+1)) hlt m hm hgm
      have hg'z : g' z = g' m := by rw [heq, map_add, hgf' b₀, zero_add]
      have hzmem : z ∈ (I^((n-c)-d)) • (⊤ : Submodule A M) := by
        rwa [show ((n-c)-(d+1)) + 1 = (n-c) - d by omega] at hz
      have hzconcl : z ∈ LinearMap.range f' ⊔ (I^(n-c)) • (⊤ : Submodule A M) :=
        ih (by omega) z (by rwa [hg'z]) hzmem
      rw [heq]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (LinearMap.mem_range_self f' b₀)) hzconcl
  intro m hm
  apply aux_07ve (n - c) le_rfl m (Submodule.mem_comap.mp hm)
  rw [show (n - c) - (n - c) = 0 by omega]
  simp

/-- The first half of **Stacks 07VE**, with no Noetherianity and no Jacobson radical hypothesis:
if `c` works for `f` and `g`, the complex `L --f--> M --g--> N` is exact, and `f'`, `g'` agree
with `f`, `g` modulo `I^{c+1}`, then `c` works for `g'`. Only the exactness of the *second*
complex, not proved here, needs `I` inside the Jacobson radical. -/
theorem isArtinReesConstant_of_congr {A : Type*} [CommRing A] (I : Ideal A) {L M N : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module A L] [Module A M] [Module A N]
    (f f' : L →ₗ[A] M) (g g' : M →ₗ[A] N) (c : ℕ) (hS'c : g'.comp f' = 0)
    (hf : IsArtinReesConstant I f c) (hg : IsArtinReesConstant I g c)
    (hexact : LinearMap.ker g = LinearMap.range f)
    (hff' : CongruentModPow I f f' (c + 1)) (hgg' : CongruentModPow I g g' (c + 1)) :
    IsArtinReesConstant I g' c := by
  have hgf' : ∀ l : L, g' (f' l) = 0 := fun l => by
    rw [← LinearMap.comp_apply, hS'c, LinearMap.zero_apply]
  intro n hn a ha
  obtain ⟨h_range, h_pow⟩ := ha
  obtain ⟨m, rfl⟩ := h_range
  have h_sup := comap_pow_smul_top_le_sup I f f' g g' c hS'c hf hg hexact hff' hgg' hn
    (Submodule.mem_comap.mpr h_pow)
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp h_sup
  obtain ⟨l, rfl⟩ := hx
  rw [map_add, hgf' l, zero_add]
  exact Submodule.mem_map_of_mem hy

/-- **Stacks 07VE**.
Let `A` be Noetherian and `I ⊆ rad(A)`. Let `L --f--> M --g--> N` and `L --f'--> M --g'--> N` be
two complexes of `A`-modules with `M` finite, and `c ≥ 0` such that `c` works for `f` and `g` in
the Artin-Rees lemma, the first complex is exact, `f' ≡ f (mod I^{c+1})` and
`g' ≡ g (mod I^{c+1})`. Then `c` works for `g'` in the Artin-Rees lemma and the second complex
is exact. -/
@[stacks 07VE]
theorem artinRees_stability {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ (⊥ : Ideal A).jacobson) {L M N : Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module A L] [Module A M] [Module A N] [Module.Finite A M]
    (f f' : L →ₗ[A] M) (g g' : M →ₗ[A] N) (c : ℕ) (hS'c : g'.comp f' = 0)
    (hf : IsArtinReesConstant I f c) (hg : IsArtinReesConstant I g c)
    (hexact : LinearMap.ker g = LinearMap.range f)
    (hff' : CongruentModPow I f f' (c + 1)) (hgg' : CongruentModPow I g g' (c + 1)) :
    IsArtinReesConstant I g' c ∧ LinearMap.ker g' = LinearMap.range f' := by
  have key : ∀ n : ℕ, c ≤ n →
      Submodule.comap g' ((I ^ n) • (⊤ : Submodule A N))
        ≤ LinearMap.range f' ⊔ (I ^ (n - c)) • (⊤ : Submodule A M) := fun n hn =>
    comap_pow_smul_top_le_sup I f f' g g' c hS'c hf hg hexact hff' hgg' hn
  refine ⟨isArtinReesConstant_of_congr I f f' g g' c hS'c hf hg hexact hff' hgg', ?_⟩
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      set Q := LinearMap.range f' with hQ
      set π := Q.mkQ with hπ
      have hmem : ∀ k : ℕ, π x ∈ (I ^ k) • (⊤ : Submodule A (M ⧸ Q)) := by
        intro k
        have hxk : x ∈ Submodule.comap g' ((I ^ (k + c)) • (⊤ : Submodule A N)) := by
          rw [Submodule.mem_comap, hx]
          exact Submodule.zero_mem _
        have hxsup : x ∈ LinearMap.range f' ⊔ (I ^ k) • (⊤ : Submodule A M) := by
          have h := key (k + c) (by omega) hxk
          rwa [show k + c - c = k by omega] at h
        have hmap : π x ∈ Submodule.map π (LinearMap.range f' ⊔ (I ^ k) • (⊤ : Submodule A M)) :=
          Submodule.mem_map_of_mem hxsup
        have hQbot : Submodule.map π Q = ⊥ := by
          rw [hπ]; exact Submodule.mkQ_map_self Q
        have hcompute :
            Submodule.map π (LinearMap.range f' ⊔ (I ^ k) • (⊤ : Submodule A M))
              = (I ^ k) • (⊤ : Submodule A (M ⧸ Q)) := by
          rw [Submodule.map_sup, ← hQ, hQbot, bot_sup_eq,
            Submodule.map_smul'', Submodule.map_top, hπ, Submodule.range_mkQ]
        rwa [hcompute] at hmap
      have hbot : π x = 0 := by
        have hinf : π x ∈ (⨅ i, (I ^ i) • (⊤ : Submodule A (M ⧸ Q))) :=
          Submodule.mem_iInf _ |>.mpr hmem
        rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hI] at hinf
        simpa using hinf
      have : x ∈ LinearMap.ker π := LinearMap.mem_ker.mpr hbot
      rwa [hπ, Submodule.ker_mkQ] at this
    · exact LinearMap.range_le_ker_iff.mpr hS'c

/-- **Stacks 07VG**.
Let `A → B` be a flat ring homomorphism, `I ⊆ A` an ideal, and `f : M → N` a map of `A`-modules.
If `c` works for `f` in the Artin-Rees lemma with respect to `I`, then `c` works for the base
change `B ⊗[A] M → B ⊗[A] N` with respect to the ideal `IB`. -/
@[stacks 07VG]
theorem artinRees_baseChange {A : Type*} (B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A) {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (f : M →ₗ[A] N) (c : ℕ)
    (hf : IsArtinReesConstant I f c) :
    IsArtinReesConstant (Ideal.map (algebraMap A B) I) (LinearMap.baseChange B f) c := by
  intro n hn
  rw [ArtinReesBaseChange.range_baseChange, ← Ideal.map_pow,
    ArtinReesBaseChange.ideal_smul_top, ← ArtinReesBaseChange.baseChange_inf,
    ← Ideal.map_pow, ArtinReesBaseChange.ideal_smul_top,
    ArtinReesBaseChange.map_baseChange]
  exact ArtinReesBaseChange.baseChange_mono (hf n hn)
