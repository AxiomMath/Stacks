module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPrimeThroughPoints
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

/-!
# A point specializing to two given points, in commutative algebra

Let `p`, `q` be closed points of an irreducible closed subset `W`, of dimension at least two, of a
scheme of finite type over a field `k`, and let `K` be the function field of `W`. This file proves
the commutative algebra behind finding a point of `W` other than its generic point that
specializes to both `p` and `q`, without assuming that `p` and `q` have a common affine
neighbourhood.

The input is read in `K`: the rings `A`, `A'` of affine neighbourhoods `U ∋ p`, `U' ∋ q`, the local
rings at `p`, `q` and at a closed point `r ∈ U ∩ U'` of `W`, and their maps to `K`. Valuation rings
of `K` dominating the local rings at `p` and at `q`, and two denominators `λ ∈ A`, `λ' ∈ A'`, give
a finitely generated `k`-subalgebra `R = k[λ⁻¹, a/λ, λ'⁻¹, a'/λ']` of `K` contained in both
valuation rings and in the local ring at `r`; geometrically, `Spec R` is an affine chart of the
closure of the function field in the product of projective completions of `U` and `U'`, chosen to
contain a point above each of `p`, `q`, `r`. A nonzero prime of `R` inside three maximal ideals
above these points (`Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal`, an application of the
Bertini irreducibility theorem [Stacks, Tag 0G4F]) localizes to the required prime of the local
ring at `r`.

## Main results

* `Stacks.Algebraization.CurveThroughPoints.exists_dominant`: the denominators. Over a finite field
  a linear combination of generators need not have the largest valuation, so a power of a
  generator, corrected by the Chinese remainder theorem, is used.
* `Stacks.Algebraization.CurveThroughPoints.exists_prime_specializing`: the prime.

## References

* [Stacks Project, Tag 0EJ1](https://stacks.math.columbia.edu/tag/0EJ1)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

universe u

open IsLocalRing Polynomial

namespace Stacks.Algebraization.CurveThroughPoints

variable {k : Type u} [Field k]

/-- **Inverting a unit of a local ring modulo its maximal ideal by a polynomial in it.** If the
residue class of a unit `w` is integral over `k`, then `w · h(w) ≡ 1` modulo the maximal ideal
for some polynomial `h` over `k`. -/
theorem exists_mul_aeval_sub_one_mem {S : Type*} [CommRing S] [IsLocalRing S] [Algebra k S]
    {w : S} (hw : w ∉ maximalIdeal S) (hint : IsIntegral k (residue S w)) :
    ∃ h : k[X], w * aeval w h - 1 ∈ maximalIdeal S := by
  set g := minpoly k (residue S w)
  have hres0 : residue S w ≠ 0 := by rwa [ne_eq, residue_eq_zero_iff]
  have hc : g.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hres0
  have hg : aeval w g ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff]
    change algebraMap S (ResidueField S) (aeval w g) = 0
    rw [← Polynomial.aeval_algebraMap_apply]
    exact minpoly.aeval k (residue S w)
  have key : aeval w g = w * aeval w g.divX + algebraMap k S (g.coeff 0) := by
    have h := congrArg (aeval w) g.divX_mul_X_add
    rw [map_add, map_mul, aeval_X, aeval_C] at h
    rw [← h]
    ring
  refine ⟨C (-(g.coeff 0)⁻¹) * g.divX, ?_⟩
  have : w * aeval w (C (-(g.coeff 0)⁻¹) * g.divX) - 1 =
      algebraMap k S (-(g.coeff 0)⁻¹) * aeval w g := by
    rw [key, map_mul, aeval_C, mul_add, ← map_mul, neg_mul, inv_mul_cancel₀ hc]
    simp only [map_neg, map_one]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hg

/-- **Residue classes of a localization at a maximal ideal are integral.** Let `S` be a local ring
receiving a map `g` from a finite type `k`-algebra `A` such that every element of `S` is a
fraction `g a / g b` with `g b` a unit, and such that the contraction of the maximal ideal is
maximal. Then the residue field of `S` is integral over `k`. -/
theorem isIntegral_residue {A S : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing S] [IsLocalRing S] [Algebra k S] (g : A →ₐ[k] S)
    (hm : ((maximalIdeal S).comap g).IsMaximal)
    (hl : ∀ w : S, ∃ a b : A, g b ∉ maximalIdeal S ∧ g b * w = g a) (w : S) :
    IsIntegral k (residue S w) := by
  set P := (maximalIdeal S).comap g
  let : Field (A ⧸ P) := Ideal.Quotient.field P
  have : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  let φ : A ⧸ P →ₐ[k] ResidueField S :=
    Ideal.Quotient.liftₐ P ((IsScalarTower.toAlgHom k S (ResidueField S)).comp g) (fun a ha => by
      change algebraMap S (ResidueField S) (g a) = 0
      exact (residue_eq_zero_iff _).mpr ha)
  have hint (a : A) : IsIntegral k (residue S (g a)) :=
    (Algebra.IsIntegral.isIntegral (Ideal.Quotient.mk P a)).map φ
  obtain ⟨a, b, hb, hab⟩ := hl w
  have hb0 : residue S (g b) ≠ 0 := by rwa [ne_eq, residue_eq_zero_iff]
  have : residue S w = residue S (g a) * (residue S (g b))⁻¹ := by
    rw [← hab, map_mul, mul_comm (residue S (g b)), mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  rw [this]
  exact (hint a).mul (IsIntegral.inv (hint b))


section Dominant

variable {K : Type u} [Field K] [Algebra k K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- On a finitely generated `k`-algebra mapping to `K`, a valuation that is at most one on `k`
grows at most geometrically with the degree: if it is at most `μ ≥ 1` on the generators, it is
at most a power of `μ` everywhere. -/
theorem exists_valuation_le_pow {A : Type*} [CommRing A] [Algebra k A] (ι : A →ₐ[k] K)
    (v : Valuation K Γ₀) (hk : ∀ c : k, v (algebraMap k K c) ≤ 1) (s : Set A) {μ : Γ₀}
    (hμ : 1 ≤ μ) (hs : ∀ a ∈ s, v (ι a) ≤ μ) {u : A} (hu : u ∈ Algebra.adjoin k s) :
    ∃ d : ℕ, v (ι u) ≤ μ ^ d := by
  induction hu using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by rw [pow_one]; exact hs x hx⟩
  | algebraMap c => exact ⟨0, by rw [pow_zero, AlgHom.commutes]; exact hk c⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨e, he⟩ := hy
    refine ⟨max d e, ?_⟩
    rw [map_add]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · exact hd.trans (pow_le_pow_right₀ hμ (le_max_left d e))
    · exact he.trans (pow_le_pow_right₀ hμ (le_max_right d e))
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨e, he⟩ := hy
    refine ⟨d + e, ?_⟩
    rw [map_mul, map_mul, pow_add]
    exact mul_le_mul' hd he

/-- **A denominator dominating finitely many elements for one valuation, and a unit at two
maximal ideals.** Let `A` be a `k`-algebra generated by a finite set `s`, mapping to `K` by `ι`,
and let `v` be a valuation of `K` at most one on `k`. For two maximal ideals `P₁`, `P₂` of `A`
there is `λ ∈ A` outside both with `v(ι λ) ≥ 1` and `v(ι λ) ≥ v(ι a)` for every `a ∈ s`.

Over a finite field a linear combination of the generators need not do, so `λ` is taken as
`β ^ (d + 1) + u`, where `β` is a generator of largest valuation and `u` is supplied by the Chinese
remainder theorem to make `λ` a unit at `P₁` and `P₂`; the exponent makes `β ^ (d + 1)` the
dominant term. -/
theorem exists_dominant {A : Type*} [CommRing A] [Algebra k A] (ι : A →ₐ[k] K)
    (v : Valuation K Γ₀) (hk : ∀ c : k, v (algebraMap k K c) ≤ 1) (s : Finset A)
    (hs : Algebra.adjoin k (s : Set A) = ⊤) (P₁ P₂ : Ideal A) [hP₁ : P₁.IsMaximal]
    [hP₂ : P₂.IsMaximal] :
    ∃ l : A, l ∉ P₁ ∧ l ∉ P₂ ∧ 1 ≤ v (ι l) ∧ ∀ a ∈ s, v (ι a) ≤ v (ι l) := by
  classical
  by_cases hsmall : ∀ a ∈ s, v (ι a) ≤ 1
  · refine ⟨1, (Ideal.ne_top_iff_one _).mp hP₁.ne_top, (Ideal.ne_top_iff_one _).mp hP₂.ne_top,
      by simp, fun a ha => ?_⟩
    rw [map_one, map_one]
    exact hsmall a ha
  push Not at hsmall
  obtain ⟨a₀, ha₀s, ha₀⟩ := hsmall
  obtain ⟨β, hβs, hβ⟩ := s.exists_max_image (fun a => v (ι a)) ⟨a₀, ha₀s⟩
  set μ := v (ι β) with hμdef
  have hμ : 1 < μ := ha₀.trans_le (hβ a₀ ha₀s)
  -- the Chinese remainder theorem
  have hcrt : ∃ u : A, (β ∈ P₁ → u - 1 ∈ P₁) ∧ (β ∉ P₁ → u ∈ P₁) ∧
      (β ∈ P₂ → u - 1 ∈ P₂) ∧ (β ∉ P₂ → u ∈ P₂) := by
    let c₁ : A := if β ∈ P₁ then 1 else 0
    let c₂ : A := if β ∈ P₂ then 1 else 0
    suffices h : ∃ u : A, u - c₁ ∈ P₁ ∧ u - c₂ ∈ P₂ by
      obtain ⟨u, h₁, h₂⟩ := h
      refine ⟨u, fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
      · simpa [c₁, hb] using h₁
      · simpa [c₁, hb] using h₁
      · simpa [c₂, hb] using h₂
      · simpa [c₂, hb] using h₂
    by_cases hP : P₁ = P₂
    · subst hP
      refine ⟨c₁, by simp, ?_⟩
      simp [c₁, c₂]
    · have htop := hP₁.coprime_of_ne hP₂ hP
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (htop.symm ▸ Submodule.mem_top :
        (1 : A) ∈ P₁ ⊔ P₂)
      refine ⟨c₁ * y + c₂ * x, ?_, ?_⟩
      · have : c₁ * y + c₂ * x - c₁ = (c₂ - c₁) * x := by
          linear_combination c₁ * hxy
        rw [this]; exact Ideal.mul_mem_left _ _ hx
      · have : c₁ * y + c₂ * x - c₂ = (c₁ - c₂) * y := by
          linear_combination c₂ * hxy
        rw [this]; exact Ideal.mul_mem_left _ _ hy
  obtain ⟨u, hu₁, hu₁', hu₂, hu₂'⟩ := hcrt
  have hgen : ∀ a ∈ (s : Set A), v (ι a) ≤ μ := fun a ha => hβ a ha
  obtain ⟨d, hd⟩ := exists_valuation_le_pow ι v hk (s : Set A) hμ.le hgen
    (show u ∈ Algebra.adjoin k (s : Set A) from hs ▸ Algebra.mem_top)
  have hlt : v (ι u) < v (ι (β ^ (d + 1))) := by
    rw [map_pow, map_pow]
    exact hd.trans_lt (pow_lt_pow_right₀ hμ (Nat.lt_succ_self d))
  have hval : v (ι (β ^ (d + 1) + u)) = μ ^ (d + 1) := by
    rw [map_add, v.map_add_eq_of_lt_left hlt, map_pow, map_pow]
  have hμle : μ ≤ μ ^ (d + 1) := by
    simpa using pow_le_pow_right₀ hμ.le (Nat.succ_le_succ (Nat.zero_le d))
  have hnot : ∀ P : Ideal A, P.IsPrime → (β ∈ P → u - 1 ∈ P) → (β ∉ P → u ∈ P) →
      β ^ (d + 1) + u ∉ P := by
    intro P hP h₁ h₂ hmem
    by_cases hb : β ∈ P
    · have h1 : (1 : A) = β ^ (d + 1) + u - (u - 1) - β ^ d * β := by ring
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (h1 ▸ P.sub_mem (P.sub_mem hmem (h₁ hb))
        (Ideal.mul_mem_left _ _ hb)))
    · have : β ^ (d + 1) ∈ P := by
        have h := P.sub_mem hmem (h₂ hb)
        rwa [add_sub_cancel_right] at h
      exact hb (hP.mem_of_pow_mem _ this)
  refine ⟨β ^ (d + 1) + u, hnot P₁ hP₁.isPrime hu₁ hu₁', hnot P₂ hP₂.isPrime hu₂ hu₂', ?_,
    fun a ha => ?_⟩
  · rw [hval]
    exact hμ.le.trans hμle
  · rw [hval]
    exact (hβ a ha).trans hμle

end Dominant

section Chart

variable {K : Type u} [Field K] [Algebra k K]

/-- The ideal of the elements of a subalgebra `R` of the valuation ring `V` on which the valuation
of `V` is `< 1`. -/
def valIdeal (V : ValuationSubring K) (R : Subalgebra k K) (hR : ∀ x ∈ R, x ∈ V) : Ideal R where
  carrier := {x | V.valuation (x : K) < 1}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (V.valuation.map_add _ _).trans_lt (max_lt hx hy)
  smul_mem' c x hx := by
    change V.valuation ((c : K) * x) < 1
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((V.valuation_le_one_iff _).mpr (hR _ c.2))).trans_lt hx

/-- The ideal `valIdeal V R hR` is prime. -/
theorem valIdeal_isPrime (V : ValuationSubring K) (R : Subalgebra k K) (hR : ∀ x ∈ R, x ∈ V) :
    (valIdeal V R hR).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have : (1 : R) ∈ valIdeal V R hR := h ▸ Submodule.mem_top
    simp [valIdeal] at this
  · change V.valuation ((x : K) * y) < 1 at hxy
    rw [map_mul] at hxy
    by_contra! h
    have hx : 1 ≤ V.valuation (x : K) := not_lt.mp h.1
    have hy : 1 ≤ V.valuation (y : K) := not_lt.mp h.2
    have h1 := mul_le_mul' hx hy
    rw [one_mul] at h1
    exact h1.not_gt hxy

/-- The ideal of the elements of a subalgebra `R` of the image of `ρ` that are images of the
maximal ideal of the local ring. -/
def maxIdeal {S : Type*} [CommRing S] [IsLocalRing S] [Algebra k S] (ρ : S →ₐ[k] K)
    (R : Subalgebra k K) (hR : R ≤ ρ.range) : Ideal R where
  carrier := {x | ∃ w ∈ maximalIdeal S, ρ w = x}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' {x y} := by
    rintro ⟨w, hw, hwx⟩ ⟨w', hw', hwy⟩
    exact ⟨w + w', add_mem hw hw', by rw [map_add, hwx, hwy]; rfl⟩
  smul_mem' c x := by
    rintro ⟨w, hw, hwx⟩
    obtain ⟨c', hc'⟩ := hR c.2
    have hc'' : ρ c' = c := hc'
    exact ⟨c' * w, Ideal.mul_mem_left _ _ hw, by rw [map_mul, hc'', hwx]; rfl⟩

/-- An element of a local ring with the same image under a ring map into a field as an element of
the maximal ideal lies in the maximal ideal: the kernel is a proper ideal, hence contained in the
maximal ideal. -/
theorem mem_maximalIdeal_of_map_eq {S : Type*} [CommRing S] [IsLocalRing S] (ρ : S →+* K)
    {w w' : S} (hw : w ∈ maximalIdeal S) (h : ρ w' = ρ w) : w' ∈ maximalIdeal S := by
  have hker : w' - w ∈ maximalIdeal S := by
    by_contra hn
    have hu := (IsLocalRing.notMem_maximalIdeal.mp hn).map ρ
    rw [map_sub, h, sub_self] at hu
    exact not_isUnit_zero hu
  simpa using add_mem hker hw

/-- If an ideal `I` of a subalgebra `R` contains the images of the maximal ideal of a local ring
`S` and the image of an element `w ∉ maximalIdeal S`, then `1 ∈ I`. -/
private theorem one_mem_of_map_mem {S : Type*} [CommRing S] [IsLocalRing S] [Algebra k S]
    (ρ : S →ₐ[k] K) (R : Subalgebra k K) (hint : ∀ w : S, IsIntegral k (residue S w))
    {I : Ideal R} (hI : ∀ (w : S) (y : R), w ∈ maximalIdeal S → ρ w = y → y ∈ I) {w : S} {x : R}
    (hw : ρ w = x) (hwm : w ∉ maximalIdeal S) (hx : x ∈ I) : (1 : R) ∈ I := by
  obtain ⟨h, hh⟩ := exists_mul_aeval_sub_one_mem hwm (hint w)
  have hmem : x * aeval x h - 1 ∈ I := hI _ _ hh (by
    rw [map_sub, map_mul, ← Polynomial.aeval_algHom_apply, hw, map_one,
      ← Polynomial.aeval_subalgebra_coe]
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one])
  have : (1 : R) = x * aeval x h - (x * aeval x h - 1) := by ring
  rw [this]
  exact I.sub_mem (I.mul_mem_right _ hx) hmem

/-- If the residue field of the local ring `S` is integral over `k`, then `maxIdeal ρ R hR` is a
maximal ideal of `R`. -/
theorem maxIdeal_isMaximal {S : Type*} [CommRing S] [IsLocalRing S] [Algebra k S]
    (ρ : S →ₐ[k] K) (R : Subalgebra k K) (hR : R ≤ ρ.range)
    (hint : ∀ w : S, IsIntegral k (residue S w)) : (maxIdeal ρ R hR).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, fun J x hle hx hxJ => ?_⟩
  · rintro ⟨w, hw, h1⟩
    have : (1 : S) ∈ maximalIdeal S :=
      mem_maximalIdeal_of_map_eq ρ.toRingHom hw (by simpa using h1.symm)
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal S).ne_top this
  · obtain ⟨w, hw⟩ := hR x.2
    exact one_mem_of_map_mem ρ R hint (fun w y hw hy => hle ⟨w, hw, hy⟩) hw
      (fun h => hx ⟨w, h, hw⟩) hxJ

/-- The `k`-algebra generated by `t`, `t'`, `ι a * t` and `ι' a * t'` lies in a subring `B`
containing the generators and the image of `k`. -/
private theorem adjoin_chart_le {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A]
    [Algebra k A'] (ι : A →ₐ[k] K) (ι' : A' →ₐ[k] K) (s : Set A)
    (s' : Set A') (B : Subring K) (hB : ∀ c : k, algebraMap k K c ∈ B) {t t' : K} (ht : t ∈ B)
    (ht' : t' ∈ B) (hs : ∀ a ∈ s, ι a * t ∈ B) (hs' : ∀ a ∈ s', ι' a * t' ∈ B) :
    ∀ x ∈ Algebra.adjoin k (({t, t'} ∪ (fun a => ι a * t) '' s) ∪ (fun a => ι' a * t') '' s'),
      x ∈ B := fun x hx => by
  refine Algebra.adjoin_le (S := {B with algebraMap_mem' := hB}) ?_ hx
  rintro x (((rfl | rfl) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩)
  exacts [ht, ht', hs a ha, hs' a ha]

/-- Multiplying by a further power of `u ∈ R` keeps `x * u ^ n` in `R`. -/
private theorem mul_pow_mem_of_le {R : Subalgebra k K} {x u : K} (hu : u ∈ R) {n N : ℕ}
    (hx : x * u ^ n ∈ R) (hN : n ≤ N) : x * u ^ N ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [pow_add, ← mul_assoc]
  exact R.mul_mem hx (R.pow_mem hu _)

/-- If the generators `a` of `A` satisfy `ι a * t ^ 1 ∈ R`, then every `a` satisfies
`ι a * t ^ n ∈ R` for some `n`. -/
private theorem exists_mul_pow_mem {A : Type*} [CommRing A] [Algebra k A] (ι : A →ₐ[k] K)
    (R : Subalgebra k K) {t : K} (ht : t ∈ R) (s : Set A) (hs : Algebra.adjoin k s = ⊤)
    (hsR : ∀ a ∈ s, ι a * t ∈ R) (a : A) : ∃ n : ℕ, ι a * t ^ n ∈ R := by
  have ha : a ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by rw [pow_one]; exact hsR x hx⟩
  | algebraMap c =>
    exact ⟨0, by rw [pow_zero, mul_one, AlgHom.commutes]; exact R.algebraMap_mem c⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [map_add, add_mul]
    exact R.add_mem (mul_pow_mem_of_le ht hn (Nat.le_add_right n m))
      (mul_pow_mem_of_le ht hm (Nat.le_add_left m n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : ι (x * y) * t ^ (n + m) = (ι x * t ^ n) * (ι y * t ^ m) := by
      rw [map_mul, pow_add]; ring
    rw [this]
    exact R.mul_mem hn hm

end Chart

section Main

variable {K : Type u} [Field K] [Algebra k K]

/-- A valuation subring dominating the image of a local ring: it contains the image, and sends
the image of the maximal ideal to its own maximal ideal. -/
theorem exists_valuationSubring_dominating {S : Type*} [CommRing S] [IsLocalRing S]
    (ρ : S →+* K) :
    ∃ V : ValuationSubring K, (∀ w, ρ w ∈ V) ∧
      ∀ w ∈ maximalIdeal S, V.valuation (ρ w) < 1 := by
  set I := Ideal.map ρ.rangeRestrict (maximalIdeal S)
  have hker : RingHom.ker ρ.rangeRestrict ≤ maximalIdeal S := by
    refine IsLocalRing.le_maximalIdeal fun h => ?_
    have h1 : (1 : S) ∈ RingHom.ker ρ.rangeRestrict := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hI : I ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_of_surjective _ ρ.rangeRestrict_surjective (maximalIdeal S)
    rw [show Ideal.map ρ.rangeRestrict (maximalIdeal S) = ⊤ from h, Ideal.comap_top] at this
    have h2 : maximalIdeal S ⊔ Ideal.comap ρ.rangeRestrict ⊥ = maximalIdeal S :=
      sup_eq_left.mpr hker
    rw [h2] at this
    exact (maximalIdeal.isMaximal S).ne_top this.symm
  obtain ⟨V, hle, hnu⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨V, fun w => hle ⟨w, rfl⟩, fun w hw => ?_⟩
  rw [← ValuationSubring.mem_nonunits_iff]
  exact hnu ⟨ρ.rangeRestrict w, Ideal.mem_map_of_mem _ hw, rfl⟩

/-- If a valuation subring `V` contains the image of `ρ`, then the image of a unit has valuation
`1`. -/
theorem valuation_eq_one_of_isUnit (V : ValuationSubring K) {S : Type*} [CommRing S]
    (ρ : S →+* K) (hV : ∀ w, ρ w ∈ V) {w : S} (hw : IsUnit w) : V.valuation (ρ w) = 1 := by
  have hu : IsUnit (⟨ρ w, hV w⟩ : V) := by
    obtain ⟨u, rfl⟩ := hw
    refine ⟨⟨⟨ρ u, hV _⟩, ⟨ρ ↑u⁻¹, hV _⟩, ?_, ?_⟩, rfl⟩ <;>
      apply Subtype.ext <;>
      simp [mul_inv_cancel₀ (u.isUnit.map ρ).ne_zero, inv_mul_cancel₀ (u.isUnit.map ρ).ne_zero]
  exact (V.valuation_eq_one_iff _).mp hu

/-- The inverse of the image of a unit lies in the range of `ρ`. -/
theorem inv_mem_range_of_isUnit {S : Type*} [CommRing S] [Algebra k S] (ρ : S →ₐ[k] K)
    {w : S} (hw : IsUnit w) : (ρ w)⁻¹ ∈ ρ.range := by
  obtain ⟨u, rfl⟩ := hw
  refine ⟨↑u⁻¹, ?_⟩
  change ρ ↑u⁻¹ = (ρ ↑u)⁻¹
  exact map_units_inv ρ u

/-- If `V` contains the image of `ρ`, the inverse of the image of a unit lies in `V`. -/
private theorem inv_mem_of_isUnit (V : ValuationSubring K) {S : Type*} [CommRing S] [Algebra k S]
    (ρ : S →ₐ[k] K) (hV : ∀ w, ρ w ∈ V) {w : S} (hw : IsUnit w) : (ρ w)⁻¹ ∈ V := by
  obtain ⟨y, hy⟩ := inv_mem_range_of_isUnit ρ hw
  exact hy ▸ hV y

/-- If the valuation of `V` is at least one at `l` and at most `v l` at `a`, then `a / l ∈ V`. -/
private theorem mul_inv_mem_of_valuation_le (V : ValuationSubring K) {a l : K}
    (hl : 1 ≤ V.valuation l) (ha : V.valuation a ≤ V.valuation l) : a * l⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, map_mul, map_inv₀]
  calc V.valuation a * (V.valuation l)⁻¹ ≤ V.valuation l * (V.valuation l)⁻¹ :=
        mul_le_mul' ha le_rfl
    _ = 1 := mul_inv_cancel₀ (by rintro h; rw [h] at hl; simp at hl)

/-- If `d * ι a` lies in a prime `𝔡` of the chart ring `R` with `d ∉ 𝔡`, and `𝔡` lies in a maximal
ideal of `R` above the valuation ring `V` dominating the local ring `S`, then `g a` lies in the
maximal ideal of `S`. Here `t = (ι l)⁻¹` for a unit `g l`, and `ι a * t ^ n ∈ R` for some `n`. -/
private theorem mem_maximalIdeal_of_mul_mem_prime {A S : Type*} [CommRing A] [Algebra k A]
    [CommRing S] [IsLocalRing S] [Algebra k S] (ρ : S →ₐ[k] K) (g : A →ₐ[k] S) (ι : A →ₐ[k] K)
    (hι : ∀ a, ι a = ρ (g a)) (V : ValuationSubring K) (hV : ∀ w, ρ w ∈ V)
    (hlt : ∀ w ∈ maximalIdeal S, V.valuation (ρ w) < 1)
    (hint : ∀ w : S, IsIntegral k (residue S w)) (R : Subalgebra k K) (hR : ∀ x ∈ R, x ∈ V)
    {γ 𝔡 : Ideal R} (hγ : γ.IsMaximal) (hle : valIdeal V R hR ≤ γ) (h𝔡 : 𝔡.IsPrime)
    (h𝔡γ : 𝔡 ≤ γ) {l : A} (hl : IsUnit (g l)) {t : K} (htdef : t = (ι l)⁻¹) (htR : t ∈ R)
    (hpow : ∀ a, ∃ n : ℕ, ι a * t ^ n ∈ R) {d x : R} (hd : d ∉ 𝔡) (hx : x ∈ 𝔡) {a : A}
    (hdx : (d : K) * ι a = x) : g a ∈ maximalIdeal S := by
  obtain ⟨n, hn⟩ := hpow a
  let α : R := ⟨ι a * t ^ n, hn⟩
  have hdα : d * α = x * ⟨t, htR⟩ ^ n := Subtype.ext (by
    push_cast
    change (d : K) * (ι a * t ^ n) = x * t ^ n
    rw [← hdx, mul_assoc])
  have hα : α ∈ 𝔡 :=
    (h𝔡.mem_or_mem (show d * α ∈ 𝔡 from hdα ▸ Ideal.mul_mem_right _ _ hx)).resolve_left hd
  have htr : t ∈ ρ.range := by rw [htdef, hι]; exact inv_mem_range_of_isUnit ρ hl
  have hv : V.valuation (ι a * t ^ n) < 1 := by
    obtain ⟨w, hw⟩ : (α : K) ∈ ρ.range :=
      Subalgebra.mul_mem _ ⟨g a, (hι a).symm⟩ (Subalgebra.pow_mem _ htr _)
    by_cases hwm : w ∈ maximalIdeal S
    · change V.valuation (α : K) < 1
      rw [← hw]; exact hlt w hwm
    · exact (hγ.ne_top ((Ideal.eq_top_iff_one _).mpr (one_mem_of_map_mem ρ R hint
        (fun w y hw hy => hle (show V.valuation (y : K) < 1 from hy ▸ hlt w hw)) hw hwm
        (h𝔡γ hα)))).elim
  have hv1 : V.valuation (ι l) = 1 := by
    rw [hι]; exact valuation_eq_one_of_isUnit V ρ.toRingHom hV hl
  rw [map_mul, map_pow, htdef, map_inv₀, hv1, inv_one, one_pow, mul_one, hι] at hv
  by_contra hcon
  have h1 : V.valuation (ρ (g a)) = 1 :=
    valuation_eq_one_of_isUnit V ρ.toRingHom hV (notMem_maximalIdeal.mp hcon)
  exact lt_irrefl _ (h1 ▸ hv)

/-- **A point specializing to three closed points, read in one local ring.** This is the
algebraic core of passing an irreducible proper closed subset through two closed points `p`,
`q` of an irreducible scheme of finite type over a field when `p` and `q` have no common affine
neighbourhood. `A`, `A'` are the rings of affine neighbourhoods of `p` and `q`, `Sp`, `Sq`, `Sr`
the local rings at `p`, `q` and at a closed point `r` of both neighbourhoods, and the maps `ρ`
to `K` are the maps to the function field. The conclusion is a prime of the local ring at `r`,
strictly containing the generic one, whose traces on `A` and `A'` lie in the ideals of `p` and
`q`.

Valuation rings of `K` dominating the local rings at `p` and `q` and two well chosen
denominators give a finitely generated `k`-subalgebra `R` of `K` contained in both valuation
rings and in the local ring at `r` — the coordinate ring of a chart of the closure of the
function field in a product of two projective completions. A nonzero prime of `R` inside
maximal ideals above the three points (`Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal`,
which needs `dim R ≥ 2`) is then localized at the point above `r`. -/
theorem exists_prime_specializing
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A']
    [Algebra.FiniteType k A] [Algebra.FiniteType k A']
    {Sp Sq Sr : Type u} [CommRing Sp] [CommRing Sq] [CommRing Sr]
    [IsLocalRing Sp] [IsLocalRing Sq] [IsLocalRing Sr]
    [Algebra k Sp] [Algebra k Sq] [Algebra k Sr]
    (ρp : Sp →ₐ[k] K) (ρq : Sq →ₐ[k] K) (ρr : Sr →ₐ[k] K)
    (gp : A →ₐ[k] Sp) (gq : A' →ₐ[k] Sq) (gr : A →ₐ[k] Sr) (gr' : A' →ₐ[k] Sr)
    (hpr : ρp.comp gp = ρr.comp gr) (hqr : ρq.comp gq = ρr.comp gr')
    (hmp : ((maximalIdeal Sp).comap gp).IsMaximal) (hmq : ((maximalIdeal Sq).comap gq).IsMaximal)
    (hmr : ((maximalIdeal Sr).comap gr).IsMaximal)
    (hmr' : ((maximalIdeal Sr).comap gr').IsMaximal)
    (hlp : ∀ w : Sp, ∃ a b : A, gp b ∉ maximalIdeal Sp ∧ gp b * w = gp a)
    (hlq : ∀ w : Sq, ∃ a b : A', gq b ∉ maximalIdeal Sq ∧ gq b * w = gq a)
    (hlr : ∀ w : Sr, ∃ a b : A, gr b ∉ maximalIdeal Sr ∧ gr b * w = gr a)
    (hgen : ∀ z : K, ∃ a b : A, ρr (gr b) ≠ 0 ∧ z = ρr (gr a) / ρr (gr b))
    (hdim : 2 ≤ (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞)) :
    ∃ Q : Ideal Sr, Q.IsPrime ∧ RingHom.ker ρr ≤ Q ∧ ¬ Q ≤ RingHom.ker ρr ∧
      Q.comap gr ≤ (maximalIdeal Sp).comap gp ∧ Q.comap gr' ≤ (maximalIdeal Sq).comap gq := by
  classical
  have hip := isIntegral_residue gp hmp hlp
  have hiq := isIntegral_residue gq hmq hlq
  have hir := isIntegral_residue gr hmr hlr
  -- valuation rings dominating the local rings at `p` and `q`
  obtain ⟨V₁, hV₁, hV₁lt⟩ := exists_valuationSubring_dominating (ρp : Sp →+* K)
  obtain ⟨V₂, hV₂, hV₂lt⟩ := exists_valuationSubring_dominating (ρq : Sq →+* K)
  have hk₁ : ∀ c : k, V₁.valuation (algebraMap k K c) ≤ 1 := fun c => by
    rw [V₁.valuation_le_one_iff, ← ρp.commutes c]; exact hV₁ _
  have hk₂ : ∀ c : k, V₂.valuation (algebraMap k K c) ≤ 1 := fun c => by
    rw [V₂.valuation_le_one_iff, ← ρq.commutes c]; exact hV₂ _
  -- the two maps to `K`
  set ι : A →ₐ[k] K := ρr.comp gr with hιdef
  set ι' : A' →ₐ[k] K := ρr.comp gr' with hι'def
  have hιp : ∀ a, ι a = ρp (gp a) := fun a => (AlgHom.congr_fun hpr a).symm
  have hι'q : ∀ a, ι' a = ρq (gq a) := fun a => (AlgHom.congr_fun hqr a).symm
  -- generators
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  obtain ⟨s', hs'⟩ := Algebra.FiniteType.out (R := k) (A := A')
  -- the two denominators
  have := hmp; have := hmq; have := hmr; have := hmr'
  obtain ⟨l, hlp', hlr', hl1, hls⟩ := exists_dominant ι V₂.valuation hk₂ s hs
    ((maximalIdeal Sp).comap gp) ((maximalIdeal Sr).comap gr)
  obtain ⟨l', hlq', hlr'', hl1', hls'⟩ := exists_dominant ι' V₁.valuation hk₁ s' hs'
    ((maximalIdeal Sq).comap gq) ((maximalIdeal Sr).comap gr')
  have hulp : IsUnit (gp l) := notMem_maximalIdeal.mp hlp'
  have hulr : IsUnit (gr l) := notMem_maximalIdeal.mp hlr'
  have hulq : IsUnit (gq l') := notMem_maximalIdeal.mp hlq'
  have hulr' : IsUnit (gr' l') := notMem_maximalIdeal.mp hlr''
  have hl0 : ι l ≠ 0 := (hulr.map ρr).ne_zero
  have hl0' : ι' l' ≠ 0 := (hulr'.map ρr).ne_zero
  obtain ⟨t, htdef⟩ : ∃ t : K, t = (ι l)⁻¹ := ⟨_, rfl⟩
  obtain ⟨t', ht'def⟩ : ∃ t' : K, t' = (ι' l')⁻¹ := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := htdef ▸ inv_ne_zero hl0
  -- the chart ring
  set S : Set K := ({t, t'} ∪ (fun a => ι a * t) '' (s : Set A)) ∪
    (fun a => ι' a * t') '' (s' : Set A') with hSdef
  set R : Subalgebra k K := Algebra.adjoin k S with hRdef
  have htR : t ∈ R := Algebra.subset_adjoin (by simp [hSdef])
  have ht'R : t' ∈ R := Algebra.subset_adjoin (by simp [hSdef])
  have hsR : ∀ a ∈ s, ι a * t ∈ R := fun a ha =>
    Algebra.subset_adjoin (Or.inl (Or.inr ⟨a, ha, rfl⟩))
  have hs'R : ∀ a ∈ s', ι' a * t' ∈ R := fun a ha =>
    Algebra.subset_adjoin (Or.inr ⟨a, ha, rfl⟩)
  -- `R` lies in the image of the local ring at `r`
  have htr : t ∈ ρr.range := htdef ▸ inv_mem_range_of_isUnit ρr hulr
  have ht'r : t' ∈ ρr.range := ht'def ▸ inv_mem_range_of_isUnit ρr hulr'
  have hRr : R ≤ ρr.range := adjoin_chart_le ι ι' (s : Set A) (s' : Set A') ρr.range.toSubring
    (fun c => ρr.range.algebraMap_mem c) htr ht'r
    (fun a _ => Subalgebra.mul_mem _ ⟨gr a, rfl⟩ htr)
    (fun a _ => Subalgebra.mul_mem _ ⟨gr' a, rfl⟩ ht'r)
  -- `R` lies in the two valuation rings
  have ht₁ : t ∈ V₁ := by rw [htdef, hιp]; exact inv_mem_of_isUnit V₁ ρp hV₁ hulp
  have ht'₂ : t' ∈ V₂ := by rw [ht'def, hι'q]; exact inv_mem_of_isUnit V₂ ρq hV₂ hulq
  have ht'₁ : t' ∈ V₁ := by
    simpa [ht'def] using mul_inv_mem_of_valuation_le V₁ hl1' (a := 1) (by rwa [map_one])
  have ht₂ : t ∈ V₂ := by
    simpa [htdef] using mul_inv_mem_of_valuation_le V₂ hl1 (a := 1) (by rwa [map_one])
  have hR₁ : ∀ x ∈ R, x ∈ V₁ := adjoin_chart_le ι ι' (s : Set A) (s' : Set A') V₁.toSubring
    (fun c => (V₁.valuation_le_one_iff _).mp (hk₁ c)) ht₁ ht'₁
    (fun a _ => by rw [hιp]; exact mul_mem (hV₁ _) ht₁)
    (fun a ha => by rw [ht'def]; exact mul_inv_mem_of_valuation_le V₁ hl1' (hls' a ha))
  have hR₂ : ∀ x ∈ R, x ∈ V₂ := adjoin_chart_le ι ι' (s : Set A) (s' : Set A') V₂.toSubring
    (fun c => (V₂.valuation_le_one_iff _).mp (hk₂ c)) ht₂ ht'₂
    (fun a ha => by rw [htdef]; exact mul_inv_mem_of_valuation_le V₂ hl1 (hls a ha))
    (fun a _ => by rw [hι'q]; exact mul_mem (hV₂ _) ht'₂)
  -- the ideals above `p`, `q` and `r`
  set γ₁ := valIdeal V₁ R hR₁ with hγ₁def
  set γ₂ := valIdeal V₂ R hR₂ with hγ₂def
  have := valIdeal_isPrime V₁ R hR₁
  have := valIdeal_isPrime V₂ R hR₂
  obtain ⟨γ₁', hγ₁'max, hγ₁le⟩ := Ideal.exists_le_maximal γ₁ (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨γ₂', hγ₂'max, hγ₂le⟩ := Ideal.exists_le_maximal γ₂ (Ideal.IsPrime.ne_top ‹_›)
  set ρ' := maxIdeal ρr R hRr with hρ'def
  have hρ'max : ρ'.IsMaximal := maxIdeal_isMaximal ρr R hRr hir
  -- every element of `A` becomes an element of `R` after multiplication by a power of `t`
  have hpow := exists_mul_pow_mem ι R htR (s : Set A) hs hsR
  have hpow' := exists_mul_pow_mem ι' R ht'R (s' : Set A') hs' hs'R
  -- `R` has fraction field `K`, is of finite type, and so has dimension at least two
  have hfrac : IsFractionRing R K := by
    refine IsFractionRing.of_field R K fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := hgen z
    obtain ⟨n, hn⟩ := hpow a
    obtain ⟨m, hm⟩ := hpow b
    refine ⟨⟨_, mul_pow_mem_of_le htR hn (Nat.le_add_right n m)⟩,
      ⟨_, mul_pow_mem_of_le htR hm (Nat.le_add_left m n)⟩, ?_⟩
    change ι a / ι b = (ι a * t ^ (n + m)) / (ι b * t ^ (n + m))
    rw [mul_div_mul_right _ _ (pow_ne_zero _ ht0)]
  have hSfin : S.Finite :=
    ((Set.toFinite _).union (s.finite_toSet.image _)).union (s'.finite_toSet.image _)
  have : Algebra.FiniteType k R :=
    (Subalgebra.fg_iff_finiteType R).mp (Subalgebra.fg_def.mpr ⟨S, hSfin, rfl⟩)
  have hdimR : 2 ≤ ringKrullDim R := by
    rw [(ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, 0} k R K).1]
    exact hdim
  -- a nonzero prime of `R` inside the three maximal ideals
  obtain ⟨𝔡, h𝔡, h𝔡0, h𝔡le⟩ := Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal (k := k) hdimR
    {γ₁', γ₂', ρ'} (by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact hγ₁'max
    · exact hγ₂'max
    · exact hρ'max)
  have h𝔡₁ : 𝔡 ≤ γ₁' := h𝔡le _ (by simp)
  have h𝔡₂ : 𝔡 ≤ γ₂' := h𝔡le _ (by simp)
  have h𝔡ρ : 𝔡 ≤ ρ' := h𝔡le _ (by simp)
  -- every element of the local ring at `r` is a fraction with denominator in `R` outside `ρ'`
  have hunitρ : ∀ (w : Sr) (x : R), w ∉ maximalIdeal Sr → ρr w = x → x ∉ ρ' := by
    rintro w x hw hwx ⟨w', hw', hw'x⟩
    exact hw (mem_maximalIdeal_of_map_eq ρr.toRingHom hw' (by
      change ρr w = ρr w'; rw [hwx, hw'x]))
  have hSR : ∀ c : Sr, ∃ x d : R, d ∉ ρ' ∧ (d : K) * ρr c = x := by
    intro c
    obtain ⟨a, b, hb, hab⟩ := hlr c
    obtain ⟨n, hn⟩ := hpow a
    obtain ⟨m, hm⟩ := hpow b
    have hbu : IsUnit (gr b) := notMem_maximalIdeal.mp hb
    obtain ⟨tl, htl⟩ := htr
    refine ⟨⟨_, mul_pow_mem_of_le htR hn (Nat.le_add_right n m)⟩,
      ⟨_, mul_pow_mem_of_le htR hm (Nat.le_add_left m n)⟩, ?_, ?_⟩
    · refine hunitρ (gr b * tl ^ (n + m)) _ ?_ ?_
      · rw [notMem_maximalIdeal]
        refine hbu.mul (IsUnit.pow _ ?_)
        have : ρr tl * ι l = 1 := by
          rw [show ρr tl = t from htl, htdef, inv_mul_cancel₀ hl0]
        rw [← notMem_maximalIdeal]
        intro hmem
        have h1 : tl * gr l ∈ maximalIdeal Sr := Ideal.mul_mem_right _ _ hmem
        have h2 : (1 : Sr) ∈ maximalIdeal Sr :=
          mem_maximalIdeal_of_map_eq ρr.toRingHom h1 (by
            change ρr 1 = ρr (tl * gr l)
            rw [map_one, map_mul]; exact this.symm)
        exact (maximalIdeal.isMaximal Sr).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
      · change ρr (gr b * tl ^ (n + m)) = ι b * t ^ (n + m)
        rw [map_mul, map_pow, show ρr tl = t from htl]; rfl
    · change ι b * t ^ (n + m) * ρr c = ι a * t ^ (n + m)
      have : ι b * ρr c = ι a := by
        change ρr (gr b) * ρr c = ρr (gr a)
        rw [← map_mul, hab]
      rw [mul_right_comm, this]
  -- the prime of the local ring at `r` cut out by `𝔡`
  have hρ'prime : ρ'.IsPrime := hρ'max.isPrime
  have hnot𝔡 : ∀ d : R, d ∉ ρ' → d ∉ 𝔡 := fun d hd h => hd (h𝔡ρ h)
  have hone : (1 : R) ∉ ρ' := fun h => hρ'max.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  let Q : Ideal Sr :=
    { carrier := {w | ∃ d : R, d ∉ ρ' ∧ ∃ x ∈ 𝔡, (d : K) * ρr w = x}
      zero_mem' := ⟨1, hone, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro w₁ w₂ ⟨d₁, hd₁, x₁, hx₁, h₁⟩ ⟨d₂, hd₂, x₂, hx₂, h₂⟩
        refine ⟨d₁ * d₂, fun h => (hρ'prime.mem_or_mem h).elim hd₁ hd₂, d₂ * x₁ + d₁ * x₂,
          add_mem (Ideal.mul_mem_left _ _ hx₁) (Ideal.mul_mem_left _ _ hx₂), ?_⟩
        push_cast
        rw [map_add, ← h₁, ← h₂]; ring
      smul_mem' := by
        rintro c w ⟨d, hd, x, hx, h⟩
        obtain ⟨y, e, he, hey⟩ := hSR c
        refine ⟨e * d, fun h' => (hρ'prime.mem_or_mem h').elim he hd, y * x,
          Ideal.mul_mem_left _ _ hx, ?_⟩
        push_cast
        rw [smul_eq_mul, map_mul, ← hey, ← h]; ring }
  have hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : Sr) ∈ Q := h ▸ Submodule.mem_top
      obtain ⟨d, hd, x, hx, hdx⟩ := h1
      rw [map_one, mul_one] at hdx
      have : d = x := Subtype.ext hdx
      exact hnot𝔡 d hd (this ▸ hx)
    · obtain ⟨d, hd, x, hx, hdx⟩ := hab
      obtain ⟨ya, ea, hea, heya⟩ := hSR a
      obtain ⟨yb, eb, heb, heyb⟩ := hSR b
      have heq : d * (ya * yb) = ea * eb * x := Subtype.ext (by
        push_cast
        rw [← heya, ← heyb, ← hdx, map_mul]; ring)
      have hmem : d * (ya * yb) ∈ 𝔡 := heq ▸ Ideal.mul_mem_left _ _ hx
      rcases h𝔡.mem_or_mem hmem with h | h
      · exact absurd h (hnot𝔡 d hd)
      · rcases h𝔡.mem_or_mem h with h | h
        · exact Or.inl ⟨ea, hea, ya, h, heya⟩
        · exact Or.inr ⟨eb, heb, yb, h, heyb⟩
  refine ⟨Q, hQ, fun w hw => ⟨1, hone, 0, zero_mem _, by
      rw [RingHom.mem_ker] at hw; simp [hw]⟩, ?_, ?_, ?_⟩
  · intro hle
    obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡0
    obtain ⟨w, hw⟩ := hRr x₀.2
    have hwQ : w ∈ Q := ⟨1, hone, x₀, hx₀, by
      change (1 : K) * ρr w = x₀; rw [one_mul]; exact hw⟩
    have := hle hwQ
    rw [RingHom.mem_ker] at this
    exact hx₀0 (Subtype.ext (by change ρr w = (x₀ : K) at hw; rw [← hw]; exact this))
  · rintro a ⟨d, hd, x, hx, hdx⟩
    exact mem_maximalIdeal_of_mul_mem_prime ρp gp ι hιp V₁ hV₁ hV₁lt hip R hR₁ hγ₁'max hγ₁le
      h𝔡 h𝔡₁ hulp htdef htR hpow (hnot𝔡 d hd) hx hdx
  · rintro a ⟨d, hd, x, hx, hdx⟩
    exact mem_maximalIdeal_of_mul_mem_prime ρq gq ι' hι'q V₂ hV₂ hV₂lt hiq R hR₂ hγ₂'max hγ₂le
      h𝔡 h𝔡₂ hulq ht'def ht'R hpow' (hnot𝔡 d hd) hx hdx

end Main

end Stacks.Algebraization.CurveThroughPoints

end
