module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Tactic.LinearCombination

@[expose] public section

universe u v

/-
# Problem Description

Stacks Tag 0C2A, Lemma 15.110.3 ("Branches of the completion", More on Algebra).

All rings are commutative with unit, and ring maps preserve the unit.

Statement. Let `A` be a ring and let `I ⊆ A` be a finitely generated ideal. Let `A → C`
be a ring map such that for all `f ∈ I` the ring map `A_f → C_f` is localization at an
idempotent. Then there exists a surjective ring map `A → C'` such that for all `f ∈ I`
the canonical ring map `A_f → (C × C')_f` is an isomorphism.

Here, for an `A`-algebra `C` and `f ∈ A`, the localization `C_f = C ⊗_A A_f` is `C` with
the image of `f` inverted, an `A_f`-algebra in the evident way; and `C × C'` is the
product ring, an `A`-algebra via `a ↦ (image of a in C, image of a in C')`.
-/

-- Background and context (as comments):
--
-- Definition 1 (Localization at an element). For a ring `A` and `f ∈ A`, the
-- localization `A_f = A[1/f]` inverts `f`. For an `A`-algebra `C`, the localization
-- `C_f = C ⊗_A A_f` is `C` with the image of `f` inverted. We model `A_f` and `C_f`
-- by Mathlib's concrete localizations `Localization.Away f` and
-- `Localization.Away (algebraMap A C f)` (these satisfy the universal property
-- `IsLocalization.Away`). The induced map `A_f → C_f` is `IsLocalization.Away.map`.
--
-- Definition 2 (Idempotent). `e` is idempotent if `e^2 = e`; in Mathlib this is
-- `IsIdempotentElem e`, i.e. `e * e = e`.
--
-- Definition 3 (Localization at an idempotent). For an idempotent `e` of `B`, the
-- localization `B_e = B[1/e]`. Since `e` is idempotent, `B → B_e` is surjective with
-- kernel `(1 - e)·B`, and `B_e ≅ B/(1-e)B`. Equivalently `B_e` is the localization of
-- `B` away from `e`, captured by `IsLocalization.Away e B_e`.
--
-- Definition 4 (A ring map "is localization at an idempotent"). A ring map
-- `φ : B → D` is localization at an idempotent if there is an idempotent `e ∈ B` and a
-- `B`-algebra isomorphism `D ≅ B_e`. Equivalently (giving `D` the `B`-algebra structure
-- induced by `φ`), `D` is the localization of `B` away from `e`, i.e.
-- `IsLocalization.Away e D` holds for that algebra structure. This is exactly the bridge
-- provided by `IsLocalization.away_of_isIdempotentElem`.

/-- A ring map `φ : B →+* D` *is localization at an idempotent* if there is an idempotent
`e ∈ B` such that, viewing `D` as a `B`-algebra via `φ`, the ring `D` is the localization
of `B` away from `e` (equivalently `D ≅ B_e ≅ B/(1-e)B` as `B`-algebras). -/
def RingHom.IsLocalizationAtIdempotent {B D : Type*} [CommRing B] [CommRing D]
    (φ : B →+* D) : Prop :=
  ∃ e : B, IsIdempotentElem e ∧
    (letI := φ.toAlgebra; IsLocalization.Away e D)

/-- `RingHom.IsLocalizationAtIdempotent`, under the root-level name used by the Stacks 0C2A
statement. -/
abbrev IsLocalizationAtIdempotent {B D : Type*} [CommRing B] [CommRing D]
    (φ : B →+* D) : Prop :=
  RingHom.IsLocalizationAtIdempotent φ

-- Proof sketch of `exists_surjective_bijective_away_prod` (decomposition into named sub-lemmas).
--
-- The proof follows the Stacks 0C2A argument. Fix finitely many generators
-- `f₁,…,f_r` of `I` (from `hI : I.FG`). The plan:
--
--   (Step B) Localization commutes with the finite product `C × C'`: the
--     canonical map `(C × C')_f → C_f × C'_f` is bijective. (Lemma
--     `IsLocalization.Away.prod` below; Mathlib has no product-localization
--     lemma, so this is built by hand from the `IsLocalization.Away` universal
--     property.)
--
--   (Step C) There is a surjection `A → C'` (a quotient `A ⧸ J`) such that for
--     EACH generator `fᵢ` the canonical map `A_{fᵢ} → (C × C')_{fᵢ}` is
--     bijective. Concretely: `h fᵢ` + `RingHom.isLocalizationAtIdempotent_iff` gives an
--     idempotent `eᵢ ∈ A_{fᵢ}` with `C_{fᵢ} ≅ (A_{fᵢ})_{eᵢ}`. Lift
--     `eᵢ = aᵢ/fᵢ^{nᵢ}` to `aᵢ ∈ A`, set `J = (a₁,…,a_r)` (suitably normalized),
--     `C' = A ⧸ J`; then `C'_{fᵢ} ≅ (A_{fᵢ})_{1-eᵢ}` is the complementary factor,
--     and `(C × C')_{fᵢ} ≅ (A_{fᵢ})_{eᵢ} × (A_{fᵢ})_{1-eᵢ} ≅ A_{fᵢ}` with the
--     canonical map the iso. (Lemma
--     `RingHom.IsLocalizationAtIdempotent.exists_complementary_quotient` below.)
--
--   (Step D / glue) For ANY `f ∈ I`, the generators `f₁,…,f_r` generate the unit
--     ideal of `A_f`, so a map of `A_f`-modules is bijective iff it is bijective
--     after further localizing at each `fᵢ`. The map `A_f → (C × C')_f`, further
--     localized at `fᵢ`, is `A_{fᵢ} → (C × C')_{fᵢ}` (localization-localization,
--     `IsLocalization.Away.mul`), which is bijective by Step C. Hence
--     `A_f → (C × C')_f` is bijective. (Lemma
--     `IsLocalization.Away.map_bijective_of_bijective_at_generators` below; uses
--     `bijective_of_isLocalized_span`, Stacks 00EO.)

/-- **Step B (product–localization splitting).**
Localization away from an element commutes with a finite product of rings.
Concretely: let `Sc`, `Sc'` be localizations of `C`, `C'` away from `yc`, `yc'`
respectively. Then the product ring `Sc × Sc'`, with the product algebra
structure (the compatibility hypothesis `hcompat`), is a localization of
`C × C'` away from `(yc, yc')`. Applied with `yc = algebraMap A C f`,
`yc' = algebraMap A C' f` (and the scalar towers from `A`), this says
`(C × C')_f ≅ C_f × C'_f`: the canonical comparison map is bijective.

Mathlib has no product-localization lemma, so this must be proven directly from
the three `IsLocalization.Away` clauses for `(yc, yc')` applied to `Sc × Sc'`:
  (1) `(yc, yc')` maps to a unit (it is a unit in each factor, via
      `IsLocalization.Away.algebraMap_isUnit`, and a pair of units is a unit);
  (2) every `(y, y') ∈ Sc × Sc'` is a fraction `(c, c')/(yc, yc')^N` for a common
      power `N` (clear denominators of `y = c/yc^n`, `y' = c'/yc'^m` to `N = n+m`,
      using `IsLocalization.Away.surj` in each factor);
  (3) `algebraMap (C×C') (Sc×Sc') x = algebraMap _ _ x'` reflects to a common
      power of `(yc, yc')` equalizing `x, x'` (`IsLocalization.Away.exists_of_eq`
      in each factor, take the max of the two exponents).
This is the reusable analytic kernel for "localization of a product ring is the
product of localizations". -/
theorem IsLocalization.Away.prod {C C' : Type*} [CommRing C] [CommRing C']
    (Sc Sc' : Type*) [CommRing Sc] [CommRing Sc'] [Algebra C Sc] [Algebra C' Sc']
    [Algebra (C × C') (Sc × Sc')] (yc : C) (yc' : C')
    [IsLocalization.Away yc Sc] [IsLocalization.Away yc' Sc']
    (hcompat : algebraMap (C × C') (Sc × Sc') =
      (algebraMap C Sc).prodMap (algebraMap C' Sc')) :
    IsLocalization.Away ((yc, yc') : C × C') (Sc × Sc') := by
  -- Strategy: verify the three `IsLocalization.Away` clauses for the product
  -- (units / fraction-surjectivity / equality-reflection), as detailed above,
  -- handling each coordinate with the single-factor `Away` API and combining via
  -- a common power of `(yc, yc')`.
  -- evaluate `algebraMap` on a pair coordinatewise.
  have heval : ∀ p : C × C',
      algebraMap (C × C') (Sc × Sc') p = (algebraMap C Sc p.1, algebraMap C' Sc' p.2) := by
    intro p
    rw [hcompat]
    rfl
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · -- (1) map_units
    rintro ⟨y, n, rfl⟩
    rw [heval, Prod.isUnit_iff]
    refine ⟨?_, ?_⟩
    · change IsUnit (algebraMap C Sc ((yc, yc') ^ n).1)
      rw [Prod.pow_mk]
      simp only [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit yc).pow n
    · change IsUnit (algebraMap C' Sc' ((yc, yc') ^ n).2)
      rw [Prod.pow_mk]
      simp only [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit yc').pow n
  · -- (2) surj
    intro z
    obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj yc z.1
    obtain ⟨m, c', hc'⟩ := IsLocalization.Away.surj yc' z.2
    refine ⟨⟨(c * yc ^ m, c' * yc' ^ n), ⟨(yc, yc') ^ (n + m), ⟨n + m, rfl⟩⟩⟩, ?_⟩
    rw [heval, heval]
    apply Prod.ext
    · change z.1 * algebraMap C Sc (((yc, yc') ^ (n + m)).1) = algebraMap C Sc (c * yc ^ m)
      rw [Prod.pow_mk]
      simp only [map_mul, map_pow]
      rw [pow_add, ← mul_assoc, hc]
    · change z.2 * algebraMap C' Sc' (((yc, yc') ^ (n + m)).2) = algebraMap C' Sc' (c' * yc' ^ n)
      rw [Prod.pow_mk]
      simp only [map_mul, map_pow]
      rw [pow_add, mul_comm (algebraMap C' Sc' yc' ^ n) (algebraMap C' Sc' yc' ^ m),
        ← mul_assoc, hc']
  · -- (3) exists_of_eq
    intro x y hxy
    rw [heval, heval, Prod.ext_iff] at hxy
    obtain ⟨hxy1, hxy2⟩ := hxy
    obtain ⟨⟨_, k, rfl⟩, hc1⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers yc) (S := Sc) hxy1
    obtain ⟨⟨_, l, rfl⟩, hc2⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers yc') (S := Sc') hxy2
    simp only at hc1 hc2
    refine ⟨⟨(yc, yc') ^ (k + l), ⟨k + l, rfl⟩⟩, ?_⟩
    apply Prod.ext
    · change ((yc, yc') ^ (k + l) : C × C').1 * x.1 = ((yc, yc') ^ (k + l) : C × C').1 * y.1
      rw [Prod.pow_mk]
      simp only
      rw [pow_add]
      calc yc ^ k * yc ^ l * x.1 = yc ^ l * (yc ^ k * x.1) := by ring
        _ = yc ^ l * (yc ^ k * y.1) := by rw [hc1]
        _ = yc ^ k * yc ^ l * y.1 := by ring
    · change ((yc, yc') ^ (k + l) : C × C').2 * x.2 = ((yc, yc') ^ (k + l) : C × C').2 * y.2
      rw [Prod.pow_mk]
      simp only
      rw [pow_add]
      calc yc' ^ k * yc' ^ l * x.2 = yc' ^ k * (yc' ^ l * x.2) := by ring
        _ = yc' ^ k * (yc' ^ l * y.2) := by rw [hc2]
        _ = yc' ^ k * yc' ^ l * y.2 := by ring

/- **Idempotent Gluing Lemma (the analytic crux of Stacks Tag 0C2A).**
The locally-defined complementary idempotents glue to a single global ideal.
Concretely: under the hypotheses of `exists_surjective_bijective_away_prod`, there is a *single*
  ideal
`J ⊆ A` such that for every generator `f ∈ s` and every idempotent `e ∈ A_f`
presenting `C_f` (i.e. with `IsLocalization.Away e C_f` for the induced algebra
structure — such `e` is unique, being the characteristic idempotent of the
open-closed decomposition `Spec C_f ↪ Spec A_f`), the extension of `J` to `A_f`
is exactly the principal ideal `(e)`.

This is the substance of Stacks 0C2A: the idempotents `e_f ∈ A_f` agree on the
overlaps `A_{fg}` (by uniqueness of the idempotent presentation of the FIXED map
`A_{fg} → C_{fg}`, since `e_f` and `e_g` both cut out `Spec C_{fg}`), hence by the
sheaf condition for the structure sheaf on the affine cover `{D(f)}_{f∈s}` they
glue to a global section, producing the required `J`. A key bridge is
`IsLocalization.ker_map`, giving `ker(A_f → C_f) = K·A_f` with
`K = RingHom.ker (algebraMap A C)` a *single global* ideal; combined with
`RingHom.isLocalizationAtIdempotent_iff` this gives `(1 - e_f) = K·A_f` for every `f`, so
the *complementary* family is already globally given by `K` — the remaining task
is producing the global `J` with `J·A_f = (e_f)` (the annihilator side), which
requires the overlap-uniqueness/gluing argument above. -/

/-- **L1 (idempotent complement annihilator).** In a commutative ring `R`, the
principal ideal generated by an idempotent `e` is the annihilator of the
complementary principal ideal `(1 - e)`. (Elementary; the formal backbone of the
local picture `(e_f) = Ann(1 - e_f) = Ann(ker(A_f → C_f))`.) -/
theorem IsIdempotentElem.span_singleton_eq_annihilator_one_sub {R : Type*} [CommRing R] {e : R}
    (he : IsIdempotentElem e) :
    Ideal.span {e} = (Ideal.span {1 - e}).annihilator :=
  ((Submodule.annihilator_span_singleton (1 - e)).trans
    he.ker_toSpanSingleton_one_sub_eq_span).symm

/-- **Kernel bridge (`IsLocalization.ker_map` specialized).** The kernel of the
induced localization map `A_f → C_f` is the extension to `A_f` of the single
global ideal `K = RingHom.ker (algebraMap A C)`. This is the bridge expressing the
*complementary* family `(1 - e_f)` uniformly by one global ideal `K`. -/
theorem IsLocalization.Away.ker_map {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] (f : A) :
    RingHom.ker (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f)
      = Ideal.map (algebraMap A (Localization.Away f)) (RingHom.ker (algebraMap A C)) := by
  rw [IsLocalization.Away.map]
  exact IsLocalization.ker_map (Localization.Away (algebraMap A C f)) (algebraMap A C)
    (Submonoid.map_powers (algebraMap A C) f)

/-- **Helper (power-killing implies vanishing after a unit denominator).** If `f^m·x = 0`
in `A`, then the image of `x` in `A_{fg} = Localization.Away (ℓ_g f)` vanishes, because `f`
becomes a unit there. -/
theorem IsLocalization.Away.algebraMap_eq_zero_of_pow_mul_eq_zero {A : Type*} [CommRing A]
    (f g x : A) {m : ℕ} (hx : f ^ m * x = 0) :
    (algebraMap (Localization.Away g) (Localization.Away (algebraMap A (Localization.Away g) f)))
      ((algebraMap A (Localization.Away g)) x) = 0 := by
  set fg := (algebraMap A (Localization.Away g) f)
  set μ := algebraMap (Localization.Away g) (Localization.Away fg)
  have hunit : IsUnit (μ fg) := IsLocalization.Away.algebraMap_isUnit fg
  have h0 : μ (fg ^ m * (algebraMap A (Localization.Away g)) x) = 0 := by
    have : fg ^ m * (algebraMap A (Localization.Away g)) x
        = (algebraMap A (Localization.Away g)) (f ^ m * x) := by
      rw [map_mul, map_pow]
    rw [this, hx, map_zero, map_zero]
  rw [map_mul, map_pow] at h0
  exact (IsUnit.mul_right_eq_zero (hunit.pow m)).mp h0

/-- **Overlap vanishing (the analytic crux of the gluing).** Suppose `ℓ_f(a)` kills `ℓ_f(K)`
in the sense that for each `k ∈ K = ker(A→C)` some power of `f` kills `a·k` in `A` (`hkill`).
Then, for any `g`, the element `(ℓ_g f)^M · ℓ_g(a)` annihilates the complementary idempotent
`1 - e_g` for a sufficiently large power `M`. The proof passes to the overlap
`A_{fg} = Localization.Away (ℓ_g f)`, where `f` is a unit, so each `μ(ℓ_g(a·k)) = 0`
individually; thus `μ(ℓ_g a)` annihilates `μ(map ℓ_g K) ∋ μ(1 - e_g)`, and the spurious
denominator is reflected back as a finite power `M` of `ℓ_g f`. -/
theorem IsLocalization.Away.exists_pow_mul_algebraMap_mul_one_sub_eq_zero {A : Type*} [CommRing A]
    (K : Ideal A) (f g a : A) (e : Localization.Away g)
    (hker : Ideal.map (algebraMap A (Localization.Away g)) K = Ideal.span {1 - e})
    (hkill : ∀ k ∈ K, ∃ m : ℕ, f ^ m * (a * k) = 0) :
    ∃ M : ℕ, (algebraMap A (Localization.Away g) f) ^ M
        * (algebraMap A (Localization.Away g)) a * (1 - e) = 0 := by
  set lg := algebraMap A (Localization.Away g) with hlg
  set fg := lg f
  set μ := algebraMap (Localization.Away g) (Localization.Away fg) with hμ
  have key : μ (lg a) * μ (1 - e) = 0 := by
    have hmem : (1 - e) ∈ Ideal.map lg K := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hmem2 : μ (1 - e) ∈ Ideal.map (μ.comp lg) K := by
      rw [← Ideal.map_map]
      exact Ideal.mem_map_of_mem μ hmem
    have hann : ∀ y ∈ Ideal.map (μ.comp lg) K, μ (lg a) * y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨k, hk, rfl⟩
        obtain ⟨m, hm⟩ := hkill k hk
        have heq : μ (lg a) * (μ.comp lg) k = μ (lg (a * k)) := by
          simp only [RingHom.comp_apply, hμ, hlg, map_mul]
        rw [heq]
        exact IsLocalization.Away.algebraMap_eq_zero_of_pow_mul_eq_zero f g (a * k) hm
      · rw [mul_zero]
      · intro x y _ _ hx hy
        rw [mul_add, hx, hy, add_zero]
      · intro r x _ hx
        rw [mul_smul_comm, hx, smul_zero]
    exact hann (μ (1 - e)) hmem2
  have key2 : μ (lg a * (1 - e)) = 0 := by rwa [map_mul]
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers fg)] at key2
  obtain ⟨⟨_, M, rfl⟩, hc⟩ := key2
  simp only at hc
  exact ⟨M, by linear_combination hc⟩

/-- In a localization away from an idempotent `e`, the image of `e` is `1`. -/
theorem IsLocalization.Away.algebraMap_eq_one_of_isIdempotentElem {S T : Type*} [CommRing S]
    [CommRing T] [Algebra S T] {e : S} (he : IsIdempotentElem e) [IsLocalization.Away e T] :
    algebraMap S T e = 1 :=
  (IsLocalization.Away.algebraMap_isUnit e).mul_eq_left.mp (by rw [← map_mul, he])

/-- In a localization away from an idempotent `e`, `x` maps to zero iff `e * x = 0`. -/
theorem IsLocalization.Away.algebraMap_eq_zero_iff_of_isIdempotentElem {S T : Type*}
    [CommRing S] [CommRing T] [Algebra S T] {e : S} (he : IsIdempotentElem e)
    [IsLocalization.Away e T] (x : S) :
    algebraMap S T x = 0 ↔ e * x = 0 := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨⟨_, m, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) T x).1 hx
    simp only at hc
    rw [← he.pow_succ_eq m, pow_succ, mul_comm (e ^ m) e, mul_assoc, hc, mul_zero]
  · rw [← one_mul (algebraMap S T x), ← algebraMap_eq_one_of_isIdempotentElem he, ← map_mul, hx,
      map_zero]

/-- The kernel of a localization away from an idempotent `e` is `(1 - e)`. -/
theorem IsLocalization.Away.ker_algebraMap_eq_span_one_sub_of_isIdempotentElem {S T : Type*}
    [CommRing S] [CommRing T] [Algebra S T] {e : S} (he : IsIdempotentElem e)
    [IsLocalization.Away e T] :
    RingHom.ker (algebraMap S T) = Ideal.span {1 - e} := by
  ext x
  rw [RingHom.mem_ker, algebraMap_eq_zero_iff_of_isIdempotentElem he,
    Ideal.mem_span_singleton']
  refine ⟨fun h => ⟨x, by linear_combination -h⟩, ?_⟩
  rintro ⟨a, rfl⟩
  linear_combination -a * he.eq

/-- A ring map `φ : B →+* D` is localization at an idempotent if and only if there is an
idempotent `e ∈ B` such that `φ` is surjective with kernel `(1 - e)B`. -/
theorem RingHom.isLocalizationAtIdempotent_iff {B D : Type*} [CommRing B] [CommRing D]
    (φ : B →+* D) :
    φ.IsLocalizationAtIdempotent ↔
      ∃ e : B, IsIdempotentElem e ∧ Function.Surjective φ ∧
        RingHom.ker φ = Ideal.span {1 - e} := by
  let := φ.toAlgebra
  have hmap : (algebraMap B D) = φ := rfl
  constructor
  · rintro ⟨e, he, hL⟩
    exact ⟨e, he, IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he,
      IsLocalization.Away.ker_algebraMap_eq_span_one_sub_of_isIdempotentElem he⟩
  · rintro ⟨e, he, hsurj, hker⟩
    exact ⟨e, he, IsLocalization.away_of_isIdempotentElem he (hmap ▸ hker) (hmap ▸ hsurj)⟩

/-- If an idempotent `e ∈ A_f` presents `C_f` as the localization `(A_f)_e`, then the
extension to `A_f` of the global kernel `ker (A → C)` is the complementary principal
ideal `(1 - e)`. -/
theorem IsLocalization.Away.map_ker_eq_span_one_sub_of_isIdempotentElem {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C] (f : A) {e : Localization.Away f}
    (he : IsIdempotentElem e)
    (hloc : letI := (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f).toAlgebra
      IsLocalization.Away e (Localization.Away (algebraMap A C f))) :
    Ideal.map (algebraMap A (Localization.Away f)) (RingHom.ker (algebraMap A C))
      = Ideal.span {1 - e} := by
  let := (IsLocalization.Away.map (Localization.Away f)
      (Localization.Away (algebraMap A C f)) (algebraMap A C) f).toAlgebra
  rw [← IsLocalization.Away.ker_map f]
  exact IsLocalization.Away.ker_algebraMap_eq_span_one_sub_of_isIdempotentElem he

/-- **Crux (annihilator gluing).** With `K = RingHom.ker (algebraMap A C)` the single
global kernel, there is a *single global* ideal `J ⊆ A` such that for every
generator `f ∈ s` the extension of `J` to `A_f` is the annihilator (in `A_f`) of
the extension of `K`. Equivalently (via `IsLocalization.Away.ker_map` +
`IsIdempotentElem.span_singleton_eq_annihilator_one_sub`), `J·A_f`
is the principal ideal `(e_f)` of the characteristic idempotent. This isolates ALL
the gluing/overlap-compatibility content of Stacks 0C2A: the kernel/annihilator
reductions are discharged separately, in
`exists_ideal_map_eq_span_singleton_idempotent`, leaving only the existence of the
global `J` whose local extensions are the prescribed (complementary) annihilators.

ROADMAP (span-of-lifts + overlap):
choose, for each `f ∈ s`, a lift `a_f ∈ A` with `map ℓ_f (span{a_f}) = (map ℓ_f K).annihilator`
(possible since `(map ℓ_f K).annihilator = span{e_f}` is principal generated by the
idempotent `e_f = mk'(a_f, f^{n_f})`); set `J = span {a_f : f ∈ s}`. Then
`map ℓ_g J = span {ℓ_g(a_f) : f ∈ s}`; the `⊇` inclusion uses `f = g`, and the
`⊆` inclusion is the OVERLAP: `ℓ_g(a_f) ∈ (map ℓ_g K).annihilator`, i.e.
`ℓ_g(a_f)·(1 - e_g) = 0`, which follows from `image(e_f) = image(e_g)` in `A_{fg}`
(uniqueness of the idempotent presentation of the fixed map `A_{fg} → C_{fg}`,
via `IsLocalization.Away.ker_map` functorially in `A_{fg}` + idempotents generating equal ideals
coincide). -/
theorem RingHom.IsLocalizationAtIdempotent.exists_ideal_map_eq_annihilator_map_ker {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C] (s : Finset A)
    (h : ∀ f ∈ s, RingHom.IsLocalizationAtIdempotent
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f)) :
    ∃ (J : Ideal A), ∀ f ∈ s,
        Ideal.map (algebraMap A (Localization.Away f)) J
          = (Ideal.map (algebraMap A (Localization.Away f))
              (RingHom.ker (algebraMap A C))).annihilator := by
  set K := RingHom.ker (algebraMap A C)
  -- Per-generator idempotent data: for each `g ∈ s` there is an idempotent
  -- `e_g ∈ A_g` with `map ℓ_g K = span{1 - e_g}` (kernel of `φ_g`, via
  -- `IsLocalization.Away.ker_map`).
  have hgdata : ∀ g ∈ s, ∃ e : Localization.Away g, IsIdempotentElem e ∧
      Ideal.map (algebraMap A (Localization.Away g)) K = Ideal.span {1 - e} := by
    intro g hg
    obtain ⟨e, he_idem, he_loc⟩ := h g hg
    exact ⟨e, he_idem,
      IsLocalization.Away.map_ker_eq_span_one_sub_of_isIdempotentElem g he_idem he_loc⟩
  choose! egfun hegidem hkerg using hgdata
  -- Good lift per generator: an `a ∈ A` whose image generates `span{e_f}` in `A_f`
  -- (the annihilator side) AND which already lies in the annihilator of `map ℓ_g K`
  -- for *every* `g ∈ s` (overlap compatibility). The overlap is handled by
  -- `exists_pow_mul_algebraMap_mul_one_sub_eq_zero` plus a uniform power of `f` (a finite
  -- `Finset.sup`).
  have hgood : ∀ f ∈ s, ∃ a : A,
      (∀ g ∈ s, (algebraMap A (Localization.Away g)) a ∈
        (Ideal.map (algebraMap A (Localization.Away g)) K).annihilator) ∧
      Ideal.map (algebraMap A (Localization.Away f)) (Ideal.span {a})
        = (Ideal.map (algebraMap A (Localization.Away f)) K).annihilator := by
    intro f hf
    set lf := algebraMap A (Localization.Away f)
    obtain ⟨n, a0, ha0⟩ := IsLocalization.Away.surj f (egfun f)
    -- `ℓ_f(a₀)` kills `ℓ_f(K)`: each generator `ℓ_f(k)` lies in `span{1-e_f}`, so
    -- `e_f·ℓ_f(k) = 0`, hence `ℓ_f(a₀·k) = 0`, hence a power of `f` kills `a₀·k`.
    have hkill : ∀ k ∈ K, ∃ m : ℕ, f ^ m * (a0 * k) = 0 := by
      intro k hk
      have hek : egfun f * lf k = 0 := by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hkerg f hf ▸ Ideal.mem_map_of_mem lf hk)
        rw [hc]
        linear_combination -(c * (hegidem f hf).eq)
      have hlf0 : lf (a0 * k) = 0 := by
        rw [map_mul, ← ha0]
        linear_combination lf f ^ n * hek
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hlf0
      obtain ⟨⟨_, m, rfl⟩, hc⟩ := hlf0
      exact ⟨m, hc⟩
    -- per `g ∈ s`, `exists_pow_mul_algebraMap_mul_one_sub_eq_zero` gives a power `M_g` of
    -- `ℓ_g f` killing `ℓ_g(a₀)(1-e_g)`.
    have hM : ∀ g ∈ s, ∃ M : ℕ, (algebraMap A (Localization.Away g) f) ^ M
        * (algebraMap A (Localization.Away g)) a0 * (1 - egfun g) = 0 := fun g hg =>
      IsLocalization.Away.exists_pow_mul_algebraMap_mul_one_sub_eq_zero K f g a0 (egfun g)
        (hkerg g hg) hkill
    choose! Mfun hMfun using hM
    -- a single uniform exponent `Mf = sup M_g` works for all `g ∈ s`.
    set Mf := s.sup Mfun
    refine ⟨f ^ Mf * a0, ?_, ?_⟩
    · -- overlap: `ℓ_g(f^Mf·a₀) ∈ (map ℓ_g K).annihilator` for every `g ∈ s`.
      intro g hg
      rw [hkerg g hg, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      rw [map_mul, map_pow]
      have hle : Mfun g ≤ Mf := Finset.le_sup hg
      have hbase := hMfun g hg
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, pow_add]
      linear_combination (algebraMap A (Localization.Away g)) f ^ j * hbase
    · -- lift: `map ℓ_f (span{f^Mf·a₀}) = span{e_f} = (map ℓ_f K).annihilator`.
      rw [Ideal.map_span, Set.image_singleton]
      rw [hkerg f hf, ← (hegidem f hf).span_singleton_eq_annihilator_one_sub]
      have hval : lf (f ^ Mf * a0) = egfun f * lf f ^ (Mf + n) := by
        rw [map_mul, map_pow, ← ha0, pow_add]
        ring
      rw [hval]
      have hunit : IsUnit (lf f ^ (Mf + n)) := (IsLocalization.Away.algebraMap_isUnit f).pow _
      rw [mul_comm]
      exact Ideal.span_singleton_mul_left_unit hunit (egfun f)
  choose! afun hafun_ann hafun_lift using hgood
  -- `J` is the span of the lifts. `map ℓ_f J = span{ℓ_f(a_g) : g ∈ s}`; the `f`-term
  -- gives `⊇ span{e_f}` (the target), and the overlap conditions give `⊆`.
  refine ⟨Ideal.span (afun '' (s : Set A)), ?_⟩
  intro f hf
  rw [Ideal.map_span]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro x ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact hafun_ann g hg f hf
  · rw [← hafun_lift f hf, Ideal.map_span, Set.image_singleton]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨afun f, ⟨f, hf, rfl⟩, rfl⟩)

/-- Let `A → C` be a ring map such that for every `f ∈ I` the map `A_f → C_f` is localization
at an idempotent, and let `s ⊆ I` be finite. Then there is an ideal `J ⊆ A` such that for every
`f ∈ s` and every idempotent `e ∈ A_f` presenting `C_f` as the localization `(A_f)_e`, the
extension of `J` to `A_f` is the principal ideal `(e)`. -/
theorem RingHom.IsLocalizationAtIdempotent.exists_ideal_map_eq_span_singleton_idempotent
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] (s : Finset A)
    (h : ∀ f ∈ s, RingHom.IsLocalizationAtIdempotent
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f)) :
    ∃ (J : Ideal A), ∀ f ∈ s, ∀ e : Localization.Away f,
        IsIdempotentElem e →
        (letI := (IsLocalization.Away.map (Localization.Away f)
            (Localization.Away (algebraMap A C f)) (algebraMap A C) f).toAlgebra
         IsLocalization.Away e (Localization.Away (algebraMap A C f))) →
         Ideal.map (algebraMap A (Localization.Away f)) J = Ideal.span {e} := by
  obtain ⟨J, hJ⟩ := exists_ideal_map_eq_annihilator_map_ker s h
  refine ⟨J, fun f hf e he_idem he_loc => ?_⟩
  rw [hJ f hf,
    IsLocalization.Away.map_ker_eq_span_one_sub_of_isIdempotentElem f he_idem he_loc,
    ← he_idem.span_singleton_eq_annihilator_one_sub]

/-- **Idempotent CRT splitting.** For an idempotent `e` of a commutative ring `S`, with
`Se`, `Se'` the localizations of `S` away from `e` and `1 - e` respectively, the canonical
ring map `S → Se × Se'` is bijective. (This is the ring-theoretic incarnation of the
decomposition `S ≅ S/(1-e) × S/(e)` along a complementary pair of idempotents.) -/
theorem IsIdempotentElem.bijective_algebraMap_prod {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (Se Se' : Type*) [CommRing Se] [CommRing Se']
    [Algebra S Se] [Algebra S Se'] [IsLocalization.Away e Se]
    [IsLocalization.Away (1 - e) Se'] :
    Function.Bijective (algebraMap S (Se × Se')) := by
  have heSe : algebraMap S Se e = 1 := IsLocalization.Away.algebraMap_eq_one_of_isIdempotentElem he
  have h1eSe' : algebraMap S Se' (1 - e) = 1 :=
    IsLocalization.Away.algebraMap_eq_one_of_isIdempotentElem he.one_sub
  have h1eSe : algebraMap S Se (1 - e) = 0 := by rw [map_sub, map_one, heSe, sub_self]
  have heSe' : algebraMap S Se' e = 0 := by
    rw [show e = 1 - (1 - e) by ring, map_sub, map_one, h1eSe', sub_self]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun ⟨y, z⟩ => ?_⟩
  · have h₁ := (IsLocalization.Away.algebraMap_eq_zero_iff_of_isIdempotentElem he x).1
      congr(Prod.fst $hx)
    have h₂ := (IsLocalization.Away.algebraMap_eq_zero_iff_of_isIdempotentElem he.one_sub x).1
      congr(Prod.snd $hx)
    linear_combination h₁ + h₂
  · obtain ⟨a, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he y
    obtain ⟨b, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _ he.one_sub z
    refine ⟨e * a + (1 - e) * b, Prod.ext ?_ ?_⟩
    · change algebraMap S Se (e * a + (1 - e) * b) = _
      rw [map_add, map_mul, map_mul, heSe, h1eSe, one_mul, zero_mul, add_zero]
    · change algebraMap S Se' (e * a + (1 - e) * b) = _
      rw [map_add, map_mul, map_mul, heSe', h1eSe', one_mul, zero_mul, zero_add]

/-- The away map sends the image of `x` to the image of `g x`. -/
private theorem away_map_algebraMap {R P : Type*} [CommRing R] [CommRing P] (g : R →+* P) (r : R)
    (S Q : Type*) [CommRing S] [CommRing Q] [Algebra R S] [Algebra P Q]
    [IsLocalization.Away r S] [IsLocalization.Away (g r) Q] (x : R) :
    IsLocalization.Away.map S Q g r (algebraMap R S x) = algebraMap P Q (g x) := by
  rw [IsLocalization.Away.map, IsLocalization.map_eq]

/-- If `A_f → C_f` is the away map, then `C_f` is a scalar tower over `A` and `A_f`. -/
private theorem isScalarTower_away_map {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (f : A) [Algebra (Localization.Away f) (Localization.Away (algebraMap A C f))]
    (h : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      IsLocalization.Away.map _ _ (algebraMap A C) f) :
    IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [h, away_map_algebraMap]
  rfl

/-- **Per-generator splitting.** Let `e` be an idempotent of `A_f` presenting `C_f` as the
localization `(A_f)_e`, and let `J ⊆ A` be an ideal whose extension to `A_f` is `(e)`. Then the
canonical localization map `A_f → (C × A ⧸ J)_f` is bijective.

Localization commutes with the quotient (`(A ⧸ J)_f ≅ A_f/(J·A_f) = A_f/(e) ≅ (A_f)_{1-e}`); the
product–localization splitting `IsLocalization.Away.prod` gives
`(C × A ⧸ J)_f ≅ C_f × (A ⧸ J)_f ≅ (A_f)_e × (A_f)_{1-e}`; and the canonical map is then the
idempotent CRT isomorphism `A_f ≅ (A_f)_e × (A_f)_{1-e}`, `x ↦ (e·x, (1-e)·x)`. -/
theorem RingHom.IsLocalizationAtIdempotent.bijective_awayMap_prod_quotient_of_map_eq_span_singleton
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {J : Ideal A} {f : A}
    {e : Localization.Away f} (he_idem : IsIdempotentElem e)
    (he_loc : letI := (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f).toAlgebra
      IsLocalization.Away e (Localization.Away (algebraMap A C f)))
    (he_ext : Ideal.map (algebraMap A (Localization.Away f)) J = Ideal.span {e}) :
    Function.Bijective
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A (C × (A ⧸ J)) f)) (algebraMap A (C × (A ⧸ J))) f) := by
  -- Give the two factor localizations `C_f`, `(A⧸J)_f` their `A_f`-algebra
  -- structures via the canonical comparison maps.
  let algCf : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (IsLocalization.Away.map (Localization.Away f) (Localization.Away (algebraMap A C f))
        (algebraMap A C) f).toAlgebra
  let algDf : Algebra (Localization.Away f) (Localization.Away (algebraMap A (A ⧸ J) f)) :=
    (IsLocalization.Away.map (Localization.Away f) (Localization.Away (algebraMap A (A ⧸ J) f))
        (algebraMap A (A ⧸ J)) f).toAlgebra
  have hCfmap : (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)))
      = IsLocalization.Away.map (Localization.Away f) (Localization.Away (algebraMap A C f))
          (algebraMap A C) f := rfl
  have hDfmap : (algebraMap (Localization.Away f) (Localization.Away (algebraMap A (A ⧸ J) f)))
      = IsLocalization.Away.map (Localization.Away f) (Localization.Away (algebraMap A (A ⧸ J)
          f)) (algebraMap A (A ⧸ J)) f := rfl
  -- scalar towers `A → A_f → C_f` and `A → A_f → (A⧸J)_f`.
  have htow1 := isScalarTower_away_map (C := C) f hCfmap
  have htow2 := isScalarTower_away_map (C := A ⧸ J) f hDfmap
  -- `C_f = (A_f)_e` (the given presentation) and `(A⧸J)_f = (A_f)_{1-e}` (from `he_ext`).
  have hCfloc : IsLocalization.Away e (Localization.Away (algebraMap A C f)) := he_loc
  have hDfloc : IsLocalization.Away (1 - e) (Localization.Away (algebraMap A (A ⧸ J) f)) := by
    apply IsLocalization.away_of_isIdempotentElem he_idem.one_sub
    · rw [hDfmap, IsLocalization.Away.ker_map f, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker,
        he_ext, sub_sub_cancel]
    · rw [hDfmap, IsLocalization.Away.map]
      exact IsLocalization.map_surjective_of_surjective _ _ _ Ideal.Quotient.mk_surjective
  -- the idempotent CRT splitting `A_f → C_f × (A⧸J)_f` is bijective.
  have hcrt : Function.Bijective (algebraMap (Localization.Away f)
      ((Localization.Away (algebraMap A C f)) × (Localization.Away (algebraMap A (A ⧸ J) f)))) :=
    he_idem.bijective_algebraMap_prod _ _
  set P := C × (A ⧸ J)
  set T := Localization.Away (algebraMap A P f)
  set Cf := Localization.Away (algebraMap A C f)
  set Df := Localization.Away (algebraMap A (A ⧸ J) f)
  -- the product `(C⧸J)_f`-algebra structure on `C_f × (A⧸J)_f`, with the
  -- product-localization fact (Step B `IsLocalization.Away.prod`).
  let algP : Algebra P (Cf × Df) := ((algebraMap C Cf).prodMap (algebraMap (A ⧸ J)
      Df)).toAlgebra
  have hcompat : algebraMap P (Cf × Df) = (algebraMap C Cf).prodMap (algebraMap (A ⧸ J) Df) :=
    rfl
  have hprodloc :
      IsLocalization.Away ((algebraMap A C f, algebraMap A (A ⧸ J) f) : P) (Cf × Df) :=
    IsLocalization.Away.prod Cf Df (algebraMap A C f) (algebraMap A (A ⧸ J) f) hcompat
  have hPf : algebraMap A P f = (algebraMap A C f, algebraMap A (A ⧸ J) f) :=
    Prod.algebraMap_apply f
  have hprodloc' : IsLocalization.Away (algebraMap A P f) (Cf × Df) := by rwa [hPf]
  -- `(C × A⧸J)_f` and `C_f × (A⧸J)_f` both localize `C × A⧸J` at `f`'s image,
  -- hence are canonically `(C×A⧸J)`-algebra isomorphic.
  let ψ := IsLocalization.algEquiv (Submonoid.powers (algebraMap A P f)) (Cf × Df) T
  set φ := IsLocalization.Away.map (Localization.Away f) T (algebraMap A P) f with hφ
  set ψr := ψ.toRingHom
  set crt := algebraMap (Localization.Away f) (Cf × Df) with hcrtm
  -- the goal map `φ` equals `ψ ∘ (CRT splitting)`, hence is bijective.
  have hident : φ = ψr.comp crt := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    change φ (algebraMap A (Localization.Away f) x) = ψr (crt (algebraMap A (Localization.Away
        f) x))
    have hlhs : φ (algebraMap A (Localization.Away f) x) = algebraMap A T x := by
      exact away_map_algebraMap _ f _ _ x
    rw [hlhs]
    have hcrtx : crt (algebraMap A (Localization.Away f) x)
        = ((algebraMap C Cf) (algebraMap A C x), (algebraMap (A ⧸ J) Df) (algebraMap A (A ⧸ J)
            x)) := by
      rw [hcrtm]
      have e1 : (algebraMap (Localization.Away f) (Cf × Df)) (algebraMap A (Localization.Away
          f) x)
          = ((algebraMap (Localization.Away f) Cf) (algebraMap A (Localization.Away f) x),
             (algebraMap (Localization.Away f) Df) (algebraMap A (Localization.Away f) x)) :=
                 rfl
      rw [e1]
      congr 1
      · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A C Cf]
      · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A (A ⧸ J) Df]
    rw [hcrtx]
    have hpair : (((algebraMap C Cf) (algebraMap A C x), (algebraMap (A ⧸ J) Df) (algebraMap A
        (A ⧸ J) x)) : Cf × Df)
        = algebraMap P (Cf × Df) (algebraMap A P x) := by
      rw [hcompat, show (algebraMap A P) x = (algebraMap A C x, algebraMap A (A ⧸ J) x) from
          Prod.algebraMap_apply x]
      rfl
    rw [hpair]
    change (algebraMap A T) x = ψ (algebraMap P (Cf × Df) (algebraMap A P x))
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  rw [hident, RingHom.coe_comp]
  exact Function.Bijective.comp ψ.bijective hcrt

/-- **Step C (construction of the complementary quotient).**
Under the hypotheses of `exists_surjective_bijective_away_prod`, for a finite generating set `s` of
  `I`
there is a surjective `A`-algebra `C'` such that for every generator `f ∈ s` the
canonical localization map `A_f → (C × C')_f` is bijective.

Construction (Stacks 0C2A): for each generator `fᵢ`, `h fᵢ` together with
`RingHom.isLocalizationAtIdempotent_iff` yields an idempotent `eᵢ ∈ A_{fᵢ}` with
`A_{fᵢ} → C_{fᵢ}` surjective of kernel `(1-eᵢ)`. Lift `eᵢ = aᵢ/fᵢ^{nᵢ}` to
`aᵢ ∈ A`; set `J` to be cut out so that `J·A_{fᵢ} = eᵢ·A_{fᵢ}` and let
`C' = A ⧸ J`. Then `A → C'` is the (surjective) quotient map, and at each
generator `C'_{fᵢ} ≅ (A_{fᵢ})_{1-eᵢ}` is the complementary idempotent factor, so
by Step B `(C × C')_{fᵢ} ≅ (A_{fᵢ})_{eᵢ} × (A_{fᵢ})_{1-eᵢ} ≅ A_{fᵢ}` with the
canonical map the isomorphism. -/
theorem RingHom.IsLocalizationAtIdempotent.exists_complementary_quotient {A : Type u}
    {C : Type*} [CommRing A] [CommRing C] [Algebra A C] (s : Finset A)
    (h : ∀ f ∈ s, RingHom.IsLocalizationAtIdempotent
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra A C'),
      Function.Surjective (algebraMap A C') ∧
      ∀ f ∈ s, Function.Bijective
        (IsLocalization.Away.map (Localization.Away f)
          (Localization.Away (algebraMap A (C × C') f)) (algebraMap A (C × C')) f) := by
  -- The construction produces `C' = A ⧸ J` for a suitable ideal `J ⊆ A` (so that
  -- `C'` lives in the universe `u` of `A`). The ideal `J` is glued from the lifted
  -- complementary idempotents `1 - eᵢ` (Stacks 0C2A): `h fᵢ` together with
  -- `RingHom.isLocalizationAtIdempotent_iff` yields an idempotent `eᵢ ∈ A_{fᵢ}` with
  -- `A_{fᵢ} → C_{fᵢ}` surjective of kernel `(1 - eᵢ)`, and `J` is arranged so that
  -- `J · A_{fᵢ} = eᵢ · A_{fᵢ}`, whence `C'_{fᵢ} ≅ (A_{fᵢ})_{1-eᵢ}` and Step B gives
  -- `(C × C')_{fᵢ} ≅ (A_{fᵢ})_{eᵢ} × (A_{fᵢ})_{1-eᵢ} ≅ A_{fᵢ}`.
  obtain ⟨J, hJ⟩ := exists_ideal_map_eq_span_singleton_idempotent s h
  refine ⟨A ⧸ J, inferInstance, inferInstance, Ideal.Quotient.mk_surjective, fun f hf => ?_⟩
  obtain ⟨e, he_idem, he_loc⟩ := h f hf
  exact bijective_awayMap_prod_quotient_of_map_eq_span_singleton he_idem he_loc
    (hJ f hf e he_idem he_loc)

/-- A bijective ring hom `ψ : B →+* D` localizes to a bijective map of localizations
`B_x → D_{ψ x}` (`IsLocalization.Away.map`). Reusable transport-of-bijectivity helper. -/
theorem IsLocalization.Away.map_bijective {B D : Type*} [CommRing B] [CommRing D] (ψ : B →+* D)
    (hψ : Function.Bijective ψ) (x : B)
    (Bx Dx : Type*) [CommRing Bx] [CommRing Dx] [Algebra B Bx] [Algebra D Dx]
    [IsLocalization.Away x Bx] [IsLocalization.Away (ψ x) Dx] :
    Function.Bijective (IsLocalization.Away.map Bx Dx ψ x : Bx →+* Dx) := by
  rw [IsLocalization.Away.map]
  have : IsLocalization (Submonoid.map ψ (Submonoid.powers x)) Dx := by
    rw [Submonoid.map_powers]
    infer_instance
  exact ⟨IsLocalization.map_injective_of_injective _ _ _ hψ.1,
    IsLocalization.map_surjective_of_surjective _ _ _ hψ.2⟩

/-- If `A_g → P_g` is bijective then the away map of `algebraMap A P` at `g * f` is
bijective, for any localizations `Sgf`, `Tgf` away from `g*f` / `algebraMap A P (g*f)`.
"Bijectivity is stable under one further localization." Reusable. -/
theorem IsLocalization.Away.map_mul_bijective {A P : Type*} [CommRing A] [CommRing P] [Algebra A P]
    (f g : A)
    (hg : Function.Bijective
      (IsLocalization.Away.map (Localization.Away g)
        (Localization.Away (algebraMap A P g)) (algebraMap A P) g))
    (Sgf Tgf : Type*) [CommRing Sgf] [CommRing Tgf] [Algebra A Sgf] [Algebra P Tgf]
    [Algebra A Tgf] [IsScalarTower A P Tgf]
    [IsLocalization.Away (g * f) Sgf]
    [IsLocalization.Away (algebraMap A P (g * f)) Tgf] :
    Function.Bijective
      (IsLocalization.Away.map Sgf Tgf (algebraMap A P) (g * f)) := by
  set Sg := Localization.Away g
  set Tg := Localization.Away (algebraMap A P g)
  set ψ := IsLocalization.Away.map Sg Tg (algebraMap A P) g
  set Sgf0 := Localization.Away (algebraMap A Sg f)
  set Tgf0 := Localization.Away (algebraMap A Tg f)
  have hψf : ψ (algebraMap A Sg f) = algebraMap A Tg f := by
    change IsLocalization.Away.map Sg Tg (algebraMap A P) g (algebraMap A Sg f) = algebraMap A Tg f
    exact away_map_algebraMap _ g _ _ f
  have hsgf0 : IsLocalization.Away (g * f) Sgf0 := by
    have := IsLocalization.Away.mul Sg Sgf0 g f
    rwa [mul_comm f g] at this
  have htgf0P : IsLocalization.Away (algebraMap A P (g * f)) Tgf0 := by
    have hmul := IsLocalization.Away.mul (R := P) Tg Tgf0 (algebraMap A P g) (algebraMap A P f)
    rwa [← map_mul, mul_comm f g] at hmul
  have hψinst : IsLocalization.Away (ψ (algebraMap A Sg f)) Tgf0 := by
    rw [hψf]
    infer_instance
  have hmap0 : Function.Bijective (IsLocalization.Away.map Sgf0 Tgf0 ψ (algebraMap A Sg f)) :=
    IsLocalization.Away.map_bijective ψ hg (algebraMap A Sg f) Sgf0 Tgf0
  let e1 : Sgf0 ≃ₐ[A] Sgf := IsLocalization.algEquiv (Submonoid.powers (g * f)) Sgf0 Sgf
  let e2 : Tgf0 ≃ₐ[P] Tgf := IsLocalization.algEquiv (Submonoid.powers (algebraMap A P (g * f)))
      Tgf0 Tgf
  set Φ := IsLocalization.Away.map Sgf Tgf (algebraMap A P) (g * f)
  set iter := IsLocalization.Away.map Sgf0 Tgf0 ψ (algebraMap A Sg f)
  have hkey : Φ.comp (e1 : Sgf0 →+* Sgf) = (e2 : Tgf0 →+* Tgf).comp iter := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (g * f)) (S := Sgf0)
    ext a
    simp only [RingHom.comp_apply]
    have hL : Φ (e1 (algebraMap A Sgf0 a)) = algebraMap P Tgf (algebraMap A P a) := by
      rw [show e1 (algebraMap A Sgf0 a) = algebraMap A Sgf a from (e1.commutes a)]
      exact away_map_algebraMap _ (g * f) _ _ a
    have hR : e2 (iter (algebraMap A Sgf0 a)) = algebraMap P Tgf (algebraMap A P a) := by
      have hstep : iter (algebraMap A Sgf0 a) = algebraMap A Tgf0 a := by
        rw [IsScalarTower.algebraMap_apply A Sg Sgf0 a]
        change IsLocalization.Away.map Sgf0 Tgf0 ψ (algebraMap A Sg f) (algebraMap Sg Sgf0
            (algebraMap A Sg a))
          = algebraMap A Tgf0 a
        rw [IsLocalization.Away.map, IsLocalization.map_eq]
        change algebraMap Tg Tgf0 (ψ (algebraMap A Sg a)) = algebraMap A Tgf0 a
        have : ψ (algebraMap A Sg a) = algebraMap A Tg a := away_map_algebraMap _ g _ _ a
        rw [this, ← IsScalarTower.algebraMap_apply A Tg Tgf0 a]
      rw [hstep, IsScalarTower.algebraMap_apply A P Tgf0 a]
      exact e2.commutes (algebraMap A P a)
    exact hL.trans hR.symm
  have hΦeq : (Φ : Sgf → Tgf) = (e2 : Tgf0 → Tgf) ∘ iter ∘ (e1.symm : Sgf → Sgf0) := by
    funext y
    have hc := RingHom.congr_fun hkey (e1.symm y)
    simp only [RingHom.comp_apply] at hc
    rwa [show ((e1 : Sgf0 →+* Sgf) (e1.symm y)) = y from e1.apply_symm_apply y] at hc
  rw [hΦeq]
  exact e2.bijective.comp (hmap0.comp e1.symm.bijective)

/-- **Step D (Zariski gluing).**
If `s` is a finite subset of `A` whose image generates the unit ideal of `A_f`
(equivalently, `f` lies in the radical of the ideal generated by `s`, which holds
when `f ∈ I = span s`), and the canonical map `A_g → (C × C')_g` is bijective for
each `g ∈ s`, then `A_f → (C × C')_f` is bijective.

This is the ring-map form of Stacks 00EO, which Mathlib provides as
`bijective_of_isLocalization_of_span_eq_top`. Applying it to the map
`ℓ_f : A_f → (C × C')_f` over the cover of `A_f` by the images `g/1` (`g ∈ s`) of the
generators reduces the claim to bijectivity after one further localization at `g/1`,
which is `A_{gf} → (C × C')_{gf}` (`IsLocalization.Away.mul'`) and hence bijective by
`IsLocalization.Away.map_mul_bijective`. -/
theorem IsLocalization.Away.map_bijective_of_bijective_at_generators {A C C' : Type*}
    [CommRing A] [CommRing C] [CommRing C'] [Algebra A C] [Algebra A C']
    (s : Finset A) (f : A) (hf : f ∈ Ideal.span (s : Set A))
    (hgen : ∀ g ∈ s, Function.Bijective
      (IsLocalization.Away.map (Localization.Away g)
        (Localization.Away (algebraMap A (C × C') g)) (algebraMap A (C × C')) g)) :
    Function.Bijective
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A (C × C') f)) (algebraMap A (C × C')) f) := by
  set P := C × C'
  set R := Localization.Away f
  set N := Localization.Away (algebraMap A P f)
  set lamf := IsLocalization.Away.map R N (algebraMap A P) f with hlamf
  set b : A →+* R := algebraMap A R with hb
  -- `f` is a unit in `A_f`, so the images `g/1` (`g ∈ s`) generate the unit ideal of `A_f`.
  have hb_top : Ideal.span (b '' (s : Set A)) = ⊤ := by
    have h1 : b f ∈ Ideal.map b (Ideal.span (s : Set A)) := Ideal.mem_map_of_mem b hf
    rw [Ideal.map_span] at h1
    refine Ideal.eq_top_of_isUnit_mem _ h1 ?_
    rw [hb]
    exact IsLocalization.Away.algebraMap_isUnit (S := R) f
  refine bijective_of_isLocalization_of_span_eq_top hb_top
    (fun r => Localization.Away r.1) (fun r => Localization.Away (lamf r.1)) lamf ?_
  rintro ⟨_, g, hg, rfl⟩
  -- `A_{gf}` and `(C × C')_{gf}` are the localizations of `A_f`, `(C × C')_f` at `g/1`.
  have hAgf_R : IsLocalization.Away (algebraMap A R g) (Localization.Away (b g)) := by
    rw [← hb]
    infer_instance
  have hAgf_gf : IsLocalization.Away (g * f) (Localization.Away (b g)) := by
    have := IsLocalization.Away.mul' (R := A) R (Localization.Away (b g)) f g
    rwa [mul_comm] at this
  have hβ : lamf (b g) = algebraMap P N (algebraMap A P g) := by
    exact away_map_algebraMap _ f _ _ g
  have hPgf_N : IsLocalization.Away (algebraMap P N (algebraMap A P g))
      (Localization.Away (lamf (b g))) := by
    rw [← hβ]
    infer_instance
  have hPgf_gf : IsLocalization.Away (algebraMap A P (g * f))
      (Localization.Away (lamf (b g))) := by
    have := IsLocalization.Away.mul' (R := P) N (Localization.Away (lamf (b g)))
      (algebraMap A P f) (algebraMap A P g)
    rwa [← map_mul, mul_comm f g] at this
  -- Bijectivity at `g` survives the further localization at `f`.
  have hmu : Function.Bijective
      (IsLocalization.Away.map (Localization.Away (b g)) (Localization.Away (lamf (b g)))
        (algebraMap A P) (g * f)) :=
    IsLocalization.Away.map_mul_bijective f g (hgen g hg)
      (Localization.Away (b g)) (Localization.Away (lamf (b g)))
  -- ... and that map is the localization of `ℓ_f` at `g/1`.
  have hsquare :
      (IsLocalization.Away.map (Localization.Away (b g)) (Localization.Away (lamf (b g)))
          (algebraMap A P) (g * f)).comp (algebraMap R (Localization.Away (b g)))
        = (algebraMap N (Localization.Away (lamf (b g)))).comp lamf := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f) (S := R)
    ext a
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A R (Localization.Away (b g)) a,
      IsLocalization.Away.map, IsLocalization.map_eq]
    rw [away_map_algebraMap (algebraMap A P) f R N a,
      ← IsScalarTower.algebraMap_apply P N (Localization.Away (lamf (b g))) (algebraMap A P a)]
  have heq : IsLocalization.Away.map (Localization.Away (b g))
        (Localization.Away (lamf (b g))) lamf (b g)
      = IsLocalization.Away.map (Localization.Away (b g)) (Localization.Away (lamf (b g)))
        (algebraMap A P) (g * f) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (b g)) (S := Localization.Away (b g))
    rw [hsquare, IsLocalization.Away.map]
    exact IsLocalization.map_comp _
  rwa [heq]

/-- **Stacks Tag 0C2A, Lemma 15.110.3.**
Let `A` be a ring, `I ⊆ A` a finitely generated ideal, and `A → C` a ring map such that
for every `f ∈ I` the induced map `A_f → C_f` is localization at an idempotent. Then there
is a surjective ring map `A → C'` such that for every `f ∈ I` the canonical ring map
`A_f → (C × C')_f` is an isomorphism (here expressed as a bijective ring homomorphism).

Note: `C'` is constructed as a quotient of `A`, so it lives in the universe `u` of `A`. -/
@[stacks 0C2A]
theorem exists_surjective_bijective_away_prod {A : Type u} {C : Type v} [CommRing A] [CommRing C]
  [Algebra A C]
    (I : Ideal A) (hI : I.FG)
    (h : ∀ f ∈ I, IsLocalizationAtIdempotent
      (IsLocalization.Away.map (Localization.Away f)
        (Localization.Away (algebraMap A C f)) (algebraMap A C) f)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra A C'),
      Function.Surjective (algebraMap A C') ∧
      ∀ f ∈ I, Function.Bijective
        (IsLocalization.Away.map (Localization.Away f)
          (Localization.Away (algebraMap A (C × C') f)) (algebraMap A (C × C')) f) := by
  -- Extract a finite generating set `s` of `I` from `hI : I.FG`, with `I = span s`.
  obtain ⟨s, hs⟩ := hI
  -- Step C: build the complementary quotient `C'`, surjective, with the canonical
  -- map bijective at every generator `g ∈ s`.
  obtain ⟨C', _, _, hsurj, hgen⟩ :=
    RingHom.IsLocalizationAtIdempotent.exists_complementary_quotient s
      fun x hx => h x (hs ▸ Ideal.subset_span hx)
  refine ⟨C', inferInstance, inferInstance, hsurj, ?_⟩
  -- Step D: glue from the generators to all `f ∈ I`. Since `I = span s`, any
  -- `f ∈ I` lies in `span s`, so Zariski gluing applies.
  exact fun f hf => IsLocalization.Away.map_bijective_of_bijective_at_generators s f (hs ▸ hf) hgen
