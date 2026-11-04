module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Glueing functions

Let `R` be a commutative ring and let `f 1, ..., f n ∈ R` generate the unit ideal of `R`, that is,
`Ideal.span (Set.range f) = ⊤`. For each `i`, `R_{f_i}` denotes `Localization.Away (f i)`, and for
each pair `(i, j)`, `R_{f_i f_j}` denotes `Localization.Away (f i * f j)`. The sequence

  `0 → R --α--> ∏_i R_{f_i} --β--> ∏_{(i,j)} R_{f_i f_j}`

is exact, i.e. `α` is injective and `ker β = im α`. For an `R`-module `M`, the map
`Λ : M → ∏_i M_{f_i}`, `m ↦ (m/1, ..., m/1)`, is injective if and only if the map
`Φ : M → ∏_i M`, `m ↦ (f_1 m, ..., f_n m)`, is injective.

## Main definitions

* `alphaLin`: the map `α : R → ∏_i R_{f_i}`, sending `x` to the tuple whose `i`-th component is
  the image of `x` in `R_{f_i}`.
* `betaLin`: the map `β : ∏_i R_{f_i} → ∏_{(i,j)} R_{f_i f_j}`, indexed by all ordered pairs
  `(i, j)`, whose `(i, j)`-component on `s = (s_i)` is the image of `s_i` in `R_{f_i f_j}` minus
  the image of `s_j` in `R_{f_i f_j}`.
* `alphaPair` and `betaPair`: the maps `R → R_a × R_b → R_{ab}` of the two-element case.
* `bigLambda` and `bigPhi`: the maps `Λ` and `Φ`.

## Main results

* `alphaLin_injective` and `ker_betaLin_eq_range_alphaLin`: exactness of
  `0 → R → ∏_i R_{f_i} → ∏_{(i,j)} R_{f_i f_j}`.
* `alphaPair_injective` and `ker_betaPair_eq_range_alphaPair`: exactness of
  `0 → R → R_a × R_b → R_{ab}` when `a` and `b` generate the unit ideal.
* `bigLambda_injective_iff_bigPhi_injective`: `Λ` is injective if and only if `Φ` is.

## References

* [Stacks Project, Tag 00EJ](https://stacks.math.columbia.edu/tag/00EJ)
* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
-/

@[expose] public section

/-- For `a ∣ c` and an away-localization `C` of `R` at `c`, the canonical `R`-linear map
`R_a → C`, induced by the universal property of `Localization.Away a`. -/
noncomputable def awayLinearMap (R : Type*) [CommRing R] (a : R) {C : Type*} [CommRing C]
    [Algebra R C] (c : R) [IsLocalization.Away c C] (h : a ∣ c) :
    Localization.Away a →ₗ[R] C :=
  (IsLocalization.liftAlgHom (M := Submonoid.powers a) (f := Algebra.ofId R C) (by
    rintro ⟨_, k, rfl⟩
    simpa using (IsLocalization.Away.isUnit_of_dvd (S := C) c h).pow k)).toLinearMap

variable (R : Type*) [CommRing R] (n : ℕ) (f : Fin n → R)

/-- The `R`-linear map `α : R → ⊕_i R_{f_i}`. -/
noncomputable def alphaLin : R →ₗ[R] (∀ i : Fin n, Localization.Away (f i)) :=
  LinearMap.pi fun i => Algebra.linearMap R (Localization.Away (f i))

/-- The `R`-linear map `β : ⊕_i R_{f_i} → ⊕_{(i,j)} R_{f_i f_j}`.
The `(i, j)`-component of `β s` is the image of `s i` under `R_{f_i} → R_{f_i f_j}`
minus the image of `s j` under `R_{f_j} → R_{f_i f_j}`. -/
noncomputable def betaLin :
    (∀ i : Fin n, Localization.Away (f i)) →ₗ[R]
      (∀ p : Fin n × Fin n, Localization.Away (f p.1 * f p.2)) :=
  LinearMap.pi fun p =>
    (awayLinearMap R (f p.1) (f p.1 * f p.2) (Dvd.intro (f p.2) rfl)).comp (LinearMap.proj p.1) -
      (awayLinearMap R (f p.2) (f p.1 * f p.2) (Dvd.intro_left (f p.1) rfl)).comp
        (LinearMap.proj p.2)

/-- The `i`-th component of `α x` is the image of `x` in `R_{f_i}`. -/
@[simp]
theorem alphaLin_apply (x : R) (i : Fin n) :
    alphaLin R n f x i = algebraMap R (Localization.Away (f i)) x := rfl

/-- The `(i, j)`-component of `β s` is the image of `s i` in `R_{f_i f_j}` minus the image of
`s j` in `R_{f_i f_j}`. -/
@[simp]
theorem betaLin_apply (s : ∀ i : Fin n, Localization.Away (f i)) (p : Fin n × Fin n) :
    betaLin R n f s p =
      awayLinearMap R (f p.1) (f p.1 * f p.2) (Dvd.intro (f p.2) rfl) (s p.1) -
        awayLinearMap R (f p.2) (f p.1 * f p.2) (Dvd.intro_left (f p.1) rfl) (s p.2) := rfl

/-- The canonical map `R_a → C` sends the image of `x : R` in `R_a` to the image of
`x` in `C`. -/
@[simp]
theorem awayLinearMap_algebraMap {R : Type*} [CommRing R] (a : R) (C : Type*) [CommRing C]
    [Algebra R C] (c : R) [IsLocalization.Away c C] (h : a ∣ c) (x : R) :
    (awayLinearMap R a c h (algebraMap R (Localization.Away a) x) : C) = algebraMap R C x := by
  simp [awayLinearMap]

/-- The canonical map `R_a → C` is multiplicative. -/
theorem awayLinearMap_mul {R : Type*} [CommRing R] (a : R) (C : Type*) [CommRing C]
    [Algebra R C] (c : R) [IsLocalization.Away c C] (h : a ∣ c)
    (u v : Localization.Away a) :
    (awayLinearMap R a c h (u * v) : C)
      = awayLinearMap R a c h u * awayLinearMap R a c h v := by
  simp [awayLinearMap]

/-- The canonical map `R_a → C` transports a relation `s * t = b` in `R_a` (with `t, b ∈ R`)
to the same relation in `C`. -/
theorem awayLinearMap_mul_algebraMap {R : Type*} [CommRing R] (a : R) (C : Type*) [CommRing C]
    [Algebra R C] (c : R) [IsLocalization.Away c C] (h : a ∣ c)
    {s : Localization.Away a} {t b : R}
    (hs : s * algebraMap R _ t = algebraMap R _ b) :
    (awayLinearMap R a c h s : C) * algebraMap R C t = algebraMap R C b := by
  rw [← awayLinearMap_algebraMap a C c h t, ← awayLinearMap_mul, hs, awayLinearMap_algebraMap]

/-- If the `f i` generate the unit ideal, then so do the powers `f i ^ N i`, so `1` is an
`R`-linear combination of them. -/
theorem exists_sum_mul_pow_eq_one {R ι : Type*} [CommRing R] [Fintype ι] {f : ι → R}
    (hf : Ideal.span (Set.range f) = ⊤) (N : ι → ℕ) :
    ∃ c : ι → R, ∑ i, c i * f i ^ N i = 1 := by
  have hspan : Ideal.span (Set.range fun i => f i ^ N i) = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨N i, Ideal.subset_span ⟨i, rfl⟩⟩
  exact Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Submodule.mem_top)

/-- If `f` generates the unit ideal, then `α` is injective. -/
@[stacks 00EJ "exactness at `R`, i.e. injectivity of `α`"]
theorem alphaLin_injective (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (alphaLin R n f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hpow : ∀ i : Fin n, ∃ N : ℕ, f i ^ N * x = 0 := fun i => by
    obtain ⟨⟨_, N, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f i))
      (Localization.Away (f i)) x).mp (by simpa using congrFun hx i)
    exact ⟨N, hm⟩
  choose N hN using hpow
  obtain ⟨c, hc⟩ := exists_sum_mul_pow_eq_one hf N
  calc x = (∑ i, c i * f i ^ N i) * x := by rw [hc, one_mul]
    _ = ∑ i, c i * (f i ^ N i * x) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by simp [hN]

/-- `β ∘ α = 0`. -/
theorem betaLin_comp_alphaLin :
    (betaLin R n f).comp (alphaLin R n f) = 0 :=
  LinearMap.ext fun _ => funext fun _ => by simp

/-- Given representations `s i = a i / f i ^ e i` that agree on overlaps up to a power of
`f i * f j`, there are representations `s i = c i / f i ^ M i` satisfying the relations
`f j ^ M j * c i = f i ^ M i * c j` in `R`. -/
theorem exists_uniform_rep (s : ∀ i : Fin n, Localization.Away (f i)) (a : Fin n → R)
    (e : Fin n → ℕ)
    (hae : ∀ i, s i * algebraMap R (Localization.Away (f i)) (f i ^ e i) = algebraMap R _ (a i))
    (hrel : ∀ i j, ∃ k : ℕ,
      (f i * f j) ^ k * (a i * f j ^ e j) = (f i * f j) ^ k * (a j * f i ^ e i)) :
    ∃ (M : Fin n → ℕ) (c : Fin n → R),
      (∀ i, s i * algebraMap R (Localization.Away (f i)) (f i ^ M i) = algebraMap R _ (c i)) ∧
      ∀ i j, f j ^ M j * c i = f i ^ M i * c j := by
  choose k hk using hrel
  obtain ⟨K, hK⟩ : ∃ K, ∀ i j, k i j ≤ K :=
    ⟨Finset.univ.sup fun p : Fin n × Fin n => k p.1 p.2, fun i j =>
      Finset.le_sup (f := fun p : Fin n × Fin n => k p.1 p.2) (Finset.mem_univ (i, j))⟩
  refine ⟨fun i => e i + K, fun i => a i * f i ^ K, fun i => ?_, fun i j => ?_⟩
  · rw [pow_add, map_mul, ← mul_assoc, hae i, map_mul]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hK i j)
    linear_combination (f i * f j) ^ d * hk i j

/-- If `s = c / a ^ k` in `R_a` and `a ^ k * x = c` in `R`, then `s` is the image of `x`. -/
private theorem algebraMap_eq_of_mul_pow_eq {R : Type*} [CommRing R] {a : R}
    {s : Localization.Away a} {c x : R} (k : ℕ)
    (hs : s * algebraMap R _ (a ^ k) = algebraMap R _ c) (hx : a ^ k * x = c) :
    algebraMap R (Localization.Away a) x = s := by
  have hunit : IsUnit (algebraMap R (Localization.Away a) (a ^ k)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit a).pow k
  apply hunit.mul_left_cancel
  rw [← map_mul, hx, mul_comm _ s, hs]

/-- If `s i = c i / f i ^ M i` with `f j ^ M j * c i = f i ^ M i * c j` for all
`i, j`, and `∑ i, g i * f i ^ M i = 1`, then `s` is the image of `∑ i, g i * c i` under `α`. -/
theorem alphaLin_sum_mul_eq_of_rep (s : ∀ i : Fin n, Localization.Away (f i))
    (M : Fin n → ℕ) (c g : Fin n → R)
    (hrep : ∀ i, s i * algebraMap R (Localization.Away (f i)) (f i ^ M i) = algebraMap R _ (c i))
    (hcross : ∀ i j, f j ^ M j * c i = f i ^ M i * c j) (hg : ∑ i, g i * f i ^ M i = 1) :
    alphaLin R n f (∑ i, g i * c i) = s := by
  funext l
  have hR : f l ^ M l * ∑ i, g i * c i = c l := by
    rw [← one_mul (c l), ← hg, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by linear_combination g i * hcross i l
  exact algebraMap_eq_of_mul_pow_eq (M l) (hrep l) hR

/-- If `s = p / a ^ e` and `t = q / b ^ e'` have the same image in `R_{ab}`, then
`p * b ^ e'` and `q * a ^ e` agree after multiplying by a power of `a * b`. -/
private theorem exists_pow_mul_eq_of_away_eq {R : Type*} [CommRing R] {a b p q : R} {e e' : ℕ}
    {s : Localization.Away a} {t : Localization.Away b}
    (hp : s * algebraMap R _ (a ^ e) = algebraMap R _ p)
    (hq : t * algebraMap R _ (b ^ e') = algebraMap R _ q)
    (hst : (awayLinearMap R a (a * b) (Dvd.intro b rfl) s : Localization.Away (a * b))
      = awayLinearMap R b (a * b) (Dvd.intro_left a rfl) t) :
    ∃ k : ℕ, (a * b) ^ k * (p * b ^ e') = (a * b) ^ k * (q * a ^ e) := by
  have key : algebraMap R (Localization.Away (a * b)) (p * b ^ e')
      = algebraMap R (Localization.Away (a * b)) (q * a ^ e) := by
    rw [map_mul, map_mul, ← awayLinearMap_mul_algebraMap a _ (a * b) (Dvd.intro b rfl) hp,
      ← awayLinearMap_mul_algebraMap b _ (a * b) (Dvd.intro_left a rfl) hq, hst]
    ring
  rw [IsLocalization.eq_iff_exists (Submonoid.powers (a * b))] at key
  obtain ⟨⟨_, k, rfl⟩, ht⟩ := key
  exact ⟨k, ht⟩

/-- If `f` generates the unit ideal, then for an element `s = (s_i)` the images of `s i` and `s j`
agree in `R_{f_i f_j}` for all `i, j` if and only if `s = α x` for some `x ∈ R`. -/
theorem mem_ker_betaLin_iff (hf : Ideal.span (Set.range f) = ⊤)
    (s : ∀ i : Fin n, Localization.Away (f i)) :
    (∀ i j : Fin n,
        (awayLinearMap R (f i) (f i * f j) (Dvd.intro (f j) rfl) (s i)
            : Localization.Away (f i * f j))
          = awayLinearMap R (f j) (f i * f j) (Dvd.intro_left (f i) rfl) (s j))
      ↔ ∃ x : R, alphaLin R n f x = s := by
  refine ⟨fun hcompat => ?_, ?_⟩
  · have hrep : ∀ i : Fin n, ∃ (a : R) (e : ℕ),
        s i * algebraMap R (Localization.Away (f i)) (f i ^ e) = algebraMap R _ a := fun i => by
      obtain ⟨⟨a, _, e, rfl⟩, hd⟩ := IsLocalization.surj (Submonoid.powers (f i)) (s i)
      exact ⟨a, e, hd⟩
    choose a e hae using hrep
    have hrel : ∀ i j : Fin n, ∃ k : ℕ,
        (f i * f j) ^ k * (a i * f j ^ e j) = (f i * f j) ^ k * (a j * f i ^ e i) := by
      intro i j
      exact exists_pow_mul_eq_of_away_eq (hae i) (hae j) (hcompat i j)
    obtain ⟨M, c, hrepc, hcross⟩ := exists_uniform_rep R n f s a e hae hrel
    obtain ⟨g, hg⟩ := exists_sum_mul_pow_eq_one hf M
    exact ⟨_, alphaLin_sum_mul_eq_of_rep R n f s M c g hrepc hcross hg⟩
  · rintro ⟨x, rfl⟩ i j
    simp

/-- If `f` generates the unit ideal, then the kernel of `β` equals the range of `α`. -/
@[stacks 00EJ "exactness at the middle term, i.e. `ker β = im α`"]
theorem ker_betaLin_eq_range_alphaLin (hf : Ideal.span (Set.range f) = ⊤) :
    LinearMap.ker (betaLin R n f) = LinearMap.range (alphaLin R n f) := by
  ext s
  rw [LinearMap.mem_ker, LinearMap.mem_range, ← mem_ker_betaLin_iff R n f hf s]
  simp [funext_iff, sub_eq_zero]

/-! ### The two-element case, in product form -/

/-- If `a` and `b` generate the unit ideal, then for any exponents `N` and `M`, `1` is an
`R`-linear combination of `a ^ N` and `b ^ M`. -/
theorem exists_mul_pow_add_mul_pow_eq_one {R : Type*} [CommRing R] {a b : R}
    (hab : Ideal.span ({a, b} : Set R) = ⊤) (N M : ℕ) :
    ∃ c d : R, c * a ^ N + d * b ^ M = 1 := by
  have hrad : Ideal.span ({a ^ N, b ^ M} : Set R) = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hab, Ideal.span_le]
    rintro x (rfl | rfl)
    · exact ⟨N, Ideal.subset_span (Or.inl rfl)⟩
    · exact ⟨M, Ideal.subset_span (Or.inr rfl)⟩
  exact Ideal.mem_span_pair.mp ((Ideal.eq_top_iff_one _).mp hrad)

variable {R}

/-- The two-element case of `α`: the canonical `R`-linear map `R → R_a × R_b`. -/
noncomputable def alphaPair (a b : R) : R →ₗ[R] Localization.Away a × Localization.Away b :=
  (Algebra.linearMap R (Localization.Away a)).prod (Algebra.linearMap R (Localization.Away b))

/-- The components of `alphaPair a b x` are the images of `x` in `R_a` and `R_b`. -/
@[simp]
theorem alphaPair_apply (a b : R) (x : R) :
    alphaPair a b x =
      (algebraMap R (Localization.Away a) x, algebraMap R (Localization.Away b) x) := rfl

/-- The two-element case of `β`: the canonical `R`-linear map `R_a × R_b → R_{ab}`, whose value
on `(s, t)` is the difference of the images of `s` and `t` in `R_{ab}`. -/
noncomputable def betaPair (a b : R) :
    Localization.Away a × Localization.Away b →ₗ[R] Localization.Away (a * b) :=
  (awayLinearMap R a (a * b) (Dvd.intro b rfl)).comp (LinearMap.fst R _ _) -
    (awayLinearMap R b (a * b) (Dvd.intro_left a rfl)).comp (LinearMap.snd R _ _)

/-- The value of `betaPair a b` on `(s, t)` is the image of `s` in `R_{ab}` minus the image of
`t` in `R_{ab}`. -/
@[simp]
theorem betaPair_apply (a b : R) (s : Localization.Away a) (t : Localization.Away b) :
    betaPair a b (s, t) =
      awayLinearMap R a (a * b) (Dvd.intro b rfl) s -
        awayLinearMap R b (a * b) (Dvd.intro_left a rfl) t := rfl

/-- `β ∘ α = 0` in the two-element case. -/
theorem betaPair_comp_alphaPair (a b : R) : (betaPair a b).comp (alphaPair a b) = 0 :=
  LinearMap.ext fun _ => by simp

/-- If `a` and `b` generate the unit ideal, then `R → R_a × R_b` is injective. -/
theorem alphaPair_injective (a b : R) (hab : Ideal.span ({a, b} : Set R) = ⊤) :
    Function.Injective (alphaPair a b) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxa : algebraMap R (Localization.Away a) x = 0 := by
    simpa [alphaPair_apply] using congrArg Prod.fst hx
  have hxb : algebraMap R (Localization.Away b) x = 0 := by
    simpa [alphaPair_apply] using congrArg Prod.snd hx
  obtain ⟨⟨_, N, rfl⟩, hNa⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) x).mp hxa
  obtain ⟨⟨_, M, rfl⟩, hMb⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).mp hxb
  obtain ⟨c, d, hcd⟩ := exists_mul_pow_add_mul_pow_eq_one hab N M
  calc x = (c * a ^ N + d * b ^ M) * x := by rw [hcd, one_mul]
    _ = c * (a ^ N * x) + d * (b ^ M * x) := by ring
    _ = 0 := by rw [hNa, hMb]; ring

/-- If `a` and `b` generate the unit ideal, then the kernel of `β : R_a × R_b → R_{ab}` equals the
range of `α : R → R_a × R_b`. -/
theorem ker_betaPair_eq_range_alphaPair (a b : R) (hab : Ideal.span ({a, b} : Set R) = ⊤) :
    LinearMap.ker (betaPair a b) = LinearMap.range (alphaPair a b) := by
  ext ⟨s, t⟩
  simp only [LinearMap.mem_ker, LinearMap.mem_range, betaPair_apply, alphaPair_apply,
    sub_eq_zero, Prod.mk.injEq]
  refine ⟨fun hst ↦ ?_, ?_⟩
  · obtain ⟨⟨p, _, e, rfl⟩, hpe⟩ := IsLocalization.surj (Submonoid.powers a) s
    obtain ⟨⟨q, _, e', rfl⟩, hqe⟩ := IsLocalization.surj (Submonoid.powers b) t
    obtain ⟨k, hk⟩ := exists_pow_mul_eq_of_away_eq hpe hqe hst
    set c := p * a ^ k with hc
    set d := q * b ^ k with hd
    have hcross : b ^ (e' + k) * c = a ^ (e + k) * d := by
      rw [hc, hd]; linear_combination hk
    have hpe' : s * algebraMap R (Localization.Away a) (a ^ (e + k)) =
        algebraMap R (Localization.Away a) c := by
      rw [hc, pow_add, map_mul, ← mul_assoc, hpe, ← map_mul]
    have hqe' : t * algebraMap R (Localization.Away b) (b ^ (e' + k)) =
        algebraMap R (Localization.Away b) d := by
      rw [hd, pow_add, map_mul, ← mul_assoc, hqe, ← map_mul]
    obtain ⟨c', d', hcd'⟩ := exists_mul_pow_add_mul_pow_eq_one hab (e + k) (e' + k)
    refine ⟨c' * c + d' * d, ?_, ?_⟩
    · exact algebraMap_eq_of_mul_pow_eq _ hpe' (by linear_combination c * hcd' - d' * hcross)
    · exact algebraMap_eq_of_mul_pow_eq _ hqe' (by linear_combination d * hcd' + c' * hcross)
  · rintro ⟨x, rfl, rfl⟩
    simp [awayLinearMap_algebraMap]

variable (R)

/-! ### Localizations of a module away from the elements `f i` -/

@[expose] public section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The localization of the module `M` at the element `f ∈ R`, i.e. `M_f`. -/
@[ega "0 1.2.3", ega "I 1.3.1"]
noncomputable abbrev moduleLocAway (f : R) (M : Type*) [AddCommGroup M] [Module R M] :
    Type _ :=
  LocalizedModule.Away f M

/-- The canonical `R`-linear localization map `λ_i : M → M_{f}`, `m ↦ m/1`. -/
@[ega "0 1.2.2" "partial, special case"]
noncomputable def localizationAwayMap (f : R) : M →ₗ[R] moduleLocAway f M :=
  LocalizedModule.mkLinearMap (Submonoid.powers f) M

/-- The map `Λ : M → ∏_{i} M_{f_i}` whose `i`-th component is `λ_i`,
i.e. `Λ(m) = (m/1, ..., m/1)`. -/
noncomputable def bigLambda (n : ℕ) (f : Fin n → R) :
    M →ₗ[R] (∀ i, moduleLocAway (f i) M) :=
  LinearMap.pi (fun i => localizationAwayMap (f i))

/-- The map `Φ : M → ∏_{i} M`, `Φ(m) = (f_1 m, ..., f_n m)`. -/
def bigPhi (n : ℕ) (f : Fin n → R) : M →ₗ[R] (Fin n → M) :=
  LinearMap.pi (fun i => (f i) • LinearMap.id)

/-- An element `m` lies in the kernel of `localizationAwayMap f : M → M_f` iff some nonnegative
power of `f` annihilates `m`. -/
@[ega "0 1.2.2" "kernel of M→M_f"]
theorem mem_ker_lambdaMap_iff (f : R) (m : M) :
    m ∈ LinearMap.ker (localizationAwayMap f) ↔ ∃ k : ℕ, (f ^ k) • m = (0 : M) := by
  rw [localizationAwayMap, LocalizedModule.mem_ker_mkLinearMap_iff]
  simp [Submonoid.mem_powers_iff]

/-- `bigLambda` is injective iff no nonzero element of `M` is annihilated by some power of each
`f i`. -/
theorem bigLambda_injective_iff_powerTorsion
    (n : ℕ) (f : Fin n → R) :
    Function.Injective (bigLambda (M := M) n f) ↔
      (∀ m : M, (∀ i, ∃ k : ℕ, ((f i) ^ k) • m = (0 : M)) → m = 0) := by
  simp [injective_iff_map_eq_zero, bigLambda, funext_iff, ← mem_ker_lambdaMap_iff]

/-- `bigPhi` is injective iff no nonzero element of `M` is annihilated by all the `f i`. -/
theorem bigPhi_injective_iff_commonAnnihilator
    (n : ℕ) (f : Fin n → R) :
    Function.Injective (bigPhi (M := M) n f) ↔
      (∀ m : M, (∀ i, (f i) • m = (0 : M)) → m = 0) := by
  simp [injective_iff_map_eq_zero, funext_iff, bigPhi]

/-- Suppose no nonzero element of `M` is annihilated by all the `f_i` simultaneously. Then any `m`
annihilated by some power of each `f_i` is `0`. -/
theorem common_annih_power_aux (n : ℕ) (f : Fin n → R)
    (hΦ : ∀ m : M, (∀ i, (f i) • m = (0 : M)) → m = 0) :
    ∀ (k : Fin n → ℕ) (m : M), (∀ i, (f i) ^ (k i) • m = (0 : M)) → m = 0 := by
  suffices H : ∀ s : ℕ, ∀ (k : Fin n → ℕ), (∑ i, k i) ≤ s → ∀ (m : M),
      (∀ i, (f i) ^ (k i) • m = (0 : M)) → m = 0 from fun k m hm => H _ k le_rfl m hm
  intro s
  induction s with
  | zero =>
    intro k hk m hm
    have hk0 : ∀ i, k i = 0 := by simpa using hk
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · exact hΦ m (fun i => (hn.false i).elim)
    · simpa [hk0 i] using hm i
  | succ s ih =>
    intro k hk m hm
    by_cases hzero : ∃ j, k j = 0
    · obtain ⟨j, hj⟩ := hzero
      simpa [hj] using hm j
    · push Not at hzero
      refine hΦ m fun j => ih (Function.update k j (k j - 1)) ?_ (f j • m) fun i => ?_
      · rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
        have := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j) k
        have := hzero j
        omega
      · by_cases hij : i = j
        · subst hij
          rw [Function.update_self, smul_smul, ← pow_succ,
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (hzero i)), hm i]
        · rw [Function.update_of_ne hij, smul_comm, hm i, smul_zero]

/-- The intersection of the `f_i`-power-torsion submodules is zero if and only if no nonzero
element is annihilated by all the `f_i` simultaneously. -/
theorem ker_torsion_inter_eq_zero_iff_common_annihilator_eq_zero
    (n : ℕ) (f : Fin n → R) :
    (∀ m : M, (∀ i, ∃ k : ℕ, ((f i) ^ k : R) • m = (0 : M)) → m = 0) ↔
      (∀ m : M, (∀ i, (f i) • m = (0 : M)) → m = 0) :=
  ⟨fun h m hm => h m fun i => ⟨1, by simpa using hm i⟩, fun hΦ m hm => by
    choose k hk using hm
    exact common_annih_power_aux n f hΦ k m hk⟩

/-- The map `Λ : M → ⨁_i M_{f_i}`, `m ↦ (m/1, ..., m/1)`,
is injective if and only if the map `Φ : M → ⨁_i M`, `m ↦ (f_1 m, ..., f_n m)`, is
injective. -/
@[stacks 0565]
theorem bigLambda_injective_iff_bigPhi_injective
    (n : ℕ) (f : Fin n → R) :
    Function.Injective (bigLambda (M := M) n f) ↔ Function.Injective (bigPhi (M := M) n f) := by
  rw [bigLambda_injective_iff_powerTorsion, bigPhi_injective_iff_commonAnnihilator]
  exact ker_torsion_inter_eq_zero_iff_common_annihilator_eq_zero n f
