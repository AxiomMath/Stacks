module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineOrders
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFibreTransport

/-!
# The prime cycle of a point of the affine line over the generic point of the base

Let `A` be a Noetherian domain and let `q` be a nonzero prime of `A[X]` lying over the zero ideal
of `A`: the generic point of an integral closed subscheme `W ⊊ Spec A × 𝔸¹` dominating
`Spec A`. In the proof of Stacks 02TT the generic fibre of `W` is cut out by a polynomial over
the function field of `A`, and over a dense open subscheme of `Spec A` the cycle `[W]` is the
principal divisor of that polynomial. This file proves that statement.

The polynomial is chosen without passing to the fraction field: take `f ∈ q` nonzero of least
degree and let `s` be its leading coefficient. Pseudo-division by `f`
(`Stacks.Chow.exists_pow_leadingCoeff_mul_eq_mul`) gives `s ^ N g ∈ (f)` for every `g ∈ q`. Hence
on the basic open `D(s)` of `Spec A[X]` the polynomial `f` generates the maximal ideal of the
local ring at `q`, so vanishes to order one there, and every prime of `D(s)` containing `f`
contains `q`, so `f` vanishes at no other point of codimension one.

## Main definitions

* `Stacks.Chow.polyBasicOpen` — the basic open subscheme `D(s)` of `Spec A[X]` for `s ∈ A`.

## Main results

* `Stacks.Chow.exists_pow_leadingCoeff_mul_eq_mul` — pseudo-division by a polynomial of least
  degree in an ideal of `A[X]`.
* `Stacks.Chow.eq_of_le_of_comap_eq_bot` — a nonzero prime of `A[X]` lying over zero has height
  one.
* `Stacks.Chow.coheight_eq_one_of_comap_eq_bot` — such a prime is a point of codimension one of
  `Spec A[X]`.
* `Stacks.Chow.exists_principalCycle_polyBasicOpen_eq_single` — on `D(s)`, the prime cycle of `q`
  is the principal divisor of a nonzero rational function.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace Stacks.Chow

/-- The basic open subscheme `D(s)` of `Spec A[X]` cut out by a constant `s ∈ A`. -/
abbrev polyBasicOpen {A : Type u} [CommRing A] (s : A) :
    (Spec (CommRingCat.of (Polynomial A))).Opens :=
  PrimeSpectrum.basicOpen (C s)

/-- Strict inclusion of prime ideals is strict inequality in the (reversed) order on `Spec`. -/
private theorem spec_lt_iff_asIdeal_lt {R : CommRingCat} {x y : Spec R} :
    x < y ↔ y.asIdeal < x.asIdeal := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, AffineSpace.spec_le_iff, AffineSpace.spec_le_iff]

/-- The image of a nonzero polynomial under the inverse of `ΓSpecIso` is nonzero. -/
private theorem ΓSpecIso_inv_ne_zero {A : Type u} [CommRing A] {f : A[X]} (hf0 : f ≠ 0) :
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv f ≠ 0 := fun h ↦
  hf0 (by simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom h)

section Algebra

variable {A : Type u} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- A nonzero ideal of `A[X]` contains a nonzero polynomial of least degree among its nonzero
elements. -/
theorem exists_mem_ne_zero_natDegree_le (I : Ideal A[X]) (hI : I ≠ ⊥) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, g ≠ 0 → f.natDegree ≤ g.natDegree := by
  classical
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n, ∃ f ∈ I, f ≠ 0 ∧ f.natDegree = n := ⟨_, g, hg, hg0, rfl⟩
  obtain ⟨f, hf, hf0, hfn⟩ := Nat.find_spec hex
  exact ⟨f, hf, hf0, fun g hg hg0 ↦ hfn.trans_le (Nat.find_min' hex ⟨g, hg, hg0, rfl⟩)⟩

/-- **Pseudo-division by a polynomial of least degree.** If `f` is a nonzero polynomial of least
degree in an ideal `I` of `A[X]` with leading coefficient `s`, then every `g ∈ I` satisfies
`s ^ N * g = h * f` for some `N` and `h`. -/
theorem exists_pow_leadingCoeff_mul_eq_mul (I : Ideal A[X]) {f : A[X]} (hf : f ∈ I)
    (hf0 : f ≠ 0) (hmin : ∀ g ∈ I, g ≠ 0 → f.natDegree ≤ g.natDegree) :
    ∀ g ∈ I, ∃ (N : ℕ) (h : A[X]), C f.leadingCoeff ^ N * g = h * f := by
  intro g
  induction hd : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ d ih =>
  intro hg
  by_cases hg0 : g = 0
  · exact ⟨0, 0, by simp [hg0]⟩
  have hle := hmin g hg hg0
  set s := f.leadingCoeff
  have hs0 : s ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set m := g.natDegree - f.natDegree
  set q := C g.leadingCoeff * X ^ m * f with hq
  set g' := C s * g - q with hg'
  have hg'I : g' ∈ I := I.sub_mem (I.mul_mem_left _ hg) (I.mul_mem_left _ hf)
  have hdegp : (C s * g).degree = g.natDegree := by
    rw [degree_C_mul hs0, degree_eq_natDegree hg0]
  have hdegq : q.degree = g.natDegree := by
    rw [hq, degree_mul, degree_C_mul_X_pow _ (leadingCoeff_ne_zero.mpr hg0),
      degree_eq_natDegree hf0]
    norm_cast
    omega
  have hlc : (C s * g).leadingCoeff = q.leadingCoeff := by
    simp only [hq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one]
    ring
  by_cases hg'0 : g' = 0
  · exact ⟨1, C g.leadingCoeff * X ^ m, by simpa using sub_eq_zero.mp hg'0⟩
  · have hlt : g'.degree < (C s * g).degree :=
      degree_sub_lt_left (by rw [hdegp, hdegq]) (mul_ne_zero (by simpa using hs0) hg0) hlc
    have hlt' : g'.natDegree < d := hd ▸ natDegree_lt_natDegree hg'0
      (by rwa [hdegp, ← degree_eq_natDegree hg0] at hlt)
    obtain ⟨N, h, hN⟩ := ih _ hlt' g' rfl hg'I
    refine ⟨N + 1, h + C s ^ N * (C g.leadingCoeff * X ^ m), ?_⟩
    rw [hg', hq] at hN
    linear_combination hN

variable {q : Ideal A[X]} [hq : q.IsPrime]

omit [IsDomain A] hq in
/-- A prime of `A[X]` lying over the zero ideal contains no nonzero constant. -/
theorem C_notMem_of_comap_eq_bot (hq0 : q.comap (C : A →+* A[X]) = ⊥) {a : A} (ha : a ≠ 0) :
    C a ∉ q :=
  fun h ↦ ha (Ideal.mem_bot.mp (hq0 ▸ Ideal.mem_comap.mpr h))

omit hq in
/-- If `f` has least degree among the nonzero elements of a prime `q` lying over zero, then any
prime `q'` containing `f` but not its leading coefficient contains `q`. -/
theorem le_of_mem_of_leadingCoeff_notMem {f : A[X]} (hf : f ∈ q) (hf0 : f ≠ 0)
    (hmin : ∀ g ∈ q, g ≠ 0 → f.natDegree ≤ g.natDegree) {q' : Ideal A[X]} [q'.IsPrime]
    (hfq' : f ∈ q') (hs : C f.leadingCoeff ∉ q') : q ≤ q' := by
  intro g hg
  obtain ⟨N, h, hN⟩ := exists_pow_leadingCoeff_mul_eq_mul q hf hf0 hmin g hg
  have hmem : C f.leadingCoeff ^ N * g ∈ q' := hN ▸ q'.mul_mem_left h hfq'
  exact (‹q'.IsPrime›.mem_or_mem hmem).resolve_left
    fun h1 ↦ hs (‹q'.IsPrime›.mem_of_pow_mem _ h1)

omit hq in
/-- A nonzero prime of `A[X]` lying over the zero ideal has height one: every nonzero prime
contained in it is equal to it. -/
theorem eq_of_le_of_comap_eq_bot (hq0 : q.comap (C : A →+* A[X]) = ⊥) {p : Ideal A[X]}
    [hp : p.IsPrime] (hpq : p ≤ q) (hp0 : p ≠ ⊥) : p = q := by
  have hqb : q ≠ ⊥ := fun h ↦ hp0 (le_bot_iff.mp (h ▸ hpq))
  obtain ⟨f, hf, hf0, hmin⟩ := exists_mem_ne_zero_natDegree_le q hqb
  obtain ⟨f', hf', hf'0, hmin'⟩ := exists_mem_ne_zero_natDegree_le p hp0
  have hs0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  refine le_antisymm hpq (le_of_mem_of_leadingCoeff_notMem hf hf0 hmin ?_
    fun h ↦ C_notMem_of_comap_eq_bot hq0 hs0 (hpq h))
  obtain ⟨N, h, hN⟩ := exists_pow_leadingCoeff_mul_eq_mul q hf hf0 hmin f' (hpq hf')
  have hmem : h * f ∈ p := hN ▸ p.mul_mem_left _ hf'
  refine (hp.mem_or_mem hmem).resolve_left fun hh ↦ ?_
  have hdf : 0 < f.natDegree := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero h0
    exact C_notMem_of_comap_eq_bot hq0 (fun h ↦ hf0 (by rw [hfC, h, map_zero])) (hfC ▸ hf)
  have hl : (h * f).natDegree = f'.natDegree := by
    rw [← hN, ← C_pow, natDegree_C_mul (pow_ne_zero _ hs0)]
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hs0)) hf'0 (hN.trans (zero_mul f))
  have := hmin' h hh hh0
  have := natDegree_mul hh0 hf0
  omega

end Algebra

section Scheme

variable {A : Type u} [CommRing A] [IsDomain A]

/-- A nonzero prime of `A[X]` lying over the zero ideal of `A` is a point of codimension one of
`Spec A[X]`. -/
theorem coheight_eq_one_of_comap_eq_bot (q : Spec (CommRingCat.of (Polynomial A)))
    (hq : q.asIdeal.comap (C : A →+* Polynomial A) = ⊥) (hq0 : q.asIdeal ≠ ⊥) :
    Order.coheight q = 1 := by
  have := q.2
  let η : Spec (CommRingCat.of (Polynomial A)) := ⟨⊥, inferInstance⟩
  have hmax : ∀ y : Spec (CommRingCat.of (Polynomial A)), y.asIdeal = ⊥ → IsMax y :=
    fun y hy b _ ↦ (AffineSpace.spec_le_iff _ _ _).mpr (hy ▸ bot_le)
  have hlt : q < η := spec_lt_iff_asIdeal_lt.mpr (bot_lt_iff_ne_bot.mpr hq0)
  refine le_antisymm (Order.coheight_le_coe_iff.mpr fun y hy ↦ ?_) ?_
  · have := y.2
    by_cases hy0 : y.asIdeal = ⊥
    · exact (Order.coheight_eq_zero.mpr (hmax y hy0)).trans_lt zero_lt_one
    · exact absurd (PrimeSpectrum.ext (eq_of_le_of_comap_eq_bot hq
        (spec_lt_iff_asIdeal_lt.mp hy).le hy0)) hy.ne'
  · simpa [Order.coheight_eq_zero.mpr (hmax η rfl)] using Order.coheight_add_one_le hlt

/-- The order of vanishing at a point of codimension one of `Spec A[X]` of the rational function
of a polynomial is its order of vanishing in the localization at that point. -/
theorem ord_germToFunctionField_spec [IsNoetherianRing A] {z : Spec (CommRingCat.of A[X])}
    [z.asIdeal.IsPrime] [Nonempty (⊤ : (Spec (CommRingCat.of A[X])).Opens)]
    (hco : Order.coheight z = 1) {f : A[X]} (hf0 : f ≠ 0) {n : ℕ}
    (hn : Ring.ord (Localization.AtPrime z.asIdeal) (algebraMap A[X] _ f) = n) :
    (Spec (CommRingCat.of A[X])).ord ((Spec (CommRingCat.of A[X])).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv f)) z = n := by
  refine ord_eq_ringOrd_germ hco (show z ∈ (⊤ : (Spec (CommRingCat.of A[X])).Opens) from
    trivial) _ (ΓSpecIso_inv_ne_zero hf0) ?_
  have h1 : ((Spec (CommRingCat.of A[X])).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv f) =
        (Spec.stalkIso (CommRingCat.of A[X]) z).inv
          (algebraMap A[X] (Localization.AtPrime z.asIdeal) f) :=
    (ConcreteCategory.congr_hom
      (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of A[X]) z) f).symm
  rw [h1]
  exact (ord_of_ringEquiv (Spec.stalkIso (CommRingCat.of A[X]) z).commRingCatIsoToRingEquiv.symm
    (algebraMap A[X] (Localization.AtPrime z.asIdeal) f)).trans hn

open Classical in
/-- The order of vanishing of the polynomial `f`, of least degree in a nonzero prime `q` lying
over zero, at a point `z` of `D(s)` — where `s` is the leading coefficient of `f` — is one at `q`
and zero elsewhere. -/
theorem ord_germToFunctionField_spec_eq [IsNoetherianRing A]
    [Nonempty (⊤ : (Spec (CommRingCat.of A[X])).Opens)] (q : Spec (CommRingCat.of A[X]))
    (hq : q.asIdeal.comap (C : A →+* Polynomial A) = ⊥) (hq0 : q.asIdeal ≠ ⊥) {f : A[X]}
    (hf : f ∈ q.asIdeal) (hf0 : f ≠ 0)
    (hmin : ∀ g ∈ q.asIdeal, g ≠ 0 → f.natDegree ≤ g.natDegree)
    (z : Spec (CommRingCat.of A[X])) (hz : C f.leadingCoeff ∉ z.asIdeal) :
    (Spec (CommRingCat.of A[X])).ord ((Spec (CommRingCat.of A[X])).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv f)) z = if z = q then 1 else 0 := by
  have := q.2
  have := z.2
  have hcoq := coheight_eq_one_of_comap_eq_bot q hq hq0
  by_cases hco : Order.coheight z = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco, if_neg]
    rintro rfl
    exact hco hcoq
  by_cases hfz : f ∈ z.asIdeal
  · have hqz : q.asIdeal ≤ z.asIdeal := le_of_mem_of_leadingCoeff_notMem hf hf0 hmin hfz hz
    have hzq : z = q := by
      by_contra hne
      have h := Order.coheight_add_one_le (spec_lt_iff_asIdeal_lt.mpr
        (hqz.lt_of_ne fun h ↦ hne (PrimeSpectrum.ext h.symm)))
      rw [hco, hcoq] at h
      exact absurd h (by decide)
    subst hzq
    rw [if_pos rfl]
    refine ord_germToFunctionField_spec hco hf0 (ord_eq_one_of_span_eq_maximalIdeal ?_)
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal z.asIdeal (Localization.AtPrime z.asIdeal)]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hf
    · refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
      obtain ⟨N, h, hN⟩ := exists_pow_leadingCoeff_mul_eq_mul z.asIdeal hf hf0 hmin g hg
      have hu : IsUnit (algebraMap A[X] (Localization.AtPrime z.asIdeal)
          (C f.leadingCoeff ^ N)) :=
        IsLocalization.map_units (Localization.AtPrime z.asIdeal)
          (⟨C f.leadingCoeff ^ N, fun h ↦ hz (z.2.mem_of_pow_mem _ h)⟩ :
            z.asIdeal.primeCompl)
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul, hN, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [if_neg (show ¬ z = q by rintro rfl; exact hfz hf)]
    refine ord_germToFunctionField_spec hco hf0 ?_
    exact_mod_cast ord_eq_zero_of_isUnit (IsLocalization.map_units
      (Localization.AtPrime z.asIdeal) (⟨f, hfz⟩ : z.asIdeal.primeCompl))

/-- **The prime cycle of a point of `𝔸¹` over the generic point of the base is principal over a
dense open of the base.** Let `A` be a Noetherian domain and `q` a nonzero prime of `A[X]` lying
over the zero ideal of `A`. Then there is a nonzero `s ∈ A` such that, on the basic open
subscheme `D(s)` of `Spec A[X]`, the prime cycle of `q` is the principal divisor of a nonzero
rational function.

The rational function is a polynomial `f` of least degree in `q` and `s` is its leading
coefficient: over `A_s` the polynomial `f / s` is monic and generates `q` by the division
algorithm, so `f` vanishes to order one at `q` and nowhere else on `D(s)`. This is the step of
the proof of Stacks 02TT in which the generic fibre of `W ⊆ Y × 𝔸¹` is cut out by a polynomial
`P ∈ R(Y)[T]`. -/
theorem exists_principalCycle_polyBasicOpen_eq_single [IsNoetherianRing A]
    (q : Spec (CommRingCat.of (Polynomial A)))
    (hq : q.asIdeal.comap (C : A →+* Polynomial A) = ⊥) (hq0 : q.asIdeal ≠ ⊥) :
    ∃ s : A, s ≠ 0 ∧ ∃ hqs : q ∈ polyBasicOpen s,
      ∀ [IsIntegral (polyBasicOpen s).toScheme] [IsLocallyNoetherian (polyBasicOpen s).toScheme],
      ∃ g : (polyBasicOpen s).toScheme.functionField,
        g ≠ 0 ∧ principalCycle (polyBasicOpen s).toScheme g =
          @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _
            (⟨q, hqs⟩ : (polyBasicOpen s).toScheme) 1 := by
  have := q.2
  obtain ⟨f, hf, hf0, hmin⟩ := exists_mem_ne_zero_natDegree_le q.asIdeal hq0
  have hs0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hqs : C f.leadingCoeff ∉ q.asIdeal := C_notMem_of_comap_eq_bot hq hs0
  refine ⟨f.leadingCoeff, hs0, hqs, fun {_ _} ↦ ?_⟩
  set D := polyBasicOpen f.leadingCoeff
  have : Nonempty D := ⟨⟨q, hqs⟩⟩
  have : Nonempty (⊤ : (Spec (CommRingCat.of A[X])).Opens) := ⟨⟨q, trivial⟩⟩
  have : IsDominant D.ι := isDominant_of_isOpenImmersion' D.ι
  set fX := (Spec (CommRingCat.of A[X])).germToFunctionField ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv f)
  have hfX0 : fX ≠ 0 := fun h ↦ ΓSpecIso_inv_ne_zero hf0
    (Scheme.germToFunctionField_injective (Spec (CommRingCat.of A[X])) ⊤
      (h.trans (map_zero _).symm))
  refine ⟨functionFieldEquiv_openImmersion D.ι fX,
    (map_ne_zero_iff _ (functionFieldEquiv_openImmersion D.ι).injective).mpr hfX0,
    Function.locallyFinsuppWithin.ext fun y ↦ ?_⟩
  rw [principalCycle_functionFieldEquiv_openImmersion_apply, principalCycle_apply,
    show D.ι y = y.1 from rfl, ord_germToFunctionField_spec_eq q hq hq0 hf hf0 hmin y.1 y.2]
  refine Eq.trans ?_ (@Function.locallyFinsuppWithin.single_apply D.toScheme _ ℤ
    (Classical.decEq _) _ ⟨q, hqs⟩ y 1).symm
  by_cases hy : y.1 = q
  · rw [if_pos hy]
    exact (@if_pos _ (Classical.decEq _ _ _) (Subtype.ext hy) _ _ _).symm
  · rw [if_neg hy]
    exact (@if_neg _ (Classical.decEq _ _ _) (fun h ↦ hy (congrArg Subtype.val h)) _ _ _).symm

end Scheme

end Stacks.Chow
