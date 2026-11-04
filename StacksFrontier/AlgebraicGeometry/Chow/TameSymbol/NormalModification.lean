module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FiniteExtension
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tame symbol of a one-dimensional Noetherian local domain

Stacks 0EAH asks, for a one-dimensional Noetherian local ring `(A, 𝔪)`, for a tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

satisfying Stacks 0EAI, 0EAJ and 0EAK — equivalently, by `Stacks.Chow.RegularTameSymbol.extend`,
for a symbol on pairs of nonzerodivisors of `A` satisfying Stacks 0EAL, 0EAM, 0EAN and 0EAP. The
source's recipe Stacks 0EAQ chooses, for each pair of nonzerodivisors, a finite modification
`A ⊆ B` in which both become unit multiples of powers of one parameter (Stacks 0EAG), and its
well-definedness is Stacks 0EAR.

For a one-dimensional Noetherian local domain that admits one *normal* finite modification,
this file produces such a symbol with no choice depending on the pair. If `A ⊆ B` is
module-finite with `B` an integrally closed domain and `B/A` annihilated by a power of `𝔪`, then
every localization `B_𝔮` at a maximal ideal is a discrete valuation ring, so a single `B` carries
a tame symbol on *all* pairs of nonzerodivisors at once — `Stacks.Chow.dvrRegularTameSymbol` at
each `𝔮` — and Stacks 0EAT assembles them into a symbol on `A` by
`Stacks.Chow.normPushforwardOfModuleFinite`.

`A` itself is not assumed integrally closed, so `A` need not be a discrete valuation ring. Taking
for `B` the integral closure of `A` in its fraction field covers exactly the one-dimensional
Noetherian local domains with a finite normalization, such as the local rings of schemes of finite
type over a field.

## Main definitions

* `Stacks.Chow.localizationSymbol` — the tame symbol at a maximal ideal of a normal finite
  modification.
* `Stacks.Chow.normPushforwardOfIsIntegrallyClosed` — Stacks 0EAH on nonzerodivisors, from a
  normal finite modification.
* `Stacks.Chow.normPushforwardOfFiniteIntegralClosure`,
  `Stacks.Chow.tameSymbolOfFiniteIntegralClosure` — the same with the modification taken to be
  the integral closure in the fraction field, on nonzerodivisors and on `Q(A)^*`.
* `Stacks.Chow.heightOneSymbolOfFiniteIntegralClosure` — the symbol at a height-one prime of a
  Noetherian domain.

## Main results

* `Stacks.Chow.not_isAssociatedPrime_maximalIdeal` — `𝔪` is not an associated prime of a domain
  extension of `A`.
* `Stacks.Chow.dimensionLEOne_of_moduleFinite`,
  `Stacks.Chow.height_eq_one_of_isMaximal` — a module-finite domain extension of a
  one-dimensional domain is one-dimensional, and each of its maximal ideals has height one.
* `Stacks.Chow.isDiscreteValuationRing_localization_isMaximal` — a normal finite modification is
  a discrete valuation ring at each maximal ideal.
* `Stacks.Chow.exists_nonZeroDivisor_smul_mem_range`,
  `Stacks.Chow.exists_maximalIdeal_pow_smul_le` — a module-finite extension inside `Q(A)` is
  carried into `A` by one nonzerodivisor, and such a quotient is annihilated by a power of `𝔪`.
* `Stacks.Chow.krullDimLE_one_localization_of_height_eq_one`,
  `Stacks.Chow.not_isField_localization_of_height_eq_one` — a height-one localization of a
  Noetherian domain is one-dimensional and not a field.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.Chow

/-! ### The hypotheses of Stacks 0EAT for a domain extension -/

/-- The maximal ideal of a Noetherian local ring that is not a field is not an associated prime
of a domain extension. -/
theorem not_isAssociatedPrime_maximalIdeal {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {B : Type v} [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (hA : ¬ IsField A) :
    ¬ IsAssociatedPrime (maximalIdeal A) B := by
  intro h
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp h
  by_cases hx0 : x = 0
  · subst hx0
    refine hprime.ne_top ?_
    rw [hx, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  · refine hA (isField_iff_maximalIdeal_eq.mpr ?_)
    rw [hx, eq_bot_iff]
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def] at hr
    exact Ideal.mem_bot.mpr (hinj (by rw [(mul_eq_zero.mp hr).resolve_right hx0, map_zero]))

/-- A module-finite domain extension of a one-dimensional domain is one-dimensional. -/
theorem dimensionLEOne_of_moduleFinite (A : Type u) [CommRing A] [IsDomain A]
    [Ring.KrullDimLE 1 A] (B : Type v) [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] : Ring.DimensionLEOne B :=
  have : Ring.DimensionLEOne A :=
    ⟨fun hp0 hp => (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance) _ hp0 hp⟩
  Ring.DimensionLEOne.of_isIntegral A B

/-- Every maximal ideal of a module-finite domain extension of a one-dimensional domain that is
not a field has height one. -/
theorem height_eq_one_of_isMaximal (A : Type u) [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    {B : Type v} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] :
    q.height = 1 := by
  have := dimensionLEOne_of_moduleFinite A B
  have hq0 : q ≠ ⊥ := fun hq =>
    hA (isField_of_isIntegral_of_isField (S := B) hinj
      (Ring.isField_iff_maximal_bot.mpr (hq ▸ (inferInstance : q.IsMaximal))))
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr fun hz =>
    hq0 (Ideal.height_eq_zero_iff_eq_bot.mp hz))
  have h1 := Ideal.height_le_ringKrullDim_of_isPrime (I := q)
  have hd : ringKrullDim B ≤ (1 : ℕ) := Ring.krullDimLE_iff.mp inferInstance
  exact_mod_cast h1.trans hd

/-! ### The symbol of a normal finite modification -/

section Modification

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  [IsDomain A] (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  [IsIntegrallyClosed B]

omit [IsLocalRing A] in
/-- A normal finite modification of a one-dimensional Noetherian local domain is a discrete
valuation ring at each maximal ideal. -/
@[ega "II 7.1.6" "special case"]
theorem isDiscreteValuationRing_localization_isMaximal (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) :=
  have := IsNoetherianRing.of_finite A B
  isDiscreteValuationRing_localization_of_height_eq_one q
    (height_eq_one_of_isMaximal A hA hinj q)

/-- The tame symbol `Stacks.Chow.dvrRegularTameSymbol` of the discrete valuation ring `B_𝔮`, at a
maximal ideal `𝔮` of a normal finite modification `B`. -/
noncomputable def localizationSymbol (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : MaximalSpectrum B) :
    RegularTameSymbol (Localization.AtPrime q.asIdeal) :=
  haveI := q.isMaximal
  haveI := isDiscreteValuationRing_localization_isMaximal A B hA hinj q.asIdeal
  dvrRegularTameSymbol (Classical.choose_spec
    (IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q.asIdeal)))

/-- The tame symbol on nonzerodivisors of a one-dimensional Noetherian local domain `A` with a
normal finite modification: for `A ⊆ B` module-finite with `B` an integrally closed domain and
`B/A` annihilated by a power of `𝔪`,

`∂_A(a, b) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}(∂_{B_𝔮}(a, b))`,

the product over the maximal ideals `𝔮` of `B`. -/
@[stacks 0EAH "on nonzerodivisors, for a local domain with a normal finite modification"]
noncomputable def normPushforwardOfIsIntegrallyClosed (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    RegularTameSymbol A :=
  normPushforwardOfModuleFinite (not_isAssociatedPrime_maximalIdeal hinj hA)
    (localizationSymbol A B hA hinj) hinj hquot

end Modification

/-! ### Annihilation of the modification by a power of the maximal ideal -/

/-- A module over a one-dimensional Noetherian local ring is carried into a submodule by a
power of `𝔪` as soon as it is carried there by a single nonzerodivisor. -/
theorem exists_maximalIdeal_pow_smul_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] {M : Type v} [AddCommGroup M] [Module A M]
    {N : Submodule A M} {d : A} (hd : d ∈ nonZeroDivisors A) (hdM : ∀ x : M, d • x ∈ N) :
    ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A M) ≤ N := by
  have hrad : maximalIdeal A ≤ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hJ, hJp⟩
    exact (Stacks.Length.eq_maximalIdeal_of_mem_of_isPrime J hd
      (hJ (Ideal.mem_span_singleton_self d))).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨n, Submodule.smul_le.mpr fun r hr x _ => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hn hr)
  rw [← hc, mul_smul]
  exact N.smul_mem c (hdM x)

/-- A module-finite extension of `A` inside its total ring of fractions is carried into `A` by
one nonzerodivisor. -/
theorem exists_nonZeroDivisor_smul_mem_range (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    [Algebra A B] [Module.Finite A B] {K : Type*} [CommRing K] [Algebra A K] [Algebra B K]
    [IsScalarTower A B K] [IsLocalization (nonZeroDivisors A) K]
    (hBK : Function.Injective (algebraMap B K)) :
    ∃ d ∈ nonZeroDivisors A, ∀ b : B, d • b ∈ LinearMap.range (Algebra.linearMap A B) := by
  classical
  obtain ⟨s, hs⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule A B).FG)
  have key : ∀ x : B, ∃ d : nonZeroDivisors A,
      (d : A) • x ∈ LinearMap.range (Algebra.linearMap A B) := by
    intro x
    obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj (nonZeroDivisors A) (algebraMap B K x)
    refine ⟨d, a, hBK ?_⟩
    have hsm : algebraMap B K ((d : A) • x) = algebraMap B K x * algebraMap A K (d : A) := by
      rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply A B K, mul_comm]
    rw [Algebra.linearMap_apply, hsm, ← IsScalarTower.algebraMap_apply A B K]
    exact had.symm
  choose dd hdd using key
  refine ⟨∏ x ∈ s, (dd x : A), prod_mem fun x _ => (dd x).2, fun b => ?_⟩
  have hle : (⊤ : Submodule A B) ≤ (LinearMap.range (Algebra.linearMap A B)).comap
      (LinearMap.lsmul A B (∏ x ∈ s, (dd x : A))) := by
    rw [← hs, Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
    rw [← Finset.prod_erase_mul s _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hdd x)
  exact hle Submodule.mem_top

/-! ### The symbol from a finite integral closure -/

section IntegralClosure

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  [IsDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  [Module.Finite A (integralClosure A K)]

/-- The tame symbol on nonzerodivisors of a one-dimensional Noetherian local domain whose
integral closure `A'` in its fraction field is module finite:
`Stacks.Chow.normPushforwardOfIsIntegrallyClosed` with `B = A'`. -/
noncomputable def normPushforwardOfFiniteIntegralClosure (hA : ¬ IsField A) :
    RegularTameSymbol A :=
  haveI : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (L := K) K
  have hinj : Function.Injective (algebraMap A (integralClosure A K)) := fun x y h =>
    IsFractionRing.injective A K (congrArg Subtype.val h)
  normPushforwardOfIsIntegrallyClosed A (integralClosure A K) hA hinj
    (by
      obtain ⟨d, hd, hdB⟩ := exists_nonZeroDivisor_smul_mem_range A (integralClosure A K)
        (K := K) Subtype.val_injective
      exact exists_maximalIdeal_pow_smul_le hd hdB)

/-- The tame symbol `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of a one-dimensional Noetherian local domain
`A` whose integral closure in its fraction field is module finite: the extension
`Stacks.Chow.RegularTameSymbol.extend` of `Stacks.Chow.normPushforwardOfFiniteIntegralClosure`. -/
@[stacks 0EAH "on Q(A)^*, for a local domain with a module-finite integral closure"]
noncomputable def tameSymbolOfFiniteIntegralClosure (hA : ¬ IsField A)
    (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q] : TameSymbol A Q :=
  (normPushforwardOfFiniteIntegralClosure A K hA).extend Q

end IntegralClosure

/-! ### The symbol at a height-one prime -/

section HeightOne

variable {A : Type u} [CommRing A]

/-- The localization at a height-one prime is one-dimensional. -/
theorem krullDimLE_one_localization_of_height_eq_one (p : Ideal A) [p.IsPrime]
    (hp : p.height = 1) : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
  refine Ring.krullDimLE_iff.mpr ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
  rfl

/-- The localization at a height-one prime is not a field. -/
theorem not_isField_localization_of_height_eq_one (p : Ideal A) [p.IsPrime]
    (hp : p.height = 1) : ¬ IsField (Localization.AtPrime p) := by
  intro h
  have hz := ringKrullDim_eq_zero_of_isField h
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp] at hz
  simp at hz

/-- The tame symbol `Stacks.Chow.normPushforwardOfFiniteIntegralClosure` of the localization of a
Noetherian domain at a height-one prime, when the integral closure of that localization is
module finite. -/
noncomputable def heightOneSymbolOfFiniteIntegralClosure [IsDomain A] [IsNoetherianRing A]
    (p : HeightOnePrime A)
    [Module.Finite (Localization.AtPrime p.1.asIdeal)
      (integralClosure (Localization.AtPrime p.1.asIdeal)
        (FractionRing (Localization.AtPrime p.1.asIdeal)))] :
    RegularTameSymbol (Localization.AtPrime p.1.asIdeal) :=
  haveI := krullDimLE_one_localization_of_height_eq_one p.1.asIdeal p.2
  normPushforwardOfFiniteIntegralClosure (Localization.AtPrime p.1.asIdeal)
    (FractionRing (Localization.AtPrime p.1.asIdeal))
    (not_isField_localization_of_height_eq_one p.1.asIdeal p.2)

end HeightOne

/-! For a local domain with a normal finite modification, the product formula of Stacks 0EAQ
satisfies the four identities 0EAL, 0EAM, 0EAN and 0EAP on nonzerodivisors, which is what being a
term of `Stacks.Chow.RegularTameSymbol` asserts. -/
add_to_stacks 0EAS "that the product formula of Stacks 0EAQ satisfies (4), (5), (6), (7), for a \
local domain with a normal finite modification, where one extension serves every pair of \
nonzerodivisors" Stacks.Chow.normPushforwardOfIsIntegrallyClosed

end Stacks.Chow

end
