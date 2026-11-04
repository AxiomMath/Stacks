module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Formula

/-!
# The tame symbol of Stacks 0EAQ along a finite extension

Let `(A, 𝔪)` be a Noetherian local ring of dimension one, let `A ⊆ B` be a finite ring extension
with `B / A` annihilated by a power of `𝔪` and `𝔪` not an associated prime of `B`, and let
`a, b ∈ A` be nonzerodivisors. Stacks 0EAT asserts

`∂_A(a, b) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}(∂_{B_j}(a, b))`,

the product over the maximal ideals `𝔪_j` of `B`, where `∂` is the tame symbol defined by the
formula Stacks 0EAQ, `Stacks.Chow.tameSymbolFormula`. Each `B_j` is again a Noetherian local
ring of dimension one in which `a` and `b` are nonzerodivisors, so the right-hand side makes
sense.

The proof compares both sides with norm pushforwards of tame symbols from a single finite
extension. Choose a preparation `A ⊆ B'` of `a, b` (Stacks 0EAG) and let
`C = (B ⊗_A B') / (𝔪`-power torsion`)`, which contains both `B` and `B'`. By Stacks 0EAR the
left-hand side is the norm pushforward to `A` of any family of tame symbols on the local rings of
`C`. Transitivity of norms (Stacks 0BIJ) writes that pushforward as the product over the maximal
ideals `𝔮` of `B` of the norms of the pushforwards to `B_𝔮` from the semilocalization `C_𝔮`. The
factorizations of `a, b` in the local rings of `B'` map to factorizations in the local rings of
`C_𝔮`, so `C_𝔮` carries a preparation of `a, b` over `B_𝔮`, and by Stacks 0EAR again the
pushforward to `B_𝔮` is `∂_{B_𝔮}(a, b)`.

## Main results

* `Stacks.Chow.tameSymbolFormula_eq_symbolValue` — the tame symbol of Stacks 0EAQ is the value of
  the formula on any preparation.
* `Stacks.Chow.normPushforward_eq_tameSymbolFormula` — the norm pushforward of tame symbols from a
  finite extension in whose local rings the two elements factor is the tame symbol of Stacks 0EAQ.
* `Stacks.Chow.ringKrullDim_localizationAtPrime_eq_one` — the local rings of `B` have dimension
  one.
* `Stacks.Chow.tameSymbolFormula_eq_finprod_norm` — Stacks 0EAT.

## References

* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

universe u v w

namespace Stacks.Chow

/-- **A factorization by a nonzerodivisor.** If the members of a family of nonzerodivisors are
units times powers of a common element `π`, they are units times powers of a common
nonzerodivisor: either `π` is one, or every exponent vanishes and `1` serves. -/
theorem exists_isRegular_factorization {T : Type*} [CommRing T] {r : ℕ} {t : Fin r → T}
    (ht : ∀ i, IsRegular (t i)) {π : T} {u : Fin r → Tˣ} {e : Fin r → ℕ}
    (h : ∀ i, t i = u i * π ^ e i) :
    ∃ (π' : T) (u' : Fin r → Tˣ) (e' : Fin r → ℕ), IsRegular π' ∧
      ∀ i, t i = u' i * π' ^ e' i := by
  by_cases hπ : IsRegular π
  · exact ⟨π, u, e, hπ, h⟩
  refine ⟨1, u, fun _ ↦ 0, isRegular_one, fun i ↦ ?_⟩
  have he : e i = 0 := by
    by_contra hne
    have hreg := ht i
    rw [h i] at hreg
    exact hπ ((IsRegular.pow_iff (Nat.pos_of_ne_zero hne)).mp (isRegular_mul_iff.mp hreg).2)
  rw [h i, he, pow_zero, pow_zero]

section Formula

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The tame symbol of Stacks 0EAQ is the formula of a prepared extension, with the instances of
its maximal spectrum installed. -/
private theorem exists_prepared_extension_symbolValue (hdim : ringKrullDim A = 1) {a₁ a₂ : A}
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) :
    ∃ (E : PreparedTameSymbolExtension ![a₁, a₂]) (_ : Fintype (MaximalSpectrum E.extension))
      (_ : ∀ q : MaximalSpectrum E.extension,
        IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))),
      tameSymbolFormula hdim a₁ a₂ ha₁ ha₂ = E.preparation.symbolValue 0 1 := by
  rw [tameSymbolFormula]
  generalize (nonempty_preparedTameSymbolExtension hdim ha₁ ha₂).some = E
  have := E.preparation.finite_maximalSpectrum
  let := Fintype.ofFinite (MaximalSpectrum E.extension)
  have := fun q ↦ E.preparation.isLocalHom q
  exact ⟨E, ‹_›, this, E.preparation.value_eq_symbolValue 0 1⟩

/-- **The tame symbol of Stacks 0EAQ is the value of the formula on any preparation**, by
Stacks 0EAR. -/
theorem tameSymbolFormula_eq_symbolValue (hdim : ringKrullDim A = 1) {a₁ a₂ : A}
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) {B : Type v} [CommRing B] [Algebra A B]
    (P : TameSymbolPreparation ![a₁, a₂] B) [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))] :
    tameSymbolFormula hdim a₁ a₂ ha₁ ha₂ = P.symbolValue 0 1 := by
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  obtain ⟨E, _, _, h⟩ := exists_prepared_extension_symbolValue hdim ha₁ ha₂
  exact h.trans (TameSymbolPreparation.symbolValue_eq_symbolValue _ P 0 1)

/-- **The tame symbol of two units is `1`.** -/
theorem tameSymbolFormula_eq_one (hdim : ringKrullDim A = 1) {a₁ a₂ : A}
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) (hu₁ : IsUnit a₁) (hu₂ : IsUnit a₂) :
    tameSymbolFormula hdim a₁ a₂ ha₁ ha₂ = 1 := by
  obtain ⟨E, _, _, h⟩ := exists_prepared_extension_symbolValue hdim ha₁ ha₂
  exact h.trans (E.preparation.symbolValue_eq_one 0 1 hu₁ hu₂)

end Formula

section Refinement

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
  {D : Type v} [CommRing D] [Algebra R D] [Module.Finite R D] [Fintype (MaximalSpectrum D)]
  [∀ s : MaximalSpectrum D, IsLocalHom (algebraMap R (Localization.AtPrime s.asIdeal))]

/-- **A norm pushforward of tame symbols is the tame symbol of Stacks 0EAQ.** Let `R ⊆ D` be a
finite extension with `D / R` annihilated by a power of the maximal ideal, which is not an
associated prime of `D`. If two nonzerodivisors `x, y` of `R` are, in every local ring of `D`,
units times powers of a common element, then `D` with these factorizations is a preparation of
`x, y`, and by Stacks 0EAR the norm pushforward to `R` of any family of tame symbols on the local
rings of `D` is `∂_R(x, y)`. -/
theorem normPushforward_eq_tameSymbolFormula (hdim : ringKrullDim R = 1)
    (hD : ¬ IsAssociatedPrime (maximalIdeal R) D)
    (symb : ∀ s : MaximalSpectrum D, RegularTameSymbol (Localization.AtPrime s.asIdeal))
    (hinj : Function.Injective (algebraMap R D))
    (hquot : ∃ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R D) ≤
      LinearMap.range (Algebra.linearMap R D))
    (x y : nonZeroDivisors R)
    (hfac : ∀ s : MaximalSpectrum D, ∃ (π : Localization.AtPrime s.asIdeal)
      (u : Fin 2 → (Localization.AtPrime s.asIdeal)ˣ) (e : Fin 2 → ℕ), ∀ i,
        algebraMap D (Localization.AtPrime s.asIdeal)
          (algebraMap R D ((![(x : R), (y : R)] : Fin 2 → R) i)) = u i * π ^ e i) :
    normPushforward hD symb hinj hquot x y =
      tameSymbolFormula hdim (x : R) (y : R) (isRegular_iff_mem_nonZeroDivisors.mpr x.2)
        (isRegular_iff_mem_nonZeroDivisors.mpr y.2) := by
  classical
  have hmem : ∀ i, (![(x : R), (y : R)] : Fin 2 → R) i ∈ nonZeroDivisors R := by
    intro i
    fin_cases i
    exacts [x.2, y.2]
  have hreg : ∀ s : MaximalSpectrum D, ∃ (π : Localization.AtPrime s.asIdeal)
      (u : Fin 2 → (Localization.AtPrime s.asIdeal)ˣ) (e : Fin 2 → ℕ), IsRegular π ∧ ∀ i,
        algebraMap D (Localization.AtPrime s.asIdeal)
          (algebraMap R D ((![(x : R), (y : R)] : Fin 2 → R) i)) = u i * π ^ e i := by
    intro s
    obtain ⟨π, u, e, h⟩ := hfac s
    refine exists_isRegular_factorization (fun i ↦ ?_) h
    rw [← IsScalarTower.algebraMap_apply]
    exact isRegular_iff_mem_nonZeroDivisors.mpr (toExtensionNonZeroDivisor hD s ⟨_, hmem i⟩).2
  choose π u e hπ h using hreg
  let Q : TameSymbolPreparation ![(x : R), (y : R)] D :=
    { finite := inferInstance
      algebraMap_injective := hinj
      quotient_annihilated_by_maximalIdeal_power := hquot
      parameter q _ := π ⟨q, inferInstance⟩
      parameter_isRegular q _ := hπ ⟨q, inferInstance⟩
      factorUnit q _ := u ⟨q, inferInstance⟩
      exponent q _ := e ⟨q, inferInstance⟩
      factorization q _ i := h ⟨q, inferInstance⟩ i }
  rw [tameSymbolFormula_eq_symbolValue hdim _ _ Q]
  exact Q.normPushforward_eq_symbolValue (C := D) hD hD symb (fun _ _ h ↦ h) hinj hquot 0 1 x y
    rfl rfl

end Refinement

section Fibre

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
  {C : Type w} [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Algebra.IsIntegral B C]
  {B' : Type*} [CommRing B'] [Algebra A B'] [Algebra B' C] [IsScalarTower A B' C]
  [Algebra.IsIntegral B' C]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- **Local factorizations along the fibre.** Let `B` and `B'` be `A`-algebras with a common
extension `C`, integral over both. Factorizations `a_i = u_i π ^ {e_i}` of a family of `A` in the
local rings of `B'` (a preparation) give factorizations of its image in every local ring of the
semilocalization `C_𝔮` of `C` at a maximal ideal `𝔮` of `B`: that local ring is the local ring of
`C` at a maximal ideal `𝔯`, which receives the local ring of `B'` at `𝔯 ∩ B'`. -/
theorem exists_factorization_semilocalization {r : ℕ} {a : Fin r → A}
    (P : TameSymbolPreparation a B') (q : MaximalSpectrum B)
    (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) :
    ∃ (π : Localization.AtPrime v.asIdeal) (u : Fin r → (Localization.AtPrime v.asIdeal)ˣ)
      (e : Fin r → ℕ), ∀ i,
        algebraMap (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
          (Localization.AtPrime v.asIdeal)
          (algebraMap (Localization.AtPrime q.asIdeal)
            (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
            (algebraMap A (Localization.AtPrime q.asIdeal) (a i))) = u i * π ^ e i := by
  have : (v.asIdeal.under C).IsMaximal := (maximalSpectrumSigmaEquiv B C ⟨q, v⟩).isMaximal
  have : ((v.asIdeal.under C).under B').IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  let g : Localization.AtPrime ((v.asIdeal.under C).under B') →+*
      Localization.AtPrime (v.asIdeal.under C) :=
    Localization.localRingHom _ (v.asIdeal.under C) (algebraMap B' C) rfl
  let f : Localization.AtPrime ((v.asIdeal.under C).under B') →+*
      Localization.AtPrime v.asIdeal :=
    (localizationAtPrimeUnderAlgEquiv B C q v).toAlgHom.toRingHom.comp g
  refine ⟨f (P.parameter ((v.asIdeal.under C).under B')),
    fun i ↦ Units.map f.toMonoidHom (P.factorUnit ((v.asIdeal.under C).under B') i),
    P.exponent ((v.asIdeal.under C).under B'), fun i ↦ ?_⟩
  have key : f (algebraMap B' (Localization.AtPrime ((v.asIdeal.under C).under B'))
      (algebraMap A B' (a i))) =
      algebraMap (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
        (Localization.AtPrime v.asIdeal)
        (algebraMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
          (algebraMap A (Localization.AtPrime q.asIdeal) (a i))) := by
    rw [algebraMap_semilocalization_algebraMap q (a i),
      ← IsScalarTower.algebraMap_apply C
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))
        (Localization.AtPrime v.asIdeal)]
    simp only [f, g, RingHom.comp_apply, Localization.localRingHom_to_map]
    rw [← IsScalarTower.algebraMap_apply A B' C]
    exact (localizationAtPrimeUnderAlgEquiv B C q v).commutes _
  rw [← key, P.factorization ((v.asIdeal.under C).under B') i, map_mul, map_pow]
  rfl

end Fibre

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **The local rings of `B` are one-dimensional.** Their dimension is at most one because `B` is
integral over `A`; it is not zero because a nonzerodivisor of `A` in `𝔪`, which exists as `𝔪`
is not an associated prime of `A`, stays a nonzerodivisor of `B_𝔮` and is not a unit there. -/
theorem ringKrullDim_localizationAtPrime_eq_one (hdim : ringKrullDim A = 1)
    {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B) (q : MaximalSpectrum B) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 1 := by
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral A B
  have := krullDimLE_one_localizationAtPrime q.asIdeal
  have := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
  obtain ⟨t, htm, ht⟩ :=
    exists_mem_maximalIdeal_mem_nonZeroDivisors (not_isAssociatedPrime_self hinj hass)
  have h1 : ringKrullDim (Localization.AtPrime q.asIdeal) ≤ 1 :=
    Ring.krullDimLE_iff.mp inferInstance
  have h0 : ¬ ringKrullDim (Localization.AtPrime q.asIdeal) ≤ 0 := by
    intro h
    have : Ring.KrullDimLE 0 (Localization.AtPrime q.asIdeal) :=
      Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
      IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    have hu := IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (toExtensionNonZeroDivisor hass q ⟨t, ht⟩).2
    exact (mem_maximalIdeal t).mp htm (isUnit_of_map_unit (algebraMap A _) t hu)
  induction h : ringKrullDim (Localization.AtPrime q.asIdeal) using WithBot.recBotCoe with
  | bot => rw [h] at h0; exact absurd bot_le h0
  | coe n =>
    rw [h] at h0 h1
    have h1' : n ≤ 1 := by exact_mod_cast h1
    have h0' : n ≠ 0 := fun hn ↦ h0 (by rw [hn]; rfl)
    rw [le_antisymm h1' (Order.one_le_iff_ne_zero.mpr h0')]
    rfl

/-- A nonzerodivisor of `A` is a nonzerodivisor of each local ring of `B`. -/
theorem isRegular_algebraMap_localizationAtPrime (hdim : ringKrullDim A = 1)
    {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B) (q : MaximalSpectrum B) {a : A}
    (ha : IsRegular a) : IsRegular (algebraMap A (Localization.AtPrime q.asIdeal) a) :=
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  isRegular_iff_mem_nonZeroDivisors.mpr
    (toExtensionNonZeroDivisor hass q ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩).2

/-- **Stacks 0EAT.** Let `(A, 𝔪)` be a Noetherian local ring of dimension one, let `A ⊆ B` be a
finite ring extension with `B / A` annihilated by a power of `𝔪` and `𝔪` not an associated prime
of `B`. For nonzerodivisors `a, b ∈ A`,

`∂_A(a, b) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}(∂_{B_j}(a, b))`,

the product over the maximal ideals `𝔪_j` of `B`, `B_j = B_{𝔪_j}`, where `∂` is the tame symbol of
Stacks 0EAQ (`Stacks.Chow.tameSymbolFormula`) — on `A`, and on each `B_j`, which is again a
one-dimensional Noetherian local ring in which `a` and `b` are nonzerodivisors. -/
@[stacks 0EAT "the displayed equation for the tame symbol of Stacks 0EAQ on A and on each local \
ring B_j"]
theorem tameSymbolFormula_eq_finprod_norm (hdim : ringKrullDim A = 1)
    {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B) {a b : A} (ha : IsRegular a)
    (hb : IsRegular b) :
    tameSymbolFormula hdim a b ha hb =
      ∏ᶠ q : MaximalSpectrum B,
        haveI := Stacks.Length.isLocalHom_algebraMap_localization (A := A) q
        haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (tameSymbolFormula (ringKrullDim_localizationAtPrime_eq_one hdim hinj hass q)
            (algebraMap A (Localization.AtPrime q.asIdeal) a)
            (algebraMap A (Localization.AtPrime q.asIdeal) b)
            (isRegular_algebraMap_localizationAtPrime hdim hass q ha)
            (isRegular_algebraMap_localizationAtPrime hdim hass q hb)) := by
  classical
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral A B
  have hBq' : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
    fun q ↦ krullDimLE_one_localizationAtPrime q.asIdeal
  have hlocB : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
    fun q ↦ Stacks.Length.isLocalHom_algebraMap_localization q
  let : Fintype (MaximalSpectrum B) :=
    @Fintype.ofFinite _ (Stacks.Length.finite_maximalSpectrum (A := A) (B := B))
  rw [finprod_eq_prod_of_fintype]
  by_cases hu : IsUnit a ∧ IsUnit b
  · rw [tameSymbolFormula_eq_one hdim ha hb hu.1 hu.2]
    refine (Finset.prod_eq_one fun q _ ↦ ?_).symm
    rw [tameSymbolFormula_eq_one _ _ _ (hu.1.map _) (hu.2.map _), map_one]
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ¬ IsUnit ((![a, b] : Fin 2 → A) k) := by
    by_cases h : IsUnit a
    · exact ⟨1, fun h' ↦ hu ⟨h, h'⟩⟩
    · exact ⟨0, h⟩
  obtain ⟨E, _, _, h⟩ := exists_prepared_extension_symbolValue hdim ha hb
  let := E.preparation.finite
  rw [h]
  have hB' := E.preparation.not_isAssociatedPrime_maximalIdeal fun h ↦ hk (h k)
  obtain ⟨n, hn⟩ := hquot
  obtain ⟨n', hn'⟩ := E.preparation.quotient_annihilated_by_maximalIdeal_power
  have hD := not_isAssociatedPrime_commonRefinement (A := A) (B := B) (B' := E.extension)
  have hinjD := injective_algebraMap_commonRefinement hinj E.preparation.algebraMap_injective
    hass hn'
  obtain ⟨N, hN⟩ := exists_pow_smul_le_range_commonRefinement hn hn'
  have hinjBD := injective_algebraMap_left_commonRefinement E.preparation.algebraMap_injective
    hass hn'
  have hinjB'D := injective_algebraMap_right_commonRefinement hinj hB' hn
  let : Fintype (MaximalSpectrum (TorsionCommonRefinement A B E.extension)) :=
    @Fintype.ofFinite _ (Stacks.Length.finite_maximalSpectrum (A := A)
      (B := TorsionCommonRefinement A B E.extension))
  have : ∀ s : MaximalSpectrum (TorsionCommonRefinement A B E.extension),
      IsLocalHom (algebraMap A (Localization.AtPrime s.asIdeal)) :=
    fun s ↦ Stacks.Length.isLocalHom_algebraMap_localization s
  have : IsNoetherianRing (TorsionCommonRefinement A B E.extension) :=
    IsNoetherianRing.of_finite A (TorsionCommonRefinement A B E.extension)
  have : Ring.KrullDimLE 1 (TorsionCommonRefinement A B E.extension) :=
    krullDimLE_one_of_isIntegral A (TorsionCommonRefinement A B E.extension)
  let symb : ∀ s : MaximalSpectrum (TorsionCommonRefinement A B E.extension),
      RegularTameSymbol (Localization.AtPrime s.asIdeal) := fun s ↦
    have := krullDimLE_one_localizationAtPrime s.asIdeal
    regularTameSymbolOfKrullDimLEOne _
  let x : nonZeroDivisors A := ⟨a, isRegular_iff_mem_nonZeroDivisors.mp ha⟩
  let y : nonZeroDivisors A := ⟨b, isRegular_iff_mem_nonZeroDivisors.mp hb⟩
  rw [← E.preparation.normPushforward_eq_symbolValue hB' hD symb hinjB'D hinjD ⟨N, hN⟩ 0 1 x y
    rfl rfl]
  let hfin : ∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        (TorsionCommonRefinement A B E.extension) q.asIdeal.primeCompl))) :=
    fun q ↦ @Fintype.ofFinite _ (finite_maximalSpectrum_semilocalization B _ q)
  let hAlg : ∀ (q : MaximalSpectrum B)
      (s : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        (TorsionCommonRefinement A B E.extension) q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime (s.asIdeal.under (TorsionCommonRefinement A B E.extension))) :=
    fun q s ↦ Localization.AtPrime.algebraOfLiesOver q.asIdeal
      (s.asIdeal.under (TorsionCommonRefinement A B E.extension))
  have hLies : ∀ (q : MaximalSpectrum B)
      (s : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        (TorsionCommonRefinement A B E.extension) q.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q.asIdeal
        (s.asIdeal.under (TorsionCommonRefinement A B E.extension)) :=
    fun _ _ ↦ ⟨rfl⟩
  obtain ⟨t, htm, ht⟩ :=
    exists_mem_maximalIdeal_mem_nonZeroDivisors (not_isAssociatedPrime_self hinj hass)
  have hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid (TorsionCommonRefinement A B E.extension)
          q.asIdeal.primeCompl)) :=
    fun q ↦ not_isAssociatedPrime_semilocalization q hD htm ht
  rw [normPushforward_apply_eq_prod_norm_normPushforward hass hD hfibre symb hinjD ⟨N, hN⟩
    (fun q ↦ injective_algebraMap_semilocalization hinjBD q)
    (fun q ↦ exists_pow_smul_le_range_semilocalization q hN) x y]
  refine Finset.prod_congr rfl fun q _ ↦ congrArg _ ?_
  refine normPushforward_eq_tameSymbolFormula
    (ringKrullDim_localizationAtPrime_eq_one hdim hinj hass q) (hfibre q) _ _ _
    (toExtensionNonZeroDivisor hass q x) (toExtensionNonZeroDivisor hass q y) fun v ↦ ?_
  obtain ⟨π, u, e, h⟩ :=
    exists_factorization_semilocalization (C := TorsionCommonRefinement A B E.extension)
      E.preparation q v
  refine ⟨π, u, e, fun i ↦ ?_⟩
  fin_cases i
  exacts [h 0, h 1]

end Main

end Stacks.Chow

end
