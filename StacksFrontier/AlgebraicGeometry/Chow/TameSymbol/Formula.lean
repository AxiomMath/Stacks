module

public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Existence
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.TorsionCommonRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.PairSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The formula defining the tame symbol

Let `(A, 𝔪)` be a Noetherian local ring of dimension one and let `a₁, a₂ ∈ A` be
nonzerodivisors. Choose a finite ring extension `A ⊆ B` with `B / A` annihilated by a power of
`𝔪`, a nonzerodivisor `π_j` of each local ring `B_j = B_{𝔪_j}` and factorizations
`a_i = u_{i, j} π_j ^ {e_{i, j}}` in `B_j` with `u_{i, j}` units, as Stacks 0EAG provides — an
`AlgebraicGeometry.TameSymbolPreparation`. Stacks 0EAQ defines

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j) ^ {m_j}`,  `m_j = length_{B_j}(B_j / π_j B_j)`.

`Stacks.Chow.tameSymbolFormula` is this definition, evaluated on one chosen preparation, and
`Stacks.Chow.tameSymbolFormula_eq` says that the displayed product computed from *any* extension
`B` and *any* local factorizations is that value.

The latter is the content of Stacks 0EAR, proved here as the source proves it. Two extensions
`B` and `B'` are compared through `C = (B ⊗_A B') / (𝔪`-power torsion`)`, which is an extension of
the same kind containing both (`Stacks.Chow.TorsionCommonRefinement`). For any family of tame
symbols on the local rings of `C`, the norm pushforward of that family to `A` equals the norm
pushforward to `A`, through the maximal ideals of `B`, of the norm pushforwards to the `B_j` —
this is transitivity of norms, Stacks 0BIJ, in the form
`Stacks.Chow.normPushforward_apply_eq_prod_norm_normPushforward`. On the other hand any tame
symbol on `B_j` takes the value of the formula's factor on the factorizations at `𝔪_j`. So the
formula for `B` equals the pushforward from `C`; by symmetry so does the formula for `B'`. Tame
symbols on the local rings of `C` exist by Stacks 0EAH. When both elements are units every factor
is `1`, whatever the extension.

## Main definitions

* `Stacks.Chow.regularTameSymbolOfKrullDimLEOne` — a tame symbol on nonzerodivisors of a
  Noetherian local ring of dimension at most one.
* `AlgebraicGeometry.TameSymbolPreparation.ofIsUnit` — the preparation of a family of units on
  `A` itself.
* `Stacks.Chow.tameSymbolFormula` — the tame symbol `∂_A(a₁, a₂)` of Stacks 0EAQ.

## Main results

* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_symbolValue` — the right-hand side of
  Stacks 0EAQ does not depend on the extension nor on the local factorizations.
* `Stacks.Chow.tameSymbolFormula_eq` — Stacks 0EAQ.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

universe u v w

namespace Stacks.Chow

/-- An integral extension of a ring of Krull dimension at most one has Krull dimension at most
one: contraction of primes along an integral ring map is strictly monotone. -/
@[ega "0 16.1.5" "special case"]
theorem krullDimLE_one_of_isIntegral (R : Type*) (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [Ring.KrullDimLE 1 R] : Ring.KrullDimLE 1 S :=
  Ring.krullDimLE_iff.mpr ((Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S)) fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h).trans
      (Ring.krullDimLE_iff.mp ‹_›))

/-- The constant symbol `1` is a tame symbol on a local ring in which every nonzerodivisor is a
unit: every length `length_R(R / bR)` occurring in Stacks 0EAM and 0EAN is then zero. -/
noncomputable def RegularTameSymbol.ofForallIsUnit {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ∀ x ∈ nonZeroDivisors R, IsUnit x) : RegularTameSymbol R where
  toFun _ _ := 1
  map_mul_left _ _ _ := (mul_one 1).symm
  map_mul_right _ _ _ := (mul_one 1).symm
  self b := by simp [Ring.ord_of_isUnit (h _ b.2)]
  unit_left _ b _ _ := by simp [Ring.ord_of_isUnit (h _ b.2)]
  steinberg _ _ _ _ := rfl

/-- **A tame symbol on a Noetherian local ring of dimension at most one.** In dimension one this
is the symbol of Stacks 0EAH; in dimension zero the ring is Artinian, every nonzerodivisor is a
unit, and the constant symbol `1` is one. -/
noncomputable def regularTameSymbolOfKrullDimLEOne (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Ring.KrullDimLE 1 R] : RegularTameSymbol R := by
  classical
  exact if hdim : ringKrullDim R = 1 then regularTameSymbolOfKrullDimOne hdim else
    RegularTameSymbol.ofForallIsUnit fun x hx ↦ by
      have hlt : ringKrullDim R < 1 :=
        lt_of_le_of_ne (Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 R›) hdim
      have hle : ringKrullDim R ≤ 0 := by
        induction h : ringKrullDim R using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe n =>
          rw [h] at hlt
          have hn : n < 1 := WithBot.coe_lt_coe.mp hlt
          rw [ENat.lt_one_iff_eq_zero.mp hn]
          rfl
      have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast hle)
      have : IsArtinianRing R := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors hx

end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

section Basic

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B)

/-- **The preparation of a family of units on `A` itself**: the parameter is `1`, the exponents
are `0` and the unit parts are the members of the family. -/
noncomputable def ofIsUnit (a : Fin r → A) (ha : ∀ i, IsUnit (a i)) :
    TameSymbolPreparation a A where
  finite := Module.Finite.self A
  algebraMap_injective := fun _ _ h ↦ h
  quotient_annihilated_by_maximalIdeal_power := ⟨0, fun z _ ↦ ⟨z, rfl⟩⟩
  parameter _ _ := 1
  parameter_isRegular _ _ := isRegular_one
  factorUnit q _ i := ((ha i).map (algebraMap A (Localization.AtPrime q))).unit
  exponent _ _ _ := 0
  factorization q _ i := by simp

/-- The right-hand side of the formula Stacks 0EAQ for a preparation, with the finiteness of the
maximal spectrum and the locality of `A → B_𝔮` supplied by the preparation itself. -/
noncomputable def value (i j : Fin r) : (ResidueField A)ˣ :=
  haveI := P.finite_maximalSpectrum
  letI := Fintype.ofFinite (MaximalSpectrum B)
  haveI := fun q ↦ P.isLocalHom q
  P.symbolValue i j

variable [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

/-- `TameSymbolPreparation.value` computed with any instances. -/
theorem value_eq_symbolValue (i j : Fin r) : P.value i j = P.symbolValue i j := by
  unfold value
  congr 1
  exact Subsingleton.elim _ _

/-- **The formula Stacks 0EAQ on two units is `1`**: at each maximal ideal either the parameter is
a unit, and the exponent `length(B_j / π_j B_j)` vanishes, or both exponents `e_{i, j}` vanish. -/
theorem symbolValue_eq_one (i j : Fin r) (hi : IsUnit (a i)) (hj : IsUnit (a j)) :
    P.symbolValue i j = 1 := by
  refine Finset.prod_eq_one fun q _ ↦ ?_
  have h1 : factorizationValue (P.parameter q.asIdeal) (P.factorUnit q.asIdeal i)
      (P.factorUnit q.asIdeal j) (P.exponent q.asIdeal i) (P.exponent q.asIdeal j) = 1 := by
    by_cases hp : IsUnit (P.parameter q.asIdeal)
    · simp [factorizationValue, Ring.ord_of_isUnit hp]
    · have hexp : ∀ k, IsUnit (a k) → P.exponent q.asIdeal k = 0 := fun k hk ↦ by
        have h := (hk.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q.asIdeal))
        rw [P.factorization q.asIdeal k] at h
        by_contra hn
        exact hp ((isUnit_pow_iff hn).mp (isUnit_of_mul_isUnit_right h))
      simp [factorizationValue, hexp i hi, hexp j hj]
  rw [h1, map_one]

end Basic

section Tower

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] {r : ℕ} {a : Fin r → A}

/-- **The formula Stacks 0EAQ for `B` is the norm pushforward from any refinement.** Let
`B ⊆ C` be a finite extension with `C / A` annihilated by a power of `𝔪` and `𝔪` not an
associated prime of `C`. For every family of tame symbols on the local rings of `C`, its norm
pushforward to `A`, evaluated on two members of a family prepared over `B`, is the value of the
formula Stacks 0EAQ for that preparation. By transitivity of norms the pushforward from `C`
factors through the norm pushforwards to the local rings `B_j`, and a tame symbol on `B_j` takes
on the factorizations at `𝔪_j` the value of the factor of the formula there. -/
theorem normPushforward_eq_symbolValue (P : TameSymbolPreparation a B)
    {C : Type w} [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite B C] [Module.Finite A C]
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [Fintype (MaximalSpectrum C)]
    [∀ s : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime s.asIdeal))]
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B) (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (symb : ∀ s : MaximalSpectrum C, RegularTameSymbol (Localization.AtPrime s.asIdeal))
    (hinjBC : Function.Injective (algebraMap B C)) (hinjC : Function.Injective (algebraMap A C))
    (hquotC : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C))
    (i j : Fin r) (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normPushforward hC symb hinjC hquotC x y = P.symbolValue i j := by
  let := P.finite
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral A B
  have hBq : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    fun q ↦ IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have hBq' : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
    fun q ↦ krullDimLE_one_localizationAtPrime q.asIdeal
  let hfin : ∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C
        q.asIdeal.primeCompl))) :=
    fun q ↦ @Fintype.ofFinite _ (finite_maximalSpectrum_semilocalization B C q)
  let hAlg : ∀ (q : MaximalSpectrum B)
      (s : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (s.asIdeal.under C)) :=
    fun q s ↦ Localization.AtPrime.algebraOfLiesOver q.asIdeal (s.asIdeal.under C)
  obtain ⟨N, hN⟩ := hquotC
  obtain ⟨t, htm, ht⟩ :=
    exists_mem_maximalIdeal_mem_nonZeroDivisors
      (not_isAssociatedPrime_self P.algebraMap_injective hB)
  have hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)) :=
    fun q ↦ not_isAssociatedPrime_semilocalization q hC htm ht
  rw [normPushforward_apply_eq_prod_norm_normPushforward hB hC hfibre symb hinjC ⟨N, hN⟩
    (fun q ↦ injective_algebraMap_semilocalization hinjBC q)
    (fun q ↦ exists_pow_smul_le_range_semilocalization q hN) x y]
  rw [← normPushforward_apply_eq_symbolValue hB
    (fun q ↦ normPushforward (hfibre q) (fibreSymbol symb q)
      (injective_algebraMap_semilocalization hinjBC q)
      (exists_pow_smul_le_range_semilocalization q hN))
    P.algebraMap_injective P.quotient_annihilated_by_maximalIdeal_power P i j x y hx hy,
    normPushforward_apply]

end Tower

section Independence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] {B' : Type w} [CommRing B'] [Algebra A B']
  {r : ℕ} {a : Fin r → A}

/-- **The formula Stacks 0EAQ does not depend on the choices made (Stacks 0EAR).** Two
preparations of the same family, over two finite extensions `A ⊆ B` and `A ⊆ B'` and with any
local parameters, unit parts and exponents, give the same value of the formula.

Following the source, both are compared with the common refinement
`C = (B ⊗_A B') / (𝔪`-power torsion`)`: for a family of tame symbols on the local rings of `C`
(which exist by Stacks 0EAH), each of the two values is the norm pushforward of that family to
`A`. If both members are units, both values are `1`. -/
theorem symbolValue_eq_symbolValue (P : TameSymbolPreparation a B)
    (P' : TameSymbolPreparation a B')
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [Fintype (MaximalSpectrum B')]
    [∀ q : MaximalSpectrum B', IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (i j : Fin r) : P.symbolValue i j = P'.symbolValue i j := by
  classical
  by_cases hu : IsUnit (a i) ∧ IsUnit (a j)
  · rw [P.symbolValue_eq_one i j hu.1 hu.2, P'.symbolValue_eq_one i j hu.1 hu.2]
  obtain ⟨k, hk⟩ : ∃ k, ¬ IsUnit (a k) := by
    by_cases h : IsUnit (a i)
    · exact ⟨j, fun h' ↦ hu ⟨h, h'⟩⟩
    · exact ⟨i, h⟩
  have hB := P.not_isAssociatedPrime_maximalIdeal fun h ↦ hk (h k)
  have hB' := P'.not_isAssociatedPrime_maximalIdeal fun h ↦ hk (h k)
  let := P.finite
  let := P'.finite
  obtain ⟨n, hn⟩ := P.quotient_annihilated_by_maximalIdeal_power
  obtain ⟨n', hn'⟩ := P'.quotient_annihilated_by_maximalIdeal_power
  have hC := not_isAssociatedPrime_commonRefinement (A := A) (B := B) (B' := B')
  have hinjC := injective_algebraMap_commonRefinement P.algebraMap_injective
    P'.algebraMap_injective hB hn'
  have hquotC := exists_pow_smul_le_range_commonRefinement hn hn'
  let : Fintype (MaximalSpectrum (TorsionCommonRefinement A B B')) :=
    @Fintype.ofFinite _ (Stacks.Length.finite_maximalSpectrum (A := A)
      (B := TorsionCommonRefinement A B B'))
  have : ∀ s : MaximalSpectrum (TorsionCommonRefinement A B B'),
      IsLocalHom (algebraMap A (Localization.AtPrime s.asIdeal)) :=
    fun s ↦ Stacks.Length.isLocalHom_algebraMap_localization s
  have : IsNoetherianRing (TorsionCommonRefinement A B B') :=
    IsNoetherianRing.of_finite A (TorsionCommonRefinement A B B')
  have : Ring.KrullDimLE 1 (TorsionCommonRefinement A B B') :=
    krullDimLE_one_of_isIntegral A (TorsionCommonRefinement A B B')
  let symb : ∀ s : MaximalSpectrum (TorsionCommonRefinement A B B'),
      RegularTameSymbol (Localization.AtPrime s.asIdeal) := fun s ↦
    have : IsNoetherianRing (Localization.AtPrime s.asIdeal) :=
      IsLocalization.isNoetherianRing s.asIdeal.primeCompl _ inferInstance
    have := krullDimLE_one_localizationAtPrime s.asIdeal
    regularTameSymbolOfKrullDimLEOne _
  let x : nonZeroDivisors A := ⟨a i, P.mem_nonZeroDivisors i⟩
  let y : nonZeroDivisors A := ⟨a j, P.mem_nonZeroDivisors j⟩
  rw [← P.normPushforward_eq_symbolValue hB hC symb
      (injective_algebraMap_left_commonRefinement P'.algebraMap_injective hB hn') hinjC hquotC
      i j x y rfl rfl,
    ← P'.normPushforward_eq_symbolValue hB' hC symb
      (injective_algebraMap_right_commonRefinement P.algebraMap_injective hB' hn) hinjC hquotC
      i j x y rfl rfl]

end Independence

end AlgebraicGeometry.TameSymbolPreparation

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Two nonzerodivisors of a one-dimensional Noetherian local ring admit a finite extension with
local factorizations as in Stacks 0EAG: by Stacks 0EAG itself unless both are units, and on `A`
itself with parameter `1` if both are. -/
theorem nonempty_preparedTameSymbolExtension (hdim : ringKrullDim A = 1) {a₁ a₂ : A}
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) :
    Nonempty (PreparedTameSymbolExtension ![a₁, a₂]) := by
  by_cases hu : ∀ i, IsUnit ((![a₁, a₂] : Fin 2 → A) i)
  · exact ⟨{ extension := CommAlgCat.of A A
             preparation := TameSymbolPreparation.ofIsUnit ![a₁, a₂] hu }⟩
  · obtain ⟨B, _, _, ⟨P⟩⟩ := exists_tameSymbolPreparation_of_ringKrullDim_eq_one
      (le_refl 2) ![a₁, a₂] (fun i ↦ by fin_cases i <;> simpa) hu hdim
    exact ⟨{ extension := CommAlgCat.of A B, preparation := P }⟩

/-- **The tame symbol `∂_A(a₁, a₂)` of Stacks 0EAQ.** For nonzerodivisors `a₁`, `a₂` of a
one-dimensional Noetherian local ring `A`, choose a finite extension `A ⊆ B` with local
factorizations `a_i = u_{i, j} π_j ^ {e_{i, j}}` at the maximal ideals `𝔪_j` of `B`, as in
Stacks 0EAG, and take

```
∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}} mod 𝔪_j)^{m_j}
```

with `m_j = length_{B_j}(B_j / π_j B_j)`. By `Stacks.Chow.tameSymbolFormula_eq` the choice does not
matter. -/
noncomputable def tameSymbolFormula (hdim : ringKrullDim A = 1) (a₁ a₂ : A)
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) : (ResidueField A)ˣ :=
  (nonempty_preparedTameSymbolExtension hdim ha₁ ha₂).some.preparation.value 0 1

/-- **Stacks 0EAQ.** Let `(A, 𝔪)` be a Noetherian local ring of dimension one and `a₁, a₂ ∈ A`
nonzerodivisors. For every finite ring extension `A ⊆ B` with `B / A` annihilated by a power of
`𝔪`, every choice of nonzerodivisors `π_j ∈ B_j = B_{𝔪_j}` at the maximal ideals `𝔪_j` of `B`,
and every choice of factorizations `a_i = u_{i, j} π_j ^ {e_{i, j}}` in `B_j` with `u_{i, j}`
units and `e_{i, j} ≥ 0` — the data of Stacks 0EAG, bundled as `P` — the tame symbol is

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j) ^ {m_j}`,  `m_j = length_{B_j}(B_j / π_j B_j)`,

the product over the maximal ideals of `B`. The definition `Stacks.Chow.tameSymbolFormula` uses
one such choice; that every other choice gives the same element is Stacks 0EAR,
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_symbolValue`. -/
@[stacks 0EAQ "the tame symbol defined by the formula from one admissible extension, and equal \
to the displayed product for every admissible extension A ⊆ B and every choice of local \
factorizations"]
theorem tameSymbolFormula_eq (hdim : ringKrullDim A = 1) {a₁ a₂ : A}
    (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) {B : Type v} [CommRing B] [Algebra A B]
    (P : TameSymbolPreparation ![a₁, a₂] B) :
    tameSymbolFormula hdim a₁ a₂ ha₁ ha₂ =
      ∏ᶠ q : MaximalSpectrum B,
        haveI := P.isLocalHom q
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          ((-1) ^ (P.exponent q.asIdeal 0 * P.exponent q.asIdeal 1) *
            Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom
              (P.factorUnit q.asIdeal 0) ^ P.exponent q.asIdeal 1 *
            (Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom
              (P.factorUnit q.asIdeal 1))⁻¹ ^ P.exponent q.asIdeal 0) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⧸ Ideal.span {P.parameter q.asIdeal})).toNat := by
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  let := P.finite_maximalSpectrum
  let := Fintype.ofFinite (MaximalSpectrum B)
  have := fun q ↦ P.isLocalHom q
  rw [finprod_eq_prod_of_fintype]
  rw [tameSymbolFormula]
  generalize (nonempty_preparedTameSymbolExtension hdim ha₁ ha₂).some = E
  let := E.preparation.finite_maximalSpectrum
  let := Fintype.ofFinite (MaximalSpectrum E.extension)
  have := fun q ↦ E.preparation.isLocalHom q
  rw [TameSymbolPreparation.value_eq_symbolValue]
  refine ((TameSymbolPreparation.symbolValue_eq_symbolValue _ P 0 1).trans ?_)
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  rw [factorizationValue, map_pow]
  rfl

end Stacks.Chow

end
