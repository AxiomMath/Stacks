module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.DefiningFormula
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.ExtensionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne

/-!
# The formula of Stacks 0EAQ for an arbitrary one-dimensional Noetherian local ring

Stacks 0EAQ is the displayed equation defining the tame symbol of a one-dimensional Noetherian
local ring `(A, 𝔪)`: for nonzerodivisors `a₁, a₂ ∈ A`, choose a finite ring extension `A ⊆ B` as
in Stacks 0EAG — module finite, with `B / A` annihilated by a power of `𝔪` — with a local
parameter `π_𝔮` at each maximal ideal of `B` and factorizations `a_i = u_{i, 𝔮} π_𝔮^{e_{i, 𝔮}}`
in `B_𝔮`; then

`∂_A(a₁, a₂) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_{1,𝔮}e_{2,𝔮}} u_{1,𝔮}^{e_{2,𝔮}} u_{2,𝔮}^{-e_{1,𝔮}}
  mod 𝔮)^{m_𝔮}`,  `m_𝔮 = length_{B_𝔮}(B_𝔮 / π_𝔮 B_𝔮)`.

`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.DefiningFormula` proves this equation for a
one-dimensional Noetherian local **domain** whose integral closure in its fraction field is
module finite — the class for which that file's `∂_A` exists. This file removes that
qualification. Nothing is assumed of `A` beyond what Stacks 0EAH assumes of it: Noetherian,
local, of dimension at most one. In particular `A` is not assumed to be a domain and no normal
finite modification is assumed to exist.

Two observations make that possible.

* **The family of symbols upstairs is not a choice.** `Stacks.Chow.normPushforward` builds the
  tame symbol on `A` out of a family of tame symbols on the local rings `B_𝔮`, carried as a
  hypothesis. For an extension of the kind Stacks 0EAG produces that family is canonical: `𝔪` is
  not an associated prime of `B`, so `𝔪` is not an associated prime of `A`
  (`Stacks.Chow.not_isAssociatedPrime_self`) and therefore contains a nonzerodivisor
  (`Stacks.Chow.exists_mem_maximalIdeal_mem_nonZeroDivisors`), which stays a nonzerodivisor in
  each `B_𝔮` and lies in its maximal ideal. A Noetherian local ring of dimension at most one
  whose maximal ideal contains a nonzerodivisor has dimension exactly one, so each `B_𝔮` carries
  the canonical tame symbol `Stacks.Chow.regularTameSymbolOfKrullDimOne` of Stacks 0EAH. That is
  `Stacks.Chow.extensionSymbol`, and `Stacks.Chow.normPushforwardOfExtension` is the resulting
  `∂_A`, a term of `Stacks.Chow.RegularTameSymbol` depending on nothing but `A`, `B` and the two
  properties of the extension that the source asks for.

* **The right-hand side is independent of every choice.** That is Stacks 0EAR:
  `Stacks.Chow.preparationSymbolValue_eq_of_preparations` for the local factorizations and
  `Stacks.Chow.preparationSymbolValue_eq_of_extensions` for the extension itself. So the product
  of the source is a function of `A` and the two elements alone, and the equation below pins the
  tame symbol of every admissible extension to that one value.

## Main definitions

* `Stacks.Chow.extensionSymbol` — the canonical tame symbol of Stacks 0EAH on each local ring of
  an auxiliary extension of the kind Stacks 0EAG produces.
* `Stacks.Chow.normPushforwardOfExtension` — the tame symbol `∂_A` of Stacks 0EAH on
  nonzerodivisors of `A` that such an extension defines, with no instance and no symbol carried
  as a hypothesis.

## Main results

* `Stacks.Chow.ringKrullDim_eq_one_of_mem_maximalIdeal_mem_nonZeroDivisors` — a local ring of
  dimension at most one whose maximal ideal contains a nonzerodivisor has dimension one.
* `Stacks.Chow.ringKrullDim_localization_eq_one` — every local ring of an auxiliary extension is
  one-dimensional.
* `Stacks.Chow.normPushforwardOfExtension_apply_eq_preparationSymbolValue` — Stacks 0EAQ, with no
  qualification on `A`.
* `Stacks.Chow.normPushforwardOfExtension_apply_eq_of_extensions` — the value is the same for two
  auxiliary extensions, by Stacks 0EAR.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry Stacks.Localization

universe u v w

namespace Stacks.Chow

/-! ### A local ring whose maximal ideal contains a nonzerodivisor is one-dimensional -/

section Dimension

/-- An element of `WithBot ℕ∞` that is not at most `0` is at least `1`. -/
private theorem one_le_of_not_le_zero {d : WithBot ℕ∞} (h : ¬ d ≤ 0) : 1 ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h
  | coe m =>
    have hm : m ≠ 0 := by rintro rfl; exact h (by simp)
    simpa using Order.one_le_iff_ne_zero.mpr hm

/-- **A local ring of Krull dimension at most one whose maximal ideal contains a nonzerodivisor
has Krull dimension exactly one.** Were the dimension zero, the maximal ideal would consist of
nilpotents (`Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal`), and a nilpotent nonzerodivisor
forces `1 = 0`. -/
theorem ringKrullDim_eq_one_of_mem_maximalIdeal_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [IsLocalRing R] [Ring.KrullDimLE 1 R] {x : R} (hx : x ∈ maximalIdeal R)
    (hreg : x ∈ nonZeroDivisors R) : ringKrullDim R = 1 := by
  have hzero : ¬ Ring.KrullDimLE 0 R := by
    intro _
    obtain ⟨k, hk⟩ := Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hx
    have h1 := pow_mem hreg k
    rw [mem_nonZeroDivisors_iff] at h1
    exact one_ne_zero (h1.2 1 (by rw [one_mul, hk]))
  exact le_antisymm (Ring.krullDimLE_iff.mp inferInstance)
    (one_le_of_not_le_zero fun h => hzero (Ring.krullDimLE_iff.mpr h))

end Dimension

/-! ### The canonical symbol on the local rings of an auxiliary extension -/

section Extension

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]

/-- **Every local ring of an auxiliary extension is one-dimensional.** Let `A ⊆ B` be module
finite with `𝔪` not an associated prime of `B` — an extension of the kind Stacks 0EAG produces.
Then `𝔪` is not an associated prime of `A` either, so it contains a nonzerodivisor `x`; the image
of `x` in `B_𝔮` is again a nonzerodivisor (`Stacks.Chow.toExtensionNonZeroDivisor`) and lies in
the maximal ideal because `A → B_𝔮` is local, and `B_𝔮` has dimension at most one because `B`
does. -/
theorem ringKrullDim_localization_eq_one (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B) (q : MaximalSpectrum B) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 1 := by
  obtain ⟨x, hxm, hx⟩ :=
    exists_mem_maximalIdeal_mem_nonZeroDivisors (not_isAssociatedPrime_self hinj hB)
  have : Ring.KrullDimLE 1 B := Stacks.Chow.krullDimLE_one_of_moduleFinite (A := A)
  have : Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
    krullDimLE_one_localizationAtPrime q.asIdeal
  have : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
    Stacks.Length.isLocalHom_algebraMap_localization q
  refine ringKrullDim_eq_one_of_mem_maximalIdeal_mem_nonZeroDivisors
    (x := algebraMap A (Localization.AtPrime q.asIdeal) x) ?_
    (toExtensionNonZeroDivisor hB q ⟨x, hx⟩).2
  exact (mem_maximalIdeal _).mpr fun hu =>
    (mem_maximalIdeal x).mp hxm (IsLocalHom.map_nonunit _ hu)

/-- **The canonical tame symbol of Stacks 0EAH on a local ring of an auxiliary extension.** Each
`B_𝔮` is a one-dimensional Noetherian local ring by
`Stacks.Chow.ringKrullDim_localization_eq_one`, so it carries the tame symbol
`Stacks.Chow.regularTameSymbolOfKrullDimOne` — the periodic-determinant symbol of Stacks 02PZ.
No family of symbols upstairs has to be chosen. -/
noncomputable def extensionSymbol (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B) (q : MaximalSpectrum B) :
    RegularTameSymbol (Localization.AtPrime q.asIdeal) :=
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  haveI : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  regularTameSymbolOfKrullDimOne (ringKrullDim_localization_eq_one hinj hB q)

/-- **The tame symbol of Stacks 0EAH that an auxiliary extension defines**, for an arbitrary
one-dimensional Noetherian local ring `A`. The norm pushforward of Stacks 0EAT applied to the
canonical family `Stacks.Chow.extensionSymbol`: a term of `Stacks.Chow.RegularTameSymbol`, hence
Stacks 0EAH on nonzerodivisors of `A`, whose only inputs are the two properties of `A ⊆ B` that
the source asks for. -/
noncomputable def normPushforwardOfExtension (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    RegularTameSymbol A :=
  normPushforwardOfModuleFinite hB (extensionSymbol hinj hB) hinj hquot

/-- **Stacks 0EAQ, with nothing assumed beyond the hypotheses of Stacks 0EAH on `A`.** Let
`(A, 𝔪)` be a Noetherian local ring of dimension at most one, let `A ⊆ B` be module finite with
`B / A` annihilated by a power of `𝔪` and `𝔪` not an associated prime of `B` — an extension of
the kind Stacks 0EAG produces — and let `P` be a tame-symbol preparation of a family `a` over
`B`. Then for two members `a i`, `a j` of the family,

`∂_A(a i, a j) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}`,
`m_𝔮 = length_{B_𝔮}(B_𝔮 / π_𝔮 B_𝔮)`,

which is the displayed equation of the source.

`∂_A` on the left is `Stacks.Chow.normPushforwardOfExtension`, a term of
`Stacks.Chow.RegularTameSymbol` — Stacks 0EAH on nonzerodivisors of `A` — and not a symbol
carried as a hypothesis: the family of symbols on the local rings of `B` is the canonical one
there (`Stacks.Chow.extensionSymbol`), and the finiteness of the maximal spectrum and the
locality of `A → B_𝔮` are supplied in the statement rather than assumed. `A` is not assumed to be
a domain, and no normal finite modification of it is assumed to exist, which is what
distinguishes this from
`Stacks.Chow.tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue`.

The right-hand side is a function of `A` and the pair alone: it does not depend on `P` by
`Stacks.Chow.preparationSymbolValue_eq_of_preparations` nor on `B` by
`Stacks.Chow.preparationSymbolValue_eq_of_extensions`, the two halves of Stacks 0EAR. -/
theorem normPushforwardOfExtension_apply_eq_preparationSymbolValue
    (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    letI := Stacks.Length.finite_maximalSpectrum (A := A) (B := B)
    letI := Fintype.ofFinite (MaximalSpectrum B)
    letI : ∀ q : MaximalSpectrum B,
        IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := fun q =>
      Stacks.Length.isLocalHom_algebraMap_localization q
    normPushforwardOfExtension hinj hB hquot x y = preparationSymbolValue P i j := by
  let := Stacks.Length.finite_maximalSpectrum (A := A) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) (B := B)
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := Stacks.Chow.krullDimLE_one_of_moduleFinite (A := A)
  have : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q =>
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := fun q =>
    krullDimLE_one_localizationAtPrime q.asIdeal
  rw [normPushforwardOfExtension, normPushforwardOfModuleFinite_apply]
  exact normPushforward_apply_eq_symbolValue hB _ hinj hquot P i j x y hx hy

/-- **Stacks 0EAS for an arbitrary one-dimensional Noetherian local ring.** Both halves. The
first: the product formula of Stacks 0EAQ, read over an auxiliary extension `A ⊆ B` of the kind
Stacks 0EAG produces, satisfies the four identities 0EAL, 0EAM, 0EAN and 0EAP on nonzerodivisors
of `A` — that is what being a term of `Stacks.Chow.RegularTameSymbol` asserts, and
`Stacks.Chow.normPushforwardOfExtension` is such a term. The second: it therefore yields

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

satisfying 0EAI, 0EAJ and 0EAK, which is `Stacks.Chow.RegularTameSymbol.extend`.

`Stacks.Chow.normPushforwardOfIsIntegrallyClosed` is the first half for a local *domain* with a
normal finite modification. Here `A` is an arbitrary Noetherian local ring of dimension at most
one: no domain hypothesis and no normal finite modification. One auxiliary extension still serves
every pair of nonzerodivisors, as it does there — the source instead chooses an extension
depending on the pair, and gluing those choices into a single symbol is not assembled. -/
noncomputable def tameSymbolOfExtension (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q] :
    TameSymbol A Q :=
  (normPushforwardOfExtension hinj hB hquot).extend Q

/-- **Stacks 0EAQ on `Q(A)^*`, with no qualification on `A`.** The tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

of Stacks 0EAH that an auxiliary extension defines takes, on a pair of nonzerodivisors of `A`,
the value of the displayed product of the source. The extension of a symbol on nonzerodivisors to
`Q(A)^*` restricts back to it (`Stacks.Chow.RegularTameSymbol.extend_regularFractionUnit`), so
this is `Stacks.Chow.normPushforwardOfExtension_apply_eq_preparationSymbolValue` transported
along `Stacks.Chow.regularFractionUnit`. -/
theorem tameSymbolOfExtension_apply_eq_preparationSymbolValue
    (hinj : Function.Injective (algebraMap A B))
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    {n : ℕ} {a : Fin n → A} (P : TameSymbolPreparation a B) (i j : Fin n)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    letI := Stacks.Length.finite_maximalSpectrum (A := A) (B := B)
    letI := Fintype.ofFinite (MaximalSpectrum B)
    letI : ∀ q : MaximalSpectrum B,
        IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := fun q =>
      Stacks.Length.isLocalHom_algebraMap_localization q
    tameSymbolOfExtension hinj hB hquot Q (regularFractionUnit x) (regularFractionUnit y) =
      preparationSymbolValue P i j := by
  rw [tameSymbolOfExtension, RegularTameSymbol.extend_regularFractionUnit]
  exact normPushforwardOfExtension_apply_eq_preparationSymbolValue hinj hB hquot P i j x y hx hy

end Extension

/-! ### The value does not depend on the auxiliary extension -/

section TwoExtensions

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] {B' : Type w} [CommRing B'] [Algebra A B']

/-- **The tame symbols of two auxiliary extensions agree on a prepared pair.** Each is the value
of the product of Stacks 0EAQ computed over its own extension, and by Stacks 0EAR
(`Stacks.Chow.preparationSymbolValue_eq_of_extensions`) the two products agree. So the equation
of Stacks 0EAQ determines one element of `κ(𝔪)^*`, as the source asserts. -/
theorem normPushforwardOfExtension_apply_eq_of_extensions
    {n : ℕ} {a : Fin n → A}
    (P : TameSymbolPreparation a B) (P' : TameSymbolPreparation a B')
    (hB : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (hB' : ¬ IsAssociatedPrime (maximalIdeal A) B')
    (hquot : ∃ m : ℕ, maximalIdeal A ^ m • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hquot' : ∃ m : ℕ, maximalIdeal A ^ m • (⊤ : Submodule A B') ≤
      LinearMap.range (Algebra.linearMap A B'))
    (i j : Fin n) (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    letI := P.finite
    letI := P'.finite
    normPushforwardOfExtension P.algebraMap_injective hB hquot x y =
      normPushforwardOfExtension P'.algebraMap_injective hB' hquot' x y := by
  let := P.finite
  let := P'.finite
  let := Stacks.Length.finite_maximalSpectrum (A := A) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Stacks.Length.finite_maximalSpectrum (A := A) (B := B')
  let := Fintype.ofFinite (MaximalSpectrum B')
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) (B := B)
  let := Stacks.Length.isLocalHom_algebraMap_localization (A := A) (B := B')
  exact (normPushforwardOfExtension_apply_eq_preparationSymbolValue P.algebraMap_injective hB
      hquot P i j x y hx hy).trans <|
    (preparationSymbolValue_eq_of_extensions P P' hB hB' i j).trans
      (normPushforwardOfExtension_apply_eq_preparationSymbolValue P'.algebraMap_injective hB'
        hquot' P' i j x y hx hy).symm

end TwoExtensions

end Stacks.Chow

end
