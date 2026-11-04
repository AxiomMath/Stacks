module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.NormalModification
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined

/-!
# The formula of Stacks 0EAQ, for the tame symbol itself

Stacks 0EAQ is the displayed equation defining the tame symbol of a one-dimensional Noetherian
local ring `(A, 𝔪)`: for nonzerodivisors `a₁`, `a₂ ∈ A`, choose a finite extension `A ⊆ B` as in
Stacks 0EAG, with a local parameter `π_j` at each maximal ideal `𝔪_j` of `B` and factorizations
`a_i = u_{i, j} π_j^{e_{i, j}}` in `B_j = B_{𝔪_j}` with `u_{i, j}` a unit; then

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j)^{m_j}`,  `m_j = length_{B_j}(B_j / π_j B_j)`.

The right-hand side is `AlgebraicGeometry.TameSymbolPreparation.symbolValue`, a function of a
`AlgebraicGeometry.TameSymbolPreparation` — which is exactly the output of Stacks 0EAG. What this
file supplies is the **left-hand side**: the equation is proved here for the tame symbol `∂_A`
itself, the one this development constructs, and not for a tame symbol carried as a hypothesis.

That distinction is the whole point. `Stacks.Chow.normPushforward_apply_eq_symbolValue` already
has the equation, but its left-hand side is `Stacks.Chow.normPushforward` applied to an arbitrary
family `symb` of tame symbols on the localizations `B_𝔮`, together with four hypotheses — that
`𝔪` is not an associated prime of `B`, and that each `B_𝔮` is Noetherian of dimension at most
one. For a *normal* finite modification all four are consequences of the finiteness of `A → B`:
`𝔪` is not an associated prime of a domain extension
(`Stacks.Chow.not_isAssociatedPrime_maximalIdeal`), `B` is Noetherian because it is finite over
`A`, each `B_𝔮` is a discrete valuation ring
(`Stacks.Chow.isDiscreteValuationRing_localization_isMaximal`) and so has dimension one, and the
family `symb` is then not a choice either — it is the canonical symbol
`Stacks.Chow.localizationSymbol` of a discrete valuation ring. Discharging all of them turns the
left-hand side into `Stacks.Chow.normPushforwardOfIsIntegrallyClosed`, which is this
development's `∂_A` for a local domain with a normal finite modification, and then into
`Stacks.Chow.normPushforwardOfFiniteIntegralClosure` and
`Stacks.Chow.tameSymbolOfFiniteIntegralClosure`, which depend on nothing but `A` and its fraction
field.

The last of those is `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`, the map Stacks 0EAH asks for, so
`Stacks.Chow.tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue` is Stacks 0EAQ at the
spelling of the source: the symbol on the left is the symbol of the source, and the product on
the right is the product of the source.

The hypothesis carried throughout is that `A` is a one-dimensional Noetherian local domain, not a
field, whose integral closure in its fraction field is module finite — equivalently, that `A` has
a normal finite modification; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Chow/TameSymbol/NormalModification.lean`. That hypothesis buys the
*universal* auxiliary extension: the integral closure serves every pair of nonzerodivisors at
once, so the symbol depends on `A` and its fraction field alone.

It is not needed for the equation itself.
`StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.DefiningFormulaGeneral` proves Stacks 0EAQ for an
arbitrary one-dimensional Noetherian local ring — no domain hypothesis and no normal finite
modification — with the auxiliary extension of Stacks 0EAG as the source's own datum, and with
the value of the product independent of that datum by Stacks 0EAR.

## Main definitions

* `Stacks.Chow.modificationPreparation`, `Stacks.Chow.integralClosurePreparation` — a normal
  finite modification, and in particular a module-finite integral closure, is a tame-symbol
  preparation of *every* family of nonzerodivisors of `A` at once.

## Main results

* `Stacks.Chow.normPushforwardOfModuleFinite_apply` — the product formula of Stacks 0EAT for the
  form of the symbol with no instance hypothesis left.
* `Stacks.Chow.normPushforwardOfIsIntegrallyClosed_apply_eq_symbolValue` — Stacks 0EAQ for the
  symbol of a normal finite modification.
* `Stacks.Chow.normPushforwardOfFiniteIntegralClosure_apply_eq_symbolValue` — Stacks 0EAQ for the
  symbol on nonzerodivisors of `A`, which depends only on `A` and its fraction field.
* `Stacks.Chow.tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue` — Stacks 0EAQ for
  `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`.
* `Stacks.Chow.tameSymbolOfFiniteIntegralClosure_eq_symbolValue` — the same with no instance
  hypothesis and no preparation supplied: every ingredient of the right-hand side is derived
  from the hypotheses on `A`.

## Implementation notes

`Stacks.Chow.normPushforwardOfModuleFinite` manufactures its own `Fintype (MaximalSpectrum B)`
from `Stacks.Length.finite_maximalSpectrum`, while a statement mentioning the product of Stacks
0EAQ must name some `Fintype` instance to be stated at all. The two are equal by
`Subsingleton.elim`, which is what `Stacks.Chow.normPushforwardOfModuleFinite_apply` is for; every
later statement here is free to take the instance as a binder, which makes it a statement about
every such instance. `Stacks.Chow.tameSymbolOfFiniteIntegralClosure_eq_symbolValue` instead
supplies the instance, from the finiteness of `A → B` alone, so that no `Fintype` and no locality
of `A → B_𝔮` is left standing as a hypothesis.

## References

* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Chow

section ModuleFinite

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
  [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

/-- **The product formula of Stacks 0EAT for the symbol with no instance hypothesis left.**
`Stacks.Chow.normPushforwardOfModuleFinite` builds a `Fintype (MaximalSpectrum B)` of its own out
of `Stacks.Length.finite_maximalSpectrum`; the product it takes is therefore over that instance,
and this is the same product read against an arbitrary one. Two `Fintype` structures on a type
are equal, and the locality hypotheses are propositions. -/
theorem normPushforwardOfModuleFinite_eq
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)) :
    normPushforwardOfModuleFinite hass symb hinj hquot =
      normPushforward hass symb hinj hquot := by
  unfold normPushforwardOfModuleFinite
  congr 1
  exact Subsingleton.elim _ _

/-- The product formula of Stacks 0EAT, read against an arbitrary `Fintype` instance on the
maximal spectrum. -/
theorem normPushforwardOfModuleFinite_apply
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (x y : nonZeroDivisors A) :
    normPushforwardOfModuleFinite hass symb hinj hquot x y =
      normPushforward hass symb hinj hquot x y :=
  congrFun (congrFun (congrArg RegularTameSymbol.toFun
    (normPushforwardOfModuleFinite_eq hass symb hinj hquot)) x) y

end ModuleFinite

section Modification

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  [IsDomain A] (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  [IsIntegrallyClosed B]

/-! #### A normal finite modification is itself a preparation

The formula of Stacks 0EAQ is evaluated on a tame-symbol preparation, whose existence is Stacks
0EAG. For a *normal* finite modification no appeal to Stacks 0EAG is needed: each `B_𝔮` is a
discrete valuation ring, so each member of any family of nonzerodivisors of `A` is already a unit
times a power of one uniformizer there. That is `Stacks.Chow.modificationPreparation`, which makes
the statements below non-vacuous for every family at once. -/

/-- **A uniformizer at a maximal ideal of a normal finite modification.** The localization is a
discrete valuation ring by `Stacks.Chow.isDiscreteValuationRing_localization_isMaximal`, and this
is a chosen irreducible element of it, as in `Stacks.Chow.localizationSymbol`. -/
noncomputable def modificationUniformizer (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] :
    Localization.AtPrime q :=
  letI := isDiscreteValuationRing_localization_isMaximal A B hA hinj q
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q))

omit [IsLocalRing A] in
/-- `Stacks.Chow.modificationUniformizer` is an irreducible element of `B_𝔮`. -/
theorem irreducible_modificationUniformizer (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] :
    Irreducible (modificationUniformizer A B hA hinj q) :=
  let := isDiscreteValuationRing_localization_isMaximal A B hA hinj q
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q))

omit [IsDomain A] [Module.Finite A B] [IsIntegrallyClosed B] in
/-- A nonzerodivisor of `A` stays a nonzerodivisor in `B_𝔮`, by
`Stacks.Chow.toExtensionNonZeroDivisor`: `𝔪` is not an associated prime of a domain extension. -/
theorem mem_nonZeroDivisors_algebraMap_localization (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [hq : q.IsMaximal] {x : A}
    (hx : x ∈ nonZeroDivisors A) :
    algebraMap A (Localization.AtPrime q) x ∈ nonZeroDivisors (Localization.AtPrime q) :=
  (toExtensionNonZeroDivisor (not_isAssociatedPrime_maximalIdeal (B := B) hinj hA)
    ⟨q, hq⟩ ⟨x, hx⟩).2

/-- The unit part of a nonzerodivisor of `A` at a maximal ideal of a normal finite
modification, with respect to `Stacks.Chow.modificationUniformizer`. -/
noncomputable def modificationFactorUnit (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] {x : A}
    (hx : x ∈ nonZeroDivisors A) : (Localization.AtPrime q)ˣ :=
  letI := isDiscreteValuationRing_localization_isMaximal A B hA hinj q
  dvrUnitPart (irreducible_modificationUniformizer A B hA hinj q)
    ⟨algebraMap A (Localization.AtPrime q) x,
      mem_nonZeroDivisors_algebraMap_localization A B hA hinj q hx⟩

/-- The exponent of a nonzerodivisor of `A` at a maximal ideal of a normal finite modification:
its order of vanishing in `B_𝔮`. -/
noncomputable def modificationExponent (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] {x : A}
    (hx : x ∈ nonZeroDivisors A) : ℕ :=
  letI := isDiscreteValuationRing_localization_isMaximal A B hA hinj q
  dvrOrd (A := Localization.AtPrime q)
    ⟨algebraMap A (Localization.AtPrime q) x,
      mem_nonZeroDivisors_algebraMap_localization A B hA hinj q hx⟩

/-- In `B_𝔮`, the image of a nonzerodivisor `x` of `A` equals
`Stacks.Chow.modificationFactorUnit` times `Stacks.Chow.modificationUniformizer` raised to
`Stacks.Chow.modificationExponent`. -/
theorem modificationFactorization (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsMaximal] {x : A}
    (hx : x ∈ nonZeroDivisors A) :
    algebraMap A (Localization.AtPrime q) x =
      (modificationFactorUnit A B hA hinj q hx : Localization.AtPrime q) *
        modificationUniformizer A B hA hinj q ^ modificationExponent A B hA hinj q hx :=
  let := isDiscreteValuationRing_localization_isMaximal A B hA hinj q
  dvrUnitPart_spec (irreducible_modificationUniformizer A B hA hinj q)
    ⟨algebraMap A (Localization.AtPrime q) x,
      mem_nonZeroDivisors_algebraMap_localization A B hA hinj q hx⟩

/-- **A normal finite modification prepares every family of nonzerodivisors of `A` at once.**
Stacks 0EAG produces, for a given finite family of nonzerodivisors, *some* finite extension in
which they all become unit multiples of powers of one local parameter. For a normal finite
modification `A ⊆ B` no such choice is needed: each `B_𝔮` is a discrete valuation ring, so a
single uniformizer there serves every element at once, the unit part and the exponent being
`Stacks.Chow.dvrUnitPart` and `Stacks.Chow.dvrOrd`. -/
noncomputable def modificationPreparation (hA : ¬ IsField A)
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {r : ℕ} (a : Fin r → A) (ha : ∀ i, a i ∈ nonZeroDivisors A) :
    TameSymbolPreparation a B where
  finite := inferInstance
  algebraMap_injective := hinj
  quotient_annihilated_by_maximalIdeal_power := hquot
  parameter q hq := modificationUniformizer A B hA hinj q
  parameter_isRegular q hq := isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_of_ne_zero
      (irreducible_modificationUniformizer A B hA hinj q).ne_zero)
  factorUnit q hq i := modificationFactorUnit A B hA hinj q (ha i)
  exponent q hq i := modificationExponent A B hA hinj q (ha i)
  factorization q hq i := by
    rw [← IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
    exact modificationFactorization A B hA hinj q (ha i)

/-- **Stacks 0EAQ for the tame symbol of a normal finite modification.** Let `(A, 𝔪)` be a
one-dimensional Noetherian local domain that is not a field and let `A ⊆ B` be module finite with
`B` an integrally closed domain and `B/A` annihilated by a power of `𝔪`. Let `P` be a
tame-symbol preparation of a family `a` over `B`, as produced by Stacks 0EAG: a local parameter
`π_𝔮` at each maximal ideal of `B` together with factorizations `a_i = u_{i, 𝔮} π_𝔮^{e_{i, 𝔮}}`
in `B_𝔮`. Then for two members `a i`, `a j` of the family, both nonzerodivisors of `A`,

`∂_A(a i, a j) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}`,

`m_𝔮 = length_{B_𝔮}(B_𝔮 / π_𝔮 B_𝔮)`, which is the displayed equation of the source.

`∂_A` on the left is this development's tame symbol
`Stacks.Chow.normPushforwardOfIsIntegrallyClosed`, not a symbol carried as a hypothesis: the
family of symbols on the localizations is the canonical one of a discrete valuation ring, and the
three remaining hypotheses of `Stacks.Chow.normPushforward_apply_eq_symbolValue` are consequences
of the finiteness of `A → B`. -/
@[stacks 0EAQ "for the tame symbol of a normal finite modification, on a preparation over that
modification"]
theorem normPushforwardOfIsIntegrallyClosed_apply_eq_symbolValue
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (hA : ¬ IsField A) (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normPushforwardOfIsIntegrallyClosed A B hA hinj hquot x y = P.symbolValue i j := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q =>
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) :=
    fun q => krullDimLE_one_localization_of_moduleFinite (A := A) q
  rw [normPushforwardOfIsIntegrallyClosed, normPushforwardOfModuleFinite_apply]
  exact normPushforward_apply_eq_symbolValue _ _ hinj hquot P i j x y hx hy

end Modification

section IntegralClosure

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  [IsDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  [Module.Finite A (integralClosure A K)]

omit [IsDomain A] in
/-- A power of `𝔪` annihilates the quotient of the integral closure by `A`: a single
nonzerodivisor of `A` clears the denominators of its finitely many module generators. -/
theorem exists_maximalIdeal_pow_smul_le_integralClosure :
    ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A (integralClosure A K)) ≤
      LinearMap.range (Algebra.linearMap A (integralClosure A K)) := by
  obtain ⟨d, hd, hdB⟩ := exists_nonZeroDivisor_smul_mem_range A (integralClosure A K)
    (K := K) Subtype.val_injective
  exact exists_maximalIdeal_pow_smul_le hd hdB

/-- **The integral closure prepares every family of nonzerodivisors of `A`**, by
`Stacks.Chow.modificationPreparation`: a module-finite integral closure is a normal finite
modification. This is the witness that makes the statements below non-vacuous; no appeal to
Stacks 0EAG is involved. -/
noncomputable def integralClosurePreparation (hA : ¬ IsField A) {r : ℕ} (a : Fin r → A)
    (ha : ∀ i, a i ∈ nonZeroDivisors A) : TameSymbolPreparation a (integralClosure A K) :=
  haveI : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (L := K) K
  modificationPreparation A (integralClosure A K) hA
    (fun _ _ h ↦ IsFractionRing.injective A K (congrArg Subtype.val h))
    (exists_maximalIdeal_pow_smul_le_integralClosure A K) a ha

variable [Fintype (MaximalSpectrum (integralClosure A K))]
  [∀ q : MaximalSpectrum (integralClosure A K),
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]

/-- **Stacks 0EAQ for the tame symbol on nonzerodivisors of `A`.** With `B` the integral closure
of `A` in its fraction field, the symbol of
`Stacks.Chow.normPushforwardOfIsIntegrallyClosed` is
`Stacks.Chow.normPushforwardOfFiniteIntegralClosure`, which depends on nothing but `A` and `K`;
so the displayed equation of the source holds for it, on a preparation over that integral
closure — for instance `Stacks.Chow.integralClosurePreparation`. -/
@[stacks 0EAQ "for the tame symbol on nonzerodivisors of A, on a preparation over the integral
closure of A in its fraction field"]
theorem normPushforwardOfFiniteIntegralClosure_apply_eq_symbolValue (hA : ¬ IsField A)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a (integralClosure A K)) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normPushforwardOfFiniteIntegralClosure A K hA x y = P.symbolValue i j := by
  have : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (L := K) K
  have hinj : Function.Injective (algebraMap A (integralClosure A K)) :=
    fun _ _ h ↦ IsFractionRing.injective A K (congrArg Subtype.val h)
  have hquot := exists_maximalIdeal_pow_smul_le_integralClosure A K
  rw [normPushforwardOfFiniteIntegralClosure]
  exact normPushforwardOfIsIntegrallyClosed_apply_eq_symbolValue A (integralClosure A K) hA hinj
    hquot P i j x y hx hy

/-- **Stacks 0EAQ, at the spelling of the source.** For a one-dimensional Noetherian local domain
`A` that is not a field and whose integral closure in its fraction field is module finite, the
tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

of Stacks 0EAH — `Stacks.Chow.tameSymbolOfFiniteIntegralClosure` — is given on a pair of
nonzerodivisors of `A` by the product of the source:

`∂_A(a₁, a₂) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}} u_{2,j}^{-e_{1,j}}
  mod 𝔪_j)^{m_j}`,

computed from any tame-symbol preparation of the pair over the integral closure. The extension of
a symbol on nonzerodivisors to `Q(A)^*` restricts back to it
(`Stacks.Chow.RegularTameSymbol.extend_regularFractionUnit`), so this is the previous statement
transported along `Stacks.Chow.regularFractionUnit`. -/
@[stacks 0EAQ "for the tame symbol on Q(A)^*, on a preparation over the integral closure of A in
its fraction field"]
theorem tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue (hA : ¬ IsField A)
    (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a (integralClosure A K)) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    tameSymbolOfFiniteIntegralClosure A K hA Q (regularFractionUnit x) (regularFractionUnit y) =
      P.symbolValue i j := by
  rw [tameSymbolOfFiniteIntegralClosure, RegularTameSymbol.extend_regularFractionUnit]
  exact normPushforwardOfFiniteIntegralClosure_apply_eq_symbolValue A K hA P i j x y hx hy

end IntegralClosure

section Unconditional

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  [IsDomain A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  [Module.Finite A (integralClosure A K)]

/-- **Stacks 0EAQ with nothing assumed beyond the hypotheses on `A`.** For a one-dimensional
Noetherian local domain `A` that is not a field whose integral closure in its fraction field is
module finite, and for any finite family `a` of nonzerodivisors of `A`,

`∂_A(a i, a j) = ∏_j Norm_{κ(𝔪_j)/κ(𝔪)}((-1)^{e_{1,j} e_{2,j}} u_{1,j}^{e_{2,j}}
  u_{2,j}^{-e_{1,j}} mod 𝔪_j)^{m_j}`,

the preparation being the canonical one on the integral closure
(`Stacks.Chow.integralClosurePreparation`) and the symbol being
`Stacks.Chow.tameSymbolOfFiniteIntegralClosure`, the map
`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of Stacks 0EAH.

Nothing here is a hypothesis that the finiteness of `A → B` does not already give: the maximal
ideals of the integral closure are finite in number by
`Stacks.Length.finite_maximalSpectrum`, each localization is local over `A` by
`Stacks.Length.isLocalHom_algebraMap_localization`, and those are the two instances the product
of the source needs in order to be written down at all. They are supplied in the statement rather
than assumed, which is what distinguishes this from
`Stacks.Chow.tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue`. -/
@[stacks 0EAQ "unconditionally for a one-dimensional Noetherian local domain with a module-finite
integral closure: the symbol of Stacks 0EAH on Q(A)^*, the canonical preparation on the integral
closure, and no instance assumed that the finiteness of the extension does not supply"]
theorem tameSymbolOfFiniteIntegralClosure_eq_symbolValue (hA : ¬ IsField A)
    (Q : Type*) [CommRing Q] [Algebra A Q] [IsFractionRing A Q]
    {r : ℕ} (a : Fin r → A) (ha : ∀ i, a i ∈ nonZeroDivisors A) (i j : Fin r) :
    letI := Stacks.Length.finite_maximalSpectrum (A := A) (B := integralClosure A K)
    letI := Fintype.ofFinite (MaximalSpectrum (integralClosure A K))
    letI : ∀ q : MaximalSpectrum (integralClosure A K),
        IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := fun q =>
      Stacks.Length.isLocalHom_algebraMap_localization q
    tameSymbolOfFiniteIntegralClosure A K hA Q
        (regularFractionUnit ⟨a i, ha i⟩) (regularFractionUnit ⟨a j, ha j⟩) =
      (integralClosurePreparation A K hA a ha).symbolValue i j := by
  let : Finite (MaximalSpectrum (integralClosure A K)) :=
    Stacks.Length.finite_maximalSpectrum (A := A) (B := integralClosure A K)
  let : Fintype (MaximalSpectrum (integralClosure A K)) :=
    Fintype.ofFinite (MaximalSpectrum (integralClosure A K))
  let : ∀ q : MaximalSpectrum (integralClosure A K),
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := fun q =>
    Stacks.Length.isLocalHom_algebraMap_localization q
  exact tameSymbolOfFiniteIntegralClosure_apply_eq_symbolValue A K hA Q
    (integralClosurePreparation A K hA a ha) i j ⟨a i, ha i⟩ ⟨a j, ha j⟩ rfl rfl

end Unconditional

end Stacks.Chow

end
