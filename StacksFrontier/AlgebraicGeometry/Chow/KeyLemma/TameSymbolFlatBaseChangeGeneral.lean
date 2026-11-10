module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefined
public import StacksFrontier.RingTheory.Length.NormFlatBaseChange

/-!
# The tame symbol of a general pair of nonzerodivisors under a flat local homomorphism

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian local
rings and let `m = length_{A'}(A' / 𝔪A')`. Stacks 0EPG asserts that for nonzerodivisors
`a₁, a₂ ∈ A` the element `∂_A(a₁, a₂) ^ m` of `κ` maps to `∂_{A'}(a₁, a₂)` under `κ → κ'`.

`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChange` proves this for a pair
that already admits a simultaneous power factorization `a₁ = u π^{e₁}`, `a₂ = v π^{e₂}` over `A`
itself. This file removes that restriction: it proves the statement for the value of the formula
Stacks 0EAQ on an arbitrary tame-symbol preparation, which by Stacks 0EAG exists for *every*
pair of nonzerodivisors of `A`.

## Main definitions

* `Stacks.Chow.baseChangeLocalizationHom` — the structure map `B → (A' ⊗_A B)_𝔭` of the base
  change at a maximal ideal of `A' ⊗_A B`.

## Main results

* `Stacks.Chow.map_norm_factorizationValue_pow_eq_prod` — Stacks 0EPG at a single maximal ideal:
  the `m`-th power of the norm of the factor of Stacks 0EAQ, read in `κ'`, is the product of the
  norms of the corresponding factors over the maximal ideals of `A' ⊗_A B`.
* `Stacks.Chow.map_symbolValue_pow_eq_prod_prod` — Stacks 0EPG for a general pair of
  nonzerodivisors: the formula Stacks 0EAQ over `A`, raised to the power `m` and read in `κ'`,
  is the formula Stacks 0EAQ over `A'` for the base-changed data.
* `Stacks.Chow.map_normPushforward_pow_eq_prod_prod` — the same equation with the left-hand side
  spelled as the tame symbol `∂_A(a₁, a₂)` of Stacks 0EAT.

## Implementation notes

The index set of the right-hand side is the maximal ideals of `A' ⊗_A B_𝔮`, fibre by fibre over
the maximal ideals `𝔮` of `B`, rather than the maximal ideals of `A' ⊗_A B` as in the source; the
two are identified by `Stacks.Chow.baseChangeSigmaEquiv`.

The finiteness of the set of maximal ideals of `A' ⊗_A B_𝔮`, the locality of
`A' → (A' ⊗_A B_𝔮)_𝔭` and the finiteness of the residue field extensions are carried as instance
hypotheses, exactly as the corresponding facts about `B` are carried by
`Stacks.Chow.normProd` and `AlgebraicGeometry.TameSymbolPreparation.symbolValue`. Asked at
*every* maximal ideal `𝔭` of `A' ⊗_A B_𝔮`, they are more than holds in the situation of
Stacks 0EPG: `A' ⊗_A B_𝔮` is a localization of a ring finite over `A'`, not a finite
`A'`-algebra, and the maximal ideals it acquires in the process need not have a local ring over
which `A'` is local. For `A = ℤ_(5)`, `A' = ℤ₅`, `B` the semilocalization of `ℤ[i]` at `5` and
`𝔮` one of its two maximal ideals, `A' ⊗_A B_𝔮` is `ℚ₅ × ℤ₅`, whose local ring at `0 × ℤ₅` is
`ℚ₅`. The forms that apply are `Stacks.Chow.map_norm_factorizationValue_pow_eq_prod_support` and
`Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support`, which ask for those hypotheses at the
maximal ideals carrying the parameter only.

The multiplier `m` is carried as a natural number together with the hypothesis
`length_{A'}(A' / 𝔪A') = m`, as in
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChange`.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0GU1](https://stacks.math.columbia.edu/tag/0GU1)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

section BaseChange

variable {A : Type u} [CommRing A] (A' : Type v) [CommRing A'] [Algebra A A']
  {B : Type w} [CommRing B] [Algebra A B]

/-- **The structure map of a base change at a maximal ideal.** For a maximal ideal `𝔭` of
`A' ⊗_A B` this is the composition of `b ↦ 1 ⊗ b` with the localization map. -/
noncomputable def baseChangeLocalizationHom (p : MaximalSpectrum (A' ⊗[A] B)) :
    B →+* Localization.AtPrime p.asIdeal :=
  (algebraMap (A' ⊗[A] B) (Localization.AtPrime p.asIdeal)).comp
    (Algebra.TensorProduct.includeRight (A := A') : B →ₐ[A] A' ⊗[A] B).toRingHom

/-- `baseChangeLocalizationHom A' p` sends `b` to the image of `1 ⊗ b` in `(A' ⊗_A B)_𝔭`. -/
@[simp]
theorem baseChangeLocalizationHom_apply (p : MaximalSpectrum (A' ⊗[A] B)) (b : B) :
    baseChangeLocalizationHom A' p b =
      algebraMap (A' ⊗[A] B) (Localization.AtPrime p.asIdeal)
        (Algebra.TensorProduct.includeRight b) := rfl

end BaseChange

section Factorization

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The factor of Stacks 0EAQ is the residue of a unit of `R`, raised to `length_R(R / πR)`:
the unit is `(-1)^{ef} u^f v^{-e}`. -/
theorem factorizationValue_eq_units_map_residue (π : R) (u v : Rˣ) (e f : ℕ) :
    factorizationValue π u v e f =
      Units.map (residue R).toMonoidHom ((-1) ^ (e * f) * u ^ f * (v ^ e)⁻¹) ^
        (Ring.ord R π).toNat := by
  have hneg : Units.map (residue R).toMonoidHom (-1 : Rˣ) = (-1 : (ResidueField R)ˣ) :=
    Units.ext (by simp)
  simp only [factorizationValue, map_mul, map_pow, map_inv, hneg, inv_pow]

end Factorization

/-- **Stacks 0EPG at a single maximal ideal.** Let `A → A'` be a flat local homomorphism of local
rings with `m = length_{A'}(A' / 𝔪A')`, and let `B` be a one-dimensional Noetherian local
`A`-algebra along a local homomorphism with `κ(B)/κ(A)` finite. For a nonzerodivisor `π` of `B`,
units `u`, `v` of `B` and exponents `e`, `f`, the norm to `κ` of the factor Stacks 0EAQ attaches
to that data, raised to the power `m` and read in `κ'`, is the product over the maximal ideals
`𝔭` of `A' ⊗_A B` of the norms to `κ'` of the factors attached to the images of the data in
`(A' ⊗_A B)_𝔭`. -/
theorem map_norm_factorizationValue_pow_eq_prod
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A']
    [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    {B : Type w} [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Ring.KrullDimLE 1 B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Finite (ResidueField A) (ResidueField B)]
    [Fintype (MaximalSpectrum (A' ⊗[A] B))]
    [∀ p : MaximalSpectrum (A' ⊗[A] B),
      IsLocalHom (algebraMap A' (Localization.AtPrime p.asIdeal))]
    [∀ p : MaximalSpectrum (A' ⊗[A] B),
      Module.Finite (ResidueField A') (ResidueField (Localization.AtPrime p.asIdeal))]
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    {π : B} (hπ : π ∈ nonZeroDivisors B) (u v : Bˣ) (e f : ℕ) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (Units.map (Algebra.norm (ResidueField A) : ResidueField B →* ResidueField A)
          (factorizationValue π u v e f)) ^ m =
      ∏ p : MaximalSpectrum (A' ⊗[A] B),
        Units.map (Algebra.norm (ResidueField A') :
            ResidueField (Localization.AtPrime p.asIdeal) →* ResidueField A')
          (factorizationValue (baseChangeLocalizationHom A' p π)
            (Units.map (baseChangeLocalizationHom A' p).toMonoidHom u)
            (Units.map (baseChangeLocalizationHom A' p).toMonoidHom v) e f) := by
  have hM : IsFiniteLength B (B ⧸ Ideal.span {π}) :=
    Module.length_ne_top_iff.mp (Ring.ord_ne_top hπ)
  have hkey := Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length
    (A := A) (S := A') (B := B) π (((-1) ^ (e * f) * u ^ f * (v ^ e)⁻¹ : Bˣ) : B) hM hm
  have hright (p : MaximalSpectrum (A' ⊗[A] B)) :
      ((-1) ^ (e * f) * (Units.map (baseChangeLocalizationHom A' p).toMonoidHom u) ^ f *
          ((Units.map (baseChangeLocalizationHom A' p).toMonoidHom v) ^ e)⁻¹) =
        Units.map (baseChangeLocalizationHom A' p).toMonoidHom
          ((-1) ^ (e * f) * u ^ f * (v ^ e)⁻¹) := by
    have hneg : Units.map (baseChangeLocalizationHom A' p).toMonoidHom (-1 : Bˣ) =
        (-1 : (Localization.AtPrime p.asIdeal)ˣ) := Units.ext (by simp)
    simp only [map_mul, map_pow, map_inv, hneg]
  refine Units.ext ?_
  simp only [factorizationValue_eq_units_map_residue, hright]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass,
    RingHom.toMonoidHom_eq_coe, map_pow, Ring.ord, baseChangeLocalizationHom_apply]
  simp only [map_pow] at hkey
  exact hkey.trans (Finset.prod_congr rfl fun i _ => rfl)

section General

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {A' : Type v} [CommRing A'] [IsLocalRing A'] [Algebra A A']
  [IsLocalHom (algebraMap A A')] [Module.Flat A A']
  {B : Type w} [CommRing B] [Algebra A B]
  [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B,
    Module.Finite (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, Fintype (MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal))]
  [∀ (q : MaximalSpectrum B) (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal)),
    IsLocalHom (algebraMap A' (Localization.AtPrime p.asIdeal))]
  [∀ (q : MaximalSpectrum B) (p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal)),
    Module.Finite (ResidueField A') (ResidueField (Localization.AtPrime p.asIdeal))]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian
local rings and let `m = length_{A'}(A' / 𝔪A')`. Let `A ⊆ B` be a finite extension carrying a
tame-symbol preparation of a family `a` of elements of `A` (by Stacks 0EAG one exists for every
pair of nonzerodivisors of `A`). Then the value of the formula Stacks 0EAQ for two members of
that family, raised to the power `m` and read in `κ'`, is the value of the same formula over `A'`
for the base-changed data:

`(∏_𝔮 Norm_{κ(𝔮)/κ}(c_𝔮))^m = ∏_𝔮 ∏_𝔭 Norm_{κ(𝔭)/κ'}(c_𝔭)`,

where `𝔮` runs over the maximal ideals of `B`, `𝔭` over the maximal ideals of `A' ⊗_A B_𝔮`, and
the local data over `𝔭` is the image of the local data over `𝔮` under `B_𝔮 → (A' ⊗_A B_𝔮)_𝔭`.
The index set of the right-hand side is thus presented fibre by fibre over the maximal ideals of
`B`; in the source it is presented as the set of maximal ideals of `A' ⊗_A B`, whose fibred
decomposition is `Stacks.Chow.baseChangeSigmaEquiv`. The hypotheses below hold only at the maximal
ideals carrying the parameter; `Stacks.Chow.map_symbolValue_pow_eq_prod_prod_support` is the form
that asks for them there alone. -/
@[stacks 0EPG "for a general pair of nonzerodivisors, in the spelling in which both sides are \
the formula Stacks 0EAQ: on the left for a tame-symbol preparation over a finite extension `B` \
of `A`, which Stacks 0EAG provides for every pair, and on the right for the base change of that \
preparation, with the maximal ideals of `A' ⊗_A B` presented fibre by fibre over those of `B`"]
theorem map_symbolValue_pow_eq_prod_prod
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom (P.symbolValue i j) ^ m =
      ∏ q : MaximalSpectrum B,
        ∏ p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal),
          Units.map (Algebra.norm (ResidueField A') :
              ResidueField (Localization.AtPrime p.asIdeal) →* ResidueField A')
            (factorizationValue (baseChangeLocalizationHom A' p (P.parameter q.asIdeal))
              (Units.map (baseChangeLocalizationHom A' p).toMonoidHom (P.factorUnit q.asIdeal i))
              (Units.map (baseChangeLocalizationHom A' p).toMonoidHom (P.factorUnit q.asIdeal j))
              (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)) := by
  rw [TameSymbolPreparation.symbolValue, map_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun q _ =>
    map_norm_factorizationValue_pow_eq_prod hm
      (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal)) _ _ _ _

/-- For nonzerodivisors `a₁ = a i` and `a₂ = a j` of `A` and a tame-symbol preparation `P` of `a`
over `B`, the tame symbol `∂_A(a₁, a₂)` of Stacks 0EAT, raised to the power `m` and read in `κ'`,
is the value of the formula Stacks 0EAQ over `A'` for the base change of `P`: the right-hand side
of `Stacks.Chow.map_symbolValue_pow_eq_prod_prod`. -/
@[stacks 0EPG "for a general pair of nonzerodivisors, with the symbol on `A` spelled as the norm \
pushforward of Stacks 0EAT and the symbol on `A'` as the formula Stacks 0EAQ for the base change"]
theorem map_normPushforward_pow_eq_prod_prod [Module.Finite A B]
    {m : ℕ} (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (normPushforward hass symb hinj hquot x y) ^ m =
      ∏ q : MaximalSpectrum B,
        ∏ p : MaximalSpectrum (A' ⊗[A] Localization.AtPrime q.asIdeal),
          Units.map (Algebra.norm (ResidueField A') :
              ResidueField (Localization.AtPrime p.asIdeal) →* ResidueField A')
            (factorizationValue (baseChangeLocalizationHom A' p (P.parameter q.asIdeal))
              (Units.map (baseChangeLocalizationHom A' p).toMonoidHom (P.factorUnit q.asIdeal i))
              (Units.map (baseChangeLocalizationHom A' p).toMonoidHom (P.factorUnit q.asIdeal j))
              (P.exponent q.asIdeal i) (P.exponent q.asIdeal j)) := by
  rw [normPushforward_apply_eq_symbolValue hass symb hinj hquot P i j x y hx hy]
  exact map_symbolValue_pow_eq_prod_prod hm P i j

end General

end Stacks.Chow

end
