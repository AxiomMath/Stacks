module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionTame
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionB
public import StacksFrontier.RingTheory.DiscreteValuationRing.KummerCompletion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Step 3 of Tag 09F9 in the wild case

`EppCompletionTame` proves step 3 for a weak solution `M / K^` that is **separable**, which is Tag
09EJ's hypothesis and is free only in mixed characteristic. In equal characteristic `M / K^` need
not be separable, and the published proof supplies instead its condition (b): `M` is a compositum
of a separable extension and one obtained by adjoining a `p`-power root of a uniformizer. That is
proved, in the form the proof consumes, as
`Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin` — for a `p`-power root `ρ` of `π` inside
  `M`, with
`M / K^⟮ρ⟯` separable.

This file consumes it.

## Main results

* an `example` recording that **condition (b) applies at `A^` with the two residue
  transports** — a composition check, which passes. It is an
  `example` because restating condition (b)'s conclusion over `A^` does not elaborate; see the
  implementation note there, which constrains how that statement must be written.
* `Algebra.isSeparable_of_adjoin_pow_one`: the degenerate case `n = 0` of condition (b), where `ρ`
  lies in the base and separability over `K⟮ρ⟯` is separability over `K`.

## Implementation notes

The case split in the wild route is on the `n` that condition (b) returns, **not** on the
characteristic — condition (b) proves both characteristics, and it can return `n = 0` in equal
characteristic too, whenever `π` has no further `p`-power root in `M`. Only `n = 0` is degenerate:
`Stacks.KummerExtension.isDiscreteValuationRing_A1` needs the Kummer exponent to be at least `2`,
  and that
exponent is `p ^ n`, which for prime `p` is at least `2` as soon as `n ≥ 1`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09EJ](https://stacks.math.columbia.edu/tag/09EJ)
-/

@[expose] public section

open IsLocalRing Polynomial

universe uA uB uK uL z₁ z₂ z₃

/-- **The degenerate case of condition (b).**

If the `p`-power root `ρ` is a first root — `ρ ^ 1` is in the image of the base — then `ρ` lies in
the base, `K⟮ρ⟯` is the bottom intermediate field, and separability of `M` over `K⟮ρ⟯` *is*
separability over `K`.

This is what makes condition (b)'s `n = 0` output usable: it hands step 3 the separability that
`exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion` asks for, with no Kummer
machinery at all. -/
theorem Algebra.isSeparable_of_adjoin_pow_one
    {K M : Type*} [Field K] [Field M] [Algebra K M] {x : K} {ρ : M}
    (hρ : ρ ^ 1 = algebraMap K M x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K {ρ}) M) :
    Algebra.IsSeparable K M := by
  have hmem : ρ ∈ (⊥ : IntermediateField K M) := by
    rw [IntermediateField.mem_bot]
    exact ⟨x, by simpa using hρ.symm⟩
  have hbot : IntermediateField.adjoin K {ρ} = ⊥ :=
    le_antisymm (IntermediateField.adjoin_le_iff.mpr (by simpa using hmem)) bot_le
  rw [hbot] at hsep
  refine Algebra.IsSeparable.of_equiv_equiv (IntermediateField.botEquiv K M).toRingEquiv
    (RingEquiv.refl M) (RingHom.ext fun y => ?_)
  obtain ⟨z, rfl⟩ := (IntermediateField.botEquiv K M).symm.surjective y
  simp [IntermediateField.botEquiv_symm]

namespace IsDiscreteValuationRing

/-- **Residue characteristic `p` with `p ≠ 0` in the ring means characteristic zero.**

For a discrete valuation ring whose residue field has characteristic `p`, the ring itself has
characteristic `p` or characteristic zero — the two cases being equal and mixed characteristic —
and `(p : A) ≠ 0` selects the second. The argument: `ringChar A` is prime or zero; if prime then
`p` divides it (because `p` dies in the residue field) and primality forces `p = ringChar A`,
making `(p : A) = 0`.

This is the case distinction that the wild route of step 3 turns on, and the one condition (b)'s
own proof makes. It appears inline in `Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin`; it
  is stated
here because step 3 has to make the same split *before* invoking condition (b), in order to know
which branch it is in. -/
theorem charZero_of_ne_zero_of_charP_residueField (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField A) p]
    (hpA : (p : A) ≠ 0) :
    CharZero A := by
  have hCr := ringChar.charP A
  rcases CharP.char_is_prime_or_zero A (ringChar A) with hprime | hzero
  · refine absurd ?_ hpA
    have hq0 : ((ringChar A : ℕ) : ResidueField A) = 0 := by
      rw [← map_natCast (IsLocalRing.residue A) (ringChar A), CharP.cast_eq_zero A (ringChar A),
        map_zero]
    have hpq : p ∣ ringChar A := (CharP.cast_eq_zero_iff (ResidueField A) p _).mp hq0
    have hpe : p = ringChar A := (hprime.eq_one_or_self_of_dvd p hpq).resolve_left hp.out.ne_one
    rw [hpe]
    exact CharP.cast_eq_zero A _
  · have : CharP A 0 := hzero ▸ hCr
    exact CharP.charP_to_charZero A

/-- **The fraction field of the completion inherits characteristic zero.**

`A → K^` is injective (`injective_algebraMap_adicCompletionFractionField`), and characteristic zero
transports along an injective ring map.

Together with the previous lemma this is what makes step 3 free in mixed characteristic: `K^` has
characteristic zero, so every finite extension of it is separable, so Tag 09EJ applies directly and
condition (b) is never needed. -/
theorem charZero_adicCompletionFractionField (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CharZero A] :
    CharZero (AdicCompletionFractionField A) :=
  charZero_of_injective_algebraMap (injective_algebraMap_adicCompletionFractionField A)

/-- **The composition check: condition (b) applies at `A^`, with the residue transports.**

Condition (b) (`Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin`) is stated over a complete
discrete
valuation ring with perfect residue field of characteristic `p`; step 3 applies it to `A^`. This is
the check that the two transports of `EppCompletionSquare` —
`perfectField_residueField_adicCompletion` and `charP_residueField_adicCompletion` — supply exactly
what those binders ask for, alongside `IsAdicComplete` of the completion (a Mathlib instance) and
`IsFractionRing A^ K^`. **It passes**, which is what this declaration records.

It is an `example`, and the reason is a finding rather than a convenience: **restating condition
(b)'s conclusion over `A^` does not elaborate.** A theorem whose conclusion writes out
`algebraMap A^ K^ π` in the position condition (b) puts it diverges at `whnf` — not slowly, but
past four million heartbeats, so a budget will not fix it. Applying condition (b) inside a tactic
block, where the expected type is not a restatement, elaborates immediately. P1 therefore performs
this composition the way it is performed here — two `let`s and a `have` — and must **not** try to
package it as a lemma with an explicit conclusion.

One further constraint found the same way: the uniformizer must be *bound* before it is passed, not
built inline. Passing `algebraMap A A^ π` directly into condition (b)'s `π` argument diverges too;
binding it first — `have hπ' : Irreducible (algebraMap A A^ π) :=`
`irreducible_algebraMap_adicCompletion A hπ`, then passing the bound term — does not. -/
example (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [PerfectField (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (π : AdicCompletion (IsLocalRing.maximalIdeal A) A) (hπ : Irreducible π)
    (M : Type) [Field M] [Algebra (AdicCompletionFractionField A) M]
    [Module.Finite (AdicCompletionFractionField A) M] : True := by
  let := perfectField_residueField_adicCompletion A
  let := charP_residueField_adicCompletion A p
  have := Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin
    (A := AdicCompletion (IsLocalRing.maximalIdeal A) A)
    (K := AdicCompletionFractionField A) (M := M) p π hπ
  trivial

end IsDiscreteValuationRing

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

open scoped TensorProduct

/-- **Condition (b)'s `minpoly` conjunct, read as an isomorphism.**

Condition (b) hands back `ρ ∈ M` with `minpoly K ρ = X ^ q - C π`. Since the Kummer field of Tag
09EV is by construction `AdjoinRoot (X ^ q - C π)`, that equation says exactly that `K⟮ρ⟯` **is**
the Kummer field `K(π^{1/q})`:

`Stacks.KummerExtension.K1 K π q ≃ₐ[K] K⟮ρ⟯`.

This is the load-bearing use of the `minpoly` conjunct, and the reason that conjunct was worth
asking condition (b) for: the degree alone would give `[K⟮ρ⟯ : K] = q` without saying that the
generator satisfies *that* polynomial, and it is the polynomial that matches the two
`AdjoinRoot`s. -/
noncomputable def kummerAlgEquivAdjoin {Ah Kc M : Type*} [CommRing Ah] [IsDomain Ah]
    [IsDiscreteValuationRing Ah] [Field Kc] [Algebra Ah Kc] [IsFractionRing Ah Kc]
    [Field M] [Algebra Kc M] [Module.Finite Kc M]
    (π : Ah) (q : ℕ) (ρ : M) (hmin : minpoly Kc ρ = Stacks.KummerExtension.kummerPoly Kc π q) :
    Stacks.KummerExtension.K1 Kc π q ≃ₐ[Kc] IntermediateField.adjoin Kc {ρ} :=
  (AdjoinRoot.algEquivOfAssociated Kc (Stacks.KummerExtension.kummerPoly Kc π q) (minpoly Kc ρ)
      (hmin ▸ Associated.refl _)).trans
    (IntermediateField.adjoinRootEquivAdjoin Kc (IsIntegral.of_finite Kc ρ))

section

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {M : Type*} [Field M] [Algebra (AdicCompletionFractionField A) M]
    [Module.Finite (AdicCompletionFractionField A) M]

/-- **`K^⟮ρ⟯` is a fraction field of the completion of `A_n`.**

This is what makes Tag 09EJ applicable over `A_n`: 09EJ asks for a field receiving
`(A_n)^∧` as its fraction field, and the field it has to be handed is `K^⟮ρ⟯`, because that is
where condition (b) puts the separable part of `M`.

Both inputs are already in place. `Stacks.KummerExtension.exists_ringEquiv_adicCompletion_A1`
  identifies
`(A_n)^∧` with the Kummer ring of integers over `A^∧`, whose fraction field is the Kummer field
over `A^∧` (`Stacks.KummerExtension.isFractionRing_A1`); and `kummerAlgEquivAdjoin` identifies that
  Kummer
field with `K^⟮ρ⟯`. `IsFractionRing.of_ringEquiv_ringEquiv` puts the two together, and the
compatibility it asks for is `rfl` because the algebra structure returned here is *defined* as the
composite of the two isomorphisms with the structure map between them.

The algebra structure is returned in the existential rather than declared, because it is built from
`exists_ringEquiv_adicCompletion_A1`, which is itself an existential (see the note there). A
consumer does `obtain ⟨alg, hfr, hcompat⟩ := …` and then `let _ := alg`.

The third conjunct is what stops the inexplicitness from mattering. It says the structure map
`(A_n)^∧ → K^⟮ρ⟯` **restricts on `A` to the one already there**, `A → K^ → K^⟮ρ⟯`. That is the only
thing the surrounding argument needs to know about a map built out of an existential, and it is
exactly what the `A`-linearity carried by `exists_ringEquiv_adicCompletion_A1` delivers: the two
towers out of `A` — one through `A_n` and its completion, one through `A^∧` and `K^` — agree. Tag
09EJ's conclusion speaks of `K_n` through an `IsFractionRing.lift` of this very map, so a consumer
comparing 09EJ's `K_n → K^⟮ρ⟯` with anything else compares them on `A` and appeals to this. -/
theorem exists_algebra_isFractionRing_adjoin
    (π : A) (q : ℕ) (hq : 2 ≤ q) (hπ : Irreducible π) (ρ : M)
    [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π q))]
    [IsLocalRing (Stacks.KummerExtension.A1 K π q)]
    (hmin : minpoly (AdicCompletionFractionField A) ρ = Stacks.KummerExtension.kummerPoly
      (AdicCompletionFractionField A)
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q) :
    ∃ alg : Algebra (AdicCompletion (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π q))
        (Stacks.KummerExtension.A1 K π q))
        (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}),
      letI := alg
      IsFractionRing (AdicCompletion (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π q))
        (Stacks.KummerExtension.A1 K π q))
        (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) ∧
      ∀ x : A, algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π
        q))
          (Stacks.KummerExtension.A1 K π q)) (IntermediateField.adjoin (AdicCompletionFractionField
            A) {ρ})
          (algebraMap A _ x)
        = algebraMap (AdicCompletionFractionField A)
            (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
            (algebraMap A (AdicCompletionFractionField A) x) := by
  have hπh : Irreducible (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) :=
    irreducible_algebraMap_adicCompletion A hπ
  obtain ⟨ch, hch⟩ := Stacks.KummerExtension.exists_ringEquiv_adicCompletion_A1 K
    (AdicCompletionFractionField A) π q hq hπ hπh
  let f := kummerAlgEquivAdjoin
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q ρ hmin
  have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly (AdicCompletionFractionField A)
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible _ _ _ (by omega) hπh⟩
  have hfr := Stacks.KummerExtension.isFractionRing_A1 (AdicCompletionFractionField A)
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q
  let alg := ((f.toRingEquiv.toRingHom.comp (algebraMap
    (Stacks.KummerExtension.A1 (AdicCompletionFractionField A)
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q)
    (Stacks.KummerExtension.K1 (AdicCompletionFractionField A)
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q))).comp
        ch.toRingHom).toAlgebra
  let _ := alg
  refine ⟨alg, IsFractionRing.of_ringEquiv_ringEquiv ch f.toRingEquiv fun _ => rfl, fun x => ?_⟩
  change f (algebraMap _ _ (ch (algebraMap A _ x))) = _
  rw [hch,
    ← IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (Stacks.KummerExtension.A1 (AdicCompletionFractionField A)
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q)
      (Stacks.KummerExtension.K1 (AdicCompletionFractionField A)
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q),
    IsScalarTower.algebraMap_apply (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletionFractionField A)
      (Stacks.KummerExtension.K1 (AdicCompletionFractionField A)
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q),
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) (AdicCompletionFractionField A)]

/-- **Tag 09EJ applies over `A_n` at `Khat := K^⟮ρ⟯`, and this records that it does.**

Every binder of `exists_finite_separable_extension_tensorProduct_equiv_of_isDVR` is met at
`A := A_n`, `K := K_n`, `Khat := K^⟮ρ⟯`, `M := M`: the base is a discrete valuation ring by Tag
09EV (3) with `K_n` as its fraction field (`Stacks.KummerExtension.isFractionRing_A1`), the
  completion's
fraction field is `K^⟮ρ⟯` by `exists_algebra_isFractionRing_adjoin`, `M` is finite over `K^⟮ρ⟯`
because it is finite over `K^` beneath it, and `M / K^⟮ρ⟯` is separable — which is condition (b)'s
third conjunct, and the whole reason the wild case is routed through `K_n` rather than through `K`.

So 09EJ returns a finite separable `L / K_n` together with `K^⟮ρ⟯ ⊗_{K_n} L ≃ₐ M`, which is the
input to the final base-change cancellation.

This is an `example`, for the same reason the composition check above is: the equivalence 09EJ
returns is stated through two statement-level `letI`s of its own (`Algebra A Khat` and
`Algebra K Khat`), so a theorem re-exporting it would have to re-declare those instances in its own
conclusion, and what a consumer then needs is not the equivalence alone but a characterisation of
those instances. The remaining work is exactly that characterisation.
What is checked here, and checked by the build, is that
the application itself elaborates — which was the open architectural question. -/
example (π : A) (q : ℕ) (hq : 2 ≤ q) (hπ : Irreducible π) (ρ : M)
    [Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π q))]
    [IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π q)]
    (hmin : minpoly (AdicCompletionFractionField A) ρ = Stacks.KummerExtension.kummerPoly
      (AdicCompletionFractionField A)
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) π) q)
    (hsep : Algebra.IsSeparable
      (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M) :
    True := by
  let _ := Stacks.KummerExtension.isFractionRing_A1 K π q
  obtain ⟨alg, hfr, -⟩ := exists_algebra_isFractionRing_adjoin K π q hq hπ ρ hmin
  let _ := alg
  let _ := hfr
  let _ := hsep
  have : FiniteDimensional (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M :=
    Module.Finite.of_restrictScalars_finite (AdicCompletionFractionField A) _ M
  obtain ⟨L, hLfin, hLsep, ⟨ψ⟩⟩ :=
    exists_finite_separable_extension_tensorProduct_equiv_of_isDVR
      (A := Stacks.KummerExtension.A1 K π q) (K := Stacks.KummerExtension.K1 K π q)
      (Khat := IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) (M := M)
  trivial

end

/-- **`(p : R) = 0` for a prime `p` in a nontrivial ring pins the characteristic.**

The companion to `IsDiscreteValuationRing.charZero_of_ne_zero_of_charP_residueField`: that one
reads off characteristic zero from `(p : A) ≠ 0`, this one reads off characteristic `p` from
`(p : A) = 0`. Both halves of the split are needed — the second because the Kummer branch's
uniqueness-of-roots step is only available in characteristic `p`. -/
@[ega "0 21.1.2" "partial"]
theorem charP_of_cast_eq_zero (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ)
    [hp : Fact p.Prime] (hpR : (p : R) = 0) : CharP R p := by
  have hdvd : ringChar R ∣ p := ringChar.dvd hpR
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hpe
  · exfalso
    have h : ((1 : ℕ) : R) = 0 :=
      (CharP.cast_eq_zero_iff R (ringChar R) 1).mpr (by rw [h1])
    simp at h
  · exact hpe ▸ ringChar.charP R

-- The three branches, the Kummer tower and the bijectivity count are one proof, and the types
-- involved (`FractionRing (AdicCompletion …)`, `AdjoinRoot (kummerPoly …)`, an `IntermediateField`
-- of an `AlgebraicClosure`) are deeply nested, so elaboration runs past the default budget.
set_option maxHeartbeats 1600000 in
-- The conjugate factors of the completed tensor product carry a large instance graph.
/-- **Tag 09EJ without separability, over a perfect residue field.**

Let `A` be a discrete valuation ring with fraction field `K` and **perfect** residue field of
characteristic `p`, with no completeness assumed. Then every finite extension `M / K^` of the
fraction field of the completion is a base change of a finite extension `K₁ / K`:

`K^ ⊗_K K₁ ≅ M`.

Tag 09EJ is this statement with `M / K^` assumed **separable**, and separability is free only in
mixed characteristic. This is the wild case, and it is the whole mathematical content of the third
paragraph of Tag 09F9's proof — note that `B`, `L` and the weak-solution package appear nowhere:
the descent is a separate, already-proved step
(`isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv`), applied to this.

## The three branches

The split is on `(p : A)` and then on the `n` that condition (b) returns — **never** on the
characteristic read off condition (b), which a consumer cannot do.

* `(p : A) ≠ 0`: then `A`, hence `K`, hence `K^` has characteristic zero, so `M / K^` is separable
  and Tag 09EJ applies unchanged. Condition (b) is never invoked.
* `(p : A) = 0` and `n = 0`: condition (b)'s root `ρ` lies in `K^`, so again `M / K^` is separable,
  by `Algebra.isSeparable_of_adjoin_pow_one`.
* `(p : A) = 0` and `n ≥ 1`: the Kummer route. `K_n = K(π^{1/p^n})` with ring of integers `A_n`
  (a discrete valuation ring by Tag 09EV (3), needing no completeness);
  `K^⟮ρ⟯` is a fraction field of `(A_n)^∧`
  (`exists_algebra_isFractionRing_adjoin`, built on the identification of that completion); Tag
  09EJ **over `A_n`** then yields a finite separable `L / K_n` with `K^⟮ρ⟯ ⊗_{K_n} L ≅ M`.

## Why the last branch ends in a bijectivity rather than a chain of equivalences

The obvious finish — transport 09EJ's equivalence through a base-change cancellation — does not
work: the cancellation needs `Algebra K_n (K^ ⊗_K K_n)` to be
`Algebra.TensorProduct.rightAlgebra`, while 09EJ's conclusion uses its own statement-level `letI`,
and reconciling them needs the Kummer identification evaluated on the root. Instead the map

`Θ : K^ ⊗_K L →ₐ[K^] M`,  `Θ = Algebra.TensorProduct.lift (algebraMap K^ M) j`

is written down directly, where `j : L →ₐ[K] M` is `ψ ∘ includeRight` — its `K`-linearity is the
one place the identification's canonicity is spent, through the third conjunct of
`exists_algebra_isFractionRing_adjoin` — and then shown bijective:

* **surjective**, because `ρ` is forced into the range: `j` carries the Kummer root to an element
  with the same `p^n`-th power as `ρ`, and **in characteristic `p` a `p^n`-th root is unique**.
  That puts `K^⟮ρ⟯` in the range, and `ψ` surjective finishes.
* **injective**, from surjectivity and `finrank K^ (K^ ⊗_K L) = finrank K L = finrank K^ M`, the
  two sides both being `p^n · [L : K_n]`.

The conclusion carries `letI := algebraAdicCompletionFractionField A K`, and that placement is
load-bearing: `K^ ⊗[K] K₁` cannot be formed from a `let`-introduced `Algebra K K^` inside a tactic
block, only from one fixed in a statement. -/
theorem exists_finite_extension_nonempty_tensorProduct_algEquiv_of_conditionB
    (A : Type uA) (K : Type uK) (M : Type uA)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    [Field M] [Algebra (AdicCompletionFractionField A) M]
    [Module.Finite (AdicCompletionFractionField A) M]
    (π : A) (hπ : Irreducible π)
    (hcond : (p : A) = 0 → ∃ (n : ℕ) (ρ : M),
      ρ ^ p ^ n = algebraMap (AdicCompletionFractionField A) M
          (algebraMap A (AdicCompletionFractionField A) π) ∧
        minpoly (AdicCompletionFractionField A) ρ =
          Polynomial.X ^ p ^ n -
            Polynomial.C (algebraMap A (AdicCompletionFractionField A) π) ∧
        Algebra.IsSeparable
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      let := algebraAdicCompletionFractionField A K
      Nonempty ((AdicCompletionFractionField A ⊗[K] K₁)
        ≃ₐ[AdicCompletionFractionField A] M) := by
  classical
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  let : Algebra K M := ((algebraMap (AdicCompletionFractionField A) M).comp
    (algebraMap K (AdicCompletionFractionField A))).toAlgebra
  let : IsScalarTower K (AdicCompletionFractionField A) M :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- The separable route, used by two of the three branches.
  have hsepRoute : Algebra.IsSeparable (AdicCompletionFractionField A) M →
      ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
        (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
        Nonempty ((AdicCompletionFractionField A ⊗[K] K₁)
          ≃ₐ[AdicCompletionFractionField A] M) := by
    intro hsep
    let := hsep
    obtain ⟨F, hFfin, -, ⟨e⟩⟩ :=
      exists_finite_separable_extension_tensorProduct_equiv_of_isDVR
        (A := A) (K := K) (Khat := AdicCompletionFractionField A) (M := M)
    let : Algebra A F := ((algebraMap K F).comp (algebraMap A K)).toAlgebra
    let : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' rfl
    exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hFfin, ⟨e⟩⟩
  by_cases hpA : (p : A) = 0
  · -- Equal characteristic `p`: condition (b) applies at `A^`.
    obtain ⟨n, ρ, hρpow, hρmin, hρsep⟩ := hcond hpA
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · -- `n = 0`: `ρ` lies in the base, so `M / K^` is separable after all.
      subst hn0
      exact hsepRoute (Algebra.isSeparable_of_adjoin_pow_one (by simpa using hρpow) hρsep)
    · -- `n ≥ 1`: the Kummer route.
      have hq2 : 2 ≤ p ^ n := by
        calc 2 ≤ p := (Fact.out : p.Prime).two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hn1
      have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π (p ^ n))) :=
        ⟨Stacks.KummerExtension.kummerPoly_irreducible K π (p ^ n) (by omega) hπ⟩
      have : IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π (p ^ n)) :=
        Stacks.KummerExtension.isDiscreteValuationRing_A1 K π (p ^ n) hq2 hπ
      have := Stacks.KummerExtension.isFractionRing_A1 K π (p ^ n)
      obtain ⟨alg, hfr, hcompat⟩ :=
        Stacks.EppTheorem.exists_algebra_isFractionRing_adjoin K π (p ^ n) hq2 hπ ρ hρmin
      let := alg
      let := hfr
      let := hρsep
      have : FiniteDimensional
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M :=
        Module.Finite.of_restrictScalars_finite (AdicCompletionFractionField A) _ M
      -- The two instances Tag 09EJ introduces in its own conclusion, re-introduced by the same
      -- terms so that its `ψ` and our `algebraMap` agree.
      let algAnF : Algebra (Stacks.KummerExtension.A1 K π (p ^ n))
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) :=
        ((algebraMap (AdicCompletion (maximalIdeal (Stacks.KummerExtension.A1 K π (p ^ n)))
          (Stacks.KummerExtension.A1 K π (p ^ n)))
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})).comp
          (algebraMap (Stacks.KummerExtension.A1 K π (p ^ n))
            (AdicCompletion (maximalIdeal (Stacks.KummerExtension.A1 K π (p ^ n)))
              (Stacks.KummerExtension.A1 K π (p ^ n))))).toAlgebra
      have hinjAnF : Function.Injective (algebraMap (Stacks.KummerExtension.A1 K π (p ^ n))
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})) :=
        (IsFractionRing.injective
          (AdicCompletion (maximalIdeal (Stacks.KummerExtension.A1 K π (p ^ n)))
            (Stacks.KummerExtension.A1 K π (p ^ n)))
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})).comp
          (AdicCompletion.of_injective (maximalIdeal (Stacks.KummerExtension.A1 K π (p ^ n)))
            (Stacks.KummerExtension.A1 K π (p ^ n)))
      let algKnF : Algebra (Stacks.KummerExtension.K1 K π (p ^ n))
          (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) :=
        (IsFractionRing.lift (A := Stacks.KummerExtension.A1 K π (p ^ n))
          (K := Stacks.KummerExtension.K1 K π (p ^ n))
          (L := IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
          (g := algebraMap (Stacks.KummerExtension.A1 K π (p ^ n))
            (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}))
          hinjAnF).toAlgebra
      obtain ⟨L, hLfin, hLsep, ⟨ψ⟩⟩ :=
        exists_finite_separable_extension_tensorProduct_equiv_of_isDVR
          (A := Stacks.KummerExtension.A1 K π (p ^ n)) (K := Stacks.KummerExtension.K1 K π (p ^ n))
          (Khat := IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) (M := M)
      let := hLfin
      -- Step 1: the tower `K → K_n → K^⟮ρ⟯ → M` agrees with `K → K^ → M`.
      have htower : ∀ y : K,
          algebraMap (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M
            (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
              (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
              (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)) y))
          = algebraMap K M y := by
        intro y
        have key : ((algebraMap (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
              M).comp ((algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
              (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})).comp
                (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)))))
            = algebraMap K M := by
          refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => ?_)
          simp only [RingHom.coe_comp, Function.comp_apply]
          have hlift : ∀ z : Stacks.KummerExtension.A1 K π (p ^ n),
              algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
                (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                (algebraMap (Stacks.KummerExtension.A1 K π (p ^ n)) (Stacks.KummerExtension.K1 K π
                  (p ^ n)) z)
              = algebraMap (Stacks.KummerExtension.A1 K π (p ^ n))
                (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) z :=
            fun z => IsFractionRing.lift_algebraMap hinjAnF z
          rw [← IsScalarTower.algebraMap_apply A K (Stacks.KummerExtension.K1 K π (p ^ n)),
            IsScalarTower.algebraMap_apply A (Stacks.KummerExtension.A1 K π (p ^ n))
              (Stacks.KummerExtension.K1 K π (p ^ n)), hlift]
          change algebraMap _ M (algebraMap
            (AdicCompletion (maximalIdeal (Stacks.KummerExtension.A1 K π (p ^ n)))
              (Stacks.KummerExtension.A1 K π (p ^ n)))
            (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
            (algebraMap A _ a)) = _
          rw [hcompat, ← IsScalarTower.algebraMap_apply (AdicCompletionFractionField A)
              (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M,
            IsScalarTower.algebraMap_apply K (AdicCompletionFractionField A) M,
            ← IsScalarTower.algebraMap_apply A K (AdicCompletionFractionField A)]
        exact congrArg (fun f => f y) key
      -- Step 2: `L → M` as a `K`-algebra map.
      let j : L →ₐ[K] M :=
        { toRingHom := ψ.toRingEquiv.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := Stacks.KummerExtension.K1 K π (p ^ n))
              (A := IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
              (B := L)).toRingHom
          commutes' := fun y => by
            change ψ (1 ⊗ₜ algebraMap K L y) = algebraMap K M y
            have h1 : (1 : IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                  ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] (algebraMap K L y)
                = (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
                    (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                    (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)) y))
                      ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] (1 : L) := by
              rw [show algebraMap K L y = algebraMap (Stacks.KummerExtension.K1 K π (p ^ n)) L
                  (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)) y) from rfl,
                Algebra.algebraMap_eq_smul_one (R := Stacks.KummerExtension.K1 K π (p ^ n)) (A :=
                  L),
                Algebra.algebraMap_eq_smul_one (R := Stacks.KummerExtension.K1 K π (p ^ n))
                  (A := IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}),
                TensorProduct.smul_tmul]
            rw [h1, show (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
                  (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                  (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)) y))
                    ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] (1 : L)
                = algebraMap (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) _
                  (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n))
                    (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                    (algebraMap K (Stacks.KummerExtension.K1 K π (p ^ n)) y)) from rfl,
              AlgEquiv.commutes, htower] }
      -- `L / K` is finite, through `K_n`.
      have : Module.Finite K L :=
        Module.Finite.trans (Stacks.KummerExtension.K1 K π (p ^ n)) L
      let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
      -- The candidate map, and characteristic `p` carried down to `M`.
      set Θ := Algebra.TensorProduct.lift
        (Algebra.ofId (AdicCompletionFractionField A) M) j
        (fun _ _ => Commute.all _ _) with hΘdef
      have hCA : CharP A p := charP_of_cast_eq_zero A p hpA
      have hCK : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective A K) p
      have hCM : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
      -- `j` carries the Kummer root to `ρ`: both have `p ^ n`-th power the image of `π`, and in
      -- characteristic `p` a `p ^ n`-th root is unique.
      have hjroot : j (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n)) L
          (Stacks.KummerExtension.piRoot K π (p ^ n))) = ρ := by
        have hL : (j (algebraMap (Stacks.KummerExtension.K1 K π (p ^ n)) L
            (Stacks.KummerExtension.piRoot K π (p ^ n)))) ^ p ^ n
            = algebraMap (AdicCompletionFractionField A) M
              (algebraMap A (AdicCompletionFractionField A) π) := by
          rw [← map_pow, ← map_pow, Stacks.KummerExtension.piRoot_pow,
            IsScalarTower.algebraMap_apply A K (Stacks.KummerExtension.K1 K π (p ^ n)),
            ← IsScalarTower.algebraMap_apply K (Stacks.KummerExtension.K1 K π (p ^ n)) L,
            AlgHom.commutes, IsScalarTower.algebraMap_apply K (AdicCompletionFractionField A) M,
            ← IsScalarTower.algebraMap_apply A K (AdicCompletionFractionField A)]
        have hR : ρ ^ p ^ n
            = algebraMap (AdicCompletionFractionField A) M
              (algebraMap A (AdicCompletionFractionField A) π) := hρpow
        have hq0 : p ^ n ≠ 0 := (Nat.pow_pos (Fact.out : p.Prime).pos).ne'
        exact eq_of_sub_eq_zero ((pow_eq_zero_iff hq0).mp
          (by rw [sub_pow_char_pow, hL, hR, sub_self]))
      -- Hence `K^⟮ρ⟯` lands in the range.
      have hρmem : ρ ∈ Θ.range :=
        ⟨1 ⊗ₜ algebraMap (Stacks.KummerExtension.K1 K π (p ^ n)) L (Stacks.KummerExtension.piRoot K
          π (p ^ n)), by
          simp [hΘdef, Algebra.TensorProduct.lift_tmul, hjroot]⟩
      have hFmem : ∀ z : IntermediateField.adjoin (AdicCompletionFractionField A) {ρ},
          (z : M) ∈ Θ.range := by
        have hsub : (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}).toSubalgebra
            ≤ Θ.range := by
          rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
            (F := AdicCompletionFractionField A) (S := {ρ})
            (fun x hx => by
              rw [Set.mem_singleton_iff] at hx
              exact hx ▸ (IsIntegral.of_finite (AdicCompletionFractionField A) ρ).isAlgebraic)]
          exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hρmem)
        exact fun z => hsub z.2
      -- Surjectivity: `ψ` is onto and every `ψ (z ⊗ₜ y)` is `↑z * j y`.
      have hmem : ∀ m : M, m ∈ Θ.range := by
        intro m
        obtain ⟨t, rfl⟩ := ψ.surjective m
        induction t using TensorProduct.inductionOn with
        | tmul z y =>
          have hmul : ψ (z ⊗ₜ y) = (z : M) * j y := by
            rw [show z ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] y
                = (z ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] (1 : L))
                  * ((1 : IntermediateField.adjoin (AdicCompletionFractionField A) {ρ})
                    ⊗ₜ[Stacks.KummerExtension.K1 K π (p ^ n)] y) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul]
            congr 1
            exact AlgEquiv.commutes ψ z
          rw [hmul]
          exact mul_mem (hFmem z) ⟨1 ⊗ₜ y, by
            simp [hΘdef, Algebra.TensorProduct.lift_tmul]⟩
        | add x y hx hy =>
          rw [show ψ (x + y) = ψ x + ψ y from map_add ψ.toRingEquiv x y]; exact add_mem hx hy
      have hsurj : Function.Surjective Θ := by
        intro m
        obtain ⟨x, hx⟩ := hmem m
        exact ⟨x, hx⟩
      -- Injectivity, from surjectivity and equal `K^`-dimension.
      have hfinT : FiniteDimensional (AdicCompletionFractionField A)
          (AdicCompletionFractionField A ⊗[K] L) := Module.Finite.base_change K _ L
      have hdim : Module.finrank (AdicCompletionFractionField A)
            (AdicCompletionFractionField A ⊗[K] L)
          = Module.finrank (AdicCompletionFractionField A) M := by
        rw [Module.finrank_baseChange]
        have h1 : Module.finrank K (Stacks.KummerExtension.K1 K π (p ^ n)) = p ^ n :=
          Stacks.KummerExtension.finrank_K1 K π (p ^ n) hq2 hπ
        have h2 : Module.finrank (AdicCompletionFractionField A)
            (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) = p ^ n := by
          rw [IntermediateField.adjoin.finrank
            (IsIntegral.of_finite (AdicCompletionFractionField A) ρ), hρmin,
            Polynomial.natDegree_X_pow_sub_C]
        have h3 : Module.finrank (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M
            = Module.finrank (Stacks.KummerExtension.K1 K π (p ^ n)) L := by
          rw [← ψ.toLinearEquiv.finrank_eq]
          exact Module.finrank_baseChange
        rw [← Module.finrank_mul_finrank K (Stacks.KummerExtension.K1 K π (p ^ n)) L,
          ← Module.finrank_mul_finrank (AdicCompletionFractionField A)
            (IntermediateField.adjoin (AdicCompletionFractionField A) {ρ}) M, h1, h2, h3]
      have hinj : Function.Injective Θ :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
          (f := Θ.toLinearMap)).mpr hsurj
      exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        ⟨AlgEquiv.ofBijective Θ ⟨hinj, hsurj⟩⟩⟩
  · -- Residue characteristic `p` but `(p : A) ≠ 0`: characteristic zero, hence separable.
    have hCZA : CharZero A := charZero_of_ne_zero_of_charP_residueField A p hpA
    let := hCZA
    let := charZero_adicCompletionFractionField A
    exact hsepRoute inferInstance

/-- The completion descent package when the residue field is perfect.  Perfectness is used only
to produce condition (b); the Kummer descent itself is the preceding theorem. -/
theorem exists_finite_extension_nonempty_tensorProduct_algEquiv_of_perfectField
    (A : Type uA) (K : Type uK) (M : Type uA)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [PerfectField (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    [Field M] [Algebra (AdicCompletionFractionField A) M]
    [Module.Finite (AdicCompletionFractionField A) M] :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      let := algebraAdicCompletionFractionField A K
      Nonempty ((AdicCompletionFractionField A ⊗[K] K₁)
        ≃ₐ[AdicCompletionFractionField A] M) := by
  obtain ⟨π, hπprime⟩ := exists_prime A
  have hπ : Irreducible π := hπprime.irreducible
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  apply exists_finite_extension_nonempty_tensorProduct_algEquiv_of_conditionB
    A K M p π hπ
  intro hpA
  have hπh : Irreducible (algebraMap A (AdicCompletion (maximalIdeal A) A) π) :=
    irreducible_algebraMap_adicCompletion A hπ
  let := perfectField_residueField_adicCompletion A
  let := charP_residueField_adicCompletion A p
  obtain ⟨n, ρ, hρpow, hρmin, hρsep⟩ := Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin
    (A := AdicCompletion (maximalIdeal A) A)
    (K := AdicCompletionFractionField A) (M := M) p
    (algebraMap A (AdicCompletion (maximalIdeal A) A) π) hπh
  simp only [← IsScalarTower.algebraMap_apply A
    (AdicCompletion (maximalIdeal A) A) (AdicCompletionFractionField A)] at hρpow hρmin
  exact ⟨n, ρ, hρpow, hρmin, hρsep⟩

/-- **Step 3 of Tag 09F9 in the wild case: B1a.**

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, **with no
completeness assumed**, and let the residue field of `A` be **perfect** of characteristic `p`. If
there is a finite extension `M / K^` of the fraction field of `A^` which is a weak solution for
`A^ → B^`, then there is a finite `K₁ / K` which is a weak solution for `A → B`.

This is the tame theorem
`exists_finite_extension_isWeakSolution_of_isSeparable_adicCompletion` with its separability
hypothesis on `M / K^` **removed**, at the cost of assuming the residue field perfect — which is
the hypothesis the perfect-residue complete case already carries, so nothing upstream is
strengthened to
supply it. Perfectness is what discharges condition (b) of the published proof, and condition (b)
is what replaces separability.

Two lines of proof, because the content is elsewhere:
`exists_finite_extension_nonempty_tensorProduct_algEquiv_of_perfectField` produces `K₁` with
`K^ ⊗_K K₁ ≅ M`, and `isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv` — the
descent, which is Tag 09ES (2) then (1) over the completion square, and into which all use of
completeness is isolated — turns that into the weak solution downstairs.

Unlike the tame statement this does **not** conclude `Algebra.IsSeparable K K₁`, and cannot: in the
wild case `K₁` sits over the purely inseparable `K(π^{1/p^n})`. Tag 09F9 asks only for a weak
solution, so nothing needs it. -/
theorem exists_finite_extension_isWeakSolution_of_perfectResidue_adicCompletion
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [PerfectField (ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hup :
      letI := algebraAdicCompletion A B
      letI := isExtension_adicCompletionMap A B
      letI := algebraAdicCompletionFractionFieldMap A B
      letI := isScalarTower_adicCompletionFractionFieldMap A B
      ∃ (M : Type uA) (_ : Field M) (_ : Algebra (AdicCompletionFractionField A) M)
        (_ : Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) M)
        (_ : IsScalarTower (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletionFractionField A) M)
        (_ : Module.Finite (AdicCompletionFractionField A) M),
        ∃ D : IntegralClosureBaseChange.{uA, uB, uA, uB, uA, z₁, z₂, z₃}
          (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal B) B)
          (AdicCompletionFractionField A) (AdicCompletionFractionField B) M,
          D.IsWeakSolution) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK} A B K L K₁,
        D.IsWeakSolution := by
  let := algebraAdicCompletion A B
  let := isExtension_adicCompletionMap A B
  let := algebraAdicCompletionFractionFieldMap A B
  let := isScalarTower_adicCompletionFractionFieldMap A B
  let := algebraAdicCompletionFractionField A K
  let := isScalarTower_adicCompletionFractionField A K
  obtain ⟨M, hMfield, hMalgKc, hMalgAc, hMtower, hMfin, D_AcBc, hAcBc⟩ := hup
  let := hMfield
  let := hMalgKc
  let := hMalgAc
  let := hMtower
  let := hMfin
  obtain ⟨K₁, hK₁field, hK₁algK, hK₁algA, hK₁tower, hK₁fin, ⟨e⟩⟩ :=
    exists_finite_extension_nonempty_tensorProduct_algEquiv_of_perfectField A K M p
  let := hK₁field
  let := hK₁algK
  let := hK₁algA
  let := hK₁tower
  let := hK₁fin
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    canonicalBaseChange A B K L K₁,
    isWeakSolution_canonicalBaseChange_of_tensorProduct_algEquiv A B K L K₁ M
      ⟨D_AcBc, hAcBc⟩ e⟩

end Stacks.EppTheorem

end
