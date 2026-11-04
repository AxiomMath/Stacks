module

public import StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange
public import StacksFrontier.RingTheory.BaseChangeTransport
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer

/-!
# The completion of the ring of integers of a Kummer extension

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, let `n ≥ 2`, let
`K_n = K(π^{1/n})` be the Kummer extension of Tag 09EV and let `A_n` be the integral closure of `A`
in it. This file identifies the completion of `A_n`:

`(A_n)^∧ ≅ A_n'`, where `A_n'` is *the same Kummer construction performed over the completion* —
the integral closure of `A^∧` in `K^∧(π^{1/n})`.

That is the content Tag 09F9's third paragraph needs and it is the one step of that paragraph with
no citation in the Stacks text, which simply says the two agree. Formally it is a chain of five
isomorphisms, and the point of collecting it here is that the chain is *canonical on `A_n`*, which
is the only thing a consumer ever needs to know about it: see
`nonempty_ringEquiv_adicCompletion_A1_apply_algebraMap` below.

## The chain

1. `(A_n)^∧ ≅ A_n ⊗[A] A^∧` — completion commutes with finite base change over a local ring,
   `AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing`. Its three hypotheses are free
   here: `A_n` is local because it is a discrete valuation ring (Tag 09EV (3), and note this needs
   no completeness), it is module-finite over `A` through the power basis of `A[x]/(x^n - π)`, and
   its structure map is local by `isLocalHom_algebraMap_of_isIntegral`.
2. `A_n ⊗[A] A^∧ ≅ A^∧ ⊗[A] A_n` — commutativity.
3. `A^∧ ⊗[A] A_n ≅ A^∧ ⊗[A] A[x]/(x^n - π)` — Tag 09EV (2'),
  `Stacks.KummerExtension.canonAlgEquiv`, tensored.
4. `A^∧ ⊗[A] A[x]/(x^n - π) ≅ A^∧[x]/(x^n - π)` — adjoining a root commutes with base change,
   `AdjoinRoot.baseChangeAlgEquiv`, together with the computation that `x^n - π` maps to
`x^n - π̂`. 5. `A^∧[x]/(x^n - π̂) ≅ A_n'` — Tag 09EV (2') again, now over `A^∧`.

Only the first link is inexplicit (it comes from a `Nonempty`, ultimately from Tag 07N9), and that
is harmless: it is an `A_n`-algebra equivalence, so its value on the image of `A_n` is forced, and
that is exactly the information the chain is used through.

## Main results

* `Stacks.KummerExtension.finite_A1`, `Stacks.KummerExtension.isFractionRing_A1`,
  `Stacks.KummerExtension.isIntegral_A1`: three facts
  about `A_n` that Tag 09EV establishes only inside the proof of `isTotallyRamified_K1` and that
  are wanted standalone.
* `Stacks.KummerExtension.nonempty_ringEquiv_adicCompletion_A1`: the identification above.
* `Stacks.KummerExtension.isFractionRing_adicCompletion_A1`: consequently `K^∧(π^{1/n})` is a
  fraction field of
  `(A_n)^∧`. This is the form Tag 09EJ consumes, since 09EJ asks for a fraction field of the
  completion of its base.

## References

* [The Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open scoped TensorProduct

open Polynomial

namespace Stacks.KummerExtension

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (π : A) (n : ℕ)

/-- **`A_n` is integral over `A`**, being an integral closure. -/
instance isIntegral_A1 : Algebra.IsIntegral A (A1 K π n) :=
  ⟨fun x => integralClosure.isIntegral x⟩

/-- **`A_n` is module-finite over `A`.**

Tag 09EV (2') makes `A_n` isomorphic to `A[x]/(x^n - π)`, which is free of rank `n` over `A` on the
power basis; `Module.Finite` transports across the isomorphism. This appears inside the proof of
`Stacks.KummerExtension.isTotallyRamified_K1`; it is stated here because the completion argument
  needs it as a
hypothesis of its own. -/
theorem finite_A1 (hn : 2 ≤ n) (hπ : Irreducible π) : Module.Finite A (A1 K π n) :=
  have : Module.Finite A (A' π n) := PowerBasis.finite (powerBasisA' π n (by omega))
  Module.Finite.equiv (canonAlgEquiv K π n hn hπ).toLinearEquiv

omit [IsDiscreteValuationRing A] in
/-- **`K_n` is a fraction field of `A_n`**, the integral closure being taken in a finite
extension. Also inside the proof of `Stacks.KummerExtension.isTotallyRamified_K1`. -/
theorem isFractionRing_A1 [Fact (Irreducible (kummerPoly K π n))] :
    IsFractionRing (A1 K π n) (K1 K π n) :=
  integralClosure.isFractionRing_of_finite_extension K (K1 K π n)

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The Kummer polynomial over the completion is the base change of the Kummer polynomial over the
base: `(x^n - π).map (A → A^∧) = x^n - π̂`. -/
theorem map_kummerPolyA {Ah : Type*} [CommRing Ah] [Algebra A Ah] :
    (kummerPolyA π n).map (algebraMap A Ah) = kummerPolyA (algebraMap A Ah π) n := by
  simp [kummerPolyA, Polynomial.map_sub, Polynomial.map_pow]

end Stacks.KummerExtension

namespace Stacks.KummerExtension

open IsLocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- **The completion of `A_n` is the Kummer construction over the completion.**

`(A_n)^∧ ≅ A_n'`, where on the right `A_n'` is the integral closure of `A^∧` in
`K^∧(π̂^{1/n})` — the same construction over the completed base. See the module docstring for the
five links of the chain.

The equivalence is returned as a `RingEquiv` inside an `∃`, rather than as a definition, because
its first link is Tag 07N9, which is itself a `Nonempty` of an `A_n`-algebra equivalence: there is
no canonical *term* to hand back. What a consumer needs instead is carried along in the `∃`, namely
that the equivalence is **`A`-linear**. That is enough, and it is what makes the identification
usable: every link is a morphism of `A`-algebras (the first because it is even `A_n`-linear), so
the composite commutes with the structure maps out of `A`, and a consumer comparing two maps out of
`K_n` can compare them on `K` this way. -/
theorem exists_ringEquiv_adicCompletion_A1
    [IsDomain (AdicCompletion (maximalIdeal A) A)]
    [IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A)]
    (Kh : Type*) [Field Kh]
    [Algebra (AdicCompletion (maximalIdeal A) A) Kh]
    [IsFractionRing (AdicCompletion (maximalIdeal A) A) Kh]
    (π : A) (n : ℕ) [Fact (Irreducible (kummerPoly K π n))] [IsLocalRing (A1 K π n)]
    (hn : 2 ≤ n) (hπ : Irreducible π)
    (hπh : Irreducible (algebraMap A (AdicCompletion (maximalIdeal A) A) π)) :
    ∃ e : AdicCompletion (maximalIdeal (A1 K π n)) (A1 K π n) ≃+*
        A1 Kh (algebraMap A (AdicCompletion (maximalIdeal A) A) π) n,
      ∀ x : A, e (algebraMap A _ x) =
        algebraMap (AdicCompletion (maximalIdeal A) A) _
          (algebraMap A (AdicCompletion (maximalIdeal A) A) x) := by
  have hfin1 : Module.Finite A (A1 K π n) := finite_A1 K π n hn hπ
  let _ := hfin1
  let _ : IsLocalHom (algebraMap A (A1 K π n)) := isLocalHom_algebraMap_of_isIntegral
  have hassoc : Associated
      ((kummerPolyA π n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
      (kummerPolyA (algebraMap A (AdicCompletion (maximalIdeal A) A) π) n) := by
    rw [map_kummerPolyA]
  obtain ⟨e1⟩ := AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing A (A1 K π n)
  let e2 := Algebra.TensorProduct.comm A (A1 K π n) (AdicCompletion (maximalIdeal A) A)
  let e3 := Algebra.TensorProduct.congr
    (AlgEquiv.refl : AdicCompletion (maximalIdeal A) A ≃ₐ[A] AdicCompletion (maximalIdeal A) A)
    (canonAlgEquiv K π n hn hπ).symm
  let e4 := AdjoinRoot.baseChangeAlgEquiv A (AdicCompletion (maximalIdeal A) A) (kummerPolyA π n)
  let e4' := AdjoinRoot.algEquivOfAssociated (AdicCompletion (maximalIdeal A) A) _ _ hassoc
  let e5 := canonAlgEquiv Kh (algebraMap A (AdicCompletion (maximalIdeal A) A) π) n hn hπh
  refine ⟨e1.symm.toRingEquiv.trans (e2.toRingEquiv.trans (e3.toRingEquiv.trans
    (e4.toRingEquiv.trans (e4'.toRingEquiv.trans e5.toRingEquiv)))), fun x => ?_⟩
  have h1 : e1.symm (algebraMap A _ x) = algebraMap A (A1 K π n ⊗[A]
      AdicCompletion (maximalIdeal A) A) x := by
    rw [show (algebraMap A (AdicCompletion (maximalIdeal (A1 K π n)) (A1 K π n))) x
      = algebraMap (A1 K π n) _ (algebraMap A (A1 K π n) x) from rfl, AlgEquiv.commutes]
    rfl
  simp only [RingEquiv.coe_trans, Function.comp_apply, AlgEquiv.coe_ringEquiv, h1]
  rw [show (algebraMap A (A1 K π n ⊗[A] AdicCompletion (maximalIdeal A) A)) x
    = algebraMap A _ x from rfl, AlgEquiv.commutes, AlgEquiv.commutes]
  rw [show (algebraMap A (AdicCompletion (maximalIdeal A) A ⊗[A] A' π n)) x
    = algebraMap (AdicCompletion (maximalIdeal A) A) _
        (algebraMap A (AdicCompletion (maximalIdeal A) A) x) from rfl,
    AlgEquiv.commutes, AlgEquiv.commutes, AlgEquiv.commutes]

end Stacks.KummerExtension

end
