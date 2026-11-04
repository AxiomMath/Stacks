module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder

/-!
# Orders along a minimal prime of a quotient and along a height-one prime

In the proof of the key formula, Stacks 0EQV, the order of vanishing along a prime divisor `P`
of `Z_i` is computed on the chart `W' = W ×_X Z_i` at a point `y` over the generic point of `P`,
as a sum over the minimal primes `𝔭` of `O = 𝒪_{W', y}` of orders along `O/𝔭`
(`Ring.minimalPrimeOrd`), while the Key Lemma (Stacks 0EAX) for `A = 𝒪_{W, w}` uses orders along
`A/𝔮` for height-one primes `𝔮` of `A` (`Stacks.Chow.heightOneOrd`). The closed immersion
`W' → W` makes `A → O` surjective, and `𝔮 = 𝔭 ∩ A` gives `A/𝔮 ≅ O/𝔭`; this file transports the
order along this isomorphism.

## Main definitions

* `Ring.quotientComapEquiv`: `A/(φ⁻¹𝔭) ≃ O/𝔭` for a surjection `φ : A → O`.
* `Ring.minimalPrimeResidueFieldEquiv`: the induced `Frac(O/𝔭) ≃ κ(A_𝔮)`.

## Main results

* `Ring.minimalPrimeOrd_eq_heightOneOrd`: `ord_{O/𝔭}(F) = ord_{A/𝔮}(F)`, `F` read in `κ(A_𝔮)`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Ring

variable {A O : Type u} [CommRing A] [CommRing O] (φ : A →+* O) (hφ : Function.Surjective φ)
    (p : Ideal O) [p.IsPrime] (P : Ideal A) [P.IsPrime] (hP : P = p.comap φ)

/-- **`A/(φ⁻¹𝔭) ≃ O/𝔭` for a surjection `φ : A → O`.** -/
def quotientComapEquiv : A ⧸ P ≃+* O ⧸ p :=
  RingEquiv.ofBijective (Ideal.quotientMap p φ hP.le)
    ⟨Ideal.quotientMap_injective' hP.ge, Ideal.quotientMap_surjective hφ⟩

omit [p.IsPrime] [P.IsPrime] in
/-- The isomorphism `A/(φ⁻¹𝔭) ≃ O/𝔭` on classes. -/
theorem quotientComapEquiv_mk (a : A) :
    quotientComapEquiv φ hφ p P hP (Ideal.Quotient.mk P a) = Ideal.Quotient.mk p (φ a) :=
  Ideal.quotientMap_mk (I := p) (f := φ) (H := hP.le)

/-- **The identification `Frac(O/𝔭) ≃ κ(A_𝔮)`**, `𝔮 = φ⁻¹𝔭`, induced by `A/𝔮 ≃ O/𝔭`, `κ(A_𝔮)`
being a fraction field of `A/𝔮`. -/
def minimalPrimeResidueFieldEquiv :
    FractionRing (O ⧸ p) ≃+* ResidueField (Localization.AtPrime P) :=
  IsFractionRing.ringEquivOfRingEquiv (A := O ⧸ p) (K := FractionRing (O ⧸ p)) (B := A ⧸ P)
    (L := P.ResidueField) (quotientComapEquiv φ hφ p P hP).symm

omit [p.IsPrime] in
/-- The identification `Frac(O/𝔭) ≃ κ(A_𝔮)` on the class of `φ a` is the residue of `a`. -/
theorem minimalPrimeResidueFieldEquiv_algebraMap_mk (a : A) :
    minimalPrimeResidueFieldEquiv φ hφ p P hP
        (algebraMap (O ⧸ p) (FractionRing (O ⧸ p)) (Ideal.Quotient.mk p (φ a))) =
      residue (Localization.AtPrime P) (algebraMap A (Localization.AtPrime P) a) := by
  rw [minimalPrimeResidueFieldEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    ← quotientComapEquiv_mk φ hφ p P hP a, RingEquiv.symm_apply_apply]
  exact Ideal.algebraMap_quotient_residueField_mk P a

variable [IsNoetherianRing A] [IsNoetherianRing O] [Ring.KrullDimLE 1 O]
    {K : Type*} [CommRing K] [Algebra O K] [IsFractionRing O K]

/-- **The order along a minimal prime of `O` is the order along the height-one prime below it.**
For a surjection `φ : A → O` from a two-dimensional Noetherian ring, a minimal prime `𝔭` of `O`
with `𝔮 = φ⁻¹𝔭` of height one, and a unit `F` of the total ring of fractions of `O`,
`ord_{O/𝔭}(F) = ord_{A/𝔮}(F)`, where on the right `F` is read in `Frac(O/𝔭) ≃ κ(A_𝔮)`. -/
theorem minimalPrimeOrd_eq_heightOneOrd (hdim : ringKrullDim A = 2) (p : minimalPrimes O)
    (P : Stacks.Chow.HeightOnePrime A) (hP : P.1.asIdeal = (p : Ideal O).comap φ) (F : K)
    (hF : IsUnit F) :
    haveI : (p : Ideal O).IsPrime := p.2.1.1
    minimalPrimeOrd p F hF =
      Stacks.Chow.heightOneOrd hdim P
        (hF.map ((minimalPrimeResidueFieldEquiv φ hφ (p : Ideal O) P.1.asIdeal hP).toRingHom.comp
          (minimalPrimeFractionMap (K := K) p))).unit := by
  have : (p : Ideal O).IsPrime := p.2.1.1
  have := krullDimLE_one_quotient (O := O) (p : Ideal O)
  have := Stacks.Chow.krullDimLE_quotient_of_height_eq_one hdim P.1.asIdeal P.2
  set E := minimalPrimeResidueFieldEquiv φ hφ (p : Ideal O) P.1.asIdeal hP
  have hne : minimalPrimeFractionMap (K := K) p F ≠ 0 := (hF.map _).ne_zero
  have hEne : E (minimalPrimeFractionMap (K := K) p F) ≠ 0 := (hF.map (E.toRingHom.comp _)).ne_zero
  have h := Stacks.Chow.ordInt_congr (quotientComapEquiv φ hφ (p : Ideal O) P.1.asIdeal hP).symm E
    (fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ r) _ hne hEne
  refine (Eq.trans ?_ h).symm
  rfl

end Ring

end
