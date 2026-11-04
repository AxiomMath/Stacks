module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.EtaleLocalRingHub
public import StacksFrontier.RingTheory.Henselian.HenselizationBranchLocalization
public import StacksFrontier.RingTheory.Length.HenselizationBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplicity of a prime divisor over a prime divisor in henselian and étale local rings

Let `f : X ⟶ Y` be a morphism of decent algebraic spaces, let `Z ⊆ X` and `Z' ⊆ Y` be prime
divisors with generic points `ξ` and `ξ'`, and let `x̄` and `ȳ` be geometric points above them.
The multiplicity of `Z` over `Z'` is the colength of an extended maximal ideal, and it can be read
either in the henselian local rings `𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` or in the étale local rings
`𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}`. This file proves that the two readings give the same number.

## Main results

* `Ring.length_quotient_map_eq_of_flatHom_of_map_maximalIdeal_eq`: the colength of an ideal is
  unchanged along a flat local homomorphism which extends the maximal ideal to the maximal
  ideal.
* `Ring.length_quotient_extendedMaximalIdeal_eq_of_square`: in a commuting square of ring
  homomorphisms whose verticals extend the maximal ideal to the maximal ideal, the one on the
  right being moreover flat and local, the colength of the extended maximal ideal computed in the
  lower row is the one computed in the upper row.
* `Ring.length_localizationAtPrime_eq_of_isHenselization`: the localization of a henselization
  at a minimal prime has, over itself, the length that the localization of the base at the prime
  below has over itself.
* `AlgebraicGeometry.Space.PrimeDivisor.length_etaleLocalRing_eq_length_genericHenselianLocalRing`:
  the length of `𝒪_{X, x̄}` over itself is the length of `𝒪^h_{X, ξ}` over itself.
* `AlgebraicGeometry.Space.PrimeDivisor.length_quotient_map_eq_primeDivisorFlatMultiplicity`:
  the colength of the maximal ideal of `𝒪_{Y, ȳ}` extended to `𝒪_{X, x̄}` is
  `AlgebraicGeometry.Space.primeDivisorFlatMultiplicity` along a homomorphism of henselian local
  rings compatible with the maps `𝒪^h ⟶ 𝒪` of Stacks 0EMZ.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

namespace Ring

/-- If `ψ : B ⟶ B'` is flat and local and extends the maximal ideal of `B` to the maximal ideal
of `B'`, then for every ideal `J` of `B` the colength of `J B'` in `B'` is the colength of `J` in
`B`. -/
@[ega "IV 2.5.5.1" "Case ℱ = 𝒪_X", ega "IV 2.5.5.3" "special case", ega "IV 4.7.1" "special case"]
theorem length_quotient_map_eq_of_flatHom_of_map_maximalIdeal_eq
    {B B' : Type*} [CommRing B] [CommRing B'] [IsLocalRing B] [IsLocalRing B']
    {ψ : B →+* B'} (hloc : IsLocalHom ψ) (hflat : ψ.Flat)
    (hmax : Ideal.map ψ (IsLocalRing.maximalIdeal B) = IsLocalRing.maximalIdeal B')
    (J : Ideal B) :
    Module.length B' (B' ⧸ Ideal.map ψ J) = Module.length B (B ⧸ J) := by
  let : Algebra B B' := ψ.toAlgebra
  have : Module.Flat B B' := hflat
  have : IsLocalHom (algebraMap B B') := hloc
  rw [show Ideal.map ψ J = Ideal.map (algebraMap B B') J from rfl,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' J).toLinearEquiv.length_eq]
  exact (length_baseChange_eq_of_map_maximalIdeal B B' hmax _).symm

/-- If `ψ : B ⟶ B'` is flat and local and extends the maximal ideal of `B` to the maximal ideal
of `B'`, then the length of `B'` over itself is the length of `B` over itself. -/
theorem length_self_eq_of_flatHom_of_map_maximalIdeal_eq
    {B B' : Type*} [CommRing B] [CommRing B'] [IsLocalRing B] [IsLocalRing B']
    {ψ : B →+* B'} (hloc : IsLocalHom ψ) (hflat : ψ.Flat)
    (hmax : Ideal.map ψ (IsLocalRing.maximalIdeal B) = IsLocalRing.maximalIdeal B') :
    Module.length B' B' = Module.length B B := by
  rw [← (Submodule.quotEquivOfEqBot (⊥ : Ideal B') rfl).length_eq,
    ← (Submodule.quotEquivOfEqBot (⊥ : Ideal B) rfl).length_eq,
    ← length_quotient_map_eq_of_flatHom_of_map_maximalIdeal_eq hloc hflat hmax ⊥, Ideal.map_bot]

/-- In a commuting square of ring homomorphisms whose left vertical `χ` extends the maximal
ideal of `A` to that of `A'`, the extension of the maximal ideal of `A'` along the lower
horizontal `φ'` is the extension along the right vertical `ψ` of the extension of the maximal
ideal of `A` along the upper horizontal `φ`. -/
theorem map_maximalIdeal_eq_map_map_of_comp_eq
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsLocalRing A']
    {χ : A →+* A'} {φ : A →+* B} {φ' : A' →+* B'} {ψ : B →+* B'}
    (hsq : ψ.comp φ = φ'.comp χ)
    (hmax : Ideal.map χ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal A') :
    Ideal.map φ' (IsLocalRing.maximalIdeal A') =
      Ideal.map ψ (Ideal.map φ (IsLocalRing.maximalIdeal A)) := by
  rw [← hmax, Ideal.map_map, Ideal.map_map, hsq]

/-- Let `φ : A ⟶ B` and `φ' : A' ⟶ B'` be two horizontal ring homomorphisms, joined by verticals
`χ : A ⟶ A'` and `ψ : B ⟶ B'` making the square commute, and suppose each vertical extends the
maximal ideal to the maximal ideal, `ψ` being moreover flat and local. Then

  `length_{B'}(B' / 𝔪_{A'} B') = length_B(B / 𝔪_A B)`. -/
theorem length_quotient_extendedMaximalIdeal_eq_of_square
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
    {χ : A →+* A'} {φ : A →+* B} {φ' : A' →+* B'} {ψ : B →+* B'}
    (hsq : ψ.comp φ = φ'.comp χ)
    (hmaxA : Ideal.map χ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal A')
    (hloc : IsLocalHom ψ) (hflat : ψ.Flat)
    (hmaxB : Ideal.map ψ (IsLocalRing.maximalIdeal B) = IsLocalRing.maximalIdeal B') :
    Module.length B' (B' ⧸ Ideal.map φ' (IsLocalRing.maximalIdeal A')) =
      Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) := by
  rw [map_maximalIdeal_eq_map_map_of_comp_eq hsq hmaxA]
  exact length_quotient_map_eq_of_flatHom_of_map_maximalIdeal_eq hloc hflat hmaxB _

/-- Let `Bh` be a henselization or a strict henselization of a local ring `A`, let `q` be a
minimal prime of `Bh` and let `p` be the prime of `A` it lies over. Then

  `length_{(Bh)_q}((Bh)_q) = length_{A_p}(A_p)`. -/
theorem length_localizationAtPrime_eq_of_isHenselization
    {A : Type*} {Bh : Type*} [CommRing A] [CommRing Bh] [IsLocalRing A] [IsLocalRing Bh]
    [Algebra A Bh] (L : Type*) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [IsLocalRing.IsHenselization A L Bh]
    (p : Ideal A) [p.IsPrime] (q : Ideal Bh) [q.IsPrime] [q.LiesOver p]
    (hq : q ∈ minimalPrimes Bh) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime p) (Localization.AtPrime p) :=
  length_self_eq_of_flatHom_of_map_maximalIdeal_eq
    (Localization.isLocalHom_localRingHom p q (algebraMap A Bh) Ideal.LiesOver.over)
    (IsLocalRing.flat_localRingHom_of_isHenselization L p q)
    (IsLocalRing.map_maximalIdeal_localRingHom_of_isHenselization L p q hq)

end Ring

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
  {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))

include hX hxbar

/-! ### The étale-local invariance of the multiplicity at the generic point -/

/-- At a geometric point `x̄` over the generic point `ξ` of a prime divisor of a decent algebraic
space,

  `length_{𝒪_{X, x̄}}(𝒪_{X, x̄}) = length_{𝒪^h_{X, ξ}}(𝒪^h_{X, ξ})`. -/
theorem PrimeDivisor.length_etaleLocalRing_eq_length_genericHenselianLocalRing :
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Module.length (etaleLocalRing B S hS X xbar : Type (u + 1))
        (etaleLocalRing B S hS X xbar : Type (u + 1)) =
      Module.length ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  Ring.length_self_eq_of_flatHom_of_map_maximalIdeal_eq
    (Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec hxbar)
    (Z.flat_henselianToEtaleLocalRing B S hS hX hdec hxbar)
    (Z.map_maximalIdeal_henselianToEtaleLocalRing B S hS hX hdec hxbar)

/-! ### The multiplicity of a prime divisor over a prime divisor, in the two readings -/

/-- Let `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` and `ψ : 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` be ring
homomorphisms making the square whose verticals are the two maps of Stacks 0EMZ commute. Then

  `length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}) = m`,

where `m` is `AlgebraicGeometry.Space.primeDivisorFlatMultiplicity` along `φ`, that is the
colength `length_{𝒪^h_{X, ξ}}(𝒪^h_{X, ξ} / 𝔪^h_{Y, ξ'} 𝒪^h_{X, ξ})`. -/
theorem PrimeDivisor.length_quotient_map_eq_primeDivisorFlatMultiplicity
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hdecY : IsDecentSpace B S hS Y) (ZY : PrimeDivisor B S hS Y)
    {ybar : GeometricPoint B S hS Y} (hybar : ybar.LiesOver (ZY.genericPoint B S hS Y))
    (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
      ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (ψ : (etaleLocalRing B S hS Y ybar : Type (u + 1)) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hsq : (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).comp φ =
      ψ.comp (ZY.henselianToEtaleLocalRing B S hS hY hdecY hybar)) :
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    letI := isLocalRing_etaleLocalRing B S hS Y hY ybar
    letI := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
    Module.length (etaleLocalRing B S hS X xbar : Type (u + 1))
        ((etaleLocalRing B S hS X xbar : Type (u + 1)) ⧸
          Ideal.map ψ (maximalIdeal (etaleLocalRing B S hS Y ybar : Type (u + 1)))) =
      primeDivisorFlatMultiplicity B S hS hX hdec Z hY hdecY ZY φ :=
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := isLocalRing_etaleLocalRing B S hS Y hY ybar
  let := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  Ring.length_quotient_extendedMaximalIdeal_eq_of_square hsq
    (ZY.map_maximalIdeal_henselianToEtaleLocalRing B S hS hY hdecY hybar)
    (Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec hxbar)
    (Z.flat_henselianToEtaleLocalRing B S hS hX hdec hxbar)
    (Z.map_maximalIdeal_henselianToEtaleLocalRing B S hS hX hdec hxbar)

end AlgebraicGeometry.Space

end
