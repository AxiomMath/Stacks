module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealTwist
import StacksCore.Tactic.StacksAttribute

/-!
# The restriction sequence of the powers of the exceptional ideal sheaf

Let `(A, 𝔪)` be a local ring, let `X` be the blowup of `Spec(A)` in `𝔪`, let `i : E ⟶ X` be its
exceptional divisor and let `ℐ` be the ideal sheaf of `E`. This file provides the family of short
exact sequences

`0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0`

that the proof of [Stacks, Tag 0B63] takes its clauses (4) and (5) from, with the first map
identified as the inclusion of ideal sheaves.

## Main definitions

* `AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequence`: the sequence, as a short
  complex of `𝒪_X`-modules whose middle term is `ℐⁿ` on the nose.
* `AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequenceIsoOne` and
  `.exceptionalTwistedSequenceIsoThree`: its first term is `ℐ^{n+1} = ℐ·ℐⁿ` and its third term is
  `i_*𝒪_E(n)`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.shortExact_exceptionalTwistedSequence`: the sequence is
  short exact, with no hypothesis on `A`.
* `AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequence_f_comp_idealInclusion`:
  **the first map is the inclusion `ℐⁿ⁺¹ ⊆ ℐⁿ`**, in the sense that it is compatible with the two
  inclusions into `𝒪_X`. This is what makes the induced map on global sections the inclusion
  `𝔪ⁿ⁺¹ ⊆ 𝔪ⁿ` and not merely some map.

## Where the sequence comes from

It is the ideal sheaf sequence `0 ⟶ ℐ ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` of [Stacks, Tag 0C6K] tensored by the
invertible sheaf `ℐⁿ`, which is `Stacks.Divisors.exists_shortExact_invertibleTwist` at `ℐⁿ`: there
the outer terms are already identified, the middle term is `ℐⁿ` itself by the left unit constraint
and the third term is `i_*i^*ℐⁿ` by the projection formula of [Stacks, Tag 0FZE] at the closed
immersion `i`. Its hypothesis is that `ℐⁿ` be an effective Cartier divisor, and that holds with no
hypothesis on `A`: the exceptional divisor of a blowup is an effective Cartier divisor by part (2)
of [Stacks, Tag 02OS], and powers of an effective Cartier divisor are effective Cartier divisors.

The first term is `ℐ ⊗ ℐⁿ`, carried onto the ideal sheaf of `ℐ·ℐⁿ` by
`Stacks.Divisors.idealTensorMulIso`; the compatibility of that identification with the inclusions
into `𝒪_X` is `Stacks.Divisors.idealTensorMul_comp_idealInclusion`, because both composites
are multiplication of sections. The sequence is therefore indexed by `ℐ·ℐⁿ` rather than by
`ℐⁿ⁺¹`: the two sheaves of ideals are *equal*, by `pow_succ'`, so a statement about one rewrites
into a statement about the other with no transport.

The third term is turned into `i_*𝒪_E(n)` by part (3) of [Stacks, Tag 02OS] in degree `n`
(`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealPowIsoTwistSheaf`) restricted to `E`, the
restriction of `𝒪_X(n)` being `𝒪_E(n)` by
`AlgebraicGeometry.BlowUpDualizing.pullbackTwistSheafIso`.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple RingedSpaceModuleAdjunction
open Stacks.Divisors (idealInclusion idealSheafOfModules idealTensorInclusion idealUnitIso
  idealTensorMulIso idealTensorMul_comp_idealInclusion isEffectiveCartierDivisor_pow
  exists_shortExact_invertibleTwist)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **Every power of the ideal sheaf of the exceptional divisor is an effective Cartier
divisor.** The exceptional divisor of a blowup is one by part (2) of [Stacks, Tag 02OS], and a
power of an effective Cartier divisor is an effective Cartier divisor. No hypothesis on `A`. -/
theorem isEffectiveCartierDivisor_exceptionalIdealPow (n : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdeal (centre A) ^ n) :=
  isEffectiveCartierDivisor_pow inferInstance n

/-- **The restriction sequence `0 ⟶ ℐ·ℐⁿ ⟶ ℐⁿ ⟶ i_*i^*ℐⁿ ⟶ 0`** of the `n`-th power of the ideal
sheaf of the exceptional divisor: the ideal sheaf sequence of [Stacks, Tag 0C6K] tensored by the
invertible sheaf `ℐⁿ`. Short exactness is `shortExact_exceptionalTwistedSequence`. -/
def exceptionalTwistedSequence (n : ℕ) : ShortComplex (blowUpScheme A).Modules :=
  ShortComplex.mk
    (idealTensorInclusion (exceptionalIdeal (centre A)) (exceptionalIdeal (centre A) ^ n) ≫
      (idealUnitIso (exceptionalIdeal (centre A) ^ n)).hom)
    ((modulePullbackPushforwardAdjunction
        (exceptionalIdeal (centre A)).subschemeι.toLRSHom.toShHom).unit.app
      (idealSheafOfModules (exceptionalIdeal (centre A) ^ n)))
    (exists_shortExact_invertibleTwist (exceptionalIdeal (centre A))
      (idealSheafOfModules (exceptionalIdeal (centre A) ^ n))
      (isEffectiveCartierDivisor_exceptionalIdealPow A n)).fst

/-- The middle term of the sequence is `ℐⁿ` itself. -/
theorem exceptionalTwistedSequence_X₂ (n : ℕ) :
    (exceptionalTwistedSequence A n).X₂ = idealSheafOfModules (exceptionalIdeal (centre A) ^ n) :=
  rfl

/-- **The sequence is short exact**, with no hypothesis on `A`. -/
theorem shortExact_exceptionalTwistedSequence (n : ℕ) :
    (exceptionalTwistedSequence A n).ShortExact :=
  (exists_shortExact_invertibleTwist (exceptionalIdeal (centre A))
    (idealSheafOfModules (exceptionalIdeal (centre A) ^ n))
    (isEffectiveCartierDivisor_exceptionalIdealPow A n)).snd

/-- The first term of the sequence is the ideal sheaf of `ℐ·ℐⁿ`, which is `ℐⁿ⁺¹`: the
multiplication `ℐ ⊗ ℐⁿ ⟶ ℐ_{ℐ·ℐⁿ}` is an isomorphism because `ℐⁿ` is an effective Cartier
divisor. -/
def exceptionalTwistedSequenceIsoOne (n : ℕ) :
    (exceptionalTwistedSequence A n).X₁ ≅
      idealSheafOfModules (exceptionalIdeal (centre A) * exceptionalIdeal (centre A) ^ n) :=
  idealTensorMulIso (exceptionalIdeal (centre A)) (exceptionalIdeal (centre A) ^ n)
    (isEffectiveCartierDivisor_exceptionalIdealPow A n)

/-- **The first map of the sequence is the inclusion of ideal sheaves.** Read through
`exceptionalTwistedSequenceIsoOne`, the map `ℐⁿ⁺¹ ⟶ ℐⁿ` is compatible with the two inclusions
into `𝒪_X`; since those inclusions are monomorphisms this pins the map down, and it is what makes
the induced map on global sections the inclusion `𝔪ⁿ⁺¹ ⊆ 𝔪ⁿ`. -/
theorem exceptionalTwistedSequence_f_comp_idealInclusion (n : ℕ) :
    (exceptionalTwistedSequence A n).f ≫ idealInclusion (exceptionalIdeal (centre A) ^ n) =
      (exceptionalTwistedSequenceIsoOne A n).hom ≫
        idealInclusion (exceptionalIdeal (centre A) * exceptionalIdeal (centre A) ^ n) :=
  (Category.assoc _ _ _).trans (idealTensorMul_comp_idealInclusion (exceptionalIdeal (centre A))
    (exceptionalIdeal (centre A) ^ n)).symm

/-- **`i^*ℐⁿ ≅ 𝒪_E(n)`**: part (3) of [Stacks, Tag 02OS] in degree `n`, restricted to the
exceptional curve. -/
def pullbackExceptionalIdealPowIso (n : ℕ) :
    (Scheme.Modules.pullback (exceptionalImmersion A)).obj
        (idealSheafOfModules (exceptionalIdeal (centre A) ^ n)) ≅
      curveTwistSheaf A (n : ℤ) :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).mapIso
      (exceptionalIdealPowIsoTwistSheaf A n) ≪≫
    pullbackTwistSheafIso A (n : ℤ)

/-- **The third term of the sequence is `i_*𝒪_E(n)`.** -/
def exceptionalTwistedSequenceIsoThree (n : ℕ) :
    (exceptionalTwistedSequence A n).X₃ ≅
      (Scheme.Modules.pushforward (exceptionalImmersion A)).obj (curveTwistSheaf A (n : ℤ)) :=
  (Scheme.Modules.pushforward (exceptionalImmersion A)).mapIso
    (pullbackExceptionalIdealPowIso A n)

end AlgebraicGeometry.BlowUpDualizing

end
