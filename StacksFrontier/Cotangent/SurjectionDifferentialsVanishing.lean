module

public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex

/-!
# Vanishing of the zeroth homology of the differentials on the polynomial site

Let `A → B` be a surjective ring map and let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` be the sheaf of `B̲`-modules on
the polynomial site `C_{B/A}`. Then `H₀(C_{B/A}, Ω) = 0`.

This is the case `k = 1` of the final assertion of Stacks Tag 08RF (Quillen's spectral
sequence), namely that `H_i(C_{B/A}, Symᵏ_{B̲}(Ω)) = 0` for `i < k`; for `k = 1` the symmetric
power is `Ω` itself and the assertion is the vanishing of `H₀`. It is also the step the source's
own proof of 08RF makes first: "Note that `π_!(Ω) = Ω_{B/A} = 0` (Lemma 08QF) as `A → B` is
surjective".

## Main results

* `CommAlgCat.isZero_lowerShriekZero_polynomialCotangentSheaf_of_surjective`: the vanishing.

## Implementation notes

`H₀(C_{B/A}, Ω)` is read in the only form this library has it: the sections at the point of
`L₀π_!` at abelian coefficients, on the small model of the footnote-restricted site, exactly as
in Tag 08PU's `CommAlgCat.standardResolutionLeftDerivedCotangentComplexIso`. The attribute is
labelled with that caveat.

The proof is the source's. Tag 08PU identifies `L₀π_!(Ω)` with `H⁰(L_{B/A})`, Tag 08QF
identifies the latter with `Ω[B⁄A]`, and `Ω[B⁄A] = 0` for a surjection
(`KaehlerDifferential.subsingleton_of_surjective`).

### What this file does not prove about 08RF

The spectral sequence itself — `E₁^{p,q} = H_{-p-q}(C_{B/A}, Symᵏ_{B̲}(Ω)) ⇒ Tor^A_{-p-q}(B, B)`
with `d_r` of bidegree `(r, -r+1)` — is not constructed here.

The final vanishing is proved here only for `k = 1`, at abelian coefficients, which is the form
the Tag 08PU material of this library computes. The general case, for every `k`, is
`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective` in
`StacksFrontier.Cotangent.SurjectionSymmetricPowerVanishing`, read at linear coefficients as Tag
08RD is.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **Stacks 08RF**, the final vanishing in the case `k = 1`. For a surjective ring map `A → B`
the zeroth homology of the sheaf of base-changed differentials on the polynomial site vanishes,
because it is `H⁰(L_{B/A}) = Ω[B⁄A]` and `Ω[B⁄A] = 0` for a surjection. -/
@[stacks 08RF "the final vanishing H_i(C_{B/A}, Symᵏ(Ω)) = 0 for i < k, in the case k = 1, \
  where Sym¹(Ω) = Ω: for a surjective A → B the sections at the point of L₀π_!(Ω_{𝒪/A} ⊗_𝒪 B̲) \
  vanish. As in Tag 08PU, Lπ_! is read degreewise at abelian coefficients on the small model of \
  the footnote-restricted site. The same vanishing for every k, at linear coefficients, is \
  CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective"]
theorem isZero_lowerShriekZero_polynomialCotangentSheaf_of_surjective
    (hsurj : Function.Surjective (algebraMap A ↥B)) :
    IsZero ((Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
      (((Stacks.ChaoticSite.abelianPointLowerShriek
            (smallBoundedPolynomialSite A B
              (standardResolutionVarCardinal A B))).leftDerived 0).obj
        (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B)))) := by
  have hs : Subsingleton Ω[↥B⁄A] := KaehlerDifferential.subsingleton_of_surjective A ↥B hsurj
  have h0 : IsZero (ModuleCat.of ↥B Ω[↥B⁄A]) := ModuleCat.isZero_iff_subsingleton.mpr hs
  have h1 : IsZero ((cotangentComplex.{u, u} A B).homology (-((0 : ℕ) : ℤ))) := by
    rw [Nat.cast_zero, neg_zero]
    exact h0.of_iso (cotangentComplex_homologyZeroIso A B)
  exact (((forget₂ (ModuleCat.{u} ↥B) AddCommGrpCat.{u}).map_isZero h1)).of_iso
    (standardResolutionLeftDerivedCotangentComplexIso A B 0)

end CommAlgCat

end
