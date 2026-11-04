module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# A second centre inside a power of the first

Let `X` be a scheme, let `I` be a quasi-coherent ideal sheaf on `X` with blowup
`b : X' = Bl_I(X) ⟶ X` and exceptional ideal `E = I·𝒪_{X'}`, and let `J ≤ I ^ d` be a second
ideal sheaf on `X`. Then `b⁻¹J·𝒪_{X'}` is `E ^ d` times a third ideal sheaf `Z'` on `X'`, and
the two clauses of [Stacks, Tag 080B] hold for the centre `I · J` and that `Z'`.

This is the direction of tag 080B that needs no input beyond the blowup itself: it produces a
closed subscheme `Z'` of `X'` out of a centre `Y = I · J` on `X`. Tag 080B is the converse —
given `Z'`, produce `J` — and that converse is [Stacks, Tag 0803]; see the implementation notes.

## Main results

* `AlgebraicGeometry.exists_comap_eq_exceptionalIdeal_pow_mul`: the inverse image of `J ≤ I ^ d`
  on the blowup factors as `E ^ d · Z'`.
* `AlgebraicGeometry.exists_supportSet_eq_union_image_and_nonempty_blowUpCompositionIso`: both
  clauses of [Stacks, Tag 080B] for that `Z'`.

## Implementation notes

The factorization is division by an effective Cartier divisor. The inverse image of `I ^ d` is
`E ^ d` (`Stacks.IdealSheaf.comap_pow`), so `b⁻¹J·𝒪_{X'} ≤ E ^ d`; and `E ^ d` is an effective
Cartier divisor, being a power of one ([Stacks, Tag 02OS] for the exceptional ideal), so
`AlgebraicGeometry.exists_mul_eq_of_le_of_isEffectiveCartierDivisor` divides by it. The second
factor is the quotient `(b⁻¹J·𝒪_{X'}) : E ^ d`, and it is the only one: the generator of
`E ^ d` on a chart is a nonzerodivisor, so a cofactor is determined.

What tag 080B needs and this file does not supply is the opposite assignment: given a closed
subscheme `Z'` of `X'` of finite presentation, a `d > 0` and a finite-type `J ≤ I ^ d` on `X`
whose quotient `(b⁻¹J·𝒪_{X'}) : E ^ d` is `Z'`. That is [Stacks, Tag 0803], Lemma 31.32.5, for
the Rees algebra `⨁ Iⁿ`: the finite-type submodule `ℱ ⊆ Iᵈ` with `Z' = Proj(𝒜/ℱ𝒜)`, read as an
ideal sheaf `J = ℱ ⊆ 𝒪_X`. The chart-level identity that turns that presentation of `Z'` into
the factorization is already available, as
`affineBlowupAlgebra.map_ideal_eq_map_pow_mul_normalize` in
`StacksFrontier/RingTheory/Blowup/IdealFactorization.lean`.

## References

* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 02ON](https://stacks.math.columbia.edu/tag/02ON)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The inverse image of a centre contained in `I ^ d` is contained in the `d`-th power of the
exceptional ideal, the inverse image of a power being the power of the inverse image. -/
theorem comap_le_exceptionalIdeal_pow (I J : X.IdealSheafData) (d : ℕ) (hJ : J ≤ I ^ d) :
    J.comap (blowUpToBase I) ≤ exceptionalIdeal I ^ d :=
  (Scheme.IdealSheafData.comap_mono (blowUpToBase I) hJ).trans
    (Stacks.IdealSheaf.comap_pow I (blowUpToBase I) d).le

/-- **The factorization of a centre inside a power of the first centre.** For `J ≤ I ^ d` the
inverse image of `J` on the blowup of `X` in `I` is the `d`-th power of the exceptional ideal
times a second ideal sheaf on the blowup. -/
theorem exists_comap_eq_exceptionalIdeal_pow_mul (I J : X.IdealSheafData) (d : ℕ)
    (hJ : J ≤ I ^ d) :
    ∃ Z' : (blowUp I).IdealSheafData,
      J.comap (blowUpToBase I) = exceptionalIdeal I ^ d * Z' :=
  exists_mul_eq_of_le_of_isEffectiveCartierDivisor _ _
    (Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) d)
    (comap_le_exceptionalIdeal_pow I J d hJ)

/-- **Both clauses of [Stacks, Tag 080B], for a centre `I · J` with `J ≤ I ^ d`.** There is a
centre `Z'` on the blowup of `X` in `I` whose support together with that of `I` is the support
of `I · J`, and whose blowup composed with the first is the blowup of `X` in `I · J`.

This is not the tag itself: tag 080B starts from `Z'` and produces the centre on `X`, and that
direction is [Stacks, Tag 0803]. -/
theorem exists_supportSet_eq_union_image_and_nonempty_blowUpCompositionIso
    (I J : X.IdealSheafData) (d : ℕ) (hJ : J ≤ I ^ d) :
    ∃ Z' : (blowUp I).IdealSheafData,
      (I * J).supportSet = I.supportSet ∪ (blowUpToBase I).base '' Z'.supportSet ∧
        Nonempty (Over.mk (blowUpToBase Z' ≫ blowUpToBase I) ≅
          Over.mk (blowUpToBase (I * J))) := by
  obtain ⟨Z', hZ'⟩ := exists_comap_eq_exceptionalIdeal_pow_mul I J d hJ
  exact ⟨Z', supportSet_mul_eq_union_image I Z' d J hZ',
    nonempty_blowUpCompositionIso I Z' d J hZ'⟩

end AlgebraicGeometry

end
