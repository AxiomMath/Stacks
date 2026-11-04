module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistDown

/-!
# Twisting down inside the geometric factor `N ↦ 𝒪_X(q) ⊗ p^*Ñ`

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. `BitUniformityIII/AmbientTwistDown.lean` builds the sheaf-level family
`Stacks.Blowup.twistDownMap I q q' : 𝒪_X(q) ⟶ 𝒪_X(q')` for every pair of integers `q' ≤ q`. The
cohomological clauses of [Stacks, Tag 0GAA] need that family *tensored into the fixed factor* of
`Stacks.Blowup.twistedGeometricFactor`, i.e. the natural transformation

`𝒪_X(q) ⊗ p^*Ñ ⟶ 𝒪_X(q') ⊗ p^*Ñ`,  natural in the `A`-module `N`,

because every cohomology family of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` on the
blowup is the cohomology of a sheaf built from `twistedGeometricFactor I q`.

## Why no comparison isomorphism is needed

`Stacks.Blowup.twistedGeometricFactor I q` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula A (blowUpOver I)
(blowUpTwist I q)`, whose only dependence on `q` is through the *fixed factor* `𝒪_X(q)`, and
`Stacks.Blowup.blowUpTwist` is an abbreviation for
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (reesGrading I) q` — which is exactly the
type `twistDownMap` is stated at. So `twistDownMap` is already a morphism of the fixed factor and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap` applies to it directly.
There is no arithmetic and no transport left in this file; both live in
`AmbientTwistDown.lean`, inside degree-preservation `Prop`s.

## Main definitions

* `Stacks.Blowup.twistDownFactorMap`: **the natural transformation
  `𝒪_X(q) ⊗ p^*(-) ⟶ 𝒪_X(q') ⊗ p^*(-)` for `q' ≤ q`.**

## Main results

* `Stacks.Blowup.twistDownFactorMap_self`: it is the identity at `q' = q`.
* `Stacks.Blowup.twistDownFactorMap_comp`: **it is functorial** — the sheaf-level functoriality
  `Stacks.Blowup.twistDownMap_comp` survives tensoring into the fixed factor, which is the
  content the field `HGtr_trans` of
  `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation` asks for.

## References

* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.TopDegreeBaseChange (geometricFactorFormulaMap
  geometricFactorFormulaMap_congr geometricFactorFormulaMap_id geometricFactorFormulaMap_comp)

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A) (q q' q'' : ℤ)

/-- **The twisting-down map tensored into the fixed factor of the geometric factor**: for
`q' ≤ q`, the natural transformation `𝒪_X(q) ⊗ p^*Ñ ⟶ 𝒪_X(q') ⊗ p^*Ñ` of functors of the
`A`-module `N`, induced by `Stacks.Blowup.twistDownMap I q q'`.

This is the one ingredient the twist-indexed fields of
`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation` need beyond the sheaf-level
family: all four cohomology families of a `ModuleSituation` on the blowup are built from
`Stacks.Blowup.twistedGeometricFactor`, so a map between its values at `q` and at `q'` is what
`Hⁱ(X, -)` is applied to. -/
def twistDownFactorMap (hq : q' ≤ q) :
    twistedGeometricFactor I q ⟶ twistedGeometricFactor I q' :=
  geometricFactorFormulaMap A (blowUpOver I) (twistDownMap I q q' hq)

/-- **The family is the identity at `q' = q`**, because
`Stacks.Blowup.twistDownMap_self` is. -/
theorem twistDownFactorMap_self : twistDownFactorMap I q q le_rfl = 𝟙 _ :=
  (geometricFactorFormulaMap_congr A (blowUpOver I) (twistDownMap_self I q)).trans
    (geometricFactorFormulaMap_id A (blowUpOver I) _)

/-- **The family is functorial.** Tensoring into the fixed factor is itself functorial
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap_comp`), so the
composition law reduces to `Stacks.Blowup.twistDownMap_comp` at the level of sheaves. -/
theorem twistDownFactorMap_comp (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    twistDownFactorMap I q q' hq ≫ twistDownFactorMap I q' q'' hq'' =
      twistDownFactorMap I q q'' h :=
  (geometricFactorFormulaMap_comp A (blowUpOver I) (twistDownMap I q q' hq)
      (twistDownMap I q' q'' hq'')).symm.trans
    (geometricFactorFormulaMap_congr A (blowUpOver I) (twistDownMap_comp I q q' q'' hq'' hq h))

end Stacks.Blowup

end
