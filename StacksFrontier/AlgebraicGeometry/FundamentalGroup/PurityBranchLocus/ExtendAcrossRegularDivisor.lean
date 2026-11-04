module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.RegularDivisorExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedRegularBoundary
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a cover unramified in codimension one across a regular divisor

Let `X` be a locally Noetherian scheme and `D ⊆ X` an effective Cartier divisor which is a regular
scheme. A finite étale `Y → X ∖ D` which is unramified over `X` in codimension one is the
restriction of a finite étale cover of `X`. This is [Stacks, Tag 0EYE].

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_of_isEffectiveCartierDivisor`:
  [Stacks, Tag 0EYE].

## Implementation notes

The proof is the one of the source: the tag is the special case `U = X ∖ D` of
[Stacks, Tag 0H2W] (`exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne`), whose two
remaining hypotheses are checked here.

* `X ∖ D` is dense in `X`. It is even scheme-theoretically dense, which is the density half of
  [Stacks, Tag 07ZU] (`Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl`), the
  fact the source cites from Divisors, Section 01WQ.
* `𝒪_{X, x}` is regular for `x ∈ D`. This is
  `AlgebraicGeometry.isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk`: the local
  ring `𝒪_{X, x}` is cut out by a nonzerodivisor with quotient `𝒪_{D, x}`, which is regular
  because `D` is ([Stacks, Tag 02IT]), so `𝒪_{X, x}` is regular by [Stacks, Tag 00NU].

"`D` is a regular scheme" is `AlgebraicGeometry.IsRegular D.subscheme` ([Stacks, Tag 02IS]), and
"`Y` is unramified over `X` in codimension one" is
`Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne` for the inclusion of `X ∖ D`, the
predicate [Stacks, Tag 0H2W] is stated with.

## References

* [Stacks Project, Lemma 58.31.3 (0EYE)](https://stacks.math.columbia.edu/tag/0EYE)
* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Lemma 10.106.3 (00NU)](https://stacks.math.columbia.edu/tag/00NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EYE.** Let `X` be a locally Noetherian scheme and let `D ⊆ X` be an
effective Cartier divisor such that `D` is a regular scheme. Let `f : Y ⟶ X ∖ D` be a finite
étale morphism. If `Y` is unramified over `X` in codimension one, then there exists a finite étale
morphism `p : Y' ⟶ X` whose restriction to `X ∖ D` is `Y`: an isomorphism
`Y' ×_X (X ∖ D) ≅ Y` over `X ∖ D`.

Here `D` is the closed subscheme `D.subscheme` cut out by the ideal sheaf `D`, and `X ∖ D` is the
open subscheme `D.support.compl`. -/
@[stacks 0EYE "a finite étale cover of `X ∖ D` unramified in codimension one extends across a \
regular effective Cartier divisor `D`; the special case `U = X ∖ D` of Tag 0H2W",
  sga "7 II 2.3.1" "Extension clause"]
public theorem exists_finiteEtale_extension_of_isEffectiveCartierDivisor
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hDreg : IsRegular D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ D.support.compl) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne
      (Scheme.Opens.ι D.support.compl) f) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ X), IsFinite p ∧ Etale p ∧
      ∃ e : pullback p (Scheme.Opens.ι D.support.compl) ≅ Y,
        e.hom ≫ f = pullback.snd p (Scheme.Opens.ι D.support.compl) := by
  refine exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne D.support.compl ?_ f hunr
    fun x hx ↦ ?_
  · rw [DenseRange, Scheme.Opens.range_ι]
    exact dense_of_isSchemeTheoreticallyDense _
      (Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl D hD)
  · have hxD : x ∈ D.support := by
      by_contra h
      exact hx h
    have h := (isRegular_tfae D.subscheme).out 1 2
    exact isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk D hD x hxD
      ((h.mp hDreg).2 _)

end AlgebraicGeometry

end
