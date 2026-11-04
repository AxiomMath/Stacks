module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiFunction

/-!
# The Euler characteristic of the derived fibres on the points of an algebraic space

For an object `E` of `D(𝒪_X)` on an algebraic space `X` over `S` the Betti-number functions
`β_i : |X| → ℕ` of Stacks 0D1Y are
`AlgebraicGeometry.Space.geometricFibreBettiFunction`.  Stacks 0D1Z speaks of their alternating
sum

`χ_E : |X| → ℤ,  x ↦ ∑ (-1)^i β_i(x)`,

which is formed here.  Its formation commutes with arbitrary base change, degreewise from
clause (1) of Stacks 0D1Y.

## Main definitions

* `AlgebraicGeometry.Space.geometricFibreChiFunction` is `χ_E : |X| → ℤ`.

## Main results

* `AlgebraicGeometry.Space.geometricFibreChiFunction_derivedPullback`: formation of `χ_E`
  commutes with arbitrary base change.

## Implementation notes

*The sum.*  It is a `finsum` over all of `ℤ`, which is `0` unless the summand has finite
support; this is the junk-value convention of `Mathlib/Algebra/Homology/EulerCharacteristic`
and the one the derived-fibre Euler characteristic of a scheme,
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre`, is written at, so that the two read at
the same shape.  The signs are `Int.negOnePow`, again as there.

*Which hypothesis the base change carries.*  Pseudo-coherence of `E`, the hypothesis of
clause (1) of Stacks 0D1Y, which is the only input.  Stacks 0D1Z asks for a perfect `E`, but
that is for its own conclusion — local constancy — and not for this one.

*The derived-category model.*  The objects live in Mathlib's standard model, the one
`AlgebraicGeometry.Space.geometricFibreBettiFunction` is stated at, and that model is named in
the binders rather than installed as an instance for the file.

## References

* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS}

/-- **The Euler characteristic `χ_E : |X| → ℤ` of the derived fibres of an object of `D(𝒪_X)`
on an algebraic space `X`**: the alternating sum `∑ (-1)^i β_i(x)` of the Betti-number functions
`AlgebraicGeometry.Space.geometricFibreBettiFunction` of Stacks 0D1Y. -/
def geometricFibreChiFunction
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (x : points B S hS X.1) : ℤ :=
  ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (geometricFibreBettiFunction B S hS E i x : ℤ)

/-- `χ_E(x)` is the alternating sum `∑ (-1)^i β_i(x)`. -/
@[simp]
theorem geometricFibreChiFunction_apply
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (x : points B S hS X.1) :
    geometricFibreChiFunction B S hS E x =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (geometricFibreBettiFunction B S hS E i x : ℤ) :=
  rfl

/-- **Formation of `χ_E` commutes with arbitrary base change.** For a morphism `g : Y ⟶ X` of
algebraic spaces the Euler characteristic of the derived fibres of `Lg^*E` is that of `E`
composed with the map `|Y| → |X|`, degreewise by clause (1) of Stacks 0D1Y. -/
theorem geometricFibreChiFunction_derivedPullback {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _ _
      (HasDerivedCategory.standard _))
    (hE : @AlgebraicGeometry.RingedSite.IsPseudoCoherent
      (smallEtaleRingedSite B S hS X.1 X.2) _ _ _ _ _ _ (HasDerivedCategory.standard _) E) :
    geometricFibreChiFunction B S hS ((smallEtaleDerivedModulePullback B S hS g).obj E) =
      geometricFibreChiFunction B S hS E ∘ pointsMap B S hS Y.1 g.hom :=
  funext fun y => finsum_congr fun i => congrArg (fun n : ℕ => (i.negOnePow : ℤ) * (n : ℤ))
    (congrFun (geometricFibreBettiFunction_derivedPullback B S hS g E hE i) y)

end AlgebraicGeometry.Space

end
