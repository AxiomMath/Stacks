module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack

/-!
# The target of a relative diagonal of algebraic stacks, and two of the 04YS conditions

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. Stacks 04YS asserts that, for `f` representable by algebraic spaces,

1. `f` is separated,
2. `Δ_f` is a closed immersion,
3. `Δ_f` is proper, and
4. `Δ_f` is universally closed

are equivalent, the four notions being the ones of Properties of Stacks, Section 04XB. Stating
the second of them requires the target `𝒳 ×_{f, 𝒴, f} 𝒳` of the relative diagonal to be an
*algebraic* stack, since `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedImmersion` is a
property of a 1-morphism of the 2-category of algebraic stacks. This file supplies that, and
records the one implication among the four conditions that holds by definition.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_relativeDiagonalTarget`: the target of the relative
  diagonal of a 1-morphism of algebraic stacks is an algebraic stack. This is **Stacks 04TF**
  (`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`) at `𝒳 ×_{f, 𝒴, f} 𝒳`, whose two
  hypotheses on the base — that it is a stack in groupoids and that its diagonal is
  representable by algebraic spaces — are two of the clauses of `𝒴` being an algebraic stack.
* `AlgebraicGeometry.Stack.relativeDiagonalTargetStack`: that target, bundled as an object of the
  2-category of algebraic stacks, so that the relative diagonal becomes a 1-morphism of that
  2-category.
* `AlgebraicGeometry.Stack.universallyClosed_of_isProper`: a proper 1-morphism is universally
  closed, which is the implication (3) ⇒ (4) of Stacks 04YS.

## Implementation notes

The hypotheses of Stacks 04TF are read off the proof of algebraicity of `𝒴` by destructing it:
the witness that `𝒴` is fibred in groupoids inside that proof and the one carried by `𝒴` itself
are two proofs of one proposition, so proof irrelevance identifies the two spellings of the
diagonal condition, and `AlgebraicGeometry.Stack.HasRepresentableDiagonal` is by definition the
representability of `AlgebraicGeometry.Stack.diagonalBasedFunctor`.

Properness of a morphism of algebraic spaces is *separated, of finite type and universally
closed* (`AlgebraicGeometry.Space.IsProper`, Stacks 03ZM), and the conditions of Stacks 04XB are
quantified clause by clause over the same data, so (3) ⇒ (4) is the third projection applied
pointwise. The remaining links of the 04YS equivalence are not available here: Stacks proves
them by transporting each property between `Δ_f` and `Δ_{U/V}` along a smooth surjective chart
`V → 𝒴`, which is Properties of Stacks, Lemma 04XD, and then applying Morphisms of Spaces,
Lemma 04Y0 (`AlgebraicGeometry.Space.isSeparated_tfae`) to `U → V`. 04XD is not in this
library.

Both statements are untagged: the tag 04TF is on the general form of the first, and the tag 04YS
belongs to the equivalence of the four conditions, which is not proved here.

## References

* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The target of a relative diagonal of algebraic stacks is an algebraic stack.** For a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the 2-fibre product `𝒳 ×_{f, 𝒴, f} 𝒳` —
the target of the relative diagonal of `f` — is an algebraic stack over `S`. This is Stacks 04TF
applied with base `𝒴`, whose two hypotheses there are the stack and diagonal clauses of the
algebraicity of `𝒴`. -/
theorem isAlgebraicStack_relativeDiagonalTarget
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ 𝒴) :
    IsAlgebraicStack.{u, w} B S hS
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val := by
  obtain ⟨h𝒴, h𝒴stack, h𝒴diag, -⟩ := 𝒴.property
  exact isAlgebraicStack_twoFibreProduct B S hS 𝒳.val.val 𝒳.val.val 𝒴.val.val
    f.hom.hom f.hom.hom h𝒴stack h𝒴diag 𝒳.property 𝒳.property

/-- The target `𝒳 ×_{f, 𝒴, f} 𝒳` of the relative diagonal of a 1-morphism of algebraic stacks,
as an object of the 2-category of algebraic stacks over `S`. -/
def relativeDiagonalTargetStack
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ 𝒴) : AlgebraicStacks.{u, w} B S hS :=
  ⟨twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom,
    isAlgebraicStack_relativeDiagonalTarget B S hS 𝒳 𝒴 f⟩

/-- **The implication (3) ⇒ (4) of Stacks 04YS.** A 1-morphism of categories fibred in groupoids
over the big fppf site of `S` which is proper in the sense of Stacks 04XB is universally closed
in that sense: properness of a morphism of algebraic spaces includes universal closedness, and
the two conditions of Stacks 04XB are quantified over the same data. -/
theorem universallyClosed_of_isProper
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsProper B S hS f) : UniversallyClosed B S hS f :=
  fun U y hy F hF hEq => (hf U y hy F hF hEq).2.2

end AlgebraicGeometry.Stack

end
