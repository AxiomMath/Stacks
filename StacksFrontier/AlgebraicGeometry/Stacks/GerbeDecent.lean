module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactSurjectiveDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack

/-!
# Decency of the base of a gerbe of algebraic stacks (Stacks 0GW5)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0GW5** says that if `f`
exhibits `𝒳` as a gerbe over `𝒴` (**Stacks 06QC**) and `𝒳` is decent (**Stacks 0GW1**), then `𝒴`
is decent.

The source's proof is two citations: `f` is a universal homeomorphism (**Stacks 06R9**), and the
target of a quasi-compact surjection out of a decent algebraic stack is decent
(**Stacks 0GW4**). Both of the hypotheses of Stacks 0GW4 are extracted here from the gerbe
condition:

* *surjectivity* is available outright, from the surjectivity clause of **Stacks 06QI**
  (`AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver`), with no appeal to Stacks 06R9 at all;
* *quasi-compactness* is the one place where Stacks 06R9 is used, and it is used only through its
  conclusion: a universal homeomorphism identifies the points of every base change `𝒵 ×_𝒴 𝒳` with
  the points of `𝒵`, so compactness of `|𝒵|` is carried back to `|𝒵 ×_𝒴 𝒳|`, which is
  quasi-compactness of `f` in the sense of **Stacks 050U**.

Stacks 06R9 is `AlgebraicGeometry.Stack.AlgebraicStacks.universalHomeomorphism_of_isGerbeOver`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_universalHomeomorphism`: a universal
  homeomorphism of algebraic stacks (**Stacks 0CI7**) is quasi-compact (**Stacks 050U**).
* `AlgebraicGeometry.Stack.isDecent_of_isGerbeOver`: **Stacks 0GW5**.

## Implementation notes

Of the two spellings of Stacks 0CI7 in this library, the hypothesis is taken in the form
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`, which tests only the canonical
2-fibre-product square of Stacks 04T2. That is the weaker of the two to supply — the other,
`AlgebraicGeometry.Stack.UniversalHomeomorphism`, tests every model of the base change — and it is
already the square that quasi-compactness of a 1-morphism
(`AlgebraicGeometry.Stack.IsQuasiCompactMorphism`) is stated at, so the two conditions meet with
no transport between models.

Quasi-compactness of an algebraic stack (`AlgebraicGeometry.Stack.IsQuasiCompactStack`,
**Stacks 04YB**) is `CompactSpace` for the topology of **Stacks 04XL** on the point set of
**Stacks 04XG**, and being a homeomorphism on points is `IsHomeomorph` for those same two
topologies, so the step is `Homeomorph.compactSpace` along the inverse of the bundled
homeomorphism and needs no comparison lemma. The direction matters: a continuous bijection onto a
compact space does not make its source compact, so it is the *inverse* of the homeomorphism that
is used, which is why surjectivity of the base change is not enough here and the full
homeomorphism statement of Stacks 06R9 is what gets consumed.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06R9](https://stacks.math.columbia.edu/tag/06R9)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW4](https://stacks.math.columbia.edu/tag/0GW4)
* [Stacks Project, Tag 0GW5](https://stacks.math.columbia.edu/tag/0GW5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universal homeomorphism of algebraic stacks over `S` is quasi-compact.** If every
canonical base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f : 𝒳 ⟶ 𝒴` is a homeomorphism on the points of
Stacks 04XG for the topology of Stacks 04XL (**Stacks 0CI7**), then `f` is quasi-compact in the
sense of **Stacks 050U**: a base change of `f` by a quasi-compact algebraic stack is again
quasi-compact.

Quasi-compactness of an algebraic stack is compactness of its space of points (**Stacks 04YB**),
and the inverse of the homeomorphism transports it from `|𝒵|` to `|𝒵 ×_𝒴 𝒳|`. -/
theorem isQuasiCompactMorphism_of_universalHomeomorphism
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f) :
    IsQuasiCompactMorphism.{u, w} B S hS f := by
  intro 𝒵 g h𝒵
  let _ := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
  let _ := pointTopology B S hS 𝒵.val
  have := h𝒵
  exact (hf 𝒵 g).homeomorph.symm.compactSpace

/-- **Stacks 0GW5.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If `f`
exhibits `𝒳` as a gerbe over `𝒴` (**Stacks 06QC**) and `𝒳` is decent (**Stacks 0GW1**), then `𝒴`
is decent.

By **Stacks 06R9** `f` is a universal homeomorphism (**Stacks 0CI7**), hence quasi-compact,
through `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_universalHomeomorphism`; surjectivity
of `f` comes from the gerbe condition directly, by the surjectivity clause of **Stacks 06QI**.
With both in hand the conclusion is **Stacks 0GW4**. -/
@[stacks 0GW5]
theorem isDecent_of_isGerbeOver
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver.{u, w} B S hS f)
    (h𝒳 : IsDecent B S hS 𝒳.val) :
    IsDecent B S hS 𝒴.val :=
  isDecent_of_isQuasiCompactMorphism_of_isSurjective B S hS f
    (isQuasiCompactMorphism_of_universalHomeomorphism B S hS f
      (AlgebraicStacks.universalHomeomorphism_of_isGerbeOver B S hS f hf))
    (isSurjective_of_isGerbeOver B S hS f hf) h𝒳

end AlgebraicGeometry.Stack

end
