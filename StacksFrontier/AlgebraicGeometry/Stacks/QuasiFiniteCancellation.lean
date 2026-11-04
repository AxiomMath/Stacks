module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiFiniteAlgebraicStack

/-!
# Quasi-finiteness cancels a quasi-separated quasi-DM second factor (Stacks 0G2Q)

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. **Stacks 0G2Q**: if the composite
`𝒳 ⟶ 𝒵` is quasi-finite (**Stacks 0G2M**) and `𝒴 ⟶ 𝒵` is quasi-separated and quasi-DM (both
**Stacks 04YW**), then `𝒳 ⟶ 𝒴` is quasi-finite.

The source's proof is "combine Lemmas 06UG and 050Y", and that is what happens here.
Quasi-finiteness is the conjunction of local quasi-finiteness (**Stacks 06PU**) and
quasi-compactness (**Stacks 050U**), and each conjunct cancels on its own: the first by
**Stacks 06UG**, which consumes quasi-DMness of the second factor, and the second by
**Stacks 050Y**, which consumes its quasi-separatedness. So the two hypotheses on `g` are used
one apiece, and neither conjunct of the conclusion needs the other.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiFinite_of_comp_of_isQuasiSeparated_of_isQuasiDM`:
  **Stacks 0G2Q**.

## Implementation notes

This is the cancellation counterpart of
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiFinite_comp` (**Stacks 0G2N**) in
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiFiniteComposition`, and it is assembled the same way:
quasi-finiteness is an `abbrev` for a conjunction, so the hypothesis on the composite is
projected and the conclusion is built as a pair. That is the whole proof, which is why the
covering set is the one declaration.

No hypothesis beyond those of the source is carried: the local quasi-finiteness conjunct is
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_of_comp_of_isQuasiDM`
(**Stacks 06UG**) and the quasi-compactness conjunct is
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated` (**Stacks 050Y**),
both unconditional.

Both conditions on `g` are the **Stacks 04YW** conditions on a 1-morphism of *algebraic stacks*,
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated` and
`...IsQuasiDM`, and not the namesakes `AlgebraicGeometry.Stack.IsQuasiSeparated` and
`AlgebraicGeometry.Space.IsQuasiSeparated`, which are the Stacks 04XB relative property and the
property of a morphism of algebraic spaces.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UD](https://stacks.math.columbia.edu/tag/06UD)
* [Stacks Project, Tag 06UG](https://stacks.math.columbia.edu/tag/06UG)
* [Stacks Project, Tag 0G2M](https://stacks.math.columbia.edu/tag/0G2M)
* [Stacks Project, Tag 0G2N](https://stacks.math.columbia.edu/tag/0G2N)
* [Stacks Project, Tag 0G2Q](https://stacks.math.columbia.edu/tag/0G2Q)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0G2Q.** If a composite of 1-morphisms of algebraic stacks over `S` is quasi-finite
and its second factor is quasi-separated and quasi-DM, then its first factor is quasi-finite.

Quasi-finiteness is local quasi-finiteness together with quasi-compactness, and the source's
proof combines the cancellation of each conjunct: local quasi-finiteness cancels against the
quasi-DM second factor by **Stacks 06UG** and quasi-compactness cancels against the
quasi-separated second factor by **Stacks 050Y**. -/
@[stacks 0G2Q]
theorem isQuasiFinite_of_comp_of_isQuasiSeparated_of_isQuasiDM
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsQuasiFinite B S hS (f ≫ g)) (hgQuasiSeparated : IsQuasiSeparated B S hS g)
    (hgQuasiDM : IsQuasiDM B S hS g) :
    IsQuasiFinite B S hS f :=
  ⟨isLocallyQuasiFinite_of_comp_of_isQuasiDM B S hS f g
      hfg.1 hgQuasiDM,
    Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS f g hfg.2 hgQuasiSeparated⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
