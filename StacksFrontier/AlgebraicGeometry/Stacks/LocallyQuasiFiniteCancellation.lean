module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRelativePresentation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Local quasi-finiteness cancels a quasi-DM second factor (Stacks 06UG)

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. **Stacks 06UG**: if the composite
`𝒳 ⟶ 𝒵` is locally quasi-finite (**Stacks 06PU**) and `𝒴 ⟶ 𝒵` is quasi-DM (**Stacks 04YW**),
then `𝒳 ⟶ 𝒴` is locally quasi-finite.

The argument is the source's. `f : 𝒳 ⟶ 𝒴` factors as the graph `Γ_f : 𝒳 ⟶ 𝒳 ×_𝒵 𝒴` followed by
the second projection `𝒳 ×_𝒵 𝒴 ⟶ 𝒴`. The projection is a base change of `f ≫ g` along `g`, so
it is locally quasi-finite by **Stacks 06UB**. The graph is locally quasi-finite in the sense of
Properties of Stacks, Section 04XB because `g` is quasi-DM (**Stacks 050I**, part (3)), and it
is representable by algebraic spaces (**Stacks 050I**, part (1)), so **Stacks 06UA** upgrades
that to local quasi-finiteness in the sense of **Stacks 06PU**. **Stacks 06UD** composes the
two, and `f` is 2-isomorphic to the composite.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_of_iso`: local quasi-finiteness
  of a 1-morphism of algebraic stacks depends on it only up to 2-isomorphism.
* `...isLocallyQuasiFinite_graph_of_isQuasiDM`: the graph of `f` over `𝒵` is locally
  quasi-finite in the sense of **Stacks 06PU** when `g` is quasi-DM.
* `...isLocallyQuasiFinite_of_comp_of_isQuasiDM`: **Stacks 06UG**.

## Implementation notes

`isLocallyQuasiFinite_of_iso` is obtained without a separate invariance argument: a 1-morphism
2-isomorphic to `f'` is a base change of `f'` along the identity, because reindexing the second
leg of the cospan `(𝟙 𝒴, f)` of `CategoryTheory.Bicategory.TwoCommSq.idCospan` along the
2-isomorphism leaves the apex and the first projection untouched. **Stacks 06UB** then applies
verbatim. This is the shape of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_iso` in
`StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation`, which handles the same mismatch in
the properness cancellation of Stacks 0CPT.

No hypothesis beyond those of the source is carried: the factorisation through the graph, the
base change, the invariance under 2-isomorphism and the composition of **Stacks 06UD** are all
proved.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
* [Stacks Project, Tag 06UD](https://stacks.math.columbia.edu/tag/06UD)
* [Stacks Project, Tag 06UG](https://stacks.math.columbia.edu/tag/06UG)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Local quasi-finiteness of a 1-morphism of algebraic stacks over `S` depends on the
1-morphism only up to 2-isomorphism.** Reindexing the second leg of the cospan `(𝟙 𝒴, f)` of
`CategoryTheory.Bicategory.TwoCommSq.idCospan` along a 2-isomorphism `f ≅ f'` exhibits `f` as
the first projection of a 2-fibre product of the cospan `(𝟙 𝒴, f')`, that is as a base change
of `f'`, so **Stacks 06UB** gives the conclusion. -/
theorem isLocallyQuasiFinite_of_iso {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf' : IsLocallyQuasiFinite B S hS f') :
    IsLocallyQuasiFinite B S hS f :=
  isLocallyQuasiFinite_baseChange B S hS f' (𝟙 𝒴)
    ((Bicategory.TwoCommSq.idCospan f).reindexSnd e)
    (Bicategory.isTwoFibreProduct_reindexSnd e (Bicategory.isTwoFibreProduct_idCospan f)) hf'

/-- **The graph of `f : 𝒳 ⟶ 𝒴` over `𝒵` is locally quasi-finite when `g : 𝒴 ⟶ 𝒵` is quasi-DM.**
It is locally quasi-finite in the sense of Properties of Stacks, Section 04XB by **Stacks 050I**
part (3) and representable by algebraic spaces by part (1) of that tag, so **Stacks 06UA**
identifies that with local quasi-finiteness in the sense of **Stacks 06PU**. -/
theorem isLocallyQuasiFinite_graph_of_isQuasiDM (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hg : IsQuasiDM B S hS g) :
    IsLocallyQuasiFinite B S hS (Stack.graph B S hS f (f ≫ g) g (Iso.refl _)) :=
  isLocallyQuasiFinite_of_isLocallyQuasiFinite_hom B S hS
    (Stack.graph B S hS f (f ≫ g) g (Iso.refl _))
    (Stack.isRepresentableByAlgebraicSpaces_graph B S hS f (f ≫ g) g (Iso.refl _))
    (Stack.isLocallyQuasiFinite_graph B S hS f (f ≫ g) g (Iso.refl _) hg)

/-- **Stacks 06UG.** If a composite of 1-morphisms of algebraic stacks over `S` is locally
quasi-finite and its second factor is quasi-DM, then its first factor is locally quasi-finite.

`f` is 2-isomorphic to its graph over `𝒵` followed by the second projection of the canonical
2-fibre product of the cospan `(f ≫ g, g)`. The graph is locally quasi-finite because `g` is
quasi-DM (**Stacks 050I** part (3) and **Stacks 06UA**), the projection is a base change of
`f ≫ g` and so is locally quasi-finite by **Stacks 06UB**, and **Stacks 06UD** composes the
two. -/
@[stacks 06UG]
theorem isLocallyQuasiFinite_of_comp_of_isQuasiDM
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsLocallyQuasiFinite B S hS (f ≫ g)) (hg : IsQuasiDM B S hS g) :
    IsLocallyQuasiFinite B S hS f := by
  have hsnd : IsLocallyQuasiFinite B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).snd :=
    isLocallyQuasiFinite_baseChange B S hS (f ≫ g) g
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).swap
      (Bicategory.isTwoFibreProduct_swap
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g))
      hfg
  exact isLocallyQuasiFinite_of_iso B S hS
    (Stack.graph_snd_iso B S hS f (f ≫ g) g (Iso.refl _))
    (isLocallyQuasiFinite_comp B S hS
      (Stack.graph B S hS f (f ≫ g) g (Iso.refl _))
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).snd
      (isLocallyQuasiFinite_graph_of_isQuasiDM B S hS f g hg) hsnd)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
