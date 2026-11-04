module

public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal closedness and properness cancel a separated second factor (Stacks 0CPT)

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S` and suppose `𝒴 ⟶ 𝒵` is separated
(**Stacks 04YW**). This file proves **Stacks 0CPT**: if the composite `𝒳 ⟶ 𝒵` is universally
closed then `𝒳 ⟶ 𝒴` is universally closed and its image in `|𝒴|` is closed, and if the
composite is proper then `𝒳 ⟶ 𝒴` is proper.

The argument is the one of the source. `f : 𝒳 ⟶ 𝒴` factors as the graph `𝒳 ⟶ 𝒳 ×_𝒵 𝒴` followed
by the second projection `𝒳 ×_𝒵 𝒴 ⟶ 𝒴`. The graph is proper in the sense of Stacks 04XB because
`g` is separated (**Stacks 050I**, part (4)), hence universally closed there, hence universally
closed as a 1-morphism of algebraic stacks by **Stacks 0512**. The projection is the base change
of `f ≫ g` along `g`, so it is universally closed by **Stacks 0514**, and **Stacks 0515**
composes the two. Properness adds separatedness by **Stacks 050M** part (3), local finite type
by **Stacks 06U9** and quasi-compactness by **Stacks 050Y**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_comp_of_isSeparated`:
  **Stacks 0CPT**, the universal closedness of part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_range_of_comp_of_isSeparated`:
  **Stacks 0CPT**, the closed image of part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_comp_of_isSeparated`: **Stacks 0CPT**,
  part (2).

## Implementation notes

Two facts about universal closedness that the source uses silently are isolated first.
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_iso` transports the condition
along a 2-isomorphism of the 1-morphism, which is needed because the factorisation through the
graph reproduces `f` only up to the 2-isomorphism
`AlgebraicGeometry.Stack.graph_snd_iso`; it is
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` followed by
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr`, since reindexing the second leg of a
cospan leaves the apex and the first projection untouched.
`AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_universallyClosed` specialises the
universal condition to the identity base change, recognised as a 2-fibre product by
`CategoryTheory.Bicategory.isTwoFibreProduct_idCospan`.

The hypothesis of Stacks 050M part (3) is separatedness of `Δ_g` in the sense of Stacks 04XB,
while separatedness of `g` is properness of `Δ_g` in that sense; the passage between them is
`AlgebraicGeometry.Stack.isSeparated_of_isProper`, the first projection of properness of a
morphism of algebraic spaces.

## References

* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 0514](https://stacks.math.columbia.edu/tag/0514)
* [Stacks Project, Tag 0515](https://stacks.math.columbia.edu/tag/0515)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 06U9](https://stacks.math.columbia.edu/tag/06U9)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CPT](https://stacks.math.columbia.edu/tag/0CPT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is proper
in the sense of Stacks 04XB is separated in that sense: properness of a morphism of algebraic
spaces includes separatedness, and the two conditions are quantified over the same data. -/
theorem isSeparated_of_isProper
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsProper B S hS f) : IsSeparated B S hS f :=
  fun U y hy F hF hEq => (hf U y hy F hF hEq).1

namespace AlgebraicStacks

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- Closedness of the first projection transfers between any two 2-fibre products of a cospan of
algebraic stacks over `S`. -/
private theorem isClosed_fst_of_isTwoFibreProduct {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    {g : 𝒲 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P Q : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q) (h : IsClosed B S hS P.fst) : IsClosed B S hS Q.fst :=
  Stack.isClosedMap_pointsMap_fst_congr B S hS P.underlying Q.underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _ hP)
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _ hQ) h

/-- Universal closedness of a 1-morphism of algebraic stacks over `S` depends on the 1-morphism
only up to 2-isomorphism. -/
theorem universallyClosed_of_iso {f f' : 𝒳 ⟶ 𝒴} (e : f ≅ f')
    (hf : UniversallyClosed B S hS f) : UniversallyClosed B S hS f' := fun 𝒲 g =>
  isClosed_fst_of_isTwoFibreProduct B S hS
    ((Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).reindexSnd e)
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f')
    (Bicategory.isTwoFibreProduct_reindexSnd e
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f))
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f') (hf 𝒲 g)

/-- A universally closed 1-morphism of algebraic stacks over `S` is closed: it is its own base
change along the identity of its target. -/
theorem isClosed_of_universallyClosed (f : 𝒳 ⟶ 𝒴) (hf : UniversallyClosed B S hS f) :
    IsClosed B S hS f :=
  isClosed_fst_of_isTwoFibreProduct B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f) (Bicategory.TwoCommSq.idCospan f)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f)
    (Bicategory.isTwoFibreProduct_idCospan f) (hf 𝒴 (𝟙 𝒴))

/-- The graph of `f : 𝒳 ⟶ 𝒴` over `𝒵` is universally closed as a 1-morphism of algebraic stacks
when `g : 𝒴 ⟶ 𝒵` is separated: it is proper in the sense of Stacks 04XB by **Stacks 050I**
part (4), hence universally closed there, and **Stacks 0512** identifies that with universal
closedness of Stacks 0513 for a 1-morphism representable by algebraic spaces. -/
theorem universallyClosed_graph_of_isSeparated (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hg : IsSeparated B S hS g) :
    UniversallyClosed B S hS (Stack.graph B S hS f (f ≫ g) g (Iso.refl _)) :=
  (Stack.representable_universallyClosed_iff_closedMap_baseChange B S hS
      (Stack.graph B S hS f (f ≫ g) g (Iso.refl _))
      (Stack.isRepresentableByAlgebraicSpaces_graph B S hS f (f ≫ g) g (Iso.refl _))).mp
    (Stack.universallyClosed_of_isProper B S hS _
      (Stack.isProper_graph B S hS f (f ≫ g) g (Iso.refl _) hg))

/-- **Stacks 0CPT, part (1).** If a composite of 1-morphisms of algebraic stacks over `S` is
universally closed and its second factor is separated, then its first factor is universally
closed.

`f` is 2-isomorphic to its graph over `𝒵` followed by the second projection of the canonical
2-fibre product of the cospan `(f ≫ g, g)`. The graph is universally closed because `g` is
separated, the projection is the base change of `f ≫ g` along `g` and so is universally closed
by **Stacks 0514**, and **Stacks 0515** composes them. -/
@[stacks 0CPT "part (1): universal closedness", ega "II 5.4.9" "5.4.3 univ. closed"]
theorem universallyClosed_of_comp_of_isSeparated (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : UniversallyClosed B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    UniversallyClosed B S hS f :=
  universallyClosed_of_iso B S hS
    (Stack.graph_snd_iso B S hS f (f ≫ g) g (Iso.refl _)).symm
    (universallyClosed_comp B S hS _ _
      (universallyClosed_graph_of_isSeparated B S hS f g hg)
      (universallyClosed_baseChange_of_isTwoFibreProduct B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).swap
        (Bicategory.isTwoFibreProduct_swap
          (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g))
        hfg))

/-- **Stacks 0CPT, part (1).** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_comp_of_isSeparated` the image of
`|𝒳|` in `|𝒴|` is closed for the topology of Stacks 04XL. -/
@[stacks 0CPT "part (1): closed image"]
theorem isClosed_range_of_comp_of_isSeparated (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : UniversallyClosed B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    @_root_.IsClosed _ (Stack.pointTopology B S hS 𝒴.val)
      (Set.range (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)) :=
  let := Stack.pointTopology B S hS 𝒳.val
  let := Stack.pointTopology B S hS 𝒴.val
  (isClosed_of_universallyClosed B S hS f
    (universallyClosed_of_comp_of_isSeparated B S hS f g hfg hg)).isClosed_range

/-- **Stacks 0CPT, part (2).** If a composite of 1-morphisms of algebraic stacks over `S` is
proper and its second factor is separated, then its first factor is proper.

Properness of **Stacks 0CL5** is separatedness, finite type and universal closedness. The first
is **Stacks 050M** part (3), whose hypothesis on `Δ_g` is separatedness in the sense of
Stacks 04XB and follows from the properness of `Δ_g` that separatedness of `g` asserts. Finite
type is local finite type, which cancels outright by **Stacks 06U9**, together with
quasi-compactness, which cancels against the quasi-separatedness of `g` by **Stacks 050Y**.
Universal closedness is part (1). -/
@[stacks 0CPT "part (2): properness"]
theorem isProper_of_comp_of_isSeparated (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsProper B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsProper B S hS f :=
  ⟨isSeparated_of_comp_of_isSeparated_diagonal B S hS f g hfg.1
      (Stack.isSeparated_of_isProper B S hS _ hg),
    ⟨isLocallyOfFiniteType_of_comp B S hS f g hfg.2.1.1,
      Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS f g hfg.2.1.2
        (isQuasiSeparated_of_isSeparated B S hS hg)⟩,
    universallyClosed_of_comp_of_isSeparated B S hS f g hfg.2.2 hg⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
