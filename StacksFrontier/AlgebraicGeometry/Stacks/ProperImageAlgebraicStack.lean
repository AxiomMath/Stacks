module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedPoints
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# A surjective image of a universally closed algebraic stack (Stacks 0CQK)

Let `f : 𝒳 ⟶ 𝒴` and `q : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If the composite
`f ≫ q` is universally closed in the sense of **Stacks 0513** and `f` is surjective
(**Stacks 04ZS**), then `q` is universally closed; if moreover `q` is separated
(**Stacks 04YW**) and of finite type (**Stacks 06FS**), then `q` is proper (**Stacks 0CL5**).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_surjective_comp`: **Stacks 0CQK**,
  universal closedness of the image.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_surjective_universallyClosed_comp`:
  **Stacks 0CQK**, properness of the image.

## Implementation notes

The source's argument is the set-theoretic identity `p'((f')^{-1}(T)) = q'(T)` for the base
changes along a test 1-morphism `g : 𝒵' ⟶ 𝒵`. Three library facts turn it into a proof.

* The base change `𝒵' ×_𝒵 𝒳 ⟶ 𝒵' ×_𝒵 𝒴` of `f` is the first projection of the canonical
  2-fibre product square of the cospan `((𝒵' ×_𝒵 𝒴) ⟶ 𝒴, f)`, and it is surjective by
  **Stacks 04ZU** (`AlgebraicGeometry.Stack.isSurjective_of_isTwoFibreProduct`) read on the
  exchanged square `CategoryTheory.Bicategory.TwoCommSq.swap`, since that lemma concludes about
  the projection away from the surjective leg.
* The composite of that projection with `(𝒵' ×_𝒵 𝒴) ⟶ 𝒵'` is the first projection of the
  iterated 2-fibre product, which is a 2-fibre product of the outer cospan `(g, f ≫ q)` by
  **Stacks 02XD** at the level of algebraic stacks
  (`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks`).
* Universal closedness of `f ≫ q` is stated at the *canonical* square of that cospan, and
  `AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr` transfers closedness on points
  between any two 2-fibre products of one cospan, so the hypothesis applies to the iterated apex.
  It is a statement about categories fibred in groupoids, and
  `AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_algebraicStacks` supplies the two
  2-fibre-product witnesses it needs at that level.

With those three, the remaining step is the elementary observation that a map is closed as soon
as its precomposition with a continuous surjection is; `f ≫ q` and the surjectivity of `f` enter
nowhere else.

Import minimality is assessed in this module-system file and not in a plain-`import` probe. Two
of the seven imports are removable *individually* at exit 0 with the signature byte-identical
under `pp.universes` and `pp.fullNames` taken in one scope, and removing both *jointly* is also
exit 0 with the identical signature; both are retained, `StacksCore.Tactic.StacksAttribute` because
every module registering a tag imports it explicitly, and
`StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties` because it is where this library's
permanence results about surjectivity live. The two names the argument uses by hand,
`AlgebraicGeometry.Stack.isSurjective_of_isTwoFibreProduct` and
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp`, are in
`StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange` and
`StacksFrontier.AlgebraicGeometry.Stacks.Surjective`, both reached through
`StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack`.

The second result is the conjunction `AlgebraicGeometry.Stack.AlgebraicStacks.IsProper` of
**Stacks 0CL5**, two of whose three conjuncts are among its hypotheses, so it is the first result
paired with them. Both results are stated for an arbitrary 1-morphism of algebraic stacks, not
only for one representable by algebraic spaces, exactly as `IsProper` is.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 0CL5](https://stacks.math.columbia.edu/tag/0CL5)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A map is closed as soon as its precomposition with a continuous surjection is closed: the
image of a closed set is the image of its preimage along the surjection. -/
private theorem isClosedMap_of_comp_of_surjective {A C D : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [TopologicalSpace D] {a : A → C} {b : C → D}
    (ha : Continuous a) (hsurj : Function.Surjective a)
    (h : IsClosedMap (b ∘ a)) : IsClosedMap b := by
  intro T hT
  have himg : b '' T = (b ∘ a) '' (a ⁻¹' T) := by
    rw [Set.image_comp, Set.image_preimage_eq _ hsurj]
  rw [himg]
  exact h _ (hT.preimage ha)

/-- **Stacks 0CQK, universal closedness of the image.** If the composite `f ≫ q` of 1-morphisms
of algebraic stacks over `S` is universally closed and `f` is surjective, then `q` is universally
closed. -/
@[stacks 0CQK "universally closed image"]
theorem universallyClosed_of_surjective_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : UniversallyClosed B S hS (f ≫ q)) (hf : Stack.IsSurjective B S hS f) :
    UniversallyClosed B S hS q := by
  intro 𝒵' g
  have hDfp := Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS g q f (f ≫ q)
    (Iso.refl _)
  have hDclosed := Stack.isClosedMap_pointsMap_fst_congr B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ q)).underlying
    (Stack.cancelSndSquareAlgebraicStacks B S hS g q f (f ≫ q) (Iso.refl _)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ q)))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _ hDfp) (hp 𝒵' g)
  set A := Stack.twoFibreProductSquareAlgebraicStacks B S hS g q with hA
  set C := Stack.twoFibreProductSquareAlgebraicStacks B S hS A.snd f with hC
  have hCfst : Stack.IsSurjective B S hS C.fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS _
      (Bicategory.isTwoFibreProduct_swap
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS A.snd f)) hf
  refine @isClosedMap_of_comp_of_surjective _ _ _
    (Stack.pointTopology B S hS C.pt.val) (Stack.pointTopology B S hS A.pt.val)
    (Stack.pointTopology B S hS 𝒵'.val)
    (Stack.pointsMap B S hS C.pt.val.val C.pt.val.property A.pt.val.property C.fst.hom.hom)
    (Stack.pointsMap B S hS A.pt.val.val A.pt.val.property 𝒵'.val.property A.fst.hom.hom)
    (Stack.continuous_pointsMap B S hS C.pt.val A.pt.val C.fst.hom.hom) hCfst ?_
  rw [← Stack.AlgebraicStacks.pointsMap_comp B S hS C.fst A.fst]
  exact hDclosed

/-- **Stacks 0CQK, properness of the image.** If the composite `f ≫ q` of 1-morphisms of
algebraic stacks over `S` is universally closed, `f` is surjective and `q` is separated and of
finite type, then `q` is proper. -/
@[stacks 0CQK "properness of the image", ega "II 5.4.3" "(ii)"]
theorem isProper_of_surjective_universallyClosed_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : UniversallyClosed B S hS (f ≫ q)) (hf : Stack.IsSurjective B S hS f)
    (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    IsProper B S hS q :=
  ⟨hsep, hft, universallyClosed_of_surjective_comp B S hS f q hp hf⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
