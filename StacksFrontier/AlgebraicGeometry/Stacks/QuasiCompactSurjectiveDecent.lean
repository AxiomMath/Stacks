module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Decency of the target of a quasi-compact surjection of algebraic stacks (Stacks 0GW4)

An algebraic stack over `S` is *decent* (**Stacks 0GW1**) when every one of its points admits a
field-valued representative whose 1-morphism `Spec k ⟶ 𝒳` is quasi-compact. This file proves
**Stacks 0GW4**: if `f : 𝒳 ⟶ 𝒴` is quasi-compact (**Stacks 050U**) and surjective
(**Stacks 04ZS**) and `𝒳` is decent, then `𝒴` is decent.

The only condition on the decency ladder that occurs is *decent* itself, on both sides; no
reasonableness or quasi-separatedness hypothesis appears, and there is no finite-type condition
of any kind — the hypotheses on `f` are exactly quasi-compactness and surjectivity.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_fieldValuedPointMap`: the image of a
  field-valued point under a 1-morphism is quasi-compact as soon as the composite of the point's
  own 1-morphism with that 1-morphism is quasi-compact.
* `AlgebraicGeometry.Stack.isDecent_of_isQuasiCompactMorphism_of_isSurjective`: **Stacks 0GW4**.

## Implementation notes

Both reductions the source performs are already discharged by the shape the library gives its
notions, so the argument is two steps long.

Surjectivity needs no conversion. The source passes from surjectivity of `f` to the statement
that every point of `|𝒴|` is the image of a field-valued point of `𝒳` through Properties of
Stacks, Lemma **Stacks 04XI**, which identifies surjectivity of a 1-morphism representable by
algebraic spaces with surjectivity of the map on points. For a 1-morphism of algebraic stacks
that is not assumed representable, surjectivity *is* surjectivity of the map on points
(**Stacks 04ZS**, `AlgebraicGeometry.Stack.IsSurjective`), so the hypothesis is applied
directly to the point of `𝒴` under consideration.

Quasi-compactness of the image point is the composition property. The source tests
quasi-compactness of `y = f ∘ x` against an affine scheme `T ⟶ 𝒴` using
`T ×_{𝒴, y} Spec(k) = (T ×_𝒴 𝒳) ×_{𝒳, x} Spec(k)` and the fppf descent of **Stacks 0DTL**. That
computation is exactly the proof of **Stacks 050W**, the composition property of quasi-compact
1-morphisms, which is already available as
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_comp`; so quasi-compactness of the image point
is obtained by composing the 1-morphism of the representative with `f`, with no separate appeal
to Stacks 0DTL.

The image point is produced by `AlgebraicGeometry.Stack.fieldValuedPointMap`, which keeps the
base of the point and moves only its object, and its 1-morphism is identified with the composite
by `AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso` — naturality of the 2-Yoneda lift
in the stack. That identification is an isomorphism of based functors rather than an equality, so
quasi-compactness and representability are transported across it by
`AlgebraicGeometry.Stack.isQuasiCompact_congr_basedIso` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_basedIso`, which are **Stacks 0459**
and **Stacks 0457** at identity horizontal 1-morphisms; the passage between the Stacks 04XB form
of quasi-compactness that the decency predicate asks for and the Stacks 050U form that the
permanence lemmas are stated in is **Stacks 050T**.

**No appeal to Stacks 0DTK is made, and none is needed.** The source reads decency of `𝒳` at an
arbitrary field-valued point and then uses the independence of the representative; here the
representative of the image point is *constructed* from the one `𝒳`'s decency hands over, so only
the existential form of `AlgebraicGeometry.Stack.IsDecent` is used, in both directions.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 0DTL](https://stacks.math.columbia.edu/tag/0DTL)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW4](https://stacks.math.columbia.edu/tag/0GW4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The image of a field-valued point under a 1-morphism of algebraic stacks is quasi-compact
as soon as the composite is.** If `p` is a field-valued point of `𝒳` and the composite of the
1-morphism `Spec k ⟶ 𝒳` it determines with `f : 𝒳 ⟶ 𝒴` is quasi-compact in the sense of
Stacks 050U, then the field-valued point `f ∘ p` of `𝒴` is quasi-compact in the sense of
Stacks 04XB, which is the form the decency predicate of Stacks 0GW1 asks for.

The 1-morphism of `f ∘ p` is isomorphic to that composite by naturality of the 2-Yoneda lift
(`AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso`), and quasi-compactness and
representability by algebraic spaces are invariant under such an isomorphism (**Stacks 0459**
and **Stacks 0457**); the two forms of quasi-compactness are matched by **Stacks 050T**. -/
theorem isQuasiCompactFieldValuedPoint_fieldValuedPointMap
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (h : IsQuasiCompactMorphism.{u, w} B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p ≫ f)) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒴.val
      (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p) := by
  have hrep := isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism B S hS 𝒴
    (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p)
  have hrep' := isRepresentableByAlgebraicSpaces_of_basedIso B S hS _ _
    (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p).symm hrep
  refine (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒴 _).2 ?_
  refine (isQuasiCompact_iff_baseChange_quasiCompact B S hS _ hrep).1 ?_
  exact isQuasiCompact_congr_basedIso B S hS
    (fieldValuedPointStackMorphism B S hS 𝒳 p ≫ f).hom _
    (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p) hrep' hrep
    ((isQuasiCompact_iff_baseChange_quasiCompact B S hS _ hrep').2 h)

/-- **Stacks 0GW4.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If `f` is
quasi-compact and surjective and `𝒳` is decent, then `𝒴` is decent.

Let `y` be a point of `𝒴`. Surjectivity of `f` is surjectivity of the map on points
(**Stacks 04ZS**), so `y` is the image of a point `x` of `𝒳`, and decency of `𝒳` supplies a
field-valued representative `p` of `x` whose 1-morphism `Spec k ⟶ 𝒳` is quasi-compact
(**Stacks 050T**). The image field-valued point `f ∘ p` has the same base, represents `y`, and
its 1-morphism is the composite of that of `p` with `f`, hence quasi-compact by **Stacks 050W**.
-/
@[stacks 0GW4]
theorem isDecent_of_isQuasiCompactMorphism_of_isSurjective
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsQuasiCompactMorphism.{u, w} B S hS f)
    (hsurj : IsSurjective.{u, w} B S hS f)
    (h𝒳 : IsDecent B S hS 𝒳.val) :
    IsDecent B S hS 𝒴.val := by
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  obtain ⟨p, hp, hpqc⟩ := h𝒳 x
  refine ⟨fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p, ?_, ?_⟩
  · rw [← hx, ← hp]
    rfl
  · exact isQuasiCompactFieldValuedPoint_fieldValuedPointMap B S hS f p
      (isQuasiCompactMorphism_comp B S hS _ f
        ((isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 p).1 hpqc) hf)

end AlgebraicGeometry.Stack

end
