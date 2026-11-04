module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Quasi-compact field-valued points of an algebraic stack

A field-valued point of an algebraic stack `𝒳` over `S` determines, by the 2-Yoneda lemma, a
1-morphism `Spec k → 𝒳`, and Stacks 0GW1 calls `𝒳` *decent* when every point of `𝒳` has a
representative whose 1-morphism is quasi-compact in the sense of Stacks 04XB. This file supplies
the two things a consumer of that predicate needs and cannot get from its definition: the
representability witness it quantifies over, and the identification of its quantifier with
quasi-compactness of a 1-morphism of algebraic stacks in the sense of Stacks 050U, along which
the permanence properties Stacks 050V, 050W and 050Y become available.

It also records three facts about quasi-compact algebraic stacks used on that route and stated
for their own sake: the stack represented by the final object of the big fppf site of `S` is
*strictly* terminal, the algebraic stack of a quasi-compact scheme over `S` is quasi-compact, and
quasi-compactness of a 2-fibre product descends along a pair of surjective 1-morphisms.

## Main definitions

* `AlgebraicGeometry.Stack.fieldValuedPointStackMorphism`: the 1-morphism a field-valued point
  determines, read in the 2-category of algebraic stacks over `S` rather than in the ambient
  2-category of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.eq_structureMorphism`: every 1-morphism to the algebraic stack
  represented by the final object of the big fppf site of `S` *is* the structure morphism of
  Stacks 050D.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack`: the algebraic stack of a
  quasi-compact scheme over `S` is quasi-compact, and
  `AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine` at an affine one.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProduct_of_isSurjective_of_isSurjective`:
  quasi-compactness of a 2-fibre product descends along a pair of surjective 1-morphisms.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism`: the
  1-morphism of a field-valued point of an algebraic stack is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_isQuasiCompact`: the quantifier of
  `AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint` is the Stacks 04XB property at
  quasi-compactness of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism`: it is
  equivalently quasi-compactness of that 1-morphism in the sense of Stacks 050U.

## Implementation notes

`AlgebraicGeometry.Stack.eq_structureMorphism` is a strict statement and not merely a 2-cell: a
1-morphism to the stack of `S/S` is a based functor whose composite with the forgetful functor of
that slice is the structure functor of its source, and the iterated-slice equivalence of
Stacks 03EH is strict, so the underlying functor is determined. Consequently quasi-compactness of
the structure morphism in the sense of Stacks 050U says exactly that every 2-fibre product of
`𝒳` with a quasi-compact algebraic stack over the final stack is quasi-compact, with no
quantifier over the test 1-morphism left.

`AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack` compares the two models of a scheme as
an algebraic stack — the slice of the site and the category of elements of the presheaf it
represents — by `AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence`, and transports
compactness of the point space along the *inverse* of that equivalence through
`AlgebraicGeometry.Stack.isQuasiCompactStack_of_essSurj`, which needs only essential
surjectivity of the underlying functor. The affine corollary is formally redundant and is kept
because it is the form in which a field-valued point supplies it, its base being identified with
a field spectrum by `AlgebraicGeometry.Stack.FieldValuedPoint.isSpec`.

`AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProduct_of_isSurjective_of_isSurjective` is
proved from Stacks 02XD in the 2-category of algebraic stacks — twice, once for each factor —
together with Stacks 04ZT, Stacks 04ZU and the invariance
`AlgebraicGeometry.Stack.isQuasiCompactStack_of_isTwoFibreProduct` of quasi-compactness across
the 2-fibre products of one cospan. Each of the two steps writes the relevant iterated apex as a
2-fibre product of the outer cospan, moves quasi-compactness onto it, and then surjects it onto
the apex one step down along a base change of the given surjection; applications of
`CategoryTheory.Bicategory.TwoCommSq.swap` reconcile the order of the cospans, the cancellation
consuming its cospans in the opposite order to the one Stacks 04ZU projects from.

The representability witness is not new mathematics: it is the basic consequence of Stacks 045G
recorded as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`, at the source
`AlgebraicGeometry.Stack.schemeFibredCategory` of a field-valued point's base, which is
representable by an algebraic space by Stacks 04SV. It is stated here because
`AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint` quantifies over exactly that witness and
every consumer has to produce it.

`AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_isQuasiCompact` is `Iff.rfl` and
carries no hypothesis on the property, unlike
`AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_hasRelativeProperty`, which has to
take the missing fppf-locality instance for quasi-compactness of morphisms of algebraic spaces as
a hypothesis. The two record the same observation from opposite sides: the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` does not use its instance arguments, so the
written-out predicate of `StacksFrontier/AlgebraicGeometry/Stacks/DecentStack.lean` is the Stacks
04XB property on the nose.

Three of the seven imports are cosmetic and are retained deliberately. `StacksDraft.
AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces`, `...Stacks.
SmoothPresentationQuasiCompact` and `...Stacks.StructureMorphism` already lie in the import
closure of the other four, so the closure is the same with and without them and the signatures of
all eight declarations below are byte-identical under `pp.universes` together with `pp.fullNames`
whether they are present, absent individually, or absent jointly. They are kept because this
module names `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`,
`AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence` and
`AlgebraicGeometry.Stack.structureMorphism` by hand, and an import that documents where a named
ingredient comes from is worth more than the line it costs.

No declaration here carries a `@[stacks]` attribute. Each is an instance or an auxiliary of a tag
already registered elsewhere — Stacks 045G at a represented source, Stacks 050T at the 1-morphism
of a field-valued point, Stacks 04YB at a represented stack, Stacks 02XD at the level of algebraic
stacks — and registering a tag on an instantiation of its own general form would invert the ruling
that put Stacks 06TS's six keys on instantiated declarations rather than on the general
Stacks 06NW theorem they come from.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The final algebraic stack over `S` -/

/-- **The algebraic stack represented by the final object of the big fppf site of `S` is strictly
terminal.** Every 1-morphism to it is the structure morphism of Stacks 050D of its source.

A 1-morphism to the stack of `S/S` has as its only datum a functor whose composite with the
forgetful functor of that slice is the structure functor of the source; the iterated-slice
equivalence at the identity of `S` is strict, so that functor is the structure functor read
through its inverse, which is what the structure morphism is. -/
theorem eq_structureMorphism (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (g : 𝒵 ⟶ schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :
    g = structureMorphism B S hS 𝒵 := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedCategory.BasedFunctor.ext'
  obtain ⟨P, hP⟩ : ∃ P : 𝒵.val.val.obj ⥤ BigFppfOver B S hS,
      P ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))) = g.hom.hom.toFunctor :=
    ⟨_, Over.comp_iteratedSliceForward_comp_iteratedSliceBackward
      (Over.mk (𝟙 (B.obj hS))) g.hom.hom.toFunctor⟩
  have hw := g.hom.hom.w
  rw [← hP] at hw ⊢
  have hassoc :
      (P ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS)))) ⋙
          Over.forget (Over.mk (𝟙 (B.obj hS))) =
        P ⋙ (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))) ⋙
          Over.forget (Over.mk (𝟙 (B.obj hS)))) :=
    Functor.assoc _ _ _
  have hP' : P = 𝒵.val.val.p := by
    refine Eq.trans ?_ hw
    refine Eq.trans ?_ hassoc.symm
    rw [Over.iteratedSliceBackward_mk_id_comp_forget, Functor.comp_id]
  rw [hP']
  rfl

/-! ### Quasi-compactness of represented algebraic stacks -/

/-- **The algebraic stack of a quasi-compact scheme over `S` is quasi-compact.** The category of
elements of the presheaf the scheme represents is quasi-compact because that presheaf is a
quasi-compact algebraic space, and the inverse of
`AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence` carries quasi-compactness from it to
the slice of the site, being an equivalence and in particular essentially surjective. -/
theorem isQuasiCompactStack_schemeStack (T : BigFppfOver B S hS)
    (hT : Space.IsQuasiCompactSpace B S hS (yoneda.obj T)) :
    IsQuasiCompactStack.{u, w} B S hS (schemeStack.{u, w} B S hS T).val
      (schemeStack.{u, w} B S hS T).property := by
  have hAlg : IsAlgebraicStack.{u, w} B S hS (fibredCategory B S hS (yoneda.obj T)).val :=
    isAlgebraicStack_fibredCategory.{u, w} B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)
  have h1 : IsQuasiCompactStack.{u, w} B S hS (fibredCategory B S hS (yoneda.obj T)) hAlg :=
    isQuasiCompactStack_fibredCategory.{u, w} B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) hT hAlg
  let e := schemeFibredCategoryEquivalence B S hS T
  let 𝒰' : AlgebraicStacks.{u, w} B S hS := ⟨fibredCategory B S hS (yoneda.obj T), hAlg⟩
  let F : 𝒰' ⟶ schemeStack.{u, w} B S hS T :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom e.inverse)
  have : F.hom.hom.toFunctor.EssSurj := by
    have : F.hom.hom.toFunctor.IsEquivalence :=
      e.symm.equiv.isEquivalence_functor
    infer_instance
  exact isQuasiCompactStack_of_essSurj B S hS F h1

/-- **The algebraic stack of an affine scheme over `S` is quasi-compact.** The identity is an
affine, surjective, étale cover of the presheaf it represents, so that presheaf is a
quasi-compact algebraic space. -/
theorem isQuasiCompactStack_schemeStack_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactStack.{u, w} B S hS (schemeStack.{u, w} B S hS T).val
      (schemeStack.{u, w} B S hS T).property :=
  isQuasiCompactStack_schemeStack.{u, w} B S hS T
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT)

/-! ### Descent of quasi-compactness of a 2-fibre product -/

/-- Quasi-compactness of a 2-fibre product of algebraic stacks is symmetric in the cospan. -/
private theorem isQuasiCompactStack_twoFibreProduct_swap
    {𝒴 𝒵 𝒰 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴) (f : 𝒰 ⟶ 𝒴)
    (h : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS g f).val
      (twoFibreProductAlgebraicStack B S hS g f).property) :
    IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS f g).val
      (twoFibreProductAlgebraicStack B S hS f g).property :=
  isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g) h

/-- Quasi-compactness of the 2-fibre product of `(g, b ≫ f)` for a surjective `b` gives that of
`(g, f)`. -/
private theorem isQuasiCompactStack_twoFibreProduct_of_isSurjective_right
    {𝒴 𝒵 𝒰 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒰 ⟶ 𝒴) (b : 𝒲 ⟶ 𝒰) (hb : IsSurjective B S hS b)
    (h : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS g (b ≫ f)).val
      (twoFibreProductAlgebraicStack B S hS g (b ≫ f)).property) :
    IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS g f).val
      (twoFibreProductAlgebraicStack B S hS g f).property := by
  have h1 := isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g (b ≫ f))
    (isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS g f b (b ≫ f) (Iso.refl _)) h
  exact isQuasiCompactStack_of_isSurjective B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g f).snd b).fst h1
    (isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS g f).snd b).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS g f).snd b)) hb)

/-- **Quasi-compactness of a 2-fibre product of algebraic stacks over `S` descends along a pair of
surjective 1-morphisms.** If `a : 𝒱 ⟶ 𝒵` and `b : 𝒲 ⟶ 𝒰` are surjective and the 2-fibre product
of the cospan `(a ≫ g, b ≫ f)` is quasi-compact, then so is the 2-fibre product of `(g, f)`.

Stacks 02XD identifies the iterated apex `(𝒱 ×_𝒴 𝒰) ×_𝒰 𝒲` with a 2-fibre product of
`(a ≫ g, b ≫ f)`, so the hypothesis transports onto it; its projection to `𝒱 ×_𝒴 𝒰` is a base
change of `b`, hence surjective, which gives quasi-compactness of `𝒱 ×_𝒴 𝒰`. The same two steps
with `a` in place of `b` give quasi-compactness of `𝒰 ×_𝒴 𝒵`, and exchanging the cospan once
more gives it for `𝒵 ×_𝒴 𝒰`. -/
theorem isQuasiCompactStack_twoFibreProduct_of_isSurjective_of_isSurjective
    {𝒴 𝒵 𝒰 𝒱 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒰 ⟶ 𝒴) (a : 𝒱 ⟶ 𝒵) (b : 𝒲 ⟶ 𝒰)
    (ha : IsSurjective B S hS a) (hb : IsSurjective B S hS b)
    (h : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS (a ≫ g) (b ≫ f)).val
      (twoFibreProductAlgebraicStack B S hS (a ≫ g) (b ≫ f)).property) :
    IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS g f).val
      (twoFibreProductAlgebraicStack B S hS g f).property :=
  isQuasiCompactStack_twoFibreProduct_swap B S hS f g
    (isQuasiCompactStack_twoFibreProduct_of_isSurjective_right B S hS f g a ha
      (isQuasiCompactStack_twoFibreProduct_swap B S hS (a ≫ g) f
        (isQuasiCompactStack_twoFibreProduct_of_isSurjective_right B S hS (a ≫ g) f b hb h)))

/-! ### The 1-morphism of a field-valued point -/

/-- **The 1-morphism a field-valued point of an algebraic stack determines, read in the 2-category
of algebraic stacks over `S`.** Its source is the algebraic stack of the point's base, which is an
algebraic stack by Stacks 04X5 at a represented object. -/
noncomputable def fieldValuedPointStackMorphism (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    schemeStack.{u, w} B S hS p.base ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (fieldValuedPointMorphism B S hS 𝒳.val p)

/-- **The 1-morphism of a field-valued point of an algebraic stack is representable by algebraic
spaces.** Its source is representable by an algebraic space (Stacks 04SV) and the diagonal of its
target is representable by algebraic spaces, which is the third clause of algebraicity; this is
the consequence of Stacks 045G the conventions of Properties of Stacks, Section 04XB use without
further mention. -/
theorem isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsRepresentableByAlgebraicSpaces B S hS
      (fieldValuedPointMorphism B S hS 𝒳.val p).hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base) _

/-- **Quasi-compactness of a field-valued point is the Stacks 04XB property at quasi-compactness
of morphisms of algebraic spaces.** Unlike
`AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_hasRelativeProperty` this needs no
locality hypothesis on the property, because
`AlgebraicGeometry.Stack.IsQuasiCompact` is itself the written-out quantifier. -/
theorem isQuasiCompactFieldValuedPoint_iff_isQuasiCompact
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒳 p ↔
      ∃ _hf : IsRepresentableByAlgebraicSpaces B S hS
          (fieldValuedPointMorphism B S hS 𝒳 p).hom,
        IsQuasiCompact B S hS (fieldValuedPointMorphism B S hS 𝒳 p) :=
  Iff.rfl

/-- **Quasi-compactness of a field-valued point of an algebraic stack is quasi-compactness of its
1-morphism in the sense of Stacks 050U.** The representability witness the predicate quantifies
over is always available, and Stacks 050T converts the Stacks 04XB property of a representable
1-morphism into the condition that its base change by every quasi-compact algebraic stack is
quasi-compact.

This is the form in which the permanence properties Stacks 050V, 050W and 050Y apply to a
field-valued point, and hence the form in which decency (Stacks 0GW1) is reached from a
separation property of the structure morphism. -/
theorem isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p ↔
      IsQuasiCompactMorphism.{u, w} B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) :=
  let hf := isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism.{u, w} B S hS 𝒳 p
  ⟨fun h => (isQuasiCompact_iff_baseChange_quasiCompact.{u, w} B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) hf).1 h.2,
    fun h => ⟨hf, (isQuasiCompact_iff_baseChange_quasiCompact.{u, w} B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) hf).2 h⟩⟩

end AlgebraicGeometry.Stack

end
