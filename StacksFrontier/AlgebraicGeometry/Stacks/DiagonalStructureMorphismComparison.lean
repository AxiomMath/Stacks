module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalFunctoriality

/-!
# The absolute diagonal as the relative diagonal of the structure morphism

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`. The absolute
diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` has as its target the 2-fibre product of `𝒳` with itself over the final
object of the 2-category of categories fibred in groupoids over the big fppf site of `S`, namely
the site with the identity as structure functor. The relative diagonal of the structure
1-morphism of **Stacks 050D** has as its target the 2-fibre product over the algebraic stack
represented by `S` itself, namely the big fppf site of the *identity* of `S`. Both base stacks
are final, and the 1-morphism identifying them is the iterated-slice equivalence of **Stacks
03EH**; so the two diagonals differ exactly by postcomposing both legs of the product with that
equivalence, which is `CategoryTheory.TwoFibreProductOver.mapBase`.

This file records that comparison and transports the relative property of **Stacks 03YK** across
it: the absolute diagonal of `𝒳` has a property `P` if and only if the relative diagonal of the
structure 1-morphism of `𝒳` does.

## Main definitions

* `AlgebraicGeometry.Stack.productToTwoFibreProductStructureMorphism`: the comparison 1-morphism
  from `𝒳 × 𝒳` to the 2-fibre product of `𝒳` with itself over the algebraic stack represented by
  `S`.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_productToTwoFibreProductStructureMorphism`: the
  comparison 1-morphism is an equivalence.
* `AlgebraicGeometry.Stack.relativeDiagonal_structureMorphism_eq_comp`: the relative diagonal of
  the structure 1-morphism is the absolute diagonal followed by the comparison.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonal_algebraicStack`: the
  absolute diagonal of an algebraic stack is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_iff_relativeDiagonal_structureMorphism`:
  the two diagonals have the same relative properties.
* `AlgebraicGeometry.Stack.relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism`: the
  same equivalence with the relative property written out as the quantifier of Stacks 03YK, which
  needs no hypothesis on `P` and so applies to the conditions of Properties of Stacks, Section
  04XB — the ones the separation axioms over the base of Stacks 050D are stated with.

## Implementation notes

No declaration here carries a `@[stacks]` attribute: the comparison is an identification of two
spellings of one 1-morphism and asserts no key of the source. Stacks 050D's own part keys are
predicates *about* the structure 1-morphism and are formalized elsewhere.

The factorization is `CategoryTheory.TwoFibreProductOver.diagonal_comp_mapBase` read at the
structure functor of `𝒳` as the 1-morphism into the final object and at the inverse of the
iterated-slice equivalence as the change of target. Its hypothesis
`(H ⋙ b) ⋙ p𝒟 = q𝒮` is supplied by the `CategoryTheory.BasedFunctor.w` field of the structure
1-morphism itself, so the composite leg `H ⋙ b` is the structure 1-morphism on the nose and no
transport of the target 2-fibre product intervenes. The `CategoryTheory.BasedFunctor.w` field of
the comparison is `rfl`, because `CategoryTheory.TwoFibreProductOver.mapBase` preserves the base
object and the base morphism of an object and of a morphism of a 2-fibre product.

`AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalences` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` are applied with
their two `CategoryTheory.Functor.IsEquivalence` arguments given explicitly rather than
synthesised, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia`: the sources and targets
are spelled through `AlgebraicGeometry.Stack.twoFibreProduct` and
`CategoryTheory.CatFiberedInGroupoids.product`, which are `def`s, so instance search does not see
through to the `CategoryTheory.TwoFibreProductOver` the comparison is defined on. For the same
reason full faithfulness of the iterated-slice equivalence is introduced by a `have` stated at
the spelling `CategoryTheory.Over.iteratedSliceBackward`.

`AlgebraicGeometry.Stack.diagonal` and `AlgebraicGeometry.Stack.relativeDiagonal` are written
`.{u, u, u + 1}` at every term occurrence, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia`: without the pin their three
universe arguments are not determined by the explicit arguments.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The comparison 1-morphism `𝒳 × 𝒳 ⟶ 𝒳 ×_S 𝒳`.** Postcomposition of both legs of the product
of an algebraic stack with itself with the inverse of the iterated-slice equivalence of `S`, which
turns the 2-fibre product over the final object of the 2-category into the 2-fibre product over
the algebraic stack represented by `S` along the structure 1-morphism of Stacks 050D. -/
noncomputable def productToTwoFibreProductStructureMorphism :
    (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val ⥤ᵇ
      (twoFibreProduct B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        𝒳.val 𝒳.val (structureMorphism.{u, w} B S hS 𝒳).hom.hom
        (structureMorphism.{u, w} B S hS 𝒳).hom.hom).val where
  toFunctor :=
    TwoFibreProductOver.mapBase (pT := 𝒳.val.val.p) (p𝒜 := 𝒳.val.val.p)
      𝒳.val.val.p 𝒳.val.val.p (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
      (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))
  w := rfl

/-- **The comparison 1-morphism is an equivalence**, the iterated-slice equivalence of Stacks
03EH being one and `CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` asking only for
full faithfulness of the change of target. -/
theorem isEquivalence_productToTwoFibreProductStructureMorphism :
    Functor.IsEquivalence
      (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳).toFunctor :=
  have _hb : (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS)))).IsEquivalence :=
    (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).isEquivalence_inverse
  TwoFibreProductOver.isEquivalence_mapBase
    (pT := 𝒳.val.val.p) (p𝒜 := 𝒳.val.val.p)
    (G := 𝒳.val.val.p) (F := 𝒳.val.val.p)
    (b := Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
    (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))

/-- **The relative diagonal of the structure 1-morphism is the absolute diagonal followed by the
comparison 1-morphism.** Both send an object `x` of `𝒳` to the triple `(x, x, φ)` with `φ` an
identity, read through the inverse of the iterated-slice equivalence on one side. -/
theorem relativeDiagonal_structureMorphism_eq_comp :
    BasedFunctor.comp (BasedFunctor.id 𝒳.val.val)
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
          (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
          (structureMorphism.{u, w} B S hS 𝒳).hom).hom =
      BasedFunctor.comp (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom
        (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳) :=
  BasedCategory.BasedFunctor.ext'
    (TwoFibreProductOver.diagonal_comp_mapBase (Functor.comp_id 𝒳.val.val.p)
      (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))
      (structureMorphism.{u, w} B S hS 𝒳).hom.hom.w).symm

private instance isEquivalence_id_toFunctor :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))

private instance isEquivalence_comparison_toFunctor :
    Functor.IsEquivalence
      (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳).toFunctor :=
  isEquivalence_productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳

/-- **The absolute diagonal of an algebraic stack over `S` is representable by algebraic
spaces.** The relative diagonal of the structure 1-morphism is, by Stacks 04XS part (1), and the
two are identified by an equivalence of the targets, across which Stacks 0457 carries
representability. -/
theorem isRepresentableByAlgebraicSpaces_diagonal_algebraicStack :
    IsRepresentableByAlgebraicSpaces B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
      (structureMorphism.{u, w} B S hS 𝒳).hom).hom
    (BasedFunctor.id 𝒳.val.val)
    (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳)
    (eqToIso (relativeDiagonal_structureMorphism_eq_comp.{u, w} B S hS 𝒳))
    ).mp
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks.{u, w} B S hS
      (structureMorphism.{u, w} B S hS 𝒳))

/-- **The absolute diagonal and the relative diagonal of the structure 1-morphism have the same
relative properties.** For a property `P` of morphisms of algebraic spaces over `S` which is
stable under base change and local at the target for the fppf precoverage, the absolute diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` of an algebraic stack over `S` has `P` in the sense of Stacks 03YK if and only
if the relative diagonal of the structure 1-morphism of Stacks 050D does.

This is Stacks 0459 applied along the identity of `𝒳` and the comparison 1-morphism
`AlgebraicGeometry.Stack.productToTwoFibreProductStructureMorphism`, whose 2-commutativity datum
is the equality `AlgebraicGeometry.Stack.relativeDiagonal_structureMorphism_eq_comp`. -/
theorem hasRelativeProperty_diagonal_iff_relativeDiagonal_structureMorphism
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (h₁ : IsRepresentableByAlgebraicSpaces B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom)
    (h₂ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism.{u, w} B S hS 𝒳).hom).hom) :
    HasRelativeProperty B S hS P (diagonal.{u, u, u + 1} B S hS 𝒳.val) h₁ ↔
      HasRelativeProperty B S hS P
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
          (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
          (structureMorphism.{u, w} B S hS 𝒳).hom) h₂ :=
  (hasRelativeProperty_iff_of_equivalences B S hS P
    (diagonal.{u, u, u + 1} B S hS 𝒳.val)
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
      (structureMorphism.{u, w} B S hS 𝒳).hom)
    (BasedFunctor.id 𝒳.val.val)
    (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳)
    (eqToIso (relativeDiagonal_structureMorphism_eq_comp.{u, w} B S hS 𝒳))
    h₂).symm

/-- **The absolute diagonal and the relative diagonal of the structure 1-morphism satisfy the
condition of Properties of Stacks, Section 04XB for the same properties `P`.** This is
`AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_iff_relativeDiagonal_structureMorphism` with
the relative property of Stacks 03YK written out as a quantifier, so that no hypothesis on `P` and
no representability witness is needed; it is the form in which the separation axioms of Stacks
04YW — and hence the properties of an algebraic stack over its base of Stacks 050D — are stated.
-/
theorem relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism
    (P : MorphismProperty (AlgebraicSpaces B S hS)) :
    (∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.obj)
      (_hy : y ⋙ (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p y
            (CatFiberedInGroupoids.homFunctor (diagonal.{u, u, u + 1} B S hS 𝒳.val)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
            𝒳.val 𝒳.val (structureMorphism.{u, w} B S hS 𝒳).hom.hom
            (structureMorphism.{u, w} B S hS 𝒳).hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS
            (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
            𝒳.val 𝒳.val (structureMorphism.{u, w} B S hS 𝒳).hom.hom
            (structureMorphism.{u, w} B S hS 𝒳).hom.hom).val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
              (twoFibreProduct B S hS
                (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
                𝒳.val 𝒳.val (structureMorphism.{u, w} B S hS 𝒳).hom.hom
                (structureMorphism.{u, w} B S hS 𝒳).hom.hom).val.p y
              (CatFiberedInGroupoids.homFunctor
                (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
                  (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
                  (structureMorphism.{u, w} B S hS 𝒳).hom)))
            (presheafOfCategories (F ⋙ typeToCat)).p) →
          P (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  ⟨relativeProperty_of_equivalences_symm B S hS P
      (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism.{u, w} B S hS 𝒳).hom).hom
      (BasedFunctor.id 𝒳.val.val)
      (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳)
      (eqToIso (relativeDiagonal_structureMorphism_eq_comp.{u, w} B S hS 𝒳)),
    relativeProperty_of_equivalences B S hS P
      (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism.{u, w} B S hS 𝒳).hom).hom
      (BasedFunctor.id 𝒳.val.val)
      (productToTwoFibreProductStructureMorphism.{u, w} B S hS 𝒳)
      (eqToIso (relativeDiagonal_structureMorphism_eq_comp.{u, w} B S hS 𝒳))⟩

end AlgebraicGeometry.Stack

end
