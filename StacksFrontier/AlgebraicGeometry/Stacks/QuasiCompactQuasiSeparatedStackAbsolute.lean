module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase

/-!
# Morphisms out of quasi-compact and quasi-separated algebraic stacks, absolutely (Stacks 075S)

**Stacks 075S** is stated for algebraic stacks over an arbitrary base scheme `S`, with
quasi-separatedness of an algebraic stack read *absolutely*: quasi-separated over `Spec ℤ`
(**Stacks 050D** part (8)). This file states the three parts that way, with separation as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyQuasiSeparated` and no hypothesis on `S`;
the argument `hZ`, that the site contains the terminal scheme, is the parameter of that absolute
notion. These are the declarations registered for the tag.

`StacksFrontier/AlgebraicGeometry/Stacks/QuasiCompactQuasiSeparatedStack.lean` proves the relative
variant, with the separation conditions read over `S` as
`AlgebraicGeometry.Stack.IsQuasiSeparatedOver` (**Stacks 050D** part (4)) and under the hypothesis
`QuasiSeparatedSpace S`. That hypothesis is needed for the relative reading: its proof of part (1)
cancels the structure morphism to `S`, and quasi-compactness of that morphism for a quasi-compact
algebraic stack is compactness of `W ×_S V` for affine objects `W`, `V` of the site, which fails
over a base scheme that is not quasi-separated. The source's products are over `Spec ℤ` instead.
The source's `Spec ℤ` is the terminal scheme `⊤_ Scheme`, which is affine and hence
quasi-separated unconditionally, so the relative statement applies *there* with nothing to assume,
and the conclusion is carried back to `S`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_absolute`:
  **Stacks 075S**, part (1).
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_and_isQuasiSeparated_absolute`:
  **Stacks 075S**, part (2).
* `AlgebraicGeometry.Stack.isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct`:
  **Stacks 075S**, part (3).

## Implementation notes

Part (1) is the one part that changes base. Quasi-compactness of a 1-morphism is **Stacks 050U**,
the condition that every base change of it by a quasi-compact algebraic stack is quasi-compact, so
the statement to be carried from the terminal scheme back to `S` is quasi-compactness of a
2-fibre product. Two results do that, and nothing else is needed:

* `AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv`, an equivalence of categories, identifies
  the 2-fibre product of the views with the view of the 2-fibre product, so
  `AlgebraicGeometry.Stack.isQuasiCompactStack_of_essSurj` transports quasi-compactness between
  them;
* `AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff` descends it from the
  view to the 2-fibre product itself.

Parts (2) and (3) then never leave `S`. Part (2) adds quasi-separatedness of the 1-morphism, which
comes from **Stacks 050N** part (4),
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`,
feeding the over-the-base statement
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver`. Part (3) is the
relative proof verbatim with its last step replaced: the projection to `𝒵` is a base change of the
1-morphism, hence quasi-compact and quasi-separated, quasi-compactness of its source is
`AlgebraicGeometry.Stack.isQuasiCompactStack_of_isQuasiCompactMorphism`, and **Stacks 050L**
part (8), `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`,
carries absolute quasi-separatedness from `𝒵` to the apex where the relative proof used part (4).

That last substitution is what makes the absolute statement usable where the relative one was: the
conclusion of part (3) is an input to part (1) at the next application, and part (1) asks for the
absolute condition on its target.

The views of the two 1-morphisms are produced by the hom-bijection of **Stacks 04X5**,
`AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv`, exactly as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isDM`;
`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose, so no
identification of sources or targets is needed.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The 1-morphism of views over the terminal scheme that the hom-bijection of **Stacks 04X5**
assigns to a 1-morphism of algebraic stacks over `S`. -/
noncomputable abbrev viewOverIntegersHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.viewOverIntegers.{u, w} B S hS hZ 𝒳 ⟶
      AlgebraicStacks.viewOverIntegers.{u, w} B S hS hZ 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (algebraicStackConstructionHomEquiv.{u, w} B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 𝒴 f).val

/-- **Quasi-compactness of a 2-fibre product descends from the terminal scheme to `S`.** The
2-fibre product of the views of a cospan over the terminal scheme is identified with the view of
the 2-fibre product by `AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv`, which is an
equivalence of categories, and quasi-compactness descends along a view by
`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff`. -/
theorem isQuasiCompactStack_twoFibreProductAlgebraicStack_of_viewOverIntegers
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (k : 𝒴 ⟶ 𝒵)
    (h : IsQuasiCompactStack.{u, w} B (⊤_ Scheme.{u}) hZ
      (twoFibreProductAlgebraicStack B (⊤_ Scheme.{u}) hZ
        (viewOverIntegersHom.{u, w} B S hS hZ f) (viewOverIntegersHom.{u, w} B S hS hZ k)).val
      (twoFibreProductAlgebraicStack B (⊤_ Scheme.{u}) hZ
        (viewOverIntegersHom.{u, w} B S hS hZ f)
        (viewOverIntegersHom.{u, w} B S hS hZ k)).property) :
    IsQuasiCompactStack.{u, w} B S hS (twoFibreProductAlgebraicStack B S hS f k).val
      (twoFibreProductAlgebraicStack B S hS f k).property := by
  refine (isQuasiCompactStack_changeBaseAlgebraicStack_iff.{u, w} B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)
    (twoFibreProductAlgebraicStack B S hS f k)).1 ?_
  have hess : (changeBaseTwoFibreProductInv B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒵.val 𝒳.val 𝒴.val f.hom.hom
      k.hom.hom).toFunctor.EssSurj := by
    have := isEquivalence_changeBaseTwoFibreProductInv B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒵.val 𝒳.val 𝒴.val f.hom.hom k.hom.hom
    infer_instance
  exact @isQuasiCompactStack_of_essSurj B (⊤_ Scheme.{u}) hZ
    (twoFibreProductAlgebraicStack B (⊤_ Scheme.{u}) hZ
      (viewOverIntegersHom.{u, w} B S hS hZ f) (viewOverIntegersHom.{u, w} B S hS hZ k))
    (changeBaseAlgebraicStack B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) (twoFibreProductAlgebraicStack B S hS f k))
    (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (changeBaseTwoFibreProductInv B S (⊤_ Scheme.{u}) hS hZ
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒵.val 𝒳.val 𝒴.val f.hom.hom k.hom.hom)))
    hess h

/-- **Stacks 075S, part (1).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks with `𝒳` quasi-compact
and `𝒴` quasi-separated in the absolute sense of Stacks 050D part (8) is quasi-compact. Nothing is
asked of the base scheme of the big fppf site.

Quasi-compactness of a 1-morphism is Stacks 050U, so what has to be shown is quasi-compactness of
each base change of `f` by a quasi-compact algebraic stack. Over the terminal scheme the relative
statement `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack` applies with no
hypothesis — the terminal scheme is affine, hence quasi-separated — to the views of `f` and of the
test stack, whose quasi-compactness is
`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff`; and
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_twoFibreProductAlgebraicStack_of_viewOverIntegers` brings the resulting
quasi-compact 2-fibre product back to `S`. -/
@[stacks 075S "part (1)", sga "4 VI 1.14" "(i), algebraic stacks"]
theorem isQuasiCompactMorphism_of_isQuasiCompactStack_absolute
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒴 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒴) :
    IsQuasiCompactMorphism.{u, w} B S hS f := by
  intro 𝒵 k h𝒵
  have hview := fun 𝒲 => (isQuasiCompactStack_changeBaseAlgebraicStack_iff.{u, w} B S
    (⊤_ Scheme.{u}) hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒲).2
  refine isQuasiCompactStack_twoFibreProductAlgebraicStack_of_viewOverIntegers.{u, w}
    B S hS hZ k f ?_
  exact isQuasiCompactMorphism_of_isQuasiCompactStack.{u, w} B (⊤_ Scheme.{u}) hZ inferInstance
    (viewOverIntegersHom.{u, w} B S hS hZ f) (hview 𝒳 h𝒳) h𝒴
    (AlgebraicStacks.viewOverIntegers.{u, w} B S hS hZ 𝒵)
    (viewOverIntegersHom.{u, w} B S hS hZ k) (hview 𝒵 h𝒵)

/-- **Stacks 075S, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks with `𝒳` quasi-compact
and quasi-separated and `𝒴` quasi-separated, both in the absolute sense of Stacks 050D part (8),
is quasi-compact and quasi-separated.

Quasi-compactness is part (1). Quasi-separatedness is Stacks 050N part (8), whose two inputs are
the over-the-base readings of the two absolute hypotheses, supplied by Stacks 050N part (4). -/
@[stacks 075S "part (2)", sga "4 VI 1.14" "(i), stacks, X also qs"]
theorem isQuasiCompactMorphism_and_isQuasiSeparated_absolute
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (h𝒴 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒴) :
    IsQuasiCompactMorphism.{u, w} B S hS f ∧
      AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS f :=
  ⟨isQuasiCompactMorphism_of_isQuasiCompactStack_absolute.{u, w} B S hS hZ f h𝒳qc h𝒴,
    AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS f
      (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒳 h𝒳qs)
      (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒴 h𝒴).2⟩

/-- **Stacks 075S, part (3).** A 2-fibre product `𝒳 ×_𝒴 𝒵` of algebraic stacks, with `𝒳`, `𝒵`
quasi-compact and quasi-separated and `𝒴` quasi-separated, all in the absolute sense of
Stacks 050D part (8), is quasi-compact and quasi-separated in that same absolute sense. Nothing is
asked of the base scheme of the big fppf site.

The projection to `𝒵` is a base change of `f`, which is quasi-compact and quasi-separated by
part (2), hence is itself quasi-compact (Stacks 050V) and quasi-separated (Stacks 050F). A
quasi-compact 1-morphism into the quasi-compact `𝒵` has quasi-compact source, and Stacks 050L
part (8) carries absolute quasi-separatedness from `𝒵` to the apex.

The absolute conclusion is what the next application of part (1) needs of its target, which the
over-the-base conclusion of
`AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct` is not. -/
@[stacks 075S "part (3)"]
theorem isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProduct
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (h𝒵qc : IsQuasiCompactStack.{u, w} B S hS 𝒵.val 𝒵.property)
    (h𝒵qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒵)
    (h𝒴 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒴) :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductAlgebraicStack B S hS f g).property ∧
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ
        (twoFibreProductAlgebraicStack B S hS f g) := by
  obtain ⟨hfqc, hfqs⟩ := isQuasiCompactMorphism_and_isQuasiSeparated_absolute.{u, w} B S hS hZ
    f h𝒳qc h𝒳qs h𝒴
  have hprojqc : IsQuasiCompactMorphism.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isQuasiCompactMorphism_baseChange B S hS f g
      (twoFibreProductSquareAlgebraicStacks B S hS f g).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)) hfqc
  have hprojqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    AlgebraicStacks.isQuasiSeparated_baseChange B S hS f g hfqs
  exact ⟨isQuasiCompactStack_of_isQuasiCompactMorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd hprojqc h𝒵qc,
    AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd h𝒵qs hprojqs⟩

end AlgebraicGeometry.Stack

end
