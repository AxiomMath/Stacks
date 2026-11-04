module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Universal injectivity descends along a surjective cover (Stacks 0DTP)

**Stacks 0DTP** says that universal injectivity of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` may be checked after base change along a surjective, flat, locally finitely presented
1-morphism from (the stack of) an algebraic space onto `𝒴`.

## Main results

* `AlgebraicGeometry.Stack.universallyInjective_of_isSurjective_baseChange`: the descent itself,
  for an arbitrary surjective 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.universallyInjective_of_fppfCover`: **Stacks 0DTP**, the form of the
  source.

## Implementation notes

**Only surjectivity of the cover is used.** Flatness and local finite presentation are what the
source needs for the *other* characterisation of universal injectivity, through geometric points
(Stacks 0CPN part (3)); the characterisation by the relative diagonal, parts (1) and (2), makes
them unnecessary. `AlgebraicGeometry.Stack.universallyInjective_of_isSurjective_baseChange` is
therefore stated without them, and with an arbitrary algebraic stack in place of the stack of an
algebraic space, and `AlgebraicGeometry.Stack.universallyInjective_of_fppfCover` records the
source's statement as an immediate consequence.

The proof is a chain of three 2-fibre products over a test 1-morphism `d : 𝒵 ⟶ 𝒴`, with `g` the
cover, `Q := 𝒲 ×_𝒴 𝒳` the given base change and `F := 𝒵 ×_𝒴 𝒳` the one to be shown injective on
points:

* `C := 𝒲 ×_𝒴 𝒵`, whose projection to `𝒵` is surjective because `g` is (**Stacks 04ZU**);
* `T := C ×_𝒲 Q`, whose projection to `C` is injective on points because it is a base change of
  `Q.fst` and that morphism is universally injective by hypothesis;
* `E := C ×_𝒵 F`, whose projection to `C` is what the last step consumes.

`T` and `E` are then the *same* 2-fibre product. Pasting (`Bicategory.isTwoFibreProduct_pasteFst`)
exhibits `T` as a 2-fibre product of the cospan `(C.fst ≫ g, f)` and `E` as one of
`(C.snd ≫ d, f)`, and those two cospans differ exactly by the filler `C.iso` of `C` — not on the
nose. Reindexing along it (`Bicategory.isTwoFibreProduct_reindexFst`) puts both over one cospan,
where `AlgebraicGeometry.Stack.injective_pointsMap_fst_of_isTwoFibreProduct` transports
injectivity from one to the other; pasting keeps the first projection untouched, so the
injectivity transported is exactly that of `E.fst`.

The last step descends injectivity from `E.fst` to `F.fst`
(`AlgebraicGeometry.Stack.injective_pointsMap_of_isSurjective_of_isTwoFibreProduct`): two points
of `F` with a common image in `|𝒵|` are lifted, through a point of `C` over that image, to two
points of `E` over one point of `C` by **Stacks 04XH**, which injectivity of `E.fst` then
identifies.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0DTP](https://stacks.math.columbia.edu/tag/0DTP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Injectivity on points descends along a surjective leg of a cospan.** If `E` is a 2-fibre
product of `(c, h)` whose first projection is injective on points and `c` is surjective, then `h`
is injective on points: two points of the source of `h` with a common image lift, through a point
of the source of `c` over that image (**Stacks 04XH**), to two points of `E` sharing a first
projection. -/
theorem injective_pointsMap_of_isSurjective_of_isTwoFibreProduct
    {𝒞 𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} {c : 𝒞 ⟶ 𝒵} {h : 𝒳 ⟶ 𝒵}
    (E : Bicategory.TwoCommSq c h) (hE : Bicategory.IsTwoFibreProduct E)
    (hc : IsSurjective B S hS c)
    (hfst : Function.Injective (AlgebraicStacks.pointsMap B S hS E.fst)) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS h) := by
  intro x₁ x₂ hx
  obtain ⟨p, hp⟩ := hc (AlgebraicStacks.pointsMap B S hS h x₁)
  obtain ⟨e₁, he₁, he₁'⟩ :=
    AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS E hE p x₁ hp
  obtain ⟨e₂, he₂, he₂'⟩ :=
    AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS E hE p x₂ (hp.trans hx)
  rw [← he₁', ← he₂', hfst (he₁.trans he₂.symm)]

/-- **Universal injectivity descends along a surjective 1-morphism of algebraic stacks.** If
`g : 𝒲 ⟶ 𝒴` is surjective and the first projection of the canonical 2-fibre product
`𝒲 ×_𝒴 𝒳` is universally injective, then `f : 𝒳 ⟶ 𝒴` is universally injective.

This is **Stacks 0DTP** with neither flatness nor local finite presentation of the cover, and
with an arbitrary algebraic stack in place of the stack of an algebraic space; see the
implementation notes of this file. -/
theorem universallyInjective_of_isSurjective_baseChange
    {𝒳 𝒴 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴)
    (hg : IsSurjective B S hS g)
    (hgf : UniversallyInjective B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS g f).fst) :
    UniversallyInjective B S hS f := by
  intro 𝒵 d P hP
  set Q := AlgebraicStacks.twoFibreProductSquare B S hS g f with hQdef
  set C := AlgebraicStacks.twoFibreProductSquare B S hS g d with hCdef
  set F := AlgebraicStacks.twoFibreProductSquare B S hS d f with hFdef
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g f
  have hC := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS g d
  have hF := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS d f
  set E := AlgebraicStacks.twoFibreProductSquare B S hS C.snd F.fst with hEdef
  set T := AlgebraicStacks.twoFibreProductSquare B S hS C.fst Q.fst with hTdef
  have hE := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS C.snd F.fst
  have hT := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS C.fst Q.fst
  -- `T` is a 2-fibre product of `(C.fst ≫ g, f)`, and `E` one of `(C.snd ≫ d, f)`; the two
  -- cospans are identified by the filler of `C`, so reindexing puts both over the first.
  have hEpaste : Bicategory.IsTwoFibreProduct
      ((F.pasteFst E).reindexFst C.iso.symm) :=
    Bicategory.isTwoFibreProduct_reindexFst C.iso.symm
      (Bicategory.isTwoFibreProduct_pasteFst F hF E hE)
  have hTpaste : Bicategory.IsTwoFibreProduct (Q.pasteFst T) :=
    Bicategory.isTwoFibreProduct_pasteFst Q hQ T hT
  -- stated at the reindexed pasted square, whose first projection *is* `E.fst`; annotating it
  -- as such instead would make the elaborator pick `E` for the lemma's implicit square
  have hEinj := injective_pointsMap_fst_of_isTwoFibreProduct B S hS hEpaste hTpaste
    (hgf C.pt C.fst T hT)
  exact injective_pointsMap_fst_of_isTwoFibreProduct B S hS hP hF
    (injective_pointsMap_of_isSurjective_of_isTwoFibreProduct B S hS E hE
      (isSurjective_of_isTwoFibreProduct B S hS C hC hg) hEinj)

/-- **Stacks 0DTP.** Universal injectivity of a 1-morphism of algebraic stacks over `S` can be
checked after base change along a surjective, flat, locally finitely presented 1-morphism from
the stack of an algebraic space onto its target.

Only surjectivity of the cover is used; see
`AlgebraicGeometry.Stack.universallyInjective_of_isSurjective_baseChange`. -/
@[stacks 0DTP, ega "IV 11.9.14" "fppf descent clause"]
theorem universallyInjective_of_fppfCover
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (hgSurj : IsSurjective B S hS g)
    (_hgFlat : AlgebraicStacks.IsFlat B S hS g)
    (_hgLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hgf : UniversallyInjective B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS g f).fst) :
    UniversallyInjective B S hS f :=
  universallyInjective_of_isSurjective_baseChange B S hS f g hgSurj hgf

end AlgebraicGeometry.Stack

end
