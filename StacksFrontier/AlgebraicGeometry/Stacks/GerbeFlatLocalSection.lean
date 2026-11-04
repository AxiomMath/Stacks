module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeFactorisationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingCoverReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation

/-!
# The fppf-local flat section of a gerbe (the route of Stacks 06QI)

**Stacks 06QI** asserts three properties of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
which exhibits `𝒳` as a gerbe over `𝒴` (**Stacks 06QC**): it is surjective, flat, and locally of
finite presentation. Surjectivity is `AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver`, and
the remaining two are
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`.
This file supplies, unconditionally, the fppf-local section along which the source's own proof
runs, so that `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isGerbeOver` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isGerbeOver` apply to
every gerbe.

The source argues fppf-locally on `𝒴`: by **Stacks 06QH** (1) `⟹` (2) there is a surjective,
flat, locally finitely presented 1-morphism `g : 𝒰 ⟶ 𝒴` after which `f` acquires a section, and
by **Stacks 06QG** part (3) that section is surjective, flat and locally of finite presentation;
a 1-morphism admitting a surjective flat section is flat (**Stacks 06Q0**) and, the section being
moreover locally of finite presentation, locally of finite presentation (**Stacks 06Q9**), and
both properties descend along `g` by **Stacks 06PZ** and **Stacks 06Q8**. The two descent steps
are `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_section` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_section` in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation`.

## The fppf-local section, and why it is now available

The input the source takes from Stacks 06QH and Stacks 06QG is assembled here out of two halves
which the library proves separately.

*The section exists.* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_snd_of_isGerbeOver`
produces an object `U` of the site and a surjective, flat, locally finitely presented
`g : 𝒰 ⟶ 𝒴` out of the algebraic stack of `U` for which *every* 2-fibre product of the cospan
`(f, g)` — in particular the canonical one of **Stacks 04T2** — has a section of its projection to
`𝒰`. Its proof needs neither a coproduct of algebraic stacks nor the descent of an object of `𝒳`:
the covering family the gerbe condition produces is gathered inside a smooth *scheme* atlas of
`𝒳`, where an object of a fibre is an arrow of the site.

*The section is flat and locally of finite presentation.* The base change of `f` along `g` is
again a gerbe (**Stacks 06QE**), so this is the flatness-and-local-finite-presentation half of
Stacks 06QG part (3) for a gerbe over the algebraic stack of an object of the site. It is reached
without the converse half of Stacks 06PL — hence without Stacks 06PK, Stacks 06PJ and Stacks 06FI,
which the library carries only under hypotheses — by the route of
`Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_factorisation`:
`AlgebraicGeometry.Stack.exists_single_cover_section_factorisation_of_isGerbeOver` produces a
surjective, flat, locally finitely presented `q : 𝒱 ⟶ 𝒳` out of the algebraic stack of an object
`V` of the site together with a factorisation `γ ≫ x = q` of it through the section `x`, and that
theorem then runs **Stacks 06NR** along the triangle `𝒱 ×_𝒳 𝒱 ⟶ 𝒱 ×_𝒳 𝒰 ⟶ 𝒱` and descends along
`q` by Stacks 06PZ and Stacks 06Q8.

## Reading the three 2-fibre products as algebraic spaces

The Stacks 06NR step is a statement about morphisms of presheaves carrying
`AlgebraicGeometry.IsAlgebraicSpace`, so
`isFlat_and_isLocallyOfFinitePresentation_of_factorisation` asks for its three objects `𝒱 ×_𝒳 𝒱`,
`𝒱 ×_𝒳 𝒰` and `𝒱` to be presented that way: a presheaf, its algebraicity, and a
`StacksRepresentableCFG.EquivalenceOver` identifying it with the stack. Supplying those three data
is all that separates the two halves above from Stacks 06QI, and it is what this file adds.

For `𝒱` itself the datum is **Stacks 04SV** for a slice of the site,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`. For the two
2-fibre products it is **Stacks 0300**,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`: the apex of a
2-fibre product square is represented by an algebraic space as soon as one leg of the cospan is
representable by algebraic spaces and the source of the other is represented by an algebraic
space. The source of the other leg is `𝒱` in both cases, and the legs `q : 𝒱 ⟶ 𝒳` and
`x : 𝒰 ⟶ 𝒳` are representable by algebraic spaces because their sources are the algebraic stacks
of objects of the site and `𝒳` is an algebraic stack: that is condition (3) of **Stacks 045G**,
reached from the diagonal clause of algebraicity, which is condition (1), through the
equivalences (1) `⇔` (2) `⇔` (3).

Note that this is the *absolute* representability of Stacks 04SV and Stacks 02ZW, not the relative
property of Stacks 03YK; `AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange`
(**Stacks 04XC**) is a different statement and is not used.

## Main results

* `Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`:
  a section of a gerbe over an algebraic space is flat and locally of finite presentation. With
  the surjectivity of `AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver` this is
  **Stacks 06QG** part (3).
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_flatLfpSection_of_isGerbeOver`: fppf-locally on
  the target a gerbe has a section which is flat and locally of finite presentation. This is
  **Stacks 06QH** (1) `⟹` (2) combined with the previous item, and it is the input Stacks 06QI
  takes from them.

## Implementation notes

The section is read at the *canonical* 2-fibre product of Stacks 04T2, which is the square at
which the library's Stacks 06Q8 reads its own hypothesis; its leg exchange is a 2-fibre product of
the reversed cospan (`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), which is the form
Stacks 06PZ takes. Carrying one square for both descents avoids comparing two apexes of the same
cospan.

`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct` is stated at the
universe pattern at which the 2-category of categories fibred in groupoids is closed under
forming the 2-fibre product; the 2-category of algebraic stacks of Stacks 03YP sits at
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, which is that pattern at `v := u`
and `w := u + 1`. The apex of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` is the apex of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` by definition, so the square the
representability statement is applied to is the underlying one and nothing is transported.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (3) of Stacks 045G for an algebraic stack**: every 1-morphism into an algebraic
stack over `S` from the algebraic stack of an object of the site is representable by algebraic
spaces. The diagonal clause of algebraicity is condition (1), and the two equivalences
(1) `⇔` (2) `⇔` (3) are proved. -/
private theorem isRepresentableFromSchemes_of_algebraicStack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Stack.IsRepresentableFromSchemes B S hS 𝒳.val := by
  obtain ⟨hfib, hstack, hdiag, hpresentation⟩ := 𝒳.property
  exact (Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳.val).1
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).1 hdiag)

/-- **Stacks 0300 for the canonical 2-fibre product of a cospan of algebraic stacks whose first
leg has the algebraic stack of an object of the site as its source.** The apex is represented by
an algebraic space over `S`: the source of the first leg is, by **Stacks 04SV** for a slice of the
site, and the second leg is assumed representable by algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpace_pt
    {𝒳 𝒰 : Stack.AlgebraicStacks.{u, w} B S hS} {V : BigFppfOver B S hS}
    (q : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒳) (x : 𝒰 ⟶ 𝒳)
    (hx : Stack.IsRepresentableByAlgebraicSpaces B S hS x.hom.hom) :
    Stack.IsRepresentableByAlgebraicSpace B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val :=
  Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    𝒰.val 𝒳.val (Stack.schemeStack.{u, w} B S hS V).val x.hom q.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} q.hom x.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      q.hom x.hom)
    hx (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)

/-- **A section of a gerbe over an algebraic space is flat and locally of finite presentation.**
Let `π : 𝒳 ⟶ 𝒰` make `𝒳` a gerbe over an algebraic stack `𝒰` which is representable by an
algebraic space, and let `x : 𝒰 ⟶ 𝒳` be a section of `π`. Then `x` is flat and locally of finite
presentation.

Together with `AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver` this is **Stacks
06QG** part (3), at the source's generality; the three parts of the tag are assembled in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack`.

`AlgebraicGeometry.Stack.exists_single_cover_section_factorisation_of_isGerbeOver` produces a
surjective, flat, locally finitely presented `q : 𝒱 ⟶ 𝒳` out of the algebraic stack of an object
of the site together with a `γ : 𝒱 ⟶ 𝒰` with `γ ≫ x = q` on the nose, and
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_factorisation`
turns such a factorisation into the conclusion by the **Stacks 06NR** step and the descent along
`q`. The three representability data that step needs are the two instances of
`isRepresentableByAlgebraicSpace_pt` at the cospans `(q, q)` and `(q, x)` and **Stacks 04SV** for
the slice of the site over `V`; the leg `q` is representable by algebraic spaces by condition (3)
of **Stacks 045G**, its source being the algebraic stack of an object of the site, and the leg `x`
by **Stacks 045G** condition (2) through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`, its source being
representable by an algebraic space. -/
@[stacks 06QG "part (3): flatness and local finite presentation of the section"]
theorem isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver
    {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    (π : 𝒳 ⟶ 𝒰) (x : 𝒰 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒰)
    (hπ : IsGerbeOver B S hS π)
    (h𝒰 : Stack.IsRepresentableByAlgebraicSpace B S hS 𝒰.val) :
    IsFlat B S hS x ∧ IsLocallyOfFinitePresentation B S hS x := by
  obtain ⟨V, γ, hqsurj, hqflat, hqlfp⟩ :=
    Stack.exists_single_cover_section_factorisation_of_isGerbeOver B S hS π x hx hπ
  set q := γ ≫ x with hq
  have hrep := isRepresentableFromSchemes_of_algebraicStack B S hS 𝒳
  obtain ⟨A, hA, ⟨eA⟩⟩ := isRepresentableByAlgebraicSpace_pt B S hS q q (hrep V q.hom.hom)
  obtain ⟨Y, hY, ⟨eY⟩⟩ := isRepresentableByAlgebraicSpace_pt B S hS q x
    (Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property h𝒰 x.hom)
  obtain ⟨G, hG, ⟨eG⟩⟩ :=
    Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V
  exact isFlat_and_isLocallyOfFinitePresentation_of_factorisation B S hS x q γ (Iso.refl q) π hx
    hqsurj hqflat hqlfp A Y G hA hY hG eA eY eG

/-- **A gerbe has, fppf-locally on its target, a section which is flat and locally of finite
presentation.** Let `f : 𝒳 ⟶ 𝒴` make `𝒳` a gerbe over `𝒴`. Then there are an algebraic stack `𝒵`
over `S` and a surjective, flat, locally finitely presented `g : 𝒵 ⟶ 𝒴` such that the base change
of `f` along `g` — the canonical 2-fibre product of **Stacks 04T2** — admits a section which is
flat and locally of finite presentation.

This is the input **Stacks 06QI** takes from **Stacks 06QH** (1) `⟹` (2) and from **Stacks 06QG**
part (3), assembled from
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_snd_of_isGerbeOver`, which produces the
section, and from
`Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`, which
makes it flat and locally of finite presentation — applicable because the base change of a gerbe is
a gerbe (**Stacks 06QE**) and the covering 1-morphism comes out of the algebraic stack of an object
of the site. -/
theorem exists_flatLfpSection_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    ∃ (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
      Stack.IsSurjective B S hS g ∧ IsFlat B S hS g ∧
        IsLocallyOfFinitePresentation B S hS g ∧
        ∃ s : 𝒵 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt,
          Nonempty (s ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd ≅ 𝟙 𝒵) ∧
            IsFlat B S hS s ∧ IsLocallyOfFinitePresentation B S hS s := by
  obtain ⟨U, g, hgsurj, hgflat, hglfp, hsection⟩ :=
    exists_section_snd_of_isGerbeOver B S hS f hf
  obtain ⟨σ, ⟨hσ⟩⟩ := hsection (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
  obtain ⟨hσflat, hσlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd σ hσ
      (isGerbeOver_of_isTwoFibreProduct B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g)
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g) hf)
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  exact ⟨Stack.schemeStack.{u, w} B S hS U, g, hgsurj, hgflat, hglfp, σ, ⟨hσ⟩, hσflat, hσlfp⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
