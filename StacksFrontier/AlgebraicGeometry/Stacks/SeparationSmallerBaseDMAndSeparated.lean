module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase

/-!
# DM, quasi-DM and separatedness over a larger base descend to the base (Stacks 050N)

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `𝒳` be an algebraic stack over `S`.
Construction A of Stacks, Section 04WT views `𝒳` as an algebraic stack over `S'` with the same
underlying category and the structure functor composed with `CategoryTheory.Over.map g`. This
file proves that if that view of `𝒳` is DM, quasi-DM or separated over `S'`, then `𝒳` is DM,
quasi-DM or separated over `S`; at `S' = Spec ℤ` these are parts (5), (6) and (7) of Stacks 050D
implying parts (1), (2) and (3), which are the DM, quasi-DM and separated assertions of
Stacks 050N.

All four separation properties of an algebraic stack over its base are conditions on the relative
diagonal of its structure morphism, in the sense of Stacks 04XB: a condition on the algebraic
space representing each base change of that diagonal along a scheme-valued point of the
self-product. The comparison that carries such a representing object from the self-product over
`S` to the self-product over `S'`,
`CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute`, mentions no separation
condition at all, so the only step that differs between the four keys is the last one, which reads
the resulting morphism of algebraic spaces over the two bases:

* DM: `AlgebraicGeometry.Space.IsUnramified` is `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`
  at `AlgebraicGeometry.Unramified`, so the step is the arbitrary-property statement
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`.
* quasi-DM: `AlgebraicGeometry.Space.IsLocallyQuasiFinite` is the same condition at
  `AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`, so it is that
  same lemma at a different property.
* separated: `AlgebraicGeometry.Space.IsProper` is the conjunction of the four clauses of
  Stacks 03ZM, and the step is `AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of`,
  which assembles them.

Those are the three steps the corresponding three keys of Stacks 050G use for the *relative*
diagonal, so nothing new about the properties themselves is needed here.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isDMOver_changeBase`,
  `...isQuasiDMOver_of_isQuasiDMOver_changeBase` and
  `...isSeparatedOver_of_isSeparatedOver_changeBase`: the general forms, along an arbitrary
  morphism `g : S ⟶ S'` of the site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isAbsolutelyDM`,
  `...isQuasiDMOver_of_isAbsolutelyQuasiDM` and `...isSeparatedOver_of_isAbsolutelySeparated`:
  the three absolute forms, at `S' = Spec ℤ`.

## Implementation notes

**Only `isSeparatedOver_of_isAbsolutelySeparated` carries a Stacks attribute.** The separated
assertion of Stacks 050N is the one-directional statement that an absolutely separated algebraic
stack is separated over its base, and that single declaration states the whole of it. The DM and
quasi-DM assertions of the source are *biconditionals*, and only the implication from the absolute
property is available here: the converse would need the change of target along
`CategoryTheory.Over.map g` to be an equivalence of categories rather than merely fully faithful,
and `CategoryTheory.Over.map g` is not full for a general `g` — a morphism over `S'` between two
objects pushed forward from `Over S` need not commute with the two morphisms to `S`. One direction
of a biconditional is not that assertion's covering set, so neither is registered.

Being DM and being quasi-DM are existential statements, asserting representability of the relative
diagonal by algebraic spaces together with the pointwise condition. The representability witness is
supplied directly by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks` rather
than transported from the larger base, exactly as the quasi-DM key of Stacks 050G does; only the
second component is carried across the change of base.

The `AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated` of the third conclusion unfolds to
`AlgebraicGeometry.Stack.IsProper` at the relative diagonal — the Stacks 04XB condition on a
1-morphism of categories fibred in groupoids — and *not* to
`AlgebraicGeometry.Stack.AlgebraicStacks.IsProper`, which is the conjunction of separatedness,
finite type and universal closedness of a 1-morphism of algebraic stacks. Those two and
`AlgebraicGeometry.Space.IsProper`, the property of a morphism of algebraic spaces that the
transfer lemma above is about, are three different predicates sharing one leaf name, and no two of
them can be compared: they take three different kinds of morphism.

The explicit universe applications `Stack.AlgebraicStacks.{u, w}` and `⊤_ Scheme.{u}` are
cosmetic — deleting them leaves the six signatures byte-identical under `pp.universes` and
`pp.fullNames` — and are retained for consistency with the eight parts of Stacks 050D, the three
keys of Stacks 050G and the quasi-separated sibling of these three results, all of which write
them.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050G](https://stacks.math.columbia.edu/tag/050G)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Being DM over a larger base implies being DM over the base.** If Construction A of `𝒳`
along `g : S ⟶ S'` is DM over `S'`, then `𝒳` is DM over `S`.

Representability of the relative diagonal is supplied over `S` directly; the pointwise condition
is carried across by `CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute` and
read over the two bases by the arbitrary-property statement
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`, at the property
`AlgebraicGeometry.Unramified`. -/
theorem isDMOver_of_isDMOver_changeBase
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsDMOver B S' hS' (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)) :
    Stack.IsDMOver B S hS 𝒳 := by
  refine ⟨Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
    (Stack.structureMorphism B S hS 𝒳), ?_⟩
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (Stack.structureMorphism B S hS 𝒳).hom.hom.w
    (Stack.structureMorphism B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := h𝒳.2 (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
    U.hom S' hS' g _ rfl _ F hF).mp hprop

/-- **Being quasi-DM over a larger base implies being quasi-DM over the base.** If Construction A
of `𝒳` along `g : S ⟶ S'` is quasi-DM over `S'`, then `𝒳` is quasi-DM over `S`.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isDMOver_changeBase` with the
property tested of the represented base changes of the relative diagonal changed from
`AlgebraicGeometry.Unramified` to
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`, both conditions
being `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` and the transfer across the change of base
being stated for an arbitrary property. -/
theorem isQuasiDMOver_of_isQuasiDMOver_changeBase
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsQuasiDMOver B S' hS' (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)) :
    Stack.IsQuasiDMOver B S hS 𝒳 := by
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (Stack.structureMorphism B S hS 𝒳).hom.hom.w
    (Stack.structureMorphism B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := h𝒳 (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact (Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
    U.hom S' hS' g _ rfl _ F hF).mp hprop

/-- **Being separated over a larger base implies being separated over the base.** If
Construction A of `𝒳` along `g : S ⟶ S'` is separated over `S'`, then `𝒳` is separated over `S`.

Separatedness over the base is properness of the relative diagonal of the structure morphism in
the sense of Stacks 04XB, so the last step is
`AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of`, which reads the four clauses
of Stacks 03ZM over the two bases. There is no existential clause to supply: unlike the DM and
quasi-DM conditions, properness of a 1-morphism representable by algebraic spaces is stated
without a representability witness. -/
theorem isSeparatedOver_of_isSeparatedOver_changeBase
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsSeparatedOver B S' hS' (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)) :
    Stack.IsSeparatedOver B S hS 𝒳 := by
  intro U y hy F hF he
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (Stack.structureMorphism B S hS 𝒳).hom.hom.w
    (Stack.structureMorphism B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := h𝒳 (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact Space.isProper_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
    U.hom S' hS' g _ rfl F hF hprop

/-- **A DM algebraic stack is DM over its base.** This is part (5) of Stacks 050D implying
part (1), the forward implication of the DM assertion of Stacks 050N: absolute DM-ness is
DM-ness over the terminal scheme `Spec ℤ` after `𝒳` has been viewed over it by Construction A, so
this is `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isDMOver_changeBase` at
`S' = Spec ℤ`. The converse is not proved here. -/
theorem isDMOver_of_isAbsolutelyDM
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsAbsolutelyDM B S hS hZ 𝒳) :
    Stack.IsDMOver B S hS 𝒳 :=
  isDMOver_of_isDMOver_changeBase B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 h𝒳

/-- **A quasi-DM algebraic stack is quasi-DM over its base.** This is part (6) of Stacks 050D
implying part (2), the forward implication of the quasi-DM assertion of Stacks 050N, obtained
from `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_of_isQuasiDMOver_changeBase` at
`S' = Spec ℤ`. The converse is not proved here. -/
theorem isQuasiDMOver_of_isAbsolutelyQuasiDM
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsAbsolutelyQuasiDM B S hS hZ 𝒳) :
    Stack.IsQuasiDMOver B S hS 𝒳 :=
  isQuasiDMOver_of_isQuasiDMOver_changeBase B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 h𝒳

/-- **Stacks 050N, the separated assertion: a separated algebraic stack is separated over its
base.** This is part (7) of Stacks 050D implying part (3): absolute separatedness is
separatedness over the terminal scheme `Spec ℤ` after `𝒳` has been viewed over it by
Construction A, so this is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparatedOver_of_isSeparatedOver_changeBase` at
`S' = Spec ℤ`. -/
@[stacks 050N "separated_base"]
theorem isSeparatedOver_of_isAbsolutelySeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsAbsolutelySeparated B S hS hZ 𝒳) :
    Stack.IsSeparatedOver B S hS 𝒳 :=
  isSeparatedOver_of_isSeparatedOver_changeBase B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 h𝒳

end AlgebraicGeometry.Stack.AlgebraicStacks

end
