module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism

/-!
# Permanence of quasi-compactness under a quasi-compact relative diagonal

Four statements of this library about quasi-compactness of a 1-morphism of algebraic stacks
over `S` take *quasi-separatedness* as their hypothesis — the condition of Stacks 04YW, which
asks of every algebraic space representing a base change of the relative diagonal that its
structural morphism be quasi-compact **and** quasi-separated. In each of the four, the second
conjunct is never read: the argument is an application of Stacks 045C to the relative diagonal
at a property of morphisms of algebraic spaces, and the conjunction is carried through only
because it is the shape the definition is written in. Restated at the first conjunct alone,
each becomes a statement whose hypothesis is quasi-compactness of the relative diagonal:

* the comparison 1-morphism of Stacks 050H,
* the graph of Stacks 050I,
* the section of Stacks 050J part (5),
* and the cancellation of Stacks 050Y.

Those weaker forms are what Stacks 0GW2 needs. The source of that lemma asserts decency of a
quasi-separated algebraic stack and then, *more generally*, of one whose absolute diagonal is
merely quasi-compact; its proof of the second assertion is the single sentence "Details
omitted". Stacks 04YW asks of a quasi-separated 1-morphism that its relative diagonal be
quasi-compact and quasi-separated, so the second assertion is genuinely the weaker hypothesis,
and the four statements below are exactly the gap between them.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_relativeDiagonal_iff`: for the relative
  diagonal of a 1-morphism of algebraic stacks, the condition of Stacks 050U and the condition
  of Properties of Stacks, Section 04XB agree.
* `AlgebraicGeometry.Stack.isQuasiCompact_comparison_of_isQuasiCompact_relativeDiagonal`:
  Stacks 050H part (7), quasi-compactness, from quasi-compactness of the relative diagonal.
* `AlgebraicGeometry.Stack.isQuasiCompact_graph_of_isQuasiCompact_relativeDiagonal`:
  Stacks 050I part (5), quasi-compactness, likewise.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_baseChange`: Stacks 050F,
  quasi-compactness of the relative diagonal is stable under base change.
* `AlgebraicGeometry.Stack.isQuasiCompact_section_of_isQuasiCompact_relativeDiagonal`:
  Stacks 050J part (5), quasi-compactness, likewise.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiCompact_relativeDiagonal`:
  the cancellation of Stacks 050Y under the weaker hypothesis.

## Implementation notes

Nothing here is new mathematics, and nothing is a restatement of an existing result at a changed
generality that could be mistaken for it. Each of the five propositional results instantiates
the *same* property-generic lemma the quasi-separated form instantiates — Stacks 045C in
the hypothesis-free form `AlgebraicGeometry.Stack.relativeProperty_baseChange`, and the
transfers `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison` and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` — at the single property
`AlgebraicGeometry.Space.IsQuasiCompact` instead of at its conjunction with
`AlgebraicGeometry.Space.IsQuasiSeparated`. All three of those lemmas quantify over an
arbitrary `CategoryTheory.MorphismProperty` with no stability or locality hypothesis, which is
why the weakening costs nothing; the quasi-separated forms differ from these only in taking the
first projection of the resulting conjunction.

`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiCompact_relativeDiagonal`
is a strict generalisation of the `@[stacks 050Y]`
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated`, whose hypothesis
implies this one pointwise by `And.left`. The tag stays where it is, on the source-literal
form: Stacks 050Y states the cancellation with a quasi-separated second factor, and a tag
belongs on the statement the source makes. Nothing here carries a `@[stacks]` attribute for the
same reason — each is a tagged statement at a weakened hypothesis, and in particular
**Stacks 0GW2 is not proved here**: its remaining two obligations are the quasi-compact half of
Stacks 050D (8) ⇒ (4) and quasi-compactness of the structure morphism of a represented
algebraic stack over the final one.

Two of the three imports are load-bearing.
`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare` is the home of
`AlgebraicGeometry.Stack.diagonalMapDiag`,
`AlgebraicGeometry.Stack.diagonalBaseChangeSquare` and
`AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalBaseChangeSquare`, the Stacks 04YR square
that the base-change result below applies Stacks 045C to, and
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence` of
`AlgebraicGeometry.Stack.graphSection`.
`StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism` is removable at exit 0 with no output,
because `QuasiCompactMorphismPermanence` public-imports it, so it is **cosmetic and retained
deliberately**, this module naming
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_section` by hand.

`AlgebraicGeometry.Stack.isQuasiCompactMorphism_relativeDiagonal_iff` is Stacks 050T at the
relative diagonal, whose representability is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks` and
so never has to be assumed. Only its `mpr` direction is consumed below; the `mp` direction
costs nothing and is stated because the two conditions are the two forms in which a
quasi-compact diagonal is written in this library, and a consumer arriving with either should
not have to rebuild the bridge.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050T at a relative diagonal.** Quasi-compactness of the relative diagonal of a
1-morphism of algebraic stacks over `S` in the sense of Stacks 050U — every base change by a
quasi-compact algebraic stack is quasi-compact — is the same condition as quasi-compactness in
the sense of Properties of Stacks, Section 04XB.

The representability by algebraic spaces that Stacks 050T needs holds for the relative diagonal
of every 1-morphism of algebraic stacks (Stacks 04XS part (1)), so it is not a hypothesis. -/
theorem isQuasiCompactMorphism_relativeDiagonal_iff {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) :
    IsQuasiCompactMorphism B S hS (relativeDiagonalAlgebraicStacks B S hS f) ↔
      IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS
    (relativeDiagonalAlgebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).symm

/-- **Stacks 050H part (7), quasi-compactness, under a quasi-compact relative diagonal.** The
comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is quasi-compact in the sense of Properties of
Stacks, Section 04XB as soon as the relative diagonal of `h : 𝒵 ⟶ 𝒯` is.

The comparison is a base change of `Δ_h`, and Stacks 045C in the hypothesis-free form
`AlgebraicGeometry.Stack.relativeProperty_baseChange` carries any property of morphisms of
algebraic spaces across that square — here quasi-compactness alone, where the quasi-separated
form of this statement uses its conjunction with quasi-separatedness and then projects. -/
theorem isQuasiCompact_comparison_of_isQuasiCompact_relativeDiagonal
    {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hh : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)) :
    IsQuasiCompact B S hS (comparison B S hS f g h).hom :=
  fun U y hy F hF he =>
    relativeProperty_baseChange.{u, u, u + 1} B S hS
      (fun _ _ k => Space.IsQuasiCompact B S hS k.hom)
      𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
      (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
      (relativeDiagonalAlgebraicStacks B S hS h).hom
      (comparisonCospanRight B S hS f g h).hom
      (comparisonSquare B S hS f g h)
      (isTwoFibreProduct_comparisonSquare B S hS f g h) hh U y hy F hF he

/-- **Stacks 050I part (5), quasi-compactness, under a quasi-compact relative diagonal.** The
graph `Γ_g : 𝒳 ⟶ 𝒳 ×_{p, 𝒯, q} 𝒴` of `g : 𝒳 ⟶ 𝒴` over `𝒯` is quasi-compact in the sense of
Properties of Stacks, Section 04XB as soon as the relative diagonal of `q : 𝒴 ⟶ 𝒯` is.

The graph is identified with the comparison 1-morphism of the previous result by
`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`, which transfers any property
with no hypothesis on it. -/
theorem isQuasiCompact_graph_of_isQuasiCompact_relativeDiagonal
    {𝒳 𝒴 𝒯 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯)
    (η : p ≅ g ≫ q)
    (hq : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒯.val q.hom)) :
    IsQuasiCompact B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS
    (fun _ _ k => Space.IsQuasiCompact B S hS k.hom) g p q η
    (isQuasiCompact_comparison_of_isQuasiCompact_relativeDiagonal B S hS g (𝟙 𝒴) q hq)

/-- **The relative half of Stacks 050J part (5), quasi-compactness, under a quasi-compact
relative diagonal.** A section of `f : 𝒳 ⟶ 𝒯` is quasi-compact in the sense of Properties of
Stacks, Section 04XB as soon as the relative diagonal of `f` is.

A section is the graph of itself up to an equivalence, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries any property across that
identification with no hypothesis on it. -/
theorem isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal
    {𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳)
    (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒯.val f.hom)) :
    IsQuasiCompact B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsQuasiCompact B S hS k.hom) f s η
    (isQuasiCompact_graph_of_isQuasiCompact_relativeDiagonal B S hS s (𝟙 𝒯) f η.symm hf)

/-- **Stacks 050J part (5), quasi-compactness, under a quasi-compact relative diagonal.** A
section of `f : 𝒳 ⟶ 𝒯` is quasi-compact in the sense of Stacks 050U as soon as the relative
diagonal of `f` is.

The section is representable by algebraic spaces by Stacks 050J part (1), so Stacks 050T
converts the relative statement above. -/
theorem isQuasiCompact_section_of_isQuasiCompact_relativeDiagonal
    {𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳)
    (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒯.val f.hom)) :
    IsQuasiCompactMorphism B S hS s :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS s
      (isRepresentableByAlgebraicSpaces_section B S hS f s hs)).mp
    (isRelativelyQuasiCompact_section_of_isQuasiCompact_relativeDiagonal B S hS f s hs hf)

/-- **Stacks 050F for a quasi-compact relative diagonal.** If the relative diagonal of
`f : 𝒳 ⟶ 𝒴` is quasi-compact in the sense of Properties of Stacks, Section 04XB, then so is
the relative diagonal of the base change `f' : 𝒳 ×_{f, 𝒴, g} 𝒴' ⟶ 𝒴'` of `f` along any
`g : 𝒴' ⟶ 𝒴`.

`Δ_{f'}` is a base change of `Δ_f` by Stacks 04YR, and Stacks 045C carries quasi-compactness
across it — the quasi-separated form of this statement is the same application at the
conjunction of quasi-compactness and quasi-separatedness. -/
theorem isQuasiCompact_relativeDiagonal_baseChange
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (hf : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val 𝒴'.val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom) :=
  relativeProperty_baseChange.{u, u, u + 1} B S hS
    (fun _ _ k => Space.IsQuasiCompact B S hS k.hom)
    𝒳.val (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
    (diagonalMapDiag B S hS f g) (diagonalBaseChangeSquare B S hS f g)
    (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f g) hf

/-- **The cancellation of Stacks 050Y under a quasi-compact relative diagonal.** If a composite
`f ≫ g` of 1-morphisms of algebraic stacks over `S` is quasi-compact and the relative diagonal
of `g` is quasi-compact, then `f` is quasi-compact.

This is the argument of Stacks 050Y with its hypothesis weakened: `f` is the composite of its
graph section with the projection of `𝒴 ×_𝒵 𝒳` to `𝒴`; the projection to `𝒳` is a base change
of `g`, so its relative diagonal is quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_baseChange`, which makes the graph
section quasi-compact; the projection to `𝒴` is a base change of `f ≫ g`, hence quasi-compact
by Stacks 050V; and Stacks 050W composes the two.

Stacks 050Y itself assumes `g` quasi-separated, which by Stacks 04YW asks of each represented
base change of `Δ_g` both quasi-compactness and quasi-separatedness; only the first is used, so
this statement is strictly more general than
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated`, which it implies
pointwise by `And.left`. -/
theorem isQuasiCompactMorphism_of_comp_of_isQuasiCompact_relativeDiagonal
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hgf : IsQuasiCompactMorphism B S hS (f ≫ g))
    (hg : IsQuasiCompact B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)) :
    IsQuasiCompactMorphism B S hS f := by
  have hsec : IsQuasiCompactMorphism B S hS (graphSection B S hS f g) :=
    isQuasiCompact_section_of_isQuasiCompact_relativeDiagonal B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).snd
      (graphSection B S hS f g) ⟨Iso.refl _⟩
      (isQuasiCompact_relativeDiagonal_baseChange B S hS g (f ≫ g) hg)
  have hproj : IsQuasiCompactMorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).fst :=
    isQuasiCompactMorphism_baseChange B S hS (f ≫ g) g
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)) hgf
  exact isQuasiCompactMorphism_comp B S hS (graphSection B S hS f g)
    (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).fst hsec hproj

end AlgebraicGeometry.Stack

end
