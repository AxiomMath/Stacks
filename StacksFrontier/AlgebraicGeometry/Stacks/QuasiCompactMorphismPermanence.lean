module

public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Permanence properties of quasi-compact morphisms of algebraic stacks

Quasi-compactness of a 1-morphism of algebraic stacks over `S` — Stacks 050U, the condition that
every base change by a quasi-compact algebraic stack is a quasi-compact algebraic stack — is
stable under base change (Stacks 050V) and under composition (Stacks 050W), and the first factor
of a quasi-compact composite is quasi-compact as soon as the second factor is quasi-separated
(Stacks 050Y).

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_baseChange`: **Stacks 050V**.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_comp`: **Stacks 050W**.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_comp_of_isQuasiSeparated`: **Stacks 050Y**.

## Implementation notes

All three are consequences of two facts and no new geometry: Stacks 02XD in the 2-category of
algebraic stacks, `AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks`, and
the invariance `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isTwoFibreProduct` of
quasi-compactness of an algebraic stack across the 2-fibre products of one cospan.

For composition the base change of `f ≫ g` by a quasi-compact `𝒲 ⟶ 𝒵` is the iterated product
`(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳`, quasi-compact by applying the hypothesis on `g` and then the hypothesis on
`f`; the cancellation says that iterated apex is a 2-fibre product of the cospan `(k, f ≫ g)`,
and the invariance moves quasi-compactness onto the canonical apex.

For base change the given square `P` over the cospan `(g, f)` is only *recognised* as a 2-fibre
product rather than built as one, so the cancellation is used in the form
`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks`, with comparison
the strict `AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` of the *exchanged* square
`P.swap` — exchanged because what the cancellation consumes is the comparison followed by the
second inner projection, and that composite has to be `P.fst` on the nose. Two applications of
`CategoryTheory.Bicategory.TwoCommSq.swap` then reconcile the order of the two cospans, since
quasi-compactness of a 1-morphism quantifies over the base change with the *test* morphism first.

For Stacks 050Y the source's own argument is used: `f` is the composite of its graph section with
the projection of `𝒴 ×_𝒵 𝒳` to `𝒴`. The graph section is
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks` at the square with apex `𝒳`, legs `f`
and the identity, and identity filler, so both of its compatibilities hold on the nose and the
composite with the projection to `𝒴` is `f` itself rather than a 1-morphism 2-isomorphic to it.
Its quasi-compactness is Stacks 050J part (5) applied to the base change of `g`, which is
quasi-separated by Stacks 050F; the projection is quasi-compact by Stacks 050V; and Stacks 050W
composes them.

The quasi-separatedness used throughout is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated` — the Stacks 04YW condition on a
1-morphism of algebraic stacks — and not the namesake `AlgebraicGeometry.Space.IsQuasiSeparated`
for morphisms of algebraic spaces.

## References

* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050W.** The composite of two quasi-compact 1-morphisms of algebraic stacks over `S`
is quasi-compact.

A base change of `f ≫ g` by a quasi-compact algebraic stack is the iterated 2-fibre product
`(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳`; the inner apex is quasi-compact because `g` is, the outer one because `f` is,
and Stacks 02XD identifies the outer apex with a 2-fibre product of the cospan of `f ≫ g`. -/
@[stacks 050W]
theorem isQuasiCompactMorphism_comp {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsQuasiCompactMorphism B S hS f) (hg : IsQuasiCompactMorphism B S hS g) :
    IsQuasiCompactMorphism B S hS (f ≫ g) := by
  intro 𝒲 k h𝒲
  exact isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS k g f (f ≫ g) (Iso.refl _))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g))
    (hf _ (twoFibreProductSquareAlgebraicStacks B S hS k g).snd (hg 𝒲 k h𝒲))

/-- **Stacks 050V.** A base change of a quasi-compact 1-morphism of algebraic stacks over `S` is
quasi-compact: if `P` is a 2-fibre product of the cospan `(g, f)` and `f` is quasi-compact, then
the projection `P.fst` is quasi-compact.

The base change of `P.fst` by a test 1-morphism `k` is `𝒵 ×_{𝒴'} P.pt`, and Stacks 02XD at the
recognised 2-fibre product `P` identifies it with a 2-fibre product of the cospan `(f, k ≫ g)`;
the base change of `f` along `k ≫ g` is another, and it is quasi-compact by hypothesis. -/
@[stacks 050V]
theorem isQuasiCompactMorphism_baseChange {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hf : IsQuasiCompactMorphism B S hS f) :
    IsQuasiCompactMorphism B S hS P.fst := by
  intro 𝒵 k h𝒵
  have hswap : Bicategory.IsTwoFibreProduct P.swap := Bicategory.isTwoFibreProduct_swap hP
  have hcmp :
      ((canonicalPreHomAlgebraicStacks B S hS f g P.swap).hom).hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hswap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g)
      (canonicalPreHomAlgebraicStacks B S hS f g P.swap)
  have hcancel := isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks B S hS f g
    (canonicalPreHomAlgebraicStacks B S hS f g P.swap).hom k (k ≫ g) (Iso.refl _) hcmp
  have houter := isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (k ≫ g) f))
    hcancel (hf 𝒵 (k ≫ g) h𝒵)
  have houter' : IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack B S hS P.fst k).val
      (twoFibreProductAlgebraicStack B S hS P.fst k).property := houter
  exact isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.fst k))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k P.fst) houter'

/-- **Stacks 050X.** Let `f : 𝒳 ⟶ 𝒴`, `p : 𝒳 ⟶ 𝒵` and `q : 𝒴 ⟶ 𝒵` be a 2-commutative triangle
of 1-morphisms of algebraic stacks over `S`. If `f` is surjective and `p` is quasi-compact, then
`q` is quasi-compact.

A base change `𝒯 ×_𝒵 𝒴` of `q` by a quasi-compact algebraic stack receives the iterated product
`(𝒯 ×_𝒵 𝒴) ×_𝒴 𝒳`, which is a base change of the surjective `f` and hence surjects onto it
(Stacks 04ZU); Stacks 02XD identifies that iterated apex with a 2-fibre product of the cospan
`(k, p)`, quasi-compact by the hypothesis on `p`, and quasi-compactness of an algebraic stack
passes along a surjection. -/
@[stacks 050X]
theorem isQuasiCompactMorphism_of_comp_of_isSurjective
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒵) (q : 𝒴 ⟶ 𝒵) (e : f ≫ q ≅ p)
    (hf : IsSurjective B S hS f) (hp : IsQuasiCompactMorphism B S hS p) :
    IsQuasiCompactMorphism B S hS q := by
  intro 𝒯 k h𝒯
  have hinner := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS k q).snd f
  have hcancel := isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k p)
    (isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS k q f p e)
    (hp 𝒯 k h𝒯)
  exact isQuasiCompactStack_of_isSurjective B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS k q).snd f).fst
    hcancel
    (isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS k q).snd f).swap
      (Bicategory.isTwoFibreProduct_swap hinner) hf)

variable {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}

/-- The graph of `f : 𝒳 ⟶ 𝒴` as a 2-commutative square over the cospan `(g, f ≫ g)`: the apex is
`𝒳`, the leg to `𝒴` is `f`, the leg to `𝒳` is the identity, and the filler is the identity. -/
def graphSquare (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) : Bicategory.TwoCommSq g (f ≫ g) where
  pt := 𝒳
  fst := f
  snd := 𝟙 𝒳
  iso := Iso.refl _

/-- The graph section `𝒳 ⟶ 𝒴 ×_𝒵 𝒳` of `f : 𝒳 ⟶ 𝒴` over `g : 𝒴 ⟶ 𝒵`: the strict comparison of
`AlgebraicGeometry.Stack.graphSquare` with the canonical 2-fibre product square. Its composite
with the projection to `𝒳` is the identity and its composite with the projection to `𝒴` is `f`,
both on the nose. -/
noncomputable def graphSection (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    𝒳 ⟶ (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).pt :=
  (canonicalPreHomAlgebraicStacks B S hS g (f ≫ g) (graphSquare B S hS f g)).hom

/-- **Stacks 050Y.** If a composite of 1-morphisms of algebraic stacks over `S` is quasi-compact
and its second factor is quasi-separated, then its first factor is quasi-compact.

`f` is the composite of its graph section with the projection of `𝒴 ×_𝒵 𝒳` to `𝒴`. The projection
to `𝒳` is a base change of `g`, hence quasi-separated (Stacks 050F), so the graph section is
quasi-compact by Stacks 050J part (5); the projection to `𝒴` is a base change of `f ≫ g`, hence
quasi-compact by Stacks 050V; and Stacks 050W composes the two. -/
@[stacks 050Y, ega "IV 1.2.4"]
theorem isQuasiCompactMorphism_of_comp_of_isQuasiSeparated (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hgf : IsQuasiCompactMorphism B S hS (f ≫ g))
    (hg : AlgebraicStacks.IsQuasiSeparated B S hS g) :
    IsQuasiCompactMorphism B S hS f := by
  have hqs : AlgebraicStacks.IsQuasiSeparated B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).snd :=
    AlgebraicStacks.isQuasiSeparated_baseChange B S hS g (f ≫ g) hg
  have hsec : IsQuasiCompactMorphism B S hS (graphSection B S hS f g) :=
    isQuasiCompact_section B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).snd
      (graphSection B S hS f g) ⟨Iso.refl _⟩ hqs
  have hproj : IsQuasiCompactMorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).fst :=
    isQuasiCompactMorphism_baseChange B S hS (f ≫ g) g
      (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)) hgf
  exact isQuasiCompactMorphism_comp B S hS (graphSection B S hS f g)
    (twoFibreProductSquareAlgebraicStacks B S hS g (f ≫ g)).fst hsec hproj

end AlgebraicGeometry.Stack

end
