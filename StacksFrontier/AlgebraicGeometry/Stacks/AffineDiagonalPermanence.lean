module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance

/-!
# Permanence of affineness under an affine relative diagonal

An affine 1-morphism of algebraic stacks over `S` is one which is representable by algebraic
spaces and affine in the sense of Properties of Stacks, Section 04XB
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`, **Stacks 0CHQ**). Base change and
composition of such 1-morphisms are **Stacks 0CHR** and **Stacks 0CHS**, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability` and used here as they stand.

This file adds the two transfers that take an affine relative diagonal as their hypothesis — for
the comparison 1-morphism of Stacks 050H and for the graph of Stacks 050I — and deduces
**Stacks 0GQE**: in a 2-commutative triangle

```text
  𝒳 ----f----> 𝒴
    \         /
     a       b
      \     /
       >  𝒵 <
```

of 1-morphisms of algebraic stacks over `S`, if `a` is affine and the relative diagonal `Δ_b` is
affine, then `f` is affine. The argument is the source's: `f` is 2-isomorphic to the composite of
its graph `Γ_f : 𝒳 ⟶ 𝒳 ×_𝒵 𝒴` over `𝒵` with the second projection `pr₂ : 𝒳 ×_𝒵 𝒴 ⟶ 𝒴`; the
projection is a base change of `a` and the graph is a base change of `Δ_b`.

## Main results

* `AlgebraicGeometry.Stack.isAffineHom_comparison_of_diagonal`: the comparison 1-morphism
  `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of Stacks 050H is affine in the sense of Stacks 04XB as soon as the
  relative diagonal of `𝒵 ⟶ 𝒯` is.
* `AlgebraicGeometry.Stack.isAffineHom_graph`: the graph of Stacks 050I is affine in that sense as
  soon as the relative diagonal of the structural 1-morphism of its target is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_iso`: affineness of a 1-morphism of
  algebraic stacks is invariant under a 2-isomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_comp_of_isAffineHom_relativeDiagonal`:
  **Stacks 0GQE**.

## Implementation notes

The two transfers instantiate the property-generic lemmas
`AlgebraicGeometry.Stack.isAffineHom_baseChange` — Stacks 045C at affineness, from
`StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability` — and
`AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`, neither of which assumes anything
about the property; in particular no fppf locality of affineness of morphisms of algebraic spaces
(Stacks 041Z) is used anywhere below, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism`.

Only Stacks 0GQE carries a `@[stacks]` attribute. The first two results are the affine clauses of
Stacks 050H and Stacks 050I stated for the condition of Stacks 04XB alone, under a hypothesis on
`Δ` that asks for that condition and not for representability — which `Δ` has unconditionally by
Stacks 04XS part (1) — so each is weaker on both sides than the statement whose tag already sits
in `StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison` and
`StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism`. This follows
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalPermanence`, which carries the same
four shapes for quasi-compactness.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0CHR](https://stacks.math.columbia.edu/tag/0CHR)
* [Stacks Project, Tag 0CHS](https://stacks.math.columbia.edu/tag/0CHS)
* [Stacks Project, Tag 0GQE](https://stacks.math.columbia.edu/tag/0GQE)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparison

variable {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- **The affine clause of Stacks 050H.** If the relative diagonal `Δ_{𝒵/𝒯}` is affine in the
sense of Properties of Stacks, Section 04XB, then so is the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of Stacks 050H.

By **Stacks 04Z1** the comparison is a base change of `Δ_{𝒵/𝒯}`, and Stacks 045C carries
affineness across that square with no hypothesis on the property. -/
theorem isAffineHom_comparison_of_diagonal (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (hΔ : Stack.IsAffineHom B S hS (relativeDiagonalAlgebraicStacks B S hS h).hom) :
    Stack.IsAffineHom B S hS (comparison B S hS f g h).hom :=
  isAffineHom_baseChange.{u, u, u + 1} B S hS
    𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
    (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonalAlgebraicStacks B S hS h).hom
    (comparisonCospanRight B S hS f g h).hom
    (comparisonSquare B S hS f g h)
    (isTwoFibreProduct_comparisonSquare B S hS f g h) hΔ

/-- **The affine clause of Stacks 050I.** If the relative diagonal `Δ_q` of `q : 𝒴 ⟶ 𝒯` is affine
in the sense of Properties of Stacks, Section 04XB, then the graph `Γ_g : 𝒳 ⟶ 𝒳 ×_𝒯 𝒴` of
`g : 𝒳 ⟶ 𝒴` over `𝒯` is affine in that sense.

The graph is identified with the comparison 1-morphism `𝒳 ×_𝒴 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` of the previous
result by `AlgebraicGeometry.Stack.relativeProperty_graph_of_comparison`, which transfers any
property of morphisms of algebraic spaces with no hypothesis on it. -/
theorem isAffineHom_graph (g : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒯) (q : 𝒴 ⟶ 𝒯) (η : p ≅ g ≫ q)
    (hΔ : Stack.IsAffineHom B S hS (relativeDiagonalAlgebraicStacks B S hS q).hom) :
    Stack.IsAffineHom B S hS (graph B S hS g p q η).hom :=
  relativeProperty_graph_of_comparison B S hS (Space.affineMorphismProperty B S hS) g p q η
    (isAffineHom_comparison_of_diagonal B S hS g (𝟙 𝒴) q hΔ)

end Comparison

namespace AlgebraicStacks

/-- **Affineness of a 1-morphism of algebraic stacks is invariant under a 2-isomorphism.** Both
halves are Stacks 0457 and Stacks 0459 at the identity equivalences of source and target, the
2-isomorphism of underlying based functors being
`AlgebraicGeometry.Stack.algStackHomHomIso`. -/
theorem isAffineHom_of_iso {𝒰 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {q q' : 𝒰 ⟶ 𝒵}
    (e : q ≅ q') (h : IsAffineHom B S hS q) : IsAffineHom B S hS q' := by
  have (𝒜 : Stack.AlgebraicStacks.{u, w} B S hS) :
      Functor.IsEquivalence (BasedFunctor.id 𝒜.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒜.val.val.obj))
  exact ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS q'.hom.hom q.hom.hom
      (BasedFunctor.id 𝒰.val.val) (BasedFunctor.id 𝒵.val.val)
      (Stack.algStackHomHomIso B S hS e)).1 h.1,
    relativeProperty_of_equivalences B S hS (Space.affineMorphismProperty B S hS)
      q'.hom.hom q.hom.hom (BasedFunctor.id 𝒰.val.val) (BasedFunctor.id 𝒵.val.val)
      (Stack.algStackHomHomIso B S hS e) h.2⟩

/-- **Stacks 0GQE.** Let

```text
  𝒳 ----f----> 𝒴
    \         /
     a       b
      \     /
       >  𝒵 <
```

be a 2-commutative triangle of 1-morphisms of algebraic stacks over `S`, the commutativity being
the 2-isomorphism `comm : a ≅ f ≫ b`. If `a` is affine and the relative diagonal `Δ_b` is affine
in the sense of Properties of Stacks, Section 04XB, then `f` is affine.

*Reading the statement.* The unqualified `IsAffineHom`, in the hypothesis `ha` on `a` and in the
conclusion on `f`, elaborates to `AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`, the notion
of an affine 1-morphism of algebraic stacks of **Stacks 0CHQ** (registered in
`StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism`). It is by definition the conjunction
`IsRepresentableByAlgebraicSpaces B S hS q.hom.hom ∧ Stack.IsAffineHom B S hS q.hom` for `q = a`
and for `q = f`, so it includes representability by algebraic spaces: `a` is assumed, and `f` is
concluded, to be representable by algebraic spaces and affine in the sense of Stacks 04XB, exactly
as in the source. The 1-morphism `relativeDiagonalAlgebraicStacks B S hS b` is the relative
diagonal `Δ_b : 𝒴 ⟶ 𝒴 ×_{b, 𝒵, b} 𝒴`, `y ↦ (y, y, id)`. The hypothesis `hΔ` on it is written
with the qualified `Stack.IsAffineHom`, the condition of Stacks 04XB alone, without
representability; it is weaker than the source's hypothesis that `Δ_b` is affine, and loses
nothing, since `Δ_b` is representable by algebraic spaces unconditionally by Stacks 04XS part (1)
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack`).

This is the source's proof. The 1-morphism `f` is 2-isomorphic to `Γ_f ≫ pr₂`, where
`Γ_f : 𝒳 ⟶ 𝒳 ×_𝒵 𝒴` is the graph of `f` over `𝒵` (Stacks 050I) and
`pr₂ : 𝒳 ×_𝒵 𝒴 ⟶ 𝒴` is the second projection of the canonical 2-fibre product of the cospan
`(a, b)`. The projection is a base change of `a`, hence affine by **Stacks 0CHR**; the graph is
affine by `AlgebraicGeometry.Stack.isAffineHom_graph`, which carries the hypothesis on `Δ_b`
along the base-change square of **Stacks 04Z1**; and **Stacks 0CHS** composes the two. -/
@[stacks 0GQE]
theorem isAffineHom_of_comp_of_isAffineHom_relativeDiagonal
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (a : 𝒳 ⟶ 𝒵) (b : 𝒴 ⟶ 𝒵) (comm : a ≅ f ≫ b)
    (ha : IsAffineHom B S hS a)
    (hΔ : Stack.IsAffineHom B S hS (relativeDiagonalAlgebraicStacks B S hS b).hom) :
    IsAffineHom B S hS f := by
  have hgraph : IsAffineHom B S hS (Stack.graph B S hS f a b comm) :=
    ⟨Stack.isRepresentableByAlgebraicSpaces_graph B S hS f a b comm,
      Stack.isAffineHom_graph B S hS f a b comm hΔ⟩
  have hproj : IsAffineHom B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a b).snd :=
    isAffineHom_snd_of_isTwoFibreProduct B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a b)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b) ha
  exact isAffineHom_of_iso B S hS (Stack.graph_snd_iso B S hS f a b comm).symm
    (isAffineHom_comp B S hS _ _ hgraph hproj)

end AlgebraicStacks

end Stack

end AlgebraicGeometry

end
