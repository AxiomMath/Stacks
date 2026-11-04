module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# Cancelling the second factor of a quasi-separated composite
(Stacks 050M part (4), Stacks 050N part (8))

Stacks 050M part (4) says that if a composite `f ≫ g` of 1-morphisms of algebraic stacks is
quasi-separated and the relative diagonal of `g` is quasi-separated, then `f` is quasi-separated.
Stacks 050N part (8) is that statement at the structure morphism of the target: if `𝒳` is
quasi-separated over `S` and `Δ_{𝒴/S}` is quasi-separated then `f : 𝒳 ⟶ 𝒴` is quasi-separated.

The source proves part (4) by cancelling across the factorisation
`𝒳 ⟶ 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` of the relative diagonal of `f ≫ g`, which needs Stacks 03KR and
Stacks 03KS at the level of morphisms of algebraic spaces. The route taken here needs neither,
because it turns that cancellation into a *composition*: put the identity of `𝒴` on one leg of
the comparison of Stacks 050H, so that

```text
                  i                    pr
    𝒴 ×_𝒴 𝒳 -------------> 𝒴 ×_𝒵 𝒳 --------> 𝒴
```

composes to the projection `𝒴 ×_𝒴 𝒳 ⟶ 𝒴` **on the nose**. The right-hand 1-morphism is the base
change of `f ≫ g` along `g` and so is quasi-separated by Stacks 050F; the comparison `i` is
quasi-separated by Stacks 050H part (2), which takes exactly the source's hypothesis on `Δ_g`;
Stacks 050K composes them; and the composite is the base change of `f` along the identity of
`𝒴`, which is `f`.

That last step is `CategoryTheory.Bicategory.isTwoFibreProduct_trivialBaseChangeSquare`, read
through the comparison of apexes exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct`
does for an arbitrary 2-fibre-product square.

## The two readings of the hypothesis on `Δ_g`, and why they agree

Stacks 050H part (2) is stated in the library with the hypothesis that `Δ_g` is quasi-separated
in the relative sense of Properties of Stacks, Section 04XB — the notion that applies to a
1-morphism representable by algebraic spaces, which `Δ_g` is by Stacks 04XS part (1) — and that
is the reading used below. Reading the same phrase as Definition 04YW instead gives an
*equivalent* hypothesis rather than a stronger or weaker one: condition (1) of Stacks 04YT is
available in both forms, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal`
(Definition 04YW) and as
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated`
(Section 04XB), and composing the two carries either form of the hypothesis to the other.

The same pair of equivalences is what makes the comparison `i` usable at all: Stacks 050H
part (2) delivers the Section 04XB predicate of `i`, while Stacks 050K composes the Definition
04YW condition, and `i` is representable by algebraic spaces, so the two readings meet.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparated_comp`:
  **Stacks 050M**, part (4).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver`:
  **Stacks 050N**, part (8).

## Implementation notes

Both statements are single implications in the source — Stacks 050M has four parts and all four
are implications, as are parts (5) to (8) of Stacks 050N — so one declaration states each of them
in full and carries its tag.

`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal`
states its right-hand side as the Section 04XB quasi-compactness predicate of `Δ_f` directly, so
its `mpr` takes that one condition and the representability of `Δ_f` is not a separate argument.

The identity `i ≫ pr = pr'` of the two projections is definitional, so no transport across it is
written: the composite is accepted at the type of the projection out of `𝒴 ×_𝒴 𝒳` directly. An
`Eq.mpr` across an explicitly stated version of that identity is unnecessary.

The separated analogues, Stacks 050M part (3) and Stacks 050N part (7), do **not** follow by this
route and are not treated here: the step that fails is Stacks 050K, which is
registered for the DM, quasi-DM and quasi-separated cases and not for the separated one, because
properness of a morphism of algebraic spaces is not known here to be fppf local on the base —
that is Stacks 0422, with Stacks 0421 for separatedness, both in `chapter-074-spaces-descent`
and neither formalized in the library.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050M, part (4).** If a composite `f ≫ g` of 1-morphisms of algebraic stacks over `S`
is quasi-separated and the relative diagonal of `g` is quasi-separated, then `f` is
quasi-separated.

The comparison 1-morphism `i : 𝒴 ×_𝒴 𝒳 ⟶ 𝒴 ×_𝒵 𝒳` of Stacks 050H, taken at the identity of `𝒴`,
composes with the second projection of `𝒴 ×_𝒵 𝒳` to give the second projection of `𝒴 ×_𝒴 𝒳` on
the nose. The projection out of `𝒴 ×_𝒵 𝒳` is the base change of `f ≫ g` along `𝟙 𝒴 ≫ g` and is
quasi-separated by Stacks 050F; `i` is quasi-separated by Stacks 050H part (2) from the
hypothesis on `Δ_g`, upgraded from the Section 04XB predicate to the Definition 04YW condition by
the two forms of Stacks 04YT condition (1); and Stacks 050K composes them. The projection out of
`𝒴 ×_𝒴 𝒳` is the base change of `f` along an identity, which is `f` itself by
`CategoryTheory.Bicategory.isTwoFibreProduct_trivialBaseChangeSquare`. -/
@[stacks 050M "quasi_separated_first"]
theorem isQuasiSeparated_of_isQuasiSeparated_comp
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsQuasiSeparated B S hS (f ≫ g))
    (hΔg : Stack.IsQuasiSeparated B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS g).hom) :
    IsQuasiSeparated B S hS f := by
  have hkRep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.comparison B S hS f (𝟙 𝒴) g).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_comparison B S hS f (𝟙 𝒴) g
  have hk : IsQuasiSeparated B S hS (Stack.comparison B S hS f (𝟙 𝒴) g) :=
    (isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S hS
        (Stack.comparison B S hS f (𝟙 𝒴) g) hkRep).mpr
      ((Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
        (Stack.comparison B S hS f (𝟙 𝒴) g) hkRep).mpr
        (Stack.isQuasiSeparated_comparison_of_diagonal B S hS f (𝟙 𝒴) g hΔg))
  have hq : IsQuasiSeparated B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) (𝟙 𝒴 ≫ g)).snd :=
    isQuasiSeparated_baseChange B S hS (f ≫ g) (𝟙 𝒴 ≫ g) hfg
  have hp : IsQuasiSeparated B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴)).snd :=
    isQuasiSeparated_comp B S hS _ _ hk hq
  have hQ := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴)
  let d : Bicategory.TwoCommSq.PreHom (Bicategory.trivialBaseChangeSquare f)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴)) :=
    _root_.Quotient.out (hQ.from (Bicategory.trivialBaseChangeSquare f))
  exact isQuasiSeparated_of_equivalence B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴)).snd f d.hom.hom.hom
    (Stack.algStackHomHomIso B S hS d.isoSnd.symm)
    (Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS
      (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare f hQ) hQ d) hp

/-- **Stacks 050N, part (8).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` whose source
is quasi-separated over `S` and whose target has quasi-separated relative diagonal over `S` is
quasi-separated.

The structure morphism of `𝒳` is `f` followed by the structure morphism of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`, an equality of 1-morphisms on the nose), so
the hypothesis on `𝒳` says that that composite is quasi-separated, and Stacks 050M part (4)
cancels the second factor. That is the source's own proof: *"Parts (5), (6), (7), and (8) follow
immediately from Lemma 050M"*. -/
@[stacks 050N "quasi_separated_source"]
theorem isQuasiSeparated_of_isQuasiSeparatedOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : Stack.IsQuasiSeparatedOver B S hS 𝒳)
    (hΔ : Stack.IsQuasiSeparated B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS
        (Stack.structureMorphism B S hS 𝒴)).hom) :
    IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isQuasiSeparated_comp B S hS f (Stack.structureMorphism B S hS 𝒴)
    (Stack.comp_structureMorphism B S hS f ▸ h𝒳) hΔ

end AlgebraicGeometry.Stack.AlgebraicStacks

end
