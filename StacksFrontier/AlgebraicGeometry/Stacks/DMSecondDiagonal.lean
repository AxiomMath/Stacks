module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified

/-!
# Stacks 04Z0, part (4): DM morphisms and the first two diagonals

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with no representability assumption. Part (4) of Stacks 04Z0 says that
`f` is DM — Deligne–Mumford, in the sense of Definition 04YW — exactly when its first relative
diagonal `Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal `Δ_{f,2}`, the
relative diagonal of `Δ_{f,1}`, are unramified in the relative sense of Properties of Stacks,
Section 04XB. This file proves it.

Definition 04YW asks of a DM `f` exactly that `Δ_{f,1}` be representable by algebraic spaces and
unramified, so the first conjunct on the right is the whole of the left-hand side: both diagonals
are representable by algebraic spaces by part (1) of Stacks 04XS, so the representability clause
costs nothing in either direction. The second conjunct is free, and that is the content of the
source's own one-line proof: `Δ_{f,2}` is *always* unramified, with no hypothesis on `f` at all,
because it is the relative diagonal of `Δ_{f,1}`, which is representable by algebraic spaces, so
Stacks 05W6 applies to it — `Δ_{f,2}` is locally of finite type and a monomorphism by parts (2)
and (3) of Stacks 04YQ, and a monomorphism of algebraic spaces locally of finite type is
unramified.

## Main results

* `AlgebraicGeometry.Stack.isDM_iff_isUnramifiedRelative_diagonals`: **Stacks 04Z0**, part (4).

## Implementation notes

The source's own proof is *"this follows from the fact that `Δ_{f,2}` is always unramified as
Lemma 04YQ applied to `Δ_f = Δ_{f,1}` shows that `Δ_{f,2}` is locally of finite type and a
monomorphism; see Stacks 05W6"*, and that is what the forward direction's second component is
here: `AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`
— part (3) of Stacks 050E, which is exactly that argument — applied to `Δ_{f,1}` with its
representability supplied by part (1) of Stacks 04XS,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`. That
theorem is stated in the packaged form `AlgebraicGeometry.Stack.IsDM`, which carries the
representability of the diagonal as a conjunct, so its second component is the one taken. The two
remaining components are the identity: `AlgebraicGeometry.Stack.IsDM` *is* representability of
`Δ_{f,1}` together with the Section 04XB unramifiedness condition on it, so the left-hand side is
the first conjunct on the right once the representability clause is discharged by Stacks 04XS.

`AlgebraicGeometry.Stack.IsUnramifiedRelative` is the Section 04XB notion at
`AlgebraicGeometry.Space.IsUnramified`, written out as the quantifier of that section in the
spelling of `AlgebraicGeometry.Stack.IsSeparated`,
`AlgebraicGeometry.Stack.UniversallyClosed` and `AlgebraicGeometry.Stack.IsFiniteType`. Two
things forced the longer name and the explicit quantifier rather than reuse:

* the name `AlgebraicGeometry.Stack.IsUnramified` is already taken, by **Stacks 0CIT** in
  `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism` — a different notion, defined
  for an *arbitrary* 1-morphism of algebraic stacks by the universal étale-smooth diagram test.
  The two agree for a 1-morphism representable by algebraic spaces, but only through a bridge
  this library does not have, so the statement below is not written at it;
* the notion is not reached through `AlgebraicGeometry.Stack.HasRelativeProperty` either, for the
  reason recorded in `StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified`: that
  abbreviation carries base-change stability and fppf locality of the tested property as instance
  arguments which its body does not use, and neither is available in this library at
  unramifiedness of morphisms of algebraic spaces.

The two diagonals are the algebraic-stacks-level
`AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, so the second diagonal is literally the
first applied twice; the target of the first is already the algebraic stack
`AlgebraicGeometry.Stack.twoFibreProductAlgebraicStack`, which is why no separate target bundle is
needed. This is the spelling of the three sibling parts of Stacks 04Z0 in
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMSecondDiagonal` and
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal`, and of Stacks 04YZ in
`StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalSeparation`.

**Parts (1), (2) and (3) of Stacks 04Z0 are not proved here**, but all three are proved: part (1)
is `AlgebraicGeometry.Stack.isSeparated_iff_universallyClosed_diagonals` in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedSecondDiagonal`, part (2) is
`AlgebraicGeometry.Stack.isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals` in
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal` and part (3) is
`AlgebraicGeometry.Stack.isQuasiDM_iff_isLocallyQuasiFinite_diagonals` in
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMSecondDiagonal`.

## References

* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Relative

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is unramified* when every algebraic space representing its
base change along a scheme-valued point of the target has unramified structural morphism, read
as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**, part (1)).

The name is not `IsUnramified`, which in this namespace is **Stacks 0CIT** — the notion for an
arbitrary 1-morphism of algebraic stacks, defined by the universal étale-smooth diagram test. -/
abbrev IsUnramifiedRelative (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsUnramified B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end Relative

section Stacks04Z0

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04Z0, part (4).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` — with no
representability hypothesis — is DM, in the sense of Definition 04YW, if and only if its first
relative diagonal `Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal `Δ_{f,2}`,
the relative diagonal of `Δ_{f,1}`, are both unramified in the relative sense of Properties of
Stacks, Section 04XB.

Definition 04YW is representability of `Δ_{f,1}` by algebraic spaces together with Section 04XB
unramifiedness of it; the representability clause is a theorem for a 1-morphism of *algebraic*
stacks — part (1) of Stacks 04XS — so the condition carried here is the Section 04XB clause alone
and the left-hand side is the first conjunct on the right. The second conjunct is unconditionally
true, which is the source's own proof: `Δ_{f,2}` is the relative diagonal of `Δ_{f,1}`, which is
representable by algebraic spaces, so part (3) of Stacks 050E — Stacks 05W6 applied at a diagonal
which is locally of finite type and a monomorphism by parts (2) and (3) of Stacks 04YQ — makes it
unramified with no hypothesis on `f`. -/
@[stacks 04Z0 "dm"]
theorem isDM_iff_isUnramifiedRelative_diagonals (f : 𝒳 ⟶ 𝒴) :
    IsDM B S hS f ↔
      (IsUnramifiedRelative B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom ∧
        IsUnramifiedRelative B S hS (relativeDiagonalAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)).hom) :=
  ⟨fun hf => ⟨hf.2, (isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
      B S hS (relativeDiagonalAlgebraicStacks B S hS f)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).2⟩,
    fun h => ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, h.1⟩⟩

end Stacks04Z0

end AlgebraicGeometry.Stack

end
