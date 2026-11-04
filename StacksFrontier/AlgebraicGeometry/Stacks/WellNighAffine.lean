module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Well-nigh affine algebraic stacks (Stacks 0DUL)

An algebraic stack `𝒳` over `S` is *well-nigh affine* when there is an affine scheme `U` of the
big fppf site and a 1-morphism `𝒳_U ⟶ 𝒳` from the algebraic stack it represents which is
surjective, flat, finite and of finite presentation. This is the hypothesis the Keel–Mori
theorem of Stacks, More on Morphisms of Stacks, Section 13 is proved under.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite`: finiteness of a 1-morphism of algebraic
  stacks, as the relative property of **Stacks 03YK** at **Stacks 03ZP**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsRelativelyFinitePresentation`: finite
  presentation of a 1-morphism of algebraic stacks, as the relative property of **Stacks 03YK**
  at **Stacks 03XP**, part (3).
* `AlgebraicGeometry.Stack.IsWellNighAffine`: **Stacks 0DUL**.

## Implementation notes

Surjectivity is Stacks 04ZS (`AlgebraicGeometry.Stack.IsSurjective`, surjectivity of the induced
map on points) and flatness is Stacks 06PW
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat`, the existential smooth-diagram test of Stacks
06FM). Both are taken from the library as they stand.

Finiteness and finite presentation are *not* on the library's side yet, and are supplied here.
Both are stated as the relative property of **Stacks 03YK**: a 1-morphism representable by
algebraic spaces has the property when every algebraic space representing its base change along
a scheme-valued point of the target has structural morphism with the corresponding property of
morphisms of algebraic spaces — finiteness of Stacks 03ZP for
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite`, and finite presentation of Stacks 03XP, part
(3), for `AlgebraicGeometry.Stack.AlgebraicStacks.IsRelativelyFinitePresentation`. Each carries its
representability datum as an existential rather than as a hypothesis, so that a single
`IsWellNighAffine` witness contains everything a consumer needs.

The test is written out longhand rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack`: that definition carries the
base-change stability and target-locality of the property as instance arguments, and neither is
in the library for finiteness or for finite presentation of morphisms of algebraic spaces, so
going through it would mean carrying two hypotheses that the statement of Stacks 0DUL does not
have. Writing the quantifier out gives the same proposition.

Stacks 06Q2, part (2) defines finite presentation for an *arbitrary* 1-morphism of algebraic
stacks as local finite presentation together with quasi-compactness (Stacks 050U) and
quasi-separatedness (Stacks 04YW); the library has part (1)
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`) and Stacks 04YW, but
not Stacks 050U, whose own definition needs the topology on the points of an algebraic stack
(Stacks 04XL). The 1-morphisms Stacks 0DUL quantifies over are finite, hence representable by
algebraic spaces, and for a representable 1-morphism the two renderings agree; so the Stacks
03YK form used here is the statement of Stacks 0DUL and needs none of that chapter.

The affine scheme is read as an algebraic stack by `AlgebraicGeometry.Stack.schemeStack`
(**Stacks 0787**), the fibred category of its big fppf site, which is the object the
lisse-étale site is formed from.

## References

* [Stacks Project, Tag 0DUL](https://stacks.math.columbia.edu/tag/0DUL)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 03YK at Stacks 03ZP.** A 1-morphism of algebraic stacks over `S` *is finite* when it
is representable by algebraic spaces and every algebraic space representing its base change along
a scheme-valued point of the target has finite structural morphism, read as a morphism of
algebraic spaces over `S`. -/
abbrev IsFinite (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ _hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsFinite B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- **Stacks 03YK at Stacks 03XP, part (3).** A 1-morphism of algebraic stacks over `S` *is of
finite presentation* when it is representable by algebraic spaces and every algebraic space
representing its base change along a scheme-valued point of the target has structural morphism of
finite presentation, read as a morphism of algebraic spaces over `S`.

This is a different condition from `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinitePresentation`,
which is [Stacks, Tag 06Q2] part (2) — locally of finite presentation, quasi-compact and
quasi-separated — for an arbitrary 1-morphism.  No statement comparing the two is available, so
both are kept. -/
abbrev IsRelativelyFinitePresentation (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ _hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsFinitePresentation B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end AlgebraicStacks

/-- **Stacks 0DUL.** An algebraic stack over `S` is *well-nigh affine* when there is an object `U`
of the big fppf site of `S` with affine underlying scheme and a 1-morphism from the algebraic
stack it represents to `𝒳` which is surjective, flat, finite and of finite presentation. -/
@[stacks 0DUL]
abbrev IsWellNighAffine (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ U : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      ∃ f : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒳,
        Stack.IsSurjective B S hS f ∧
          AlgebraicStacks.IsFlat B S hS f ∧
            AlgebraicStacks.IsFinite B S hS f ∧
              AlgebraicStacks.IsRelativelyFinitePresentation B S hS f

end AlgebraicGeometry.Stack

end
