module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Quasi-separatedness read off the relative diagonal

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained in a big fppf
site `B`, representable by algebraic spaces. Then the following are equivalent:

1. `f` is quasi-separated,
2. the relative diagonal `Δ_f` is quasi-compact, and
3. `Δ_f` is of finite type,

each condition on `Δ_f` being read in the sense of Properties of Stacks, Section 04XB.

## Main definitions

* `AlgebraicGeometry.Stack.IsFiniteType`: a 1-morphism representable by algebraic spaces is of
  finite type when the representing morphism of each of its base changes to a scheme is.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_isIso`: an isomorphism of algebraic spaces over `S`
  is quasi-compact.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_mono`: a monomorphism of algebraic spaces over `S`
  is quasi-separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal`:
  `f` is quasi-separated if and only if `Δ_f` is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompact_relativeDiagonal_of_isFiniteType`:
  if `Δ_f` is of finite type, it is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_relativeDiagonal_of_isQuasiCompact`:
  if `Δ_f` is quasi-compact, it is of finite type.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of algebraic spaces over `S` is quasi-compact. -/
theorem isQuasiCompact_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : IsQuasiCompact B S hS e := by
  intro Z hZ hqc g
  have hiso : IsIso (pullback.fst g e) := (IsPullback.of_hasPullback g e).isIso_fst_of_isIso
  exact hqc.of_iso B S hS (asIso (pullback.fst g e)).symm

/-- A monomorphism of algebraic spaces over `S` is quasi-separated. -/
theorem isQuasiSeparated_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    (hg : Mono g) : IsQuasiSeparated B S hS g := by
  have := hg
  exact isQuasiCompact_of_isIso B S hS (pullback.diagonal g)

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is of finite type* when every algebraic space representing
its base change along a scheme-valued point of the target has structural morphism of finite
type, read as a morphism of algebraic spaces over `S`. -/
abbrev IsFiniteType (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsFiniteType B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

namespace AlgebraicStacks

variable {𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is representable by algebraic
spaces is quasi-separated if and only if its relative diagonal `Δ_f` is quasi-compact. -/
@[stacks 04YT "the equivalence of parts (1) and (2)"]
theorem isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal (f : 𝒵 ⟶ 𝒯)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsQuasiSeparated B S hS f ↔
      Stack.IsQuasiCompact.{u, u, u + 1} B S hS
        (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom) :=
  ⟨fun h => h.1, fun h => ⟨h, fun U y hy F hF he => Space.isQuasiSeparated_of_mono B S hS _
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
      (subsingleton_representing_of_relativeDiagonal B S hS 𝒵.val 𝒯.val f.hom hf U y hy F he))⟩⟩

/-- If the relative diagonal `Δ_f` of a 1-morphism of algebraic stacks over `S` is of finite
type, then it is quasi-compact. -/
@[stacks 04YT "the implication (3) => (2)"]
theorem isQuasiCompact_relativeDiagonal_of_isFiniteType (f : 𝒵 ⟶ 𝒯)
    (h : Stack.IsFiniteType.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom)) :
    Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom) :=
  fun U y hy F hF he => (h U y hy F hF he).2

/-- If the relative diagonal `Δ_f` of a 1-morphism of algebraic stacks over `S` which is
representable by algebraic spaces is quasi-compact, then it is of finite type. -/
@[stacks 04YT "the implication (2) => (3)"]
theorem isFiniteType_relativeDiagonal_of_isQuasiCompact (f : 𝒵 ⟶ 𝒯)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (h : Stack.IsQuasiCompact.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom)) :
    Stack.IsFiniteType.{u, u, u + 1} B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val f.hom) :=
  fun U y hy F hF he =>
    ⟨(Stack.isLocallyOfFiniteType_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
        B S hS f hf).2 U y hy F hF he, h U y hy F hF he⟩

end AlgebraicStacks

end Stack

end AlgebraicGeometry

end
