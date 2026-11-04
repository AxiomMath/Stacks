module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The source of an algebraic 1-morphism is an algebraic stack (Stacks 05XY)

Let `S` be a scheme contained in a big fppf site `B` and let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of
stacks in groupoids over the big fppf site of `S`. If `𝒴` is an algebraic stack and `F` is
*algebraic* in the sense of Stacks 06CF, then `𝒳` is an algebraic stack. This generalizes
Stacks 05UM, where `F` is assumed representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isAlgebraicMorphism`: if `𝒴` is an algebraic stack
  and `F : 𝒳 ⟶ 𝒴` is algebraic, then `𝒳` is an algebraic stack.

## Implementation notes

Of the four clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` for `𝒳`, the first two are the
hypotheses on `𝒳` and the diagonal clause is Stacks 0D3R
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isAlgebraicMorphism`) applied to `F` and to
the diagonal clause of `𝒴`. So only the presentation clause follows the source's argument: a
smooth surjective scheme atlas `ξ` of `𝒴` makes `𝒰 = (Sch/T)_{fppf} ×_{ξ, 𝒴} 𝒳` an algebraic
stack by the hypothesis on `F`, the projection `𝒰 ⟶ 𝒳` is representable by algebraic spaces,
surjective and smooth as a base change of `ξ` (Stacks 0302 and Stacks 045C), and a scheme atlas
of `𝒰` composed with it presents `𝒳` (Stacks 0301 and Stacks 045B). Unlike the source this needs
no appeal to Stacks 05UL, whose other two clauses are obtained more cheaply here, and so none of
the bootstrap input that Stacks 05UL carries in this library.

The 2-fibre product the hypothesis on `F` speaks about is taken over the relocalization
`CategoryTheory.Over.map T.hom` of the site, while the atlas of `𝒴` comes out of
`AlgebraicGeometry.Stack.IsAlgebraicStack` as a 1-morphism from
`AlgebraicGeometry.Stack.schemeFibredCategory`, i.e. over `CategoryTheory.Over.forget T`. The
iterated-slice equivalence moves the atlas to the former, and its representability and relative
properties move with it by the cheap half of Stacks 0457, namely
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source` fed to
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`
and to `AlgebraicGeometry.Stack.relativeProperty_of_forall_nonempty_equivalenceOver_fst`. The
apex of the canonical 2-fibre product square of the relocated atlas and `F`, with its two
projections exchanged, is then on the nose the category the hypothesis on `F` asserts to be an
algebraic stack, so the abstract-square forms of Stacks 0302 and Stacks 045C apply with no
further transport.

The hypothesis `h𝒳` is the sieve-indexed rendering `CategoryTheory.Functor.IsStack` of
Stacks 026F of the source's hypothesis that `𝒳` is a stack in groupoids, whose family-indexed
rendering of Stacks 02ZI is already carried by `CategoryTheory.StackInGroupoids`. The two are
the conditions (1) and (3) of Stacks 02ZJ and either may be assumed, but only the implication
from the sieve-indexed one to the family-indexed one is available in this library, while
`AlgebraicGeometry.Stack.IsAlgebraicStack` asks for both.

## References

* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 05XY](https://stacks.math.columbia.edu/tag/05XY)
* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
* [Stacks Project, Tag 0D3R](https://stacks.math.columbia.edu/tag/0D3R)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of `S`. If `𝒴`
is an algebraic stack and `F` is algebraic in the sense of Stacks 06CF, then `𝒳` is an algebraic
stack. -/
@[stacks 05XY]
theorem isAlgebraicStack_of_isAlgebraicMorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1}
      (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : 𝒳.toBasedCategory.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.toBasedCategory)
    (hf : IsAlgebraicMorphism.{u, w, w, w} B S hS (𝒳 := 𝒳) (𝒴 := 𝒴) f.hom) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.toBasedCategory := by
  obtain ⟨hYfib, hYstack, hYdiag, T, ξ, hξrep, hξprop⟩ := h𝒴
  let X : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳.toBasedCategory 𝒳.isStackInGroupoids.isFiberedInGroupoids
  let Y : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒴.toBasedCategory 𝒴.isStackInGroupoids.isFiberedInGroupoids
  let F : X ⟶ Y := Bicategory.InducedBicategory.mkHom f.hom
  let A : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.map T.hom))
      (Functor.IsFiberedInGroupoids.over_map T.hom)
  let back : A.val ⥤ᵇ (schemeFibredCategory B S hS T).val :=
    ⟨Over.iteratedSliceBackward T, rfl⟩
  have : Functor.IsEquivalence back.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (Over.iteratedSliceEquiv T).inverse)
  let ξ' : schemeFibredCategory B S hS T ⟶ Y := Bicategory.InducedBicategory.mkHom ξ
  let ya : A ⟶ Y := Bicategory.InducedBicategory.mkHom (BasedFunctor.comp back ξ)
  have he := fun (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ Y.val.obj)
      (hy : y ⋙ Y.val.p = Over.map V.hom) =>
    nonempty_equivalenceOver_fst_of_equivalence_source B S hS
      (𝒳' := A) (𝒳 := schemeFibredCategory B S hS T) (𝒴 := Y) back ξ V y hy
  have hyarep : IsRepresentableByAlgebraicSpaces B S hS ya.hom :=
    isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst he hξrep
  let Sq : Bicategory.TwoCommSq F ya :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} ya F).swap
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} ya F)
  have hπrep : IsRepresentableByAlgebraicSpaces B S hS Sq.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS A Y X ya F Sq hSq hyarep
  obtain ⟨hUfib, hUstack, hUdiag, V, b, hbrep, hbprop⟩ := hf T ya.hom.toFunctor ya.hom.w
  let b' : schemeFibredCategory B S hS V ⟶ Sq.pt := Bicategory.InducedBicategory.mkHom b
  have hb'rep : IsRepresentableByAlgebraicSpaces B S hS b'.hom := hbrep
  have hcomp : IsRepresentableByAlgebraicSpaces B S hS (b' ≫ Sq.fst).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS b' Sq.fst hb'rep hπrep
  have key : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)] [P.IsStableUnderComposition],
      HasRelativePropertyBased B S hS P ξ hξrep → HasRelativePropertyBased B S hS P b hbrep →
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS P (b' ≫ Sq.fst) hcomp := by
    intro P _ _ _ hξP hbP
    exact hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS P b' Sq.fst hb'rep hπrep hbP
      (hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS P A Y X ya F Sq hSq hyarep
        (relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS P ξ' ya he hξP))
  exact ⟨𝒳.isStackInGroupoids.isFiberedInGroupoids, ⟨h𝒳, 𝒳.isStackInGroupoids⟩,
    hasRepresentableDiagonal_of_isAlgebraicMorphism.{u, w, w} B S hS f hf hYdiag,
    V, (b' ≫ Sq.fst).hom, hcomp, fun W y hy G hG hE =>
    ⟨key (Space.surjectiveMorphismProperty B S hS)
        (fun V y hy G hG hE => (hξprop V y hy G hG hE).1)
        (fun V y hy G hG hE => (hbprop V y hy G hG hE).1) W y hy G hG hE,
      key (Space.smoothMorphismProperty B S hS)
        (fun V y hy G hG hE => (hξprop V y hy G hG hE).2)
        (fun V y hy G hG hE => (hbprop V y hy G hG hE).2) W y hy G hG hE⟩⟩

end AlgebraicGeometry.Stack

end
