module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# Base change of a chart of a well-nigh affine stack along a representable 1-morphism

Let `h : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces, and let `x : 𝒮_U ⟶ 𝒳` be a finite 1-morphism from the algebraic stack of an
affine object `U` of the big fppf site. If `𝒳'` is well-nigh affine (Stacks 0DUL), then the
2-fibre product `𝒳' ×_𝒳 𝒮_U` is the algebraic stack of an affine object `W` of the site, and if
`x` is a chart of `𝒳` in the sense of Stacks 0DUL then its base change `𝒮_W ⟶ 𝒳'` is a chart of
`𝒳'`. This is the first step of the proof of Stacks 0DUQ: "`U' = 𝒳' ×_𝒳 U` is an algebraic space
with a finite (in particular affine) morphism `U' ⟶ 𝒳'`. By Lemma 0DUN we conclude that `U'` is
affine."

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isFinite`: a finite 1-morphism of
  algebraic stacks is affine.
* `AlgebraicGeometry.Stack.exists_isAffine_equivalenceOver_twoFibreProduct`: the apex of the
  base-change square is the algebraic stack of an affine object of the site.
* `AlgebraicGeometry.Stack.chartBaseChange_properties`: the base change of a chart is a chart.

## Implementation notes

The apex is represented by an algebraic space by Stacks 0300, since its projection to `𝒮_U` is a
base change of the representable `h`; it is well-nigh affine by Stacks 0DUN (2), since its
projection to `𝒳'` is a base change of the affine `x` (Stacks 0CHR); so it is affine by
Stacks 0DUN (1). The four properties of the base-changed chart are inherited as in the proof of
Stacks 0DUN (2): surjectivity by Stacks 04ZU, flatness by Stacks 06PY, and finiteness and
relative finite presentation by Stacks 045C.

## References

* [Stacks Project, Tag 0DUQ](https://stacks.math.columbia.edu/tag/0DUQ)
* [Stacks Project, Tag 0DUN](https://stacks.math.columbia.edu/tag/0DUN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **A finite 1-morphism of algebraic stacks is affine.** Both are relative properties in the
sense of Stacks 03YK, and a finite morphism of algebraic spaces is affine. -/
theorem isAffineHom_of_isFinite {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsFinite B S hS f) : IsAffineHom B S hS f := by
  obtain ⟨hrep, hfin⟩ := hf
  exact ⟨hrep, fun U y hy F hF he => Space.IsFinite.isAffineHom (hfin U y hy F hF he)⟩

end AlgebraicStacks

variable {B S hS}

section BaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)

/-- The canonical base-change square of a chart `x : 𝒮_U ⟶ 𝒳` along `h : 𝒳' ⟶ 𝒳`, in the
2-category of algebraic stacks. Its apex is `𝒳' ×_𝒳 𝒮_U`, its first leg goes to `𝒳'` and its
second to `𝒮_U`. -/
noncomputable abbrev chartBaseChangeSquare : Bicategory.TwoCommSq h x :=
  twoFibreProductSquareAlgebraicStacks B S hS h x

variable (B S hS) in
/-- The projection `𝒳' ×_𝒳 𝒮_U ⟶ 𝒮_U` is representable by algebraic spaces when `h` is: it is
a base change of `h` (Stacks 0302). -/
theorem isRepresentableByAlgebraicSpaces_chartBaseChangeSquare_snd
    (hh : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (chartBaseChangeSquare h x).snd.hom.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳'.val 𝒳.val
    (schemeStack.{u, w} B S hS U).val h.hom x.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        h.hom x.hom)) hh

/-- **Stacks 0300 for the base change of a chart.** The apex `𝒳' ×_𝒳 𝒮_U` is represented by an
algebraic space when `h` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpace_chartBaseChangeSquare_pt
    (hh : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom) :
    IsRepresentableByAlgebraicSpace B S hS (chartBaseChangeSquare h x).pt.val :=
  AlgebraicGeometry.isRepresentableByAlgebraicSpace_of_representable B S hS _ _
    (chartBaseChangeSquare h x).snd.hom
    (isRepresentableByAlgebraicSpaces_chartBaseChangeSquare_snd B S hS h x hh)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)

/-- **The base change of a finite chart along a representable 1-morphism to a well-nigh affine
stack is affine.** If `h : 𝒳' ⟶ 𝒳` is representable by algebraic spaces, `𝒳'` is well-nigh
affine and `x : 𝒮_U ⟶ 𝒳` is finite, then `𝒳' ×_𝒳 𝒮_U` is equivalent over the site to the
algebraic stack of an affine object `W` of the site.

This is the source's argument: `𝒳' ×_𝒳 U` is an algebraic space (Stacks 0300) with a finite,
in particular affine, morphism to `𝒳'` (Stacks 0CHR), so it is well-nigh affine by Stacks 0DUN (2)
and affine by Stacks 0DUN (1). -/
theorem exists_isAffine_equivalenceOver_chartBaseChange
    (hh : IsRepresentableByAlgebraicSpaces B S hS h.hom.hom)
    (h𝒳' : IsWellNighAffine.{u, w} B S hS 𝒳') (hx : AlgebraicStacks.IsFinite B S hS x) :
    ∃ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (schemeStack.{u, w} B S hS W).val.val.p (chartBaseChangeSquare h x).pt.val.val.p) := by
  set Q := chartBaseChangeSquare h x with hQ
  have hQtfp : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h x
  obtain ⟨F, hF, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_chartBaseChangeSquare_pt h x hh
  have haff : AlgebraicStacks.IsAffineHom B S hS Q.fst :=
    AlgebraicStacks.isAffineHom_snd_of_isTwoFibreProduct B S hS Q.swap
      (Bicategory.isTwoFibreProduct_swap hQtfp)
      (AlgebraicStacks.isAffineHom_of_isFinite B S hS x hx)
  have hwna : IsWellNighAffine.{u, w} B S hS Q.pt :=
    isWellNighAffine_of_isAffineHom B S hS Q.fst haff h𝒳'
  obtain ⟨T, hT, ⟨iT⟩⟩ := isAffineSpace_of_isWellNighAffine B S hS Q.pt hwna F hF eF
  exact ⟨T, hT, ⟨((PresheafOfCategories.sliceElementsEquivalenceOver T).trans
    (PresheafOfCategories.equivalenceOverOfIso iT.symm)).trans eF.symm⟩⟩

/-- **The base change of a chart is a chart.** If `x : 𝒮_U ⟶ 𝒳` is surjective, flat, finite and
of finite presentation, then so is the composite `𝒮_W ⟶ 𝒳' ×_𝒳 𝒮_U ⟶ 𝒳'` of any 1-morphism
whose underlying functor is an equivalence with the projection of the base-change square. -/
theorem chartBaseChange_properties {W : BigFppfOver B S hS}
    (k : schemeStack.{u, w} B S hS W ⟶ (chartBaseChangeSquare h x).pt)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom))
    (hsurj : IsSurjective B S hS x) (hflat : AlgebraicStacks.IsFlat B S hS x)
    (hfin : AlgebraicStacks.IsFinite B S hS x)
    (hfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS x) :
    IsSurjective B S hS (k ≫ (chartBaseChangeSquare h x).fst) ∧
      AlgebraicStacks.IsFlat B S hS (k ≫ (chartBaseChangeSquare h x).fst) ∧
        AlgebraicStacks.IsFinite B S hS (k ≫ (chartBaseChangeSquare h x).fst) ∧
          AlgebraicStacks.IsRelativelyFinitePresentation B S hS
            (k ≫ (chartBaseChangeSquare h x).fst) := by
  have hQtfp : Bicategory.IsTwoFibreProduct (chartBaseChangeSquare h x) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h x
  have hid𝒳' : Functor.IsEquivalence (BasedFunctor.id 𝒳'.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳'.val.val.obj))
  have hk' : Functor.IsEquivalence k.hom.hom.toFunctor := hk
  obtain ⟨hrepx, hfinbody⟩ := hfin
  obtain ⟨-, hfpbody⟩ := hfp
  have hrepQ : IsRepresentableByAlgebraicSpaces B S hS (chartBaseChangeSquare h x).fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (schemeStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val x.hom h.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        h.hom x.hom) hrepx
  have hrepk :
      IsRepresentableByAlgebraicSpaces B S hS (k ≫ (chartBaseChangeSquare h x).fst).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      (k ≫ (chartBaseChangeSquare h x).fst).hom.hom
      (chartBaseChangeSquare h x).fst.hom.hom k.hom.hom (BasedFunctor.id 𝒳'.val.val)
      (Iso.refl _)).1 hrepQ
  refine ⟨?_, ?_, ⟨hrepk, ?_⟩, ⟨hrepk, ?_⟩⟩
  · exact isSurjective_comp_of_isEquivalence B S hS k (chartBaseChangeSquare h x).fst hk
      (isSurjective_of_isTwoFibreProduct B S hS (chartBaseChangeSquare h x).swap
        (Bicategory.isTwoFibreProduct_swap hQtfp) hsurj)
  · exact AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS k (chartBaseChangeSquare h x).fst hk
      (AlgebraicStacks.isFlat_baseChange B S hS x h (chartBaseChangeSquare h x) hQtfp hflat)
  · exact relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinite B S hS m.hom) (k ≫ (chartBaseChangeSquare h x).fst).hom.hom
      (chartBaseChangeSquare h x).fst.hom.hom
      k.hom.hom (BasedFunctor.id 𝒳'.val.val) (Iso.refl _)
      (relativeProperty_baseChange.{u, u, u + 1} B S hS
        (fun _ _ m => Space.IsFinite B S hS m.hom)
        (schemeStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val x.hom h.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          h.hom x.hom) hfinbody)
  · exact relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinitePresentation B S hS m.hom)
      (k ≫ (chartBaseChangeSquare h x).fst).hom.hom (chartBaseChangeSquare h x).fst.hom.hom
      k.hom.hom (BasedFunctor.id 𝒳'.val.val) (Iso.refl _)
      (relativeProperty_baseChange.{u, u, u + 1} B S hS
        (fun _ _ m => Space.IsFinitePresentation B S hS m.hom)
        (schemeStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val x.hom h.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} h.hom x.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          h.hom x.hom) hfpbody)

end BaseChange

end AlgebraicGeometry.Stack

end
