module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition

/-!
# Étaleness of a 1-morphism read off its self-intersection

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, representable by algebraic spaces, whose base change along every scheme-valued point
of `𝒴` is surjective, flat and locally of finite presentation.  **Stacks 04XD** then lets the
relative properties of **Stacks 03YK** be tested on a single base change of `f`, namely along
`f` itself: writing `Q` for a 2-fibre product of `f` with itself, `f` has such a property exactly
when the induced morphism of representing presheaves out of `Q.pt` has it.

The reading recorded here is at étaleness, and with the apex of the square represented by a
scheme `R` of the site: if the first projection of `Q` is, as a morphism of the site, an étale
morphism `s : R ⟶ U` of schemes, then `f` is étale in the sense of **Stacks 04XB**.  The passage
from étaleness of `s` as a morphism of schemes to étaleness of the represented morphism of
algebraic spaces is the étale locality of étaleness on source and target.

This is the last step of the proof of **Stacks 06N0**: there `𝒴 = 𝒵`, `U = Spec k₀` is the
spectrum of the field of invariants, `R = R̄` is the arrow scheme of the quotient groupoid and
`s = s̄` its source map, which is étale by
`AlgebraicGeometry.GroupoidScheme.Division.etale_descended_source`.  What this theorem takes as
hypotheses are the identification of the self-intersection of `Spec k₀ ⟶ 𝒵` with `R̄` and of the
projection with `s̄`.

## Main results

* `AlgebraicGeometry.Space.isEtale_yoneda_map_iff`: a morphism of the site is étale as a morphism
  of schemes exactly when the represented morphism of algebraic spaces is étale.
* `AlgebraicGeometry.Stack.isRelativelyEtale_of_etale_representingMap_selfProduct`: the reading of
  étaleness off the self-intersection.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- **The represented morphism of algebraic spaces of a morphism of the site is étale exactly
when the morphism of schemes is.**  Étaleness of a morphism of algebraic spaces is the condition
of **Stacks 03XT**, part (7), on every étale chart, and that condition on a represented morphism
is the property itself because étaleness is étale local on source and target. -/
theorem isEtale_yoneda_map_iff (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U R : BigFppfOver B S hS} (s : R ⟶ U) :
    IsEtale B S hS (yoneda.map s) ↔ Etale ((BigFppfOver.toScheme B S hS).map s) :=
  (isEtale_iff_holdsOnEveryEtaleChart B S hS (isAlgebraicSpace_yoneda B S hS R)
      (isAlgebraicSpace_yoneda B S hS U) (yoneda.map s)).trans
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS etale_isEtaleLocalOnSourceAndTarget s)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04XD at étaleness, read off the self-intersection of the 1-morphism.**  Let
`f : 𝒳 ⟶ 𝒴` be representable by algebraic spaces and such that its base change along every
scheme-valued point of `𝒴` is surjective, flat and locally of finite presentation, and let `Q`
be a 2-fibre product of `f` with itself whose apex is represented by the scheme `R` of the site
and whose source `𝒳` is represented by the scheme `U`.  If the first projection of `Q` is,
under those identifications, an étale morphism `s : R ⟶ U` of schemes, then `f` is étale in the
sense of **Stacks 04XB**.

Stacks 04XD applies with the testing 1-morphism taken to be `f` itself, which is what makes the
single base change `Q` suffice. -/
theorem isRelativelyEtale_of_etale_representingMap_selfProduct
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hyv : yv ⋙ 𝒴.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yv
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsFlat B S hS h ∧
         Space.IsLocallyOfFinitePresentation B S hS h))
    (Q : Bicategory.TwoCommSq f f) (hQ : Bicategory.IsTwoFibreProduct Q)
    {U R : BigFppfOver B S hS}
    (eV : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (yoneda.obj R ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (s : R ⟶ U)
    (hs : representingMap B S hS Q.pt 𝒳 (yoneda.obj R) (yoneda.obj U) eV eW Q.fst =
      yoneda.map s)
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map s)) :
    IsRelativelyEtale B S hS f :=
  ⟨hf, hasRelativeProperty_of_prop_representingMap_of_fppf B S hS
    (Space.etaleMorphisms B S hS) 𝒳 𝒴 𝒳 f f hf hf hg Q hQ (yoneda.obj R) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS R) (isAlgebraicSpace_yoneda B S hS U) eV eW
    (show Space.IsEtale B S hS
        (representingMap B S hS Q.pt 𝒳 (yoneda.obj R) (yoneda.obj U) eV eW Q.fst) by
      rw [hs]
      exact (Space.isEtale_yoneda_map_iff B S hS s).2 hetale)⟩

end AlgebraicGeometry.Stack
