module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable

/-!
# Carrying an open substack along an equivalence of algebraic stacks (Stacks 0506)

`AlgebraicGeometry.Stack.OpenSubstack` is the open substack of **Stacks 04YM**: a property of the
objects of an algebraic stack `𝒳`, closed under isomorphism, whose full subcategory is an
algebraic stack with open-immersion inclusion. This module carries an open substack along a
1-morphism `F : 𝒳 ⟶ 𝒴` of algebraic stacks admitting a quasi-inverse based functor `G` with
`F ∘ G ≅ id`: the inclusion of the open substack composed with `F` is again an open immersion,
and by **Stacks 0506** the essential image of an open immersion is an open substack of its
target, received by an equivalence of full subcategories over the two inclusions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse`: an open
  immersion of algebraic stacks stays one after composition with a 1-morphism admitting a
  quasi-inverse.
* `AlgebraicGeometry.Stack.exists_openSubstack_comp_of_quasiInverse`: an open substack of `𝒳`
  carried to one of `𝒴` along such a 1-morphism, together with the equivalence of full
  subcategories over the two inclusions.
* `AlgebraicGeometry.Stack.exists_openSubstack_of_representingEquivalence`: an open substack of
  the stack of an algebraic space representing `𝒴` gives an open substack of `𝒴`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0502](https://stacks.math.columbia.edu/tag/0502)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` admitting a quasi-inverse based
functor `G` with `F ∘ G ≅ id`, and let `j : 𝒲 ⟶ 𝒳` be an open immersion in the sense of
**Stacks 04YL**, part (1). Then `j ≫ F` is an open immersion. -/
theorem AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse
    (j : 𝒲 ⟶ 𝒳) (F : 𝒳 ⟶ 𝒴) (G : 𝒴.val.val ⥤ᵇ 𝒳.val.val)
    (ν : BasedFunctor.comp F.hom.hom G ≅ BasedFunctor.id 𝒳.val.val)
    (hG : Functor.IsEquivalence G.toFunctor)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j) :
    AlgebraicStacks.IsOpenImmersion B S hS (j ≫ F) := by
  have ha : Functor.IsEquivalence (BasedFunctor.id 𝒲.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒲.val.val.obj))
  have α : BasedFunctor.comp (BasedFunctor.id 𝒲.val.val) j.hom.hom ≅
      BasedFunctor.comp (j ≫ F).hom.hom G :=
    (Bicategory.whiskerLeftIso j.hom.hom ν).symm
  refine ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (j ≫ F).hom.hom j.hom.hom (BasedFunctor.id 𝒲.val.val) G α).1 hj.1, ?_⟩
  exact relativeProperty_of_equivalences B S hS (Space.openImmersionProperty B S hS)
    (j ≫ F).hom.hom j.hom.hom (BasedFunctor.id 𝒲.val.val) G α hj.2

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` admitting a quasi-inverse based
functor `G` with `F ∘ G ≅ id`, and let `W` be an open substack of `𝒳`. Then there is an open
substack `V` of `𝒴` whose full subcategory is equivalent to that of `W` over the two inclusions:
the equivalence composed with the inclusion of `V` is 2-isomorphic to the inclusion of `W`
composed with `F`. -/
theorem exists_openSubstack_comp_of_quasiInverse
    (W : OpenSubstack 𝒳) (F : 𝒳 ⟶ 𝒴) (G : 𝒴.val.val ⥤ᵇ 𝒳.val.val)
    (ν : BasedFunctor.comp F.hom.hom G ≅ BasedFunctor.id 𝒳.val.val)
    (hG : Functor.IsEquivalence G.toFunctor) :
    ∃ (V : OpenSubstack 𝒴)
      (c : fullSubcategoryAlgebraicStack 𝒳 W.property W.isAlgebraic ⟶
        fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic),
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor c.hom) ∧
        Nonempty (c ≫ V.inclusion B S hS ≅ W.inclusion B S hS ≫ F) := by
  have hi : AlgebraicStacks.IsOpenImmersion B S hS (W.inclusion B S hS ≫ F) :=
    AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse B S hS _ F G ν hG W.isOpenImmersion
  have hiImm : AlgebraicStacks.IsImmersion B S hS (W.inclusion B S hS ≫ F) :=
    ⟨hi.1, fun U y hy E hE he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U y hy E hE he)⟩
  have hA := AlgebraicStacks.isAlgebraicStack_essImage (W.inclusion B S hS ≫ F) hiImm
  obtain ⟨c, hce, hcα⟩ :=
    AlgebraicStacks.exists_isEquivalence_to_essImage (W.inclusion B S hS ≫ F) hiImm hA
  exact ⟨⟨(CatFiberedInGroupoids.homFunctor (W.inclusion B S hS ≫ F).hom).essImage,
    inferInstance, hA,
    AlgebraicStacks.isOpenImmersion_essImageInclusion (W.inclusion B S hS ≫ F) hi hiImm hA⟩,
    c, hce, hcα⟩

/-- Let `𝒴` be an algebraic stack over `S` represented by an algebraic space `Fsp` through an
equivalence `e` of **Stacks 04SW**, and let `W` be an open substack of the algebraic stack of
`Fsp`. Then there is an open substack `V` of `𝒴` whose full subcategory is equivalent to that of
`W` over the two inclusions, the chart of the representing equivalence mediating. -/
theorem exists_openSubstack_of_representingEquivalence
    (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (Fsp ⋙ typeToCat)).p)
    (W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS Fsp hFsp)) :
    ∃ (V : OpenSubstack 𝒴)
      (c : fullSubcategoryAlgebraicStack (algebraicSpaceStack.{u, w} B S hS Fsp hFsp)
          W.property W.isAlgebraic ⟶
        fullSubcategoryAlgebraicStack 𝒴 V.property V.isAlgebraic),
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor c.hom) ∧
        Nonempty (c ≫ V.inclusion B S hS ≅ W.inclusion B S hS ≫
          Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
            (representingEquivalence B S hS Fsp 𝒴.val e).functor)) :=
  exists_openSubstack_comp_of_quasiInverse B S hS W _
    (representingEquivalence B S hS Fsp 𝒴.val e).inverse
    (representingEquivalence B S hS Fsp 𝒴.val e).unitIso
    (representingEquivalence B S hS Fsp 𝒴.val e).symm.equiv.isEquivalence_functor

end AlgebraicGeometry.Stack

end
