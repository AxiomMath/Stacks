module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.Sites.Gerbe.BaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.IsoClasses
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget

/-!
# Restricting a gerbe to an open of its target

Let `W` be an open substack of an algebraic stack `𝒳` over `S` and let `g : W ⟶ 𝒴` make `W` a
gerbe over `𝒴`. For an open immersion `j : 𝒱 ⟶ 𝒴`, the base change `W ×_𝒴 𝒱` is a gerbe over
`𝒱` (**Stacks 06QE**) and is identified, by **Stacks 0506**, with an open substack of `𝒳`. This
is the step of Stacks 0GWC that replaces the base of a gerbe by an open of it.

## Main results

* `CategoryTheory.isGerbeOver_of_isEquivalenceOver`: an equivalence over the base is a gerbe.
* `CategoryTheory.BasedCategory.Equivalence.isGerbeOver_functor`: so is the forward 1-morphism of
  an equivalence in the 2-category of categories over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isGerbeOver_comp`: **Stacks 06R8**, composites of
  gerbes of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_openSubstack_isGerbeOver_of_isOpenImmersion`:
  the restriction of a gerbe to an open of its target.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_of_isOpenImmersion_representingMap`:
  a 1-morphism of represented algebraic stacks inducing an open immersion of the representing
  algebraic spaces is an open immersion.

## Implementation notes

The open substack is the essential image of `W ×_𝒴 𝒱 ⟶ W ⟶ 𝒳`, and the 1-morphism from it to `𝒱`
is the quasi-inverse over the site of `AlgebraicGeometry.Stack.AlgebraicStacks.essImageEquivalence`
followed by the projection to `𝒱`; a quasi-inverse over the site is an equivalence over the site,
hence a gerbe, and gerbes compose.

## References

* [Stacks Project, Tag 0501](https://stacks.math.columbia.edu/tag/0501)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06R8](https://stacks.math.columbia.edu/tag/06R8)
* [Stacks Project, Tag 0GWC](https://stacks.math.columbia.edu/tag/0GWC)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₁} 𝒴]

/-- **An equivalence over the base is a gerbe.** If `a : 𝒳 ⥤ 𝒴` is an equivalence over `𝒞`
and `𝒴` is fibred in groupoids over `𝒞`, then `a` makes `𝒳` a gerbe over `𝒴`. -/
theorem isGerbeOver_of_isEquivalenceOver (J : GrothendieckTopology 𝒞) {p : 𝒳 ⥤ 𝒞}
    {q : 𝒴 ⥤ 𝒞} {a : 𝒳 ⥤ 𝒴} (ha : a ⋙ q = p) (e : Functor.IsEquivalenceOver p q a)
    (hq : q.IsFiberedInGroupoids) : IsGerbeOver J q a := by
  subst ha
  exact IsGerbeOver.of_isEquivalenceOver_base_symm (F' := 𝟭 𝒴) (Functor.comp_id a) e
    (isGerbeOver_id J hq)

/-- The forward 1-morphism of an equivalence over `𝒞` in the sense of
`CategoryTheory.BasedCategory.Equivalence` is an equivalence over `𝒞` in the sense of
`CategoryTheory.Functor.IsEquivalenceOver`. -/
noncomputable def BasedCategory.Equivalence.toFunctorIsEquivalenceOver
    {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞} (E : BasedCategory.Equivalence 𝒳 𝒴) :
    Functor.IsEquivalenceOver 𝒳.p 𝒴.p E.functor.toFunctor where
  inv := E.inverse.toFunctor
  inv_over := E.inverse.w
  unitIso := BasedFunctor.toFunctorIso E.functor E.inverse E.unitIso
  counitIso := BasedFunctor.toFunctorIso E.inverse E.functor E.counitIso
  unit_vertical X := by
    have h := E.unitIso.hom.isHomLift' X
    rwa [← IsHomLift.domain_eq 𝒳.p (𝟙 (𝒳.p.obj X)) (E.unitIso.hom.app X)] at h
  counit_vertical X := by
    have h := E.counitIso.hom.isHomLift' X
    rwa [← IsHomLift.domain_eq 𝒴.p (𝟙 (𝒴.p.obj X)) (E.counitIso.hom.app X)] at h

/-- **The forward 1-morphism of an equivalence over the base is a gerbe**, when the target is
fibred in groupoids. -/
theorem BasedCategory.Equivalence.isGerbeOver_functor (J : GrothendieckTopology 𝒞)
    {𝒳 𝒴 : BasedCategory.{v₁, u₂} 𝒞} (E : BasedCategory.Equivalence 𝒳 𝒴)
    (h𝒴 : 𝒴.p.IsFiberedInGroupoids) : IsGerbeOver J 𝒴.p E.functor.toFunctor :=
  isGerbeOver_of_isEquivalenceOver J E.functor.w E.toFunctorIsEquivalenceOver h𝒴

end CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06R8.** A composite of 1-morphisms of algebraic stacks each of which makes its
source a gerbe over its target makes its source a gerbe over the final target. -/
theorem isGerbeOver_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (g : 𝒴 ⟶ 𝒵) (hf : IsGerbeOver B S hS f) (hg : IsGerbeOver B S hS g) :
    IsGerbeOver B S hS (f ≫ g) := by
  have hf' : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS)
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒵.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom) := by
    rw [CatFiberedInGroupoids.homFunctor_comp_p]
    exact hf
  exact hf'.comp hg

/-- **The forward 1-morphism of an equivalence of algebraic stacks over the site is a gerbe.** -/
theorem isGerbeOver_mkHom_basedEquivalence {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (E : BasedCategory.Equivalence 𝒳.val.val 𝒴.val.val) :
    IsGerbeOver B S hS (Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom E.functor) : 𝒳 ⟶ 𝒴) :=
  E.isGerbeOver_functor _ 𝒴.val.property

/-- **A gerbe restricts to an open of its target.** Let `W` be an open substack of an algebraic
stack `𝒳`, let `g : W ⟶ 𝒴` make `W` a gerbe over `𝒴`, and let `j : 𝒱 ⟶ 𝒴` be an open immersion.
Then some open substack `𝒰` of `𝒳` is a gerbe over `𝒱`.

`𝒰` is the image in `𝒳` of the base change `W ×_𝒴 𝒱`, which is a gerbe over `𝒱` by
**Stacks 06QE** and is carried isomorphically onto its image by **Stacks 0506**, the composite
`W ×_𝒴 𝒱 ⟶ W ⟶ 𝒳` being an open immersion by **Stacks 0501** and **Stacks 0502**. -/
theorem exists_openSubstack_isGerbeOver_of_isOpenImmersion
    {𝒳 𝒴 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳)
    (g : W.toAlgebraicStack ⟶ 𝒴) (hg : IsGerbeOver B S hS g) (j : 𝒱 ⟶ 𝒴)
    (hj : IsOpenImmersion B S hS j) :
    ∃ (𝒰 : OpenSubstack 𝒳) (h : 𝒰.toAlgebraicStack ⟶ 𝒱), IsGerbeOver B S hS h := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS g j
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g j
  let i := P.fst ≫ W.inclusion
  have hi : IsOpenImmersion B S hS i :=
    isOpenImmersion_comp B S hS _ _
      (isOpenImmersion_baseChange_snd B S hS P.swap (Bicategory.isTwoFibreProduct_swap hP) hj)
      W.isOpenImmersion
  have hiImm : IsImmersion B S hS i :=
    ⟨hi.1, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U y hy F hF he)⟩
  let 𝒰 : OpenSubstack 𝒳 :=
    ⟨(CatFiberedInGroupoids.homFunctor i.hom).essImage, inferInstance,
      isAlgebraicStack_essImage i hiImm,
      isOpenImmersion_essImageInclusion i hi hiImm (isAlgebraicStack_essImage i hiImm)⟩
  let E := essImageEquivalence i hiImm
  refine ⟨𝒰, Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom E.inverse) ≫ P.snd, ?_⟩
  exact isGerbeOver_comp B S hS _ _
    (isGerbeOver_mkHom_basedEquivalence B S hS (𝒳 := 𝒰.toAlgebraicStack) (𝒴 := P.pt) E.symm)
    (isGerbeOver_of_isTwoFibreProduct B S hS P hP hg)

/-- **A 1-morphism between represented algebraic stacks is an open immersion when the induced
morphism of representing algebraic spaces is.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` with `𝒳` and `𝒴` represented by algebraic spaces `F` and `G`. If the induced
morphism `F ⟶ G` of representing presheaves (**Stacks 04SW**) is an open immersion, then `f` is
an open immersion (**Stacks 04YL**): it is representable by algebraic spaces, its source being
represented by one, and by the bridge of Stacks 04XB for represented source and target its
relative open-immersion property is that of `F ⟶ G`. -/
theorem isOpenImmersion_of_isOpenImmersion_representingMap
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳.val)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (hf : Space.IsOpenImmersion B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom)) :
    IsOpenImmersion B S hS f := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property h𝒳 f.hom
  exact ⟨hrep, (hasRelativeProperty_iff_prop_representingMap B S hS
    (Space.openImmersionProperty B S hS) f.hom hrep F G hF hG eF eG).2 hf⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
