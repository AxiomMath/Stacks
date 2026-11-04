module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsSmoothDiagram
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
/-!
# Small models of categories fibred in groupoids and limit preservation

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` whose total
category is locally small at the universe of the schemes of the site, while its hom types live in
a larger universe; the stack of coherent sheaves `Coh_{X/B}` of Stacks 08KB is of this kind. The
total category with its hom types replaced by models in the universe of the site,
`CategoryTheory.BasedCategory.shrinkHoms`, is a category fibred in groupoids equivalent to `𝒳`
over the site, and it is an object of the 2-category at the universes of the site, at which the
smooth-diagram tests of Stacks 06FM are formed.

This file builds the small model of a locally small category fibred in groupoids and of a
1-morphism between two such, and shows that being limit preserving on objects (Stacks 06CU)
passes to the small models. With Stacks 0CMY, (2) ⟹ (3), for categories fibred in groupoids
(`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_isLimitPreservingOnObjects`), a
1-morphism limit preserving on objects therefore has a small model which is locally of finite
presentation in the sense of Stacks 06Q2, part (1).

All declarations below are in the namespace `AlgebraicGeometry.Stack`.

## Main definitions

* `smallHomsModel`: the small model of a locally small category fibred in groupoids.
* `smallHomsModelMap`: the 1-morphism of small models induced by a 1-morphism.

## Main results

* `isLimitPreservingOnObjects_smallHomsModelMap`: a 1-morphism limit preserving on objects has a
  small model limit preserving on objects.
* `hasPropertyOnEverySmoothDiagram_smallHomsModelMap_of_isLimitPreservingOnObjects`: such a
  1-morphism has a small model passing the universal smooth-diagram test of Stacks 06FM at local
  finite presentation, which is Stacks 06Q2, part (1).

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small model of a locally small category fibred in groupoids**: its total category with
the hom types replaced by their models in the universe of the site. -/
def smallHomsModel (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS))
    [LocallySmall.{u} 𝒳.val.obj] :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk 𝒳.val.shrinkHoms
    (BasedCategory.isFiberedInGroupoids_shrinkHoms 𝒳.val 𝒳.isFiberedInGroupoids)

variable {B S hS}

/-- **The 1-morphism of small models induced by a 1-morphism** of locally small categories
fibred in groupoids: the given functor, read through the comparison equivalences of
`CategoryTheory.ShrinkHoms`. -/
def smallHomsModelMap {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] [LocallySmall.{u} 𝒴.val.obj] (f : 𝒳 ⟶ 𝒴) :
    smallHomsModel B S hS 𝒳 ⟶ smallHomsModel B S hS 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (BasedFunctor.comp ⟨ShrinkHoms.inverse.{u} 𝒳.val.obj, rfl⟩ f.hom)
      ⟨ShrinkHoms.functor.{u} 𝒴.val.obj, BasedCategory.shrinkHoms_functor_comp 𝒴.val⟩)

/-- The inverse of `ShrinkHoms.functor` undoes it on morphisms. -/
private theorem map_inverse_map_shrinkHoms_functor {C : Type*} [Category C] [LocallySmall.{u} C]
    {a b : C} (φ : a ⟶ b) :
    (ShrinkHoms.inverse.{u} C).map ((ShrinkHoms.functor.{u} C).map φ) = φ :=
  (equivShrink _).symm_apply_apply φ

/-- Morphisms over `g` in `𝒳` stay over `g` in the small model. -/
private theorem isHomLift_map_shrinkHoms_functor
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] {R R' : BigFppfOver B S hS} (g : R ⟶ R')
    {a b : 𝒳.val.obj} (φ : a ⟶ b) (h : 𝒳.val.p.IsHomLift g φ) :
    (smallHomsModel B S hS 𝒳).val.p.IsHomLift g ((ShrinkHoms.functor.{u} 𝒳.val.obj).map φ) :=
  (Functor.isHomLift_comp_iff (ShrinkHoms.inverse.{u} 𝒳.val.obj) 𝒳.val.p g _).2
    (by rwa [map_inverse_map_shrinkHoms_functor])

/-- Morphisms over `g` in `𝒳` become strongly cartesian in the small model. -/
private theorem isStronglyCartesian_map_shrinkHoms_functor
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] {R R' : BigFppfOver B S hS} (g : R ⟶ R')
    {a b : 𝒳.val.obj} (φ : a ⟶ b) (h : 𝒳.val.p.IsHomLift g φ) :
    (smallHomsModel B S hS 𝒳).val.p.IsStronglyCartesian g
      ((ShrinkHoms.functor.{u} 𝒳.val.obj).map φ) :=
  haveI := isHomLift_map_shrinkHoms_functor g φ h
  Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift
    (smallHomsModel B S hS 𝒳).isFiberedInGroupoids _ _

/-- **Limit preservation on objects passes to the small models.** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of
locally small categories fibred in groupoids is limit preserving on objects (Stacks 06CU), so is
the induced 1-morphism of small models: a datum over the small models is read in `𝒳` and `𝒴`
through the comparison functors of `CategoryTheory.ShrinkHoms`, which are the identity on objects
and bijective on morphisms, descended there, and read back. Every morphism of a category fibred
in groupoids is strongly cartesian over its image (Stacks 003V), so only the lifting conditions
need transporting. -/
theorem isLimitPreservingOnObjects_smallHomsModelMap
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] [LocallySmall.{u} 𝒴.val.obj] (f : 𝒳 ⟶ 𝒴)
    (hf : BigFppfOver.IsLimitPreservingOnObjects.{u, w, w'} B S hS 𝒳 𝒴 f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, w, w'} B S hS (smallHomsModel B S hS 𝒳)
      (smallHomsModel B S hS 𝒴) (smallHomsModelMap f) := by
  intro I _ _ D c hc i y x γ hγ
  let inc := BigAffineFppf.inclusion B S hS
  let iX := ShrinkHoms.inverse.{u} 𝒳.val.obj
  let iY := ShrinkHoms.inverse.{u} 𝒴.val.obj
  let jX := ShrinkHoms.functor.{u} 𝒳.val.obj
  let jY := ShrinkHoms.functor.{u} 𝒴.val.obj
  have hX : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  have hY : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.isFiberedInGroupoids
  let x₀ : 𝒳.val.p.Fiber (inc.obj c.pt) := ⟨iX.obj x.1, x.2⟩
  let y₀ : 𝒴.val.p.Fiber (inc.obj (D.obj i)) := ⟨iY.obj y.1, y.2⟩
  let γ₀ : (CatFiberedInGroupoids.homFunctor f).obj x₀.1 ⟶ y₀.1 := iY.map γ
  have hγ₀ : 𝒴.val.p.IsStronglyCartesian (inc.map (c.π.app i)) γ₀ := by
    have : 𝒴.val.p.IsHomLift (inc.map (c.π.app i)) γ₀ :=
      (Functor.isHomLift_comp_iff iY 𝒴.val.p _ γ).1 hγ.toIsHomLift
    exact Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hY _ _
  obtain ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ := hf I D c hc i y₀ x₀ γ₀ hγ₀
  have eY' : ∀ {a b : ShrinkHoms 𝒴.val.obj} (φ : a ⟶ b), jY.map (iY.map φ) = φ :=
    fun φ => (equivShrink _).apply_symm_apply φ
  refine ⟨i', j, ⟨jX.obj x'.1, x'.2⟩, ⟨jX.obj xU.1, xU.2⟩, jX.map δ, jX.map β, jY.map γ', ?_,
    isHomLift_map_shrinkHoms_functor _ β hβ, Functor.map_isIso jX β, ?_, ?_⟩
  · exact isStronglyCartesian_map_shrinkHoms_functor _ δ hδ.toIsHomLift
  · exact isStronglyCartesian_map_shrinkHoms_functor _ γ' hγ'.toIsHomLift
  · show jY.map (f.hom.toFunctor.map (iX.map (jX.map δ))) ≫ jY.map γ' =
      jY.map (f.hom.toFunctor.map (iX.map (jX.map β))) ≫ γ
    rw [map_inverse_map_shrinkHoms_functor, map_inverse_map_shrinkHoms_functor, ← eY' γ]
    exact (jY.map_comp _ _).symm.trans ((congrArg jY.map hcomm).trans (jY.map_comp _ _))

/-- **Stacks 0CMY, (2) ⟹ (3), on small models.** A 1-morphism of locally small categories fibred
in groupoids which is limit preserving on objects (Stacks 06CU) has a small model passing the
universal smooth-diagram test of Stacks 06FM at local finite presentation of morphisms of
algebraic spaces, which is Stacks 06Q2, part (1). -/
theorem hasPropertyOnEverySmoothDiagram_smallHomsModelMap_of_isLimitPreservingOnObjects
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.val.obj] [LocallySmall.{u} 𝒴.val.obj] (f : 𝒳 ⟶ 𝒴)
    (hf : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f) :
    HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) (smallHomsModelMap f) :=
  hasPropertyOnEverySmoothDiagram_of_isLimitPreservingOnObjects B S hS _
    (isLimitPreservingOnObjects_smallHomsModelMap f hf)

end AlgebraicGeometry.Stack

end
