module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.StackInSetoidsDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FppfLocalLifts
public import StacksFrontier.CategoryTheory.TwoFibreProduct.ElementsSpan
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Fppf-local lifts along a representable surjective flat 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is representable by algebraic spaces (Stacks 02ZW), and suppose that `f` is
surjective, flat and locally of finite presentation in the relative sense of Stacks 03YK. Then
every object `y` of `𝒴` is covered, in the associated fppf site of `𝒴` (Stacks 06TP), by a single
object of the form `f(x)`: there are an object `x` of `𝒳` and a morphism `f(x) ⟶ y` whose
generated sieve is a covering sieve of `y`.

The hypotheses are stated as properties of the structure morphism
`AlgebraicGeometry.Stack.baseChangeStructureMap` of the algebraic space representing each base
change of `f`; by `AlgebraicGeometry.Stack.prop_baseChangeStructureMap` they follow from the
relative properties `AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK.

## Main results

* `AlgebraicGeometry.Stack.exists_singleton_fppf_lift`: every object of `𝒴` is fppf-locally
  the image of an object of `𝒳`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v w

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces, and assume that the structure morphism of the
algebraic space representing the base change of `f` along any scheme-valued point of `𝒴` is
surjective, flat and locally of finite presentation. Then every object `y` of `𝒴` admits a
morphism `f(x) ⟶ y` from the image of an object `x` of `𝒳` whose generated sieve covers `y` in
the associated fppf site of `𝒴`. -/
@[stacks 06XH "part (1): fppf-local lifts along a surjective flat morphism"]
theorem exists_singleton_fppf_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsurj : ∀ (U : BigFppfOver B S hS) (q : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (hq : q ⋙ 𝒴.val.p = Over.map U.hom),
      Space.IsSurjective B S hS (baseChangeStructureMap B S hS f.hom hf U q hq).hom)
    (hflat : ∀ (U : BigFppfOver B S hS) (q : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (hq : q ⋙ 𝒴.val.p = Over.map U.hom),
      Space.IsFlat B S hS (baseChangeStructureMap B S hS f.hom hf U q hq).hom)
    (hlfp : ∀ (U : BigFppfOver B S hS) (q : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (hq : q ⋙ 𝒴.val.p = Over.map U.hom),
      Space.IsLocallyOfFinitePresentation B S hS
        (baseChangeStructureMap B S hS f.hom hf U q hq).hom)
    (y : 𝒴.val.obj) :
    ∃ (x : 𝒳.val.obj) (a : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y),
      Sieve.generate (Presieve.singleton a) ∈ fppfTopology B S hS 𝒴 y := by
  classical
  have h𝒴 : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.isFiberedInGroupoids
  let V : BigFppfOver B S hS := 𝒴.val.p.obj y
  let y₀ : 𝒴.val.p.Fiber V := ⟨y, rfl⟩
  let L := Functor.TwoYoneda.liftFunctor 𝒴.val.p h𝒴 V y₀
  let q : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj := Over.iteratedSliceBackward V ⋙ L
  have hq : q ⋙ 𝒴.val.p = Over.map V.hom := by
    change (Over.iteratedSliceBackward V ⋙ L) ⋙ 𝒴.val.p = Over.map V.hom
    rw [Functor.assoc, Functor.TwoYoneda.liftFunctor_w]
    exact Over.iteratedSliceBackward_forget V
  obtain ⟨W₀, j, hjcover, sec, hsec⟩ :=
    Space.exists_singleton_fppf_lift B S hS
      (baseChangeSpaceOverBase B S hS f.hom hf V q hq).property
      (isAlgebraicSpace_yoneda B S hS (Over.mk V.hom))
      (baseChangeStructureMap B S hS f.hom hf V q hq).hom
      (hsurj V q hq) (hflat V q hq) (hlfp V q hq) (Over.mk V.hom) (𝟙 (Over.mk V.hom))
  have hstr : (baseChangeSpaceOverBase B S hS f.hom hf V q hq).1.hom.app (op W₀) sec = j := by
    simpa using hsec
  set t := ((spacesOverSmallerBaseFunctorForgetIso B V.left.1 S V.left.2 hS V.hom).hom.app
    (baseChangeSpace B S hS f.hom hf V q hq)).app (op W₀) sec with ht
  have hψ : t.1.1 = j.left := by
    rw [ht, ← spacesOverSmallerBaseFunctor_hom_app_left B V.left.1 S V.left.2 hS V.hom
      (baseChangeSpace B S hS f.hom hf V q hq) (op W₀) sec, hstr]
  let W : BigFppfOver B V.left.1 V.left.2 := Over.mk t.1.1
  let Wb : Over V := (Over.iteratedSliceBackward V).obj W
  let ι₀ : W₀ ⟶ Wb.left := Over.homMk (𝟙 W₀.left) ((Category.id_comp _).trans t.2)
  have hι₀ : ι₀ ≫ Wb.hom = j :=
    Over.OverMorphism.ext ((Category.id_comp t.1.1).trans hψ)
  let cart : q.obj W ⟶ y := (Functor.TwoYoneda.chosenLift 𝒴.val.p h𝒴 V y₀ Wb).φ
  have hcart : 𝒴.val.p.IsHomLift Wb.hom cart :=
    (Functor.TwoYoneda.chosenLift 𝒴.val.p h𝒴 V y₀ Wb).isStronglyCartesian.toIsHomLift
  obtain ⟨e⟩ := nonempty_equivalenceOver_baseChangeSpace B S hS f.hom hf V q hq
  obtain ⟨x, -, i, hi, -⟩ := TwoFibreProductOver.exists_mk_of_section e W t.1.2
  have hihom : 𝒴.val.p.IsHomLift (𝟙 Wb.left) i.hom := hi
  have hvert : 𝒴.val.p.IsHomLift (𝟙 Wb.left) i.inv :=
    IsHomLift.lift_id_inv 𝒴.val.p Wb.left i
  have hα : 𝒴.val.p.IsHomLift Wb.hom (i.inv ≫ cart) := by
    simpa using IsHomLift.comp 𝒴.val.p (𝟙 Wb.left) Wb.hom i.inv cart
  have : 𝒴.val.p.IsFibered := h𝒴.isFibered
  have hR : Sieve.generate (Presieve.singleton (ι₀ ≫ Wb.hom)) ∈
      BigFppfOver.topology B S hS V := hι₀ ▸ hjcover
  have hfac : ∀ ⦃T : BigFppfOver B S hS⦄ (u : T ⟶ V),
      (Sieve.generate (Presieve.singleton (ι₀ ≫ Wb.hom))).arrows u →
      ∃ v : T ⟶ Wb.left, v ≫ Wb.hom = u := by
    rintro T u ⟨Y, w, c, ⟨⟩, rfl⟩
    exact ⟨w ≫ ι₀, by simp⟩
  exact ⟨x, i.inv ≫ cart, 𝒴.val.p.generate_singleton_mem_inheritedTopology_of_isHomLift
    (BigFppfOver.topology B S hS) (i.inv ≫ cart)
    (h𝒴.isStronglyCartesian_homLift _ _) Wb.hom hα hR hfac⟩

end AlgebraicGeometry.Stack

end
