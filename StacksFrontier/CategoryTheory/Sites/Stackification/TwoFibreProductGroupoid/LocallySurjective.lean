module

public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections

/-!
# Stacks 04Y2: local surjectivity on morphism presheaves

This file is the second part of the proof of Stacks 04Y2 (the stackification of a 2-fibre product
is the 2-fibre product of the stackifications), assembled in
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid`. For a morphism `H` of
2-fibre products carrying vertical 2-isomorphisms `γ`, `δ` to `π₁ ⋙ i` and `π₂ ⋙ k`, it builds the
vertical comparisons `gammaFiberIso`, `deltaFiberIso`, the comparison identities and dictionaries
between sections of `Mor(i x, i x')` coming from `𝒳` and from the 2-fibre product, and proves the
fibre-product condition after applying `j` and the crux squares. The conclusion is
`isLocallySurjective_morPresheafMap`: the map of morphism presheaves induced by `H` is locally
surjective.

## References

* [StacksProject 04Y2](https://stacks.math.columbia.edu/tag/04Y2)
-/

@[expose] public section

-- The endpoints of the chosen cartesian lifts compared below are spelled through
-- `Functor.pullbackFiber`, `Functor.Fiber.fiberInclusion` and `Functor.fiberFunctorOfCompEq`, so
-- the instance arguments of `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe vb v u₀ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type u₀} [Category.{vb} 𝒞] {𝒳 : Type u₁} [Category.{v} 𝒳] {𝒴 : Type u₂}
  [Category.{v} 𝒴] {𝒵 : Type u₃} [Category.{v} 𝒵] {𝒳' : Type u₄} [Category.{v} 𝒳'] {𝒴' : Type u₅}
  [Category.{v} 𝒴'] {𝒵' : Type u₆} [Category.{v} 𝒵']

/-- Naturality of `γ`, on the `𝒳`-components of a morphism of the 2-fibre product. -/
private lemma gamma_naturality_a {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞}
    {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'}
    {i : 𝒳 ⥤ 𝒳'} {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (φ : P ⟶ Q) :
    (H.map φ).a ≫ γ.hom.app Q = γ.hom.app P ≫ i.map φ.a := by
  simpa only [Functor.comp_map, fst_map] using γ.hom.naturality φ

/-- Naturality of `δ`, on the `𝒵`-components of a morphism of the 2-fibre product. -/
private lemma delta_naturality_b {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞}
    {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'}
    {k : 𝒵 ⥤ 𝒵'} {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    {P Q : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g} (φ : P ⟶ Q) :
    (H.map φ).b ≫ δ.hom.app Q = δ.hom.app P ≫ k.map φ.b := by
  simpa only [Functor.comp_map, snd_map] using δ.hom.naturality φ

/-- Naturality of `γ` at the chosen cartesian lift, transported along `H`. -/
private lemma gamma_fac_a {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞}
    {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'}
    {i : 𝒳 ⥤ 𝒳'}
    {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒵'.IsFibered]
    [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
    (hHmor : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i) {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (h : V ⟶ U) :
    (Functor.Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P h).hom).a ≫
        γ.hom.app (Functor.pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h).1 ≫
        i.map (Functor.IsPreFibered.pullbackMap P.2 h).a =
      (Functor.IsPreFibered.pullbackMap
          ((Functor.fiberFunctorOfCompEq hHmor.comp_eq U).obj P).2 h).a ≫ γ.hom.app P.1 := by
  rw [← gamma_naturality_a γ, ← Category.assoc, ← comp_a,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

/-- Naturality of `δ` at the chosen cartesian lift, transported along `H`. -/
private lemma delta_fac_b {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞}
    {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞} {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'}
    {k : 𝒵 ⥤ 𝒵'}
    {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    [p𝒳.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒵'.IsFibered]
    [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
    (hHmor : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k) {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (h : V ⟶ U) :
    (Functor.Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P h).hom).b ≫
        δ.hom.app (Functor.pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h).1 ≫
        k.map (Functor.IsPreFibered.pullbackMap P.2 h).b =
      (Functor.IsPreFibered.pullbackMap
          ((Functor.fiberFunctorOfCompEq hHmor.comp_eq U).obj P).2 h).b ≫ δ.hom.app P.1 := by
  rw [← delta_naturality_b δ, ← Category.assoc, ← comp_b,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

section

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}
  {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'} [p𝒳.IsFibered]
  [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered] [p𝒵'.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
  (hf₁ : Functor.IsFibredOneMorphism p𝒳 p𝒴 f) (hg₁ : Functor.IsFibredOneMorphism p𝒵 p𝒴 g)

variable (hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f')
  (hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')

/-- A lift of the identity at an equal object is a lift of the identity there. -/
private lemma isHomLift_id_of_eq {E : Type*} [Category E] (p : E ⥤ 𝒞) {a b : E} {φ : a ⟶ b}
    {R U : 𝒞} (h : p.IsHomLift (𝟙 R) φ) (hR : R = U) : p.IsHomLift (𝟙 U) φ := by
  subst hR
  exact h

open Opposite _root_.CategoryTheory.Functor in
/-- The vertical comparison `(H P).x ≅ i x` in the fibre of `p𝒳'` over `U`, read off `γ`. -/
private def gammaFiberIso (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i)
    (hHmor :
      Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
        (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P)) {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    fibFst ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) ≅
      (fiberFunctorOfCompEq hi₁.comp_eq U).obj (fibFst P) :=
  Fiber.isoMk (γ.app P.1) (isHomLift_id_of_eq p𝒳' (hγ P.1) P.2)

open Opposite _root_.CategoryTheory.Functor in
/-- The vertical comparison `(H P).y ≅ k y` in the fibre of `p𝒵'` over `U`, read off `δ`. -/
private def deltaFiberIso (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
    (hHmor :
      Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
        (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    (hδ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒵'.IsHomLift (𝟙 P.base) (δ.hom.app P)) {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    fibSnd ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) ≅
      (fiberFunctorOfCompEq hk₁.comp_eq U).obj (fibSnd P) :=
  Fiber.isoMk (δ.app P.1) (isHomLift_id_of_eq p𝒵' (hδ P.1) P.2)

section

variable (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i) (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
  (hHmor :
    Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
  (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
  (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P))
  (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
  (hδ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒵'.IsHomLift (𝟙 P.base) (δ.hom.app P))

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered]
  [p𝒵'.IsFibered] [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f'
  g').IsFibered] in
@[simp]
private lemma fiberInclusion_gammaFiberIso_hom {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Fiber.fiberInclusion.map (gammaFiberIso hi₁ hHmor γ hγ P).hom = γ.hom.app P.1 :=
  rfl

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered]
  [p𝒵'.IsFibered] [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f'
  g').IsFibered] in
@[simp]
private lemma fiberInclusion_gammaFiberIso_inv {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Fiber.fiberInclusion.map (gammaFiberIso hi₁ hHmor γ hγ P).inv = γ.inv.app P.1 :=
  rfl

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered]
  [p𝒵'.IsFibered] [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f'
  g').IsFibered] in
@[simp]
private lemma fiberInclusion_deltaFiberIso_hom {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Fiber.fiberInclusion.map (deltaFiberIso hk₁ hHmor δ hδ P).hom = δ.hom.app P.1 :=
  rfl

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered]
  [p𝒵'.IsFibered] [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f'
  g').IsFibered] in
@[simp]
private lemma fiberInclusion_deltaFiberIso_inv {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Fiber.fiberInclusion.map (deltaFiberIso hk₁ hHmor δ hδ P).inv = δ.inv.app P.1 :=
  rfl

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒳`-side comparison identity.** The composite comparison from the chosen pullback of
`i x` to the image under `i` of the `𝒳`-component of the chosen pullback of `P` in the 2-fibre
product can be read either through `H` and `γ`, or through the chosen pullbacks in `𝒳`. Both sides
are pinned down by their composite with `i` of the `𝒳`-component of the chosen cartesian lift of
`h` at `P`, which is cartesian because `i` preserves strongly cartesian morphisms. -/
@[reassoc]
private lemma gammaComp_fac {U : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) {V : 𝒞}
    (h : V ⟶ U) :
    pullbackFiberHom (gammaFiberIso hi₁ hHmor γ hγ P).inv h ≫
        (pullbackFiberFstIso hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) h).inv ≫
        (fibFstHom (hHmor.mapPullbackFiberIso P h).hom ≫
          (gammaFiberIso hi₁ hHmor γ hγ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h)).hom) =
      (hi₁.mapPullbackFiberIso (fibFst P) h).hom ≫
        (fiberFunctorOfCompEq hi₁.comp_eq V).map (pullbackFiberFstIso hf₁ hg₁ P h).inv := by
  have hcart := hi₁.map_isStronglyCartesian h _ (isStronglyCartesian_pullbackMap_a hf₁ hg₁ P h)
  refine
    fiber_hom_ext_of_cartesian h (i.map ((IsPreFibered.pullbackMap P.2 h).a)) inferInstance _ _ ?_
  trans IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hi₁.comp_eq U).obj (fibFst P)).2 h
  · simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibFstHom,
      fiberInclusion_gammaFiberIso_hom]
    rw [gamma_fac_a hHmor γ P h,
      pullbackFiberFstIso_inv_fac_assoc, pullbackFiberHom_fac_assoc,
      fiberInclusion_gammaFiberIso_inv, Iso.inv_hom_id_app]
    exact Category.comp_id _
  · symm
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [← Functor.map_comp, pullbackFiberFstIso_inv_fac,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒳`-side comparison identity, other direction.** The inverse form of
`CategoryTheory.TwoFibreProductOver.gammaComp_fac`, proved the same way: both sides are morphisms
into a chosen pullback, so they agree as soon as their composites with its cartesian lift do. -/
@[reassoc]
private lemma gammaComp_fac' {U : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) {V : 𝒞}
    (h : V ⟶ U) :
    (pullbackFiberFstIso hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) h).hom ≫
        pullbackFiberHom (gammaFiberIso hi₁ hHmor γ hγ P).hom h =
      (fibFstHom (hHmor.mapPullbackFiberIso P h).hom ≫
          (gammaFiberIso hi₁ hHmor γ hγ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h)).hom) ≫
        (fiberFunctorOfCompEq hi₁.comp_eq V).map (pullbackFiberFstIso hf₁ hg₁ P h).hom ≫
        (hi₁.mapPullbackFiberIso (fibFst P) h).inv := by
  refine
    fiber_hom_ext_of_cartesian h
      (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hi₁.comp_eq U).obj (fibFst P)).2 h)
      inferInstance _ _ ?_
  trans
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P).2 h).a ≫ γ.hom.app P.1
  · simp only [Functor.map_comp, Category.assoc]
    rw [pullbackFiberHom_fac, fiberInclusion_gammaFiberIso_hom, ← Category.assoc,
      pullbackFiberFstIso_hom_fac]
  · symm
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibFstHom,
      fiberInclusion_gammaFiberIso_hom, fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, ← Functor.map_comp,
      pullbackFiberFstIso_hom_fac, gamma_fac_a hHmor γ P h]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒵`-side comparison identity.** The composite comparison from the chosen pullback of
`k y` to the image under `k` of the `𝒵`-component of the chosen pullback of `P` in the 2-fibre
product can be read either through `H` and `δ`, or through the chosen pullbacks in `𝒵`. Both sides
are pinned down by their composite with `i` of the `𝒵`-component of the chosen cartesian lift of
`h` at `P`, which is cartesian because `k` preserves strongly cartesian morphisms. -/
@[reassoc]
private lemma deltaComp_fac {U : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) {V : 𝒞}
    (h : V ⟶ U) :
    pullbackFiberHom (deltaFiberIso hk₁ hHmor δ hδ P).inv h ≫
        (pullbackFiberSndIso hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) h).inv ≫
        (fibSndHom (hHmor.mapPullbackFiberIso P h).hom ≫
          (deltaFiberIso hk₁ hHmor δ hδ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h)).hom) =
      (hk₁.mapPullbackFiberIso (fibSnd P) h).hom ≫
        (fiberFunctorOfCompEq hk₁.comp_eq V).map (pullbackFiberSndIso hf₁ hg₁ P h).inv := by
  have hcart := hk₁.map_isStronglyCartesian h _ (isStronglyCartesian_pullbackMap_b hf₁ hg₁ P h)
  refine
    fiber_hom_ext_of_cartesian h (k.map ((IsPreFibered.pullbackMap P.2 h).b)) inferInstance _ _ ?_
  trans IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hk₁.comp_eq U).obj (fibSnd P)).2 h
  · simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibSndHom,
      fiberInclusion_deltaFiberIso_hom]
    rw [delta_fac_b hHmor δ P h,
      pullbackFiberSndIso_inv_fac_assoc, pullbackFiberHom_fac_assoc,
      fiberInclusion_deltaFiberIso_inv, Iso.inv_hom_id_app]
    exact Category.comp_id _
  · symm
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [← Functor.map_comp, pullbackFiberSndIso_inv_fac,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒵`-side comparison identity, other direction.** The inverse form of
`CategoryTheory.TwoFibreProductOver.deltaComp_fac`, proved the same way: both sides are morphisms
into a chosen pullback, so they agree as soon as their composites with its cartesian lift do. -/
@[reassoc]
private lemma deltaComp_fac' {U : 𝒞} (P : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) {V : 𝒞}
    (h : V ⟶ U) :
    (pullbackFiberSndIso hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) h).hom ≫
        pullbackFiberHom (deltaFiberIso hk₁ hHmor δ hδ P).hom h =
      (fibSndHom (hHmor.mapPullbackFiberIso P h).hom ≫
          (deltaFiberIso hk₁ hHmor δ hδ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P h)).hom) ≫
        (fiberFunctorOfCompEq hk₁.comp_eq V).map (pullbackFiberSndIso hf₁ hg₁ P h).hom ≫
        (hk₁.mapPullbackFiberIso (fibSnd P) h).inv := by
  refine
    fiber_hom_ext_of_cartesian h
      (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hk₁.comp_eq U).obj (fibSnd P)).2 h)
      inferInstance _ _ ?_
  trans
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P).2 h).b ≫ δ.hom.app P.1
  · simp only [Functor.map_comp, Category.assoc]
    rw [pullbackFiberHom_fac, fiberInclusion_deltaFiberIso_hom, ← Category.assoc,
      pullbackFiberSndIso_hom_fac]
  · symm
    simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibSndHom,
      fiberInclusion_deltaFiberIso_hom, fiberInclusion_map_fiberFunctorOfCompEq_map]
    rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, ← Functor.map_comp,
      pullbackFiberSndIso_hom_fac, delta_fac_b hHmor δ P h]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒳`-side dictionary.** A section of `Mor(i x, i x')` coming from `𝒳` and one coming from
the 2-fibre product of the stackifications agree exactly when the corresponding morphisms of the
fibres are matched by the comparison read off `γ`. -/
private lemma dict_fst {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (X : (Over U)ᵒᵖ)
    (α₀ :
      fibFst (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom) ⟶
        fibFst (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom))
    (M :
      pullbackFiber (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) X.unop.hom ⟶
        pullbackFiber (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X.unop.hom) :
    (hi₁.morPresheafMap (fibFst P) (fibFst Q)).app X
          ((pullbackFiberFstIso hf₁ hg₁ P X.unop.hom).homCongr
            (pullbackFiberFstIso hf₁ hg₁ Q X.unop.hom) α₀) =
        (morPresheafFiberIso p𝒳' (gammaFiberIso hi₁ hHmor γ hγ P)
              (gammaFiberIso hi₁ hHmor γ hγ Q)).hom.app
          X
          (morFstSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X M) ↔
      (fibFstHom (hHmor.mapPullbackFiberIso P X.unop.hom).hom ≫
            (gammaFiberIso hi₁ hHmor γ hγ
                (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom)).hom) ≫
          (fiberFunctorOfCompEq hi₁.comp_eq X.unop.left).map α₀ =
        fibFstHom M ≫
          (fibFstHom (hHmor.mapPullbackFiberIso Q X.unop.hom).hom ≫
            (gammaFiberIso hi₁ hHmor γ hγ
                (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom)).hom) := by
  have hiso := isIso_pullbackFiberHom_inv (gammaFiberIso hi₁ hHmor γ hγ P) X.unop.hom
  simp only [Functor.IsFibredOneMorphism.morPresheafMap_app, morPresheafFiberIso_hom,
    morPresheafMap_app, Iso.homCongr_apply, morFstSection, Functor.map_comp, Category.assoc]
  rw [← gammaComp_fac_assoc hf₁ hg₁ hf'₁ hg'₁ hi₁ hHmor γ hγ P X.unop.hom,
    gammaComp_fac' hf₁ hg₁ hf'₁ hg'₁ hi₁ hHmor γ hγ Q X.unop.hom]
  simp only [Category.assoc]
  refine ⟨fun hh => ?_, fun hh => by rw [reassoc_of% hh]⟩
  have h1 := (cancel_epi _).mp ((cancel_epi _).mp hh)
  simp only [← Category.assoc] at h1
  simpa only [Category.assoc] using (cancel_mono _).mp ((cancel_mono _).mp h1)

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The `𝒵`-side dictionary.** A section of `Mor(k y, k y')` coming from `𝒵` and one coming from
the 2-fibre product of the stackifications agree exactly when the corresponding morphisms of the
fibres are matched by the comparison read off `δ`. -/
private lemma dict_snd {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (X : (Over U)ᵒᵖ)
    (β₀ :
      fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom) ⟶
        fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom))
    (M :
      pullbackFiber (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P) X.unop.hom ⟶
        pullbackFiber (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X.unop.hom) :
    (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)).app X
          ((pullbackFiberSndIso hf₁ hg₁ P X.unop.hom).homCongr
            (pullbackFiberSndIso hf₁ hg₁ Q X.unop.hom) β₀) =
        (morPresheafFiberIso p𝒵' (deltaFiberIso hk₁ hHmor δ hδ P)
              (deltaFiberIso hk₁ hHmor δ hδ Q)).hom.app
          X
          (morSndSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X M) ↔
      (fibSndHom (hHmor.mapPullbackFiberIso P X.unop.hom).hom ≫
            (deltaFiberIso hk₁ hHmor δ hδ
                (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom)).hom) ≫
          (fiberFunctorOfCompEq hk₁.comp_eq X.unop.left).map β₀ =
        fibSndHom M ≫
          (fibSndHom (hHmor.mapPullbackFiberIso Q X.unop.hom).hom ≫
            (deltaFiberIso hk₁ hHmor δ hδ
                (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom)).hom) := by
  have hiso := isIso_pullbackFiberHom_inv (deltaFiberIso hk₁ hHmor δ hδ P) X.unop.hom
  simp only [Functor.IsFibredOneMorphism.morPresheafMap_app, morPresheafFiberIso_hom,
    morPresheafMap_app, Iso.homCongr_apply, morSndSection, Functor.map_comp, Category.assoc]
  rw [← deltaComp_fac_assoc hf₁ hg₁ hf'₁ hg'₁ hk₁ hHmor δ hδ P X.unop.hom,
    deltaComp_fac' hf₁ hg₁ hf'₁ hg'₁ hk₁ hHmor δ hδ Q X.unop.hom]
  simp only [Category.assoc]
  refine ⟨fun hh => ?_, fun hh => by rw [reassoc_of% hh]⟩
  have h1 := (cancel_epi _).mp ((cancel_epi _).mp hh)
  simp only [← Category.assoc] at h1
  simpa only [Category.assoc] using (cancel_mono _).mp ((cancel_mono _).mp h1)

open Opposite _root_.CategoryTheory.Functor in
/-- The first leg of the cospan, evaluated at the transported `𝒳`-component of a section and then
pushed down the cartesian lift: the image under `f` of the component, read at the chosen pullbacks
of `P` in the 2-fibre product. -/
private lemma morCospanFst_fac {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (W : Over U)
    (α₀ :
      fibFst (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom) ⟶
        fibFst (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom)) :
    Fiber.fiberInclusion.map
          ((hf₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W)
            ((pullbackFiberFstIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberFstIso hf₁ hg₁ Q W.hom)
              α₀)) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q)).2 W.hom =
      Fiber.fiberInclusion.map (hf₁.mapPullbackFiberIso (fibFst P) W.hom).hom ≫
        f.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hf₁ hg₁ P W.hom).inv) ≫
        f.map (Fiber.fiberInclusion.map α₀) ≫ f.map ((IsPreFibered.pullbackMap Q.2 W.hom).a) := by
  rw [fiberInclusion_morPresheafMap_app]
  simp only [Iso.homCongr_apply, Functor.map_comp, Category.assoc]
  rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, ← Functor.map_comp,
    pullbackFiberFstIso_hom_fac]

open Opposite _root_.CategoryTheory.Functor in
/-- The second leg of the cospan, evaluated at the transported `𝒵`-component of a section and then
pushed down the cartesian lift. The prefix is rewritten by
`CategoryTheory.TwoFibreProductOver.pullbackFiberHom_fibIso_fac`, which is where the comparison
isomorphism of the chosen pullback of `P` enters. -/
private lemma morCospanSnd_fac {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (W : Over U)
    (β₀ :
      fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom) ⟶
        fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom)) :
    Fiber.fiberInclusion.map
          ((morSnd hf₁ hg₁ P Q).app (op W)
            ((pullbackFiberSndIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberSndIso hf₁ hg₁ Q W.hom)
              β₀)) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q)).2 W.hom =
      Fiber.fiberInclusion.map (hf₁.mapPullbackFiberIso (fibFst P) W.hom).hom ≫
        f.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hf₁ hg₁ P W.hom).inv) ≫
        (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom).1.iso.hom ≫
        g.map (Fiber.fiberInclusion.map β₀) ≫
        g.map ((IsPreFibered.pullbackMap Q.2 W.hom).b) ≫ Q.1.iso.inv := by
  simp only [morSnd_app, Iso.homCongr_apply, Functor.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map]
  have hb2 :
    g.map (Fiber.fiberInclusion.map (pullbackFiberSndIso hf₁ hg₁ Q W.hom).hom) ≫
        g.map (IsPreFibered.pullbackMap (fibSnd Q).2 W.hom) =
      g.map ((IsPreFibered.pullbackMap Q.2 W.hom).b) := by
    rw [← Functor.map_comp, pullbackFiberSndIso_hom_fac]
  rw [pullbackFiberHom_fac, Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc,
    reassoc_of% hb2, pullbackFiberHom_fibIso_fac_assoc hf₁ hg₁ P W.hom,
    fiberInclusion_map_fibIso_inv]

open Opposite _root_.CategoryTheory.Functor in
/-- **The fibre-product condition holds after applying `j`.** If a section of the morphism presheaf
of the 2-fibre product of the stackifications is matched by a pair of sections coming from `𝒳` and
from `𝒵`, then that pair satisfies the fibre-product condition of
`CategoryTheory.TwoFibreProductOver.morCondition_iff` after applying the map of Stacks 042V along
`j`. This is where `CategoryTheory.TwoFibreProductOver.heart` is used. -/
private lemma morCondition_after_j (α : i ⋙ f' ≅ f ⋙ j) (β : k ⋙ g' ≅ g ⋙ j)
    (hj₁ : Functor.IsFibredOneMorphism p𝒴 p𝒴' j)
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) (W : Over U)
    (σW :
      (morPresheaf (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q)).obj
        (op W))
    (a : (morPresheaf p𝒳 (fibFst P) (fibFst Q)).obj (op W))
    (b : (morPresheaf p𝒵 (fibSnd P) (fibSnd Q)).obj (op W))
    (ha :
      (hi₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W) a =
        (morPresheafFiberIso p𝒳' (gammaFiberIso hi₁ hHmor γ hγ P)
              (gammaFiberIso hi₁ hHmor γ hγ Q)).hom.app
          (op W)
          (morFstSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) (op W) σW))
    (hb :
      (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)).app (op W) b =
        (morPresheafFiberIso p𝒵' (deltaFiberIso hk₁ hHmor δ hδ P)
              (deltaFiberIso hk₁ hHmor δ hδ Q)).hom.app
          (op W)
          (morSndSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
            ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) (op W) σW)) :
    (hj₁.morPresheafMap ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst P))
            ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q))).app
        (op W) ((hf₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W) a) =
      (hj₁.morPresheafMap ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst P))
            ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q))).app
        (op W) ((morSnd hf₁ hg₁ P Q).app (op W) b) := by
  obtain ⟨α₀, rfl⟩ :
    ∃ α₀,
      a =
        (pullbackFiberFstIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberFstIso hf₁ hg₁ Q W.hom) α₀ :=
    ⟨_, (Equiv.apply_symm_apply _ a).symm⟩
  obtain ⟨β₀, rfl⟩ :
    ∃ β₀,
      b =
        (pullbackFiberSndIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberSndIso hf₁ hg₁ Q W.hom) β₀ :=
    ⟨_, (Equiv.apply_symm_apply _ b).symm⟩
  have hd1 := (dict_fst hf₁ hg₁ hf'₁ hg'₁ hi₁ hHmor γ hγ P Q (op W) α₀ σW).mp ha
  have hd2 := (dict_snd hf₁ hg₁ hf'₁ hg'₁ hk₁ hHmor δ hδ P Q (op W) β₀ σW).mp hb
  have hE :
    ((Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P W.hom).hom).a ≫
          γ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom).1) ≫
        i.map (Fiber.fiberInclusion.map α₀) =
      (Fiber.fiberInclusion.map σW).a ≫
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q W.hom).hom).a ≫
        γ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom).1 := by
    simpa only [Functor.map_comp, fiberInclusion_map_fibFstHom, fiberInclusion_gammaFiberIso_hom,
      fiberInclusion_map_fiberFunctorOfCompEq_map, Category.assoc, comp_a] using
      congrArg Fiber.fiberInclusion.map hd1
  have hF :
    ((Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P W.hom).hom).b ≫
          δ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom).1) ≫
        k.map (Fiber.fiberInclusion.map β₀) =
      (Fiber.fiberInclusion.map σW).b ≫
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q W.hom).hom).b ≫
        δ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom).1 := by
    simpa only [Functor.map_comp, fiberInclusion_map_fibSndHom, fiberInclusion_deltaFiberIso_hom,
      fiberInclusion_map_fiberFunctorOfCompEq_map, Category.assoc, comp_b] using
      congrArg Fiber.fiberInclusion.map hd2
  have : IsIso (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P W.hom).hom).a := isIso_a _
  have hh :=
    heart α β
      (compat_of_hpsi α β γ δ hψ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P W.hom).1
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso P W.hom).hom))
      (compat_of_hpsi α β γ δ hψ (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom).1
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q W.hom).hom))
      (Fiber.fiberInclusion.map σW) hE hF
  have hwq :
    f.map ((IsPreFibered.pullbackMap Q.2 W.hom).a) =
      (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q W.hom).1.iso.hom ≫
        g.map ((IsPreFibered.pullbackMap Q.2 W.hom).b) ≫ Q.1.iso.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact (IsPreFibered.pullbackMap Q.2 W.hom).w
  simp only [Functor.map_comp] at hh
  refine
    fiber_hom_ext_of_cartesian W.hom
      (IsPreFibered.pullbackMap
        ((fiberFunctorOfCompEq hj₁.comp_eq U).obj
            ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q))).2
        W.hom)
      inferInstance _ _ ?_
  rw [fiberInclusion_morPresheafMap_app hj₁ _ _ (op W)
      ((hf₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W)
        ((pullbackFiberFstIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberFstIso hf₁ hg₁ Q W.hom) α₀)),
    fiberInclusion_morPresheafMap_app hj₁ _ _ (op W)
      ((morSnd hf₁ hg₁ P Q).app (op W)
        ((pullbackFiberSndIso hf₁ hg₁ P W.hom).homCongr (pullbackFiberSndIso hf₁ hg₁ Q W.hom) β₀))]
  simp only [Category.assoc]
  rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, ← Functor.map_comp, ←
    Functor.map_comp, morCospanFst_fac, morCospanSnd_fac, hwq]
  simp only [Functor.map_comp]
  rw [reassoc_of% hh]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The crux square, `𝒳`-side.** Taking the `𝒳`-component of the image of a section under the map
induced by `H`, and transporting it along `γ`, is the same as taking the `𝒳`-component first and
then applying the map of Stacks 042V along `i`. -/
private lemma morFstSection_psi {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (hi₁.morPresheafMap (fibFst P) (fibFst Q)).app X (morFstSection hf₁ hg₁ P Q X s) =
      (morPresheafFiberIso p𝒳' (gammaFiberIso hi₁ hHmor γ hγ P)
            (gammaFiberIso hi₁ hHmor γ hγ Q)).hom.app
        X
        (morFstSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X
          ((hHmor.morPresheafMap P Q).app X s)) := by
  refine
    (dict_fst hf₁ hg₁ hf'₁ hg'₁ hi₁ hHmor γ hγ P Q X (fibFstHom s)
          ((hHmor.morPresheafMap P Q).app X s)).mpr
      (Fiber.hom_ext ?_)
  have hnat :
    (H.map (Fiber.fiberInclusion.map s)).a ≫
        γ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom).1 =
      γ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom).1 ≫
        i.map ((Fiber.fiberInclusion.map s).a) :=
    gamma_naturality_a γ _
  have hinv :
    (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q X.unop.hom).inv).a ≫
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q X.unop.hom).hom).a =
      𝟙 _ := by
    rw [← comp_a, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_a]
  simp only [Functor.map_comp, fiberInclusion_map_fibFstHom, fiberInclusion_gammaFiberIso_hom,
    fiberInclusion_map_fiberFunctorOfCompEq_map, fiberInclusion_morPresheafMap_app, comp_a,
    Category.assoc]
  rw [reassoc_of% hinv, hnat]

open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] [p𝒴'.IsFibered] in
/-- **The crux square, `𝒵`-side.** Taking the `𝒵`-component of the image of a section under the map
induced by `H`, and transporting it along `δ`, is the same as taking the `𝒵`-component first and
then applying the map of Stacks 042V along `k`. -/
private lemma morSndSection_psi {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U)
    (X : (Over U)ᵒᵖ) (s : (morPresheaf (structureFunctor p𝒳 p𝒵 p𝒴 f g) P Q).obj X) :
    (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)).app X (morSndSection hf₁ hg₁ P Q X s) =
      (morPresheafFiberIso p𝒵' (deltaFiberIso hk₁ hHmor δ hδ P)
            (deltaFiberIso hk₁ hHmor δ hδ Q)).hom.app
        X
        (morSndSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
          ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) X
          ((hHmor.morPresheafMap P Q).app X s)) := by
  refine
    (dict_snd hf₁ hg₁ hf'₁ hg'₁ hk₁ hHmor δ hδ P Q X (fibSndHom s)
          ((hHmor.morPresheafMap P Q).app X s)).mpr
      (Fiber.hom_ext ?_)
  have hnat :
    (H.map (Fiber.fiberInclusion.map s)).b ≫
        δ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) Q X.unop.hom).1 =
      δ.hom.app (pullbackFiber (structureFunctor p𝒳 p𝒵 p𝒴 f g) P X.unop.hom).1 ≫
        k.map ((Fiber.fiberInclusion.map s).b) :=
    delta_naturality_b δ _
  have hinv :
    (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q X.unop.hom).inv).b ≫
        (Fiber.fiberInclusion.map (hHmor.mapPullbackFiberIso Q X.unop.hom).hom).b =
      𝟙 _ := by
    rw [← comp_b, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_b]
  simp only [Functor.map_comp, fiberInclusion_map_fibSndHom, fiberInclusion_deltaFiberIso_hom,
    fiberInclusion_map_fiberFunctorOfCompEq_map, fiberInclusion_morPresheafMap_app, comp_b,
    Category.assoc]
  rw [reassoc_of% hinv, hnat]

include hf₁ hg₁ hf'₁ hg'₁ γ hγ δ hδ in
open Opposite _root_.CategoryTheory.Functor in
/-- **Local surjectivity of the map of morphism presheaves induced by `H`.** A section of the
target has `𝒳`- and `𝒵`-components which, transported along `γ` and `δ`, lift locally through `i`
and `k`; the two lifts satisfy the fibre-product condition of
`CategoryTheory.TwoFibreProductOver.morCondition_iff` after applying `j`, hence — `j` being locally
injective on morphism presheaves — after a further refinement, and there they assemble into a
section of the source with the right image. -/
lemma isLocallySurjective_morPresheafMap (J : GrothendieckTopology 𝒞) (α : i ⋙ f' ≅ f ⋙ j)
    (β : k ⋙ g' ≅ g ⋙ j) (hj₁ : Functor.IsFibredOneMorphism p𝒴 p𝒴' j)
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    (hmor𝒳 :
      ∀ (V : 𝒞) (x y : p𝒳.Fiber V),
        Presheaf.IsLocallySurjective (J.over V) (hi₁.morPresheafMap x y))
    (hmor𝒵 :
      ∀ (V : 𝒞) (z w : p𝒵.Fiber V),
        Presheaf.IsLocallySurjective (J.over V) (hk₁.morPresheafMap z w))
    (hmor𝒴 :
      ∀ (V : 𝒞) (y w : p𝒴.Fiber V),
        Presheaf.IsLocallyInjective (J.over V) (hj₁.morPresheafMap y w))
    {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Presheaf.IsLocallySurjective (J.over U) (hHmor.morPresheafMap P Q) := by
  refine ⟨fun {X} σ => ?_⟩
  have hLS1 := hmor𝒳 U (fibFst P) (fibFst Q)
  have hLS2 := hmor𝒵 U (fibSnd P) (fibSnd Q)
  have hLI :=
    hmor𝒴 U ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst P))
      ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q))
  set a'' :=
    (morPresheafFiberIso p𝒳' (gammaFiberIso hi₁ hHmor γ hγ P)
          (gammaFiberIso hi₁ hHmor γ hγ Q)).hom.app
      (op X)
      (morFstSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) (op X) σ) with
    ha''
  set b'' :=
    (morPresheafFiberIso p𝒵' (deltaFiberIso hk₁ hHmor δ hδ P)
          (deltaFiberIso hk₁ hHmor δ hδ Q)).hom.app
      (op X)
      (morSndSection hf'₁ hg'₁ ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
        ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q) (op X) σ) with
    hb''
  set S : Sieve X :=
    Presheaf.imageSieve (hi₁.morPresheafMap (fibFst P) (fibFst Q)) a'' ⊓
      Presheaf.imageSieve (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)) b'' with
    hSdef
  have hS : S ∈ (J.over U) X :=
    (J.over U).intersection_covering (hLS1.imageSieve_mem a'') (hLS2.imageSieve_mem b'')
  set T : ∀ ⦃W : Over U⦄ (hw : W ⟶ X), S hw → Sieve W := fun W hw hws =>
    Presheaf.equalizerSieve (F :=
      morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst P))
        ((fiberFunctorOfCompEq hf₁.comp_eq U).obj (fibFst Q)))
      ((hf₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W)
        (Presheaf.localPreimage (hi₁.morPresheafMap (fibFst P) (fibFst Q)) a'' hw hws.1))
      ((morSnd hf₁ hg₁ P Q).app (op W)
        (Presheaf.localPreimage (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)) b'' hw hws.2)) with
    hTdef
  have hT : ∀ ⦃W : Over U⦄ (hw : W ⟶ X) (hws : S hw), T hw hws ∈ (J.over U) W := by
    intro W hw hws
    refine
      Presheaf.equalizerSieve_mem (J.over U) _ _ _
        (morCondition_after_j hf₁ hg₁ hf'₁ hg'₁ hi₁ hk₁ hHmor γ hγ δ hδ α β hj₁ hψ P Q W
          ((morPresheaf (structureFunctor p𝒳' p𝒵' p𝒴' f' g')
                ((fiberFunctorOfCompEq hHmor.comp_eq U).obj P)
                ((fiberFunctorOfCompEq hHmor.comp_eq U).obj Q)).map
            hw.op σ)
          _ _ ?_ ?_)
    · rw [Presheaf.app_localPreimage, ha'', ← NatTrans.naturality_apply, ←
        morFstSection_naturality]
    · rw [Presheaf.app_localPreimage, hb'', ← NatTrans.naturality_apply, ←
        morSndSection_naturality]
  refine (J.over U).superset_covering ?_ ((J.over U).transitive hS (Sieve.bind S.1 T) ?_)
  · rintro W hw ⟨Y, gg, ff, Hff, hR, rfl⟩
    set a₀ :=
      (morPresheaf p𝒳 (fibFst P) (fibFst Q)).map gg.op
        (Presheaf.localPreimage (hi₁.morPresheafMap (fibFst P) (fibFst Q)) a'' ff Hff.1) with
      ha₀
    set b₀ :=
      (morPresheaf p𝒵 (fibSnd P) (fibSnd Q)).map gg.op
        (Presheaf.localPreimage (hk₁.morPresheafMap (fibSnd P) (fibSnd Q)) b'' ff Hff.2) with
      hb₀
    have hcond :
      (hf₁.morPresheafMap (fibFst P) (fibFst Q)).app (op W) a₀ =
        (morSnd hf₁ hg₁ P Q).app (op W) b₀ := by
      rwa [ha₀, hb₀, NatTrans.naturality_apply, NatTrans.naturality_apply]
    refine ⟨(morSectionEquiv hf₁ hg₁ P Q W).symm ⟨(a₀, b₀), hcond⟩, ?_⟩
    have hEq := Equiv.apply_symm_apply (morSectionEquiv hf₁ hg₁ P Q W) ⟨(a₀, b₀), hcond⟩
    have hta :
      morFstSection hf₁ hg₁ P Q (op W) ((morSectionEquiv hf₁ hg₁ P Q W).symm ⟨(a₀, b₀), hcond⟩) =
        a₀ :=
      congrArg (fun z => z.val.1) hEq
    have htb :
      morSndSection hf₁ hg₁ P Q (op W) ((morSectionEquiv hf₁ hg₁ P Q W).symm ⟨(a₀, b₀), hcond⟩) =
        b₀ :=
      congrArg (fun z => z.val.2) hEq
    have hΓinj :=
      (CategoryTheory.mono_iff_injective
            ((morPresheafFiberIso p𝒳' (gammaFiberIso hi₁ hHmor γ hγ P)
                  (gammaFiberIso hi₁ hHmor γ hγ Q)).hom.app
              (op W))).mp
        inferInstance
    have hΔinj :=
      (CategoryTheory.mono_iff_injective
            ((morPresheafFiberIso p𝒵' (deltaFiberIso hk₁ hHmor δ hδ P)
                  (deltaFiberIso hk₁ hHmor δ hδ Q)).hom.app
              (op W))).mp
        inferInstance
    refine section_ext hf'₁ hg'₁ _ _ (op W) _ _ (hΓinj ?_) (hΔinj ?_)
    · rw [← morFstSection_psi hf₁ hg₁ hf'₁ hg'₁ hi₁ hHmor γ hγ P Q (op W), hta, ha₀,
        NatTrans.naturality_apply, Presheaf.app_localPreimage, ha'', morFstSection_naturality,
        NatTrans.naturality_apply, op_comp, Functor.map_comp_apply]
    · rw [← morSndSection_psi hf₁ hg₁ hf'₁ hg'₁ hk₁ hHmor δ hδ P Q (op W), htb, hb₀,
        NatTrans.naturality_apply, Presheaf.app_localPreimage, hb'', morSndSection_naturality,
        NatTrans.naturality_apply, op_comp, Functor.map_comp_apply]
  · intro W hw hws
    exact (J.over U).superset_covering (Sieve.le_pullback_bind _ _ _ hws) (hT hw hws)

end

end

end CategoryTheory.TwoFibreProductOver

end
