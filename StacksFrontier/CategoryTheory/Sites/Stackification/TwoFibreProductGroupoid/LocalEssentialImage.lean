module

public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections
import all StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections

/-!
# Stacks 04Y2: clause (2) for one member of a covering

This file is the third part of the proof of Stacks 04Y2 (the stackification of a 2-fibre product
is the 2-fibre product of the stackifications), assembled in
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid`. It assembles an object
of `𝒳 ×_𝒴 𝒵` from objects of `𝒳` and `𝒵` over a common base and a morphism of `𝒴` between their
chosen pullbacks (`objOf`), and proves `objStep`: given cartesian morphisms over `u` from `i x` and
`k z` to the two components of an object of `𝒳' ×_{𝒴'} 𝒵'`, that object is, locally over the
source of `u`, the target of a cartesian morphism from the image under `H` of an object of
`𝒳 ×_𝒴 𝒵`.

## Implementation notes

`objStep` uses the private lemma `isHomLift_inv_app` of
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections`, which
this file therefore also imports with `import all`: that lemma cannot be made public, because
`CategoryTheory.TwoFibreProductOver.isHomLift_inv_app` already names a different lemma, in
`StacksFrontier.CategoryTheory.TwoFibreProductOverReindex`.

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

section

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}
  {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'} [p𝒳.IsFibered]
  [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered] [p𝒵'.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
  (hf₁ : Functor.IsFibredOneMorphism p𝒳 p𝒴 f) (hg₁ : Functor.IsFibredOneMorphism p𝒵 p𝒴 g)

variable (hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f')
  (hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')

section

variable (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i) (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
  (hHmor :
    Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
  (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
  (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P))
  (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
  (hδ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒵'.IsHomLift (𝟙 P.base) (δ.hom.app P))

include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
/-- The object of `𝒳 ×_𝒴 𝒵` assembled from an object of `𝒳`, an object of `𝒵`, both over `V`, and a
morphism of `𝒴` between the chosen pullbacks of their images along `W'.hom`; the comparison
isomorphism is that morphism, read through the comparisons of Stacks 042V and invertible because
`p𝒴` is fibred in groupoids. -/
private noncomputable def objOf (h𝒴 : p𝒴.IsFiberedInGroupoids) {V : 𝒞} {x : 𝒳} (hxV : p𝒳.obj x = V)
    {z : 𝒵} (hzV : p𝒵.obj z = V) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W')) :
    TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g :=
  have : IsGroupoid (p𝒴.Fiber W'.left) := h𝒴.fiber_isGroupoid W'.left
  have : IsIso ψW := IsGroupoid.all_isIso ψW
  { base := W'.left
    x := (pullbackFiber p𝒳 (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).1
    y := (pullbackFiber p𝒵 (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).1
    hx := (pullbackFiber p𝒳 (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).2
    hy := (pullbackFiber p𝒵 (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).2
    iso :=
      Fiber.fiberInclusion.mapIso
        ((hf₁.mapPullbackFiberIso (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).symm ≪≫
          asIso ψW ≪≫ hg₁.mapPullbackFiberIso (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom)
    vertical :=
      (((hf₁.mapPullbackFiberIso (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).symm ≪≫
            asIso ψW ≪≫ hg₁.mapPullbackFiberIso (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).hom).2 }

include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
@[simp]
private lemma objOf_base (h𝒴 : p𝒴.IsFiberedInGroupoids) {V : 𝒞} {x : 𝒳} (hxV : p𝒳.obj x = V)
    {z : 𝒵} (hzV : p𝒵.obj z = V) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W')) :
    (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).base = W'.left :=
  rfl

include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
@[simp]
private lemma objOf_x (h𝒴 : p𝒴.IsFiberedInGroupoids) {V : 𝒞} {x : 𝒳} (hxV : p𝒳.obj x = V) {z : 𝒵}
    (hzV : p𝒵.obj z = V) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W')) :
    (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).x = (pullbackFiber p𝒳 (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).1 :=
  rfl

include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
@[simp]
private lemma objOf_y (h𝒴 : p𝒴.IsFiberedInGroupoids) {V : 𝒞} {x : 𝒳} (hxV : p𝒳.obj x = V) {z : 𝒵}
    (hzV : p𝒵.obj z = V) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W')) :
    (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).y = (pullbackFiber p𝒵 (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).1 :=
  rfl

include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
/-- The comparison isomorphism of `CategoryTheory.TwoFibreProductOver.objOf`, in `𝒴`. -/
private lemma objOf_iso_hom (h𝒴 : p𝒴.IsFiberedInGroupoids) {V : 𝒞} {x : 𝒳} (hxV : p𝒳.obj x = V)
    {z : 𝒵} (hzV : p𝒵.obj z = V) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W')) :
    (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).iso.hom =
      Fiber.fiberInclusion.map (hf₁.mapPullbackFiberIso (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).inv ≫
        Fiber.fiberInclusion.map ψW ≫
        Fiber.fiberInclusion.map (hg₁.mapPullbackFiberIso (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).hom := by
  have : IsGroupoid (p𝒴.Fiber W'.left) := h𝒴.fiber_isGroupoid W'.left
  have : IsIso ψW := IsGroupoid.all_isIso ψW
  unfold objOf
  simp

/-- A vertical morphism followed by lifts of `t` and `u` lifts `t ≫ u`. -/
private lemma isHomLift_id_comp_comp {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟]
    (p : 𝒟 ⥤ 𝒮) {R S T : 𝒮} {a b c d : 𝒟} {t : R ⟶ S} {u : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}
    {χ : c ⟶ d} (hφ : p.IsHomLift (𝟙 R) φ) (hψ : p.IsHomLift t ψ) (hχ : p.IsHomLift u χ) :
    p.IsHomLift (t ≫ u) (φ ≫ ψ ≫ χ) := by
  simpa using (inferInstance : p.IsHomLift (𝟙 R ≫ t ≫ u) (φ ≫ ψ ≫ χ))

include hf₁ hg₁ hi₁ hk₁ hHmor γ hγ δ hδ in
open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳'.IsFibered] [p𝒴'.IsFibered] [p𝒵'.IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f'
  g').IsFibered] hHmor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
/-- **The object of the 2-fibre product produced by clause (2), and the cartesian morphism to
`P'`.** Given an object `x` of `𝒳` and a `z` of `𝒵` whose images under `i` and `k` receive
cartesian morphisms over `u` from the two components of `P'`, a vertical `ω` filling the resulting
square, and a morphism `ψW` of `𝒴` between the chosen pullbacks of `f x` and `g z` whose image
under `j` is `ω` base changed, this produces `CategoryTheory.TwoFibreProductOver.objOf` together
with a morphism `H P ⟶ P'` strongly cartesian over `W'.hom ≫ u`. -/
private lemma objStepConstruct (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hq' : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFiberedInGroupoids)
    (_hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f')
    (_hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')
    (α : i ⋙ f' ≅ f ⋙ j) (β : k ⋙ g' ≅ g ⋙ j)
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    (P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g') {V : 𝒞} (u : V ⟶ P'.base) {x : 𝒳}
    (a : i.obj x ⟶ P'.x) (ha : p𝒳'.IsHomLift u a) (hxV : p𝒳.obj x = V) {z : 𝒵} (b : k.obj z ⟶ P'.y)
    (hb : p𝒵'.IsHomLift u b) (hzV : p𝒵.obj z = V) (ω : f'.obj (i.obj x) ⟶ g'.obj (k.obj z))
    (hωfac : ω ≫ g'.map b = f'.map a ≫ P'.iso.hom) (W' : Over V)
    (ψW :
      (morPresheaf p𝒴 ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)).obj
        (op W'))
    (hψW :
      j.map (Fiber.fiberInclusion.map ψW) ≫
          j.map
            (IsPreFibered.pullbackMap
              ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V)).2 W'.hom) =
        j.map
            (IsPreFibered.pullbackMap
              ((fiberFunctorOfCompEq hf₁.comp_eq V).obj (⟨x, hxV⟩ : p𝒳.Fiber V)).2 W'.hom) ≫
          (α.inv.app x ≫ ω ≫ β.hom.app z)) :
    ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : H.obj P ⟶ P'),
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian (W'.hom ≫ u) φ := by
  have := ha
  have := hb
  have hγP := hγ (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW)
  have hδP := hδ (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW)
  have hipbmx :
    p𝒳'.IsHomLift W'.hom (i.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) :=
    Functor.isHomLift_map_of_comp_eq hi₁.comp_eq W'.hom _
  have hkpbmz :
    p𝒵'.IsHomLift W'.hom (k.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) :=
    Functor.isHomLift_map_of_comp_eq hk₁.comp_eq W'.hom _
  have hΦa :
    p𝒳'.IsHomLift (W'.hom ≫ u)
      (γ.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW) ≫
        i.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom) ≫ a) :=
    isHomLift_id_comp_comp _ hγP hipbmx ha
  have hΦb :
    p𝒵'.IsHomLift (W'.hom ≫ u)
      (δ.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW) ≫
        k.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom) ≫ b) :=
    isHomLift_id_comp_comp _ hδP hkpbmz hb
  have hcompat :=
    compat_of_hpsi α β γ δ hψ (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW)
      (𝟙 (H.obj (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW)))
  simp only [id_a, id_b, Category.id_comp] at hcompat
  have hαnat :
    f'.map (i.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) ≫ α.hom.app x =
      α.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).x ≫
        j.map (f.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) := by
    exact α.hom.naturality (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)
  have hβnat :
    j.map (g.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) ≫ β.inv.app z =
      β.inv.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).y ≫
        g'.map (k.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) := by
    exact β.inv.naturality (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)
  have hMG :
    j.map (Fiber.fiberInclusion.map (hg₁.mapPullbackFiberIso (⟨z, hzV⟩ : p𝒵.Fiber V) W'.hom).hom) ≫
        j.map (g.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) =
      j.map
        (IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V)).2 W'.hom) := by
    rw [← Functor.map_comp, Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]
  have hMF :
    j.map (Fiber.fiberInclusion.map (hf₁.mapPullbackFiberIso (⟨x, hxV⟩ : p𝒳.Fiber V) W'.hom).inv) ≫
        j.map
          (IsPreFibered.pullbackMap
            ((fiberFunctorOfCompEq hf₁.comp_eq V).obj (⟨x, hxV⟩ : p𝒳.Fiber V)).2 W'.hom) =
      j.map (f.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) := by
    rw [← Functor.map_comp, Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac]
  have hdag :
    j.map (f.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) ≫
        (α.inv.app x ≫ ω ≫ β.hom.app z) =
      j.map (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).iso.hom ≫
        j.map (g.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) := by
    rw [objOf_iso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [hMG, hψW, reassoc_of% hMF]
  have hstar :
    f'.map (i.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom)) ≫ ω =
      α.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).x ≫
        j.map (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).iso.hom ≫
        β.inv.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW).y ≫
        g'.map (k.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom)) := by
    rw [← hβnat, ← reassoc_of% hdag, ← reassoc_of% hαnat]
    simp
  have hfin :
    ∃ Φ : H.obj (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW) ⟶ P', p𝒳'.IsHomLift (W'.hom ≫ u) Φ.a := by
    refine
      ⟨Hom.mk'
          (γ.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW) ≫
            i.map (IsPreFibered.pullbackMap (⟨x, hxV⟩ : p𝒳.Fiber V).2 W'.hom) ≫ a)
          (δ.hom.app (objOf hf₁ hg₁ h𝒴 hxV hzV W' ψW) ≫
            k.map (IsPreFibered.pullbackMap (⟨z, hzV⟩ : p𝒵.Fiber V).2 W'.hom) ≫ b)
          ?_ ?_,
        ?_⟩
    · rw [IsHomLift.fac' p𝒵' (W'.hom ≫ u) _, IsHomLift.fac' p𝒳' (W'.hom ≫ u) _]
      simp
    · simp only [Functor.map_comp, Category.assoc]
      rw [← hωfac, ← reassoc_of% hcompat, reassoc_of% hstar]
    · rwa [Hom.mk'_a]
  obtain ⟨Φ, hΦ⟩ := hfin
  have := isHomLift_of_isHomLift_a Φ (W'.hom ≫ u) hΦ
  exact ⟨_, Φ, hq'.isStronglyCartesian_homLift (W'.hom ≫ u) Φ⟩

open Opposite _root_.CategoryTheory.Functor in
/-- A section of `Mor(j y, j w)` over the terminal object of `𝒞/V` is a vertical morphism
`j y ⟶ j w`; if a section of `Mor(y, w)` over `W'` maps to its restriction, then its image under
`j` is that morphism base changed along `W'.hom`. -/
private lemma sec_fac (hj₁ : Functor.IsFibredOneMorphism p𝒴 p𝒴' j) {V : 𝒞} (y w : p𝒴.Fiber V)
    (θsec :
      (morPresheaf p𝒴' ((fiberFunctorOfCompEq hj₁.comp_eq V).obj y)
            ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w)).obj
        (op (Over.mk (𝟙 V))))
    (θ : j.obj y.1 ⟶ j.obj w.1)
    (hθ :
      Fiber.fiberInclusion.map θsec ≫
          IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w).2
            (Over.mk (𝟙 V) : Over V).hom =
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hj₁.comp_eq V).obj y).2
            (Over.mk (𝟙 V) : Over V).hom ≫
          θ)
    {W' : Over V} (h : W' ⟶ Over.mk (𝟙 V)) (ψW : (morPresheaf p𝒴 y w).obj (op W'))
    (hap :
      (hj₁.morPresheafMap y w).app (op W') ψW =
        (morPresheaf p𝒴' ((fiberFunctorOfCompEq hj₁.comp_eq V).obj y)
              ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w)).map
          h.op θsec) :
    j.map (Fiber.fiberInclusion.map ψW) ≫ j.map (IsPreFibered.pullbackMap w.2 W'.hom) =
      j.map (IsPreFibered.pullbackMap y.2 W'.hom) ≫ θ := by
  have hrfl :
    (morPresheaf p𝒴' ((fiberFunctorOfCompEq hj₁.comp_eq V).obj y)
            ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w)).map
        h.op θsec =
      morRestrict p𝒴' ((fiberFunctorOfCompEq hj₁.comp_eq V).obj y)
        ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w) h θsec :=
    rfl
  rw [hrfl] at hap
  have h1 :=
    congrArg
      (fun m =>
        Fiber.fiberInclusion.map m ≫
          IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hj₁.comp_eq V).obj w).2 W'.hom)
      hap
  simp only [fiberInclusion_morPresheafMap_app, Category.assoc,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, morRestrict_fac, hθ] at h1
  rw [pullbackFiberMap_fac_assoc, ←
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hj₁ y W'.hom, Category.assoc] at h1
  exact (cancel_epi _).mp h1

include hf₁ hg₁ hi₁ hk₁ hHmor γ hγ δ hδ in
open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳'.IsFibered] [p𝒵'.IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered] hHmor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
/-- **Clause (2) for one member of the covering.** Given cartesian morphisms over `u` from `i x`
and `k z` to the two components of `P'`, the comparison isomorphism of `P'` yields a vertical `ω`
by the universal property of the second one; `ω` is locally in the image of `j` because `j`
sheafifies the morphism presheaves, and on the covering where it is
`CategoryTheory.TwoFibreProductOver.objStepConstruct` applies. -/
lemma objStep (J : GrothendieckTopology 𝒞) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (hq' : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFiberedInGroupoids)
    (hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f') (hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')
    (hj₁ : Functor.IsFibredOneMorphism p𝒴 p𝒴' j) (α : i ⋙ f' ≅ f ⋙ j)
    (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) (β : k ⋙ g' ≅ g ⋙ j)
    (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z))
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    (hmor𝒴 :
      ∀ (V : 𝒞) (y w : p𝒴.Fiber V),
        Presheaf.IsLocallySurjective (J.over V) (hj₁.morPresheafMap y w))
    (P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g') {V : 𝒞} (u : V ⟶ P'.base) {x : 𝒳}
    (a : i.obj x ⟶ P'.x) (ha : p𝒳'.IsHomLift u a) (hxV : p𝒳.obj x = V) {z : 𝒵} (b : k.obj z ⟶ P'.y)
    (hb : p𝒵'.IsHomLift u b) (hzV : p𝒵.obj z = V) :
    ∃ R ∈ J V,
      ∀ ⦃W : 𝒞⦄ (t : W ⟶ V),
        R t →
          ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : H.obj P ⟶ P'),
            (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian (t ≫ u) φ := by
  have := ha
  have := hb
  have hgb := Functor.isHomLift_map_of_comp_eq hg'₁.comp_eq u b
  have hgbc : p𝒴'.IsStronglyCartesian u (g'.map b) := h𝒴'.isStronglyCartesian_homLift u (g'.map b)
  have hfa := Functor.isHomLift_map_of_comp_eq hf'₁.comp_eq u a
  have hP'v := P'.vertical
  have hfaP : p𝒴'.IsHomLift u (f'.map a ≫ P'.iso.hom) := by
    have h0 : p𝒴'.IsHomLift (u ≫ 𝟙 P'.base) (f'.map a ≫ P'.iso.hom) := inferInstance
    rwa [Category.comp_id] at h0
  have := hgbc
  have := hfaP
  set ω :=
    IsStronglyCartesian.map p𝒴' u (g'.map b) (g := 𝟙 V) (Category.id_comp u).symm
      (f'.map a ≫ P'.iso.hom) with
    hωdef
  have hωfac : ω ≫ g'.map b = f'.map a ≫ P'.iso.hom :=
    IsStronglyCartesian.fac p𝒴' u (g'.map b) (Category.id_comp u).symm (f'.map a ≫ P'.iso.hom)
  have hωlift : p𝒴'.IsHomLift (𝟙 V) ω :=
    IsStronglyCartesian.map_isHomLift p𝒴' u (g'.map b) (Category.id_comp u).symm
      (f'.map a ≫ P'.iso.hom)
  have hαx : p𝒴'.IsHomLift (𝟙 V) (α.hom.app x) := by
    rw [← hxV]
    exact hα x
  have hβz : p𝒴'.IsHomLift (𝟙 V) (β.hom.app z) := by
    rw [← hzV]
    exact hβ z
  have hαxi := isHomLift_inv_app α x hαx
  have hθ : p𝒴'.IsHomLift (𝟙 V) (α.inv.app x ≫ ω ≫ β.hom.app z) := inferInstance
  set θfib :
    (fiberFunctorOfCompEq hj₁.comp_eq V).obj ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩) ⟶
      (fiberFunctorOfCompEq hj₁.comp_eq V).obj
        ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩) :=
    ⟨α.inv.app x ≫ ω ≫ β.hom.app z, hθ⟩ with hθfibdef
  set θsec :
    (morPresheaf p𝒴'
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
            ((fiberFunctorOfCompEq hf₁.comp_eq V).obj (⟨x, hxV⟩ : p𝒳.Fiber V)))
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V)))).obj
      (op (Over.mk (𝟙 V))) :=
    (pullbackFiberIdIso
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
            ((fiberFunctorOfCompEq hf₁.comp_eq V).obj (⟨x, hxV⟩ : p𝒳.Fiber V)))).hom ≫
      θfib ≫
      (pullbackFiberIdIso
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V)))).inv with
    hθsecdef
  have hLS :=
    hmor𝒴 V ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
      ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩)
  refine
    ⟨Sieve.overEquiv (Over.mk (𝟙 V))
        (Presheaf.imageSieve
          (hj₁.morPresheafMap ((fiberFunctorOfCompEq hf₁.comp_eq V).obj ⟨x, hxV⟩)
            ((fiberFunctorOfCompEq hg₁.comp_eq V).obj ⟨z, hzV⟩))
          θsec),
      hLS.imageSieve_mem θsec, ?_⟩
  have hθprop :
    Fiber.fiberInclusion.map θsec ≫
        IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
              ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V))).2
          (𝟙 V) =
      IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
              ((fiberFunctorOfCompEq hf₁.comp_eq V).obj (⟨x, hxV⟩ : p𝒳.Fiber V))).2
          (𝟙 V) ≫
        (α.inv.app x ≫ ω ≫ β.hom.app z) := by
    have hθfibι : Fiber.fiberInclusion.map θfib = α.inv.app x ≫ ω ≫ β.hom.app z := by
      rw [hθfibdef]
      rfl
    have hid :
      β.hom.app z ≫
          𝟙
            ((fiberFunctorOfCompEq hj₁.comp_eq V).obj
                ((fiberFunctorOfCompEq hg₁.comp_eq V).obj (⟨z, hzV⟩ : p𝒵.Fiber V))).1 =
        β.hom.app z :=
      Category.comp_id _
    rw [hθsecdef]
    simp only [Over.mk_hom, Over.mk_left, Functor.map_comp, Category.assoc, hθfibι,
      pullbackFiberIdIso_inv_fac, pullbackFiberIdIso_hom_fac, hid]
  intro W t htmem
  rw [Sieve.overEquiv_iff] at htmem
  obtain ⟨ψW, hap⟩ := htmem
  obtain ⟨P, φ, hφ⟩ :=
    objStepConstruct hf₁ hg₁ hi₁ hk₁ γ hγ δ hδ h𝒴 hq' hf'₁ hg'₁ α β hψ P' u a ha hxV b hb hzV
      ω hωfac _ ψW (sec_fac hj₁ _ _ θsec (α.inv.app x ≫ ω ≫ β.hom.app z) hθprop _ ψW hap)
  exact ⟨P, φ, by simpa using hφ⟩
end

end

end CategoryTheory.TwoFibreProductOver

end
