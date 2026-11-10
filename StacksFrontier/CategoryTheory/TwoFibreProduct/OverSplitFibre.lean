module

public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullbackProjections

/-!
# The split fibre of a 2-fibre product (Stacks 0CMT, 02XI, 004A)

`StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibres` identifies the fibre of
`CategoryTheory.TwoFibreProductOver` at an object `U` of the base with the 2-fibre product of the
fibre categories, and `StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibrePullback` compares the
chosen pullbacks on the two sides. This file assembles those two comparisons into the identities
a *functor* out of the **split fibre** of Stacks 004A needs.

An object of `CategoryTheory.Functor.SplitFiber (structureFunctor …) V` is a triple `(U, P, h)`
with `P` an object of the fibre of the 2-fibre product over `U` and `h : V ⟶ U`, and a morphism
between two such is a morphism between the *chosen pullbacks* `h^* P`. Reading such a datum
componentwise sends `(U, P, h)` to the pair `(U, P.x, h)`, `(U, P.y, h)` together with the chosen
pullback along `h` of the comparison isomorphism of `P`, and sends a morphism to the two
components of `CategoryTheory.TwoFibreProductOver.toFiberPullback` conjugated by
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` and
`…pullbackFiberSndIsoOfFiberedInGroupoids`. That this
is well defined is the compatibility condition `mapPullbackFiberIso_conj_w`, and that it is
*strictly* natural in `V` is `restrictHom_conj_fst`, `restrictHom_conj_snd` and
`restrictHom_pullbackFiberHom`: restriction is `h ↦ g ≫ h` on both sides.

## Main results

* `CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso`: the comparison
  isomorphism of a chosen pullback in the 2-fibre product is the chosen pullback of the
  comparison isomorphism, read through the four base-change comparisons.
* `CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_w`: the compatibility condition
  of the componentwise reading of a morphism of the split fibre.
* `CategoryTheory.TwoFibreProductOver.restrictHom_conj_fst` and `…restrictHom_conj_snd`: the
  componentwise reading of a morphism commutes with restriction along `g : V' ⟶ V`.
* `CategoryTheory.TwoFibreProductOver.restrictHom_pullbackFiberHom`: restricting a chosen
  pullback of a morphism of a fibre gives the chosen pullback along the composite.

## Implementation notes

Every identity here is proved by the universal property of a chosen cartesian lift, either
through `CategoryTheory.Functor.fiber_hom_ext_of_cartesian` or through
`CategoryTheory.Functor.SplitFiber.restrictHom_uniq`, and the input is always one of the
factorizations `*_fac` of the comparison isomorphisms involved. The two components of a morphism
of `CategoryTheory.TwoFibreProductOver` are functorial on the nose
(`CategoryTheory.TwoFibreProductOver.comp_a`, `…comp_b` are `rfl`), so an identity in the
2-fibre product is transported to its components by `congrArg` on a named `have`.

`CategoryTheory.Functor.fiberMap` and `CategoryTheory.Functor.fiberFunctorOfCompEq` are the same
functor under two names, and the comparisons of `OverFibres` are stated with the first while
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` is stated with the second, so
`fiberMap` is made `implicit_reducible` here and
`pullbackFiberHom_toFiberPullback_fac` restates the factorization of
`CategoryTheory.Functor.pullbackFiberHom` in the second spelling.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/
@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

open Limits _root_.CategoryTheory.Functor

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.fiberMap

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

section Restrict

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

/-- **Base change of a chosen pullback of a morphism of a fibre.** Restricting along `g` the
morphism of the split fibre given by the chosen pullback of `ψ` along `h` gives the chosen
pullback of `ψ` along `g ≫ h`. -/
lemma restrictHom_pullbackFiberHom {U V V' : 𝒞} {x y : p.Fiber U} (ψ : x ⟶ y)
    (h : V ⟶ U) (g : V' ⟶ V) :
    Functor.SplitFiber.restrictHom (p := p) g
        (o := ⟨U, x, h⟩) (o' := ⟨U, y, h⟩) (Functor.pullbackFiberHom ψ h) =
      Functor.pullbackFiberHom ψ (g ≫ h) :=
  (Functor.SplitFiber.restrictHom_uniq (p := p) (o := ⟨U, x, h⟩) (o' := ⟨U, y, h⟩) g
    (Functor.pullbackFiberHom ψ h) _ (by
    change Fiber.fiberInclusion.map (Functor.pullbackFiberHom ψ (g ≫ h)) ≫
        Functor.IsPreFibered.pullbackMap y.2 (g ≫ h) =
      Functor.pullbackFiberProj x h g ≫
        Fiber.fiberInclusion.map (Functor.pullbackFiberHom ψ h) ≫
        Functor.IsPreFibered.pullbackMap y.2 h
    rw [Functor.pullbackFiberHom_fac, Functor.pullbackFiberHom_fac,
      Functor.pullbackFiberProj_fac_assoc])).symm

end Restrict


section SplitFibre

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)

/-! Local notation for the five long applications this section repeats: the 2-fibre product
`CategoryTheory.TwoFibreProductOver.structureFunctor`, the comparison
`CategoryTheory.TwoFibreProductOver.toFiberPullback`, the two chosen-pullback comparisons
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` and
`CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids`, and the two
components `CategoryTheory.TwoFibreProductOver.pullbackHomFst` and
`CategoryTheory.TwoFibreProductOver.pullbackHomSnd` of a chosen lift. -/

local notation "𝒲" => structureFunctor p𝒳 p𝒴 p𝒮 F G
local notation "𝒯" => toFiberPullback p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq
local notation "𝒜" => pullbackFiberFstIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq
local notation "ℬ" => pullbackFiberSndIsoOfFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq
local notation "𝔞" => pullbackHomFst p𝒳 p𝒴 p𝒮 F G
local notation "𝔟" => pullbackHomSnd p𝒳 p𝒴 p𝒮 F G

omit [p𝒴.IsFibered] [p𝒮.IsFibered] in
/-- The inverse comparison of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` factors
the chosen `𝒳`-lift of `f` through the `𝒳`-component of the chosen lift of `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberFstIsoOfFiberedInGroupoids_inv_fac {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map
          (𝒜 P f h𝒳).inv ≫
        𝔞 P f =
      IsPreFibered.pullbackMap
        ((𝒯 U).obj P).fst.2 f :=
  have : p𝒳.IsStronglyCartesian f (𝔞 P f) :=
    h𝒳.isStronglyCartesian_homLift f (𝔞 P f)
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

omit [p𝒳.IsFibered] [p𝒮.IsFibered] in
/-- The inverse comparison of
`CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids` factors
the chosen `𝒴`-lift of `f` through the `𝒴`-component of the chosen lift of `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberSndIsoOfFiberedInGroupoids_inv_fac {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map
          (ℬ P f h𝒴).inv ≫
        𝔟 P f =
      IsPreFibered.pullbackMap
        ((𝒯 U).obj P).snd.2 f :=
  have : p𝒴.IsStronglyCartesian f (𝔟 P f) :=
    h𝒴.isStronglyCartesian_homLift f (𝔟 P f)
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered] in
include hG h𝒴 in
/-- The `𝒴`-component of the chosen lift of `f` in the 2-fibre product is cartesian after `G`. -/
lemma isCartesian_map_pullbackHomSnd {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    p𝒮.IsCartesian f (G.map (𝔟 P f)) :=
  have : p𝒴.IsStronglyCartesian f (𝔟 P f) :=
    h𝒴.isStronglyCartesian_homLift f (𝔟 P f)
  have := hG.map_isStronglyCartesian f (𝔟 P f) inferInstance
  inferInstance

include h𝒳 h𝒴 in
/-- **The comparison isomorphism of a chosen pullback in the 2-fibre product is the chosen
pullback of its comparison isomorphism**, read through the four base-change comparisons: the two
components of `CategoryTheory.TwoFibreProductOver.toFiberPullback` on the chosen pullback and the
images under `F` and `G` of the chosen pullbacks of the components. -/
lemma mapPullbackFiberIso_conj_obj_iso {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    (hF.mapPullbackFiberIso
          ((𝒯 U).obj P).fst f).hom ≫
        (fiberFunctorOfCompEq hF.comp_eq V).map
          (𝒜 P f h𝒳).inv ≫
        ((𝒯 V).obj
          (Functor.pullbackFiber (𝒲) P f)).iso.hom =
      Functor.pullbackFiberHom
          ((𝒯 U).obj P).iso.hom f ≫
        (hG.mapPullbackFiberIso
            ((𝒯 U).obj P).snd f).hom ≫
          (fiberFunctorOfCompEq hG.comp_eq V).map
            (ℬ P f h𝒴).inv := by
  refine Functor.fiber_hom_ext_of_cartesian f
    (G.map (𝔟 P f))
    (isCartesian_map_pullbackHomSnd p𝒳 p𝒴 p𝒮 F G hG h𝒴 P f) _ _ ?_
  have hw : Fiber.fiberInclusion.map
        ((𝒯 V).obj
          (Functor.pullbackFiber (𝒲) P f)).iso.hom ≫
        G.map (𝔟 P f) =
      F.map (𝔞 P f) ≫
        Fiber.fiberInclusion.map
          ((𝒯 U).obj P).iso.hom :=
    ((Functor.IsPreFibered.pullbackMap P.2 f).w).symm
  simp only [Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map, hw]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    pullbackFiberFstIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒳,
    pullbackFiberSndIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒴,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc,
    Functor.pullbackFiberHom_fac]


include h𝒳 h𝒴 in
/-- **The comparison isomorphism of a chosen pullback in the 2-fibre product, with the two
base-change comparisons of the projections moved to the ends.** This is
`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso` with the comparison of the
`𝒳`-components cancelled on the left and the comparison of the `𝒴`-components on the right; it is
the form in which the chosen pullback of a comparison isomorphism is read off a 2-cell of the
squares of Stacks 0CMR. -/
lemma mapPullbackFiberIso_inv_comp_pullbackFiberHom {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    (hF.mapPullbackFiberIso ((𝒯 U).obj P).fst f).inv ≫
        Functor.pullbackFiberHom ((𝒯 U).obj P).iso.hom f =
      (fiberFunctorOfCompEq hF.comp_eq V).map (𝒜 P f h𝒳).inv ≫
        ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P f)).iso.hom ≫
          (fiberFunctorOfCompEq hG.comp_eq V).map (ℬ P f h𝒴).hom ≫
            (hG.mapPullbackFiberIso ((𝒯 U).obj P).snd f).inv := by
  have key := mapPullbackFiberIso_conj_obj_iso p𝒳 p𝒴 p𝒮 F G hF hG h𝒳 h𝒴 P f
  have hcancel : (fiberFunctorOfCompEq hG.comp_eq V).map (ℬ P f h𝒴).inv ≫
      (fiberFunctorOfCompEq hG.comp_eq V).map (ℬ P f h𝒴).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [Iso.inv_comp_eq, reassoc_of% key, reassoc_of% hcancel, Iso.hom_inv_id, Category.comp_id]

include h𝒳 h𝒴 in
/-- **The same identity with the two chosen-pullback comparisons replaced by the base-change
comparisons of the two projections.** They are mutually inverse
(`CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_fst_eq` and `…_snd_eq`), and this is the
spelling in which the 2-cells of the squares of Stacks 0CMR present them: each of the four
comparisons is then the base-change comparison of a fibred 1-morphism. -/
lemma mapPullbackFiberIso_inv_comp_pullbackFiberHom_proj {U V : 𝒞}
    (hfst : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒳
      (fst p𝒳 p𝒴 p𝒮 F G))
    (hsnd : Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒴 p𝒮 F G) p𝒴
      (snd p𝒳 p𝒴 p𝒮 F G))
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    (hF.mapPullbackFiberIso ((𝒯 U).obj P).fst f).inv ≫
        Functor.pullbackFiberHom ((𝒯 U).obj P).iso.hom f =
      (fiberFunctorOfCompEq hF.comp_eq V).map ((hfst.mapPullbackFiberIso P f).hom) ≫
        ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P f)).iso.hom ≫
          (fiberFunctorOfCompEq hG.comp_eq V).map ((hsnd.mapPullbackFiberIso P f).inv) ≫
            (hG.mapPullbackFiberIso ((𝒯 U).obj P).snd f).inv := by
  rw [mapPullbackFiberIso_fst_eq p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq P f h𝒳 hfst,
    mapPullbackFiberIso_snd_eq p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq P f h𝒴 hsnd,
    Iso.symm_hom, Iso.symm_inv]
  exact mapPullbackFiberIso_inv_comp_pullbackFiberHom p𝒳 p𝒴 p𝒮 F G hF hG h𝒳 h𝒴 P f

include h𝒳 h𝒴 in
/-- `CategoryTheory.TwoFibreProductOver.mapPullbackFiberIso_conj_obj_iso` read in `𝒮`. -/
@[reassoc]
lemma mapPullbackFiberIso_conj_obj_iso_inclusion {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map
          (hF.mapPullbackFiberIso ((𝒯 U).obj P).fst f).hom ≫
        F.map (Fiber.fiberInclusion.map (𝒜 P f h𝒳).inv) ≫
        Fiber.fiberInclusion.map
          ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P f)).iso.hom =
      Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom ((𝒯 U).obj P).iso.hom f) ≫
        Fiber.fiberInclusion.map
          (hG.mapPullbackFiberIso ((𝒯 U).obj P).snd f).hom ≫
        G.map (Fiber.fiberInclusion.map (ℬ P f h𝒴).inv) := by
  have h := congrArg Fiber.fiberInclusion.map
    (mapPullbackFiberIso_conj_obj_iso p𝒳 p𝒴 p𝒮 F G hF hG h𝒳 h𝒴 P f)
  simpa only [Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map] using h

omit [p𝒳.IsFibered] [p𝒴.IsFibered] [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered] in
/-- The chosen pullback of the comparison isomorphism factors through the chosen pullbacks of
the two components. -/
@[reassoc]
lemma pullbackFiberHom_toFiberPullback_fac {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom ((𝒯 U).obj P).iso.hom f) ≫
        Functor.IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hG.comp_eq U).obj ((𝒯 U).obj P).snd).2 f =
      Functor.IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hF.comp_eq U).obj ((𝒯 U).obj P).fst).2 f ≫
        Fiber.fiberInclusion.map ((𝒯 U).obj P).iso.hom :=
  Functor.pullbackFiberHom_fac _ f

omit [p𝒴.IsFibered] [p𝒮.IsFibered] in
include h𝒳 in
/-- The image under `F` of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac`. -/
@[reassoc]
lemma map_pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    F.map (Fiber.fiberInclusion.map (𝒜 P f h𝒳).hom) ≫
        F.map (Functor.IsPreFibered.pullbackMap ((𝒯 U).obj P).fst.2 f) =
      F.map (𝔞 P f) := by
  rw [← Functor.map_comp, pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac]

omit [p𝒳.IsFibered] [p𝒮.IsFibered] in
include h𝒴 in
/-- The image under `G` of
`CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac`. -/
@[reassoc]
lemma map_pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac {U V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) :
    G.map (Fiber.fiberInclusion.map (ℬ P f h𝒴).hom) ≫
        G.map (Functor.IsPreFibered.pullbackMap ((𝒯 U).obj P).snd.2 f) =
      G.map (𝔟 P f) := by
  rw [← Functor.map_comp, pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac]

include h𝒳 h𝒴 in
/-- **The compatibility condition of the comparison out of the split fibre of a 2-fibre
product.** Conjugating the two components of a morphism of the fibre by the comparisons of the
chosen pullbacks intertwines the chosen pullbacks of the two comparison isomorphisms. -/
lemma mapPullbackFiberIso_conj_w {U U' V : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) (P' : (𝒲).Fiber U') (f' : V ⟶ U')
    (α : Functor.pullbackFiber (𝒲) P f ⟶ Functor.pullbackFiber (𝒲) P' f') :
    ((hF.mapPullbackFiberIso ((𝒯 U).obj P).fst f).hom ≫
          (fiberFunctorOfCompEq hF.comp_eq V).map
            ((𝒜 P f h𝒳).inv ≫ ((𝒯 V).map α).fst ≫ (𝒜 P' f' h𝒳).hom) ≫
          (hF.mapPullbackFiberIso ((𝒯 U').obj P').fst f').inv) ≫
        Functor.pullbackFiberHom ((𝒯 U').obj P').iso.hom f' =
      Functor.pullbackFiberHom ((𝒯 U).obj P).iso.hom f ≫
        ((hG.mapPullbackFiberIso ((𝒯 U).obj P).snd f).hom ≫
          (fiberFunctorOfCompEq hG.comp_eq V).map
            ((ℬ P f h𝒴).inv ≫ ((𝒯 V).map α).snd ≫ (ℬ P' f' h𝒴).hom) ≫
          (hG.mapPullbackFiberIso ((𝒯 U').obj P').snd f').inv) := by
  refine Functor.fiber_hom_ext_of_cartesian f'
    (Functor.IsPreFibered.pullbackMap
      ((fiberFunctorOfCompEq hG.comp_eq U').obj ((𝒯 U').obj P').snd).2 f')
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ f') _ _ ?_
  have hwP' : F.map (𝔞 P' f') ≫
        Fiber.fiberInclusion.map ((𝒯 U').obj P').iso.hom =
      Fiber.fiberInclusion.map
          ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P' f')).iso.hom ≫
        G.map (𝔟 P' f') :=
    (Functor.IsPreFibered.pullbackMap P'.2 f').w
  have hwα : F.map (Fiber.fiberInclusion.map (((𝒯 V).map α).fst)) ≫
        Fiber.fiberInclusion.map
          ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P' f')).iso.hom =
      Fiber.fiberInclusion.map
          ((𝒯 V).obj (Functor.pullbackFiber (𝒲) P f)).iso.hom ≫
        G.map (Fiber.fiberInclusion.map (((𝒯 V).map α).snd)) :=
    (Fiber.fiberInclusion.map α).w
  simp only [Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc,
    pullbackFiberHom_toFiberPullback_fac p𝒳 p𝒴 p𝒮 F G hF hG,
    map_pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac_assoc p𝒳 p𝒴 p𝒮 F G hF hG h𝒳,
    map_pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒴,
    hwP', reassoc_of% hwα,
    mapPullbackFiberIso_conj_obj_iso_inclusion_assoc p𝒳 p𝒴 p𝒮 F G hF hG h𝒳 h𝒴]


/-- Two composites `i ≫ s` and `t ≫ j` over `g` agree if they agree after a strongly cartesian
morphism over `f`, where `i` and `j` lie over identities. -/
private lemma comp_eq_comp_of_comp_eq {𝒵 : Type*} [Category 𝒵] {p : 𝒵 ⥤ 𝒞} {U V V' : 𝒞}
    (f : V ⟶ U) (g : V' ⟶ V) {a b c e z : 𝒵} (i : a ⟶ b) (s : b ⟶ c) (t : a ⟶ e) (j : e ⟶ c)
    (φ : c ⟶ z) [p.IsStronglyCartesian f φ] [p.IsHomLift (𝟙 V') i] [p.IsHomLift g s]
    [p.IsHomLift g t] [p.IsHomLift (𝟙 V) j] (h : (i ≫ s) ≫ φ = (t ≫ j) ≫ φ) : i ≫ s = t ≫ j := by
  have : p.IsHomLift g (i ≫ s) := by simpa using (inferInstance : p.IsHomLift (𝟙 V' ≫ g) (i ≫ s))
  have : p.IsHomLift g (t ≫ j) := by simpa using (inferInstance : p.IsHomLift (g ≫ 𝟙 V) (t ≫ j))
  exact Functor.IsStronglyCartesian.ext p f φ g h

omit [p𝒴.IsFibered] [p𝒮.IsFibered] in
include h𝒳 in
/-- **`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids` is natural in
the slice**: it intertwines the canonical morphism `(g ≫ f)^* ⟶ f^*` of the 2-fibre product with
that of its `𝒳`-component. -/
@[reassoc]
lemma pullbackFiberFstIsoOfFiberedInGroupoids_inv_pullbackFiberProj {U V V' : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) (g : V' ⟶ V) :
    Fiber.fiberInclusion.map (𝒜 P (g ≫ f) h𝒳).inv ≫
        (Functor.pullbackFiberProj P f g).a =
      Functor.pullbackFiberProj ((𝒯 U).obj P).fst f g ≫
        Fiber.fiberInclusion.map (𝒜 P f h𝒳).inv := by
  have : p𝒳.IsStronglyCartesian f (𝔞 P f) :=
    h𝒳.isStronglyCartesian_homLift f _
  have hv : p𝒳.IsHomLift (𝟙 V')
      (Fiber.fiberInclusion.map (𝒜 P (g ≫ f) h𝒳).inv) :=
    (𝒜 P (g ≫ f) h𝒳).inv.2
  have hv' : p𝒳.IsHomLift (𝟙 V)
      (Fiber.fiberInclusion.map (𝒜 P f h𝒳).inv) :=
    (𝒜 P f h𝒳).inv.2
  have ha : p𝒳.IsHomLift g (Functor.pullbackFiberProj P f g).a :=
    isHomLift_a (Functor.pullbackFiberProj P f g) g inferInstance
  have hcomp : (Functor.pullbackFiberProj P f g).a ≫ 𝔞 P f =
      𝔞 P (g ≫ f) :=
    congrArg TwoFibreProductOver.Hom.a (Functor.pullbackFiberProj_fac P f g)
  refine comp_eq_comp_of_comp_eq (p := p𝒳) f g _ _ _ _ (𝔞 P f) ?_
  rw [Category.assoc, Category.assoc, hcomp,
    pullbackFiberFstIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒳,
    pullbackFiberFstIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒳,
    Functor.pullbackFiberProj_fac]

omit [p𝒴.IsFibered] [p𝒮.IsFibered] in
include h𝒳 in
/-- **Base change of the conjugated `𝒳`-component of a morphism.** -/
lemma restrictHom_conj_fst {U U' V V' : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) (P' : (𝒲).Fiber U') (f' : V ⟶ U')
    (β : Functor.pullbackFiber (𝒲) P f ⟶ Functor.pullbackFiber (𝒲) P' f')
    (g : V' ⟶ V) :
    Functor.SplitFiber.restrictHom (p := p𝒳) g
        (o := ⟨U, ((𝒯 U).obj P).fst, f⟩) (o' := ⟨U', ((𝒯 U').obj P').fst, f'⟩)
        ((𝒜 P f h𝒳).inv ≫ ((𝒯 V).map β).fst ≫ (𝒜 P' f' h𝒳).hom) =
      (𝒜 P (g ≫ f) h𝒳).inv ≫
        ((𝒯 V').map (Functor.SplitFiber.restrictHom (p := 𝒲) g
          (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)).fst ≫
        (𝒜 P' (g ≫ f') h𝒳).hom := by
  have hfac : Fiber.fiberInclusion.map
          (((𝒯 V').map (Functor.SplitFiber.restrictHom (p := 𝒲) g
            (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)).fst) ≫
        𝔞 P' (g ≫ f') =
      (Functor.pullbackFiberProj P f g).a ≫
        Fiber.fiberInclusion.map (((𝒯 V).map β).fst) ≫
        𝔞 P' f' :=
    congrArg TwoFibreProductOver.Hom.a
      (Functor.SplitFiber.restrictHom_fac (p := 𝒲) g
        (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)
  refine (Functor.SplitFiber.restrictHom_uniq (p := p𝒳)
    (o := ⟨U, ((𝒯 U).obj P).fst, f⟩) (o' := ⟨U', ((𝒯 U').obj P').fst, f'⟩)
    g _ _ ?_).symm
  dsimp only [Functor.SplitFiber.proj]
  simp only [Functor.map_comp, Category.assoc,
    pullbackFiberFstIsoOfFiberedInGroupoids_hom_fac p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq (h𝒳 := h𝒳)]
  rw [hfac, pullbackFiberFstIsoOfFiberedInGroupoids_inv_pullbackFiberProj_assoc
    p𝒳 p𝒴 p𝒮 F G hF hG h𝒳]

omit [p𝒳.IsFibered] [p𝒮.IsFibered] in
include h𝒴 in
/-- **`CategoryTheory.TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids` is natural in
the slice**, by the argument of
`CategoryTheory.TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids_inv_pullbackFiberProj`
on the other side. -/
@[reassoc]
lemma pullbackFiberSndIsoOfFiberedInGroupoids_inv_pullbackFiberProj {U V V' : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) (g : V' ⟶ V) :
    Fiber.fiberInclusion.map
          (ℬ P (g ≫ f) h𝒴).inv ≫
        (Functor.pullbackFiberProj P f g).b =
      Functor.pullbackFiberProj ((𝒯 U).obj P).snd f g ≫
        Fiber.fiberInclusion.map (ℬ P f h𝒴).inv := by
  have : p𝒴.IsStronglyCartesian f (𝔟 P f) :=
    h𝒴.isStronglyCartesian_homLift f _
  have hv : p𝒴.IsHomLift (𝟙 V')
      (Fiber.fiberInclusion.map (ℬ P (g ≫ f) h𝒴).inv) :=
    (ℬ P (g ≫ f) h𝒴).inv.2
  have hv' : p𝒴.IsHomLift (𝟙 V)
      (Fiber.fiberInclusion.map (ℬ P f h𝒴).inv) :=
    (ℬ P f h𝒴).inv.2
  have hb : p𝒴.IsHomLift g (Functor.pullbackFiberProj P f g).b :=
    isHomLift_b (Functor.pullbackFiberProj P f g) g inferInstance
  have hcomp : (Functor.pullbackFiberProj P f g).b ≫ 𝔟 P f =
      𝔟 P (g ≫ f) :=
    congrArg TwoFibreProductOver.Hom.b (Functor.pullbackFiberProj_fac P f g)
  refine comp_eq_comp_of_comp_eq (p := p𝒴) f g _ _ _ _ (𝔟 P f) ?_
  rw [Category.assoc, Category.assoc, hcomp,
    pullbackFiberSndIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒴,
    pullbackFiberSndIsoOfFiberedInGroupoids_inv_fac p𝒳 p𝒴 p𝒮 F G hF hG h𝒴,
    Functor.pullbackFiberProj_fac]

omit [p𝒳.IsFibered] [p𝒮.IsFibered] in
include h𝒴 in
/-- **Base change of the conjugated `𝒴`-component of a morphism**, by the argument of
`CategoryTheory.TwoFibreProductOver.restrictHom_conj_fst` on the other side. -/
lemma restrictHom_conj_snd {U U' V V' : 𝒞}
    (P : (𝒲).Fiber U) (f : V ⟶ U) (P' : (𝒲).Fiber U') (f' : V ⟶ U')
    (β : Functor.pullbackFiber (𝒲) P f ⟶ Functor.pullbackFiber (𝒲) P' f')
    (g : V' ⟶ V) :
    Functor.SplitFiber.restrictHom (p := p𝒴) g
        (o := ⟨U, ((𝒯 U).obj P).snd, f⟩) (o' := ⟨U', ((𝒯 U').obj P').snd, f'⟩)
        ((ℬ P f h𝒴).inv ≫ ((𝒯 V).map β).snd ≫ (ℬ P' f' h𝒴).hom) =
      (ℬ P (g ≫ f) h𝒴).inv ≫
        ((𝒯 V').map (Functor.SplitFiber.restrictHom (p := 𝒲) g
          (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)).snd ≫
        (ℬ P' (g ≫ f') h𝒴).hom := by
  have hfac : Fiber.fiberInclusion.map
          (((𝒯 V').map (Functor.SplitFiber.restrictHom (p := 𝒲) g
            (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)).snd) ≫
        𝔟 P' (g ≫ f') =
      (Functor.pullbackFiberProj P f g).b ≫
        Fiber.fiberInclusion.map (((𝒯 V).map β).snd) ≫
        𝔟 P' f' :=
    congrArg TwoFibreProductOver.Hom.b
      (Functor.SplitFiber.restrictHom_fac (p := 𝒲) g
        (o := ⟨U, P, f⟩) (o' := ⟨U', P', f'⟩) β)
  refine (Functor.SplitFiber.restrictHom_uniq (p := p𝒴)
    (o := ⟨U, ((𝒯 U).obj P).snd, f⟩) (o' := ⟨U', ((𝒯 U').obj P').snd, f'⟩)
    g _ _ ?_).symm
  dsimp only [Functor.SplitFiber.proj]
  simp only [Functor.map_comp, Category.assoc,
    pullbackFiberSndIsoOfFiberedInGroupoids_hom_fac p𝒳 p𝒴 p𝒮 F G hF.comp_eq hG.comp_eq (h𝒴 := h𝒴)]
  rw [hfac, pullbackFiberSndIsoOfFiberedInGroupoids_inv_pullbackFiberProj_assoc
    p𝒳 p𝒴 p𝒮 F G hF hG h𝒴]

end SplitFibre

end CategoryTheory.TwoFibreProductOver

end
