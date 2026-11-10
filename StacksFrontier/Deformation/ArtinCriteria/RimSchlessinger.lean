module

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.Deformation.Artin.RimSchlessinger
import StacksCore.Tactic.StacksAttribute

/-!
# The Rim-Schlessinger conditions are stable under 2-fibre products

The 2-fibre product over the big fppf site of a scheme of categories fibred in groupoids
satisfying condition (RS) again satisfies (RS), and likewise for condition (RS*).

## Main results

* `Deformation.Artin.satisfiesRS_twoFibreProductOver`: condition (RS) is preserved by the
  2-fibre product of categories fibred in groupoids over the big fppf site.
* `Deformation.Artin.twoFibreProductOver_satisfiesRSStar`: the same for condition (RS*).

## References

* [Stacks Project, Tag 07WR](https://stacks.math.columbia.edu/tag/07WR)
* [Stacks Project, Tag 0CXQ](https://stacks.math.columbia.edu/tag/0CXQ)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁ v₂ v₃ v₄ uX uY uZ

namespace Deformation.Artin

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
attribute [local implicit_reducible] Functor.fiberMap
attribute [local implicit_reducible]
  Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.pullbackFunctor
attribute [local implicit_reducible] Functor.chosenPullbacks
attribute [local implicit_reducible] TwoFibreProductOver.structureFunctor
attribute [local implicit_reducible] TwoFibreProductOver.fst TwoFibreProductOver.snd

/-! The standard `mapPullbackFiberIso` has a common hom universe for its two categories.
The two factors here need not have the same hom universe, so we use the same cartesian-lift
comparison in a universe-polymorphic form. -/
private noncomputable def mapPullbackFiberIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    (Functor.fiberMap p q F hF.comp_eq V).obj (p.pullbackFiber a f) ≅
      q.pullbackFiber ((Functor.fiberMap p q F hF.comp_eq U).obj a) f := by
  let φ := Functor.IsPreFibered.pullbackMap ((Functor.fiberMap p q F hF.comp_eq U).obj a).2 f
  let ψ := F.map (Functor.IsPreFibered.pullbackMap a.2 f)
  have hψ : q.IsStronglyCartesian f ψ := hF.map_isStronglyCartesian f _ inferInstance
  have hψ' : q.IsCartesian f ψ := by
    let := hψ
    infer_instance
  exact (Functor.fiberIsoOfCartesian f φ ψ inferInstance hψ').symm

@[reassoc] private lemma mapPullbackFiberIso_hom_fac
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a f).hom ≫
      Functor.IsPreFibered.pullbackMap ((Functor.fiberMap p q F hF.comp_eq U).obj a).2 f =
        F.map (Functor.IsPreFibered.pullbackMap a.2 f) :=
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

@[reassoc] private lemma mapPullbackFiberIso_inv_fac
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a f).inv ≫
        F.map (Functor.IsPreFibered.pullbackMap a.2 f) =
      Functor.IsPreFibered.pullbackMap
        ((Functor.fiberMap p q F hF.comp_eq U).obj a).2 f :=
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- `mapPullbackFiberIso_hom_fac` with the cartesian lifts written through the canonical choice
of pullbacks. -/
@[reassoc] private lemma mapPullbackFiberIso_hom_fac_chosen
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a f).hom ≫
      (Functor.chosenPullbacks q).map f ((Functor.fiberMap p q F hF.comp_eq U).obj a) =
        F.map ((Functor.chosenPullbacks p).map f a) :=
  mapPullbackFiberIso_hom_fac hF a f

/-- `mapPullbackFiberIso_inv_fac` with the cartesian lifts written through the canonical choice
of pullbacks. -/
@[reassoc] private lemma mapPullbackFiberIso_inv_fac_chosen
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a f).inv ≫
        F.map ((Functor.chosenPullbacks p).map f a) =
      (Functor.chosenPullbacks q).map f ((Functor.fiberMap p q F hF.comp_eq U).obj a) :=
  mapPullbackFiberIso_inv_fac hF a f

private lemma fiberInclusion_map_fiberMap_map
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞}
    {a b : p.Fiber U} (φ : a ⟶ b) :
    Functor.Fiber.fiberInclusion.map
        ((Functor.fiberMap p q F hF.comp_eq U).map φ) =
      F.map (Functor.Fiber.fiberInclusion.map φ) := by
  simpa only [Functor.Fiber.fiberInclusion] using
    (Functor.fiberMap_map_coe p q F hF.comp_eq U φ)

private lemma fiberInclusion_map_fiberMap_map_eq
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    {U : 𝒞} (h : F ⋙ q = p)
    {a b : p.Fiber U} (φ : a ⟶ b) :
    Functor.Fiber.fiberInclusion.map ((Functor.fiberMap p q F h U).map φ) =
      F.map (Functor.Fiber.fiberInclusion.map φ) := by
  simpa only [Functor.Fiber.fiberInclusion] using
    Functor.fiberMap_map_coe p q F h U φ

private lemma fiberInclusion_map_fiberMap_mapIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞}
    {a b : p.Fiber U} (e : a ≅ b) :
    Functor.Fiber.fiberInclusion.map
        ((Functor.fiberMap p q F hF.comp_eq U).mapIso e).hom =
      F.map (Functor.Fiber.fiberInclusion.map e.hom) := by
  rw [Functor.mapIso_hom]
  exact fiberInclusion_map_fiberMap_map hF e.hom

private lemma mapPullbackFiberIso_naturality
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U : 𝒞}
    {a b : p.Fiber U} (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    (Functor.fiberMap p q F hF.comp_eq V).map (Functor.pullbackFiberHom φ f) ≫
        (mapPullbackFiberIso hF b f).hom =
      (mapPullbackFiberIso hF a f).hom ≫
        Functor.pullbackFiberHom
          ((Functor.fiberMap p q F hF.comp_eq U).map φ) f := by
  have hpb : q.IsCartesian f
      (Functor.IsPreFibered.pullbackMap (p := q)
        ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian (p := q)
      ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f
  refine Functor.fiber_hom_ext_of_cartesian (p := q) f
    (a := F.obj b.1)
    (z := (Functor.fiberMap p q F hF.comp_eq V).obj (Functor.pullbackFiber p a f))
    (z' := ⟨Functor.IsPreFibered.pullbackObj
        ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f,
      Functor.IsPreFibered.pullbackObj_proj
        ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f⟩)
    (Functor.IsPreFibered.pullbackMap (p := q)
      ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f) hpb _ _ ?_
  change
    (Functor.Fiber.fiberInclusion.map
        ((Functor.fiberMap p q F hF.comp_eq V).map (Functor.pullbackFiberHom φ f)) ≫
      Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF b f).hom) ≫
      Functor.IsPreFibered.pullbackMap
        ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f =
    (Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a f).hom ≫
      Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberHom
        ((Functor.fiberMap p q F hF.comp_eq U).map φ) f)) ≫
      Functor.IsPreFibered.pullbackMap
        ((Functor.fiberMap p q F hF.comp_eq U).obj b).2 f
  simp only [Category.assoc, 
    mapPullbackFiberIso_hom_fac, Functor.pullbackFiberHom_fac]
  rw [fiberInclusion_map_fiberMap_map hF, ← Functor.map_comp,
    Functor.pullbackFiberHom_fac, Functor.map_comp,
    fiberInclusion_map_fiberMap_map hF, ← Category.assoc,
    mapPullbackFiberIso_hom_fac hF]

private noncomputable def pullbackMapIso
    {C : Type*} [Category* C] {A : Type*} [Category* A]
    {B : Type*} [Category* B] {p : A ⥤ C} {q : B ⥤ C}
    {F : A ⥤ B} [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) {U V : C} (f : V ⟶ U) :
    (Functor.chosenPullbacks p).pullbackFunctor f ⋙ Functor.fiberMap p q F hF.comp_eq V ≅
      Functor.fiberMap p q F hF.comp_eq U ⋙ (Functor.chosenPullbacks q).pullbackFunctor f :=
  NatIso.ofComponents (fun a => mapPullbackFiberIso hF a f)
    (fun m => mapPullbackFiberIso_naturality hF m f)

private def productFiberFst
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (_hF : F ⋙ p𝒟 = p𝒜) (_hG : G ⋙ p𝒟 = pℬ) {U : 𝒞}
    (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U) : p𝒜.Fiber U :=
  (Functor.fiberMap (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
    (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G) TwoFibreProductOver.fst_comp_eq U).obj P

private def productFiberSnd
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (_hF : F ⋙ p𝒟 = p𝒜) (_hG : G ⋙ p𝒟 = pℬ) {U : 𝒞}
    (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U) : pℬ.Fiber U :=
  (Functor.fiberMap (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
    (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G) TwoFibreProductOver.snd_comp_eq U).obj P

attribute [local implicit_reducible] productFiberFst productFiberSnd

private noncomputable def productPullbackFstIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ)
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U)
    {V : 𝒞} (f : V ⟶ U)
    (hfst : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
      (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G))
    [p𝒜.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered] :
    productFiberFst p𝒜 pℬ p𝒟 F G hF hG
        (Functor.pullbackFiber (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f) ≅
      Functor.pullbackFiber p𝒜 (productFiberFst p𝒜 pℬ p𝒟 F G hF hG P) f := by
  simpa only [productFiberFst] using mapPullbackFiberIso hfst P f

private noncomputable def productPullbackSndIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ)
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U)
    {V : 𝒞} (f : V ⟶ U)
    (hsnd : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
      (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G))
    [pℬ.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered] :
    productFiberSnd p𝒜 pℬ p𝒟 F G hF hG
        (Functor.pullbackFiber (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f) ≅
      Functor.pullbackFiber pℬ (productFiberSnd p𝒜 pℬ p𝒟 F G hF hG P) f := by
  simpa only [productFiberSnd] using mapPullbackFiberIso hsnd P f

private noncomputable def productFiberGluingIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ)
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U) :
    (Functor.fiberMap p𝒜 p𝒟 F hF U).obj (productFiberFst p𝒜 pℬ p𝒟 F G hF hG P) ≅
      (Functor.fiberMap pℬ p𝒟 G hG U).obj (productFiberSnd p𝒜 pℬ p𝒟 F G hF hG P) := by
  obtain ⟨P, hP⟩ := P
  subst hP
  exact Functor.fiberIsoOfLift p𝒟 P.iso P.vertical

private lemma fiberInclusion_map_productFiberGluingIso_hom
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ)
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U) :
    Functor.Fiber.fiberInclusion.map
        (productFiberGluingIso p𝒜 pℬ p𝒟 F G hF hG P).hom = P.1.iso.hom := by
  obtain ⟨P, hP⟩ := P
  change P.base = U at hP
  subst U
  rfl

private noncomputable def productPullbackGluingIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : Functor.IsFibredOneMorphism p𝒜 p𝒟 F)
    (hG : Functor.IsFibredOneMorphism pℬ p𝒟 G)
    (hfst : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
      (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G))
    (hsnd : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
      (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G))
    [p𝒜.IsFibered] [pℬ.IsFibered] [p𝒟.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered]
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    (Functor.fiberMap p𝒜 p𝒟 F hF.comp_eq V).obj
        (Functor.pullbackFiber p𝒜 (productFiberFst p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P) f) ≅
      (Functor.fiberMap pℬ p𝒟 G hG.comp_eq V).obj
        (Functor.pullbackFiber pℬ (productFiberSnd p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P) f) :=
  (Functor.fiberMap p𝒜 p𝒟 F hF.comp_eq V).mapIso
      (productPullbackFstIso hF.comp_eq hG.comp_eq P f hfst).symm ≪≫
    productFiberGluingIso p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq
      (Functor.pullbackFiber (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f) ≪≫
    (Functor.fiberMap pℬ p𝒟 G hG.comp_eq V).mapIso
      (productPullbackSndIso hF.comp_eq hG.comp_eq P f hsnd)

private lemma productPullbackGluingIso_eq
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : Functor.IsFibredOneMorphism p𝒜 p𝒟 F)
    (hG : Functor.IsFibredOneMorphism pℬ p𝒟 G)
    (hfst : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
      (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G))
    (hsnd : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
      (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G))
    [p𝒜.IsFibered] [pℬ.IsFibered] [p𝒟.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered]
    {U : 𝒞} (P : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    productPullbackGluingIso hF hG hfst hsnd P f =
      mapPullbackFiberIso hF (productFiberFst p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P) f ≪≫
        Functor.pullbackFiberIso
          (productFiberGluingIso p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P) f ≪≫
        (mapPullbackFiberIso hG
          (productFiberSnd p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P) f).symm := by
  let P' := Functor.pullbackFiber
    (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f
  have hcart : p𝒟.IsCartesian f
      (G.map (Functor.IsPreFibered.pullbackMap (productFiberSnd p𝒜 pℬ p𝒟 F G
        hF.comp_eq hG.comp_eq P).2 f)) := by
    have hsc := hG.map_isStronglyCartesian f
      (Functor.IsPreFibered.pullbackMap
        (productFiberSnd p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq P).2 f) inferInstance
    let := hsc
    infer_instance
  have hleft : Functor.Fiber.fiberInclusion.map
        (productPullbackGluingIso hF hG hfst hsnd P f).hom ≫
        G.map (Functor.IsPreFibered.pullbackMap (productFiberSnd p𝒜 pℬ p𝒟 F G
          hF.comp_eq hG.comp_eq P).2 f) =
      F.map (Functor.IsPreFibered.pullbackMap (productFiberFst p𝒜 pℬ p𝒟 F G
        hF.comp_eq hG.comp_eq P).2 f) ≫ P.1.iso.hom := by
    have hfst' :
        Functor.Fiber.fiberInclusion.map
            (productPullbackFstIso hF.comp_eq hG.comp_eq P f hfst).inv ≫
          (Functor.IsPreFibered.pullbackMap P.2 f).a =
          Functor.IsPreFibered.pullbackMap (productFiberFst p𝒜 pℬ p𝒟 F G
            hF.comp_eq hG.comp_eq P).2 f := by
      simpa [productPullbackFstIso, productFiberFst, Functor.fiberMap_obj_coe] using
        mapPullbackFiberIso_inv_fac hfst P f
    have hsnd' :
        Functor.Fiber.fiberInclusion.map
            (productPullbackSndIso hF.comp_eq hG.comp_eq P f hsnd).hom ≫
          Functor.IsPreFibered.pullbackMap (productFiberSnd p𝒜 pℬ p𝒟 F G
            hF.comp_eq hG.comp_eq P).2 f =
          (Functor.IsPreFibered.pullbackMap P.2 f).b := by
      simpa [productPullbackSndIso, productFiberSnd, Functor.fiberMap_obj_coe] using
        mapPullbackFiberIso_hom_fac hsnd P f
    have hfst'' :
        Functor.Fiber.fiberInclusion.map
            (productPullbackFstIso hF.comp_eq hG.comp_eq P f hfst).symm.hom ≫
          (Functor.IsPreFibered.pullbackMap P.2 f).a =
          Functor.IsPreFibered.pullbackMap (productFiberFst p𝒜 pℬ p𝒟 F G
            hF.comp_eq hG.comp_eq P).2 f := by
      simpa only [Iso.symm_hom] using hfst'
    have hw : (Functor.pullbackFiber
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f).1.iso.hom ≫
          G.map (Functor.IsPreFibered.pullbackMap P.2 f).b =
        F.map (Functor.IsPreFibered.pullbackMap P.2 f).a ≫ P.1.iso.hom :=
      ((Functor.IsPreFibered.pullbackMap P.2 f).w).symm
    simp only [productPullbackGluingIso, Iso.trans_hom, 
      Functor.map_comp, Category.assoc]
    rw [fiberInclusion_map_fiberMap_mapIso hF,
      fiberInclusion_map_productFiberGluingIso_hom,
      fiberInclusion_map_fiberMap_mapIso hG]
    rw [← Functor.map_comp G, hsnd', hw, ← Functor.map_comp_assoc, hfst'']
  have hright : Functor.Fiber.fiberInclusion.map
        (mapPullbackFiberIso hF (productFiberFst p𝒜 pℬ p𝒟 F G
          hF.comp_eq hG.comp_eq P) f ≪≫
          Functor.pullbackFiberIso (productFiberGluingIso p𝒜 pℬ p𝒟 F G
            hF.comp_eq hG.comp_eq P) f ≪≫
          (mapPullbackFiberIso hG (productFiberSnd p𝒜 pℬ p𝒟 F G
            hF.comp_eq hG.comp_eq P) f).symm).hom ≫
        G.map (Functor.IsPreFibered.pullbackMap (productFiberSnd p𝒜 pℬ p𝒟 F G
          hF.comp_eq hG.comp_eq P).2 f) =
      F.map (Functor.IsPreFibered.pullbackMap (productFiberFst p𝒜 pℬ p𝒟 F G
        hF.comp_eq hG.comp_eq P).2 f) ≫ P.1.iso.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
      Functor.pullbackFiberIso_hom]
    rw [mapPullbackFiberIso_inv_fac hG,
      Functor.pullbackFiberHom_fac, ← Category.assoc,
      mapPullbackFiberIso_hom_fac hF,
      fiberInclusion_map_productFiberGluingIso_hom]
  exact Iso.ext (Functor.fiber_hom_ext_of_cartesian f
    (G.map (Functor.IsPreFibered.pullbackMap (productFiberSnd p𝒜 pℬ p𝒟 F G
      hF.comp_eq hG.comp_eq P).2 f)) hcart _ _ (hleft.trans hright.symm))

private noncomputable def pullbackFiberInduced
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : Functor.IsFibredOneMorphism p𝒜 p𝒟 F)
    (hG : Functor.IsFibredOneMorphism pℬ p𝒟 G)
    [p𝒜.IsFibered] [pℬ.IsFibered] [p𝒟.IsFibered]
    {U V : 𝒞} (f : V ⟶ U) :
    CategoricalPullback
        (Functor.fiberMap p𝒜 p𝒟 F hF.comp_eq U)
        (Functor.fiberMap pℬ p𝒟 G hG.comp_eq U) ⥤
      CategoricalPullback
        (Functor.fiberMap p𝒜 p𝒟 F hF.comp_eq V)
        (Functor.fiberMap pℬ p𝒟 G hG.comp_eq V) := by
  exact CategoricalPullback.map _ _
    ((Functor.chosenPullbacks p𝒜).pullbackFunctor f)
    ((Functor.chosenPullbacks pℬ).pullbackFunctor f)
    ((Functor.chosenPullbacks p𝒟).pullbackFunctor f) _ _
    (pullbackMapIso hG f) (pullbackMapIso hF f).symm

private noncomputable def fiberToPullback
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ) (U : 𝒞) :
    (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U ⥤
      CategoricalPullback (Functor.fiberMap p𝒜 p𝒟 F hF U)
        (Functor.fiberMap pℬ p𝒟 G hG U) where
  obj P :=
    { fst := ⟨P.1.x, P.1.hx.trans P.2⟩
      snd := ⟨P.1.y, P.1.hy.trans P.2⟩
      iso := productFiberGluingIso p𝒜 pℬ p𝒟 F G hF hG P }
  map {P Q} φ :=
    { fst := ⟨φ.1.a, by
        let : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsHomLift (𝟙 U) φ.1 := φ.2
        exact Functor.isHomLift_map_of_comp_eq
          TwoFibreProductOver.fst_comp_eq (𝟙 U) φ.1⟩
      snd := ⟨φ.1.b, by
        let : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsHomLift (𝟙 U) φ.1 := φ.2
        exact Functor.isHomLift_map_of_comp_eq
          TwoFibreProductOver.snd_comp_eq (𝟙 U) φ.1⟩
      w := by
        let : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsHomLift
            (𝟙 U) φ.1 := φ.2
        let aA := (Functor.fiberMap
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
          (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G)
          TwoFibreProductOver.fst_comp_eq U).map φ
        let bB := (Functor.fiberMap
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
          (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G)
          TwoFibreProductOver.snd_comp_eq U).map φ
        have haA : Functor.Fiber.fiberInclusion.map aA = φ.1.a := by rfl
        have hbB : Functor.Fiber.fiberInclusion.map bB = φ.1.b := by rfl
        apply Functor.Fiber.hom_ext
        change Functor.Fiber.fiberInclusion.map
            ((Functor.fiberMap p𝒜 p𝒟 F hF U).map aA ≫
              (productFiberGluingIso p𝒜 pℬ p𝒟 F G hF hG Q).hom) =
          Functor.Fiber.fiberInclusion.map
            ((productFiberGluingIso p𝒜 pℬ p𝒟 F G hF hG P).hom ≫
              (Functor.fiberMap pℬ p𝒟 G hG U).map bB)
        rw [Functor.map_comp, Functor.map_comp]
        rw [fiberInclusion_map_fiberMap_map_eq hF,
          fiberInclusion_map_productFiberGluingIso_hom p𝒜 pℬ p𝒟 F G hF hG Q,
          fiberInclusion_map_productFiberGluingIso_hom p𝒜 pℬ p𝒟 F G hF hG P,
          fiberInclusion_map_fiberMap_map_eq hG]
        rw [haA, hbB]
        exact φ.1.w }
  map_id P := by
    apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl
  map_comp φ ψ := by
    apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl

private noncomputable def pullbackFiberToPullbackIso
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : Functor.IsFibredOneMorphism p𝒜 p𝒟 F)
    (hG : Functor.IsFibredOneMorphism pℬ p𝒟 G)
    (hfst : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
      (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G))
    (hsnd : Functor.IsFibredOneMorphism
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
      (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G))
    [p𝒜.IsFibered] [pℬ.IsFibered] [p𝒟.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered]
    {U V : 𝒞} (f : V ⟶ U) :
    fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U ⋙
        pullbackFiberInduced hF hG f ≅
      (Functor.chosenPullbacks
        (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor f ⋙
        fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V := by
  refine NatIso.ofComponents (fun P => ?_) ?_
  · let eA := productPullbackFstIso hF.comp_eq hG.comp_eq P f hfst
    let eB := productPullbackSndIso hF.comp_eq hG.comp_eq P f hsnd
    let T := (pullbackFiberInduced hF hG f).obj
      ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U).obj P)
    let Q := ((Functor.chosenPullbacks
      (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor f ⋙
        fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V).obj P
    have hQ : Q.iso = productFiberGluingIso p𝒜 pℬ p𝒟 F G
        hF.comp_eq hG.comp_eq
        (Functor.pullbackFiber
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) P f) := by
      rfl
    have hw :
        (Functor.fiberMap p𝒜 p𝒟 F hF.comp_eq V).map eA.symm.hom ≫ Q.iso.hom =
          T.iso.hom ≫ (Functor.fiberMap pℬ p𝒟 G hG.comp_eq V).map eB.symm.hom := by
      have hglue := congrArg Iso.hom
        (productPullbackGluingIso_eq hF hG hfst hsnd P f)
      dsimp only [productPullbackGluingIso] at hglue
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
       ] at hglue
      rw [← hQ] at hglue
      have hh := congrArg (fun m => m ≫
        (Functor.fiberMap pℬ p𝒟 G hG.comp_eq V).map eB.symm.hom) hglue
      convert hh using 1
      all_goals
        simp [T, Q, eA, eB, fiberToPullback, productFiberFst, productFiberSnd,
          pullbackFiberInduced,
          Category.assoc]
        rfl
    exact CategoricalPullback.mkIso eA.symm eB.symm hw
  · intro P Q φ
    apply CategoricalPullback.Hom.ext
    · let eP := productPullbackFstIso hF.comp_eq hG.comp_eq P f hfst
      let eQ := productPullbackFstIso hF.comp_eq hG.comp_eq Q f hfst
      change ((pullbackFiberInduced hF hG f).map
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U).map φ)).fst ≫
          eQ.symm.hom =
        eP.symm.hom ≫
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V).map
            (((Functor.chosenPullbacks
              (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor f).map φ)).fst
      have h := mapPullbackFiberIso_naturality hfst φ f
      have hL :
          (Functor.fiberMap
            (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
            (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G)
            TwoFibreProductOver.fst_comp_eq U).map φ =
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U).map φ).fst := by
        apply Subtype.ext
        rfl
      have hR :
          (Functor.fiberMap
            (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) p𝒜
            (TwoFibreProductOver.fst p𝒜 pℬ p𝒟 F G)
            TwoFibreProductOver.fst_comp_eq V).map (Functor.pullbackFiberHom φ f) =
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V).map
            (((Functor.chosenPullbacks
                (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor
              f).map φ)).fst := by
        apply Subtype.ext
        rfl
      rw [hL, hR] at h
      apply (cancel_mono eQ.hom).1
      simpa [eP, eQ, pullbackFiberInduced,
        fiberToPullback, productPullbackFstIso, Category.assoc] using
        (congrArg (fun k => eP.symm.hom ≫ k) h).symm
    · let eP := productPullbackSndIso hF.comp_eq hG.comp_eq P f hsnd
      let eQ := productPullbackSndIso hF.comp_eq hG.comp_eq Q f hsnd
      change ((pullbackFiberInduced hF hG f).map
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U).map φ)).snd ≫
          eQ.symm.hom =
        eP.symm.hom ≫
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V).map
            (((Functor.chosenPullbacks
              (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor f).map φ)).snd
      have h := mapPullbackFiberIso_naturality hsnd φ f
      have hL :
          (Functor.fiberMap
            (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
            (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G)
            TwoFibreProductOver.snd_comp_eq U).map φ =
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq U).map φ).snd := by
        apply Subtype.ext
        rfl
      have hR :
          (Functor.fiberMap
            (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G) pℬ
            (TwoFibreProductOver.snd p𝒜 pℬ p𝒟 F G)
            TwoFibreProductOver.snd_comp_eq V).map (Functor.pullbackFiberHom φ f) =
          ((fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V).map
            (((Functor.chosenPullbacks
                (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor
              f).map φ)).snd := by
        apply Subtype.ext
        rfl
      rw [hL, hR] at h
      apply (cancel_mono eQ.hom).1
      simpa [eP, eQ, pullbackFiberInduced,
        fiberToPullback, productPullbackSndIso, Category.assoc] using
        (congrArg (fun k => eP.symm.hom ≫ k) h).symm

private noncomputable def fiberSquareTargetMap
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F)
    {X V W : 𝒞} (f : X ⟶ V) (g : X ⟶ W) :
    Limits.CategoricalPullback
        ((Functor.chosenPullbacks p).pullbackFunctor f)
        ((Functor.chosenPullbacks p).pullbackFunctor g) ⥤
      Limits.CategoricalPullback
        ((Functor.chosenPullbacks q).pullbackFunctor f)
        ((Functor.chosenPullbacks q).pullbackFunctor g) := by
  let α := (pullbackMapIso hF g).symm
  let β := pullbackMapIso hF f
  exact (Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    ((Functor.chosenPullbacks q).pullbackFunctor f)
    ((Functor.chosenPullbacks q).pullbackFunctor g)
    (Limits.CategoricalPullback
      ((Functor.chosenPullbacks p).pullbackFunctor f)
      ((Functor.chosenPullbacks p).pullbackFunctor g))).obj
    { fst := Limits.CategoricalPullback.π₁ _ _ ⋙
        Functor.fiberMap p q F hF.comp_eq V
      snd := Limits.CategoricalPullback.π₂ _ _ ⋙
        Functor.fiberMap p q F hF.comp_eq W
      iso :=
        Functor.isoWhiskerLeft (Limits.CategoricalPullback.π₁ _ _) β.symm ≪≫
          Functor.isoWhiskerRight
            (CatCommSq.iso
              (Limits.CategoricalPullback.π₁
                ((Functor.chosenPullbacks p).pullbackFunctor f)
                ((Functor.chosenPullbacks p).pullbackFunctor g))
              (Limits.CategoricalPullback.π₂
                ((Functor.chosenPullbacks p).pullbackFunctor f)
                ((Functor.chosenPullbacks p).pullbackFunctor g))
              ((Functor.chosenPullbacks p).pullbackFunctor f)
              ((Functor.chosenPullbacks p).pullbackFunctor g))
            (Functor.fiberMap p q F hF.comp_eq X) ≪≫
          (Functor.isoWhiskerLeft (Limits.CategoricalPullback.π₂ _ _) α).symm }

attribute [local implicit_reducible] fiberSquareTargetMap

private lemma squareComparison_iso_fac
    {C : Type u} [Category.{v₁} C] {A : Type u₁} [Category.{v₂} A]
    (p : A ⥤ C) (c : p.ChoiceOfPullbacks)
    {X V W Z : C} (f : X ⟶ V) (g : X ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (a : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison p c f g i j h).obj a).iso.hom ≫
      c.map g (c.obj j a) ≫ c.map j a = c.map f (c.obj i a) ≫ c.map i a := by
  have hinv : Functor.Fiber.fiberInclusion.map (c.objCompIso f i a).inv ≫
      c.map (f ≫ i) a = c.map f (c.obj i a) ≫ c.map i a :=
    Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _
  have heq : Functor.Fiber.fiberInclusion.map
      ((eqToIso (congrArg c.pullbackFunctor h)).hom.app a) ≫
        c.map (g ≫ j) a = c.map (f ≫ i) a := by
    generalize f ≫ i = k at h ⊢
    generalize g ≫ j = l at h ⊢
    subst l
    simp
  change Functor.Fiber.fiberInclusion.map
    ((c.objCompIso f i a).inv ≫
      (eqToIso (congrArg c.pullbackFunctor h)).hom.app a ≫
      (c.objCompIso g j a).hom) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc, Functor.ChoiceOfPullbacks.objCompIso_hom_fac]
  rw [heq, hinv]

private noncomputable def fiberSquareComparison_map
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {p : 𝒜 ⥤ 𝒞} {q : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ}
    [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F)
    {X V W Z : 𝒞} (f : X ⟶ V) (g : X ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    Deformation.Artin.fiberSquareComparison p (Functor.chosenPullbacks p) f g i j h ⋙
        fiberSquareTargetMap hF f g ≅
      Functor.fiberMap p q F hF.comp_eq Z ⋙
        Deformation.Artin.fiberSquareComparison q (Functor.chosenPullbacks q) f g i j h := by
  refine NatIso.ofComponents (fun a => ?_) ?_
  · let P := (Deformation.Artin.fiberSquareComparison p (Functor.chosenPullbacks p)
      f g i j h ⋙ fiberSquareTargetMap hF f g).obj a
    let Q := (Functor.fiberMap p q F hF.comp_eq Z ⋙
      Deformation.Artin.fiberSquareComparison q (Functor.chosenPullbacks q)
        f g i j h).obj a
    let e₁ : P.fst ≅ Q.fst := by
      simpa [P, Q, Deformation.Artin.fiberSquareComparison, fiberSquareTargetMap,
        Functor.ChoiceOfPullbacks.pullbackFunctor, Functor.chosenPullbacks_obj] using
        mapPullbackFiberIso hF a i
    let e₂ : P.snd ≅ Q.snd := by
      simpa [P, Q, Deformation.Artin.fiberSquareComparison, fiberSquareTargetMap,
        Functor.ChoiceOfPullbacks.pullbackFunctor, Functor.chosenPullbacks_obj] using
        mapPullbackFiberIso hF a j
    have hw : ((Functor.chosenPullbacks q).pullbackFunctor f).map e₁.hom ≫
          Q.iso.hom = P.iso.hom ≫
            ((Functor.chosenPullbacks q).pullbackFunctor g).map e₂.hom := by
      let cp := Functor.chosenPullbacks p
      let cq := Functor.chosenPullbacks q
      let b := (Functor.fiberMap p q F hF.comp_eq Z).obj a
      apply Functor.fiber_hom_ext_of_cartesian (g ≫ j)
        (cq.map g (cq.obj j b) ≫ cq.map j b) inferInstance
      simp only [Functor.map_comp, Category.assoc]
      change Functor.Fiber.fiberInclusion.map (cq.homMap f e₁.hom) ≫
          Functor.Fiber.fiberInclusion.map Q.iso.hom ≫
          cq.map g (cq.obj j b) ≫ cq.map j b =
        Functor.Fiber.fiberInclusion.map P.iso.hom ≫
          Functor.Fiber.fiberInclusion.map (cq.homMap g e₂.hom) ≫
          cq.map g Q.snd ≫ cq.map j b
      have hQ : Functor.Fiber.fiberInclusion.map Q.iso.hom ≫
          cq.map g (cq.obj j b) ≫ cq.map j b = cq.map f Q.fst ≫ cq.map i b :=
        squareComparison_iso_fac q cq f g i j h b
      rw [hQ]
      rw [cq.homMap_fac_assoc, cq.homMap_fac_assoc]
      change cq.map f _ ≫
          Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a i).hom ≫
          cq.map i b =
        Functor.Fiber.fiberInclusion.map
          ((mapPullbackFiberIso hF (cp.obj i a) f).inv ≫
            (Functor.fiberMap p q F hF.comp_eq X).map
              ((Deformation.Artin.fiberSquareComparison p cp f g i j h).obj a).iso.hom ≫
            (mapPullbackFiberIso hF (cp.obj j a) g).hom) ≫
          cq.map g _ ≫
          Functor.Fiber.fiberInclusion.map (mapPullbackFiberIso hF a j).hom ≫
          cq.map j b
      simp only [cp, cq, b, Functor.map_comp, Category.assoc]
      rw [mapPullbackFiberIso_hom_fac_chosen, mapPullbackFiberIso_hom_fac_chosen,
        mapPullbackFiberIso_hom_fac_chosen_assoc, fiberInclusion_map_fiberMap_map hF,
        ← F.map_comp, ← F.map_comp, squareComparison_iso_fac,
        F.map_comp, mapPullbackFiberIso_inv_fac_chosen_assoc]
      rfl
    exact Limits.CategoricalPullback.mkIso e₁ e₂ hw
  · intro a b φ
    exact CategoricalPullback.Hom.ext (mapPullbackFiberIso_naturality hF φ i)
      (mapPullbackFiberIso_naturality hF φ j)

private noncomputable def fiberSquareProductInduced
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒳 : Type u₁} [Category.{v₂} 𝒳]
    {𝒴 : Type u₂} [Category.{v₃} 𝒴]
    {𝒵 : Type u₃} [Category.{v₄} 𝒵]
    {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞}
    {F : 𝒳 ⥤ 𝒴} {G : 𝒵 ⥤ 𝒴}
    [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒴 F)
    (hG : Functor.IsFibredOneMorphism p𝒵 p𝒴 G)
    {X V W Z : 𝒞} (f : X ⟶ V) (g : X ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    CategoricalPullback
        (Functor.fiberMap p𝒳 p𝒴 F hF.comp_eq Z)
        (Functor.fiberMap p𝒵 p𝒴 G hG.comp_eq Z) ⥤
    CategoricalPullback
        (fiberSquareTargetMap hF f g)
        (fiberSquareTargetMap hG f g) := by
  let hx := Deformation.Artin.fiberSquareComparison p𝒳 (Functor.chosenPullbacks p𝒳) f g i j h
  let hy := Deformation.Artin.fiberSquareComparison p𝒴 (Functor.chosenPullbacks p𝒴) f g i j h
  let hz := Deformation.Artin.fiberSquareComparison p𝒵 (Functor.chosenPullbacks p𝒵) f g i j h
  let α := fiberSquareComparison_map hG f g i j h
  let β := (fiberSquareComparison_map hF f g i j h).symm
  exact CategoricalPullback.map _ _ hx hz hy _ _ α β

private theorem fiberSquareProductInduced_isEquivalence
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒳 : Type u₁} [Category.{v₂} 𝒳]
    {𝒴 : Type u₂} [Category.{v₃} 𝒴]
    {𝒵 : Type u₃} [Category.{v₄} 𝒵]
    {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞}
    {F : 𝒳 ⥤ 𝒴} {G : 𝒵 ⥤ 𝒴}
    [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒵.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒴 F)
    (hG : Functor.IsFibredOneMorphism p𝒵 p𝒴 G)
    {X V W Z : 𝒞} (f : X ⟶ V) (g : X ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hx : (Deformation.Artin.fiberSquareComparison p𝒳 (Functor.chosenPullbacks p𝒳)
      f g i j h).IsEquivalence)
    (hy : (Deformation.Artin.fiberSquareComparison p𝒴 (Functor.chosenPullbacks p𝒴)
      f g i j h).IsEquivalence)
    (hz : (Deformation.Artin.fiberSquareComparison p𝒵 (Functor.chosenPullbacks p𝒵)
      f g i j h).IsEquivalence) :
    (fiberSquareProductInduced hF hG f g i j h).IsEquivalence := by
  let : (Deformation.Artin.fiberSquareComparison p𝒳
      (Functor.chosenPullbacks p𝒳) f g i j h).IsEquivalence := hx
  let : (Deformation.Artin.fiberSquareComparison p𝒵
      (Functor.chosenPullbacks p𝒵) f g i j h).IsEquivalence := hz
  let : (Deformation.Artin.fiberSquareComparison p𝒴
      (Functor.chosenPullbacks p𝒴) f g i j h).IsEquivalence := hy
  exact CategoryTheory.induced_isEquivalence_of_isEquivalence
    (Deformation.Artin.fiberSquareComparison p𝒳 (Functor.chosenPullbacks p𝒳) f g i j h)
    (Deformation.Artin.fiberSquareComparison p𝒵 (Functor.chosenPullbacks p𝒵) f g i j h)
    (Deformation.Artin.fiberSquareComparison p𝒴 (Functor.chosenPullbacks p𝒴) f g i j h)
    (fiberSquareComparison_map hG f g i j h)
    (fiberSquareComparison_map hF f g i j h).symm

private noncomputable def productPullbackTargetMap
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ 𝒟} {G : ℬ ⥤ 𝒟}
    (hF : Functor.IsFibredOneMorphism p𝒜 p𝒟 F)
    (hG : Functor.IsFibredOneMorphism pℬ p𝒟 G)
    [p𝒜.IsFibered] [pℬ.IsFibered] [p𝒟.IsFibered]
    [(TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsFibered]
    {X V W : 𝒞} (f : X ⟶ V) (g : X ⟶ W) :
    Limits.CategoricalPullback
        ((Functor.chosenPullbacks
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor f)
        ((Functor.chosenPullbacks
          (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)).pullbackFunctor g) ⥤
      CategoricalPullback (pullbackFiberInduced hF hG f)
        (pullbackFiberInduced hF hG g) := by
  let hfst := TwoFibreProductOver.fst_isFibredOneMorphism p𝒜 pℬ p𝒟 F G hF hG
  let hsnd := TwoFibreProductOver.snd_isFibredOneMorphism p𝒜 pℬ p𝒟 F G hF hG
  exact CategoricalPullback.map _ _
      (fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq V)
      (fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq W)
      (fiberToPullback p𝒜 pℬ p𝒟 F G hF.comp_eq hG.comp_eq X) _ _
      (pullbackFiberToPullbackIso hF hG hfst hsnd (U := W) (V := X) g)
      (pullbackFiberToPullbackIso hF hG hfst hsnd (U := V) (V := X) f).symm

/-- A morphism lying over the identity lies over `eqToHom hP ≫ eqToHom hQ.symm`. -/
private lemma isHomLift_eqToHom_comp_eqToHom_symm {C : Type*} [Category* C] {A : Type*}
    [Category* A] (p : A ⥤ C) {B B' U : C} (hP : B = U) (hQ : B' = U) {x y : A} (a : x ⟶ y)
    [p.IsHomLift (𝟙 U) a] : p.IsHomLift (eqToHom hP ≫ eqToHom hQ.symm) a := by
  subst hP hQ
  simpa

private theorem fiberToPullback_isEquivalence
    {𝒞 : Type u} [Category.{v₁} 𝒞]
    {𝒜 : Type u₁} [Category.{v₂} 𝒜]
    {ℬ : Type u₂} [Category.{v₃} ℬ]
    {𝒟 : Type u₃} [Category.{v₄} 𝒟]
    (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (p𝒟 : 𝒟 ⥤ 𝒞)
    (F : 𝒜 ⥤ 𝒟) (G : ℬ ⥤ 𝒟)
    (hF : F ⋙ p𝒟 = p𝒜) (hG : G ⋙ p𝒟 = pℬ) (U : 𝒞) :
    (fiberToPullback p𝒜 pℬ p𝒟 F G hF hG U).IsEquivalence := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun {P Q} φ ψ h => ?_⟩
    apply Functor.Fiber.hom_ext
    apply TwoFibreProductOver.Hom.ext'
    · simpa [fiberToPullback, productFiberFst, Functor.Fiber.fiberInclusion] using
          congrArg (fun m => Functor.Fiber.fiberInclusion.map m.fst) h
    · simpa [fiberToPullback, productFiberSnd, Functor.Fiber.fiberInclusion] using
          congrArg (fun m => Functor.Fiber.fiberInclusion.map m.snd) h
  · refine ⟨fun {P Q} m => ?_⟩
    have hP : P.1.base = U := P.2
    have hQ : Q.1.base = U := Q.2
    let a : P.1.x ⟶ Q.1.x := m.fst.1
    let b : P.1.y ⟶ Q.1.y := m.snd.1
    have ha : p𝒜.IsHomLift (eqToHom hP ≫ eqToHom hQ.symm) a :=
      have : p𝒜.IsHomLift (𝟙 U) a := m.fst.2
      isHomLift_eqToHom_comp_eqToHom_symm p𝒜 hP hQ a
    have hb : pℬ.IsHomLift (eqToHom hP ≫ eqToHom hQ.symm) b :=
      have : pℬ.IsHomLift (𝟙 U) b := m.snd.2
      isHomLift_eqToHom_comp_eqToHom_symm pℬ hP hQ b
    let ψ : P.1 ⟶ Q.1 :=
      { hbase := eqToHom hP ≫ eqToHom hQ.symm
        a := a
        b := b
        ha := ha
        hb := hb
        w := by
          have hm := congrArg Functor.Fiber.fiberInclusion.map m.w
          dsimp only [fiberToPullback] at hm
          rw [Functor.map_comp, Functor.map_comp] at hm
          rw [fiberInclusion_map_productFiberGluingIso_hom
              p𝒜 pℬ p𝒟 F G hF hG P,
            fiberInclusion_map_productFiberGluingIso_hom
              p𝒜 pℬ p𝒟 F G hF hG Q] at hm
          simpa only [Functor.fiberMap_map_coe, Functor.fiberMap_obj_coe,
            Functor.Fiber.fiberInclusion, a, b] using hm }
    have hψ : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).IsHomLift (𝟙 U) ψ := by
      refine IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G)
        (𝟙 U) ψ P.2 Q.2 ?_
      change eqToHom hP ≫ eqToHom hQ.symm =
        eqToHom P.2 ≫ 𝟙 U ≫ eqToHom Q.2.symm
      have hp : hP = P.2 := Subsingleton.elim _ _
      have hq : hQ = Q.2 := Subsingleton.elim _ _
      rw [hp, hq]
      rw [Category.id_comp]
    refine ⟨⟨ψ, hψ⟩, ?_⟩
    apply CategoricalPullback.Hom.ext <;> apply Subtype.ext <;> rfl
  · refine ⟨fun T => ?_⟩
    let R : TwoFibreProductOver p𝒜 pℬ p𝒟 F G :=
      { base := U
        x := T.fst.1
        y := T.snd.1
        hx := T.fst.2
        hy := T.snd.2
        iso :=
          { hom := T.iso.hom.1
            inv := T.iso.inv.1
            hom_inv_id := congrArg Subtype.val T.iso.hom_inv_id
            inv_hom_id := congrArg Subtype.val T.iso.inv_hom_id }
        vertical := T.iso.hom.2 }
    let R' : (TwoFibreProductOver.structureFunctor p𝒜 pℬ p𝒟 F G).Fiber U := ⟨R, rfl⟩
    refine ⟨R', ?_⟩
    apply Nonempty.intro
    have he : (fiberToPullback p𝒜 pℬ p𝒟 F G hF hG U).obj R' = T := by
      cases T
      rfl
    exact eqToIso he

section Interchange

variable {A₀ : Type*} [Category* A₀] {A₁ : Type*} [Category* A₁]
  {A₂ : Type*} [Category* A₂] {B₀ : Type*} [Category* B₀]
  {B₁ : Type*} [Category* B₁] {B₂ : Type*} [Category* B₂]
  {C₀ : Type*} [Category* C₀] {C₁ : Type*} [Category* C₁]
  {C₂ : Type*} [Category* C₂]

private def spanMap
    {a : A₀ ⥤ A₂} {d : A₁ ⥤ A₂} {c : C₀ ⥤ C₂} {f : C₁ ⥤ C₂}
    (F₀ : A₀ ⥤ C₀) (F₁ : A₁ ⥤ C₁) (F₂ : A₂ ⥤ C₂)
    (β₀ : F₀ ⋙ c ≅ a ⋙ F₂) (β₁ : F₁ ⋙ f ≅ d ⋙ F₂) :
    Limits.CategoricalPullback a d ⥤ Limits.CategoricalPullback c f where
  obj T := ⟨F₀.obj T.fst, F₁.obj T.snd,
    β₀.app T.fst ≪≫ F₂.mapIso T.iso ≪≫ (β₁.app T.snd).symm⟩
  map m := ⟨F₀.map m.fst, F₁.map m.snd, by
    have h₀ := β₀.hom.naturality m.fst
    have h₁ := β₁.inv.naturality m.snd
    dsimp at h₀ h₁ ⊢
    simp only [Category.assoc]
    rw [reassoc_of% h₀, ← F₂.map_comp_assoc, m.w, F₂.map_comp_assoc, h₁]⟩

private def pullbackIso
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] {F : A ⥤ C} {G : B ⥤ C}
    {P Q : CategoricalPullback F G}
    (a : P.fst ≅ Q.fst) (b : P.snd ≅ Q.snd)
    (h : F.map a.hom ≫ Q.iso.hom = P.iso.hom ≫ G.map b.hom) : P ≅ Q where
  hom := ⟨a.hom, b.hom, h⟩
  inv := ⟨a.inv, b.inv, by
    have hh := congrArg (fun m => F.map a.inv ≫ m ≫ G.map b.inv) h
    simpa [Category.assoc] using hh.symm⟩
  hom_inv_id := by apply CategoricalPullback.Hom.ext <;> simp
  inv_hom_id := by apply CategoricalPullback.Hom.ext <;> simp


attribute [local implicit_reducible] spanMap

private def pullbackFstIso
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] {F : A ⥤ C} {G : B ⥤ C}
    {P Q : CategoricalPullback F G} (e : P ≅ Q) : P.fst ≅ Q.fst where
  hom := e.hom.fst
  inv := e.inv.fst
  hom_inv_id := congrArg CategoricalPullback.Hom.fst e.hom_inv_id
  inv_hom_id := congrArg CategoricalPullback.Hom.fst e.inv_hom_id

private def pullbackSndIso
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] {F : A ⥤ C} {G : B ⥤ C}
    {P Q : CategoricalPullback F G} (e : P ≅ Q) : P.snd ≅ Q.snd where
  hom := e.hom.snd
  inv := e.inv.snd
  hom_inv_id := congrArg CategoricalPullback.Hom.snd e.hom_inv_id
  inv_hom_id := congrArg CategoricalPullback.Hom.snd e.inv_hom_id

variable {a : A₀ ⥤ A₂} {b : B₀ ⥤ B₂} {c : C₀ ⥤ C₂}
  {d : A₁ ⥤ A₂} {e : B₁ ⥤ B₂} {f : C₁ ⥤ C₂}
  {F₀ : A₀ ⥤ C₀} {F₁ : A₁ ⥤ C₁} {F₂ : A₂ ⥤ C₂}
  {G₀ : B₀ ⥤ C₀} {G₁ : B₁ ⥤ C₁} {G₂ : B₂ ⥤ C₂}
  (α₀ : b ⋙ G₂ ≅ G₀ ⋙ c) (β₀ : F₀ ⋙ c ≅ a ⋙ F₂)
  (α₁ : e ⋙ G₂ ≅ G₁ ⋙ f) (β₁ : F₁ ⋙ f ≅ d ⋙ F₂)

private def pullbackInterchange :
    CategoricalPullback (CategoricalPullback.map _ _ a b c _ _ α₀ β₀)
      (CategoricalPullback.map _ _ d e f _ _ α₁ β₁) ⥤
    CategoricalPullback (spanMap F₀ F₁ F₂ β₀ β₁)
      (spanMap G₀ G₁ G₂ α₀.symm α₁.symm) where
  obj T :=
    { fst := ⟨T.fst.fst, T.snd.fst, pullbackFstIso T.iso⟩
      snd := ⟨T.fst.snd, T.snd.snd, pullbackSndIso T.iso⟩
      iso := Limits.CategoricalPullback.mkIso T.fst.iso T.snd.iso (by
        have h := T.iso.hom.w
        dsimp [spanMap, pullbackFstIso, pullbackSndIso] at h ⊢
        have hh := congrArg (fun k => β₀.hom.app T.fst.fst ≫ k ≫
          α₁.hom.app T.snd.snd) h
        simpa [Category.assoc, Functor.mapIso, Limits.CategoricalPullback.π₁,
          Limits.CategoricalPullback.π₂] using hh.symm) }
  map {T U} m :=
    { fst := ⟨m.fst.fst, m.snd.fst, congrArg CategoricalPullback.Hom.fst m.w⟩
      snd := ⟨m.fst.snd, m.snd.snd, congrArg CategoricalPullback.Hom.snd m.w⟩
      w := by
        exact CategoricalPullback.Hom.ext m.fst.w m.snd.w }
  map_id _ := by
    apply CategoricalPullback.Hom.ext <;> apply Limits.CategoricalPullback.Hom.ext <;> rfl
  map_comp _ _ := by
    apply CategoricalPullback.Hom.ext <;> apply Limits.CategoricalPullback.Hom.ext <;> rfl

private def pullbackInterchangeInverse :
    CategoricalPullback (spanMap F₀ F₁ F₂ β₀ β₁)
      (spanMap G₀ G₁ G₂ α₀.symm α₁.symm) ⥤
    CategoricalPullback (CategoricalPullback.map _ _ a b c _ _ α₀ β₀)
      (CategoricalPullback.map _ _ d e f _ _ α₁ β₁) where
  obj T :=
    { fst := ⟨T.fst.fst, T.snd.fst, (Limits.CategoricalPullback.π₁ _ _).mapIso T.iso⟩
      snd := ⟨T.fst.snd, T.snd.snd, (Limits.CategoricalPullback.π₂ _ _).mapIso T.iso⟩
      iso := CategoricalPullback.mkIso T.fst.iso T.snd.iso (by
        have h := T.iso.hom.w
        dsimp [spanMap, pullbackFstIso, pullbackSndIso] at h ⊢
        have hh := congrArg (fun k => β₀.inv.app T.fst.fst ≫ k ≫
          α₁.inv.app T.snd.snd) h
        simpa [Category.assoc, Functor.mapIso, Limits.CategoricalPullback.π₁,
          Limits.CategoricalPullback.π₂] using hh.symm) }
  map {T U} m :=
    { fst := ⟨m.fst.fst, m.snd.fst, congrArg Limits.CategoricalPullback.Hom.fst m.w⟩
      snd := ⟨m.fst.snd, m.snd.snd, congrArg Limits.CategoricalPullback.Hom.snd m.w⟩
      w := by
        exact CategoricalPullback.Hom.ext m.fst.w m.snd.w }
  map_id _ := by
    apply CategoricalPullback.Hom.ext <;> apply CategoricalPullback.Hom.ext <;> rfl
  map_comp _ _ := by
    apply CategoricalPullback.Hom.ext <;> apply CategoricalPullback.Hom.ext <;> rfl

private theorem pullbackInterchange_isEquivalence :
    (pullbackInterchange α₀ β₀ α₁ β₁).IsEquivalence := by
  let E : _ ≌ _ :=
    { functor := pullbackInterchange α₀ β₀ α₁ β₁
      inverse := pullbackInterchangeInverse α₀ β₀ α₁ β₁
      unitIso := NatIso.ofComponents (fun T => eqToIso (by rfl)) (by
        intro T U m
        change m ≫ 𝟙 _ = 𝟙 _ ≫ m
        simp only [Category.id_comp, Category.comp_id])
      counitIso := NatIso.ofComponents (fun T => eqToIso (by rfl)) (by
        intro T U m
        change m ≫ 𝟙 _ = 𝟙 _ ≫ m
        simp only [Category.id_comp, Category.comp_id])
      functor_unitIso_comp := by
        intro T
        change (pullbackInterchange α₀ β₀ α₁ β₁).map (𝟙 T) ≫ 𝟙 _ = 𝟙 _
        rw [CategoryTheory.Functor.map_id, Category.id_comp] }
  exact E.isEquivalence_functor

end Interchange

section ProductComparison

variable {C : Type*} [Category* C] {A : Type*} [Category* A]
  {B : Type*} [Category* B] {D : Type*} [Category* D]
  {pA : A ⥤ C} {pB : B ⥤ C} {pD : D ⥤ C}
  {F : A ⥤ D} {G : B ⥤ D}
  [pA.IsFibered] [pB.IsFibered] [pD.IsFibered]
  [(TwoFibreProductOver.structureFunctor pA pB pD F G).IsFibered]
  (hF : Functor.IsFibredOneMorphism pA pD F)
  (hG : Functor.IsFibredOneMorphism pB pD G)
  {X V W Z : C} (f : X ⟶ V) (g : X ⟶ W)
  (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)

private noncomputable def productSquareTarget :
    Limits.CategoricalPullback
      ((Functor.chosenPullbacks
        (TwoFibreProductOver.structureFunctor pA pB pD F G)).pullbackFunctor f)
      ((Functor.chosenPullbacks
        (TwoFibreProductOver.structureFunctor pA pB pD F G)).pullbackFunctor g) ⥤
    CategoricalPullback (fiberSquareTargetMap hF f g) (fiberSquareTargetMap hG f g) :=
  productPullbackTargetMap hF hG f g ⋙
    pullbackInterchange (pullbackMapIso hG f) (pullbackMapIso hF f).symm
      (pullbackMapIso hG g) (pullbackMapIso hF g).symm

private theorem productSquareTarget_isEquivalence :
    (productSquareTarget hF hG f g).IsEquivalence := by
  let := fiberToPullback_isEquivalence pA pB pD F G hF.comp_eq hG.comp_eq V
  let := fiberToPullback_isEquivalence pA pB pD F G hF.comp_eq hG.comp_eq W
  let := fiberToPullback_isEquivalence pA pB pD F G hF.comp_eq hG.comp_eq X
  have : (productPullbackTargetMap hF hG f g).IsEquivalence := by
    dsimp only [productPullbackTargetMap]
    have := CategoryTheory.induced_isEquivalence_of_isEquivalence
      (fiberToPullback pA pB pD F G hF.comp_eq hG.comp_eq V)
      (fiberToPullback pA pB pD F G hF.comp_eq hG.comp_eq W)
      (fiberToPullback pA pB pD F G hF.comp_eq hG.comp_eq X)
      (pullbackFiberToPullbackIso hF hG
        (TwoFibreProductOver.fst_isFibredOneMorphism pA pB pD F G hF hG)
        (TwoFibreProductOver.snd_isFibredOneMorphism pA pB pD F G hF hG) g)
      (pullbackFiberToPullbackIso hF hG
        (TwoFibreProductOver.fst_isFibredOneMorphism pA pB pD F G hF hG)
        (TwoFibreProductOver.snd_isFibredOneMorphism pA pB pD F G hF hG) f).symm
    infer_instance
  dsimp only [productSquareTarget]
  refine @CategoryTheory.Functor.isEquivalence_trans _ _ _ _ _ _ _ _ ?_ ?_
  · exact ‹(productPullbackTargetMap hF hG f g).IsEquivalence›
  · exact pullbackInterchange_isEquivalence
      (pullbackMapIso hG f) (pullbackMapIso hF f).symm
      (pullbackMapIso hG g) (pullbackMapIso hF g).symm

private noncomputable def productSquareComparisonIso :
    Deformation.Artin.fiberSquareComparison (TwoFibreProductOver.structureFunctor pA pB pD F G)
        (Functor.chosenPullbacks _) f g i j h ⋙ productSquareTarget hF hG f g ≅
      fiberToPullback pA pB pD F G hF.comp_eq hG.comp_eq Z ⋙
        fiberSquareProductInduced hF hG f g i j h := by
  let hfst := TwoFibreProductOver.fst_isFibredOneMorphism pA pB pD F G hF hG
  let hsnd := TwoFibreProductOver.snd_isFibredOneMorphism pA pB pD F G hF hG
  refine NatIso.ofComponents (fun P => ?_) ?_
  · refine CategoricalPullback.mkIso ((fiberSquareComparison_map hfst f g i j h).app P)
      ((fiberSquareComparison_map hsnd f g i j h).app P) ?_
    exact CategoricalPullback.Hom.ext ((pullbackFiberToPullbackIso hF hG hfst hsnd i).inv.app P).w
      ((pullbackFiberToPullbackIso hF hG hfst hsnd j).inv.app P).w
  · intro P Q m
    exact CategoricalPullback.Hom.ext
      ((fiberSquareComparison_map hfst f g i j h).hom.naturality m)
      ((fiberSquareComparison_map hsnd f g i j h).hom.naturality m)

include hF hG in
private theorem productSquareComparison_isEquivalence
    (hA : (Deformation.Artin.fiberSquareComparison pA (Functor.chosenPullbacks pA)
      f g i j h).IsEquivalence)
    (hD : (Deformation.Artin.fiberSquareComparison pD (Functor.chosenPullbacks pD)
      f g i j h).IsEquivalence)
    (hB : (Deformation.Artin.fiberSquareComparison pB (Functor.chosenPullbacks pB)
      f g i j h).IsEquivalence) :
    (Deformation.Artin.fiberSquareComparison (TwoFibreProductOver.structureFunctor pA pB pD F G)
      (Functor.chosenPullbacks _) f g i j h).IsEquivalence := by
  let := fiberToPullback_isEquivalence pA pB pD F G hF.comp_eq hG.comp_eq Z
  let := fiberSquareProductInduced_isEquivalence hF hG f g i j h hA hD hB
  let := productSquareTarget_isEquivalence hF hG f g
  have := Functor.isEquivalence_of_iso (productSquareComparisonIso hF hG f g i j h).symm
  exact Functor.isEquivalence_of_comp_right _ (productSquareTarget hF hG f g)

end ProductComparison

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : Type u₁} [Category.{v₁} 𝒳]
variable {𝒴 : Type u₂} [Category.{v₂} 𝒴]
variable {𝒵 : Type u₃} [Category.{v₃} 𝒵]

/-- Condition (RS) is preserved by the two-fibre product of categories fibred in groupoids over
the big fppf site. -/
@[stacks 07WR]
public theorem satisfiesRS_twoFibreProductOver
    (p𝒳 : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (p𝒴 : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (p𝒵 : 𝒵 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴)
    (h𝒳 : p𝒳.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (hRS𝒳 : Deformation.Artin.SatisfiesRS B S hS p𝒳 h𝒳)
    (hRS𝒴 : Deformation.Artin.SatisfiesRS B S hS p𝒴 h𝒴)
    (hRS𝒵 : Deformation.Artin.SatisfiesRS B S hS p𝒵 h𝒵) :
    Deformation.Artin.SatisfiesRS B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G)
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G
        h𝒳 h𝒵 h𝒴 hF hG) := by
  let q := TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G
  let hq := TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G
    h𝒳 h𝒵 h𝒴 hF hG
  let : q.IsFibered := hq.isFibered
  let : p𝒳.IsFibered := h𝒳.isFibered
  let : p𝒴.IsFibered := h𝒴.isFibered
  let : p𝒵.IsFibered := h𝒵.isFibered
  dsimp only [Deformation.Artin.SatisfiesRS]
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hFTX hFTX' hFTY hFTY' hClosed hPush
  have hx := hRS𝒳 (i := i) (j := j) (i' := i') (j' := j') w hX hX' hY hY'
    hFTX hFTX' hFTY hFTY' hClosed hPush
  have hy := hRS𝒴 (i := i) (j := j) (i' := i') (j' := j') w hX hX' hY hY'
    hFTX hFTX' hFTY hFTY' hClosed hPush
  have hz := hRS𝒵 (i := i) (j := j) (i' := i') (j' := j') w hX hX' hY hY'
    hFTX hFTX' hFTY hFTY' hClosed hPush
  exact productSquareComparison_isEquivalence
    (h𝒴.isFibredOneMorphism hF)
    (h𝒴.isFibredOneMorphism hG)
    j i j' i' w.symm hx hy hz

/-- The two-fibre product of categories fibred in groupoids satisfying condition (RS*) again
satisfies (RS*). -/
@[stacks 0CXQ]
public theorem twoFibreProductOver_satisfiesRSStar
    {X : Type uX} [Category X]
    {Y : Type uY} [Category Y]
    {Z : Type uZ} [Category Z]
    (pX : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (pY : Y ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (pZ : Z ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (F : X ⥤ Y) (G : Z ⥤ Y)
    (hX : pX.IsFiberedInGroupoids) (hY : pY.IsFiberedInGroupoids)
    (hZ : pZ.IsFiberedInGroupoids)
    (hF : F ⋙ pY = pX) (hG : G ⋙ pY = pZ)
    (rsX : Deformation.Artin.SatisfiesRSStar B S hS pX hX)
    (rsY : Deformation.Artin.SatisfiesRSStar B S hS pY hY)
    (rsZ : Deformation.Artin.SatisfiesRSStar B S hS pZ hZ) :
    Deformation.Artin.SatisfiesRSStar B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY F G)
      (TwoFibreProductOver.isFiberedInGroupoids pX pZ pY F G
        hX hZ hY hF hG) := by
  intro U V W Z f g i j h hpull hsurj hker
  let ι := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let : pX.IsFibered := hX.isFibered
  let : pY.IsFibered := hY.isFibered
  let : pZ.IsFibered := hZ.isFibered
  let : (TwoFibreProductOver.structureFunctor pX pZ pY F G).IsFibered :=
    (TwoFibreProductOver.isFiberedInGroupoids pX pZ pY F G hX hZ hY hF hG).isFibered
  have hx := rsX U V W Z f g i j h hpull hsurj hker
  have hy := rsY U V W Z f g i j h hpull hsurj hker
  have hz := rsZ U V W Z f g i j h hpull hsurj hker
  exact productSquareComparison_isEquivalence
    (hY.isFibredOneMorphism hF)
    (hY.isFibredOneMorphism hG)
    (ι.map f) (ι.map g) (ι.map i) (ι.map j)
    (by simpa only [Functor.map_comp] using congrArg ι.map h) hx hy hz

end Deformation.Artin
