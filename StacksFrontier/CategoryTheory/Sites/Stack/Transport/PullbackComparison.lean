module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.FiberMap

/-!
# Comparing the image of a chosen pullback with the chosen pullback of the image

Let `e : BasedCategory.Equivalence 𝒳 𝒴` be an equivalence of categories over `𝒞`, with both sides
fibred. The forward functor `F` of `e` carries strongly cartesian morphisms to strongly cartesian
morphisms (`BasedCategory.Equivalence.isStronglyCartesian_map`), so the image under `F` of the
chosen pullback of `x` along `g` is again a cartesian lift of `g`, hence canonically isomorphic
to the chosen pullback of `F x` along `g`. This file defines that comparison isomorphism and
proves its compatibilities with the chosen cartesian lifts and with the restriction maps.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso`, the comparison isomorphism.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso_hom_fac` and
  `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso_inv_fac`, compatibility with
  the two chosen cartesian lifts being compared.
* `CategoryTheory.BasedCategory.Equivalence.map_pullbackFiberMap`, the naturality of the
  comparison: conjugating by it turns the restriction map of the chosen pullbacks in `𝒳` into
  that of the chosen pullbacks in `𝒴`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

-- Every declaration below is a statement about `e`, but several mention it only in their proofs.
include e

variable [𝒳.p.IsFibered] [𝒴.p.IsFibered]

open _root_.CategoryTheory.Functor

/-- The canonical isomorphism between the image under `e.functor` of the chosen pullback of `x`
along `g`, taken in `𝒳`, and the chosen pullback of `e.fiberMap x` along `g`, taken in `𝒴`. -/
noncomputable def pullbackFiberFunctorIso {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (g : V ⟶ U) :
    e.functor.obj (pullbackFiber 𝒳.p x g).1 ≅ (pullbackFiber 𝒴.p (e.fiberMap x) g).1 :=
  haveI : 𝒴.p.IsStronglyCartesian g (e.functor.map (IsPreFibered.pullbackMap x.2 g)) :=
    e.isStronglyCartesian_map g _
  IsCartesian.domainUniqueUpToIso 𝒴.p g (IsPreFibered.pullbackMap (e.fiberMap x).2 g)
    (e.functor.map (IsPreFibered.pullbackMap x.2 g))

/-- The forward direction of `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso`
lies over the identity of `V`. -/
instance isHomLift_pullbackFiberFunctorIso_hom {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (g : V ⟶ U) :
    𝒴.p.IsHomLift (𝟙 V) (e.pullbackFiberFunctorIso x g).hom :=
  haveI : 𝒴.p.IsStronglyCartesian g (e.functor.map (IsPreFibered.pullbackMap x.2 g)) :=
    e.isStronglyCartesian_map g _
  IsCartesian.domainUniqueUpToIso_inv_isHomLift 𝒴.p g
    (IsPreFibered.pullbackMap (e.fiberMap x).2 g)
    (e.functor.map (IsPreFibered.pullbackMap x.2 g))

/-- The inverse direction of `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso`
lies over the identity of `V`. -/
instance isHomLift_pullbackFiberFunctorIso_inv {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (g : V ⟶ U) :
    𝒴.p.IsHomLift (𝟙 V) (e.pullbackFiberFunctorIso x g).inv :=
  haveI : 𝒴.p.IsStronglyCartesian g (e.functor.map (IsPreFibered.pullbackMap x.2 g)) :=
    e.isStronglyCartesian_map g _
  IsCartesian.domainUniqueUpToIso_hom_isHomLift 𝒴.p g
    (IsPreFibered.pullbackMap (e.fiberMap x).2 g)
    (e.functor.map (IsPreFibered.pullbackMap x.2 g))

/-- `pullbackFiberFunctorIso` is compatible with the two chosen cartesian lifts it compares. -/
@[reassoc]
lemma pullbackFiberFunctorIso_hom_fac {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (g : V ⟶ U) :
    (e.pullbackFiberFunctorIso x g).hom ≫ IsPreFibered.pullbackMap (e.fiberMap x).2 g =
      e.functor.map (IsPreFibered.pullbackMap x.2 g) :=
  have : 𝒴.p.IsStronglyCartesian g (e.functor.map (IsPreFibered.pullbackMap x.2 g)) :=
    e.isStronglyCartesian_map g _
  IsCartesian.fac 𝒴.p g (IsPreFibered.pullbackMap (e.fiberMap x).2 g)
    (e.functor.map (IsPreFibered.pullbackMap x.2 g))

/-- Naturality of `pullbackFiberFunctorIso`: conjugating by it turns the restriction map of the
chosen pullbacks of `x` in `𝒳` into the restriction map of the chosen pullbacks of
`e.fiberMap x` in `𝒴`. -/
lemma map_pullbackFiberMap {U : 𝒞} (x : 𝒳.p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    e.functor.map (pullbackFiberMap 𝒳.p x h) ≫ (e.pullbackFiberFunctorIso x g₂.hom).hom =
      (e.pullbackFiberFunctorIso x g₁.hom).hom ≫ pullbackFiberMap 𝒴.p (e.fiberMap x) h := by
  have key : ∀ {R S : 𝒞} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsHomLift (𝟙 R ≫ f ≫ 𝟙 S) φ → 𝒴.p.IsHomLift f φ := by simp
  have hl := key h.left (e.functor.map (pullbackFiberMap 𝒳.p x h) ≫
    (e.pullbackFiberFunctorIso x g₂.hom).hom) inferInstance
  have hr := key h.left ((e.pullbackFiberFunctorIso x g₁.hom).hom ≫
    pullbackFiberMap 𝒴.p (e.fiberMap x) h) inferInstance
  refine IsStronglyCartesian.ext 𝒴.p g₂.hom
    (IsPreFibered.pullbackMap (e.fiberMap x).2 g₂.hom) h.left ?_
  rw [Category.assoc, Category.assoc, pullbackFiberFunctorIso_hom_fac, pullbackFiberMap_fac,
    pullbackFiberFunctorIso_hom_fac, ← Functor.map_comp, pullbackFiberMap_fac]

/-- Naturality of the inverse of `pullbackFiberFunctorIso` with respect to the restriction maps of
the chosen pullbacks. -/
@[reassoc]
lemma pullbackFiberFunctorIso_inv_map_pullbackFiberMap {U : 𝒞} (x : 𝒳.p.Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (e.pullbackFiberFunctorIso x g₁.hom).inv ≫ e.functor.map (pullbackFiberMap 𝒳.p x h) =
      pullbackFiberMap 𝒴.p (e.fiberMap x) h ≫ (e.pullbackFiberFunctorIso x g₂.hom).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← e.map_pullbackFiberMap x h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The inverse of `pullbackFiberFunctorIso` is compatible with the two chosen cartesian lifts it
compares. -/
@[reassoc]
lemma pullbackFiberFunctorIso_inv_fac {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    (e.pullbackFiberFunctorIso x f).inv ≫ e.functor.map (IsPreFibered.pullbackMap x.2 f) =
      IsPreFibered.pullbackMap (e.fiberMap x).2 f := by
  rw [Iso.inv_comp_eq, pullbackFiberFunctorIso_hom_fac]

end BasedCategory.Equivalence

end CategoryTheory
