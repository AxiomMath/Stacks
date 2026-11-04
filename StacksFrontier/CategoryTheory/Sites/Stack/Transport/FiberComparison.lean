module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.PullbackComparison

/-!
# The fibrewise comparison, and its compatibilities

For an equivalence `e` of fibred categories over `𝒞`, this file reads
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso` in the fibre, as an
isomorphism `pullbackFiberFunctorFiberIso` between the image under the forward functor of a
chosen pullback and the chosen pullback of the image, and proves that it is natural in the object
and compatible with iterated chosen pullbacks.

## Main definitions

* `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso`, the comparison, in the
  fibre, of the image of a chosen pullback with the chosen pullback of the image.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso_naturality`: the
  comparison is natural in the object.
* `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso_comp`: the comparison is
  compatible with iterated chosen pullbacks.
-/

@[expose] public section

-- The declarations below relate `p` and `𝒴.p` through `BasedFunctor.comp`, whose instance
-- arguments are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

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

/-- `pullbackFiberFunctorIso` read in the fibre of `𝒴` over `V`: the isomorphism between the image
under `e.functor` of the chosen pullback of `x` along `f` and the chosen pullback of
`e.fiberMap x` along `f` taken in `𝒴`. -/
noncomputable def pullbackFiberFunctorFiberIso {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    (e.fiberMapFunctor V).obj (pullbackFiber 𝒳.p x f) ≅ pullbackFiber 𝒴.p (e.fiberMap x) f :=
  Fiber.isoMk (e.pullbackFiberFunctorIso x f) inferInstance

/-- The underlying morphism of `𝒴` of the forward direction of
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso` is the forward direction of
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso`. -/
@[simp]
lemma fiberInclusion_map_pullbackFiberFunctorFiberIso_hom {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Fiber.fiberInclusion.map (e.pullbackFiberFunctorFiberIso x f).hom =
      (e.pullbackFiberFunctorIso x f).hom := rfl

/-- The underlying morphism of `𝒴` of the inverse direction of
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso` is the inverse direction of
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorIso`. -/
@[simp]
lemma fiberInclusion_map_pullbackFiberFunctorFiberIso_inv {U : 𝒞} (x : 𝒳.p.Fiber U) {V : 𝒞}
    (f : V ⟶ U) :
    Fiber.fiberInclusion.map (e.pullbackFiberFunctorFiberIso x f).inv =
      (e.pullbackFiberFunctorIso x f).inv := rfl

/-- The fibrewise comparison is natural: the base change of a morphism of a fibre of `𝒳` agrees
with the base change of its image in `𝒴`. -/
@[reassoc]
lemma pullbackFiberFunctorFiberIso_naturality {U : 𝒞} {x y : 𝒳.p.Fiber U} (φ : x ⟶ y) {V : 𝒞}
    (f : V ⟶ U) :
    (e.fiberMapFunctor V).map (pullbackFiberHom φ f) ≫ (e.pullbackFiberFunctorFiberIso y f).hom =
      (e.pullbackFiberFunctorFiberIso x f).hom ≫
        pullbackFiberHom ((e.fiberMapFunctor U).map φ) f := by
  refine fiber_hom_ext_of_cartesian f (IsPreFibered.pullbackMap (e.fiberMap y).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberMapFunctor_map,
    fiberInclusion_map_pullbackFiberFunctorFiberIso_hom, pullbackFiberFunctorIso_hom_fac,
    pullbackFiberHom_fac, pullbackFiberFunctorIso_hom_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, pullbackFiberHom_fac]

/-- The fibrewise comparison is compatible with iterated chosen pullbacks: comparing the chosen
pullback of a chosen pullback and then contracting agrees with contracting in `𝒳` and then
comparing. -/
@[reassoc]
lemma pullbackFiberFunctorFiberIso_comp {U : 𝒞} (x : 𝒳.p.Fiber U) {V Z : 𝒞} (f : V ⟶ U)
    (γ : Z ⟶ V) :
    (e.fiberMapFunctor Z).map (pullbackFiberCompIso x f γ).hom ≫
        (e.pullbackFiberFunctorFiberIso x (γ ≫ f)).hom =
      (e.pullbackFiberFunctorFiberIso (pullbackFiber 𝒳.p x f) γ).hom ≫
        pullbackFiberHom (e.pullbackFiberFunctorFiberIso x f).hom γ ≫
        (pullbackFiberCompIso (e.fiberMap x) f γ).hom := by
  refine fiber_hom_ext_of_cartesian (γ ≫ f) (IsPreFibered.pullbackMap (e.fiberMap x).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberMapFunctor_map,
    fiberInclusion_map_pullbackFiberFunctorFiberIso_hom, pullbackFiberFunctorIso_hom_fac,
    pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc,
    pullbackFiberFunctorIso_hom_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, pullbackFiberCompIso_hom_fac]

/-- The compatibility of the fibrewise comparison with iterated chosen pullbacks, stated with the
two contractions inverted. -/
@[reassoc]
lemma pullbackFiberFunctorFiberIso_comp_inv {U : 𝒞} (x : 𝒳.p.Fiber U) {V Z : 𝒞} (f : V ⟶ U)
    (γ : Z ⟶ V) :
    (e.pullbackFiberFunctorFiberIso x (γ ≫ f)).inv ≫
        (e.fiberMapFunctor Z).map (pullbackFiberCompIso x f γ).inv ≫
        (e.pullbackFiberFunctorFiberIso (pullbackFiber 𝒳.p x f) γ).hom =
      (pullbackFiberCompIso (e.fiberMap x) f γ).inv ≫
        pullbackFiberHom (e.pullbackFiberFunctorFiberIso x f).inv γ := by
  have h := e.pullbackFiberFunctorFiberIso_comp x f γ
  rw [← cancel_epi (e.pullbackFiberFunctorFiberIso x (γ ≫ f)).hom, Iso.hom_inv_id_assoc,
    ← cancel_epi ((e.fiberMapFunctor Z).map (pullbackFiberCompIso x f γ).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp, reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, pullbackFiberHom_hom_inv_id]
  exact (Category.comp_id _).symm

end BasedCategory.Equivalence

end CategoryTheory
