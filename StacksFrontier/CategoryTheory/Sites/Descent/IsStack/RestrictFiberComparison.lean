module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf

/-!
# The fibrewise comparison for a full subcategory

For the restriction of a fibred category `p` to a full subcategory closed under strongly cartesian
pullback, `CategoryTheory.Functor.pullbackFiberιFiberIso` compares, in the fibre of `p`, the image
of a chosen pullback taken in the subcategory with the chosen pullback taken in `𝒳`. It is natural
in the object and compatible with iterated chosen pullbacks.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberιFiberIso`: the fibrewise comparison.

## Main results

* `CategoryTheory.Functor.pullbackFiberιFiberIso_naturality`: naturality of the comparison.
* `CategoryTheory.Functor.pullbackFiberιFiberIso_comp`: compatibility with iterated chosen
  pullbacks.
-/

@[expose] public section

-- Needed throughout: the transfer lemmas below relate `p` and `P.ι ⋙ p`, and the instance
-- arguments of `IsHomLift` and `IsCartesian` are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
  (h1 : ClosedUnderStronglyCartesian p P)

variable {p P}

/-- The inverse form of `pullbackFiberιIso_hom_fac`. -/
@[reassoc]
lemma pullbackFiberιIso_inv_fac {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    (pullbackFiberιIso p P h1 x f).inv ≫ P.ι.map (IsPreFibered.pullbackMap x.2 f) =
      IsPreFibered.pullbackMap (fiberι p P x).2 f := by
  have := isFibered_restrict_of_closed p P h1
  rw [Iso.inv_comp_eq, pullbackFiberιIso_hom_fac]

/-- `CategoryTheory.Functor.pullbackFiberιIso` read in the fibre of `p` over `V`: the image under
`P.ι` of the chosen pullback of `x` along `f` inside the full subcategory, compared with the chosen
pullback of `ι x` along `f` taken in `𝒳`. -/
noncomputable def pullbackFiberιFiberIso {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮}
    (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    (fiberιFunctor p P V).obj (pullbackFiber (restrict p P) x f) ≅
      pullbackFiber p (fiberι p P x) f :=
  haveI := isFibered_restrict_of_closed p P h1
  Fiber.isoMk (pullbackFiberιIso p P h1 x f) (isHomLift_pullbackFiberιIso_hom h1 x f)

/-- The forward direction of the fibrewise comparison, seen in `𝒳`, is the forward direction of
`pullbackFiberιIso`. -/
@[simp]
lemma fiberInclusion_map_pullbackFiberιFiberIso_hom {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮}
    (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    Fiber.fiberInclusion.map (pullbackFiberιFiberIso h1 x f).hom =
      (pullbackFiberιIso p P h1 x f).hom := rfl

/-- The inverse of the fibrewise comparison, seen in `𝒳`, is the inverse of
`pullbackFiberιIso`. -/
@[simp]
lemma fiberInclusion_map_pullbackFiberιFiberIso_inv {U : 𝒮} (x : (restrict p P).Fiber U) {V : 𝒮}
    (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    Fiber.fiberInclusion.map (pullbackFiberιFiberIso h1 x f).inv =
      (pullbackFiberιIso p P h1 x f).inv := rfl

/-- The fibrewise comparison is natural: base change of a morphism of a fibre inside the full
subcategory agrees with base change of its image. -/
@[reassoc]
lemma pullbackFiberιFiberIso_naturality {U : 𝒮} {x y : (restrict p P).Fiber U}
    (φ : x ⟶ y) {V : 𝒮} (f : V ⟶ U) :
    haveI := isFibered_restrict_of_closed p P h1
    (fiberιFunctor p P V).map (pullbackFiberHom φ f) ≫ (pullbackFiberιFiberIso h1 y f).hom =
      (pullbackFiberιFiberIso h1 x f).hom ≫
        pullbackFiberHom ((fiberιFunctor p P U).map φ) f := by
  have := isFibered_restrict_of_closed p P h1
  refine fiber_hom_ext_of_cartesian f (IsPreFibered.pullbackMap (fiberι p P y).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberιFunctor_map,
    fiberInclusion_map_pullbackFiberιFiberIso_hom, pullbackFiberιIso_hom_fac,
    pullbackFiberHom_fac, pullbackFiberιIso_hom_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, pullbackFiberHom_fac]

/-- The fibrewise comparison is compatible with iterated chosen pullbacks: comparing the chosen
pullback of a chosen pullback and then contracting agrees with contracting inside the full
subcategory and then comparing. -/
@[reassoc]
lemma pullbackFiberιFiberIso_comp {U : 𝒮} (x : (restrict p P).Fiber U) {V Z : 𝒮}
    (f : V ⟶ U) (γ : Z ⟶ V) :
    haveI := isFibered_restrict_of_closed p P h1
    (fiberιFunctor p P Z).map (pullbackFiberCompIso x f γ).hom ≫
        (pullbackFiberιFiberIso h1 x (γ ≫ f)).hom =
      (pullbackFiberιFiberIso h1 (pullbackFiber (restrict p P) x f) γ).hom ≫
        pullbackFiberHom (pullbackFiberιFiberIso h1 x f).hom γ ≫
        (pullbackFiberCompIso (fiberι p P x) f γ).hom := by
  have := isFibered_restrict_of_closed p P h1
  refine fiber_hom_ext_of_cartesian (γ ≫ f) (IsPreFibered.pullbackMap (fiberι p P x).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fiberιFunctor_map,
    fiberInclusion_map_pullbackFiberιFiberIso_hom, pullbackFiberιIso_hom_fac,
    pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc, pullbackFiberιIso_hom_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, pullbackFiberCompIso_hom_fac]

/-- `pullbackFiberιFiberIso_comp` with the two contractions inverted. -/
@[reassoc]
lemma pullbackFiberιFiberIso_comp_inv {U : 𝒮} (x : (restrict p P).Fiber U) {V Z : 𝒮}
    (f : V ⟶ U) (γ : Z ⟶ V) :
    haveI := isFibered_restrict_of_closed p P h1
    (pullbackFiberιFiberIso h1 x (γ ≫ f)).inv ≫
        (fiberιFunctor p P Z).map (pullbackFiberCompIso x f γ).inv ≫
        (pullbackFiberιFiberIso h1 (pullbackFiber (restrict p P) x f) γ).hom =
      (pullbackFiberCompIso (fiberι p P x) f γ).inv ≫
        pullbackFiberHom (pullbackFiberιFiberIso h1 x f).inv γ := by
  have := isFibered_restrict_of_closed p P h1
  rw [Iso.inv_comp_eq, ← cancel_epi ((fiberιFunctor p P Z).map (pullbackFiberCompIso x f γ).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp, eq_comm,
    ← Category.assoc, pullbackFiberιFiberIso_comp h1 x f γ]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← pullbackFiberHom_comp,
    Iso.hom_inv_id, pullbackFiberHom_id]
  exact Category.comp_id _

end Functor

end CategoryTheory
