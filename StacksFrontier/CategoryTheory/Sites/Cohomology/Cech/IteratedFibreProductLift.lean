module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfAnIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt

/-!
# Morphisms into the iterated fibre products of a family

Let `{f_i : U_i → U}` be a family of morphisms with fixed target. A morphism from an object `W`
into the iterated fibre product `U_{i_0} ×_U ⋯ ×_U U_{i_n}` is the same as a tuple of morphisms
`y_a : W → U_{i_a}` with a common composite `w : W → U`. This file names that morphism and records
how it interacts with precomposition and with the maps of iterated fibre products induced by a
morphism of families (Stacks 03F4).

## Main definitions

* `Stacks.CechSite.cechProductLift`: the morphism into an iterated fibre product with given
  components.

## Main results

* `Stacks.CechSite.cechProductLift_π_left`: its components are the given morphisms.
* `Stacks.CechSite.comp_cechProductLift`: compatibility with precomposition.
* `Stacks.CechSite.cechProductLift_comp_cechProductMap`: compatibility with the map induced by a
  morphism of families.
-/

@[expose] public section

universe w w' v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{w} U) (n : ℕ)
  (t : Fin (n + 1) → E.I₀) [HasProduct (fun a ↦ Over.mk (E.f (t a)))]

/-- The morphism into the iterated fibre product `U_{t_0} ×_U ⋯ ×_U U_{t_n}` of a family with
components `y_a : W ⟶ U_{t_a}` over a common `w : W ⟶ U`. -/
noncomputable def cechProductLift {W : C} (w : W ⟶ U) (y : ∀ a, W ⟶ E.X (t a))
    (hy : ∀ a, y a ≫ E.f (t a) = w) : W ⟶ (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left :=
  (Pi.lift (P := Over.mk w) fun a ↦ (Over.homMk (y a) (hy a) :
    Over.mk w ⟶ Over.mk (E.f (t a)))).left

/-- The components of `Stacks.CechSite.cechProductLift` are the given morphisms. -/
@[reassoc (attr := simp)]
theorem cechProductLift_π_left {W : C} (w : W ⟶ U) (y : ∀ a, W ⟶ E.X (t a))
    (hy : ∀ a, y a ≫ E.f (t a) = w) (b : Fin (n + 1)) :
    cechProductLift E n t w y hy ≫ (Pi.π (fun a ↦ Over.mk (E.f (t a))) b).left = y b := by
  rw [cechProductLift, ← Over.comp_left, Pi.lift_π]
  rfl

/-- `Stacks.CechSite.cechProductLift` lies over the common composite. -/
@[reassoc (attr := simp)]
theorem cechProductLift_hom {W : C} (w : W ⟶ U) (y : ∀ a, W ⟶ E.X (t a))
    (hy : ∀ a, y a ≫ E.f (t a) = w) :
    cechProductLift E n t w y hy ≫ (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom = w :=
  Over.w (Pi.lift (P := Over.mk w) fun a ↦ (Over.homMk (y a) (hy a) :
    Over.mk w ⟶ Over.mk (E.f (t a))))

/-- Precomposing `Stacks.CechSite.cechProductLift` precomposes its components. -/
theorem comp_cechProductLift {W W' : C} (h : W' ⟶ W) (w : W ⟶ U) (y : ∀ a, W ⟶ E.X (t a))
    (hy : ∀ a, y a ≫ E.f (t a) = w) :
    h ≫ cechProductLift E n t w y hy =
      cechProductLift E n t (h ≫ w) (fun a ↦ h ≫ y a)
        (fun a ↦ by rw [Category.assoc, hy]) :=
  cechProduct_left_hom_ext E n t fun b ↦ by simp

/-- A morphism into an iterated fibre product is the lift of its components. -/
theorem eq_cechProductLift {W : C} (g : W ⟶ (∏ᶜ fun a ↦ Over.mk (E.f (t a))).left) :
    g = cechProductLift E n t (g ≫ (∏ᶜ fun a ↦ Over.mk (E.f (t a))).hom)
      (fun a ↦ g ≫ (Pi.π (fun a ↦ Over.mk (E.f (t a))) a).left)
      (fun a ↦ by
        rw [Category.assoc]
        exact congrArg (g ≫ ·) (Over.w (Pi.π (fun a ↦ Over.mk (E.f (t a))) a))) :=
  cechProduct_left_hom_ext E n t fun b ↦ by simp

omit [HasProduct fun a ↦ Over.mk (E.f (t a))] in
/-- The map of iterated fibre products induced by a morphism of families, composed with a lift,
is the lift of the composites. -/
theorem cechProductLift_comp_cechProductMap {V : C} (G : PreZeroHypercover.{w} V) {f : U ⟶ V}
    (φ : E.HomOver G f)
    [∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    {W : C} (w : W ⟶ U) (y : ∀ a, W ⟶ E.X (t a)) (hy : ∀ a, y a ≫ E.f (t a) = w) :
    cechProductLift E n t w y hy ≫ cechProductMap E G φ n t =
      cechProductLift G n (φ.s₀ ∘ t) (w ≫ f) (fun a ↦ y a ≫ φ.h₀ (t a))
        (fun a ↦ by
          change (y a ≫ φ.h₀ (t a)) ≫ G.f (φ.s₀ (t a)) = w ≫ f
          rw [Category.assoc, φ.w₀, reassoc_of% (hy a)]) :=
  cechProduct_left_hom_ext G n (φ.s₀ ∘ t) fun b ↦ by
    have h := cechProductMap_comp_π_left φ n t b
    rw [Category.assoc]
    refine (congrArg (cechProductLift E n t w y hy ≫ ·) h).trans ?_
    rw [cechProductLift_π_left_assoc, cechProductLift_π_left]

end Stacks.CechSite
