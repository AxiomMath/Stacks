module

public import StacksFrontier.Deformation.Cofibered.Over

/-!
# Thinness of a fibre transports along an isomorphism of the base

For a functor `p : F ⥤ C` the fibre `p.Fiber A` is cut out by the *equality* `p.obj a = A`, so
two isomorphic base objects have unrelated fibres as subtypes of `F` and a property of one
fibre is formally no property of the other. When `p` is cofibered in groupoids the two are
nevertheless matched up by pushing forward along the isomorphism: the pushforward arrows lie
over isomorphisms, hence are invertible, and conjugating by them takes the vertical morphisms
of one fibre injectively to those of the other.

## Main results

* `Deformation.isThin_fiber_of_iso`: if `A ≅ B` and the fibre of a category cofibered in
  groupoids over `A` is thin, then so is its fibre over `B`.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]

/-- **Thinness of a fibre transports along an isomorphism of the base.** Each object of the
fibre over `B` is the source of a pushforward along `e.inv`, and that arrow is invertible
because `e.inv` is; conjugating a vertical morphism of the fibre over `B` by two such arrows
gives a vertical morphism of the fibre over `A`, and the conjugation is injective, so the
first fibre is thin as soon as the second is. -/
public theorem isThin_fiber_of_iso {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) {A B : C}
    (e : A ≅ B) (hA : Quiver.IsThin (p.Fiber A)) : Quiver.IsThin (p.Fiber B) := by
  intro x y
  obtain ⟨x', ι, hι⟩ := exists_pushforward hp e.inv x.1 x.2
  obtain ⟨y', κ, hκ⟩ := exists_pushforward hp e.inv y.1 y.2
  have hιlift : p.IsHomLift e.inv ι := hι
  have hκlift : p.IsHomLift e.inv κ := hκ
  have hιmap : IsIso (p.map ι) := by
    rw [CategoryTheory.IsHomLift.fac' p e.inv ι]
    infer_instance
  have hκmap : IsIso (p.map κ) := by
    rw [CategoryTheory.IsHomLift.fac' p e.inv κ]
    infer_instance
  have hιiso : IsIso ι := isIso_of_isCofiberedInGroupoids_of_map_isIso hp ι
  have hκiso : IsIso κ := isIso_of_isCofiberedInGroupoids_of_map_isIso hp κ
  have hx' : p.obj x' = A := CategoryTheory.IsHomLift.codomain_eq p e.inv ι
  have hy' : p.obj y' = A := CategoryTheory.IsHomLift.codomain_eq p e.inv κ
  have hιsymm : p.IsHomLift e.symm.hom (asIso ι).hom := hιlift
  obtain ⟨j, hjlift, hj⟩ :
      ∃ j : x' ⟶ x.1, p.IsHomLift e.hom j ∧ ι ≫ j = 𝟙 x.1 :=
    ⟨inv ι, CategoryTheory.IsHomLift.inv_lift_inv p e.symm (asIso ι), IsIso.hom_inv_id ι⟩
  have hvert : ∀ χ : x ⟶ y, p.IsHomLift (𝟙 A) (j ≫ χ.1 ≫ κ) := by
    intro χ
    have hχ : p.IsHomLift (𝟙 B) χ.1 := χ.2
    have h : p.IsHomLift (e.hom ≫ 𝟙 B ≫ e.inv) (j ≫ χ.1 ≫ κ) := inferInstance
    rwa [Category.id_comp, e.hom_inv_id] at h
  have hthinA := hA (Functor.Fiber.mk hx') (Functor.Fiber.mk hy')
  refine ⟨fun φ ψ => Subtype.ext ?_⟩
  have hcan : j ≫ φ.1 ≫ κ = j ≫ ψ.1 ≫ κ :=
    congrArg Subtype.val
      (Subsingleton.elim (α := Functor.Fiber.mk hx' ⟶ Functor.Fiber.mk hy')
        ⟨_, hvert φ⟩ ⟨_, hvert ψ⟩)
  refine (cancel_mono κ).mp ?_
  simpa [reassoc_of% hj] using congrArg (ι ≫ ·) hcan

end

end Deformation

end
