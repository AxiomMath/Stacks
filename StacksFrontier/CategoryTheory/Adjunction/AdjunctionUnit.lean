module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Criteria for the unit of an adjunction

Let `F ⊣ G` be an adjunction and let `X` be an object of the source category.  Every morphism
`X ⟶ G.obj (F.obj X)` factors through the component of the unit at `X`, because the unit
corresponds to the identity of `F.obj X` under the hom-set bijection.  Consequently that
component is a monomorphism as soon as *some* morphism `X ⟶ G.obj (F.obj X)` is one.  If
moreover the whole composite `F ⋙ G` is isomorphic to the identity functor — by any
isomorphism at all — then the unit is an isomorphism, so `F` is fully faithful.

## Main results

* `Stacks.Adjunction.unit_app_fac`: the factorisation.
* `Stacks.Adjunction.mono_unit_app_of_mono`: the resulting monomorphism criterion.
* `Stacks.Adjunction.isIso_unit_of_comp_iso_id`: an isomorphism `F ⋙ G ≅ 𝟭` makes the unit an
  isomorphism.
* `Stacks.Adjunction.isIso_unit_app_of_iso_of_comm`: the objectwise form at an object whose
  endomorphisms commute — an isomorphism `G.obj (F.obj X) ≅ X` makes the unit at `X` invertible.
* `Stacks.Adjunction.bijective_map_of_isIso_unit_app`: when the unit at `X` is invertible, `G` is
  bijective on the morphisms out of `F.obj X`.

## Implementation notes

The monomorphism criterion is what one needs when an adjunction is only available as a chosen
inhabitant of a `Nonempty` type, so that its unit is opaque and no amount of unfolding computes
the unit on sections.  The hypothesis asks instead for a monomorphism built by hand, with no
reference to the adjunction, and the conclusion is about the opaque unit.

`isIso_unit_of_comp_iso_id` does not assume that the given isomorphism `F ⋙ G ≅ 𝟭` is the
inverse of the unit, and that is the point: in applications the isomorphism is produced by some
geometric argument and has no a priori relation to the unit.  The unit composed with it is a
natural endomorphism of the identity functor which has a retraction built from the counit, and
naturality of that retraction at the components of the endomorphism itself shows the two
composites agree, so the endomorphism is invertible.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- Every morphism `X ⟶ G.obj (F.obj X)` factors through the unit of an adjunction `F ⊣ G`
at `X`, namely through the image under `G` of its own adjoint. -/
theorem unit_app_fac (adj : F ⊣ G) {X : C} (ψ : X ⟶ G.obj (F.obj X)) :
    adj.unit.app X ≫ G.map ((adj.homEquiv X (F.obj X)).symm ψ) = ψ :=
  (adj.homEquiv X (F.obj X)).apply_symm_apply ψ

/-- If some morphism `X ⟶ G.obj (F.obj X)` is a monomorphism, then so is the unit of the
adjunction `F ⊣ G` at `X`. -/
theorem mono_unit_app_of_mono (adj : F ⊣ G) {X : C} (ψ : X ⟶ G.obj (F.obj X)) [Mono ψ] :
    Mono (adj.unit.app X) :=
  mono_of_mono_fac (unit_app_fac adj ψ)

/-- `Stacks.Adjunction.mono_unit_app_of_mono` with the monomorphism as an explicit
hypothesis. -/
theorem mono_unit_app_of_mono' (adj : F ⊣ G) {X : C} (ψ : X ⟶ G.obj (F.obj X)) (hψ : Mono ψ) :
    Mono (adj.unit.app X) :=
  have := hψ
  mono_unit_app_of_mono adj ψ

/-- The retraction of the unit built from an isomorphism `F ⋙ G ≅ 𝟭` and the counit. -/
private def unitRetraction (adj : F ⊣ G) (θ : F ⋙ G ≅ 𝟭 C) : 𝟭 C ⟶ 𝟭 C where
  app X := θ.inv.app X ≫ G.map (F.map (θ.inv.app X)) ≫
    G.map (adj.counit.app (F.obj X)) ≫ θ.hom.app X
  naturality {X Y} g := by
    have hθ : g ≫ θ.inv.app Y = θ.inv.app X ≫ G.map (F.map g) := θ.inv.naturality g
    have hh : G.map (F.map g) ≫ θ.hom.app Y = θ.hom.app X ≫ g := θ.hom.naturality g
    have key : F.map (g ≫ θ.inv.app Y) ≫ adj.counit.app (F.obj Y) =
        F.map (θ.inv.app X) ≫ adj.counit.app (F.obj X) ≫ F.map g := by
      have hc : F.map (G.map (F.map g)) ≫ adj.counit.app (F.obj Y) =
          adj.counit.app (F.obj X) ≫ F.map g := adj.counit.naturality (F.map g)
      rw [hθ, F.map_comp, Category.assoc, hc]
    dsimp only [Functor.id_obj, Functor.id_map]
    rw [← Category.assoc, hθ]
    simp only [Category.assoc]
    rw [← hh]
    simp only [← Functor.map_comp_assoc]
    rw [key]

/-- If the composite `F ⋙ G` of an adjoint pair `F ⊣ G` is isomorphic to the identity, then
the unit of the adjunction is an isomorphism — and hence `F` is fully faithful.

An arbitrary isomorphism `F ⋙ G ≅ 𝟭` is weaker than invertibility of the unit only in
appearance: the unit always has a retraction built from such an isomorphism and the counit, and
a natural endomorphism of the identity functor with a retraction is invertible, because
naturality of the retraction at the components of the endomorphism itself makes the two
composites agree. -/
theorem isIso_unit_of_comp_iso_id (adj : F ⊣ G) (θ : F ⋙ G ≅ 𝟭 C) : IsIso adj.unit := by
  set a : 𝟭 C ⟶ 𝟭 C := adj.unit ≫ θ.hom with ha_def
  set b : 𝟭 C ⟶ 𝟭 C := unitRetraction adj θ with hb_def
  have hab (X : C) : a.app X ≫ b.app X = 𝟙 X := by
    have h : adj.unit.app X ≫ G.map (F.map (θ.inv.app X)) =
        θ.inv.app X ≫ adj.unit.app (G.obj (F.obj X)) :=
      (adj.unit.naturality (θ.inv.app X)).symm
    have ht : adj.unit.app (G.obj (F.obj X)) ≫ G.map (adj.counit.app (F.obj X)) =
        𝟙 (G.obj (F.obj X)) := adj.right_triangle_components _
    dsimp [a, b, unitRetraction]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, h, Category.assoc, ← Category.assoc (adj.unit.app _), ht]
    simp
  have hba (X : C) : b.app X ≫ a.app X = 𝟙 X := by
    have h := b.naturality (a.app X)
    dsimp only [Functor.id_obj, Functor.id_map] at h
    exact h.symm.trans (hab X)
  have ha : IsIso a := by
    have h (X : C) : IsIso (a.app X) := ⟨b.app X, hab X, hba X⟩
    exact NatIso.isIso_of_isIso_app a
  exact IsIso.of_isIso_comp_right adj.unit θ.hom

/-- **The unit at an object with commuting endomorphisms.** Let `F ⊣ G` be an adjunction and let
`X` be an object any two of whose endomorphisms commute. If `G.obj (F.obj X)` is isomorphic to
`X` — by any isomorphism at all — then the unit of the adjunction at `X` is an isomorphism.

The unit at `X` has a retraction, built from the given isomorphism and the adjoint of its inverse,
so the endomorphism `η_X ≫ θ` of `X` has a left inverse; endomorphisms of `X` commuting, the left
inverse is a right inverse too. -/
theorem isIso_unit_app_of_iso_of_comm (adj : F ⊣ G) {X : C} (θ : G.obj (F.obj X) ≅ X)
    (hcomm : ∀ g h : X ⟶ X, g ≫ h = h ≫ g) : IsIso (adj.unit.app X) := by
  set r : G.obj (F.obj X) ⟶ X := G.map ((adj.homEquiv X (F.obj X)).symm θ.inv) ≫ θ.hom
  have hr : adj.unit.app X ≫ r = 𝟙 X := by
    rw [← Category.assoc, unit_app_fac adj θ.inv, Iso.inv_hom_id]
    rfl
  have hgh : (adj.unit.app X ≫ θ.hom) ≫ (θ.inv ≫ r) = 𝟙 X := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hr
  have hg : IsIso (adj.unit.app X ≫ θ.hom) :=
    ⟨θ.inv ≫ r, hgh, (hcomm _ _).symm.trans hgh⟩
  exact IsIso.of_isIso_comp_right (adj.unit.app X) θ.hom

/-- **A right adjoint is bijective on the morphisms out of `F.obj X` when the unit at `X` is
invertible.** Composed with the unit at `X`, the map `s ↦ G.map s` is the hom-set bijection of
the adjunction. -/
theorem bijective_map_of_isIso_unit_app (adj : F ⊣ G) {X : C} [IsIso (adj.unit.app X)] (Y : D) :
    Function.Bijective (fun s : F.obj X ⟶ Y => G.map s) := by
  have h : (fun s : F.obj X ⟶ Y => G.map s) =
      (fun t : X ⟶ G.obj Y => inv (adj.unit.app X) ≫ t) ∘ adj.homEquiv X Y := by
    funext s
    simp [Adjunction.homEquiv_unit]
  rw [h]
  refine Function.Bijective.comp ⟨fun a b hab => ?_, fun t => ⟨adj.unit.app X ≫ t, by simp⟩⟩
    (adj.homEquiv X Y).bijective
  simpa using congrArg (adj.unit.app X ≫ ·) hab

end Stacks.Adjunction
