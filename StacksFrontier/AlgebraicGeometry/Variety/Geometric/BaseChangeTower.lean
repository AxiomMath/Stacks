module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Irreducible

/-!
# Base change along a tower, and transport of irreducible components

Base changing a morphism `f : X ⟶ S` along a composite `K ⟶ E ⟶ S` can be done in two steps,
and the resulting comparison isomorphism `X ×_S K ≅ (X ×_S E) ×_E K` is characterized by its
two projections. This file records that comparison together with the elementary transport of
points and of irreducible components along an arbitrary isomorphism of schemes.

## Main definitions

* `AlgebraicGeometry.baseChangeTowerIsoTo` is the two-step base change comparison, stated for a
  morphism presented as a composite.

## Main results

* `AlgebraicGeometry.baseChangeTowerIsoTo_hom_fst` and
  `AlgebraicGeometry.baseChangeTowerIsoTo_hom_snd` compute the comparison on both projections.
* `AlgebraicGeometry.baseChangeTowerIsoTo_comp_of_projection` identifies any morphism of base
  changes compatible with the projections with the first projection of the two-step base change.
* `AlgebraicGeometry.image_mem_irreducibleComponents_of_iso` and
  `AlgebraicGeometry.preimage_mem_irreducibleComponents_of_iso` transport irreducible
  components along an isomorphism of schemes.
* `AlgebraicGeometry.image_eq_of_image_eq_of_comm` transports an invariant subset along a
  comparison isomorphism intertwining two self-maps.

## Implementation notes

The underlying isomorphism is Mathlib's `pullbackLeftPullbackSndIso`; the only thing added here
is the transport along a chosen factorization of the structure morphism, which is what lets the
comparison be used when the composite is only propositionally equal to the given morphism.

The transport statements are phrased with `Scheme.Hom.base` rather than with the homeomorphism
`Scheme.homeoOfIso`, so that they rewrite against goals written in terms of morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Iso

variable {X Y : Scheme.{u}}

/-- An isomorphism of schemes is surjective on points. -/
public theorem surjective_hom_base_of_iso (e : X ≅ Y) : Function.Surjective e.hom.base :=
  (Scheme.homeoOfIso e).surjective

/-- An isomorphism of schemes carries irreducible components to irreducible components. -/
public theorem image_mem_irreducibleComponents_of_iso (e : X ≅ Y) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) : e.hom.base '' Z ∈ irreducibleComponents Y := by
  have h : (Scheme.homeoOfIso e) '' Z ∈ irreducibleComponents Y :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber _
      (Scheme.homeoOfIso e).continuous (Scheme.homeoOfIso e).isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage
        (Scheme.homeoOfIso e).injective).isPreirreducible)
      (Scheme.homeoOfIso e).surjective hZ
  exact h

/-- The inverse image of a set under an isomorphism of schemes is its image under the inverse
isomorphism. -/
public theorem preimage_eq_image_inv_of_iso (e : X ≅ Y) (Z : Set Y) :
    e.hom.base ⁻¹' Z = e.inv.base '' Z := by
  ext x
  refine ⟨fun hx => ⟨e.hom.base x, hx, Scheme.hom_inv_apply e x⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  rw [Set.mem_preimage, Scheme.inv_hom_apply]
  exact hy

/-- An isomorphism of schemes pulls irreducible components back to irreducible components. -/
public theorem preimage_mem_irreducibleComponents_of_iso (e : X ≅ Y) {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    e.hom.base ⁻¹' Z ∈ irreducibleComponents X := by
  rw [preimage_eq_image_inv_of_iso]
  exact image_mem_irreducibleComponents_of_iso e.symm hZ

/-- Equal composites of morphisms of schemes agree on points. -/
private theorem comp_base_apply_eq {W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (h : X ⟶ W)
    (hfg : f ≫ g = h) (x : X) : g.base (f.base x) = h.base x := by
  rw [← hfg]
  rfl

/-- A set invariant under a self-map transports to an invariant set along a comparison
isomorphism intertwining that self-map with another one. -/
public theorem image_eq_of_image_eq_of_comm (e : X ≅ Y) (a : Y ⟶ Y) (b : X ⟶ X)
    (hcomm : e.hom ≫ a = b ≫ e.hom) (Z : Set Y) (hZ : a.base '' Z = Z) :
    b.base '' (e.hom.base ⁻¹' Z) = e.hom.base ⁻¹' Z := by
  have hpt : ∀ x, b.base x = e.inv.base (a.base (e.hom.base x)) := by
    intro x
    rw [show a.base (e.hom.base x) = e.hom.base (b.base x) from comp_base_apply_eq _ _ _ hcomm x,
      Scheme.hom_inv_apply]
  rw [Set.image_congr' hpt]
  change (e.inv.base ∘ a.base ∘ e.hom.base) '' (e.hom.base ⁻¹' Z) = e.hom.base ⁻¹' Z
  rw [Set.image_comp, Set.image_comp,
    Set.image_preimage_eq _ (surjective_hom_base_of_iso e), hZ,
    ← preimage_eq_image_inv_of_iso]

/-- An equality of inverse images along a factorization of a morphism through a comparison
isomorphism descends to an equality of inverse images along the morphism itself. -/
public theorem preimage_eq_of_comp_eq {W : Scheme.{u}} (e : X ≅ Y) (p : Y ⟶ W) (q : X ⟶ W)
    (hq : e.hom ≫ p = q) (T : Set W) (Z : Set Y)
    (hT : q.base ⁻¹' T = e.hom.base ⁻¹' Z) : p.base ⁻¹' T = Z := by
  refine Set.preimage_injective.mpr (surjective_hom_base_of_iso e) ?_
  rw [← Set.preimage_comp]
  rw [show p.base ∘ e.hom.base = q.base from funext (comp_base_apply_eq _ _ _ hq)]
  exact hT

end Iso

section Tower

variable {X S E K : Scheme.{u}}

/-- Base change along a morphism presented as a composite, performed in two steps. -/
public noncomputable def baseChangeTowerIsoTo (f : X ⟶ S) (g : E ⟶ S) (h : K ⟶ E)
    (g' : K ⟶ S) (hcomp : g' = h ≫ g) :
    pullback (pullback.snd f g) h ≅ pullback f g' :=
  (pullbackLeftPullbackSndIso f g h).trans (pullback.congrHom rfl hcomp).symm

/-- The two-step base change comparison over the projection to `X`. -/
public theorem baseChangeTowerIsoTo_hom_fst (f : X ⟶ S) (g : E ⟶ S) (h : K ⟶ E)
    (g' : K ⟶ S) (hcomp : g' = h ≫ g) :
    (baseChangeTowerIsoTo f g h g' hcomp).hom ≫ pullback.fst f g' =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g := by
  subst hcomp
  simp [baseChangeTowerIsoTo]

/-- The two-step base change comparison over the projection to `K`. -/
public theorem baseChangeTowerIsoTo_hom_snd (f : X ⟶ S) (g : E ⟶ S) (h : K ⟶ E)
    (g' : K ⟶ S) (hcomp : g' = h ≫ g) :
    (baseChangeTowerIsoTo f g h g' hcomp).hom ≫ pullback.snd f g' =
      pullback.snd (pullback.snd f g) h := by
  subst hcomp
  simp [baseChangeTowerIsoTo]

/-- Every morphism of base changes compatible with both projections is the first projection of
the two-step base change, read through the comparison isomorphism. -/
public theorem baseChangeTowerIsoTo_comp_of_projection (f : X ⟶ S) (g : E ⟶ S) (h : K ⟶ E)
    (g' : K ⟶ S) (hcomp : g' = h ≫ g) (p : pullback f g' ⟶ pullback f g)
    (hp₁ : p ≫ pullback.fst f g = pullback.fst f g')
    (hp₂ : p ≫ pullback.snd f g = pullback.snd f g' ≫ h) :
    (baseChangeTowerIsoTo f g h g' hcomp).hom ≫ p = pullback.fst (pullback.snd f g) h := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hp₁, baseChangeTowerIsoTo_hom_fst]
  · rw [Category.assoc, hp₂, ← Category.assoc, baseChangeTowerIsoTo_hom_snd,
      pullback.condition]

end Tower

end AlgebraicGeometry

end
