module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers

/-!
# Common lemmas for étale cohomology

Small general facts shared by several developments of étale cohomology in this library.

## Main results

* `AlgebraicGeometry.Scheme.stalkCongr_comp_stalkClosedPointTo_of_eq`: the local homomorphism
  attached to a morphism equal to `Spec.map f ≫ X.fromSpecStalk x` is `f`.
* `AlgebraicGeometry.Scheme.stalkMap_congr_point`: stalk maps at equal points agree up to the
  transports.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/-- The local homomorphism attached to a morphism which equals `Spec.map f ≫ X.fromSpecStalk x`
is `f`, read through the transport of stalks. -/
theorem stalkCongr_comp_stalkClosedPointTo_of_eq {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] (g : Spec R ⟶ X)
    (hg : g = Spec.map f ≫ X.fromSpecStalk x) (h : g (closedPoint R) = x) :
    (X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ Scheme.stalkClosedPointTo g = f := by
  subst hg
  exact StacksDraft.ArtinApproximation.stalkCongr_comp_stalkClosedPointTo f h

/-- The stalk maps of a morphism at two equal points agree up to the transports. -/
theorem stalkMap_congr_point {X Y : Scheme.{u}} (g : X ⟶ Y) {a b : X} (hab : a = b) :
    g.stalkMap a ≫ (X.presheaf.stalkCongr (.of_eq hab)).hom =
      (Y.presheaf.stalkCongr (.of_eq (congrArg g hab))).hom ≫ g.stalkMap b := by
  cases hab
  simp

/-- Transporting a germ along a specialization and back is the identity. -/
theorem stalkSpecializes_stalkSpecializes_apply {X : Scheme.{u}} {a b : X} (h : a ⤳ b)
    (h' : b ⤳ a) (r : X.presheaf.stalk b) :
    (X.presheaf.stalkSpecializes h').hom ((X.presheaf.stalkSpecializes h).hom r) = r := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end AlgebraicGeometry.Scheme
