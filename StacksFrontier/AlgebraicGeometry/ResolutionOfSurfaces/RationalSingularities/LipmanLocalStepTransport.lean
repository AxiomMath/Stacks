module

public import StacksFrontier.RingTheory.Dualizing.DualizingModuleRingEquiv
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# Transport of a canonical ideal along an isomorphism over `Spec B`

For a scheme `X` over `Spec B`, an ideal `J ⊆ B` and a point `x`, write `J·𝒪_{X,x}` for the
extension of `J` along `B ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,x}`. Being a dualizing module of `𝒪_{X,x}` is
transported along isomorphisms over `Spec B` (`isDualizingRingModule_map_germ_of_iso`). The
vanishing ideal of the closed point of a local ring is the kernel of the residue point
(`vanishingIdeal_closedPoint_eq_ker_residuePoint`).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- `B ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,x}` for a scheme `X` over `Spec B`. -/
abbrev baseToStalk {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) (x : X) :
    B →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

/-- Along an isomorphism `e : X' ⟶ X` over `Spec B`, the map `B ⟶ 𝒪_{X',x}` is `B ⟶ 𝒪_{X,e x}`
followed by the stalk map of `e`. -/
theorem baseToStalk_of_iso {B : Type u} [CommRing B] {X X' : Scheme.{u}} (f : X ⟶ Spec (.of B))
    (e : X' ⟶ X) (x : X') :
    baseToStalk (e ≫ f) x = (e.stalkMap x).hom.comp (baseToStalk f (e x)) := by
  rw [baseToStalk, baseToStalk, ← CommRingCat.hom_comp]
  congr 1
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.Hom.germ_stalkMap e ⊤ x trivial]
  rfl

/-- **A canonical ideal is transported along an isomorphism over `Spec B`.** -/
theorem isDualizingRingModule_map_germ_of_iso {B : Type u} [CommRing B] {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (e : X' ⟶ X) [IsIso e] (J : Ideal B) (x : X')
    (h : ∃ _ : IsNoetherianRing (X.presheaf.stalk (e x)),
      Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk (e x))
        (J.map (baseToStalk f (e x)))) :
    ∃ _ : IsNoetherianRing (X'.presheaf.stalk x),
      Stacks.Duality.IsDualizingRingModule (X'.presheaf.stalk x)
        (J.map (baseToStalk (e ≫ f) x)) := by
  obtain ⟨hN, hD⟩ := h
  let σ := (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsNoetherianRing (X'.presheaf.stalk x) := isNoetherianRing_of_ringEquiv _ σ
  refine ⟨inferInstance, ?_⟩
  rw [baseToStalk_of_iso]
  exact Stacks.Duality.isDualizingRingModule_map_ringEquiv _ σ J hD

/-- **The vanishing ideal of the closed point of `Spec B` is the kernel of the residue point.** -/
theorem vanishingIdeal_closedPoint_eq_ker_residuePoint (B : Type u) [CommRing B] [IsLocalRing B]
    (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B)))) :
    Scheme.IdealSheafData.vanishingIdeal
        (⟨{IsLocalRing.closedPoint B}, hc⟩ : TopologicalSpace.Closeds (Spec (.of B))) =
      (Stacks.Blowup.residuePoint B).ker := by
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range (Stacks.Blowup.residuePoint B)]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure, ← Scheme.Hom.support_ker]
  exact (supportSet_ker_residuePoint B).symm

end AlgebraicGeometry
