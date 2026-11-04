module

public import StacksFrontier.CategoryTheory.Adjunction.LeftTensorHomDiagonalTransport

/-!
# Dinaturality of a transported tensor–Hom adjunction in the middle variable

Let `e : C ≌ D` be an equivalence carrying a tensor bifunctor `T_C` to `T_D`, and let
`- ⊗ Q ⊣ H_D(Q, -)` on `D` be dinatural in `Q`: for `v : Q' ⟶ Q`, the transpose of
`θ ≫ H_D(v, M)` is `A ⊗ v` followed by the transpose of `θ` (the transposes being read through
any family `κ` of maps agreeing with them). Then the transported adjunctions
`- ⊗ P ⊣ H_C(P, -) = e⁻¹ H_D(e P, e -)` on `C` are dinatural in `P` in the same sense.

## Main results

* `CategoryTheory.PullbackInternalHom.transportAdjunction_homEquiv_symm_dinaturality`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackInternalHom

open Opposite

variable {C D : Type*} {instC : Category C} {instD : Category D}
  (e : C ≌ D) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ e.functor ≅ e.functor.prod e.functor ⋙ Functor.uncurry.obj TD)
  (HD : Dᵒᵖ ⥤ D ⥤ D) (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The transported tensor–Hom adjunction is dinatural in its middle variable**, as soon as
the adjunction of `D` is: for `u : P' ⟶ P` and `θ : A ⟶ H_C(P, M)`, the transpose of
`θ ≫ H_C(u, M)` is `A ⊗ u` followed by the transpose of `θ`. -/
theorem transportAdjunction_homEquiv_symm_dinaturality
    (adjC : ∀ P : C, TC.flip.obj P ⊣ (e.functor.op ⋙ HD ⋙
      (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse).obj (op P))
    (ρ : ∀ P : C, TC.flip.obj P ≅ e.functor ⋙ TD.flip.obj (e.functor.obj P) ⋙ e.inverse)
    (hρ : ∀ P A : C, (ρ P).hom.app A =
      e.unit.app ((TC.obj A).obj P) ≫ e.inverse.map (μ.hom.app (A, P)))
    (hadj : ∀ P : C, adjC P =
      ((e.toAdjunction.comp (adjD (e.functor.obj P))).comp e.symm.toAdjunction).ofNatIsoLeft
        (ρ P).symm)
    (κ : ∀ (Q A M : D), (A ⟶ (HD.obj (op Q)).obj M) → ((TD.obj A).obj Q ⟶ M))
    (hκ : ∀ (Q A M : D) (x : A ⟶ (HD.obj (op Q)).obj M), ((adjD Q).homEquiv A M).symm x = κ Q A M x)
    (hD : ∀ {Q' Q : D} (v : Q' ⟶ Q) {A M : D} (θ : A ⟶ (HD.obj (op Q)).obj M),
      κ Q' A M (θ ≫ (HD.map v.op).app M) = (TD.obj A).map v ≫ κ Q A M θ)
    {P' P : C} (u : P' ⟶ P) {A M : C}
    (θ : A ⟶ ((e.functor.op ⋙ HD ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
        (Functor.whiskeringRight _ _ _).obj e.inverse).obj (op P)).obj M) :
    ((adjC P').homEquiv A M).symm (θ ≫ ((e.functor.op ⋙ HD ⋙
        (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
          (Functor.whiskeringRight _ _ _).obj e.inverse).map u.op).app M) =
      (TC.obj A).map u ≫ ((adjC P).homEquiv A M).symm θ := by
  have key := fun P => transportAdjunction_homEquiv_symm e TC TD μ HD adjD P (ρ P) (hρ P) A M
  rw [hadj P', hadj P, key P', key P]
  have h1 : e.functor.map (θ ≫ ((e.functor.op ⋙ HD ⋙
        (Functor.whiskeringLeft _ _ _).obj e.functor ⋙
          (Functor.whiskeringRight _ _ _).obj e.inverse).map u.op).app M) ≫
        e.counit.app ((HD.obj (op (e.functor.obj P'))).obj (e.functor.obj M)) =
      (e.functor.map θ ≫ e.counit.app ((HD.obj (op (e.functor.obj P))).obj (e.functor.obj M))) ≫
        (HD.map (e.functor.map u).op).app (e.functor.obj M) := by
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (e.functor.map θ ≫ ·) (e.counit.naturality _)
  have h2 : μ.hom.app (A, P') ≫ (TD.obj (e.functor.obj A)).map (e.functor.map u) =
      e.functor.map ((TC.obj A).map u) ≫ μ.hom.app (A, P) := by
    simpa using (μ.hom.naturality ((𝟙 A, u) : ((A, P') : C × C) ⟶ (A, P))).symm
  rw [h1, hκ, hD, ← hκ, ← Category.assoc (μ.hom.app (A, P')), h2, Category.assoc, Functor.map_comp]
  simp only [Category.assoc]
  exact (e.unit.naturality_assoc ((TC.obj A).map u) _).symm

end CategoryTheory.PullbackInternalHom

end
