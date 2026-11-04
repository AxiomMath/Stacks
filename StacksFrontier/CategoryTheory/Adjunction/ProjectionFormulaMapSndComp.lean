module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap

/-!
# The projection formula map with the counit in the second factor, along a composite

Let `Lp ⊣ Rp` (`Lp : C ⥤ D`), `Li ⊣ Ri` (`Li : D ⥤ F`) and `Lq ⊣ Rq` (`Lq : C ⥤ F`) be
adjunctions with an isomorphism `γ : Lp ⋙ Li ≅ Lq`, so that the conjugate
`c : Ri ⋙ Rp ⟶ Rq` identifies the right adjoints. Let the three categories carry bifunctors
`TC`, `TD`, `TF` and the three left adjoints comparisons `μp`, `μi`, `μq` with the tensor products,
compatible with `γ`. Geometrically: `q = p ∘ i` for morphisms of ringed spaces, `γ` the
composition isomorphism of derived pullbacks and `μ` the isomorphisms of Stacks 07A4.

Then the projection formula map `H ⊗ Rq Z ⟶ Rq(Lq H ⊗ Z)` of `q` is the one of `p` at
`(H, Ri Z)` followed by `Rp` of the one of `i` at `(Lp H, Z)`, up to `c` and `γ`.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_of_counit`,
  `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_conjugateEquiv`.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {F : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} F]
  {Lp : C ⥤ D} {Rp : D ⥤ C} (ap : Lp ⊣ Rp) {Li : D ⥤ F} {Ri : F ⥤ D} (ai : Li ⊣ Ri)
  {Lq : C ⥤ F} {Rq : F ⥤ C} (aq : Lq ⊣ Rq) (γ : Lp ⋙ Li ≅ Lq)
  (TC : C × C ⥤ C) (TD : D × D ⥤ D) (TF : F × F ⥤ F)
  (μp : TC ⋙ Lp ⟶ Lp.prod Lp ⋙ TD) (μi : TD ⋙ Li ⟶ Li.prod Li ⋙ TF)
  (μq : TC ⋙ Lq ⟶ Lq.prod Lq ⋙ TF)

/-- Naturality of the comparison `α` at a product of two morphisms. -/
private theorem map_comp_comparison_app {C' D' : Type*} [Category C'] [Category D']
    {L : C' ⥤ D'} {A : C' × C' ⥤ C'} {B : D' × D' ⥤ D'} (α : A ⋙ L ⟶ L.prod L ⋙ B)
    {H H' G G' : C'} (k : H ⟶ H') (g : G ⟶ G') :
    L.map (A.map (k ×ₘ g)) ≫ α.app (H', G') =
      α.app (H, G) ≫ B.map (L.map k ×ₘ L.map g) :=
  α.naturality (k ×ₘ g)

/-- Applying the left adjoint to `adjunctionTensorMapSnd ≫ R y` and then the counit. -/
private theorem map_adjunctionTensorMapSnd_comp_counit {C' D' : Type*} [Category C']
    [Category D'] {L : C' ⥤ D'} {R : D' ⥤ C'} (adj : L ⊣ R) (A : C' × C' ⥤ C')
    (B : D' × D' ⥤ D') (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C') (G X : D')
    (y : B.obj (L.obj H, G) ⟶ X) :
    L.map (adjunctionTensorMapSnd adj A B α H G ≫ R.map y) ≫ adj.counit.app X =
      α.app (H, R.obj G) ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G) ≫ y := by
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit.naturality y]
  rw [Functor.id_map, ← Category.assoc]
  erw [← adj.homEquiv_counit]
  rw [adjunctionTensorMapSnd]
  erw [Equiv.symm_apply_apply]
  rw [Category.assoc]

/-- **The projection formula map along a composite.** If the tensor comparisons are compatible
with `γ : Lp ⋙ Li ≅ Lq`, then for `H : C` and `Z : F`, `H ⊗ c_Z` followed by the projection formula
map of `Lq ⊣ Rq` is the projection formula map of `Lp ⊣ Rp` at `(H, Ri Z)`, then `Rp` of that of
`Li ⊣ Ri` at `(Lp H, Z)` and of `γ_H ⊗ Z`, then `c`. Here `c : Ri ⋙ Rp ⟶ Rq` is any
transformation compatible with the counits through `γ⁻¹`; the conjugate of `γ⁻¹` is one
(`adjunctionTensorMapSnd_comp_conjugateEquiv`). -/
theorem adjunctionTensorMapSnd_comp_of_counit (c : Ri ⋙ Rp ⟶ Rq)
    (hc : ∀ W : F, Lq.map (c.app W) ≫ aq.counit.app W =
      γ.inv.app (Rp.obj (Ri.obj W)) ≫ Li.map (ap.counit.app (Ri.obj W)) ≫ ai.counit.app W)
    (hμ : ∀ H G : C, γ.hom.app (TC.obj (H, G)) ≫ μq.app (H, G) =
      Li.map (μp.app (H, G)) ≫ μi.app (Lp.obj H, Lp.obj G) ≫
        TF.map (γ.hom.app H ×ₘ γ.hom.app G)) (H : C) (Z : F) :
    TC.map (𝟙 H ×ₘ c.app Z) ≫
        adjunctionTensorMapSnd aq TC TF μq H Z =
      adjunctionTensorMapSnd ap TC TD μp H (Ri.obj Z) ≫
        Rp.map (adjunctionTensorMapSnd ai TD TF μi (Lp.obj H) Z ≫
          Ri.map (TF.map (γ.hom.app H ×ₘ 𝟙 Z))) ≫
        c.app (TF.obj (Lq.obj H, Z)) := by
  apply (aq.homEquiv _ _).symm.injective
  -- the left-hand side
  have hL : (aq.homEquiv _ _).symm (TC.map (𝟙 H ×ₘ c.app Z) ≫
      adjunctionTensorMapSnd aq TC TF μq H Z) =
      μq.app (H, Rp.obj (Ri.obj Z)) ≫
        TF.map (𝟙 (Lq.obj H) ×ₘ (γ.inv.app (Rp.obj (Ri.obj Z)) ≫
          Li.map (ap.counit.app (Ri.obj Z)) ≫ ai.counit.app Z)) := by
    unfold adjunctionTensorMapSnd
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    rw [← Category.assoc, map_comp_comparison_app μq (𝟙 H) (c.app Z), Category.assoc,
      ← Functor.map_comp]
    congr 2
    apply Prod.ext
    · simp
    · exact hc Z
  -- the right-hand side
  have hR : (aq.homEquiv _ _).symm (adjunctionTensorMapSnd ap TC TD μp H (Ri.obj Z) ≫
      Rp.map (adjunctionTensorMapSnd ai TD TF μi (Lp.obj H) Z ≫
        Ri.map (TF.map (γ.hom.app H ×ₘ 𝟙 Z))) ≫ c.app (TF.obj (Lq.obj H, Z))) =
      μq.app (H, Rp.obj (Ri.obj Z)) ≫
        TF.map (𝟙 (Lq.obj H) ×ₘ (γ.inv.app (Rp.obj (Ri.obj Z)) ≫
          Li.map (ap.counit.app (Ri.obj Z)) ≫ ai.counit.app Z)) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, hc]
    rw [γ.inv.naturality_assoc, γ.inv.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    rw [map_adjunctionTensorMapSnd_comp_counit ap]
    have hi := map_adjunctionTensorMapSnd_comp_counit ai TD TF μi (Lp.obj H) Z _
      (TF.map (γ.hom.app H ×ₘ 𝟙 Z))
    simp only [Functor.map_comp, Category.assoc] at hi
    simp only [Functor.map_comp, Category.assoc]
    rw [hi]
    rw [reassoc_of% (map_comp_comparison_app μi (𝟙 (Lp.obj H)) (ap.counit.app (Ri.obj Z)))]
    have hμ' := hμ H (Rp.obj (Ri.obj Z))
    have hμ'' : Li.map (μp.app (H, Rp.obj (Ri.obj Z))) ≫
        μi.app (Lp.obj H, Lp.obj (Rp.obj (Ri.obj Z))) =
        γ.hom.app _ ≫ μq.app (H, Rp.obj (Ri.obj Z)) ≫
          TF.map (γ.inv.app H ×ₘ γ.inv.app (Rp.obj (Ri.obj Z))) := by
      rw [reassoc_of% hμ', ← Functor.map_comp]
      simp only [prod_comp, Iso.hom_inv_id_app, ← prod_id]
      refine (congrArg (_ ≫ ·) ?_).symm
      exact (congrArg (_ ≫ ·) (TF.map_id _)).trans (Category.comp_id _)
    rw [reassoc_of% hμ'', Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp]
    congr 2
    apply Prod.ext
    · simp
    · simp
  exact hL.trans hR.symm


/-- `adjunctionTensorMapSnd_comp_of_counit` for the conjugate `Ri ⋙ Rp ⟶ Rq` of `γ⁻¹`. -/
theorem adjunctionTensorMapSnd_comp_conjugateEquiv
    (hμ : ∀ H G : C, γ.hom.app (TC.obj (H, G)) ≫ μq.app (H, G) =
      Li.map (μp.app (H, G)) ≫ μi.app (Lp.obj H, Lp.obj G) ≫
        TF.map (γ.hom.app H ×ₘ γ.hom.app G)) (H : C) (Z : F) :
    TC.map (𝟙 H ×ₘ (conjugateEquiv (ap.comp ai) aq γ.inv).app Z) ≫
        adjunctionTensorMapSnd aq TC TF μq H Z =
      adjunctionTensorMapSnd ap TC TD μp H (Ri.obj Z) ≫
        Rp.map (adjunctionTensorMapSnd ai TD TF μi (Lp.obj H) Z ≫
          Ri.map (TF.map (γ.hom.app H ×ₘ 𝟙 Z))) ≫
        (conjugateEquiv (ap.comp ai) aq γ.inv).app (TF.obj (Lq.obj H, Z)) :=
  adjunctionTensorMapSnd_comp_of_counit ap ai aq γ TC TD TF μp μi μq _
    (fun W => by
      have h := conjugateEquiv_counit (ap.comp ai) aq γ.inv W
      simp only [Adjunction.comp_counit_app] at h
      exact h) hμ H Z

end Stacks.ProjectionFormula
