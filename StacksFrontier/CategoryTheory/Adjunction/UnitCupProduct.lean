module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomAdjunctionTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# Projection maps through the relative cup product, and their transport along equivalences

Let `L ⊣ R` be an adjunction, `A`, `B` tensor bifunctors on its source and target and
`α : A ⋙ L ⟶ L.prod L ⋙ B` a comparison. Besides the projection map
`A(R G, H) ⟶ R B(G, L H)` (`CategoryTheory.adjunctionTensorMap`) there is the map

`A(H, R G) ⟶ A(R L H, R G) ⟶ R B(L H, G)`,

the unit of `L ⊣ R` in the first factor followed by the cup product
(`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct`). This file shows:

* the projection map is the unit in the second factor followed by the cup product
  (`CategoryTheory.adjunctionTensorMap_eq_map_unit_comp_adjunctionCupProduct`);
* when the cup product commutes with braidings, the map above is invertible as soon as the
  projection map is
  (`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.isIso_map_unit_comp_adjunctionCupProduct`);
* for an adjunction and a cup product transported along equivalences of categories, in the way
  the étale derived categories `D(X_étale, Λ)` are read off the constant ringed topoi, the unit
  of the transported adjunction is the original unit followed by the comparison of left adjoints
  (`CategoryTheory.Adjunction.map_transportedUnit_comp`), and the map above for the transported
  data is invertible exactly when its original is
  (`TensorHomAdjunction.isIso_map_comp_transportCupApp_iff`, in the namespace
  `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi`).
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace CategoryTheory

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The projection map through the cup product**: `A(R G, H) ⟶ R B(G, L H)` is the unit of
`L ⊣ R` in the second factor followed by the cup product at `(G, L H)`. -/
theorem adjunctionTensorMap_eq_map_unit_comp_adjunctionCupProduct (G : D) (H : C) :
    adjunctionTensorMap adj A B α G H =
      A.map (𝟙 (R.obj G) ×ₘ adj.unit.app H) ≫
        Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct adj A B α G
          (L.obj H) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionTensorMap Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.comp_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (𝟙 (R.obj G) ×ₘ adj.unit.app H)
  change L.map (A.map (𝟙 (R.obj G) ×ₘ adj.unit.app H)) ≫ α.app (R.obj G, R.obj (L.obj H)) =
    α.app (R.obj G, H) ≫ B.map (L.map (𝟙 (R.obj G)) ×ₘ L.map (adj.unit.app H)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Prod.ext
  · simp
  · simp

end CategoryTheory

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (T₁ : C ⥤ C ⥤ C) (T₂ : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj T₁ ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj T₂)

/-- **The unit-then-cup map is invertible once the projection map is**, for a cup product that
commutes with braidings. Let `ψ₁` and `ψ₂` be invertible braidings of the two tensor bifunctors,
`ψ₁` natural in its first variable, and suppose that the cup product intertwines them:
`cup(K, K') ≫ R ψ₂ = ψ₁ ≫ cup(K', K)`. If the projection map `R G ⊗ H ⟶ R(G ⊗ L H)` is
invertible, so is `H ⊗ R G ⟶ R L H ⊗ R G ⟶ R(L H ⊗ G)`. -/
theorem isIso_map_unit_comp_adjunctionCupProduct
    (ψ₁ : ∀ X Y : C, (T₁.obj X).obj Y ⟶ (T₁.obj Y).obj X)
    (ψ₂ : ∀ X Y : D, (T₂.obj X).obj Y ⟶ (T₂.obj Y).obj X)
    (hψ₁iso : ∀ X Y : C, IsIso (ψ₁ X Y)) (hψ₂iso : ∀ X Y : D, IsIso (ψ₂ X Y))
    (hψ₁ : ∀ {X X' : C} (u : X ⟶ X') (Y : C), (T₁.map u).app Y ≫ ψ₁ X' Y =
      ψ₁ X Y ≫ (T₁.obj Y).map u)
    (hcup : ∀ K K' : D,
      adjunctionCupProduct adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α K K' ≫
          R.map (ψ₂ K K') =
        ψ₁ (R.obj K) (R.obj K') ≫
          adjunctionCupProduct adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α K' K)
    (G : D) (H : C)
    (hPF : IsIso
      (adjunctionTensorMap adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α G H)) :
    IsIso ((T₁.map (adj.unit.app H)).app (R.obj G) ≫
      adjunctionCupProduct adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α
        (L.obj H) G) := by
  have := hψ₁iso H (R.obj G)
  have := hψ₂iso (L.obj H) G
  have e : (T₁.map (adj.unit.app H)).app (R.obj G) ≫
      adjunctionCupProduct adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α
        (L.obj H) G =
      ψ₁ H (R.obj G) ≫
        adjunctionTensorMap adj (Functor.uncurry.obj T₁) (Functor.uncurry.obj T₂) α G H ≫
          inv (R.map (ψ₂ (L.obj H) G)) := by
    have h2 : (T₁.map (adj.unit.app H)).app (R.obj G) ≫ ψ₁ (R.obj (L.obj H)) (R.obj G) =
        ψ₁ H (R.obj G) ≫ (T₁.obj (R.obj G)).map (adj.unit.app H) := hψ₁ (adj.unit.app H) (R.obj G)
    rw [← Category.assoc, IsIso.eq_comp_inv, Category.assoc, hcup, ← Category.assoc, h2,
      adjunctionTensorMap_eq_map_unit_comp_adjunctionCupProduct, Category.assoc]
    congr 1
    simp
  rw [e]
  infer_instance

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

namespace CategoryTheory.Adjunction

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {D₁ : Type*} [Category D₁]
  {D₂ : Type*} [Category D₂] (e₁ : D₁ ≌ C₁) (e₂ : D₂ ≌ C₂)
  {L' : C₂ ⥤ C₁} {R' : C₁ ⥤ C₂} (adj' : L' ⊣ R') {L : D₂ ⥤ D₁} {R : D₁ ⥤ D₂}
  (κ : e₂.functor ⋙ L' ≅ L ⋙ e₁.functor) (ρ : R ≅ e₁.functor ⋙ R' ⋙ e₂.inverse)

/-- **The unit of an adjunction transported along equivalences.** Read `L ⊣ R` off `L' ⊣ R'`
through equivalences `e₁`, `e₂`, a comparison `κ : e₂ ⋙ L' ≅ L ⋙ e₁` of the left adjoints and a
comparison `ρ : R ≅ e₁ ⋙ R' ⋙ e₂⁻¹` of the right adjoints. Then `e₂` of the unit of `L ⊣ R` at
`M`, followed by the comparison `R ⋙ e₂ ≅ e₁ ⋙ R'` induced by `ρ`, is the unit of `L' ⊣ R'` at
`e₂ M` followed by `R' κ`. -/
theorem map_transportedUnit_comp (M : D₂) :
    e₂.functor.map
        ((((e₂.toAdjunction.comp (adj'.comp e₁.symm.toAdjunction)).ofNatIsoLeft
          ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight κ _ ≪≫
            Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e₁.unitIso.symm ≪≫
            Functor.rightUnitor _)).ofNatIsoRight
          ((Functor.associator _ _ _) ≪≫ ρ.symm)).unit.app M) ≫
      (Functor.isoWhiskerRight ρ _ ≪≫
        Functor.isoWhiskerLeft (e₁.functor ⋙ R') e₂.counitIso ≪≫
        Functor.rightUnitor _).hom.app (L.obj M) =
    adj'.unit.app (e₂.functor.obj M) ≫ R'.map (κ.hom.app M) := by
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Equivalence.symm_unit, Equivalence.toAdjunction_unit]
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Equivalence.symm_functor, Equivalence.symm_inverse, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.assoc, Functor.comp_obj]
  rw [← e₂.functor.map_comp_assoc (ρ.inv.app (L.obj M)), Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  simp only [Category.comp_id, Equivalence.counit_naturality_assoc]
  rw [← Category.assoc]
  refine (congrArg (· ≫ _) (e₂.functor_unit_comp M)).trans ?_
  rw [Category.id_comp]
  congr 1
  simp only [← R'.map_comp]
  congr 1
  rw [← Category.assoc]
  refine (congrArg (· ≫ _) (e₁.counitInv_naturality (κ.hom.app M))).trans ?_
  simp only [Category.assoc]
  have h₁ : e₁.functor.map (e₁.unitIso.inv.app (L.obj M)) ≫ e₁.functor.map (𝟙 (L.obj M)) =
      e₁.functor.map (e₁.unitInv.app (L.obj M)) := by
    rw [← Functor.map_comp]
    exact congrArg _ (Category.comp_id _)
  rw [h₁]
  exact (congrArg (κ.hom.app M ≫ ·) (e₁.counitInv_functor_comp (L.obj M))).trans
    (Category.comp_id _)

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {D₁ : Type*} [Category D₁]
  {D₂ : Type*} [Category D₂] (e₁ : D₁ ≌ C₁) (e₂ : D₂ ≌ C₂) {R : D₁ ⥤ D₂} {R' : C₁ ⥤ C₂}
  (c : R ⋙ e₂.functor ≅ e₁.functor ⋙ R') {T₁ : C₁ ⥤ C₁ ⥤ C₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂}
  (cup : (R' ⋙ T₂) ⋙ (Functor.whiskeringLeft C₁ C₂ C₂).obj R' ⟶
    T₁ ⋙ (Functor.whiskeringRight C₁ C₁ C₂).obj R')

/-- **The unit-then-cup map for transported data.** For `η : M ⟶ R N`, the map
`M ⊗ R G ⟶ R N ⊗ R G ⟶ R(N ⊗ G)` of the transported tensor products and cup product is
invertible exactly when the map `e₂ M ⊗ R'(e₁ G) ⟶ R'(e₁ N) ⊗ R'(e₁ G) ⟶ R'(e₁ N ⊗ e₁ G)` of
the original ones is, the first arrow being `e₂ η` followed by the comparison `c`. -/
theorem isIso_map_comp_transportCupApp_iff {M : D₂} {N : D₁} (η : M ⟶ R.obj N) (G : D₁) :
    IsIso (((transportTensor e₂ T₂).map η).app (R.obj G) ≫ transportCupApp e₁ e₂ c cup N G) ↔
      IsIso ((T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (R'.obj (e₁.functor.obj G)) ≫
        (cup.app (e₁.functor.obj N)).app (e₁.functor.obj G)) := by
  have hnat : (T₂.obj (e₂.functor.obj M)).map (c.hom.app G) ≫
        (T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (R'.obj (e₁.functor.obj G)) =
      (T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (e₂.functor.obj (R.obj G)) ≫
        (T₂.obj (R'.obj (e₁.functor.obj N))).map (c.hom.app G) :=
    (T₂.map (e₂.functor.map η ≫ c.hom.app N)).naturality (c.hom.app G)
  have e : ((transportTensor e₂ T₂).map η).app (R.obj G) ≫ transportCupApp e₁ e₂ c cup N G =
      e₂.inverse.map ((T₂.obj (e₂.functor.obj M)).map (c.hom.app G) ≫
        ((T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (R'.obj (e₁.functor.obj G)) ≫
          (cup.app (e₁.functor.obj N)).app (e₁.functor.obj G)) ≫
        R'.map (e₁.counitInv.app _) ≫ c.inv.app _) ≫ e₂.unitInv.app _ := by
    rw [transportTensor_map_app, transportCupApp, ← Functor.map_comp_assoc]
    congr 2
    have hnat' : ∀ {Z : C₂} (h : (T₂.obj (R'.obj (e₁.functor.obj N))).obj
        (R'.obj (e₁.functor.obj G)) ⟶ Z),
        (T₂.obj (e₂.functor.obj M)).map (c.hom.app G) ≫
          (T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (R'.obj (e₁.functor.obj G)) ≫ h =
        (T₂.map (e₂.functor.map η ≫ c.hom.app N)).app (e₂.functor.obj (R.obj G)) ≫
          (T₂.obj (R'.obj (e₁.functor.obj N))).map (c.hom.app G) ≫ h := fun h => by
      rw [← Category.assoc, hnat, Category.assoc]
    rw [Category.assoc, hnat', Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rfl
  rw [e, isIso_comp_right_iff, isIso_iff_of_reflects_iso, isIso_comp_left_iff,
    ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

end
