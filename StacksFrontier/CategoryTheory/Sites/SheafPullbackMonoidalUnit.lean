module

public import StacksFrontier.CategoryTheory.Sites.SheafPullbackMonoidal
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The unit of the monoidal inverse image of sheaves

Let `G : C ⥤ D` be a continuous functor of sites for which the inverse image
`G.sheafPullback A J K` is monoidal (`CategoryTheory.Functor.sheafPullbackMonoidal`), and let `T`
be a terminal object of `C` with `G T` terminal in `D`. Both `constantSheaf J A ⋙ G.sheafPullback`
and `constantSheaf K A` are left adjoint to the sections over `G T`, so they are canonically
isomorphic. The lax unit `ε : 𝟙 ⟶ G.sheafPullback 𝟙` of the monoidal inverse image is this
canonical comparison at the unit `𝟙_ A` (`CategoryTheory.Functor.sheafPullbackMonoidal_ε`).

This identifies the unit of the monoidal structure used for the Frobenius equivariance of cup
products in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) with the
comparison of constant sheaves under inverse image.

## Main results

* `CategoryTheory.Functor.sheafPullbackMonoidal_ε`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Limits MonoidalCategory Opposite

variable {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (A : Type*) [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension G.op P]
  [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).obj M)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).flip.obj M)]

attribute [local instance] Sheaf.monoidalCategory lanMonoidal

/-- **The unit of the monoidal inverse image of sheaves is the comparison of constant sheaves.**
For `T` terminal in `C` with `G T` terminal in `D`, the lax unit `𝟙 ⟶ G.sheafPullback 𝟙` is the
canonical isomorphism between the two left adjoints `constantSheaf K A` and
`constantSheaf J A ⋙ G.sheafPullback` of the sections over `G T`, at the unit `𝟙_ A`. -/
theorem sheafPullbackMonoidal_ε {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T)) :
    letI := sheafPullbackMonoidal G A J K
    LaxMonoidal.ε (G.sheafPullback A J K) =
      (((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K)).leftAdjointUniq
        (constantSheafAdj K A hGT)).inv.app (𝟙_ A) := by
  let := sheafPullbackMonoidal G A J K
  let e := presheafToSheafCompSheafPullbackIso G A J K
  let P : Cᵒᵖ ⥤ A := 𝟙_ (Cᵒᵖ ⥤ A)
  let adj1' := (sheafificationAdjunction J A).comp (G.sheafAdjunctionContinuous A J K)
  let adj2' := ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)).ofNatIsoRight
    (Iso.refl (sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj G.op))
  have h0 : LaxMonoidal.ε (G.sheafPullback A J K) =
      (presheafToSheaf K A).map (LaxMonoidal.ε (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))) ≫
        e.inv.app P := by
    have h1 : LaxMonoidal.ε (G.sheafPullback A J K) =
        LaxMonoidal.ε (G.op.lan ⋙ presheafToSheaf K A) ≫ e.inv.app P ≫
          (G.sheafPullback A J K).map (OplaxMonoidal.η (presheafToSheaf J A)) := rfl
    have hη : OplaxMonoidal.η (presheafToSheaf J A) = 𝟙 _ := rfl
    have hε : LaxMonoidal.ε (presheafToSheaf K A) = 𝟙 _ := rfl
    rw [h1, hη, CategoryTheory.Functor.map_id, LaxMonoidal.comp_ε, hε]
    exact (Category.id_comp _ =≫ _).trans (congrArg (_ ≫ ·) (Category.comp_id _))
  -- the transpose of `e⁻¹` along `L.lan ⊣ (G.op ⋙ -)` and sheafification
  have hv : (G.op.lanAdjunction A).homEquiv _ _
      ((sheafificationAdjunction K A).homEquiv _ _ (e.inv.app P)) = adj1'.unit.app P := by
    have h : adj2'.homEquiv P _ (e.inv.app P ≫ 𝟙 _) = adj1'.homEquiv P _ (𝟙 _) :=
      Adjunction.homEquiv_leftAdjointUniq_inv_app_comp adj1' adj2' P (𝟙 _)
    simp only [adj2', Category.comp_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv, Adjunction.homEquiv_id, Equiv.trans_apply, Iso.refl_hom,
      NatTrans.id_app] at h
    simpa using h
  have hR := Adjunction.homEquiv_leftAdjointUniq_inv_app_comp
    ((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K))
    (constantSheafAdj K A hGT) (𝟙_ A) (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id] at hR
  apply ((constantSheafAdj K A hGT).homEquiv _ _).injective
  refine Eq.trans ?_ hR.symm
  refine Eq.trans (congrArg ((constantSheafAdj K A hGT).homEquiv (𝟙_ A) _) h0) ?_
  have hu : (LaxMonoidal.ε (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))).app (op (G.obj T)) =
      (G.op.lanUnit.app P).app (op T) := lanMonoidal_ε_app G.op (op T)
  have hl := congrArg (fun φ => φ.app (op T)) hv
  simp only [Adjunction.homEquiv_unit, lanAdjunction_unit, adj1', Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, NatTrans.comp_app] at hl
  have hn := NatTrans.congr_app
    (toSheafify_naturality K (LaxMonoidal.ε (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))))
    (op (G.obj T))
  simp only [NatTrans.comp_app] at hn
  refine (Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply K A hGT (𝟙_ A) _ _).trans ?_
  rw [Adjunction.comp_unit_app, Stacks.ConstantSheaf.constantSheafAdj_unit_app]
  refine Eq.trans ?_ (hl.trans ?_)
  · calc _ = ((toSheafify K _).app (op (G.obj T)) ≫
          (sheafifyMap K (LaxMonoidal.ε (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)))).app
            (op (G.obj T))) ≫ (e.inv.app P).hom.app (op (G.obj T)) := by
          simp [sheafifyMap]
          rfl
      _ = (G.op.lanUnit.app P).app (op T) ≫
            (toSheafify K (G.op.lan.obj P)).app (op (G.obj T)) ≫
            (e.inv.app P).hom.app (op (G.obj T)) := by
          rw [← hn, hu, Category.assoc]
  · rfl

end CategoryTheory.Functor

end
