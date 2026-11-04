module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.StageFactorization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# The adjoint of a map into the direct image of a stage

Let `π = c ≫ f` with `f : Y ⟶ X` and `c : Y' ⟶ Y`, and let `φ : ℱ ⟶ f_* 𝓛_Y(M)` be a map of sheaves
of modules on `X_étale`. Composing `φ` with the comparison `f_* 𝓛_Y(M) ⟶ π_* 𝓛_{Y'}(M)` and taking
the adjoint along `π` gives a map `π^{-1} ℱ ⟶ 𝓛_{Y'}(M)`; this file identifies it with the inverse
image along `c` of the adjoint `f^{-1} ℱ ⟶ 𝓛_Y(M)` of `φ`, followed by the adjoint of
`𝓛_Y(M) ⟶ c_* 𝓛_{Y'}(M)` and preceded by the comparison `π^{-1} ≅ c^{-1} f^{-1}`.

The formal half is a statement about three adjunctions and an isomorphism `R_c ⋙ R_f ≅ R_π` of
right adjoints, `CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_hom_app`. The geometric half
is that the comparison `f_* 𝓛_Y(M) ⟶ π_* 𝓛_{Y'}(M)` of
`Stacks.EtaleCohomology.locallyConstantPushforwardMap` is `f_*` of
`Stacks.EtaleCohomology.locallyConstantToDirectImage` followed by the composition isomorphism of
direct images, which is checked on sections.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_hom_app` — the formal identity.
* `Stacks.EtaleCohomology.locallyConstantPushforwardMap_eq` — the comparison of direct images of
  locally constant maps is a direct image of the comparison, up to the composition isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {Lf : C ⥤ D} {Rf : D ⥤ C} (Af : Lf ⊣ Rf) {Lc : D ⥤ E} {Rc : E ⥤ D} (Ac : Lc ⊣ Rc)
  {Lπ : C ⥤ E} {Rπ : E ⥤ C} (Aπ : Lπ ⊣ Rπ) (κ : Rc ⋙ Rf ≅ Rπ)

/-- **The adjoint along a composite.** For adjunctions `L_f ⊣ R_f`, `L_c ⊣ R_c`, `L_π ⊣ R_π` and
an isomorphism `κ : R_c ⋙ R_f ≅ R_π`, the `π`-adjoint of `φ ≫ R_f θ ≫ κ` is the comparison
`L_π ≅ L_f ⋙ L_c` followed by `L_c` of the `f`-adjoint of `φ` and the `c`-adjoint of `θ`. -/
theorem homEquiv_symm_comp_map_comp_hom_app {F : C} {G₁ : D} {G₂ : E} (φ : F ⟶ Rf.obj G₁)
    (θ : G₁ ⟶ Rc.obj G₂) :
    (Aπ.homEquiv _ _).symm (φ ≫ Rf.map θ ≫ κ.hom.app G₂) =
      (Aπ.leftAdjointUniq ((Af.comp Ac).ofNatIsoRight κ)).hom.app F ≫
        Lc.map ((Af.homEquiv _ _).symm φ) ≫ (Ac.homEquiv _ _).symm θ := by
  set A' := (Af.comp Ac).ofNatIsoRight κ
  set e := Aπ.leftAdjointUniq A'
  have hcounit : ∀ G : E, e.hom.app (Rπ.obj G) ≫ A'.counit.app G = Aπ.counit.app G :=
    fun G => leftAdjointUniq_hom_app_counit Aπ A' G
  have key : ∀ (k : F ⟶ Rπ.obj G₂),
      (Aπ.homEquiv _ _).symm k = e.hom.app F ≫ (A'.homEquiv _ _).symm k := by
    intro k
    rw [homEquiv_counit, homEquiv_counit, ← hcounit, ← Category.assoc,
      e.hom.naturality k, Category.assoc]
  rw [key]
  congr 1
  have h1 : (A'.homEquiv _ _).symm (φ ≫ Rf.map θ ≫ κ.hom.app G₂) =
      ((Af.comp Ac).homEquiv _ _).symm (φ ≫ Rf.map θ) := by
    rw [← Category.assoc]
    simp [A', ofNatIsoRight, homEquiv_counit]
  rw [h1, comp_homEquiv, Equiv.symm_trans_apply, homEquiv_naturality_right_symm,
    homEquiv_naturality_left_symm]

end CategoryTheory.Adjunction

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) r)) [AddCommGroup M] [Module Λ M]

/-- The comparison for a composite base change, followed by the first projection, is the
morphism `W ×_X Y' ⟶ W ×_X Y` induced by `c`. -/
theorem baseChangeComp'_left_fst_eq_pullbackMap {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (π : Y' ⟶ X)
    (c : Y' ⟶ Y) (hc : c ≫ f = π) (W : X.Etale) :
    ((smallEtaleBaseChangeComp' c f π hc.symm).hom.app W).left ≫
      pullback.fst ((smallEtaleBaseChange f).obj W).hom c =
      pullback.map W.hom π W.hom f (𝟙 _) c (𝟙 _) (by simp) (by simp [hc]) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((smallEtaleBaseChangeComp'_fst_fst c f π hc.symm W).trans
        (by simp only [pullback.map, Category.comp_id]; exact (pullback.lift_fst _ _ _).symm))
  · exact (Category.assoc _ _ _).trans
      ((smallEtaleBaseChange_fst_snd c f _).trans
        (by simp only [pullback.map, Category.comp_id]; exact (pullback.lift_snd _ _ _).symm))

/-- **The comparison of direct images of locally constant maps is a direct image.** For
`c : Y' ⟶ Y` over `f : Y ⟶ X` with composite `π`, the comparison
`f_* 𝓛_Y(M) ⟶ π_* 𝓛_{Y'}(M)` is `f_*` of `𝓛_Y(M) ⟶ c_* 𝓛_{Y'}(M)` followed by the composition
isomorphism `f_* c_* ≅ π_*`. Both pull a locally constant map on `W ×_X Y` back to `W ×_X Y'`
along the same morphism. -/
theorem locallyConstantPushforwardMap_eq {X Y Y' : Scheme.{u}} (f : Y ⟶ X) (π : Y' ⟶ X)
    (c : Y' ⟶ Y) (hc : c ≫ f = π) :
    locallyConstantPushforwardMap Λ M f π c hc =
      (etaleModuleDirectImage.{u, r} Λ f).map (locallyConstantToDirectImage Λ M c) ≫
        (etaleModuleDirectImageComp.{u, r} Λ c f π hc.symm).hom.app
          (smallEtaleLocallyConstantMapsModuleSheaf.{u, r} Λ Y' M) := by
  apply Sheaf.hom_ext
  ext W s
  have hmap := baseChangeComp'_left_fst_eq_pullbackMap f π c hc W.unop
  let s' : LocallyConstant ((smallEtaleBaseChange f).obj W.unop).left M := s
  apply LocallyConstant.ext
  intro y
  change s' ((pullback.map W.unop.hom π W.unop.hom f (𝟙 _) c (𝟙 _) (by simp) (by simp [hc])) y) =
    s' ((pullback.fst ((smallEtaleBaseChange f).obj W.unop).hom c)
      (((smallEtaleBaseChangeComp' c f π hc.symm).hom.app W.unop).left y))
  rw [← hmap]
  rfl

end Stacks.EtaleCohomology

end
