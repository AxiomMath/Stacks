module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantGlobalSections

/-!
# `Γ(Y_K, -|_{Y_K})` on section-wise bilinear pairings

Let `k` be a field, `K/k` a separable algebraic extension and `Y` a quasi-compact and
quasi-separated scheme over `k`. A pairing `b : G₁ × G₂ ⟶ G₃` of sheaves of modules on `Y_étale`,
given section-wise by biadditive maps `b_U : G₁(U) × G₂(U) ⟶ G₃(U)` natural in `U`, induces a
biadditive pairing of global sections over `Y_K`
`Γ(Y_K, G₁|_{Y_K}) × Γ(Y_K, G₂|_{Y_K}) ⟶ Γ(Y_K, G₃|_{Y_K})`: every global section comes from a
finite stage `Y_E`, `E ⊆ K` a finite subextension (Stacks 09YQ in degree zero), two sections
coming from `Y_E` are paired by `b` at `Y_E`, and the result does not depend on the stage because
two sections of `G` over `Y_E` with the same pull back to `Y_K` agree over a later stage.

The pairing is equivariant for the Galois actions: `σ ∈ Aut_k(K)` carries the section pulled back
from `Y_E` to the section pulled back from `Y_{σ(E)}` along the isomorphism
`Y_{σ(E)} ≅ Y_E` induced by `σ`, and `b` is natural along that morphism of étale `Y`-schemes.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSectionPairing`: a section-wise biadditive pairing of sheaves of
  modules on a small étale site, natural in the open.
* `Stacks.EtaleCohomology.galoisGlobalSectionsPairing`: the induced pairing on
  `Γ^Gal = Γ(Y_K, -|_{Y_K})`.

## Main results

* `Stacks.EtaleCohomology.ΓRes_galoisGlobalSectionsPairing`: on sections pulled back from a
  finite stage it is `b` at that stage.
* `Stacks.EtaleCohomology.galoisGlobalSectionsPairing_galoisAction`: Galois equivariance.
* `Stacks.EtaleCohomology.galoisGlobalSectionsPairing_naturality`: naturality in the sheaves.
* `Stacks.EtaleCohomology.galoisGlobalSectionsPairing_smul_left_eq_smul_right`: balancing.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **A section-wise pairing of étale sheaves of modules**: biadditive maps
`G₁(U) × G₂(U) ⟶ G₃(U)` for every étale `X`-scheme `U`, natural in `U`. The three sheaves may be
modules over different rings; only the additive structures are paired. -/
structure EtaleSectionPairing {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃] {X : Scheme.{u}}
    (G₁ : EtaleModules.{u, 0} Λ₁ X) (G₂ : EtaleModules.{u, 0} Λ₂ X)
    (G₃ : EtaleModules.{u, 0} Λ₃ X) where
  /-- The pairing over the étale `X`-scheme `U`. -/
  app : ∀ U : X.Etaleᵒᵖ, G₁.obj.obj U →+ G₂.obj.obj U →+ G₃.obj.obj U
  /-- The pairings commute with restriction. -/
  naturality : ∀ {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (a : G₁.obj.obj U) (c : G₂.obj.obj U),
    G₃.obj.map f (app U a c) = app V (G₁.obj.map f a) (G₂.obj.map f c)

/-- Restriction to the final object of the small étale site is bijective on global sections. -/
theorem ΓRes_etaleMkId_bijective (Λ : Type) [Ring Λ] {T : Scheme.{u}}
    (H : EtaleModules.{u, 0} Λ T) :
    Function.Bijective ⇑(H.ΓRes (op (Scheme.Etale.mk (𝟙 T)))) := by
  rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general (isTerminalEtaleMkId T) H]
  exact ConcreteCategory.bijective_of_isIso _

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

/-! ### Sections pulled back from finite stages -/

section Stages

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K] [Algebra.IsSeparable k K] (G : EtaleModules.{u, 0} Λ Y.left)

omit [Algebra.IsSeparable k K] in
/-- **Pulling back a restricted section.** For a morphism `φ : W' ⟶ W` of étale `Y`-schemes and
`r' : Y_K ⟶ W'` over `Y`, the section `a ∈ G(W)` pulled back along `r' ≫ φ` is the restriction
`φ^* a ∈ G(W')` pulled back along `r'`. -/
theorem map_smallEtaleBaseChangeLift_comp_moduleUnitSection {W W' : Y.left.Etale} (φ : W' ⟶ W)
    (a : G.obj.obj (op W)) {r' : fieldBaseChange Y K ⟶ W'.left}
    (hr' : r' ≫ W'.hom = fieldBaseChangeProj Y K)
    (hr : (r' ≫ φ.left) ≫ W.hom = fieldBaseChangeProj Y K) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W (r' ≫ φ.left) hr).op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a) =
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map
        (smallEtaleBaseChangeLift (fieldBaseChangeProj Y K) W' r' hr').op
        (moduleUnitSection Λ (fieldBaseChangeProj Y K) G (G.obj.map φ.op a)) := by
  let p := fieldBaseChangeProj Y K
  let H := (etaleModuleInverseImage.{u, 0} Λ p).obj G
  have hu : moduleUnitSection Λ p G (G.obj.map φ.op a) =
      H.obj.map ((smallEtaleBaseChange p).map φ).op (moduleUnitSection Λ p G a) :=
    ConcreteCategory.congr_hom (((etaleModuleInverseImageAdj.{u, 0} Λ p).unit.app G).hom.naturality
      φ.op) a
  have hl : smallEtaleBaseChangeLift p W' r' hr' ≫ (smallEtaleBaseChange p).map φ =
      smallEtaleBaseChangeLift p W (r' ≫ φ.left) hr := by
    apply smallEtaleBaseChange_hom_ext
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ φ.left) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _).symm
  rw [hu, ← hl, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

omit [Algebra.IsSeparable k K] in
/-- Two finite subextensions lie in a third, their compositum. -/
theorem exists_fext_le_le (i j : FExt k K) : ∃ l : FExt k K, i ≤ l ∧ j ≤ l := by
  have := i.2
  have := j.2
  exact ⟨⟨i.1 ⊔ j.1, IntermediateField.finiteDimensional_sup i.1 j.1⟩,
    (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩

/-- The restriction of a section of `G` from the stage `Y_E` to a larger stage `Y_{E'}`. -/
abbrev fieldStageRes {i j : FExt k K} (h : i ≤ j) :
    G.obj.obj (op ((fieldStageSystem Y K).obj (op i))) ⟶
      G.obj.obj (op ((fieldStageSystem Y K).obj (op j))) :=
  G.obj.map ((fieldStageSystem Y K).map (homOfLE h).op).op

/-- Restricting in two steps is restricting in one. -/
theorem fieldStageRes_fieldStageRes {i j l : FExt k K} (h : i ≤ j) (h' : j ≤ l)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageRes Λ Y K G h' (fieldStageRes Λ Y K G h a) =
      fieldStageRes Λ Y K G (h.trans h') a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← Functor.map_comp, ← op_comp]
  rfl

/-- **Stage sections are compatible with the transition maps**: a section over `Y_E` and its
restriction to `Y_{E'}` have the same pull back to `Y_K`. -/
theorem fieldStageSection_fieldStageRes {i j : FExt k K} (h : i ≤ j)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageSection Λ Y K G j (fieldStageRes Λ Y K G h a) = fieldStageSection Λ Y K G i a := by
  have hc : fieldStageProj Y K (op j) ≫ ((fieldStageSystem Y K).map (homOfLE h).op).left =
      fieldStageProj Y K (op i) :=
    (fieldStageCone Y K).w (homOfLE h).op
  refine (map_smallEtaleBaseChangeLift_comp_moduleUnitSection Λ Y K G _ a
    (fieldStageCone_π_comp_hom Y K (op j))
    ((congrArg (· ≫ _) hc).trans (fieldStageCone_π_comp_hom Y K (op i)))).symm.trans ?_
  exact congrArg (fun t =>
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map (Quiver.Hom.op t)
      (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a))
    (smallEtaleBaseChangeLift_congr _ _ hc _ _)

/-- Stage sections are additive. -/
theorem fieldStageSection_add (i : FExt k K)
    (a a' : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageSection Λ Y K G i (a + a') =
      fieldStageSection Λ Y K G i a + fieldStageSection Λ Y K G i a' := by
  dsimp only [fieldStageSection, moduleUnitSection]
  rw [map_add]
  exact map_add _ _ _

/-- Stage sections are `Λ`-linear. -/
theorem fieldStageSection_smul (i : FExt k K) (r : Λ)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageSection Λ Y K G i (r • a) = r • fieldStageSection Λ Y K G i a := by
  dsimp only [fieldStageSection, moduleUnitSection]
  rw [map_smul]
  exact map_smul _ _ _

/-- **Two sections over a stage with the same pull back to `Y_K` agree over a later stage**
(the injectivity half of Stacks 09YQ in degree zero). -/
theorem exists_fieldStageRes_eq_of_fieldStageSection_eq [QuasiCompact Y.hom]
    [QuasiSeparated Y.hom] {i : FExt k K}
    (a a' : G.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (h : fieldStageSection Λ Y K G i a = fieldStageSection Λ Y K G i a') :
    ∃ (j : FExt k K) (hij : i ≤ j), fieldStageRes Λ Y K G hij a = fieldStageRes Λ Y K G hij a' := by
  have : CompactSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    compactSpace_fieldStage Y K (⊥ : FExt k K)
  have : QuasiSeparatedSpace ((fieldStageSystem Y K).obj (op ⊥)).left :=
    quasiSeparatedSpace_fieldStage Y K (⊥ : FExt k K)
  have : ∀ {i j : (FExt k K)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((fieldStageSystem Y K).map a).left :=
    fun a => isAffineHom_fieldStageMap Y K a
  let p := fieldBaseChangeProj Y K
  let H := (etaleModuleInverseImage.{u, 0} Λ p).obj G
  let Gs := (etaleModuleUnderlyingSets Λ Y.left).obj G
  let eF := etaleModuleInverseImageForgetIso Λ p G
  let eU := Adjunction.leftAdjointUniq (smallEtaleInverseImageAdjunction.{u, 0} p)
    (etaleTypeInverseImageAdj p)
  let T0 := op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))
  let W := (fieldStageSystem Y K).obj (op i)
  let t := smallEtaleBaseChangeLift p W (fieldStageProj Y K (op i))
    (fieldStageCone_π_comp_hom Y K (op i))
  let T := (etaleTypeInverseImage p).obj Gs
  let Hs := (etaleModuleUnderlyingSets Λ _).obj H
  let Φ := fun y => eF.hom.hom.app T0 ((eU.hom.app Gs).hom.app T0 y)
  have key : ∀ x : G.obj.obj (op W), Φ (EtaleLimitSections.limitSections (fieldStageSystem Y K)
      (fieldStageCone Y K) (fieldStageCone_π_comp_hom Y K) Gs (op i) x) =
        fieldStageSection Λ Y K G i x := fun x => by
    have h2 := type_hom_congr ((eU.hom.app Gs).hom.naturality t.op)
      (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app Gs).hom.app (op W) x)
    have h3 := type_hom_congr (congrArg (fun φ : Gs ⟶
        ((smallEtaleBaseChange p).sheafPushforwardContinuous (Type (u + 1))
          Y.left.smallEtaleTopology (fieldBaseChange Y K).smallEtaleTopology).obj
          ((etaleTypeInverseImage p).obj Gs) => φ.hom.app (op W))
      (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleInverseImageAdjunction.{u, 0} p)
        (etaleTypeInverseImageAdj p) Gs)) x
    have h4 := type_hom_congr (eF.hom.hom.naturality t.op)
      (((etaleTypeInverseImageAdj p).unit.app Gs).hom.app (op W) x)
    have h5 := etaleModuleInverseImageForgetIso_hom_typeUnitSection Λ p G (V := W) x
    exact (congrArg (eF.hom.hom.app T0) (h2.trans (congrArg (T.obj.map t.op) h3))).trans
      (h4.trans (congrArg (Hs.obj.map t.op) h5))
  have hΦ : ∀ y y', Φ y = Φ y' → y = y' := fun y y' hy => by
    have b1 := fun y => type_hom_congr (congrArg
      (fun φ : (smallEtaleInverseImage.{u, 0} p).obj Gs ⟶
          (smallEtaleInverseImage.{u, 0} p).obj Gs =>
        φ.hom.app T0) (eU.hom_inv_id_app Gs)) y
    have b2 := fun y => type_hom_congr (congrArg
      (fun φ : (etaleTypeInverseImage p).obj Gs ⟶ (etaleTypeInverseImage p).obj Gs =>
        φ.hom.app T0) eF.hom_inv_id) y
    have hy' := congrArg (fun w => (eU.inv.app Gs).hom.app T0 (eF.inv.hom.app T0 w)) hy
    exact (b1 y).symm.trans ((congrArg ((eU.inv.app Gs).hom.app T0) (b2 _).symm).trans
      (hy'.trans ((congrArg ((eU.inv.app Gs).hom.app T0) (b2 _)).trans (b1 y'))))
  obtain ⟨j, d, hd⟩ := (EtaleLimitSections.limitSections_colimit (fieldStageSystem Y K)
    (fieldStageCone Y K) (fieldStageConeIsLimit Y K) (fieldStageCone_π_comp_hom Y K) Gs).2 i a a'
    (hΦ _ _ ((key a).trans (h.trans (key a').symm)))
  exact ⟨j, d, hd⟩

/-- **Two stage sections with the same pull back to `Y_K` agree over a stage above any given
common upper bound.** -/
theorem exists_fieldStageRes_eq_of_fieldStageSection_eq_of_le [QuasiCompact Y.hom]
    [QuasiSeparated Y.hom] {i j l : FExt k K} (hi : i ≤ l) (hj : j ≤ l)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (c : G.obj.obj (op ((fieldStageSystem Y K).obj (op j))))
    (h : fieldStageSection Λ Y K G i a = fieldStageSection Λ Y K G j c) :
    ∃ (m : FExt k K) (hlm : l ≤ m), fieldStageRes Λ Y K G (hi.trans hlm) a =
      fieldStageRes Λ Y K G (hj.trans hlm) c := by
  obtain ⟨m, hlm, hm⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq Λ Y K G
    (fieldStageRes Λ Y K G hi a) (fieldStageRes Λ Y K G hj c)
    ((fieldStageSection_fieldStageRes Λ Y K G hi a).trans
      (h.trans (fieldStageSection_fieldStageRes Λ Y K G hj c).symm))
  exact ⟨m, hlm, (fieldStageRes_fieldStageRes Λ Y K G hi hlm a).symm.trans
    (hm.trans (fieldStageRes_fieldStageRes Λ Y K G hj hlm c))⟩

/-- A global section pulled back from a stage is pulled back from every larger stage. -/
theorem ΓRes_eq_fieldStageSection_of_le {i j : FExt k K} (h : i ≤ j)
    {z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)}
    {a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (hz : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z = fieldStageSection Λ Y K G i a) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z =
      fieldStageSection Λ Y K G j (fieldStageRes Λ Y K G h a) :=
  hz.trans (fieldStageSection_fieldStageRes Λ Y K G h a).symm

/-- A sum of global sections pulled back from the stage `Y_E` is pulled back from the sum of the
restrictions to a larger stage. -/
private theorem ΓRes_add_eq_fieldStageSection {i j : FExt k K} (h : i ≤ j)
    {z z' : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)}
    {a a' : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (hz : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z = fieldStageSection Λ Y K G i a)
    (hz' : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z' = fieldStageSection Λ Y K G i a') :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) (z + z') =
      fieldStageSection Λ Y K G j (fieldStageRes Λ Y K G h a + fieldStageRes Λ Y K G h a') := by
  rw [map_add, ΓRes_eq_fieldStageSection_of_le Λ Y K G h hz,
    ΓRes_eq_fieldStageSection_of_le Λ Y K G h hz', fieldStageSection_add]

/-- **Stage sections are natural in the sheaf.** -/
theorem ΓRes_map_eq_fieldStageSection {G' : EtaleModules.{u, 0} Λ Y.left} (v : G ⟶ G')
    {i : FExt k K}
    {z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)}
    {a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (hz : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z = fieldStageSection Λ Y K G i a) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G').ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).map v) z) =
      fieldStageSection Λ Y K G' i (v.hom.app _ a) := by
  let p := fieldBaseChangeProj Y K
  let W := (fieldStageSystem Y K).obj (op i)
  let t := smallEtaleBaseChangeLift p W (fieldStageProj Y K (op i))
    (fieldStageCone_π_comp_hom Y K (op i))
  have h1 := ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality
    ((etaleModuleInverseImage.{u, 0} Λ p).map v) (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))) z
  have h2 := ConcreteCategory.congr_hom
    (((etaleModuleInverseImage.{u, 0} Λ p).map v).hom.naturality t.op) (moduleUnitSection Λ p G a)
  have h3 : ((etaleModuleInverseImage.{u, 0} Λ p).map v).hom.app _ (moduleUnitSection Λ p G a) =
      moduleUnitSection Λ p G' (v.hom.app _ a) :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op W))
      ((etaleModuleInverseImageAdj.{u, 0} Λ p).unit.naturality v)) a).symm
  exact h1.trans ((congrArg (((etaleModuleInverseImage.{u, 0} Λ p).map v).hom.app _) hz).trans
    (h2.trans (congrArg (((etaleModuleInverseImage.{u, 0} Λ p).obj G').obj.map t.op) h3)))

end Stages

/-! ### The Galois action on stage sections -/

section Galois

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u)
  [Field K] [Algebra k K] [Algebra.IsSeparable k K] (G : EtaleModules.{u, 0} Λ Y.left)

/-- The finite subextension `σ(E)` of `K` for a finite subextension `E` and `σ ∈ Aut_k(K)`. -/
def fextMap (σ : K ≃ₐ[k] K) (E : FExt k K) : FExt k K :=
  ⟨E.1.map σ.toAlgHom, by
    have := E.2
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap E.1 σ.toAlgHom).toLinearEquiv⟩

/-- `σ` restricted to `E ≅ σ(E)`. -/
def fextMapAlgEquiv (σ : K ≃ₐ[k] K) (E : FExt k K) : E.1 ≃ₐ[k] (fextMap K σ E).1 :=
  IntermediateField.equivMap E.1 σ.toAlgHom

omit [Algebra.IsSeparable k K] in
/-- `Spec σ(E) ⟶ Spec E ⟶ Spec k` is `Spec σ(E) ⟶ Spec k`. -/
theorem spectrumMap_fextMap_comp (σ : K ≃ₐ[k] K) (E : FExt k K) :
    Spec.map (CommRingCat.ofHom (fextMapAlgEquiv K σ E).toAlgHom.toRingHom) ≫
      spectrumMap k E.1 = spectrumMap k (fextMap K σ E).1 := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact congrArg Subtype.val ((fextMapAlgEquiv K σ E).commutes x)

/-- The isomorphism `Y_{σ(E)} ⟶ Y_E` induced by `σ : E ≅ σ(E)`. -/
def fextMapStageMap (σ : K ≃ₐ[k] K) (E : FExt k K) :
    pullback (spectrumMap k (fextMap K σ E).1) Y.hom ⟶ pullback (spectrumMap k E.1) Y.hom :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom
      (fextMapAlgEquiv K σ E).toAlgHom.toRingHom)) (pullback.snd _ _) (by
    rw [Category.assoc, spectrumMap_fextMap_comp, pullback.condition])

/-- The morphism `Y_{σ(E)} ⟶ Y_E` of étale `Y`-schemes induced by `σ`. -/
def fieldStageGaloisMap (σ : K ≃ₐ[k] K) (E : FExt k K) :
    (fieldStageSystem Y K).obj (op (fextMap K σ E)) ⟶ (fieldStageSystem Y K).obj (op E) :=
  MorphismProperty.Over.homMk (fextMapStageMap Y K σ E) (pullback.lift_snd _ _ _) trivial

/-- **`id_Y × Spec σ` followed by the projection to `Y_E` is the projection to `Y_{σ(E)}`
followed by `Y_{σ(E)} ≅ Y_E`.** -/
theorem galoisBaseChange_comp_fieldStageProj_eq (σ : K ≃ₐ[k] K) (E : FExt k K) :
    galoisBaseChange Y K σ ≫ fieldStageProj Y K (op E) =
      fieldStageProj Y K (op (fextMap K σ E)) ≫ (fieldStageGaloisMap Y K σ E).left := by
  apply pullback.hom_ext
  · show _ = fieldStageProj Y K (op (fextMap K σ E)) ≫ fextMapStageMap Y K σ E ≫ pullback.fst _ _
    rw [Category.assoc, fieldStageProj_fst, galoisBaseChange_comp_snd_assoc, fextMapStageMap,
      pullback.lift_fst, fieldStageProj_fst_assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  · show _ = fieldStageProj Y K (op (fextMap K σ E)) ≫ fextMapStageMap Y K σ E ≫ pullback.snd _ _
    rw [Category.assoc, fieldStageProj_snd, galoisBaseChange_comp_fst, fextMapStageMap,
      pullback.lift_snd, fieldStageProj_snd]

/-- **The Galois action on a stage section**: if a global section `z` of `G|_{Y_K}` is pulled back
from `a ∈ G(Y_E)`, then `σ · z` is pulled back from the restriction of `a` to `Y_{σ(E)}` along
`Y_{σ(E)} ≅ Y_E`. -/
theorem ΓRes_fieldBaseChangeGlobalSectionsGaloisAction_fieldStageSection (σ : K ≃ₐ[k] K)
    {i : FExt k K}
    {z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G)}
    {a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (hz : ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z = fieldStageSection Λ Y K G i a) :
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        ((fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y K σ G) z) =
      fieldStageSection Λ Y K G (fextMap K σ i) (G.obj.map (fieldStageGaloisMap Y K σ i).op a) := by
  have hc := galoisBaseChange_comp_fieldStageProj_eq Y K σ i
  rw [ΓRes_fieldBaseChangeGlobalSectionsGaloisAction Λ Y K σ G a _ z hz]
  refine (congrArg (fun t =>
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).obj.map (Quiver.Hom.op t)
      (moduleUnitSection Λ (fieldBaseChangeProj Y K) G a))
    (smallEtaleBaseChangeLift_congr _ _ hc _ (by
      rw [← hc]
      exact galoisBaseChange_comp_lies_over Y K σ (fieldStageCone_π_comp_hom Y K (op i))))).trans ?_
  exact map_smallEtaleBaseChangeLift_comp_moduleUnitSection Λ Y K G _ a
    (fieldStageCone_π_comp_hom Y K (op (fextMap K σ i))) _

end Galois

/-! ### The pairing -/

section Pairing

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
  {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃] {G₁ : EtaleModules.{u, 0} Λ₁ Y.left}
  {G₂ : EtaleModules.{u, 0} Λ₂ Y.left} {G₃ : EtaleModules.{u, 0} Λ₃ Y.left}
  (b : EtaleSectionPairing G₁ G₂ G₃)

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- `b` commutes with restriction between stages. -/
theorem EtaleSectionPairing.app_fieldStageRes {i j : FExt k K} (h : i ≤ j)
    (a : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    b.app _ (fieldStageRes Λ₁ Y K G₁ h a) (fieldStageRes Λ₂ Y K G₂ h c) =
      fieldStageRes Λ₃ Y K G₃ h (b.app _ a c) :=
  (b.naturality _ a c).symm

/-- **The stage pairing does not depend on the stage**: pairing at `Y_E` and at `Y_{E'}` sections
with the same pull backs gives sections with the same pull back. -/
theorem fieldStageSection_app_eq {i j : FExt k K}
    (a₁ : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (a₂ : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (c₁ : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op j))))
    (c₂ : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op j))))
    (h₁ : fieldStageSection Λ₁ Y K G₁ i a₁ = fieldStageSection Λ₁ Y K G₁ j c₁)
    (h₂ : fieldStageSection Λ₂ Y K G₂ i a₂ = fieldStageSection Λ₂ Y K G₂ j c₂) :
    fieldStageSection Λ₃ Y K G₃ i (b.app _ a₁ a₂) =
      fieldStageSection Λ₃ Y K G₃ j (b.app _ c₁ c₂) := by
  obtain ⟨l, hil, hjl⟩ := exists_fext_le_le K i j
  obtain ⟨m₁, hlm₁, hm₁⟩ :=
    exists_fieldStageRes_eq_of_fieldStageSection_eq_of_le Λ₁ Y K G₁ hil hjl a₁ c₁ h₁
  obtain ⟨m, hm₁m, hm⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq_of_le Λ₂ Y K G₂
    (hil.trans hlm₁) (hjl.trans hlm₁) a₂ c₂ h₂
  have hm₁' := congrArg (fieldStageRes Λ₁ Y K G₁ hm₁m) hm₁
  rw [fieldStageRes_fieldStageRes, fieldStageRes_fieldStageRes] at hm₁'
  rw [← fieldStageSection_fieldStageRes Λ₃ Y K G₃ ((hil.trans hlm₁).trans hm₁m),
    ← fieldStageSection_fieldStageRes Λ₃ Y K G₃ ((hjl.trans hlm₁).trans hm₁m),
    ← EtaleSectionPairing.app_fieldStageRes, ← EtaleSectionPairing.app_fieldStageRes, hm₁', hm]

/-- The pairing of global sections, read over the final object `Y_K` of the site: represent both
sections at a common finite stage and pair them there. -/
def galoisGlobalSectionsPairingAux
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃).obj.obj
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) :=
  let h₁ := exists_fieldStageSection_eq Λ₁ Y K G₁ z₁
  let h₂ := exists_fieldStageSection_eq Λ₂ Y K G₂ z₂
  let hj := exists_fext_le_le K h₁.choose h₂.choose
  fieldStageSection Λ₃ Y K G₃ hj.choose (b.app _
    (fieldStageRes Λ₁ Y K G₁ hj.choose_spec.1 h₁.choose_spec.choose)
    (fieldStageRes Λ₂ Y K G₂ hj.choose_spec.2 h₂.choose_spec.choose))

/-- The value of the auxiliary pairing on sections pulled back from a common stage. -/
theorem galoisGlobalSectionsPairingAux_eq {i : FExt k K}
    {z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁)}
    {z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)}
    {a₁ : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    {a₂ : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (h₁ : ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₁ = fieldStageSection Λ₁ Y K G₁ i a₁)
    (h₂ : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₂ = fieldStageSection Λ₂ Y K G₂ i a₂) :
    galoisGlobalSectionsPairingAux Y K b z₁ z₂ = fieldStageSection Λ₃ Y K G₃ i (b.app _ a₁ a₂) := by
  let e₁ := exists_fieldStageSection_eq Λ₁ Y K G₁ z₁
  let e₂ := exists_fieldStageSection_eq Λ₂ Y K G₂ z₂
  let hj := exists_fext_le_le K e₁.choose e₂.choose
  refine (fieldStageSection_app_eq Y K b _ _ _ _ ?_ ?_).symm
  · exact h₁.symm.trans (ΓRes_eq_fieldStageSection_of_le Λ₁ Y K G₁ hj.choose_spec.1
      e₁.choose_spec.choose_spec)
  · exact h₂.symm.trans (ΓRes_eq_fieldStageSection_of_le Λ₂ Y K G₂ hj.choose_spec.2
      e₂.choose_spec.choose_spec)

/-- The pairing of global sections, as a function. -/
def galoisGlobalSectionsPairingFun
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    (etaleModuleGlobalSections.{u, 0} Λ₃ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃) :=
  Function.surjInv (ΓRes_etaleMkId_bijective Λ₃ _).2 (galoisGlobalSectionsPairingAux Y K b z₁ z₂)

/-- The pairing function on sections pulled back from a common stage. -/
theorem ΓRes_galoisGlobalSectionsPairingFun {i : FExt k K}
    {z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁)}
    {z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)}
    {a₁ : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    {a₂ : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (h₁ : ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₁ = fieldStageSection Λ₁ Y K G₁ i a₁)
    (h₂ : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₂ = fieldStageSection Λ₂ Y K G₂ i a₂) :
    ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (galoisGlobalSectionsPairingFun Y K b z₁ z₂) =
      fieldStageSection Λ₃ Y K G₃ i (b.app _ a₁ a₂) :=
  (Function.surjInv_eq (ΓRes_etaleMkId_bijective Λ₃ _).2 _).trans
    (galoisGlobalSectionsPairingAux_eq Y K b h₁ h₂)

/-- Two global sections are pulled back from a common stage. -/
theorem exists_fieldStageSection_eq₂ {Λ Λ' : Type} [Ring Λ] [Ring Λ']
    {G : EtaleModules.{u, 0} Λ Y.left} {G' : EtaleModules.{u, 0} Λ' Y.left}
    (z : (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G))
    (z' : (etaleModuleGlobalSections.{u, 0} Λ' (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y K)).obj G')) (l : FExt k K) :
    ∃ (i : FExt k K) (_ : l ≤ i) (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
      (a' : G'.obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj G).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z = fieldStageSection Λ Y K G i a ∧
        ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y K)).obj G').ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z' =
          fieldStageSection Λ' Y K G' i a' := by
  obtain ⟨i, a, ha⟩ := exists_fieldStageSection_eq Λ Y K G z
  obtain ⟨i', a', ha'⟩ := exists_fieldStageSection_eq Λ' Y K G' z'
  obtain ⟨j, hij, hi'j⟩ := exists_fext_le_le K i i'
  obtain ⟨m, hlm, hjm⟩ := exists_fext_le_le K l j
  exact ⟨m, hlm, _, _, ΓRes_eq_fieldStageSection_of_le Λ Y K G (hij.trans hjm) ha,
    ΓRes_eq_fieldStageSection_of_le Λ' Y K G' (hi'j.trans hjm) ha'⟩

/-- The pairing function is additive in the second variable. -/
theorem galoisGlobalSectionsPairingFun_add_right
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ z₂' : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairingFun Y K b z₁ (z₂ + z₂') =
      galoisGlobalSectionsPairingFun Y K b z₁ z₂ + galoisGlobalSectionsPairingFun Y K b z₁ z₂' := by
  obtain ⟨i, -, a₂, a₂', h₂, h₂'⟩ := exists_fieldStageSection_eq₂ Y K z₂ z₂' ⊥
  obtain ⟨j, hij, a₁, -, h₁, -⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ i
  apply ΓRes_etaleMkId_injective
  have h₂j := ΓRes_eq_fieldStageSection_of_le Λ₂ Y K G₂ hij h₂
  have h₂j' := ΓRes_eq_fieldStageSection_of_le Λ₂ Y K G₂ hij h₂'
  rw [map_add, ΓRes_galoisGlobalSectionsPairingFun Y K b h₁
      (ΓRes_add_eq_fieldStageSection Λ₂ Y K G₂ hij h₂ h₂'),
    ΓRes_galoisGlobalSectionsPairingFun Y K b h₁ h₂j,
    ΓRes_galoisGlobalSectionsPairingFun Y K b h₁ h₂j', map_add, fieldStageSection_add]

/-- The pairing function is additive in the first variable. -/
theorem galoisGlobalSectionsPairingFun_add_left
    (z₁ z₁' : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairingFun Y K b (z₁ + z₁') z₂ =
      galoisGlobalSectionsPairingFun Y K b z₁ z₂ + galoisGlobalSectionsPairingFun Y K b z₁' z₂ := by
  obtain ⟨i, -, a₁, a₁', h₁, h₁'⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₁' ⊥
  obtain ⟨j, hij, -, a₂, -, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ i
  apply ΓRes_etaleMkId_injective
  have h₁j := ΓRes_eq_fieldStageSection_of_le Λ₁ Y K G₁ hij h₁
  have h₁j' := ΓRes_eq_fieldStageSection_of_le Λ₁ Y K G₁ hij h₁'
  rw [map_add, ΓRes_galoisGlobalSectionsPairingFun Y K b
      (ΓRes_add_eq_fieldStageSection Λ₁ Y K G₁ hij h₁ h₁') h₂,
    ΓRes_galoisGlobalSectionsPairingFun Y K b h₁j h₂,
    ΓRes_galoisGlobalSectionsPairingFun Y K b h₁j' h₂, map_add, AddMonoidHom.add_apply,
    fieldStageSection_add]

/-- **The pairing `Γ(Y_K, G₁|) × Γ(Y_K, G₂|) ⟶ Γ(Y_K, G₃|)` induced by a section-wise pairing
`b`**, on the carriers of `Γ^Gal = galoisGlobalSections` (these are `Γ(Y_K, Gᵢ|_{Y_K})` on the
nose, `Stacks.EtaleCohomology.galoisGlobalSections_comp_underlying`): two global sections are
pulled back from a common finite stage `Y_E` (Stacks 09YQ in degree zero), and are paired by `b`
over `Y_E`. It has type `((galoisGlobalSections Λ₁ Y K).obj G₁).obj.obj.V →+ ... →+
((galoisGlobalSections Λ₃ Y K).obj G₃).obj.obj.V` by definitional unfolding. -/
def galoisGlobalSectionsPairing : ↑((etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁)) →+
      ↑((etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) →+
        ↑((etaleModuleGlobalSections.{u, 0} Λ₃ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃)) :=
  AddMonoidHom.mk' (fun z₁ => AddMonoidHom.mk' (galoisGlobalSectionsPairingFun Y K b z₁)
    (galoisGlobalSectionsPairingFun_add_right Y K b z₁))
    (fun z₁ z₁' => AddMonoidHom.ext (galoisGlobalSectionsPairingFun_add_left Y K b z₁ z₁'))

/-- **(i) On sections pulled back from a common finite stage `Y_E`, the pairing is `b` over
`Y_E`.** -/
theorem ΓRes_galoisGlobalSectionsPairing {i : FExt k K}
    {z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁)}
    {z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)}
    {a₁ : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    {a₂ : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (h₁ : ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₁ = fieldStageSection Λ₁ Y K G₁ i a₁)
    (h₂ : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z₂ = fieldStageSection Λ₂ Y K G₂ i a₂) :
    ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
          (galoisGlobalSectionsPairing Y K b z₁ z₂) =
      fieldStageSection Λ₃ Y K G₃ i (b.app _ a₁ a₂) :=
  ΓRes_galoisGlobalSectionsPairingFun Y K b h₁ h₂

/-- **(ii) The pairing is Galois equivariant**: `⟨σ x, σ y⟩ = σ ⟨x, y⟩` for `σ ∈ Aut_k(K)` acting
through `id_Y × Spec σ`, which is the action `ρ σ` of `galoisGlobalSections`
(`Stacks.EtaleCohomology.galoisGlobalSections_ρ`). -/
theorem galoisGlobalSectionsPairing_galoisAction (σ : K ≃ₐ[k] K)
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K b
        (fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ₁ Y K σ G₁ z₁)
        (fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ₂ Y K σ G₂ z₂) =
      fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ₃ Y K σ G₃
        (galoisGlobalSectionsPairing Y K b z₁ z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_galoisGlobalSectionsPairing Y K b
      (ΓRes_fieldBaseChangeGlobalSectionsGaloisAction_fieldStageSection Λ₁ Y K G₁ σ h₁)
      (ΓRes_fieldBaseChangeGlobalSectionsGaloisAction_fieldStageSection Λ₂ Y K G₂ σ h₂),
    ΓRes_fieldBaseChangeGlobalSectionsGaloisAction_fieldStageSection Λ₃ Y K G₃ σ
      (ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂), b.naturality]

/-- **(iii) The pairing is natural in the sheaves**: for morphisms `vᵢ : Gᵢ ⟶ Gᵢ'` carrying `b` to
`b'`, `⟨Γ(v₁) x, Γ(v₂) y⟩' = Γ(v₃) ⟨x, y⟩`. -/
theorem galoisGlobalSectionsPairing_naturality {G₁' : EtaleModules.{u, 0} Λ₁ Y.left}
    {G₂' : EtaleModules.{u, 0} Λ₂ Y.left} {G₃' : EtaleModules.{u, 0} Λ₃ Y.left}
    (b' : EtaleSectionPairing G₁' G₂' G₃') (v₁ : G₁ ⟶ G₁') (v₂ : G₂ ⟶ G₂') (v₃ : G₃ ⟶ G₃')
    (hb : ∀ (U : Y.left.Etaleᵒᵖ) (a : G₁.obj.obj U) (c : G₂.obj.obj U),
      b'.app U (v₁.hom.app U a) (v₂.hom.app U c) = v₃.hom.app U (b.app U a c))
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K b'
        ((etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).map v₁) z₁)
        ((etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).map v₂) z₂) =
      (etaleModuleGlobalSections.{u, 0} Λ₃ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).map v₃)
        (galoisGlobalSectionsPairing Y K b z₁ z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_galoisGlobalSectionsPairing Y K b' (ΓRes_map_eq_fieldStageSection Λ₁ Y K G₁ v₁ h₁)
      (ΓRes_map_eq_fieldStageSection Λ₂ Y K G₂ v₂ h₂),
    ΓRes_map_eq_fieldStageSection Λ₃ Y K G₃ v₃ (ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂), hb]

/-- **Balancing**: if `b_U(r a, c) = b_U(a, r' c)` for all `U`, then `⟨r x, y⟩ = ⟨x, r' y⟩` on
global sections. -/
theorem galoisGlobalSectionsPairing_smul_left_eq_smul_right (r : Λ₁) (r' : Λ₂)
    (hb : ∀ (U : Y.left.Etaleᵒᵖ) (a : G₁.obj.obj U) (c : G₂.obj.obj U),
      b.app U (r • a) c = b.app U a (r' • c))
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K b (r • z₁) z₂ =
      galoisGlobalSectionsPairing Y K b z₁ (r' • z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  have h₁' : ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) (r • z₁) =
        fieldStageSection Λ₁ Y K G₁ i (r • a₁) := by
    rw [map_smul, h₁, fieldStageSection_smul]
  have h₂' : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) (r' • z₂) =
        fieldStageSection Λ₂ Y K G₂ i (r' • a₂) := by
    rw [map_smul, h₂, fieldStageSection_smul]
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_galoisGlobalSectionsPairing Y K b h₁' h₂, ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂',
    hb]

end Pairing

end Stacks.EtaleCohomology

end
