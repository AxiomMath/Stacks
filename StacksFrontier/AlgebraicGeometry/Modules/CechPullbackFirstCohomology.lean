module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleRefinementPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.LocalTriviality
public import StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionBoundaryDerivation
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCohomologySpelling

/-!
# Čech `H¹` along a morphism of schemes, from the pullback map on sheaf cohomology

Let `g : X' ⟶ X` be a morphism of schemes, `F` an `𝒪_X`-module, `U` an open cover of `X` and `W`
an open cover of `X'` refining `g⁻¹ U` through `π`. The Čech pullback map
`Stacks.Cech.cochainPullback` sends Čech cocycles of `F` for `U` to Čech cocycles of `g^*F` for
`W`. This file proves that if the map `H¹(X, F) → H¹(X, g_* g^* F)` induced by the unit of the
pullback–pushforward adjunction is injective — in particular if the pullback map on cohomology
`H¹(X, F) → H¹(X', g^* F)` of [Stacks, Tag 01FA] is injective — then a Čech `1`-cocycle of `F`
whose pullback is a coboundary is itself a coboundary.

No hypothesis on the covers beyond being covers is needed: first Čech cohomology of any cover
injects into sheaf cohomology ([Stacks, Tag 0B8R]), and the comparison is natural in the sheaf and
compatible with refinement.

## Main results

* `Stacks.Cech.exists_cechD_eq_of_cechD_eq_cochainPullback`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {I I' : Type u} (U : I → X.Opens)
  (W : I' → X'.Opens) (π : I' → I) (hW : ∀ k, W k ≤ g ⁻¹ᵁ U (π k)) (F : X.Modules)

/-- The inverse-image family of `U` along `g`. -/
abbrev preimageFamily : I → X'.Opens := fun i => g ⁻¹ᵁ U i

/-- **The Čech pullback map factors through the inverse-image family**: it is the pullback onto
`g⁻¹ U`, followed by the refinement from `g⁻¹ U` to `W`. -/
theorem cochainPullback_eq_refinementMap (p : ℕ) (s : CechCochains.Cochain U F.presheaf p) :
    cochainPullback g U W π hW F p s =
      CechCochains.refinementMap (preimageFamily g U) W π hW
        ((Scheme.Modules.pullback g).obj F).presheaf p
        (cochainPullback g U (preimageFamily g U) id (fun _ => le_rfl) F p s) := by
  funext k
  rw [CechCochains.refinementMap_apply]
  show _ = CechCochains.restr _ _ (CechCochains.restr _ _ _)
  rw [CechCochains.restr_restr]
  rfl

/-- The unit `F ⟶ g_* g^* F` of the pullback–pushforward adjunction, as a morphism of abelian
sheaves. -/
abbrev unitAb : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj F)) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)

/-- On sections over an open `V`, the unit `unitAb g F` is the pullback map
`pullbackSections g F V`. -/
theorem unitAb_app (V : X.Opens) (x : Γ(F, V)) :
    (unitAb g F).hom.app (op V) x = pullbackSections g F V x :=
  rfl

/-- The inverse image of an intersection is the intersection of the inverse images. -/
theorem preimage_inter_le {p : ℕ} (i : Fin p → I) :
    g ⁻¹ᵁ CechCochains.inter U i ≤ CechCochains.inter (preimageFamily g U) i := by
  intro x hx
  simp only [CechCochains.inter, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf,
    Set.mem_iInter, Scheme.Hom.coe_preimage, Set.mem_preimage] at hx ⊢
  exact hx

/-- Restriction of sections of a pushforward is restriction along the preimage. -/
theorem restr_pushforward (G : X'.Modules) {V V' : X.Opens} (h : V' ≤ V)
    (y : Γ((Scheme.Modules.pushforward g).obj G, V)) :
    CechCochains.restr ((Scheme.Modules.pushforward g).obj G).presheaf h y =
      CechCochains.restr G.presheaf (Scheme.Hom.preimage_mono g h) y :=
  rfl

/-- **A Čech pullback which is a coboundary on the inverse-image family is a coboundary for the
pushforward.** The cochain groups of `g_* g^* F` for `U` and of `g^* F` for `g⁻¹ U` agree up to
the identification `g⁻¹ (⋂ U) = ⋂ g⁻¹ U`. -/
theorem exists_cechD_eq_push_of_cechD_eq (c : CechCochains.Cochain U F.presheaf 1)
    (b' : CechCochains.Cochain (preimageFamily g U) ((Scheme.Modules.pullback g).obj F).presheaf 0)
    (hb' : CechCochains.cechD _ _ 0 b' =
      cochainPullback g U (preimageFamily g U) id (fun _ => le_rfl) F 1 c) :
    ∃ b : CechCochains.Cochain U
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj F)).presheaf 0,
      CechCochains.cechD _ _ 0 b = Stacks.Cohomology.CechOne.push U (unitAb g F).hom 1 c := by
  refine ⟨fun (i : Fin 1 → I) => CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
    (preimage_inter_le g U i) (b' i), ?_⟩
  funext (i : Fin 2 → I)
  have h := congrArg (CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
    (preimage_inter_le g U i)) (congrFun hb' i)
  have h2 : CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
      (preimage_inter_le g U i)
      (cochainPullback g U (preimageFamily g U) id (fun _ => le_rfl) F 1 c i) =
      pullbackSections g F (CechCochains.inter U i) (c i) := by
    show CechCochains.restr _ _ (CechCochains.restr _ _ _) = _
    rw [CechCochains.restr_restr, restr_self]
    rfl
  show _ = pullbackSections g F (CechCochains.inter U i) (c i)
  rw [← h2, ← h, CechCochains.cechD_apply, map_sum]
  refine (CechCochains.cechD_apply (U := U)
    (ℱ := ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj F)).presheaf)
    _ i).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, CechCochains.restr_restr]
  show (-1 : ℤ) ^ (j : ℕ) • CechCochains.restr ((Scheme.Modules.pullback g).obj F).presheaf
    (Scheme.Hom.preimage_mono g (CechCochains.inter_le_omit U i j))
    (CechCochains.restr _ (preimage_inter_le g U (i ∘ j.succAbove)) (b' (i ∘ j.succAbove))) = _
  rw [CechCochains.restr_restr]

section Abelian

variable {Y : TopCat.{u}}

/-- A Čech `1`-cocycle whose class maps to zero in sheaf cohomology is a coboundary
([Stacks, Tag 0B8R]). -/
private theorem exists_cechD_eq_of_cechH1ToRightDerivedSections_eq_zero {Λ : Type u}
    (V : Λ → Opens Y) (hV : (⊤ : Opens Y) = ⨆ i, V i) (H : TopCat.Sheaf AddCommGrpCat.{u} Y)
    (z : CechCochains.cocycles1 V H.presheaf)
    (h : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections Y ⊤ V hV H
      (CechCochains.cls V H.presheaf z) = 0) :
    ∃ t' : CechCochains.Cochain V H.presheaf 0,
      CechCochains.cechD V H.presheaf 0 t' = (z : CechCochains.Cochain V H.presheaf 1) :=
  (CechCochains.cls_eq_zero_iff V H.presheaf z).1
    (Stacks.Cohomology.SheafTorsor.cechH1ToRightDerivedSections_injective H V hV
      (h.trans (map_zero _).symm))

/-- **A refinement of covers is injective on first Čech cohomology.** If the refinement of a
`1`-cocycle is a coboundary, the cocycle is one. Both classes have the same image in sheaf
cohomology ([Stacks, Tag 09V2]) and the comparison is injective ([Stacks, Tag 0B8R]). -/
theorem exists_cechD_eq_of_refinementMap {Λ K : Type u} (V : Λ → Opens Y) (W' : K → Opens Y)
    (ρ : K → Λ) (hρ : ∀ k, W' k ≤ V (ρ k)) (hV : (⊤ : Opens Y) = ⨆ i, V i)
    (hW' : (⊤ : Opens Y) = ⨆ k, W' k) (H : TopCat.Sheaf AddCommGrpCat.{u} Y)
    (z : CechCochains.cocycles1 V H.presheaf) (t : CechCochains.Cochain W' H.presheaf 0)
    (ht : CechCochains.cechD W' H.presheaf 0 t =
      CechCochains.refinementMap V W' ρ hρ H.presheaf 1 z) :
    ∃ t' : CechCochains.Cochain V H.presheaf 0,
      CechCochains.cechD V H.presheaf 0 t' = (z : CechCochains.Cochain V H.presheaf 1) := by
  have h0 : CechCochains.refinementCechH1 V W' ρ hρ H.presheaf (CechCochains.cls V H.presheaf z) =
      0 := by
    rw [CechCochains.refinementCechH1_cls, CechCochains.cls_eq_zero_iff]
    exact ⟨t, ht⟩
  have h1 := Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement V W' ρ hρ
    hV hW' H (CechCochains.cls V H.presheaf z)
  rw [h0, map_zero] at h1
  exact exists_cechD_eq_of_cechH1ToRightDerivedSections_eq_zero V hV H z h1.symm

/-- **A morphism of sheaves injective on `H¹` is injective on first Čech cohomology.** -/
theorem exists_cechD_eq_of_push {Λ : Type u} (V : Λ → Opens Y) (hV : (⊤ : Opens Y) = ⨆ i, V i)
    {H G : TopCat.Sheaf AddCommGrpCat.{u} Y} (φ : H ⟶ G)
    (hinj : Function.Injective ((((sheafSections (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj (op ⊤)).rightDerived 1).map φ))
    (z : CechCochains.cocycles1 V H.presheaf) (t : CechCochains.Cochain V G.presheaf 0)
    (ht : CechCochains.cechD V G.presheaf 0 t = Stacks.Cohomology.CechOne.push V φ.hom 1 z) :
    ∃ t' : CechCochains.Cochain V H.presheaf 0,
      CechCochains.cechD V H.presheaf 0 t' = (z : CechCochains.Cochain V H.presheaf 1) := by
  let z' : CechCochains.cocycles1 V G.presheaf :=
    ⟨Stacks.Cohomology.CechOne.push V φ.hom 1 z, by
      rw [CechCochains.mem_cocycles1_iff, ← ht]
      exact CechCochains.cechD_cechD V G.presheaf 0 t⟩
  have hnat := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality Y ⊤ V hV φ z z'
    (fun _ => rfl)
  have hz' : CechCochains.cls V G.presheaf z' = 0 :=
    (CechCochains.cls_eq_zero_iff V G.presheaf z').2 ⟨t, ht⟩
  rw [hz', map_zero] at hnat
  have h1 : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections Y ⊤ V hV H
      (CechCochains.cls V H.presheaf z) = 0 := hinj (hnat.trans (map_zero _).symm)
  exact exists_cechD_eq_of_cechH1ToRightDerivedSections_eq_zero V hV H z h1

end Abelian

/-- **A Čech `1`-cocycle whose pullback is a coboundary is a coboundary**, as soon as the map
`H¹(X, F) → H¹(X, g_* g^* F)` induced by the unit of the pullback–pushforward adjunction is
injective. -/
theorem exists_cechD_eq_of_cechD_eq_cochainPullback (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hWcov : (⊤ : X'.Opens) = ⨆ k, W k)
    (hinj : Function.Injective ((((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (op ⊤)).rightDerived 1).map (unitAb g F)))
    (z : CechCochains.Cochain U F.presheaf 1) (hz : CechCochains.cechD U F.presheaf 1 z = 0)
    (t : CechCochains.Cochain W ((Scheme.Modules.pullback g).obj F).presheaf 0)
    (ht : CechCochains.cechD W _ 0 t = cochainPullback g U W π hW F 1 z) :
    ∃ t' : CechCochains.Cochain U F.presheaf 0, CechCochains.cechD U F.presheaf 0 t' = z := by
  have hV : (⊤ : X'.Opens) = ⨆ i, preimageFamily g U i := by
    rw [← Scheme.Hom.preimage_top g, hU, Scheme.Hom.preimage_iSup]
  have hz1 : cochainPullback g U (preimageFamily g U) id (fun _ => le_rfl) F 1 z ∈
      CechCochains.cocycles1 (preimageFamily g U) ((Scheme.Modules.pullback g).obj F).presheaf := by
    rw [CechCochains.mem_cocycles1_iff, cochainPullback_cechD, hz]
    funext i
    simp [cochainPullback]
  rw [cochainPullback_eq_refinementMap] at ht
  obtain ⟨t'', ht''⟩ := exists_cechD_eq_of_refinementMap (preimageFamily g U) W π hW hV hWcov
    ((SheafOfModules.toSheaf X'.ringCatSheaf).obj ((Scheme.Modules.pullback g).obj F))
    ⟨_, hz1⟩ t ht
  obtain ⟨b, hb⟩ := exists_cechD_eq_push_of_cechD_eq g U F z t'' ht''
  exact exists_cechD_eq_of_push U hU (unitAb g F) hinj ⟨z, hz⟩ b hb

/-- A monomorphism stays one under a natural isomorphism of functors. -/
theorem mono_map_of_iso {C D : Type*} [Category C] [Category D] {G H : C ⥤ D} (α : G ≅ H)
    {a b : C} (φ : a ⟶ b) [Mono (G.map φ)] : Mono (H.map φ) := by
  rw [show H.map φ = α.inv.app a ≫ G.map φ ≫ α.hom.app b by
    rw [α.hom.naturality, Iso.inv_hom_id_app_assoc]]
  infer_instance

/-- **The pullback map on `H¹` of [Stacks, Tag 01FA] factors through `H¹(X, g_* g^* F)`**, so its
injectivity gives the injectivity of the map induced on abelian sheaf cohomology by the unit
`F ⟶ g_* g^* F`. -/
theorem injective_rightDerived_unitAb (F : X.Modules)
    (h : Function.Injective
      (Stacks.Cohomology.moduleCohomologyPullbackMap g.toLRSHom.toShHom 1 F)) :
    Function.Injective ((((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (op ⊤)).rightDerived 1).map (unitAb g F)) := by
  have hfac := Stacks.Cohomology.moduleCohomologyMap_comp_left g.toLRSHom.toShHom 1
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      g.toLRSHom.toShHom).unit.app F) (𝟙 _)
  have h1 : Mono ((Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace 1).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        g.toLRSHom.toShHom).unit.app F)) := by
    have hm' : Mono ((Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace 1).map
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          g.toLRSHom.toShHom).unit.app F) ≫
        Stacks.Cohomology.moduleCohomologyMap g.toLRSHom.toShHom 1 (𝟙 _)) := by
      rw [hfac.trans (congrArg (Stacks.Cohomology.moduleCohomologyMap g.toLRSHom.toShHom 1)
        (Category.comp_id _))]
      exact (ModuleCat.mono_iff_injective _).2 h
    exact mono_of_mono _ (Stacks.Cohomology.moduleCohomologyMap g.toLRSHom.toShHom 1 (𝟙 _))
  have h1' : Mono ((Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace ((1 : ℕ) : ℤ)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)) := h1
  have h2 : Mono (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)) :=
    mono_map_of_iso (Deformation.Artin.SectionsSheaf.spaceModuleCohomologyIso X 1) _
  have h3 : Mono ((((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1) ⋙
      forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)) := by
    show Mono ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map _)
    rw [AddCommGrpCat.mono_iff_injective]
    exact (ModuleCat.mono_iff_injective _).1 h2
  have h4 := @mono_map_of_iso _ _ _ _ _ _
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ 1) _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) h3
  have h5 := @mono_map_of_iso _ _ _ _ _ _
    (Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ 1) _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) h4
  exact (AddCommGrpCat.mono_iff_injective _).1 h5

end Stacks.Cech

end

end
