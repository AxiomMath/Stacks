module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseExtVanishingConnected
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeMayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic

/-!
# `Ext^q(F, G) = 0` for `F` lisse on a scheme with finitely many connected components

Let `X` be a scheme with finitely many connected components (for instance a Noetherian one), `p`
a prime and `F` a finite type locally constant sheaf of `ℤ/p`-modules on `X_étale`. If
`Ext^q(ℤ/p_T, K) = H^q(T, K)` vanishes for every finite étale `T` over a connected component of
`X` and every `K`, then `Ext^q(F, G) = 0` for every sheaf `G` of `ℤ/p`-modules on `X`.

The connected components `W` of `X` are open, and `F` is the direct sum of the extensions by zero
`j_{W!} F|_W` (the relative Mayer--Vietoris sequence
`Stacks.EtaleCohomology.Purity.shortExact_relativeCover`, by induction over a finite set of
components); `Ext^q_X(j_{W!} F|_W, G) = Ext^q_W(F|_W, G|_W)` since `j_{W!} ⊣ j_W^{-1}` are exact,
and `F|_W` is lisse on the connected `W`, where
`Stacks.EtaleCohomology.subsingleton_ext_of_isFiniteTypeLocallyConstant_of_connectedSpace`
applies.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom`: the
  inverse image of a finite type locally constant sheaf along any morphism is one.
* `Stacks.EtaleCohomology.isZero_etaleModuleExtensionByZeroOfRestriction_of_forall_notMem`,
  `Stacks.EtaleCohomology.isIso_etaleModuleExtensionByZeroAdj_counit_of_forall_mem`: `j_{W!} F|_W`
  for the empty and for the full open.
* `Stacks.EtaleCohomology.subsingleton_ext_of_isFiniteTypeLocallyConstant`: the vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ExtensionTorsor
open ZeroObject

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- `SmallEtale.hasWeakSheafify_over_moduleCat_ring` at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_over_moduleCat_ring_zero (B : BigEtaleSite.{u}) (Λ : Type)
    [Ring Λ] (T : B.Scheme) (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafify_over_moduleCat_ring.{u, 0} B Λ T V

/-- `Stacks.ConstantSheaf.hasSheafify_over_moduleCat` on the slices of the small étale site of
Stacks 021B, at the coefficient universe `u + 1`. -/
local instance hasSheafify_smallEtaleOver_moduleCat_zero (B : BigEtaleSite.{u}) (Λ : Type)
    [Ring Λ] (S : Scheme.{u}) (hS : B.Contains S) (V : SmallEtale B S hS) :
    HasSheafify ((SmallEtale.topology B S hS).over V) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, 0, u + 1} _ Λ V

/-- `SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring` at the coefficient universe
`u + 1`. -/
local instance isRightAdjoint_smallEtalePushforward_moduleCat_ring_zero (B : BigEtaleSite.{u})
    (Λ : Type) [Ring Λ] (S T : B.Scheme) (g : T ⟶ S) :
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring.{u, 0} B Λ S T g

/-- **Inverse image preserves finite type local constancy**, along any morphism of schemes. -/
theorem isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom {T X : Scheme.{u}}
    (g : T ⟶ X) (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ X.smallEtaleTopology F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ T.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ g).obj F) := by
  let S₀ : Set Scheme.{u} := {X, T}
  let B := BigEtaleSite.ofSet S₀
  have hX : B.Contains X := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hT : B.Contains T := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  let XB : B.Scheme := ⟨X, hX⟩
  let TB : B.Scheme := ⟨T, hT⟩
  let gB : TB ⟶ XB := ObjectProperty.homMk g
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B gB
  have h₁ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ
      (SmallEtale.topology B XB.obj XB.property) ((etaleModulesToSmallEtale B XB Λ).obj F) :=
    (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B XB Λ F).2 hF
  have h₂ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ
      (SmallEtale.topology B TB.obj TB.property)
      (((AlgebraicGeometry.smallEtaleBaseChange B gB).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B XB.obj XB.property) (SmallEtale.topology B TB.obj TB.property)).obj
          ((etaleModulesToSmallEtale B XB Λ).obj F)) :=
    isFiniteTypeLocallyConstant_smallEtaleSheafPullback.{u + 1} B Λ gB _ h₁
  have h₃ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ
      (SmallEtale.topology B TB.obj TB.property)
      ((etaleModulesToSmallEtale B TB Λ).obj ((etaleModuleInverseImage.{u, 0} Λ g).obj F)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModulesToSmallEtalePullbackIso B Λ gB F).symm h₂
  exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B TB Λ _).1 h₃

section ExtensionByZero

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}}

/-- The residue geometric points of `X` cover `X`. -/
theorem iUnion_range_residueGeometricPoint (X : Scheme.{u}) :
    ⋃ x : X, Set.range (residueGeometricPoint X x).base = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x _⟩

/-- A morphism of étale modules is an isomorphism if it is so after inverse image along every
residue geometric point. -/
private theorem isIso_of_forall_isIso_inverseImage_residueGeometricPoint
    {F G : EtaleModules.{u, 0} Λ X} (γ : F ⟶ G)
    (h : ∀ x : X, IsIso ((etaleModuleInverseImage.{u, 0} Λ (residueGeometricPoint X x)).map γ)) :
    IsIso γ :=
  isIso_of_isIso_etaleModuleInverseImage_family Λ (residueGeometricPoint X)
    (iUnion_range_residueGeometricPoint X) γ h

/-- **`j_{W!} F|_W = 0` for an open `W` with no points.** -/
theorem isZero_etaleModuleExtensionByZeroOfRestriction_of_forall_notMem (W : X.Opens)
    (hW : ∀ x : X, x ∉ W) (F : EtaleModules.{u, 0} Λ X) :
    IsZero ((etaleModuleExtensionByZeroOfRestriction.{u, 0} Λ W.ι).obj F) := by
  have : IsIso (0 : (etaleModuleExtensionByZeroOfRestriction.{u, 0} Λ W.ι).obj F ⟶ 0) := by
    refine isIso_of_forall_isIso_inverseImage_residueGeometricPoint Λ _ fun x ↦ ?_
    have hd : Disjoint (Set.range (residueGeometricPoint X x).base) (Set.range W.ι.base) := by
      rw [Scheme.Opens.range_ι]
      exact Set.disjoint_left.2 fun z _ ↦ hW z
    have := (etaleModuleInverseImageAdj.{u, 0} Λ (residueGeometricPoint X x)).isLeftAdjoint
    exact ⟨⟨0, (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ
      (residueGeometricPoint X x) W.ι hd _).eq_of_src _ _,
      (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso
    (asIso (0 : (etaleModuleExtensionByZeroOfRestriction.{u, 0} Λ W.ι).obj F ⟶ 0))

/-- **`j_{W!} F|_W = F` for an open `W` containing every point**: the counit is an isomorphism. -/
theorem isIso_etaleModuleExtensionByZeroAdj_counit_of_forall_mem (W : X.Opens)
    (hW : ∀ x : X, x ∈ W) (F : EtaleModules.{u, 0} Λ X) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ W.ι).counit.app F) := by
  refine isIso_of_forall_isIso_inverseImage_residueGeometricPoint Λ _ fun x ↦ ?_
  have hsub : Set.range (residueGeometricPoint X x).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun z _ ↦ hW _
  exact isIso_etaleModuleInverseImage_map_counit_of_factors Λ (residueGeometricPoint X x) W.ι
    (IsOpenImmersion.lift W.ι _ hsub) (IsOpenImmersion.lift_fac _ _ hsub) F

end ExtensionByZero

section Vanishing

/-- `Ext^q(A ⊞ B, Y) = 0` when `Ext^q(A, Y) = 0` and `Ext^q(B, Y) = 0`. -/
theorem subsingleton_ext_biprod {C : Type*} [Category C] [Abelian C] [HasExt C] (A B Y : C)
    {q : ℕ} (hA : Subsingleton (Ext A Y q)) (hB : Subsingleton (Ext B Y q)) :
    Subsingleton (Ext (A ⊞ B) Y q) := by
  let S := ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) biprod.snd biprod.inl_snd
  have hS : S.ShortExact := ShortComplex.Splitting.shortExact
    { r := biprod.fst
      s := biprod.inr
      f_r := biprod.inl_fst
      s_g := biprod.inr_snd
      id := biprod.total }
  exact Ext.subsingleton_ext_left_X₂_of_shortExact hS Y hA hB

/-- `Ext^q(Y, Z) = 0` for a zero object `Y`. -/
theorem subsingleton_ext_of_isZero_left {C : Type*} [Category C] [Abelian C] [HasExt C] {Y : C}
    (hY : IsZero Y) (Z : C) {q : ℕ} : Subsingleton (Ext Y Z q) := by
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  rw [← Ext.mk₀_id_comp z, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.zero_comp]

/-- `Ext^q(X₃, Y) = 0` for a short exact sequence with `X₁ = 0` once `Ext^q(X₂, Y) = 0`: the map
`X₂ ⟶ X₃` is then an isomorphism. -/
theorem subsingleton_ext_X₃_of_shortExact_of_isZero {C : Type*} [Category C] [Abelian C]
    [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (h₁ : IsZero S.X₁) (Y : C) {q : ℕ}
    (h₂ : Subsingleton (Ext S.X₂ Y q)) : Subsingleton (Ext S.X₃ Y q) := by
  have := hS.exact.mono_g (h₁.eq_of_src _ _)
  have := hS.epi_g
  have : IsIso S.g := isIso_of_mono_of_epi _
  exact AdequateFunctor.subsingleton_ext_of_iso_left (asIso S.g) q h₂

/-- In a space with finitely many connected components, every union of components is open. -/
private theorem isOpen_preimage_connectedComponentsMk_of_finite {α : Type*} [TopologicalSpace α]
    [Finite (_root_.ConnectedComponents α)] (S : Set (_root_.ConnectedComponents α)) :
    IsOpen (ConnectedComponents.mk ⁻¹' S) := by
  rw [← Set.biUnion_of_singleton S, Set.preimage_iUnion₂]
  refine isOpen_biUnion fun c _ ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact Stacks.AlgebraicGeometry.ProperGeomConnected.isOpen_connectedComponent_of_finite x

variable {p : ℕ} [Fact p.Prime]

/-- `Ext^q(j_{W!} F|_W, G) = 0` for `F` lisse and a connected open `W`, from the vanishing of
`Ext^q(ℤ/p_T, -)` on the finite étale covers `T` of `W`. -/
private theorem subsingleton_ext_etaleModuleExtensionByZeroOfRestriction_of_connectedSpace
    {X : Scheme.{u}} (q : ℕ) (W : X.Opens) [ConnectedSpace W]
    (hvan : ∀ (T : Scheme.{u}) (π : T ⟶ W) [IsFinite π] [Etale π]
      (K : EtaleModules.{u, 0} (ZMod p) T), Subsingleton (Ext (unitSheaf (X := T) p) K q))
    (F : EtaleModules.{u, 0} (ZMod p) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p) X.smallEtaleTopology F)
    (G : EtaleModules.{u, 0} (ZMod p) X) :
    Subsingleton
      (Ext ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod p) W.ι).obj F) G q) := by
  have hFW : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p)
      W.toScheme.smallEtaleTopology ((etaleModuleRestriction.{u, 0} (ZMod p) W.ι).obj F) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ (ZMod p)
      ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod p) W.ι).app F)
      (isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom W.ι (ZMod p) F hF)
  have := subsingleton_ext_of_isFiniteTypeLocallyConstant_of_connectedSpace q
    hvan _ hFW ((etaleModuleRestriction.{u, 0} (ZMod p) W.ι).obj G)
  exact (Stacks.ExtAdjunction.extMap_bijective (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod p)
    W.ι) _ G q).2.subsingleton

/-- **`Ext^q(F, G) = 0` for `F` lisse, on a scheme with finitely many connected components**,
from the vanishing of `Ext^q(ℤ/p_T, -)` on the finite étale covers `T` of its connected
components. -/
theorem subsingleton_ext_of_isFiniteTypeLocallyConstant {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)] (q : ℕ)
    (hvan : ∀ (W : X.Opens) [ConnectedSpace W] (T : Scheme.{u}) (π : T ⟶ W) [IsFinite π]
      [Etale π] (K : EtaleModules.{u, 0} (ZMod p) T),
        Subsingleton (Ext (unitSheaf (X := T) p) K q))
    (F : EtaleModules.{u, 0} (ZMod p) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p) X.smallEtaleTopology F)
    (G : EtaleModules.{u, 0} (ZMod p) X) : Subsingleton (Ext F G q) := by
  have : DecidableEq (_root_.ConnectedComponents X) := Classical.decEq _
  have := Fintype.ofFinite (_root_.ConnectedComponents X)
  let WS : Set (_root_.ConnectedComponents X) → X.Opens :=
    fun S ↦ ⟨_, isOpen_preimage_connectedComponentsMk_of_finite S⟩
  have hmem : ∀ (S : Set (_root_.ConnectedComponents X)) (x : X),
      x ∈ WS S ↔ ConnectedComponents.mk x ∈ S := fun _ _ ↦ Iff.rfl
  have hone : ∀ c : _root_.ConnectedComponents X, Subsingleton (Ext
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod p) (WS {c}).ι).obj F) G q) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have hW : ((WS {ConnectedComponents.mk x} : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    have : ConnectedSpace (WS {ConnectedComponents.mk x}) := by
      have h := isConnected_connectedComponent (x := x)
      rw [← hW] at h
      exact isConnected_iff_connectedSpace.1 h
    exact subsingleton_ext_etaleModuleExtensionByZeroOfRestriction_of_connectedSpace q
      (WS {ConnectedComponents.mk x}) (hvan _) F hF G
  have hfin : ∀ S : Finset (_root_.ConnectedComponents X), Subsingleton (Ext
      ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod p) (WS ↑S).ι).obj F) G q) := by
    intro S
    induction S using Finset.cons_induction with
    | empty =>
      exact subsingleton_ext_of_isZero_left
        (isZero_etaleModuleExtensionByZeroOfRestriction_of_forall_notMem (ZMod p)
          (WS ↑(∅ : Finset (_root_.ConnectedComponents X)))
          (fun x hx ↦ by simpa using (hmem _ x).1 hx) F) G
    | cons c S hc ih =>
      have hsup : WS ↑(Finset.cons c S hc) = WS {c} ⊔ WS ↑S := by
        ext x
        rw [TopologicalSpace.Opens.coe_sup, Set.mem_union]
        change ConnectedComponents.mk x ∈ (↑(Finset.cons c S hc) : Set _) ↔
          ConnectedComponents.mk x ∈ ({c} : Set _) ∨ ConnectedComponents.mk x ∈ (↑S : Set _)
        simp only [Finset.coe_cons, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
      have hinf : ∀ x : X, x ∉ WS {c} ⊓ WS ↑S := by
        intro x hx
        rw [TopologicalSpace.Opens.mem_inf, hmem, hmem] at hx
        rw [Set.mem_singleton_iff.1 hx.1] at hx
        exact hc hx.2
      rw [hsup]
      exact subsingleton_ext_X₃_of_shortExact_of_isZero
        (Purity.shortExact_relativeCover (ZMod p) (WS {c}) (WS ↑S) F)
        (isZero_etaleModuleExtensionByZeroOfRestriction_of_forall_notMem (ZMod p) _ hinf F) G
        (subsingleton_ext_biprod _ _ G (hone c) ih)
  have := isIso_etaleModuleExtensionByZeroAdj_counit_of_forall_mem (ZMod p)
    (WS ↑(Finset.univ : Finset (_root_.ConnectedComponents X)))
    (fun x ↦ (hmem _ x).2 (Finset.mem_coe.2 (Finset.mem_univ _))) F
  exact AdequateFunctor.subsingleton_ext_of_iso_left
    (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod p)
      (WS ↑(Finset.univ : Finset (_root_.ConnectedComponents X))).ι).counit.app F)) q (hfin _)

end Vanishing

end Stacks.EtaleCohomology

end
