module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.ModuleGeneration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedAlgebra

import all StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.ModuleGeneration
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded.GradedAlgebra

/-!
# Sections of the limit of a coherent adic system over an affine open

Over an affine open `U`, the projection `Γ(lim F_m, U) ⟶ Γ(F_n, U)` is surjective with kernel
`I(U) ^ (n + 1) Γ(lim F_m, U)`; the transition kernels are identified with the associated graded
pieces of `Γ(lim F_m, U)`, together with the affine action of the associated graded algebra on
them.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

attribute [local instance] ringHomInvPairOfRingEquiv ringHomInvPairOfRingEquivSymm

section ProjectionComparison

open scoped AlgebraicGeometry

attribute [local instance] moduleOfSections'

local instance moduleOfSectionsModules {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

local instance evaluationPreservesZero {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    (SheafOfModules.evaluation R U).PreservesZeroMorphisms where
  map_zero := fun _ _ => rfl

/-- The degree-`n` transition kernel of a coherent adic system; in degree `0` it is the whole
zeroth term, and in negative degrees it is zero. -/
private def transitionKernelPiece {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) : ℤ → X.Modules
  | .ofNat 0 => F.obj.obj (op 0)
  | .ofNat (n + 1) => kernel (F.obj.map (homOfLE (Nat.le_succ n)).op)
  | .negSucc _ => kernel (𝟙 (F.obj.obj (op 0)))

private lemma transitionKernelPiece_isCoherent {X : Scheme.{u}}
    {I : X.IdealSheafData} (F : CoherentAdicSystems I) (n : ℤ) :
    (transitionKernelPiece F n).IsCoherent := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact F.property.1 0
    | succ n =>
      have := F.property.1 n
      have := F.property.1 (n + 1)
      exact SheafOfModules.kernel_isCoherent _
  | negSucc n =>
    have := F.property.1 0
    exact SheafOfModules.kernel_isCoherent _

private lemma transitionKernelPiece_isQuasicoherent {X : Scheme.{u}}
    {I : X.IdealSheafData} (F : CoherentAdicSystems I) (n : ℤ) :
    (transitionKernelPiece F n).IsQuasicoherent := by
  have := transitionKernelPiece_isCoherent F n
  exact isQuasicoherent_of_isCoherent _

private lemma transitionKernelPiece_negative {X : Scheme.{u}}
    {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    (n : ℤ) (hn : n < 0) : IsZero (transitionKernelPiece F n) := by
  cases n with
  | ofNat n => exact (Int.not_lt.mpr (Int.natCast_nonneg n) hn).elim
  | negSucc n => exact isZero_kernel_of_mono _

/-- Evaluation of a kernel sheaf is the kernel of the evaluated map. -/
private def kernelSectionsEquiv
    {X : Scheme.{u}} {L M : X.Modules} (f : L ⟶ M) (U : X.Opens) :
    (kernel f).val.obj (op U) ≃+
      LinearMap.ker (f.val.app (op U)).hom :=
  ((PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f) ≪≫
    ModuleCat.kernelIsoKer (f.val.app (op U))).toLinearEquiv.toAddEquiv

private theorem kernelSectionsEquiv_val
    {X : Scheme.{u}} {L M : X.Modules} (f : L ⟶ M) (U : X.Opens)
    (a : (kernel f).val.obj (op U)) :
    (kernelSectionsEquiv f U a).val = (kernel.ι f).val.app (op U) a := by
  show ((PreservesKernel.iso
      (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).hom ≫
    (ModuleCat.kernelIsoKer (f.val.app (op U))).hom ≫
    ModuleCat.ofHom (LinearMap.ker (f.val.app (op U)).hom).subtype) a = _
  let G : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact ConcreteCategory.congr_hom (kernelComparison_comp_ι f G) a

private lemma affine_limit_projection_surjective {X : Scheme.{u}}
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n : ℕ) :
    Function.Surjective (limit.π (globalSectionsSystem F) (op n)).hom := by
  obtain ⟨J, rfl⟩ := Scheme.IdealSheafData.equivOfIsAffine.symm.surjective I
  intro y
  obtain ⟨x, hx⟩ := globalSectionsComparison_projection_surjective X J F n y
  exact ⟨(globalSectionsComparison X J F).hom.hom x, hx⟩

/-- A submodule whose pullback along a surjection is an ideal-power multiple of the whole
module is itself that ideal-power multiple. -/
private lemma ker_eq_of_comap_eq_smul_top {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (hf : Function.Surjective f.hom) (K : Ideal R) (P : Submodule R N)
    (h : Submodule.comap f.hom P = K • ⊤) : P = K • ⊤ := by
  have hm := congrArg (Submodule.map f.hom) h
  rw [Submodule.map_comap_eq_of_surjective hf, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hf] at hm
  exact hm

private lemma affine_limit_projection_ker {X : Scheme.{u}}
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n : ℕ) :
    LinearMap.ker (limit.π (globalSectionsSystem F) (op n)).hom =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩) ^ (n + 1) • ⊤ := by
  obtain ⟨J, rfl⟩ := Scheme.IdealSheafData.equivOfIsAffine.symm.surjective I
  have h := globalSectionsComparison_projection_ker X J F n
  rw [ModuleCat.hom_comp, LinearMap.ker_comp] at h
  have := ker_eq_of_comap_eq_smul_top _ ((ModuleCat.epi_iff_surjective _).mp inferInstance) _ _ h
  simpa [Scheme.IdealSheafData.equivOfIsAffine_symm_apply] using this

/-- Sections over an open subscheme agree with sections of the restriction over the whole
space, after the change of base ring. -/
public def restrictionSectionsIso {X : Scheme.{u}} (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙
      SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars U.topIso.inv.hom ≅
    SheafOfModules.evaluation X.ringCatSheaf (op U) := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let M' := ((Scheme.Modules.restrictFunctor U.ι ⋙
        SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars U.topIso.inv.hom).obj M)
    letI : Module Γ(X, U)
      ((SheafOfModules.evaluation U.toScheme.ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) := M'.isModule
    let N' : ModuleCat Γ(X, U) := (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj M
    letI : Module Γ(X, U) N' := N'.isModule
    change M' ≅ N'
    refine {
      hom := ConcreteCategory.ofHom (show M' →ₗ[Γ(X, U)] N' from {
        toFun := fun (x : M') => M.val.map (eqToHom U.ι_image_top.symm).op x
        map_add' := by
          intro x y
          exact (M.val.map (eqToHom U.ι_image_top.symm).op).hom.map_add x y
        map_smul' := ?_ })
      inv := ConcreteCategory.ofHom (show N' →ₗ[Γ(X, U)] M' from {
        toFun := fun x => M.val.map (eqToHom U.ι_image_top).op x
        map_add' := by
          intro x y
          exact (M.val.map (eqToHom U.ι_image_top).op).hom.map_add x y
        map_smul' := ?_ })
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    · intro r x
      let x' : M.val.obj (op (U.ι ''ᵁ ⊤)) := x
      let s : X.ringCatSheaf.obj.obj (op (U.ι ''ᵁ ⊤)) :=
        (U.ι.appIso ⊤).inv (U.topIso.inv r)
      change M.val.map (eqToHom U.ι_image_top.symm).op (s • x') = _
      rw [M.val.map_smul]
      have h1 : s = X.presheaf.map (eqToHom U.ι_image_top).op r := by
        simp only [s, Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.topIso_inv]
        rfl
      have hs : X.ringCatSheaf.obj.map (eqToHom U.ι_image_top.symm).op s = r := by
        rw [h1]
        change X.presheaf.map (eqToHom U.ι_image_top.symm).op
          (X.presheaf.map (eqToHom U.ι_image_top).op r) = r
        simp [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rw [hs]
      rfl
    · intro r x
      let y' : M.val.obj (op (U.ι ''ᵁ ⊤)) := M.val.map (eqToHom U.ι_image_top).op x
      let s : X.ringCatSheaf.obj.obj (op (U.ι ''ᵁ ⊤)) :=
        (U.ι.appIso ⊤).inv (U.topIso.inv r)
      change M.val.map (eqToHom U.ι_image_top).op (r • x) = s • y'
      have h1 : s = X.presheaf.map (eqToHom U.ι_image_top).op r := by
        simp only [s, Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Opens.topIso_inv]
        rfl
      have hs : s = X.ringCatSheaf.obj.map (eqToHom U.ι_image_top).op r := h1
      rw [hs]
      exact M.val.map_smul (eqToHom U.ι_image_top).op r x
    · ext x
      change M.val.map (eqToHom U.ι_image_top).op
        (M.val.map (eqToHom U.ι_image_top.symm).op x) = x
      exact ConcreteCategory.congr_hom
        (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom_inv_id x
    · ext x
      change M.val.map (eqToHom U.ι_image_top.symm).op
        (M.val.map (eqToHom U.ι_image_top).op x) = x
      exact ConcreteCategory.congr_hom
        (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv_hom_id x
  · intro M N f
    ext x
    exact (PresheafOfModules.naturality_apply f.val (eqToHom U.ι_image_top.symm).op x).symm

/-- The system of global sections of the restricted system, after the change of base ring,
is the system of sections over the affine open. -/
public def restrictionSectionsNatIso {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) :
    globalSectionsSystem (restrictSystem I F U.1) ⋙
        ModuleCat.restrictScalars U.1.topIso.inv.hom ≅ sectionsSystem F U.1 :=
  NatIso.ofComponents (fun j => (restrictionSectionsIso U.1).app (F.obj.obj j))
    (fun f => (restrictionSectionsIso U.1).hom.naturality (F.obj.map f))

/-- The inverse limit of sections over an affine open is the inverse limit of global sections
of the restricted system. -/
public def affineOpenLimitIso {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) :
    (ModuleCat.restrictScalars U.1.topIso.inv.hom).obj
      (limit (globalSectionsSystem (restrictSystem I F U.1))) ≅
    limit (sectionsSystem F U.1) :=
  preservesLimitIso (ModuleCat.restrictScalars U.1.topIso.inv.hom)
      (globalSectionsSystem (restrictSystem I F U.1)) ≪≫
    HasLimit.isoOfNatIso (restrictionSectionsNatIso I F U)

private lemma affineOpenLimitIso_projection {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    (affineOpenLimitIso I F U).hom ≫ sectionsProjection F U.1 n =
      (ModuleCat.restrictScalars U.1.topIso.inv.hom).map
          (limit.π (globalSectionsSystem (restrictSystem I F U.1)) (op n)) ≫
        (restrictionSectionsNatIso I F U).hom.app (op n) := by
  simp only [affineOpenLimitIso, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    preservesLimitIso_hom_π_assoc]

private theorem ideal_map_eq_open {X : Scheme.{u}} (I : X.IdealSheafData)
    {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : V = W) :
    (I.ideal ⟨V, hV⟩).map
      (X.presheaf.map (eqToHom h.symm).op).hom = I.ideal ⟨W, hW⟩ := by
  cases h
  simp

private theorem ideal_map_affineOpen {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩).map
      U.1.topIso.hom.hom = I.ideal U := by
  have hJ : (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩ =
      I.ideal ⟨U.1.ι ''ᵁ ⊤,
        (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ := by
    rw [I.ideal_comap_of_isOpenImmersion]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    show (I.ideal ⟨U.1.ι ''ᵁ ⊤,
      (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩).comap
        (RingHom.id _) = _
    exact Ideal.comap_id _
  rw [hJ]
  exact ideal_map_eq_open I _ _ U.1.ι_image_top

private theorem ideal_smul_top_restrictScalars_iff
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : S →+* R) (hφ : Function.Surjective φ) (K : Ideal S) (M : ModuleCat R)
    (x : (ModuleCat.restrictScalars φ).obj M) :
    x ∈ K • (⊤ : Submodule S ((ModuleCat.restrictScalars φ).obj M)) ↔
    (show M from x) ∈ K.map φ • (⊤ : Submodule R M) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      show φ r • (show M from y) ∈ K.map φ • (⊤ : Submodule R M)
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · exact fun _ _ => Submodule.add_mem _
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro s hs y _
      obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hs
      show r • (show (ModuleCat.restrictScalars φ).obj M from y) ∈
        K • (⊤ : Submodule S ((ModuleCat.restrictScalars φ).obj M))
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · exact fun _ _ => Submodule.add_mem _

/-- The kernel of a map of modules, after restriction of scalars along a surjective ring map. -/
private lemma restrictScalars_ker_eq {R S : Type u} [CommRing R] [CommRing S]
    (φ : S →+* R) (hφ : Function.Surjective φ)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (K : Ideal R) (L : Ideal S) (hKL : L.map φ = K)
    (hker : LinearMap.ker g.hom = K • ⊤) :
    LinearMap.ker ((ModuleCat.restrictScalars φ).map g).hom = L • ⊤ := by
  ext z
  have h1 : z ∈ LinearMap.ker ((ModuleCat.restrictScalars φ).map g).hom ↔
      (show M from z) ∈ LinearMap.ker g.hom := Iff.rfl
  rw [h1, hker, ← hKL]
  exact (ideal_smul_top_restrictScalars_iff φ hφ L M z).symm

private theorem ideal_map_affineOpen_inv {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.ideal U).map U.1.topIso.inv.hom =
      (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩ := by
  rw [← ideal_map_affineOpen I U, Ideal.map_map]
  show Ideal.map (U.1.topIso.inv.hom.comp U.1.topIso.hom.hom) _ = _
  have h : U.1.topIso.inv.hom.comp U.1.topIso.hom.hom = RingHom.id _ := by
    ext x
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id x
  rw [h, Ideal.map_id]

/-- **The sections of the limit surject onto the sections of each term, over an affine open.**

On an affine open `U` of a Noetherian scheme the projection
`Γ(lim F_m, U) ⟶ Γ(F_n, U)` out of `Stacks.Coherent.sectionsLimit` is surjective: the system
restricted to `U` is the one attached to a finite module over the completion of `Γ(X, U)`, whose
quotients by the powers of the ideal are the terms. Together with
`Stacks.Coherent.affineOpen_limit_projection_ker` this is the affine quotient presentation
`Γ(F_n, U) = Γ(F, U) / I(U) ^ (n + 1) Γ(F, U)`. -/
public lemma affineOpen_limit_projection_surjective {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (sectionsProjection F U.1 n).hom := by
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let D := globalSectionsSystem (restrictSystem I F U.1)
  let E := ModuleCat.restrictScalars U.1.topIso.inv.hom
  let α := restrictionSectionsNatIso I F U
  have h := affineOpenLimitIso_projection I F U n
  have hp : Function.Surjective (E.map (limit.π D (op n))).hom :=
    affine_limit_projection_surjective (I.comap U.1.ι) (restrictSystem I F U.1) n
  have he : Function.Surjective (α.hom.app (op n)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hh : Function.Surjective ((E.map (limit.π D (op n)) ≫ α.hom.app (op n)).hom) := by
    rw [ModuleCat.hom_comp, LinearMap.coe_comp]
    exact he.comp hp
  rw [← h, ModuleCat.hom_comp, LinearMap.coe_comp] at hh
  exact hh.of_comp

/-- An isomorphism of modules after restriction of scalars along a two-sided inverse of a ring
isomorphism is a semilinear equivalence. -/
public def semilinearEquivOfRestrictScalarsIso {R S : Type u} [CommRing R] [CommRing S]
    (σ : R ≃+* S) (φ : S →+* R) (hφ : ∀ r : R, φ (σ r) = r)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (e : (ModuleCat.restrictScalars φ).obj M ≅ N) :
    M ≃ₛₗ[σ.toRingHom] N where
  toFun x := e.hom.hom x
  map_add' x y := e.hom.hom.map_add x y
  map_smul' r x := by
    have h := e.hom.hom.map_smul (σ r) x
    rw [ModuleCat.restrictScalars.smul_def φ (σ r) x, hφ r] at h
    exact h
  invFun y := e.inv.hom y
  left_inv x := ConcreteCategory.congr_hom e.hom_inv_id x
  right_inv y := ConcreteCategory.congr_hom e.inv_hom_id y

/-- The limit of sections over an affine open, compared semilinearly with the limit of global
sections of the restricted system. -/
public def affineOpenLimitSemilinearEquiv {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) :
    (limit (globalSectionsSystem (restrictSystem I F U.1)) : ModuleCat.{u} Γ(U.1.toScheme, ⊤))
      ≃ₛₗ[U.1.topIso.commRingCatIsoToRingEquiv.toRingHom]
      (limit (sectionsSystem F U.1) : ModuleCat.{u} Γ(X, U.1)) :=
  semilinearEquivOfRestrictScalarsIso U.1.topIso.commRingCatIsoToRingEquiv
    U.1.topIso.inv.hom
    (fun r => ConcreteCategory.congr_hom U.1.topIso.hom_inv_id r)
    (affineOpenLimitIso I F U)

/-- The semilinear comparison of `Stacks.Coherent.affineOpenLimitSemilinearEquiv` is carried by
the underlying function of `Stacks.Coherent.affineOpenLimitIso`. -/
public lemma affineOpenLimitSemilinearEquiv_apply {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens)
    (x : (limit (globalSectionsSystem (restrictSystem I F U.1)) :
      ModuleCat.{u} Γ(U.1.toScheme, ⊤))) :
    affineOpenLimitSemilinearEquiv I F U x = (affineOpenLimitIso I F U).hom.hom x := rfl

/-- The kernel of the projection, pulled back along the comparison isomorphism. -/
private lemma affineOpenLimit_comap_ker {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    Submodule.comap (affineOpenLimitIso I F U).hom.hom
        (LinearMap.ker (sectionsProjection F U.1 n).hom) =
      LinearMap.ker ((ModuleCat.restrictScalars U.1.topIso.inv.hom).map
        (limit.π (globalSectionsSystem (restrictSystem I F U.1)) (op n))).hom := by
  have h := affineOpenLimitIso_projection I F U n
  have hker_alpha : LinearMap.ker
      ((restrictionSectionsNatIso I F U).hom.app (op n)).hom = ⊥ :=
    LinearMap.ker_eq_bot_of_injective ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have heker := congrArg (fun k : _ ⟶ (sectionsSystem F U.1).obj (op n) =>
    LinearMap.ker (ModuleCat.Hom.hom k)) h
  simp only [ModuleCat.hom_comp, LinearMap.ker_comp, hker_alpha, Submodule.comap_bot] at heker
  exact heker

private lemma affineOpenLimit_restrictScalars_ker {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker ((ModuleCat.restrictScalars U.1.topIso.inv.hom).map
        (limit.π (globalSectionsSystem (restrictSystem I F U.1)) (op n))).hom =
      (I.ideal U) ^ (n + 1) • ⊤ := by
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hsurj : Function.Surjective U.1.topIso.inv.hom := fun y =>
    ⟨U.1.topIso.hom.hom y, ConcreteCategory.congr_hom U.1.topIso.hom_inv_id y⟩
  exact restrictScalars_ker_eq U.1.topIso.inv.hom hsurj
    (limit.π (globalSectionsSystem (restrictSystem I F U.1)) (op n))
    (((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩) ^ (n + 1)) ((I.ideal U) ^ (n + 1))
    (by rw [Ideal.map_pow, ideal_map_affineOpen_inv])
    (affine_limit_projection_ker (I.comap U.1.ι) (restrictSystem I F U.1) n)

/-- **The kernel of the projection to the `n`-th term, over an affine open.**

On an affine open `U` of a Noetherian scheme the projection `Γ(lim F_m, U) ⟶ Γ(F_n, U)` has
kernel `I(U) ^ (n + 1) · Γ(lim F_m, U)`. With
`Stacks.Coherent.affineOpen_limit_projection_surjective` this is the affine quotient
presentation `Γ(F_n, U) = Γ(F, U) / I(U) ^ (n + 1) Γ(F, U)` that [Stacks, Tag 0EH6] reads the
terms of the system off from. -/
public lemma affineOpen_limit_projection_ker {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker (sectionsProjection F U.1 n).hom =
      (I.ideal U) ^ (n + 1) • ⊤ :=
  ker_eq_of_comap_eq_smul_top (affineOpenLimitIso I F U).hom
    (fun y => ⟨(affineOpenLimitIso I F U).inv.hom y,
      ConcreteCategory.congr_hom (affineOpenLimitIso I F U).inv_hom_id y⟩)
    ((I.ideal U) ^ (n + 1)) _
    ((affineOpenLimit_comap_ker I F U n).trans
      (affineOpenLimit_restrictScalars_ker I F U n))

/-! ### The transition kernels as a graded module -/

/-- The inverse limit of the sections of a coherent adic system over an open. -/
public abbrev sectionsLimit {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U : X.Opens) : ModuleCat.{u} Γ(X, U) :=
  limit (sectionsSystem F U)

/-- The kernel of the projection to the `n`-th term is the `(n + 1)`-st power piece. -/
private lemma ker_sectionsProjection_eq_power {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker (sectionsProjection F U.1 n).hom =
      AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) (n + 1) := by
  simpa [AssociatedGraded.power] using affineOpen_limit_projection_ker I F U n

/-- On an affine open, the degree-zero piece of the limit is the zeroth term. -/
private def affineOpenLimitZeroEquiv {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) :
    AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) 0 ≃+
      Γ(F.obj.obj (op 0), U.1) :=
  associatedGradedZeroPieceEquivOfSurjective _ _ (affineOpen_limit_projection_surjective I F U 0)
    (ker_sectionsProjection_eq_power I F U 0)

/-- On an affine open, the positive-degree graded pieces of the limit are the transition
kernels. -/
private def affineOpenLimitKernelEquiv {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) (n + 1) ≃+
      LinearMap.ker ((sectionsSystem F U.1).map (homOfLE (Nat.le_succ n)).op).hom := by
  have hcomp : (((sectionsSystem F U.1).map (homOfLE (Nat.le_succ n)).op).hom).comp
      (sectionsProjection F U.1 (n + 1)).hom = (sectionsProjection F U.1 n).hom := by
    ext x
    exact congrArg (fun g => ModuleCat.Hom.hom g x)
      (limit.w (sectionsSystem F U.1) ((homOfLE (Nat.le_succ n)).op))
  exact associatedGradedPieceEquivKernel _ (n + 1) _ _ _
    (affineOpen_limit_projection_surjective I F U (n + 1))
    (ker_sectionsProjection_eq_power I F U (n + 1)) (ker_sectionsProjection_eq_power I F U n) hcomp

/-- The sections of the degree-`n` transition kernel over an affine open, identified with the
degree-`n` associated graded piece of the limit. -/
private def affineOpenTransitionSectionsEquiv {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    (transitionKernelPiece F (n : ℤ)).val.obj (op U.1) ≃+
      AssociatedGraded.piece (M := sectionsLimit F U.1) (I.ideal U) n := by
  cases n with
  | zero => exact (affineOpenLimitZeroEquiv I F U).symm
  | succ n =>
    exact (kernelSectionsEquiv
      (F.obj.map (homOfLE (Nat.le_succ n)).op) U.1).trans
      (affineOpenLimitKernelEquiv I F U n).symm

private theorem affineOpenLimitZeroEquiv_mk {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens)
    (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) 0) :
    affineOpenLimitZeroEquiv I F U (AssociatedGraded.mk (I.ideal U) 0 a) =
      (sectionsProjection F U.1 0).hom a := by
  dsimp [affineOpenLimitZeroEquiv]
  exact associatedGradedZeroPieceEquivOfSurjective_mk _ _ _ _ a

private theorem affineOpenLimitKernelEquiv_mk_val {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ)
    (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) (n + 1)) :
    (affineOpenLimitKernelEquiv I F U n
      (AssociatedGraded.mk (I.ideal U) (n + 1) a)).val =
      (sectionsProjection F U.1 (n + 1)).hom a := by
  dsimp [affineOpenLimitKernelEquiv]
  exact associatedGradedPieceEquivKernel_mk_val _ _ _ _ _ _ _ _ _ a

private theorem affineOpenTransitionZero_mk {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens)
    (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) 0)
    (x : (transitionKernelPiece F 0).val.obj (op U.1))
    (h : affineOpenTransitionSectionsEquiv I F U 0 x =
      AssociatedGraded.mk (I.ideal U) 0 a) :
    x = (sectionsProjection F U.1 0).hom a.1 := by
  have hdef : affineOpenTransitionSectionsEquiv I F U 0 =
      (affineOpenLimitZeroEquiv I F U).symm := rfl
  rw [hdef] at h
  have hh := congrArg (affineOpenLimitZeroEquiv I F U) h
  rw [affineOpenLimitZeroEquiv_mk] at hh
  exact ((affineOpenLimitZeroEquiv I F U).apply_symm_apply x).symm.trans hh

private theorem affineOpenTransitionSucc_mk {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ)
    (a : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) (n + 1))
    (x : (transitionKernelPiece F ((n + 1 : ℕ) : ℤ)).val.obj (op U.1))
    (h : affineOpenTransitionSectionsEquiv I F U (n + 1) x =
      AssociatedGraded.mk (I.ideal U) (n + 1) a) :
    ((kernel.ι (F.obj.map (homOfLE (Nat.le_succ n)).op)).val.app (op U.1)) x =
      (sectionsProjection F U.1 (n + 1)).hom a.1 := by
  have hdef : affineOpenTransitionSectionsEquiv I F U (n + 1) =
      (kernelSectionsEquiv (F.obj.map (homOfLE (Nat.le_succ n)).op) U.1).trans
        (affineOpenLimitKernelEquiv I F U n).symm := rfl
  rw [hdef] at h
  have hv := congrArg Subtype.val (congrArg (affineOpenLimitKernelEquiv I F U n) h)
  rw [affineOpenLimitKernelEquiv_mk_val] at hv
  have h2 := congrArg Subtype.val ((affineOpenLimitKernelEquiv I F U n).apply_symm_apply
    (kernelSectionsEquiv (F.obj.map (homOfLE (Nat.le_succ n)).op) U.1 x))
  exact (kernelSectionsEquiv_val _ _ x).symm.trans (h2.symm.trans hv)

private def transitionInclusion {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (n : ℕ) :
    transitionKernelPiece F n ⟶ F.obj.obj (op n) :=
  match n with
  | 0 => 𝟙 _
  | _ + 1 => kernel.ι _

private lemma transitionInclusion_injective {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (n : ℕ) (U : X.Opens) :
    Function.Injective ((transitionInclusion F n).val.app (op U)) := by
  cases n with
  | zero => exact fun _ _ h => h
  | succ n =>
    intro x y h
    apply (kernelSectionsEquiv (F.obj.map (homOfLE (Nat.le_succ n)).op) U).injective
    exact Subtype.ext ((kernelSectionsEquiv_val _ _ x).trans
      (h.trans (kernelSectionsEquiv_val _ _ y).symm))

private def transitionMk {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n : ℕ) :
    AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n →+
      (transitionKernelPiece F n).val.obj (op U.1) :=
  (affineOpenTransitionSectionsEquiv I F U n).symm.toAddMonoidHom.comp
    (Submodule.mkQ _).toAddMonoidHom

private lemma transitionMk_surjective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n : ℕ) : Function.Surjective (transitionMk I F U n) :=
  (affineOpenTransitionSectionsEquiv I F U n).symm.surjective.comp
    (Submodule.mkQ_surjective _)

private lemma transitionMk_inclusion {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n : ℕ)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n) :
    (transitionInclusion F n).val.app (op U.1) (transitionMk I F U n x) =
      (sectionsProjection F U.1 n) x := by
  have h : affineOpenTransitionSectionsEquiv I F U n (transitionMk I F U n x) =
      AssociatedGraded.mk (I.ideal U) n x :=
    (affineOpenTransitionSectionsEquiv I F U n).apply_symm_apply _
  cases n with
  | zero => exact affineOpenTransitionZero_mk I F U x _ h
  | succ n => exact affineOpenTransitionSucc_mk I F U n x _ h

private lemma transitionMk_smul {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n : ℕ) (r : Γ(X, U.1))
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n) :
    transitionMk I F U n (r • x) = r • transitionMk I F U n x := by
  apply transitionInclusion_injective F n U.1
  have h1 := transitionMk_inclusion I F U n (r • x)
  have h3 := transitionMk_inclusion I F U n x
  have h2 : (sectionsProjection F U.1 n).hom (r • (x : sectionsLimit F U.1)) =
      r • (sectionsProjection F U.1 n).hom (x : sectionsLimit F U.1) :=
    (sectionsProjection F U.1 n).hom.map_smul r _
  have h4 : ((transitionInclusion F n).val.app (op U.1)).hom
        (r • transitionMk I F U n x) =
      r • ((transitionInclusion F n).val.app (op U.1)).hom (transitionMk I F U n x) :=
    ((transitionInclusion F n).val.app (op U.1)).hom.map_smul r _
  rw [h1, h4, h3]
  exact h2

private def limitRestriction {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U V : X.Opens) (h : V ≤ U) :
    sectionsLimit F U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj
        (sectionsLimit F V) := by
  let E := ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom
  let α : sectionsSystem F U ⟶ sectionsSystem F V ⋙ E :=
    { app j := (F.obj.obj j).val.map (homOfLE h).op
      naturality j k f := ((F.obj.map f).val.naturality (homOfLE h).op).symm }
  exact limMap α ≫ (preservesLimitIso E (sectionsSystem F V)).inv

/-- Restriction of sections, as a map between the two inverse limits. -/
private def limitRestrictionFun {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U V : X.Opens) (h : V ≤ U) :
    sectionsLimit F U → sectionsLimit F V :=
  fun x => limitRestriction F U V h x

private lemma limitRestrictionFun_smul {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U V : X.Opens) (h : V ≤ U) (r : Γ(X, U))
    (x : sectionsLimit F U) :
    limitRestrictionFun F U V h (r • x) =
      X.presheaf.map (homOfLE h).op r • limitRestrictionFun F U V h x :=
  (limitRestriction F U V h).hom.map_smul r x

private lemma limitRestriction_projection {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (U V : X.Opens) (h : V ≤ U) (n : ℕ)
    (x : sectionsLimit F U) :
    (sectionsProjection F V n) (limitRestrictionFun F U V h x) =
      (F.obj.obj (op n)).val.map (homOfLE h).op ((sectionsProjection F U n) x) := by
  show ((limitRestriction F U V h ≫
    (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).map
      (sectionsProjection F V n)) x) = _
  simp only [limitRestriction, Category.assoc, preservesLimitIso_inv_π, limMap_π]
  rfl

private lemma limitRestriction_power {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U V : X.affineOpens) (h : V.1 ≤ U.1) (n : ℕ)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n) :
    limitRestrictionFun F U.1 V.1 h x ∈
      AssociatedGraded.power (M := sectionsLimit F V.1) (I.ideal V) n := by
  cases n with
  | zero => exact associatedGraded_mem_degreeZero (I.ideal V) _
  | succ n =>
    have hx : (sectionsProjection F U.1 n) x = 0 :=
      (affineOpen_limit_projection_ker I F U n).ge x.property
    have hz : (sectionsProjection F V.1 n) (limitRestrictionFun F U.1 V.1 h x) = 0 := by
      rw [limitRestriction_projection, hx]
      exact ((F.obj.obj (op n)).val.map (homOfLE h).op).hom.map_zero
    exact (affineOpen_limit_projection_ker I F V n).le hz

private lemma transitionMk_restrict {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U V : X.affineOpens) (h : V.1 ≤ U.1) (n : ℕ)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n) :
    (transitionKernelPiece F n).val.map (homOfLE h).op (transitionMk I F U n x) =
      transitionMk I F V n ⟨limitRestrictionFun F U.1 V.1 h x,
        limitRestriction_power I F U V h n x⟩ := by
  apply transitionInclusion_injective F n V.1
  have hh := ConcreteCategory.congr_hom
    ((transitionInclusion F n).val.naturality (homOfLE h).op)
    (transitionMk I F U n x)
  rw [transitionMk_inclusion]
  have hgoal : (transitionInclusion F n).val.app (op V.1)
      ((transitionKernelPiece F n).val.map (homOfLE h).op (transitionMk I F U n x)) =
      (F.obj.obj (op n)).val.map (homOfLE h).op
        ((transitionInclusion F n).val.app (op U.1) (transitionMk I F U n x)) := hh
  rw [hgoal, transitionMk_inclusion, limitRestriction_projection]

private def gradedPieceCast {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) {n m : ℕ} (h : n = m) :
    AssociatedGraded.piece (M := M) I n ≃ₗ[R] AssociatedGraded.piece (M := M) I m :=
  h ▸ LinearEquiv.refl R _

private lemma gradedPieceCast_mk {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) {n m : ℕ} (h : n = m)
    (x : AssociatedGraded.power (M := M) I n)
    (y : AssociatedGraded.power (M := M) I m) (hxy : (x : M) = y) :
    gradedPieceCast I h (AssociatedGraded.mk I n x) = AssociatedGraded.mk I m y := by
  subst m
  obtain rfl := Subtype.ext hxy
  rfl

private lemma gradedPieceCast_heq {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) {n m : ℕ} (h : n = m)
    (x : AssociatedGraded.piece (M := M) I n) : HEq (gradedPieceCast I h x) x := by
  subst m
  rfl

private def affinePowerAction {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n m : ℕ)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) m) :
    AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) (n + m) :=
  ⟨(a : Γ(X, U.1)) • (x : sectionsLimit F U.1), by
    simpa only [Nat.add_comm] using AssociatedGraded.smul_mem_power (I.ideal U) a.2 x.2⟩

/-- The action of the associated graded algebra on the transition kernels over an affine open. -/
private def affineOpenTransitionAction {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) (n m : ℕ) :
    (transitionKernelPiece F (n : ℤ)).val.obj (op U.1) →+
      ((conormalPushforward I).piece (m : ℤ)).val.obj (op U.1) →+
        (transitionKernelPiece F ((n + m : ℕ) : ℤ)).val.obj (op U.1) := by
  let e := affineOpenTransitionSectionsEquiv I F U
  let c := conormalPieceEquiv I U m
  let d := gradedPieceCast (M := sectionsLimit F U.1) (I.ideal U) (Nat.add_comm m n)
  exact {
    toFun := fun x =>
      { toFun := fun a => (e (n + m)).symm
          (d (AssociatedGraded.homogeneousSMul (I.ideal U) (c a) (e n x)))
        map_zero' := by
          simp only [map_zero, AssociatedGraded.homogeneousSMul_zero_left]
        map_add' := by
          intro a b
          simp only [map_add, AssociatedGraded.homogeneousSMul_add_left] }
    map_zero' := by
      ext a
      change (e (n + m)).symm
        (d (AssociatedGraded.homogeneousSMul (I.ideal U) (c a) ((e n) 0))) = 0
      simp only [map_zero, AssociatedGraded.homogeneousSMul_zero_right]
    map_add' := by
      intro x y
      ext a
      change (e (n + m)).symm
          (d (AssociatedGraded.homogeneousSMul (I.ideal U) (c a) ((e n) (x + y)))) =
        (e (n + m)).symm (d (AssociatedGraded.homogeneousSMul (I.ideal U) (c a) ((e n) x))) +
          (e (n + m)).symm (d (AssociatedGraded.homogeneousSMul (I.ideal U) (c a) ((e n) y)))
      simp only [map_add, AssociatedGraded.homogeneousSMul_add_right] }

private lemma affineOpenTransitionAction_mk {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n m : ℕ)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n)
    (a : AssociatedGraded.power (M := Γ(X, U.1)) (I.ideal U) m) :
    affineOpenTransitionAction I F U n m (transitionMk I F U n x)
      (conormalLocalMap I U m a) =
      transitionMk I F U (n + m) (affinePowerAction I F U n m x a) := by
  apply congrArg (affineOpenTransitionSectionsEquiv I F U (n + m)).symm
  have hx := (affineOpenTransitionSectionsEquiv I F U n).apply_symm_apply
    (AssociatedGraded.mk (I.ideal U) n x)
  have ha := conormalPieceEquiv_localMap I U m a
  exact (congrArg (gradedPieceCast (M := sectionsLimit F U.1) (I.ideal U) (Nat.add_comm m n))
    (congrArg₂ (fun a x => AssociatedGraded.homogeneousSMul (I.ideal U) a x) ha hx)).trans
      (gradedPieceCast_mk (I.ideal U) (Nat.add_comm m n) _
        (affinePowerAction I F U n m x a) rfl)

private lemma affineOpenTransitionAction_restrict {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U V : X.affineOpens) (h : V.1 ≤ U.1) (n m : ℕ)
    (x : (transitionKernelPiece F n).val.obj (op U.1))
    (a : ((conormalPushforward I).piece m).val.obj (op U.1)) :
    (transitionKernelPiece F (n + m : ℕ)).val.map (homOfLE h).op
        (affineOpenTransitionAction I F U n m x a) =
      affineOpenTransitionAction I F V n m
        ((transitionKernelPiece F n).val.map (homOfLE h).op x)
        (((conormalPushforward I).piece m).val.map (homOfLE h).op a) := by
  obtain ⟨x, rfl⟩ := transitionMk_surjective I F U n x
  obtain ⟨a, rfl⟩ := conormalLocalMap_surjective I U m a
  rw [affineOpenTransitionAction_mk, transitionMk_restrict, transitionMk_restrict,
    conormalLocalMap_restrict, affineOpenTransitionAction_mk]
  congr 1
  exact Subtype.ext (limitRestrictionFun_smul F U.1 V.1 h (a : Γ(X, U.1)) (x : sectionsLimit F U.1))

private lemma affineOpenTransitionAction_smul_left {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n m : ℕ) (r : Γ(X, U.1))
    (x : (transitionKernelPiece F n).val.obj (op U.1))
    (a : ((conormalPushforward I).piece m).val.obj (op U.1)) :
    affineOpenTransitionAction I F U n m (r • x) a =
      r • affineOpenTransitionAction I F U n m x a := by
  obtain ⟨x, rfl⟩ := transitionMk_surjective I F U n x
  obtain ⟨a, rfl⟩ := conormalLocalMap_surjective I U m a
  rw [← transitionMk_smul, affineOpenTransitionAction_mk,
    affineOpenTransitionAction_mk, ← transitionMk_smul]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

private lemma affineOpenTransitionAction_smul_right {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n m : ℕ) (r : Γ(X, U.1))
    (x : (transitionKernelPiece F n).val.obj (op U.1))
    (a : ((conormalPushforward I).piece m).val.obj (op U.1)) :
    affineOpenTransitionAction I F U n m x (r • a) =
      r • affineOpenTransitionAction I F U n m x a := by
  obtain ⟨x, rfl⟩ := transitionMk_surjective I F U n x
  obtain ⟨a, rfl⟩ := conormalLocalMap_surjective I U m a
  rw [← map_smul, affineOpenTransitionAction_mk,
    affineOpenTransitionAction_mk, ← transitionMk_smul]
  congr 1
  exact Subtype.ext (mul_smul _ _ _)

private lemma transitionMk_heq {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) {n m : ℕ} (h : n = m)
    (x : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) n)
    (y : AssociatedGraded.power (M := sectionsLimit F U.1) (I.ideal U) m)
    (hxy : (x : sectionsLimit F U.1) = y) :
    HEq (transitionMk I F U n x) (transitionMk I F U m y) := by
  subst m
  obtain rfl := Subtype.ext hxy
  rfl

private lemma affineOpenTransitionAction_assoc {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n i j : ℕ)
    (x : (transitionKernelPiece F n).val.obj (op U.1))
    (a : ((conormalPushforward I).piece i).val.obj (op U.1))
    (b : ((conormalPushforward I).piece j).val.obj (op U.1)) :
    HEq (affineOpenTransitionAction I F U (n + i) j
      (affineOpenTransitionAction I F U n i x a) b)
      (affineOpenTransitionAction I F U n (i + j) x
        (((conormalPushforward I).mul i j).app (op U.1) a b)) := by
  obtain ⟨x, rfl⟩ := transitionMk_surjective I F U n x
  obtain ⟨a, rfl⟩ := conormalLocalMap_surjective I U i a
  obtain ⟨b, rfl⟩ := conormalLocalMap_surjective I U j b
  rw [affineOpenTransitionAction_mk, affineOpenTransitionAction_mk,
    conormalLocalMap_mul, affineOpenTransitionAction_mk]
  apply transitionMk_heq I F U (Nat.add_assoc n i j)
  show (b : Γ(X, U.1)) • ((a : Γ(X, U.1)) • (x : sectionsLimit F U.1)) =
    ((a : Γ(X, U.1)) * (b : Γ(X, U.1))) • (x : sectionsLimit F U.1)
  rw [mul_smul, smul_comm]

private lemma affineOpenTransitionAction_one {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I)
    (U : X.affineOpens) (n : ℕ)
    (x : (transitionKernelPiece F n).val.obj (op U.1)) :
    affineOpenTransitionAction I F U n 0 x
        ((conormalPushforward I).one.eval (op U.1)) = x := by
  obtain ⟨x, rfl⟩ := transitionMk_surjective I F U n x
  rw [← conormalLocalMap_one, affineOpenTransitionAction_mk]
  congr 1
  exact Subtype.ext (one_smul _ _)

end ProjectionComparison

section BasisExtension

local instance moduleOfSectionsBE {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

end BasisExtension

section GradedModuleConstruction

local instance moduleOfSectionsGM {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

end GradedModuleConstruction

end Stacks.Coherent

end
