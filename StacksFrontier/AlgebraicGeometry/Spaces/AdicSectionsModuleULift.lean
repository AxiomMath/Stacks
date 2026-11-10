module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicSectionsOfSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Formal functions in degree zero and the universe lift of the module sections

Let `F` be an algebraic space, `𝓘 ⊆ 𝒪_F` a sheaf of ideals and `K` an `𝒪_F`-module with
sections in the universe `u` of the schemes, and `K↑` its universe lift to `u + 1`. If
`H⁰(F, K) ⟶ limₙ H⁰(F, K / 𝓘 ^ (n + 1) K)` is bijective, so is the same map for any module `H`
isomorphic to `K↑`. The ideal-power quotients of `K↑` are the universe lifts of those of `K`,
and the global sections of `K↑` are those of `K`.

## Main definitions

* `AlgebraicGeometry.Space.adicQuotientModuleULiftIso` — `K↑ / 𝓘 ^ n K↑ ≅ (K / 𝓘 ^ n K)↑`,
  compatible with the projections from `K↑`.
* `AlgebraicGeometry.Space.sectionsModuleULiftEquiv` — `H⁰(F, K↑) ≃ H⁰(F, K)`.

## Main results

* `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_moduleULift` — the transport to
  `K↑` itself.
* `AlgebraicGeometry.Space.bijective_adicSectionsOfSections_of_moduleULift_iso` — the
  transport to any module isomorphic to `K↑`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasCokernels_modules hasCokernels_modules_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The universe lift `K↑` of an `𝒪_F`-module with sections in `u` to the module universe
`u + 1`. -/
abbrev moduleULiftSucc (K : Modules.{u, u} B S hS F hF) : Modules.{u, u + 1} B S hS F hF :=
  (Stacks.SheafOfModules.moduleULift.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K

/-- The universe lift of a morphism. -/
abbrev moduleULiftSuccMap {K K' : Modules.{u, u} B S hS F hF} (g : K ⟶ K') :
    moduleULiftSucc B S hS F hF K ⟶ moduleULiftSucc B S hS F hF K' :=
  (Stacks.SheafOfModules.moduleULift.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).map g

/-! ### Submodules and the universe lift -/

variable {B S hS F hF} in
/-- The submodule of `K↑` of the sections whose underlying section lies in a submodule `P` of
`K`. -/
def pullupSubmodule {K : Modules.{u, u} B S hS F hF} (P : K.Submodule) :
    (moduleULiftSucc B S hS F hF K).Submodule where
  obj X :=
    { carrier := {x | x.down ∈ P.obj X}
      add_mem' := fun {_ _} ha hb => P.obj X |>.add_mem ha hb
      zero_mem' := (P.obj X).zero_mem
      smul_mem' := fun r _ hx => (P.obj X).smul_mem r hx }
  map {_ _} g _ hx := P.map g hx
  isSheaf _ x hx := P.isSheaf x.down hx

variable {B S hS F hF} in
/-- The submodule of `K` of the sections whose universe lift lies in a submodule `P'` of
`K↑`. -/
def pulldownSubmodule {K : Modules.{u, u} B S hS F hF}
    (P' : (moduleULiftSucc B S hS F hF K).Submodule) : K.Submodule where
  obj X :=
    { carrier := {y | (ULift.up y : (moduleULiftSucc B S hS F hF K).val.obj X) ∈ P'.obj X}
      add_mem' := fun {_ _} ha hb => (P'.obj X).add_mem ha hb
      zero_mem' := (P'.obj X).zero_mem
      smul_mem' := fun r _ hx => (P'.obj X).smul_mem r hx }
  map {_ _} g _ hx := P'.map g hx
  isSheaf _ y hy := P'.isSheaf (ULift.up y) hy

/-- `𝓘 ^ k K↑` lies in the lift of `𝓘 ^ k K`. -/
theorem idealPowerSubsheaf_moduleULift_le_pullup (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    idealPowerSubsheaf B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) ≤
      pullupSubmodule (idealPowerSubsheaf B S hS F hF 𝓘 k K) := by
  rw [idealPowerSubsheaf_le_iff]
  refine fun U => Submodule.smul_le.2 fun r hr x _ => ?_
  exact le_idealPowerSubsheaf_obj B S hS F hF 𝓘 k K U
    (Submodule.smul_mem_smul hr Submodule.mem_top)

/-- `𝓘 ^ k K` lies in the descent of `𝓘 ^ k K↑`. -/
theorem idealPowerSubsheaf_le_pulldown_moduleULift (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    idealPowerSubsheaf B S hS F hF 𝓘 k K ≤
      pulldownSubmodule (idealPowerSubsheaf B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K)) := by
  rw [idealPowerSubsheaf_le_iff]
  refine fun U => Submodule.smul_le.2 fun r hr y _ => ?_
  exact le_idealPowerSubsheaf_obj B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) U
    (Submodule.smul_mem_smul hr Submodule.mem_top)

/-- The lift of the inclusion of `𝓘 ^ k K`, factored through `𝓘 ^ k K↑`. -/
def idealPowerSubsheafModuleULiftHom (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSucc B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).toSheafOfModules ⟶
      (idealPowerSubsheaf B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K)).toSheafOfModules :=
  Stacks.SheafOfModules.sheafFactorThruSubmodule
    (moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι) _
    (fun _ m => idealPowerSubsheaf_le_pulldown_moduleULift B S hS F hF 𝓘 k K _ m.down.2)

/-- `idealPowerSubsheafModuleULiftHom` followed by the inclusion of `𝓘 ^ k K↑` is the lift of
the inclusion of `𝓘 ^ k K`. -/
@[reassoc (attr := simp)]
theorem idealPowerSubsheafModuleULiftHom_ι (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    idealPowerSubsheafModuleULiftHom B S hS F hF 𝓘 k K ≫
        (idealPowerSubsheaf B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K)).ι =
      moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι :=
  Stacks.SheafOfModules.sheafFactorThruSubmodule_ι _ _ _

/-- The lift of `𝓘 ^ k K` is isomorphic to `𝓘 ^ k K↑` via `idealPowerSubsheafModuleULiftHom`. -/
instance isIso_idealPowerSubsheafModuleULiftHom (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    IsIso (idealPowerSubsheafModuleULiftHom B S hS F hF 𝓘 k K) := by
  refine isIso_of_forall_bijective_val_app_affine_chart B S hS ⟨F, hF⟩ _ fun V _ => ⟨?_, ?_⟩
  · exact fun a b hab => congrArg ULift.up (Subtype.ext
      (congrArg (fun z => (z.1 : (moduleULiftSucc B S hS F hF K).val.obj (op V)).down) hab))
  · exact fun x => ⟨ULift.up ⟨x.1.down,
      idealPowerSubsheaf_moduleULift_le_pullup B S hS F hF 𝓘 k K _ x.2⟩, rfl⟩

/-! ### The ideal-power quotients and the universe lift -/

/-- The sections killed by the projection `K ⟶ K / 𝓘 ^ k K` lie in the local closure of the range
of the inclusion of `𝓘 ^ k K`. -/
theorem mem_localClosure_of_smallEtaleAdicQuotientProjection_eq_zero (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ)
    (x : K.val.obj X)
    (hx : (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K).val.app X x = 0) :
    x ∈ (Stacks.SheafOfModules.localClosure K (Stacks.SheafOfModules.presheafRangeSubmodule
      (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι.val)).obj X := by
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  set P := idealPowerSubsheaf B S hS F hF 𝓘 k K
  set π := smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K
  have hP := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel P.ι)
  let l := hP.lift (KernelFork.ofι (Stacks.SheafOfModules.kerSubmodule π).ι
    (Stacks.SheafOfModules.kerSubmodule_ι_comp π))
  have hl : l ≫ P.ι = (Stacks.SheafOfModules.kerSubmodule π).ι :=
    hP.fac _ WalkingParallelPair.zero
  have hmem : x ∈ P.obj X := by
    have h : (l ≫ P.ι).val.app X ⟨x, hx⟩ = x := by rw [hl]; rfl
    exact h ▸ (l.val.app X ⟨x, hx⟩).2
  refine (Stacks.SheafOfModules.mem_localClosure_obj _ X x).2
    (GrothendieckTopology.superset_covering _ (fun Y g _ => ?_)
      (GrothendieckTopology.top_mem _ X.unop))
  exact ⟨⟨_, P.map g.op hmem⟩, rfl⟩

/-- The inclusion of `𝓘 ^ k K↑` followed by the lift of the projection `K ⟶ K / 𝓘 ^ k K` is
zero. -/
theorem idealPowerSubsheaf_ι_comp_moduleULiftSuccMap_projection (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    (idealPowerSubsheaf B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K)).ι ≫
        moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) =
      0 := by
  rw [← cancel_epi (idealPowerSubsheafModuleULiftHom B S hS F hF 𝓘 k K),
    idealPowerSubsheafModuleULiftHom_ι_assoc, ← Functor.map_comp, cokernel.condition,
    Functor.map_zero, comp_zero]

/-- The lift of the inclusion of `𝓘 ^ k K` followed by the projection `K↑ ⟶ K↑ / 𝓘 ^ k K↑` is
zero. -/
theorem moduleULiftSuccMap_ι_comp_projection (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) = 0 := by
  rw [← idealPowerSubsheafModuleULiftHom_ι, Category.assoc, cokernel.condition, comp_zero]

/-- The lift of the cokernel of the inclusion of `𝓘 ^ k K` is the cokernel of its lift. -/
def adicQuotientModuleULiftCokernelIso (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    cokernel (moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι) ≅
      moduleULiftSucc B S hS F hF (smallEtaleAdicQuotient B S hS F hF 𝓘 k K) :=
  Stacks.SheafOfModules.cokernelIsoMapCokernelModuleULift.{u + 1}
    (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι
    (mem_localClosure_of_smallEtaleAdicQuotientProjection_eq_zero B S hS F hF 𝓘 k K)

/-- `adicQuotientModuleULiftCokernelIso` carries the cokernel projection to the lift of the
projection `K ⟶ K / 𝓘 ^ k K`. -/
theorem cokernel_π_comp_adicQuotientModuleULiftCokernelIso_hom (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    cokernel.π (moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι) ≫
        (adicQuotientModuleULiftCokernelIso B S hS F hF 𝓘 k K).hom =
      moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

/-- The inverse of `adicQuotientModuleULiftCokernelIso` carries the lift of the projection
`K ⟶ K / 𝓘 ^ k K` to the cokernel projection. -/
theorem moduleULiftSuccMap_projection_comp_cokernelIso_inv (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) ≫
        (adicQuotientModuleULiftCokernelIso B S hS F hF 𝓘 k K).inv =
      cokernel.π (moduleULiftSuccMap B S hS F hF (idealPowerSubsheaf B S hS F hF 𝓘 k K).ι) := by
  rw [← cokernel_π_comp_adicQuotientModuleULiftCokernelIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The lift of the projection `K ⟶ K / 𝓘 ^ k K` is an epimorphism. -/
instance epi_moduleULiftSuccMap_projection (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    Epi (moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K)) :=
  Stacks.SheafOfModules.epi_moduleULift_map_cokernel_π _

/-- The map `K↑ / 𝓘 ^ k K↑ ⟶ (K / 𝓘 ^ k K)↑`. -/
def adicQuotientModuleULiftHom (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) ⟶
      moduleULiftSucc B S hS F hF (smallEtaleAdicQuotient B S hS F hF 𝓘 k K) :=
  cokernel.desc _ _ (idealPowerSubsheaf_ι_comp_moduleULiftSuccMap_projection B S hS F hF 𝓘 k K)

/-- The map `(K / 𝓘 ^ k K)↑ ⟶ K↑ / 𝓘 ^ k K↑`. -/
def adicQuotientModuleULiftInv (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSucc B S hS F hF (smallEtaleAdicQuotient B S hS F hF 𝓘 k K) ⟶
      smallEtaleAdicQuotient B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) :=
  (adicQuotientModuleULiftCokernelIso B S hS F hF 𝓘 k K).inv ≫
    cokernel.desc _ _ (moduleULiftSuccMap_ι_comp_projection B S hS F hF 𝓘 k K)

/-- The projection `K↑ ⟶ K↑ / 𝓘 ^ k K↑` followed by `adicQuotientModuleULiftHom` is the lift of
the projection `K ⟶ K / 𝓘 ^ k K`. -/
theorem projection_comp_adicQuotientModuleULiftHom (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) ≫
        adicQuotientModuleULiftHom B S hS F hF 𝓘 k K =
      moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) :=
  cokernel.π_desc _ _ _

/-- The lift of the projection `K ⟶ K / 𝓘 ^ k K` followed by `adicQuotientModuleULiftInv` is
the projection `K↑ ⟶ K↑ / 𝓘 ^ k K↑`. -/
theorem moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftInv (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) ≫
        adicQuotientModuleULiftInv B S hS F hF 𝓘 k K =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) := by
  rw [adicQuotientModuleULiftInv, ← Category.assoc,
    moduleULiftSuccMap_projection_comp_cokernelIso_inv, cokernel.π_desc]

/-- **`K↑ / 𝓘 ^ k K↑ ≅ (K / 𝓘 ^ k K)↑`**, compatibly with the projections from `K↑`. -/
def adicQuotientModuleULiftIso (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotient B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) ≅
      moduleULiftSucc B S hS F hF (smallEtaleAdicQuotient B S hS F hF 𝓘 k K) where
  hom := adicQuotientModuleULiftHom B S hS F hF 𝓘 k K
  inv := adicQuotientModuleULiftInv B S hS F hF 𝓘 k K
  hom_inv_id := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k
      (moduleULiftSucc B S hS F hF K))).1 ?_
    rw [← Category.assoc, projection_comp_adicQuotientModuleULiftHom,
      moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftInv, Category.comp_id]
  inv_hom_id := by
    refine (cancel_epi (moduleULiftSuccMap B S hS F hF
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K))).1 ?_
    rw [← Category.assoc, moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftInv,
      projection_comp_adicQuotientModuleULiftHom, Category.comp_id]

/-- `adicQuotientModuleULiftIso` is compatible with the projections from `K↑`. -/
@[reassoc (attr := simp)]
theorem smallEtaleAdicQuotientProjection_comp_adicQuotientModuleULiftIso_hom (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) ≫
        (adicQuotientModuleULiftIso B S hS F hF 𝓘 k K).hom =
      moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) :=
  projection_comp_adicQuotientModuleULiftHom B S hS F hF 𝓘 k K

/-- The inverse of `adicQuotientModuleULiftIso` is compatible with the projections from `K↑`. -/
@[reassoc (attr := simp)]
theorem moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftIso_inv (k : ℕ)
    (K : Modules.{u, u} B S hS F hF) :
    moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k K) ≫
        (adicQuotientModuleULiftIso B S hS F hF 𝓘 k K).inv =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) :=
  moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftInv B S hS F hF 𝓘 k K

/-- The isomorphisms commute with the transition maps. -/
theorem adicQuotientModuleULiftIso_inv_comp_transition (k : ℕ) (K : Modules.{u, u} B S hS F hF) :
    (adicQuotientModuleULiftIso B S hS F hF 𝓘 (k + 1) K).inv ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓘 k (moduleULiftSucc B S hS F hF K) =
      moduleULiftSuccMap B S hS F hF (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 k K) ≫
        (adicQuotientModuleULiftIso B S hS F hF 𝓘 k K).inv := by
  refine (cancel_epi (moduleULiftSuccMap B S hS F hF
    (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (k + 1) K))).1 ?_
  rw [moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftIso_inv_assoc,
    smallEtaleAdicQuotientProjection_comp_transition, ← Functor.map_comp_assoc,
    smallEtaleAdicQuotientProjection_comp_transition,
    moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftIso_inv]

/-! ### Global sections of a universe lift -/

/-- **The global sections of `K↑` are the global sections of `K`.** -/
def sectionsModuleULiftEquiv (K : Modules.{u, u} B S hS F hF) :
    (moduleULiftSucc B S hS F hF K).sections ≃ K.sections where
  toFun s := ⟨fun X => (s.1 X).down, fun f => congrArg ULift.down (s.2 f)⟩
  invFun s := ⟨fun X => ULift.up (s.1 X), fun f => congrArg ULift.up (s.2 f)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inverse of `sectionsModuleULiftEquiv` commutes with the maps on global sections. -/
theorem sectionsModuleULiftEquiv_symm_sectionsMap {K K' : Modules.{u, u} B S hS F hF}
    (g : K ⟶ K') (s : K.sections) :
    (sectionsModuleULiftEquiv B S hS F hF K').symm (SheafOfModules.sectionsMap g s) =
      SheafOfModules.sectionsMap (moduleULiftSuccMap B S hS F hF g)
        ((sectionsModuleULiftEquiv B S hS F hF K).symm s) :=
  rfl

/-- `sectionsModuleULiftEquiv` commutes with the maps on global sections. -/
theorem sectionsModuleULiftEquiv_sectionsMap {K K' : Modules.{u, u} B S hS F hF}
    (g : K ⟶ K') (s : (moduleULiftSucc B S hS F hF K).sections) :
    sectionsModuleULiftEquiv B S hS F hF K'
        (SheafOfModules.sectionsMap (moduleULiftSuccMap B S hS F hF g) s) =
      SheafOfModules.sectionsMap g (sectionsModuleULiftEquiv B S hS F hF K s) :=
  rfl

/-! ### The transport of formal functions in degree zero -/

/-- The limits of the sections of the ideal-power quotients of `K` and of `K↑` agree. -/
def adicSectionsModuleULiftMap (K : Modules.{u, u} B S hS F hF)
    (t : adicSections B S hS F hF (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K)) :
    adicSections B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) (moduleULiftSucc B S hS F hF K))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (moduleULiftSucc B S hS F hF K)) :=
  ⟨fun n => SheafOfModules.sectionsMap (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1) K).inv
      ((sectionsModuleULiftEquiv B S hS F hF _).symm (t.1 n)), fun n => by
    rw [← SheafOfModules.sectionsMap_comp, adicQuotientModuleULiftIso_inv_comp_transition,
      SheafOfModules.sectionsMap_comp, ← sectionsModuleULiftEquiv_symm_sectionsMap, t.2 n]⟩

/-- The inverse of `adicSectionsModuleULiftMap`. -/
def adicSectionsModuleULiftInv (K : Modules.{u, u} B S hS F hF)
    (t : adicSections B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) (moduleULiftSucc B S hS F hF K))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (moduleULiftSucc B S hS F hF K))) :
    adicSections B S hS F hF (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K) :=
  ⟨fun n => sectionsModuleULiftEquiv B S hS F hF _
      (SheafOfModules.sectionsMap (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1) K).hom
        (t.1 n)), fun n => by
    have h : (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1 + 1) K).hom ≫
        moduleULiftSuccMap B S hS F hF
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K) =
        smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) (moduleULiftSucc B S hS F hF K) ≫
          (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1) K).hom := by
      rw [← Iso.comp_inv_eq, Category.assoc,
        ← adicQuotientModuleULiftIso_inv_comp_transition, Iso.hom_inv_id_assoc]
    change SheafOfModules.sectionsMap
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) K)
        (sectionsModuleULiftEquiv B S hS F hF
          (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1 + 1) K)
          (SheafOfModules.sectionsMap
            (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1 + 1) K).hom (t.1 (n + 1)))) =
      sectionsModuleULiftEquiv B S hS F hF (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) K)
        (SheafOfModules.sectionsMap (adicQuotientModuleULiftIso B S hS F hF 𝓘 (n + 1) K).hom
          (t.1 n))
    rw [← sectionsModuleULiftEquiv_sectionsMap, ← SheafOfModules.sectionsMap_comp, h,
      SheafOfModules.sectionsMap_comp, t.2 n]⟩

/-- `adicSectionsModuleULiftMap` is bijective. -/
theorem bijective_adicSectionsModuleULiftMap (K : Modules.{u, u} B S hS F hF) :
    Function.Bijective (adicSectionsModuleULiftMap B S hS F hF 𝓘 K) := by
  refine Function.bijective_iff_has_inverse.2 ⟨adicSectionsModuleULiftInv B S hS F hF 𝓘 K,
    fun t => Subtype.ext (funext fun n => ?_), fun t => Subtype.ext (funext fun n => ?_)⟩
  · change sectionsModuleULiftEquiv B S hS F hF _ (SheafOfModules.sectionsMap _
      (SheafOfModules.sectionsMap _ _)) = _
    rw [← SheafOfModules.sectionsMap_comp, Iso.inv_hom_id, SheafOfModules.sectionsMap_id,
      Equiv.apply_symm_apply]
  · change SheafOfModules.sectionsMap _ ((sectionsModuleULiftEquiv B S hS F hF _).symm
      (sectionsModuleULiftEquiv B S hS F hF _ (SheafOfModules.sectionsMap _ _))) = _
    rw [Equiv.symm_apply_apply, ← SheafOfModules.sectionsMap_comp, Iso.hom_inv_id,
      SheafOfModules.sectionsMap_id]

/-- `adicSectionsOfSections` for `K↑` is that of `K` read through the two identifications. -/
theorem adicSectionsOfSections_moduleULift (K : Modules.{u, u} B S hS F hF)
    (σ : (moduleULiftSucc B S hS F hF K).sections) :
    adicSectionsOfSections B S hS F hF 𝓘 (moduleULiftSucc B S hS F hF K) σ =
      adicSectionsModuleULiftMap B S hS F hF 𝓘 K
        (adicSectionsOfSections B S hS F hF 𝓘 K (sectionsModuleULiftEquiv B S hS F hF K σ)) := by
  refine Subtype.ext (funext fun n => ?_)
  change _ = SheafOfModules.sectionsMap _ ((sectionsModuleULiftEquiv B S hS F hF _).symm
    (SheafOfModules.sectionsMap _ (sectionsModuleULiftEquiv B S hS F hF K σ)))
  rw [sectionsModuleULiftEquiv_symm_sectionsMap, Equiv.symm_apply_apply,
    ← SheafOfModules.sectionsMap_comp,
    moduleULiftSuccMap_projection_comp_adicQuotientModuleULiftIso_inv]
  rfl

/-- **Formal functions in degree zero pass to the universe lift.** -/
theorem bijective_adicSectionsOfSections_moduleULift (K : Modules.{u, u} B S hS F hF)
    (h : Function.Bijective (adicSectionsOfSections B S hS F hF 𝓘 K)) :
    Function.Bijective
      (adicSectionsOfSections B S hS F hF 𝓘 (moduleULiftSucc B S hS F hF K)) := by
  have e : adicSectionsOfSections B S hS F hF 𝓘 (moduleULiftSucc B S hS F hF K) =
      adicSectionsModuleULiftMap B S hS F hF 𝓘 K ∘ adicSectionsOfSections B S hS F hF 𝓘 K ∘
        sectionsModuleULiftEquiv B S hS F hF K :=
    funext (adicSectionsOfSections_moduleULift B S hS F hF 𝓘 K)
  rw [e]
  exact (bijective_adicSectionsModuleULiftMap B S hS F hF 𝓘 K).comp
    (h.comp (sectionsModuleULiftEquiv B S hS F hF K).bijective)

/-- **Formal functions in degree zero pass to any module isomorphic to the universe lift**: if
`H⁰(F, K) ⟶ limₙ H⁰(F, K / 𝓘 ^ (n + 1) K)` is bijective for `K` with sections in `u`, then so is
`H⁰(F, H) ⟶ limₙ H⁰(F, H / 𝓘 ^ (n + 1) H)` for every `H ≅ K↑` with sections in `u + 1`. -/
theorem bijective_adicSectionsOfSections_of_moduleULift_iso (K : Modules.{u, u} B S hS F hF)
    (H : Modules.{u, u + 1} B S hS F hF)
    (e : (Stacks.SheafOfModules.moduleULift.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K ≅ H)
    (h : Function.Bijective (adicSectionsOfSections B S hS F hF 𝓘 K)) :
    Function.Bijective (adicSectionsOfSections B S hS F hF 𝓘 H) :=
  bijective_adicSectionsOfSections_of_iso B S hS F hF 𝓘 e
    (bijective_adicSectionsOfSections_moduleULift B S hS F hF 𝓘 K h)

end AlgebraicGeometry.Space

end
