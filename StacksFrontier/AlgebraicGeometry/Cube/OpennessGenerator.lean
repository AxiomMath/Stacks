module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessComplexes
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleDegreeZero
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection

/-!
# The trivializing section of a fibre, as a cocycle of the Čech complex

In the notation of `StacksFrontier/AlgebraicGeometry/Cube/OpennessSetup.lean`, let `𝔭` be a prime of
`R` and suppose the restriction of `L` to the fibre `Q_{κ(𝔭)}` of `Q ⟶ Spec R` is trivial, by
`τ`. Then the section `τ⁻¹(1)` of the fibre is a degree-zero cocycle `x` of `C ⊗_R κ(𝔭)`, through
the base-change identification of Čech complexes, and a degree-zero cocycle of `C` lifting `x` up
to a scalar `s ∉ 𝔭` is a global section of `L` whose restriction to the fibre is a unit multiple
of `τ⁻¹(1)`.

## Main results

* `AlgebraicGeometry.Cube.Openness.exists_fibre_cocycle`: the section `τ⁻¹(1)` is a
  degree-zero cocycle of `C ⊗_R κ(𝔭)`, and a cocycle of `C` lifting it up to a scalar is a global
  section of `L` restricting to a unit multiple of `τ⁻¹(1)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StacksDraft.ConeLift (bcObj bcMap bcUnit)

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness


section Generic

variable {A K : Type u} [CommRing A] [Field K] (φ : A →+* K) {Z Z' : Scheme.{u}}
  (h : Z ⟶ Spec (.of A)) [IsSeparated h] (h' : Z' ⟶ Spec (.of K)) (g : Z' ⟶ Z)
  (hsq : IsPullback g h' h (Spec.map (CommRingCat.ofHom φ))) (L : Z.Modules) [L.IsQuasicoherent]
  {I : Type u} [Finite I] (U : I → Z.Opens) (hUa : ∀ i, IsAffineOpen (U i))

/-- A `K`-linear map `e : M ⟶ N` sends `y = s • z`, with `s : A` acting through `ρ : A →+* K`,
to `e y = ρ s • e z`. -/
theorem hom_eq_smul_of_eq_smul {A K : Type u} [CommRing A] [CommRing K] (ρ : A →+* K)
    {M N : ModuleCat.{u} K} (e : M ⟶ N) (y z : (ModuleCat.restrictScalars.{u} ρ).obj M) (s : A)
    (h : y = s • z) : e.hom y = ρ s • e.hom z := by
  subst h
  exact e.hom.map_smul (ρ s) z

/-- The restriction map to degree-zero cochains is linear for the module structure of the Čech
module. -/
theorem sectionsToAlternatingₗ_smul {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of A)) {K : Type u} (V : K → Z.Opens) (N : Z.Modules)
    (hVW : ∀ i, V i ≤ ⊤) (a : A) (t : Γ(N, ⊤)) :
    (letI := Stacks.Cech.sectionsModule h N ⊤
     (Stacks.Cech.sectionsToAlternatingₗ h V N hVW (a • t) :
       Stacks.Cech.alternatingCechModuleObj h V N 0)) =
      a • (Stacks.Cech.sectionsToAlternatingₗ h V N hVW t :
        Stacks.Cech.alternatingCechModuleObj h V N 0) :=
  let := Stacks.Cech.sectionsModule h N ⊤
  (Stacks.Cech.sectionsToAlternatingₗ h V N hVW).map_smul a t

/-- A degree-zero alternating Čech cocycle of a cover of `⊤` is the restriction of a global
section. -/
theorem exists_section_of_cocycle {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of A)) {K : Type u} (V : K → Z.Opens) (N : Z.Modules)
    (hVW : ∀ i, V i ≤ ⊤) (hcov : (⊤ : Z.Opens) ≤ ⨆ i, V i)
    (c : Stacks.Cech.alternatingCechModuleObj h V N 0)
    (hc : (Stacks.Cech.alternatingCechModuleDiff h V N 0).hom c = 0) :
    ∃ σ : Γ(N, ⊤), Stacks.Cech.sectionsToAlternatingₗ h V N hVW σ = c := by
  let := Stacks.Cech.sectionsModule h N ⊤
  let := Stacks.Cech.cochainModule h V N 0
  let := Stacks.Cech.cochainModule h V N 1
  have hker : c ∈ LinearMap.ker (Stacks.Cech.alternatingCechModuleD h V N 0) := hc
  rw [← Stacks.Cech.range_sectionsToAlternatingₗ h V N hVW hcov] at hker
  exact hker

/-- The degreewise base-change identification of the alternating Čech complex with that of the
fibre. -/
abbrev fibreIso (p : ℕ) :=
  Stacks.Cech.alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) L
    (fun _ => rfl) φ h h' (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) hsq hUa p

include hsq hUa in
/-- **The trivializing section of a fibre, as a cocycle of the Čech complex, and the dictionary
with global sections.** Let `Z' = Z ×_{Spec A} Spec K` and let `τ` trivialize `L` on `Z'`. The
section `τ⁻¹(1)` is a degree-zero cocycle `x` of `Č(U, L) ⊗_A K`, and a degree-zero cocycle `c`
of `Č(U, L)` with `1 ⊗ c = s • x`, `φ s ≠ 0`, is a global section of `L` whose restriction to
the fibre is a unit multiple of `τ⁻¹(1)`. -/
theorem exists_fibre_cocycle (hU : (⊤ : Z.Opens) = ⨆ i, U i)
    (τ : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit _) :
    ∃ x : bcObj φ ((Stacks.Cech.alternatingCechModuleComplex h U L).X 0),
      (bcMap φ ((Stacks.Cech.alternatingCechModuleComplex h U L).d 0 1)).hom x = 0 ∧
      ∀ c : (Stacks.Cech.alternatingCechModuleComplex h U L).X 0,
        ((Stacks.Cech.alternatingCechModuleComplex h U L).d 0 1).hom c = 0 →
        ∀ s : A, φ s ≠ 0 → (bcUnit φ _).hom c = s • x →
        ∃ σ : Γ(L, ⊤), IsUnit (show Γ(Z', ⊤) from
          τ.hom.val.app (op ⊤) (pullbackSectionHom g L ⊤ ⊤ le_rfl σ)) := by
  classical
  have hUW : ∀ i, U i ≤ ⊤ := fun _ => le_top
  have hUW' : ∀ i, g ⁻¹ᵁ U i ≤ ⊤ := fun _ => le_top
  have hcov : (⊤ : Z.Opens) ≤ ⨆ i, U i := hU.le
  have hcov' : (⊤ : Z'.Opens) ≤ ⨆ i, g ⁻¹ᵁ U i :=
    (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.top_eq_iSup_preimage g U hU).le
  obtain ⟨τ1, hτ1⟩ : ∃ τ1 : Γ((Scheme.Modules.pullback g).obj L, ⊤),
      τ.hom.val.app (op ⊤) τ1 = (1 : Γ(Z', ⊤)) :=
    ⟨τ.inv.val.app (op ⊤) (1 : Γ(Z', ⊤)),
      congrArg (fun ψ => ψ.val.app (op ⊤) (1 : Γ(Z', ⊤))) τ.inv_hom_id⟩
  obtain ⟨x0, hx0⟩ : ∃ x0 : Stacks.Cech.alternatingCechModuleObj h' (fun i => g ⁻¹ᵁ U i)
      ((Scheme.Modules.pullback g).obj L) 0,
      Stacks.Cech.sectionsToAlternatingₗ h' (fun i => g ⁻¹ᵁ U i) _ hUW' τ1 = x0 := ⟨_, rfl⟩
  have hdx0 : (Stacks.Cech.alternatingCechModuleDiff h' (fun i => g ⁻¹ᵁ U i)
      ((Scheme.Modules.pullback g).obj L) 0).hom x0 = 0 := by
    let := Stacks.Cech.sectionsModule h' ((Scheme.Modules.pullback g).obj L) ⊤
    let := Stacks.Cech.cochainModule h' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj L) 0
    let := Stacks.Cech.cochainModule h' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj L) 1
    have hmem : x0 ∈ LinearMap.range
        (Stacks.Cech.sectionsToAlternatingₗ h' (fun i => g ⁻¹ᵁ U i) _ hUW') := ⟨τ1, hx0⟩
    rw [Stacks.Cech.range_sectionsToAlternatingₗ h' _ _ hUW' hcov'] at hmem
    exact hmem
  have hcomm := Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comm g U (fun i => g ⁻¹ᵁ U i)
    (Equiv.refl _) L (fun _ => rfl) φ h h' (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) hsq
    hUa 0
  refine ⟨(fibreIso φ h h' g hsq L U hUa 0).inv.hom x0, ?_, ?_⟩
  · have hcomm' : (fibreIso φ h h' g hsq L U hUa 0).inv ≫ (ModuleCat.extendScalars φ).map
        (Stacks.Cech.alternatingCechModuleDiff h U L 0) =
        Stacks.Cech.alternatingCechModuleDiff h' (fun i => g ⁻¹ᵁ U i)
          ((Scheme.Modules.pullback g).obj L) 0 ≫ (fibreIso φ h h' g hsq L U hUa 1).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have hh := congrArg (fun m => m.hom x0) hcomm'
    change ((ModuleCat.extendScalars φ).map (Stacks.Cech.alternatingCechModuleDiff h U L 0)).hom
        ((fibreIso φ h h' g hsq L U hUa 0).inv.hom x0) = 0
    refine hh.trans ?_
    change (fibreIso φ h h' g hsq L U hUa 1).inv.hom
      ((Stacks.Cech.alternatingCechModuleDiff h' (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj L) 0).hom x0) = 0
    rw [hdx0]
    exact (fibreIso φ h h' g hsq L U hUa 1).inv.hom.map_zero
  · intro c hc s hs hcx
    have hc' : (Stacks.Cech.alternatingCechModuleDiff h U L 0).hom c = 0 := hc
    obtain ⟨σ, hσ⟩ := exists_section_of_cocycle h U L hUW hcov c hc'
    refine ⟨σ, ?_⟩
    have h1 : (fibreIso φ h h' g hsq L U hUa 0).hom.hom ((bcUnit φ _).hom c) =
        Stacks.Cech.alternatingCochainBaseChangeₗ g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) L
          (fun _ => rfl) φ h h' (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) 0 c :=
      Stacks.Cech.alternatingCechModuleObjBaseChangeIso_hom_one_tmul _ _ _ _ _ _ _ _ _ _ _ _ 0 c
    have h2 := Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ h U L hUW g
      (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) (fun _ => rfl) φ h'
      (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) σ
    have h3 : (fibreIso φ h h' g hsq L U hUa 0).hom.hom
        ((fibreIso φ h h' g hsq L U hUa 0).inv.hom x0) = x0 :=
      congrArg (fun m => m.hom x0) (fibreIso φ h h' g hsq L U hUa 0).inv_hom_id
    have hcx' := hom_eq_smul_of_eq_smul φ (fibreIso φ h h' g hsq L U hUa 0).hom _ _ s hcx
    rw [h3] at hcx'
    have h2' := (congrArg (fun z => Stacks.Cech.alternatingCochainBaseChangeₗ g U
      (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) L (fun _ => rfl) φ h h'
      (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) 0 z) hσ).symm.trans h2
    have hfin := hcx'.symm.trans (h1.trans h2')
    rw [← hx0] at hfin
    have h4 := (Stacks.Cech.sectionsToAlternatingₗ_injective h' _ _ hUW' hcov'
      ((sectionsToAlternatingₗ_smul h' _ _ hUW' (φ s) τ1).trans hfin)).symm
    have h5 : pullbackSectionHom g L ⊤ ⊤ le_rfl σ = Stacks.Cech.pullbackSections g L ⊤ σ :=
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.pullbackSectionsBaseₗ_top_apply φ
        h h' g L (Stacks.Cech.baseRingHom_comp_app _ _ _ _ hsq) σ).symm
    have hval : (show Γ(Z', ⊤) from
        τ.hom.val.app (op ⊤) (pullbackSectionHom g L ⊤ ⊤ le_rfl σ)) =
        (Stacks.Cech.baseRingHom h' ⊤).hom (φ s) * (1 : Γ(Z', ⊤)) := by
      rw [h5, h4]
      refine ((τ.hom.val.app (op ⊤)).hom.map_smul
        ((Stacks.Cech.baseRingHom h' ⊤).hom (φ s)) τ1).trans ?_
      rw [hτ1]
      rfl
    rw [hval, mul_one]
    exact (isUnit_iff_ne_zero.2 hs).map _

end Generic

end AlgebraicGeometry.Cube.Openness

end

end
