module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.AffineModel
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Lifting global sections along a closed base change, when the Čech differential is onto

Let `f : Y ⟶ Spec A` be separated, covered by two affine opens, let `ℱ` be a quasi-coherent
`𝒪_Y`-module and let `φ : A ⟶ A'` be surjective, with `Y' = Y ×_A A'`. If the two-term Čech
differential `C⁰(ℱ) ⟶ C¹(ℱ)` is onto (for instance when `ℱ` is invertible and all fibres of
`ℱ` have vanishing `H¹`, `Stacks.TwoAffineCech.surjective_cechD_of_fibres`), then every global
section of the pullback of `ℱ` to `Y'` lifts to a global section of `ℱ`.

This is the step of the infinitesimal lifting argument for the smoothness of the morphism
`γ_d` of [Stacks, Tag 0BA0], clause (5), in which a section of an invertible module on
`X_{A/I}` is extended to `X_A`.

## Main results

* `Stacks.AbelMap.exists_ker_tmul_eq`: the linear algebra.
* `Stacks.AbelMap.exists_pullbackSections_eq`: the lift of global sections.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.AbelMap

section Linear

variable {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module C M] [Module C N]

/-- Over a surjective ring map `C ⟶ B`, an element of `N` killed by `N ⟶ B ⊗ N` lies in
`ker(C ⟶ B) • N`. -/
theorem mem_smul_top_of_one_tmul_eq_zero (hφ : Function.Surjective (algebraMap C B)) (n : N)
    (hn : (1 : B) ⊗ₜ[C] n = 0) : n ∈ RingHom.ker (algebraMap C B) • (⊤ : Submodule C N) := by
  let I := RingHom.ker (algebraMap C B)
  have hex : Function.Exact I.subtype (Algebra.linearMap C B) := by
    intro c
    simp [I, RingHom.mem_ker]
  have hsurj : Function.Surjective (Algebra.linearMap C B) := hφ
  have hrt := rTensor_exact N hex hsurj
  have h1 : (Algebra.linearMap C B).rTensor N ((1 : C) ⊗ₜ n) = 0 := by
    simpa using hn
  obtain ⟨z, hz⟩ := (hrt _).mp h1
  have hn' : n = TensorProduct.lid C N ((I.subtype).rTensor N z) := by
    rw [hz, TensorProduct.lid_tmul, one_smul]
  have key : ∀ w : I ⊗[C] N, TensorProduct.lid C N ((I.subtype).rTensor N w) ∈
      I • (⊤ : Submodule C N) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact Submodule.smul_mem_smul a.2 Submodule.mem_top
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  rw [hn']
  exact key z

/-- **Lifting a cocycle along a surjective ring map when the differential is onto.** Let
`d : M ⟶ N` be onto and `C ⟶ B` surjective. Every `y ∈ B ⊗ M` killed by `d ⊗ B` is `1 ⊗ x` for
some `x ∈ ker d`. -/
theorem exists_ker_tmul_eq (hφ : Function.Surjective (algebraMap C B)) (d : M →ₗ[C] N)
    (hd : Function.Surjective d) (y : B ⊗[C] M) (hy : d.baseChange B y = 0) :
    ∃ x : M, d x = 0 ∧ (1 : B) ⊗ₜ[C] x = y := by
  let I := RingHom.ker (algebraMap C B)
  have hgen : ∀ y : B ⊗[C] M, ∃ x : M, (1 : B) ⊗ₜ[C] x = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b m =>
      obtain ⟨c, rfl⟩ := hφ b
      exact ⟨c • m, by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, by rw [TensorProduct.tmul_add]⟩
  have hkill : ∀ x ∈ I • (⊤ : Submodule C M), (1 : B) ⊗ₜ[C] x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun x₁ x₂ h₁ h₂ => ?_)
    · rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        (RingHom.mem_ker).mp ha, zero_mul, TensorProduct.zero_tmul]
    · rw [TensorProduct.tmul_add, h₁, h₂, add_zero]
  obtain ⟨x₀, rfl⟩ := hgen y
  have hdx₀ : (1 : B) ⊗ₜ[C] d x₀ = 0 := by simpa using hy
  have hmem := mem_smul_top_of_one_tmul_eq_zero hφ (d x₀) hdx₀
  have hmap : (I • (⊤ : Submodule C M)).map d = I • (⊤ : Submodule C N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hd]
  rw [← hmap] at hmem
  obtain ⟨x₁, hx₁, hdx₁⟩ := hmem
  refine ⟨x₀ - x₁, by rw [map_sub, hdx₁, sub_self], ?_⟩
  rw [TensorProduct.tmul_sub, hkill x₁ hx₁, sub_zero]

end Linear

/-! ### Global sections and Čech cocycles of a two-element cover -/

section Cocycle

open Stacks.TwoAffineCech

variable {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab.{u} X)

/-- A cochain is unchanged, up to the identification of the intersections, by replacing its
index tuple by an equal one. -/
theorem cochain_eq_map {p : ℕ} (c : CechCochains.Cochain U ℱ p) {a b : Fin (p + 1) → I}
    (h : a = b) :
    ℱ.map (eqToHom (by rw [h])).op (c a) = c b := by
  subst h
  simp

/-- Restricting after an identification of opens is restricting. -/
theorem restr_map_eqToHom {V V' W : Opens X} (e : V' = V) (h : W ≤ V') (h' : W ≤ V)
    (y : ToType (ℱ.obj (op V))) :
    CechCochains.restr ℱ h (ℱ.map (eqToHom e).op y) = CechCochains.restr ℱ h' y := by
  subst e
  simp

/-- The intersection over a constant one-element tuple is the open itself. -/
theorem inter_const (j : I) : CechCochains.inter U (fun _ : Fin 1 => j) = U j := by
  simp [CechCochains.inter]

/-- The degree-zero Čech differential, evaluated on a pair of indices. -/
private theorem cechD_zero_apply (x : CechCochains.Cochain U ℱ 0) (a : Fin (0 + 2) → I) :
    CechCochains.cechD U ℱ 0 x a = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr ℱ (CechCochains.inter_le_omit U a j) (x (a ∘ j.succAbove)) := rfl

/-- The union of the opens of a cover is contained in the union of the one-fold intersections. -/
private theorem iSup_le_iSup_inter : ⨆ i, U i ≤ ⨆ a : Fin 1 → I, CechCochains.inter U a :=
  iSup_le fun i => le_iSup_of_le (fun _ => i) (le_iInf fun _ => le_rfl)

/-- The degree-zero cochain of restrictions of a section over an open containing the cover. -/
def restrCochain {W : Opens X} (hW : ∀ i, U i ≤ W) (s : ToType (ℱ.obj (op W))) :
    CechCochains.Cochain U ℱ 0 := fun a =>
  CechCochains.restr ℱ ((iInf_le (fun k => U (a k)) 0).trans (hW (a 0))) s

/-- The restriction cochain of a section is alternating. -/
theorem isAlternating_restrCochain {W : Opens X} (hW : ∀ i, U i ≤ W)
    (s : ToType (ℱ.obj (op W))) : CechCochains.IsAlternating U ℱ (restrCochain U ℱ hW s) :=
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  ⟨fun a ha => (ha (Function.injective_of_subsingleton a)).elim,
    fun _ x y hxy => (hxy (Subsingleton.elim x y)).elim⟩

/-- The restriction cochain of a section is a cocycle. -/
theorem cechD_restrCochain {W : Opens X} (hW : ∀ i, U i ≤ W) (s : ToType (ℱ.obj (op W))) :
    CechCochains.cechD U ℱ 0 (restrCochain U ℱ hW s) = 0 := by
  funext a
  have hle : CechCochains.inter U a ≤ W :=
    (CechCochains.inter_le_omit U a 0).trans ((iInf_le _ 0).trans (hW _))
  have key : ∀ j : Fin (0 + 2), CechCochains.restr ℱ (CechCochains.inter_le_omit U a j)
      (restrCochain U ℱ hW s (a ∘ j.succAbove)) = CechCochains.restr ℱ hle s :=
    fun j => CechCochains.restr_restr ℱ _ _ s
  rw [cechD_zero_apply, Fin.sum_univ_two, key 0, key 1]
  simp

/-- A degree-zero Čech cocycle is a compatible family of sections over the cover. -/
private theorem isCompatible_of_cechD_eq_zero (x : CechCochains.Cochain U ℱ 0)
    (hx : CechCochains.cechD U ℱ 0 x = 0) :
    TopCat.Presheaf.IsCompatible ℱ (fun a : Fin 1 → I => CechCochains.inter U a) x := by
  intro a b
  let c : Fin 2 → I := ![a 0, b 0]
  have hc0 : c ∘ Fin.succAbove 0 = b := by
    funext k
    rw [Subsingleton.elim k 0]
    rfl
  have hc1 : c ∘ Fin.succAbove 1 = a := by
    funext k
    rw [Subsingleton.elim k 0]
    rfl
  have hle : CechCochains.inter U a ⊓ CechCochains.inter U b ≤ CechCochains.inter U c := by
    refine le_iInf fun k => ?_
    fin_cases k
    · exact inf_le_left.trans (iInf_le _ 0)
    · exact inf_le_right.trans (iInf_le _ 0)
  have hA : CechCochains.inter U a ⊓ CechCochains.inter U b ≤
      CechCochains.inter U (c ∘ Fin.succAbove 0) :=
    hle.trans (CechCochains.inter_le_omit U c 0)
  have hB : CechCochains.inter U a ⊓ CechCochains.inter U b ≤
      CechCochains.inter U (c ∘ Fin.succAbove 1) :=
    hle.trans (CechCochains.inter_le_omit U c 1)
  have h : CechCochains.restr ℱ hA (x (c ∘ Fin.succAbove 0)) =
      CechCochains.restr ℱ hB (x (c ∘ Fin.succAbove 1)) := by
    have h0 := congrArg (fun y => CechCochains.restr ℱ hle (y c)) hx
    simp only [CechCochains.Cochain.zero_apply, map_zero] at h0
    rw [cechD_zero_apply, Fin.sum_univ_two, map_add] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      map_neg] at h0
    rwa [CechCochains.restr_restr, CechCochains.restr_restr, add_neg_eq_zero] at h0
  show CechCochains.restr ℱ inf_le_left (x a) = CechCochains.restr ℱ inf_le_right (x b)
  calc CechCochains.restr ℱ inf_le_left (x a)
      = CechCochains.restr ℱ
          (inf_le_left : CechCochains.inter U a ⊓ CechCochains.inter U b ≤ CechCochains.inter U a)
          (ℱ.map (eqToHom (by rw [hc1])).op (x (c ∘ Fin.succAbove 1))) := by
        rw [cochain_eq_map U ℱ x hc1]
    _ = CechCochains.restr ℱ hB (x (c ∘ Fin.succAbove 1)) := restr_map_eqToHom ℱ _ _ hB _
    _ = CechCochains.restr ℱ hA (x (c ∘ Fin.succAbove 0)) := h.symm
    _ = CechCochains.restr ℱ
          (inf_le_right : CechCochains.inter U a ⊓ CechCochains.inter U b ≤ CechCochains.inter U b)
          (ℱ.map (eqToHom (by rw [hc0])).op (x (c ∘ Fin.succAbove 0))) :=
        (restr_map_eqToHom ℱ _ _ hA _).symm
    _ = CechCochains.restr ℱ inf_le_right (x b) := by rw [cochain_eq_map U ℱ x hc0]

/-- **A degree-zero Čech cocycle of a sheaf glues to a section.** -/
theorem exists_restrCochain_eq (F : TopCat.Sheaf Ab.{u} X) {W : Opens X} (hW : ∀ i, U i ≤ W)
    (hcov : W ≤ ⨆ i, U i) (x : CechCochains.Cochain U F.1 0)
    (hx : CechCochains.cechD U F.1 0 x = 0) :
    ∃ s : ToType (F.1.obj (op W)), restrCochain U F.1 hW s = x := by
  let V : (Fin 1 → I) → Opens X := fun a => CechCochains.inter U a
  have hVW : ∀ a, V a ≤ W := fun a => (iInf_le _ 0).trans (hW (a 0))
  have hcov' : W ≤ ⨆ a, V a := hcov.trans (iSup_le_iSup_inter U)
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F V W (fun a => homOfLE (hVW a)) hcov'
    x (isCompatible_of_cechD_eq_zero U F.1 x hx)
  exact ⟨s, funext fun a => hs a⟩

end Cocycle

/-! ### Lifting global sections -/

section Lift

open Stacks.TwoAffineCech

/-- The degree-zero alternating Čech differential on elements is the Čech differential of the
underlying cochains. -/
theorem cechD_apply_coe {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    (U : Cover.{u} → Y.Opens) (F : Y.Modules)
    (c : (Stacks.Cech.alternatingCechModuleComplex f U F).X 0) :
    (cechD f U F c).1 = CechCochains.cechD U F.presheaf 0 c.1 := by
  have h : (Stacks.Cech.alternatingCechModuleComplex f U F).d 0 1 =
      Stacks.Cech.alternatingCechModuleDiff f U F 0 := by
    simp
  show ((ModuleCat.Hom.hom ((Stacks.Cech.alternatingCechModuleComplex f U F).d 0 1)) c).1 = _
  rw [h]
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {Y Y' : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (f' : Y' ⟶ Spec (.of A')) (g : Y' ⟶ Y)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (U : Cover.{u} → Y.Opens) (F : Y.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hU : (⊤ : Y.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

include hsq hU hUaff in
/-- **Global sections lift along a surjective base change when the Čech differential is onto.**
Let `Y` be separated over `Spec A` and covered by two affine opens, `ℱ` quasi-coherent on `Y` with
onto two-term Čech differential, and `Y' = Y ×_A A'` for a surjection `A ⟶ A'`. Then every global
section of the pullback of `ℱ` to `Y'` is the pullback of a global section of `ℱ`. -/
theorem exists_pullbackSections_eq (hφ : Function.Surjective φ)
    (hd : Function.Surjective (cechD f U F))
    (s₀ : Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ ⊤)) :
    ∃ s : Γ(F, ⊤), Stacks.Cech.pullbackSections g F ⊤ s = s₀ := by
  let : Algebra A A' := φ.toAlgebra
  let F' := (Scheme.Modules.pullback g).obj F
  let U' : Cover.{u} → Y'.Opens := fun i => g ⁻¹ᵁ U i
  have hU'le : ∀ i, U' i ≤ g ⁻¹ᵁ ⊤ := fun i => Scheme.Hom.preimage_mono g le_top
  let c₀ : (Stacks.Cech.alternatingCechModuleComplex f' U' F').X 0 :=
    ⟨restrCochain U' F'.presheaf hU'le s₀, isAlternating_restrCochain U' F'.presheaf hU'le s₀⟩
  have hc₀ : cechD f' U' F' c₀ = 0 := Subtype.ext <|
    (cechD_apply_coe f' U' F' c₀).trans (cechD_restrCochain U' F'.presheaf hU'le s₀)
  let e₀ := baseChangeEquiv φ f f' g hsq U F hUaff 0
  let e₁ := baseChangeEquiv φ f f' g hsq U F hUaff 1
  have hy : (cechD f U F).baseChange A' (e₀.symm c₀) = 0 := by
    apply e₁.injective
    have h := LinearMap.congr_fun (baseChangeEquiv_comm φ f f' g hsq U F hUaff) (e₀.symm c₀)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
    rw [h, map_zero]
    show cechD f' U' F' (e₀ (e₀.symm c₀)) = 0
    rwa [LinearEquiv.apply_symm_apply]
  have hφ' : Function.Surjective (algebraMap A A') := hφ
  obtain ⟨x, hx, hxy⟩ := exists_ker_tmul_eq hφ' (cechD f U F) hd _ hy
  obtain ⟨s, hs⟩ := exists_restrCochain_eq U ⟨F.presheaf, F.isSheaf⟩ (fun _ => le_top) hU.le x.1
    (by rw [← cechD_apply_coe]; exact congrArg Subtype.val hx)
  refine ⟨s, ?_⟩
  -- the comparison of `e₀ (1 ⊗ x)` with the pulled back cochain
  have hbc : e₀ ((1 : A') ⊗ₜ[A] x) = c₀ := by rw [hxy, LinearEquiv.apply_symm_apply]
  have hbc' : (e₀ ((1 : A') ⊗ₜ[A] x)).1 = Stacks.Cech.cochainBaseChange g U U' (Equiv.refl _) F
      (fun _ => rfl) 0 x.1 := by
    let := Stacks.Cech.cochainModule f U F 0
    let := Stacks.Cech.cochainModule f' U' F' 0
    let := Stacks.Cech.baseAlternatingModule g U' F φ f' 0
    let := Stacks.Cech.isScalarTowerBaseAlternating g U' F φ f' 0
    have hb := Stacks.Cech.isBaseChange_alternatingCochainBaseChangeₗ g U U' (Equiv.refl _) F
      (fun _ => rfl) φ f f' (Stacks.Cech.baseRingHom_comp_app φ f f' g hsq) hsq hUaff 0
    have he : e₀ ((1 : A') ⊗ₜ[A] x) = hb.equiv ((1 : A') ⊗ₜ[A] x) := rfl
    have he' := hb.equiv_tmul (1 : A') x
    rw [one_smul] at he'
    rw [he, he']
    rfl
  have hcoch : restrCochain U' F'.presheaf hU'le (Stacks.Cech.pullbackSections g F ⊤ s) =
      restrCochain U' F'.presheaf hU'le s₀ := by
    have h1 : Stacks.Cech.cochainBaseChange g U U' (Equiv.refl _) F (fun _ => rfl) 0 x.1 =
        restrCochain U' F'.presheaf hU'le s₀ :=
      hbc'.symm.trans (congrArg Subtype.val hbc)
    rw [← h1, ← hs]
    funext a
    exact (Stacks.Cech.pullbackSections_restr g F _ _ _ _).symm
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨F'.presheaf, F'.isSheaf⟩ (fun a : Fin 1 → Cover.{u} =>
    CechCochains.inter U' a) (g ⁻¹ᵁ ⊤) (fun a => homOfLE ((iInf_le _ 0).trans (hU'le (a 0))))
    ?_ _ _ fun a => congrFun hcoch a
  refine (Scheme.Hom.preimage_mono g hU.le).trans ?_
  rw [Scheme.Hom.preimage_iSup]
  exact iSup_le_iSup_inter U'

end Lift

/-! ### The case of an invertible module with vanishing `H¹` on the fibres -/

section Fibres

open Stacks.TwoAffineCech Stacks.FibreCohomology

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
  (U : Cover.{u} → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- An invertible module on a scheme flat over a base is flat over the base. -/
theorem isFlatOver_of_isInvertibleModule' [Flat f] : IsFlatOver f.toLRSHom.toShHom L := by
  have hL' : SheafOfModules.IsInvertible _ _ L := isInvertible_of_isInvertibleModule L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L hL')
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ L

include hU hUaff in
/-- **If `H¹` vanishes on every fibre, the two-term Čech differential is onto**, for an
invertible module on a proper flat scheme over a Noetherian ring covered by two affines. -/
theorem surjective_cechD_of_fibres' [IsNoetherianRing A] [IsProper f] [Flat f]
    (h : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology f L x 1) = 0) :
    Function.Surjective (cechD f U L) := by
  have : L.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hL' := isInvertible_of_isInvertibleModule L
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible Y L
  have hflat := isFlatOver_of_isInvertibleModule' f L
  have hmodel := hasFiniteProjectiveModel f U L hU hUaff hflat
  have := flat_X f U L hUaff hflat 1
  refine hmodel.surjective_of_forall fun p => ?_
  have hfin := hmodel.finiteDimensional_coker_fibre p
  have hdim := finrank_cohomologyOverField_one_eq f U L hU hUaff p
  rw [finrank_fibre_eq_fibreCohomology, h] at hdim
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact Module.finrank_zero_iff.1 hdim.symm

end Fibres

end Stacks.AbelMap

end
