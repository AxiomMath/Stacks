module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.AffineModel
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections

/-!
# Global sections as Čech cochains

Let `f : X ⟶ Spec A` be a scheme over an affine base with an indexed family of opens
`U : Cover → X.Opens`. A global section `s` of an `𝒪_X`-module `F` gives the Čech `0`-cochain
`i ↦ s|_{U i}`, an alternating cocycle. This file records that map, its `A`-linearity, its
injectivity when the `U i` cover `X`, and its compatibility with the base change of Čech cochains
along a cartesian square: the cochain of the pulled-back section is the base change of the
cochain of the section.

## Main definitions

* `Stacks.TwoAffineCech.sectionCochain`: the Čech `0`-cochain of a global section.
* `Stacks.TwoAffineCech.sectionCocycle`: the same, as an element of the kernel of the Čech
  differential.

## Main results

* `Stacks.TwoAffineCech.sectionCochain_injective`: the map is injective for a cover.
* `Stacks.TwoAffineCech.cochainBaseChange_sectionCochain`: compatibility with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens) (F : X.Modules)

/-- **The Čech `0`-cochain of a global section**: `i ↦ s|_{U i}`. -/
def sectionCochain (s : Γ(F, ⊤)) : CechCochains.Cochain U F.presheaf 0 :=
  fun _ => F.presheaf.map (homOfLE le_top).op s

/-- The Čech `0`-cochain of a global section is alternating. -/
theorem sectionCochain_isAlternating (s : Γ(F, ⊤)) :
    CechCochains.IsAlternating U F.presheaf (sectionCochain U F s) := by
  exact ⟨fun i hi => (hi fun a b _ => Subsingleton.elim (α := Fin 1) a b).elim,
    fun i a b hab => (hab (Subsingleton.elim (α := Fin 1) a b)).elim⟩

/-- The Čech `0`-cochain of a global section, as an alternating cochain. -/
def sectionAlt (s : Γ(F, ⊤)) : (Stacks.Cech.alternatingCechModuleComplex f U F).X 0 :=
  ⟨sectionCochain U F s, sectionCochain_isAlternating U F s⟩

/-- The Čech differential vanishes on the alternating `0`-cochain of a global section. -/
theorem cechD_sectionAlt (s : Γ(F, ⊤)) : cechD f U F (sectionAlt f U F s) = 0 := by
  apply Subtype.ext
  funext i
  change ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr F.presheaf (CechCochains.inter_le_omit U i j)
        (F.presheaf.map (homOfLE le_top).op s) = 0
  rw [Fin.sum_univ_two]
  simp only [CechCochains.restr, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  exact add_neg_cancel _

/-- The underlying Čech cochain of an alternating `0`-cochain. -/
def altCochain (x : (Stacks.Cech.alternatingCechModuleComplex f U F).X 0) :
    CechCochains.Cochain U F.presheaf 0 :=
  x.1

/-- An alternating `0`-cochain is determined by its underlying Čech cochain. -/
theorem altCochain_injective : Function.Injective (altCochain f U F) :=
  fun _ _ h => Subtype.ext h

/-- The underlying Čech cochain of the zero alternating `0`-cochain is zero. -/
theorem altCochain_zero : altCochain f U F 0 = 0 := rfl

/-- The Čech `0`-cochain of a global section, as an element of the kernel of the Čech
differential. -/
def sectionCocycle (s : Γ(F, ⊤)) : LinearMap.ker (cechD f U F) :=
  ⟨sectionAlt f U F s, cechD_sectionAlt f U F s⟩

/-- The Čech `0`-cochain of the zero section is zero. -/
theorem sectionCochain_zero : sectionCochain U F 0 = 0 :=
  funext fun _ => map_zero _

/-- The Čech `0`-cochain of a sum of global sections is the sum of their cochains. -/
theorem sectionCochain_add (s t : Γ(F, ⊤)) :
    sectionCochain U F (s + t) = sectionCochain U F s + sectionCochain U F t :=
  funext fun _ => map_add _ _ _

/-- The intersection of a constant one-element family is its member. -/
private theorem inter_const_eq (i : Cover.{u}) :
    CechCochains.inter U (fun _ : Fin (0 + 1) => i) = U i := by
  simp [CechCochains.inter]

/-- **A global section with vanishing Čech cochain vanishes**, when the `U i` cover `X`. -/
theorem eq_zero_of_sectionCochain_eq_zero (hU : (⊤ : X.Opens) = ⨆ i, U i) (s : Γ(F, ⊤))
    (h : sectionCochain U F s = 0) : s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X)
    (fun i => CechCochains.inter U (fun _ : Fin (0 + 1) => i)) ⊤ (fun i => homOfLE le_top)
    (hU.le.trans (iSup_mono fun i => (inter_const_eq U i).ge)) _ _ fun i => ?_
  rw [map_zero]
  exact congrFun h (fun _ => i)

/-- **A global section is determined by its Čech `0`-cochain**, when the `U i` cover `X`. -/
theorem sectionCochain_injective (hU : (⊤ : X.Opens) = ⨆ i, U i) :
    Function.Injective (sectionCochain U F) := by
  intro s t h
  rw [← sub_eq_zero]
  refine eq_zero_of_sectionCochain_eq_zero U F hU _ ?_
  funext i
  change F.presheaf.map _ (s - t) = 0
  rw [map_sub]
  exact sub_eq_zero.2 (congrFun h i)

/-- **The Čech cochain of a section is `A`-linear in the section**, `A` acting on global
sections through `f`. -/
theorem sectionCochain_smul (a : A) (s : Γ(F, ⊤)) :
    letI := Stacks.Cech.cochainModule f U F 0
    sectionCochain U F ((Stacks.Cech.baseRingHom f ⊤).hom a • s) =
      a • sectionCochain U F s := by
  let := Stacks.Cech.cochainModule f U F 0
  funext i
  rw [Stacks.Cech.cochain_smul_apply]
  change F.presheaf.map _ (_ • s) = _
  rw [Scheme.Modules.map_smul, Stacks.Cech.map_baseRingHom_apply]
  rfl

/-- **Every Čech cocycle comes from a global section**, when the `U i` cover `X`: the sections on
the members agree on the overlaps, so they glue. -/
theorem exists_sectionCocycle_eq (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (c : LinearMap.ker (cechD f U F)) : ∃ s : Γ(F, ⊤), sectionCocycle f U F s = c := by
  obtain ⟨⟨c, hc⟩, hd⟩ := c
  let V : Cover.{u} → X.Opens := fun i => CechCochains.inter U (fun _ : Fin (0 + 1) => i)
  have hV : ∀ i, V i = U i := inter_const_eq U
  have key : ∀ (i₁ i₂ : Fin (0 + 1) → Cover.{u}), i₁ = i₂ → ∀ {W : X.Opens}
      (h₁ : W ≤ CechCochains.inter U i₁) (h₂ : W ≤ CechCochains.inter U i₂),
      CechCochains.restr F.presheaf h₁ (c i₁) = CechCochains.restr F.presheaf h₂ (c i₂) := by
    rintro _ _ rfl W h₁ h₂
    rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.presheaf V (fun i => c (fun _ => i)) := by
    intro i j
    let t : Fin 2 → Cover.{u} := ![i, j]
    have h := congrFun (congrArg Subtype.val hd) t
    change ∑ j' : Fin 2, ((-1 : ℤ) ^ (j' : ℕ)) • CechCochains.restr F.presheaf
      (CechCochains.inter_le_omit U t j') (c (t ∘ j'.succAbove)) = 0 at h
    rw [Fin.sum_univ_two] at h
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h
    have hle : V i ⊓ V j ≤ CechCochains.inter U t := by
      refine le_iInf fun k => ?_
      rw [hV, hV]
      refine Fin.cases ?_ (fun k' => ?_) k
      · exact inf_le_left
      · rw [Subsingleton.elim (α := Fin 1) k' 0]
        exact inf_le_right
    have hj : CechCochains.inter U t ≤ V j := (iInf_le (fun k => U (t k)) 1).trans (hV j).ge
    have hi : CechCochains.inter U t ≤ V i := (iInf_le (fun k => U (t k)) 0).trans (hV i).ge
    have e0 := key (t ∘ (0 : Fin 2).succAbove) (fun _ => j) (funext fun x => by
        rw [Subsingleton.elim (α := Fin 1) x 0]
        rfl) (CechCochains.inter_le_omit U t 0) hj
    have e1 := key (t ∘ (1 : Fin 2).succAbove) (fun _ => i) (funext fun x => by
        rw [Subsingleton.elim (α := Fin 1) x 0]
        rfl) (CechCochains.inter_le_omit U t 1) hi
    rw [e0, e1, add_neg_eq_zero] at h
    have h' := congrArg (CechCochains.restr F.presheaf hle) h
    rw [CechCochains.restr_restr, CechCochains.restr_restr] at h'
    exact h'.symm
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) V ⊤
    (fun _ => homOfLE le_top) (hU.le.trans (iSup_mono fun i => (hV i).ge))
    (fun i => c (fun _ => i)) hcomp
  refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
  funext i
  have hgen : ∀ (i' : Fin (0 + 1) → Cover.{u}) (j : Cover.{u}), i' = (fun _ => j) →
      F.presheaf.map (homOfLE le_top).op s = c i' := by
    rintro _ j rfl
    exact hs j
  exact hgen i (i 0) (funext fun x => by rw [Subsingleton.elim (α := Fin 1) x 0])

section BaseChange

/-- Two composites of restriction maps between the same opens agree. -/
theorem presheaf_map_map_eq {Y : Scheme.{u}} (P : Y.Opensᵒᵖ ⥤ Ab.{u}) {V₁ V₂ V₂' V₃ : Y.Opensᵒᵖ}
    (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) (c : V₁ ⟶ V₂') (d : V₂' ⟶ V₃) (x : P.obj V₁) :
    P.map b (P.map a x) = P.map d (P.map c x) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, Subsingleton.elim (a ≫ b) (c ≫ d)]

variable {X' : Scheme.{u}} (g : X' ⟶ X)

/-- **The Čech cochain of a pulled-back section is the base change of the Čech cochain of the
section.** -/
theorem cochainBaseChange_sectionCochain (s : Γ(F, ⊤)) :
    Stacks.Cech.cochainBaseChange g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) F (fun _ => rfl) 0
        (sectionCochain U F s) =
      sectionCochain (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
        (pullbackGlobalSections g F s) := by
  funext i
  have key := congr($(Stacks.Cech.map_comp_pullbackSections g F
    (le_top : CechCochains.inter U ((Equiv.refl Cover.{u}) ∘ i) ≤ ⊤)) s)
  simp only [ConcreteCategory.comp_apply] at key
  change CechCochains.restr _ _ (Stacks.Cech.pullbackSections g F _
    (F.presheaf.map (homOfLE le_top).op s)) = _
  rw [key]
  simp only [CechCochains.restr, sectionCochain, pullbackGlobalSections]
  exact presheaf_map_map_eq _ _ _ _ _ _

end BaseChange

section Fibre

variable {A K : Type u} [CommRing A] [Field K] (φ : A →+* K) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of K)) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hUaff : ∀ i, IsAffineOpen (U i))

include hsq hUaff in
/-- **The base change of the Čech cochain of a section is the Čech cochain of the pulled-back
section**, read through the degree-zero base-change isomorphism of the two-term Čech complex. -/
theorem baseChangeEquiv_zero_one_tmul_sectionAlt (s : Γ(F, ⊤)) :
    letI : Algebra A K := φ.toAlgebra
    altCochain f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
        (baseChangeEquiv φ f f' g hsq U F hUaff 0 ((1 : K) ⊗ₜ[A] sectionAlt f U F s)) =
      sectionCochain (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
        (pullbackGlobalSections g F s) := by
  let : Algebra A K := φ.toAlgebra
  have h := Stacks.Cech.alternatingCechModuleObjBaseChangeIso_hom_one_tmul g U
    (fun i => g ⁻¹ᵁ U i) (Equiv.refl _) F (fun _ => rfl) φ f f'
    (Stacks.Cech.baseRingHom_comp_app φ f f' g hsq) hsq hUaff 0 (sectionAlt f U F s)
  exact (congrArg Subtype.val h).trans (cochainBaseChange_sectionCochain U F g s)

include hsq hUaff in
/-- **A section whose cocycle survives in the fibre at a field point pulls back to a nonzero
section of the fibre**, when the Čech differential is onto and its target is flat. -/
theorem pullbackGlobalSections_ne_zero_of_tmul_ne_zero
    [Module.Flat A ((Stacks.Cech.alternatingCechModuleComplex f U F).X 1)]
    (hd : Function.Surjective (cechD f U F)) (s : Γ(F, ⊤))
    (hne : letI : Algebra A K := φ.toAlgebra
      (1 : K) ⊗ₜ[A] sectionCocycle f U F s ≠ 0) :
    pullbackGlobalSections g F s ≠ 0 := by
  let : Algebra A K := φ.toAlgebra
  intro h0
  apply hne
  have hc := baseChangeEquiv_zero_one_tmul_sectionAlt φ f f' g hsq U F hUaff s
  rw [h0, sectionCochain_zero] at hc
  have h1 : (1 : K) ⊗ₜ[A] sectionAlt f U F s = 0 := by
    apply (baseChangeEquiv φ f f' g hsq U F hUaff 0).injective
    rw [map_zero]
    exact altCochain_injective _ _ _ hc
  refine (Stacks.TwoTermComplex.baseChangeKerEquiv _ hd K).injective (Subtype.ext ?_)
  rw [map_zero, Stacks.TwoTermComplex.baseChangeKerEquiv_tmul]
  exact h1

include hsq hUaff in
/-- **A section pulling back to a nonzero section of the fibre at a field point has a cocycle
surviving in that fibre.** -/
theorem tmul_ne_zero_of_pullbackGlobalSections_ne_zero (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (s : Γ(F, ⊤)) (hne : pullbackGlobalSections g F s ≠ 0) :
    letI : Algebra A K := φ.toAlgebra
    (1 : K) ⊗ₜ[A] sectionCocycle f U F s ≠ 0 := by
  let : Algebra A K := φ.toAlgebra
  intro h
  apply hne
  refine eq_zero_of_sectionCochain_eq_zero (fun i => g ⁻¹ᵁ U i) _
    (top_eq_iSup_preimage g U hU) _ ?_
  rw [← baseChangeEquiv_zero_one_tmul_sectionAlt φ f f' g hsq U F hUaff s]
  have h0 : (1 : K) ⊗ₜ[A] sectionAlt f U F s = 0 := by
    have := congrArg ((LinearMap.ker (cechD f U F)).subtype.baseChange K) h
    rwa [LinearMap.baseChange_tmul, map_zero] at this
  rw [h0, map_zero, altCochain_zero]

end Fibre

end Stacks.TwoAffineCech
