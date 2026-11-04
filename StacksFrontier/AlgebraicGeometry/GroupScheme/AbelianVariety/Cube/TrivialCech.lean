module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Generators

/-!
# Čech cochains of a trivial module

For a module `G` on a scheme with a generator `σ`, division by `σ` identifies Čech cochains of
`G` with Čech cochains of functions, compatibly with the differentials (`Stacks.Cube.rawD_dg`,
`Stacks.Cube.cechD_mulσ`). A degree-zero Čech cocycle of any module for an open cover glues to a
global section (`Stacks.Cube.exists_section_of_cechD_eq_zero`).

## References

* [Stacks Project, Tag 01ED](https://stacks.math.columbia.edu/tag/01ED)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {X : Scheme.{u}} {I : Type u} (W : I → X.Opens)

/-- The Čech differential of a cochain of `G` is the alternating sum of the restrictions of its
values on the faces. -/
theorem cechD_apply' (G : X.Modules) (p : ℕ)
    (x : ∀ i : Fin (p + 1) → I, Γ(G, CechCochains.inter W i))
    (i : Fin (p + 2) → I) :
    CechCochains.cechD W G.presheaf p x i = ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
      G.presheaf.map (homOfLE (CechCochains.inter_le_omit W i l)).op (x (i ∘ l.succAbove)) := rfl

/-- Every degree-zero cochain is alternating. -/
theorem isAlternating_zero (F : TopCat.Presheaf Ab X) (x : CechCochains.Cochain W F 0) :
    CechCochains.IsAlternating W F x := by
  have hs : ∀ a b : Fin (0 + 1), a = b := fun a b =>
    Fin.ext (by have := a.isLt; have := b.isLt; omega)
  refine ⟨fun i hi => absurd (fun a b _ => hs a b) hi, fun i a b hab => absurd (hs a b) hab⟩

variable {G : X.Modules} {σ : Γ(G, ⊤)} (hσ : IsGen G σ)

/-- Division of a cochain by a generator. -/
noncomputable def dg (p : ℕ) (x : ∀ i : Fin (p + 1) → I, Γ(G, CechCochains.inter W i)) :
    RawCochain W p := fun i => divGen hσ _ (x i)

/-- Multiplication of a cochain of functions by a generator. -/
noncomputable def mulσ (p : ℕ) (F : RawCochain W p) :
    ∀ i : Fin (p + 1) → I, Γ(G, CechCochains.inter W i) := fun i =>
  F i • resTop G σ _

/-- Dividing by `σ` a cochain multiplied by `σ` recovers the original cochain of functions. -/
theorem dg_mulσ (p : ℕ) (F : RawCochain W p) : dg W hσ p (mulσ W (σ := σ) p F) = F := by
  funext i
  exact (divGen_eq_iff hσ _ _ _).mpr rfl

/-- Multiplying by `σ` a cochain divided by `σ` recovers the original cochain of `G`. -/
theorem mulσ_dg (p : ℕ) (x : ∀ i : Fin (p + 1) → I, Γ(G, CechCochains.inter W i)) :
    mulσ W (σ := σ) p (dg W hσ p x) = x := by
  funext i
  exact divGen_smul_resTop hσ _ _

/-- Division by the generator `σ` commutes with the Čech differentials. -/
theorem rawD_dg (p : ℕ) (x : ∀ i : Fin (p + 1) → I, Γ(G, CechCochains.inter W i)) :
    rawD W p (dg W hσ p x) = dg W hσ (p + 1) (CechCochains.cechD W G.presheaf p x) := by
  funext i
  change _ = divGenHom hσ _ (CechCochains.cechD W G.presheaf p x i)
  rw [cechD_apply', map_sum, rawD]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, divGenHom_apply, divGen_map]
  rfl

/-- The restriction of `σ` to `O'`, further restricted to `O ⊆ O'`, is the restriction of `σ`
to `O`. -/
theorem resTop_res {O O' : X.Opens} (h : O ≤ O') :
    G.presheaf.map (homOfLE h).op (resTop G σ O') = resTop G σ O := by
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Multiplication by the generator `σ` commutes with the Čech differentials. -/
theorem cechD_mulσ (p : ℕ) (F : RawCochain W p) :
    CechCochains.cechD W G.presheaf p (mulσ W (σ := σ) p F) =
      mulσ W (σ := σ) (p + 1) (rawD W p F) := by
  funext i
  rw [cechD_apply']
  change _ = (∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
    res (CechCochains.inter_le_omit W i l) (F (i ∘ l.succAbove))) • resTop G σ _
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_assoc]
  congr 1
  change G.presheaf.map _ (F (i ∘ l.succAbove) • resTop G σ _) = _
  rw [Scheme.Modules.map_smul, resTop_res]
  rfl

/-- **A degree-zero Čech cocycle glues to a global section.** -/
theorem exists_section_of_cechD_eq_zero (G : X.Modules) (hcov : (⊤ : X.Opens) = ⨆ i, W i)
    (x : ∀ i : Fin 1 → I, Γ(G, CechCochains.inter W i))
    (hx : CechCochains.cechD W G.presheaf 0 x = 0) :
    ∃ s : Γ(G, ⊤), ∀ i, G.presheaf.map (homOfLE le_top).op s = x i := by
  have key : ∀ (a b : Fin 1 → I) (hab : a = b) (O : X.Opens) (h1 : O ≤ CechCochains.inter W a)
      (h2 : O ≤ CechCochains.inter W b),
      G.presheaf.map (homOfLE h1).op (x a) = G.presheaf.map (homOfLE h2).op (x b) := by
    intro a b hab O h1 h2; subst hab; rfl
  let ℱ : TopCat.Sheaf Ab X := ⟨G.presheaf, Scheme.Modules.isSheaf G⟩
  let t : ∀ i, ℱ.1.obj (op (W i)) := fun i =>
    G.presheaf.map (homOfLE (le_of_eq (by simp [CechCochains.inter]))).op (x (fun _ => i))
  have hcompat : ∀ i j, ℱ.1.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (t i) =
      ℱ.1.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (t j) := by
    intro i j
    have h0 := congrFun hx (![i, j])
    rw [cechD_apply', Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      CechCochains.Cochain.zero_apply] at h0
    have hij : W i ⊓ W j = CechCochains.inter W ![i, j] := by
      ext y
      simp [CechCochains.inter, TopologicalSpace.Opens.coe_iInf, Fin.forall_fin_two]
    have h0' := congrArg (G.presheaf.map (homOfLE (le_of_eq hij)).op) (add_neg_eq_zero.mp h0)
    simp only [t]
    change G.presheaf.map _ (G.presheaf.map _ (x _)) = G.presheaf.map _ (G.presheaf.map _ (x _))
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h0' ⊢
    have e1 : (![i, j] ∘ Fin.succAbove 0) = (fun _ : Fin 1 => j) := by
      funext m; fin_cases m; rfl
    have e2 : (![i, j] ∘ Fin.succAbove 1) = (fun _ : Fin 1 => i) := by
      funext m; fin_cases m; rfl
    refine (key _ _ e2.symm _ _ _).trans (h0'.symm.trans (key _ _ e1 _ _ _))
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ℱ W ⊤ (fun i => homOfLE le_top)
    (le_of_eq hcov) t (fun i j => hcompat i j)
  refine ⟨s, fun i => ?_⟩
  have hi : CechCochains.inter W i = W (i 0) := by simp [CechCochains.inter]
  have hsi := hs (i 0)
  have e3 : i = fun _ => i 0 := by funext m; fin_cases m; rfl
  have step1 : G.presheaf.map (homOfLE (le_top : CechCochains.inter W i ≤ ⊤)).op s =
      G.presheaf.map (homOfLE (le_of_eq hi)).op
        (G.presheaf.map (homOfLE (le_top : W (i 0) ≤ ⊤)).op s) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  rw [step1]
  change G.presheaf.map _ (ℱ.1.map _ s) = _
  rw [hsi]
  simp only [t, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  refine (key _ _ e3.symm _ _ (le_refl _)).trans ?_
  rw [show homOfLE (le_refl (CechCochains.inter W i)) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end Stacks.Cube

end
