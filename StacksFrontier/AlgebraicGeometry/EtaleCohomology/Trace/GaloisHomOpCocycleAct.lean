module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisSectionAct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpPairing

/-!
# A degree-zero cocycle of `Γ^Gal(ℋom^•(L, K))` as a morphism of complexes

Let `Y` be a quasi-compact quasi-separated `k`-scheme, `K/k` separable algebraic, `L` a complex of
sheaves of `Λ`-modules and `K` a complex of sheaves of abelian groups on `Y_étale`. A degree-zero
cocycle `β` of `Γ^Gal(ℋom^•_ℤ(L, K)) = Γ(Y_K, ℋom^•_ℤ(L, K)|_{Y_K})` acts on `L|_{Y_K}` through the
evaluation pairings `Lⁿ × ℋom⁰(L, K) ⟶ Kⁿ` (`Stacks.EtaleCohomology.galoisSectionAct`); these
morphisms commute with the differentials, since `β` is a cocycle and evaluation satisfies the
Leibniz rule. This gives a morphism of complexes `L|_{Y_K} ⟶ K|_{Y_K}`
(`Stacks.EtaleCohomology.galoisHomOpCocycleAct`), whose effect on global sections is the Galois
evaluation pairing with `β` (`Stacks.EtaleCohomology.galoisHomOpCocycleAct_ΓRes`).

In the base case of the derived Poincaré duality of Tag 03VM, `L` is an injective resolution of
`j_! ℱ_M` and `K` one of `j_! μ_n` on the compactification: the pairing of a degree-two class with
`β` is then `H²` of a morphism of resolutions, hence of the map `j_! ℱ_M ⟶ j_! μ_n` it lifts.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius Stacks.AbelianInternalHom

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

section Leibniz

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) {Λ : Type} [Ring Λ]
  (L : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ)
  (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)

/-- **Evaluation against a degree-zero cocycle commutes with the differentials**:
`ev(d a, e) = d ev(a, e)` when `δ e = 0`. -/
lemma etaleHomOpSectionPairing_d_of_δ_eq_zero (n q q' : ℤ) (hq : 0 + n = q) (hq' : q + 1 = q')
    (U : Y.left.Etaleᵒᵖ) (a : (L.X n).obj.obj U) (e : ((etaleHomOpComplex Y L Kc).X 0).obj.obj U)
    (he : (((etaleHomOpComplex Y L Kc).d 0 1).hom.app U).hom e = 0) :
    (etaleHomOpSectionPairing Y L Kc (n + 1) 0 q' (by omega)).app U
        (((L.d n (n + 1)).hom.app U).hom a) e =
      ((Kc.d q q').hom.app U).hom ((etaleHomOpSectionPairing Y L Kc n 0 q hq).app U a e) := by
  obtain rfl : q = q' - 1 := by omega
  have hd := homOpEval_d Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc) n 0 q' (by omega) U a e
  have hδ : (etaleHomOpComplex Y L Kc).d 0 1 = homOpComplexD _ L (etaleHomOpTarget Y Kc) 0 :=
    homOpComplex_d _ _ _ 0
  have he' : ((homOpComplexD _ L (etaleHomOpTarget Y Kc) 0).hom.app U).hom e = 0 :=
    (congrArg (fun φ => (φ.hom.app U).hom e) hδ).symm.trans he
  have h0 := hd.symm.trans ((congrArg (homOpEval Y.left.smallEtaleTopology L
    (etaleHomOpTarget Y Kc) n (0 + 1) q' (by omega) U a) he').trans (map_zero _))
  have hs : ((0 : ℤ) + 1).negOnePow = -1 := by rw [zero_add, Int.negOnePow_one]
  rw [hs, Units.neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0.symm

end Leibniz

section Act

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom] {Λ : Type} [Ring Λ]
  (L : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ)
  (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)

/-- The complex `L|_{Y_K}`, as a complex of sheaves of abelian groups. -/
abbrev galoisBaseChangeComplex {Λ : Type} [Ring Λ]
    (L : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ) :
    CochainComplex (EtaleModules.{u, 0} ℤ (fieldBaseChange Y K)) ℤ :=
  ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K) ⋙
    etaleModuleRestrictScalars (Int.castRingHom Λ) (fieldBaseChange Y K)).mapHomologicalComplex
      _).obj L

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- The map `fieldStageSection` sends the zero section over a stage to zero. -/
lemma fieldStageSection_zero {Λ' : Type} [Ring Λ'] (G : EtaleModules.{u, 0} Λ' Y.left)
    (i : FExt k K) : fieldStageSection Λ' Y K G i 0 = 0 :=
  left_eq_add.mp ((congrArg (fieldStageSection Λ' Y K G i) (add_zero 0)).symm.trans
    (fieldStageSection_add Λ' Y K G i 0 0))

/-- **A degree-zero cocycle has a stage representative which is a cocycle over its stage.** -/
theorem exists_fieldStageSection_eq_of_d_eq_zero
    (β : ((galoisHomOpE Y K L Kc).X 0).obj.obj.V)
    (hβ : ((galoisHomOpE Y K L Kc).d 0 1).hom.hom.hom.hom β = 0) :
    ∃ (l : FExt k K) (c : ((etaleHomOpComplex Y L Kc).X 0).obj.obj
        (op ((fieldStageSystem Y K).obj (op l)))),
      ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y K)).obj
          ((etaleHomOpComplex Y L Kc).X 0)).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) β =
        fieldStageSection Λᵐᵒᵖ Y K _ l c ∧
      (((etaleHomOpComplex Y L Kc).d 0 1).hom.app _).hom c = 0 := by
  let G₀ := (etaleHomOpComplex Y L Kc).X 0
  let G₁ := (etaleHomOpComplex Y L Kc).X 1
  let δ := (etaleHomOpComplex Y L Kc).d 0 1
  obtain ⟨i, c, hc⟩ := exists_fieldStageSection_eq Λᵐᵒᵖ Y K G₀ β
  have hβ' : (etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y K)).map
      ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y K)).map δ) β = 0 := hβ
  have h0 : fieldStageSection Λᵐᵒᵖ Y K G₁ i ((δ.hom.app _).hom c) =
      fieldStageSection Λᵐᵒᵖ Y K G₁ i 0 :=
    (ΓRes_map_eq_fieldStageSection Λᵐᵒᵖ Y K G₀ δ hc).symm.trans ((congrArg
      (((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))) hβ').trans
      ((map_zero _).trans (fieldStageSection_zero Y K G₁ i).symm))
  obtain ⟨l, hil, hl⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq Λᵐᵒᵖ Y K G₁ _ _ h0
  refine ⟨l, fieldStageRes Λᵐᵒᵖ Y K G₀ hil c, ΓRes_eq_fieldStageSection_of_le Λᵐᵒᵖ Y K G₀ hil hc,
    ?_⟩
  have hn := ConcreteCategory.congr_hom (δ.hom.naturality
    ((fieldStageSystem Y K).map (homOfLE hil).op).op) c
  exact hn.trans (hl.trans (map_zero _))

/-- **The morphism of complexes `L|_{Y_K} ⟶ K|_{Y_K}` of a degree-zero cocycle `β` of
`Γ^Gal(ℋom^•_ℤ(L, K))`**: in degree `n`, `β` acting through evaluation
`Lⁿ × ℋom⁰(L, K) ⟶ Kⁿ` (`Stacks.EtaleCohomology.galoisSectionAct`). -/
def galoisHomOpCocycleAct (β : ((galoisHomOpE Y K L Kc).X 0).obj.obj.V)
    (hβ : ((galoisHomOpE Y K L Kc).d 0 1).hom.hom.hom.hom β = 0) :
    galoisBaseChangeComplex Y K L ⟶ galoisBaseChangeComplex Y K Kc where
  f n := galoisSectionAct Y K (etaleHomOpSectionPairing Y L Kc n 0 n (zero_add n)) β
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    obtain ⟨l, c, hc, hδ⟩ := exists_fieldStageSection_eq_of_d_eq_zero Y K L Kc β hβ
    change galoisSectionAct Y K (etaleHomOpSectionPairing Y L Kc n 0 n (zero_add n)) β ≫
        (etaleModuleRestrictScalars (Int.castRingHom ℤ) _).map
          ((etaleModuleInverseImage.{u, 0} ℤ (fieldBaseChangeProj Y K)).map (Kc.d n (n + 1))) =
      (etaleModuleRestrictScalars (Int.castRingHom Λ) _).map
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).map (L.d n (n + 1))) ≫
        galoisSectionAct Y K (etaleHomOpSectionPairing Y L Kc (n + 1) 0 (n + 1)
          (zero_add (n + 1))) β
    refine Eq.symm ?_
    have e₁ := galoisSectionAct_eq Y K
      (etaleHomOpSectionPairing Y L Kc (n + 1) 0 (n + 1) (zero_add (n + 1))) hc
    have e₂ := galoisSectionAct_eq Y K (etaleHomOpSectionPairing Y L Kc n 0 n (zero_add n)) hc
    refine (congrArg (_ ≫ ·) e₁).trans (Eq.trans ?_ (congrArg (· ≫ _) e₂.symm))
    refine sectionPairingAct_comm _ _ _ c _ (L.d n (n + 1)) (Kc.d n (n + 1)) fun V f a => ?_
    refine etaleHomOpSectionPairing_d_of_δ_eq_zero Y L Kc n n (n + 1) (zero_add n) rfl (op V) a _ ?_
    have hn := ConcreteCategory.congr_hom
      (((etaleHomOpComplex Y L Kc).d 0 1).hom.naturality f.op) c
    exact hn.trans ((congrArg (ConcreteCategory.hom (((etaleHomOpComplex Y L Kc).X 1).obj.map f.op))
      hδ).trans (map_zero _))

/-- **On global sections, the morphism of complexes of `β` is the Galois evaluation pairing with
`β`**: `Γ(Y_K, β̃ⁿ)(a) = ⟨a, β⟩`, read on the final object of the site. -/
theorem galoisHomOpCocycleAct_ΓRes (β : ((galoisHomOpE Y K L Kc).X 0).obj.obj.V)
    (hβ : ((galoisHomOpE Y K L Kc).d 0 1).hom.hom.hom.hom β = 0) (n : ℤ)
    (a : ((galoisHomOpA Y K L).X n).obj.obj.V) :
    ((galoisHomOpCocycleAct Y K L Kc β hβ).f n).hom.app
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y K)).obj (L.X n)).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) a) =
      ((etaleModuleInverseImage.{u, 0} ℤ (fieldBaseChangeProj Y K)).obj (Kc.X n)).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (galoisHomOpPair Y K L Kc n 0 n (zero_add n) a β) := by
  refine (galoisSectionAct_ΓRes Y K _ β a).trans ?_
  change _ = ((etaleModuleInverseImage.{u, 0} ℤ (fieldBaseChangeProj Y K)).obj (Kc.X n)).ΓRes _
    (homOpPairingSign n 0 • galoisGlobalSectionsPairing Y K
      (etaleHomOpSectionPairing Y L Kc n 0 n (zero_add n)) a β)
  rw [show homOpPairingSign n 0 = 1 by simp [homOpPairingSign], one_smul]

end Act

end Stacks.EtaleCohomology

end
