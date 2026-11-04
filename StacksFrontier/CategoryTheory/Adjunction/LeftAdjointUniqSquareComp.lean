module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage

/-!
# Composition laws for comparisons of left adjoints across equivalences

Let `Φ_U : C_U ≌ M_U` be equivalences and let `L_f ⊣ R_f`, `e_f ⊣ e_f'` be adjunctions between
them, for `f` one of `p`, `q`, `p ≫ q`. A square `sq_f : e_f' ⋙ Φ ≅ Φ' ⋙ R_f` of right adjoints
induces, by uniqueness of left adjoints, a square `ψ_f : L_f ⋙ Φ'⁻¹ ≅ Φ⁻¹ ⋙ e_f` of left adjoints,
and a square `β_f : Φ ⋙ L_f ≅ e_f ⋙ Φ'` read through the equivalences.  This file proves that
if the squares of right adjoints compose, so do the squares of left adjoints: by conjugation
(`CategoryTheory.conjugateEquiv`) for `ψ`, and by the triangle identities for `β`.

## Main results

* `Stacks.CategoryTheory.SquareComposition.leftAdjointUniq_comp`: the composition law for `ψ`.
* `Stacks.CategoryTheory.SquareComposition.leftAdjointUniq_comp_of_app`: the same, with the
  composition law of the squares of right adjoints given at each object.
* `Stacks.CategoryTheory.SquareComposition.equivalenceSquare_comp`: the composition law for `β`.
* `Stacks.CategoryTheory.SquareComposition.conjugatedSquare_comparison_cube`: a cube of squares
  conjugated through comparisons of pullbacks on both sides.
* `Stacks.CategoryTheory.SquareComposition.pastedSquare_comp`: squares pasted from identifications
  `κ : ε ≅ A ⋙ F`, squares `β` and squares `α` compose as soon as the `β` and the `α` do.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.SquareComposition

variable {CX CY CZ MX MY MZ : Type*} [Category CX] [Category CY] [Category CZ]
  [Category MX] [Category MY] [Category MZ]

/-- The comparison of the left adjoints of a square whose right adjoints are compared by `sq`. -/
theorem conj_leftAdjointUniq_ofNatIsoRight {A C : Type*} [Category A]
    [Category C] {L₁ : A ⥤ C} {R₁ : C ⥤ A} {L₂ : A ⥤ C} {R₂ : C ⥤ A}
    (adjA : L₁ ⊣ R₁) (adjB : L₂ ⊣ R₂) (sq : R₂ ≅ R₁) :
    conjugateEquiv adjB adjA (Adjunction.leftAdjointUniq adjA (adjB.ofNatIsoRight sq)).hom =
      sq.hom := by
  have h := Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom adjA (adjB.ofNatIsoRight sq)
  rw [Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_left] at h
  rw [← Category.id_comp (conjugateEquiv adjB adjA _), ← sq.hom_inv_id, Category.assoc, h,
    Category.comp_id]

/-- **Composition law for the comparison of left adjoints across equivalences.** -/
theorem leftAdjointUniq_comp (ΦX : CX ≌ MX) (ΦY : CY ≌ MY) (ΦZ : CZ ≌ MZ)
    {Lp : MY ⥤ MX} {Rp : MX ⥤ MY} (adjp : Lp ⊣ Rp)
    {Lq : MZ ⥤ MY} {Rq : MY ⥤ MZ} (adjq : Lq ⊣ Rq)
    {Lpq : MZ ⥤ MX} {Rpq : MX ⥤ MZ} (adjpq : Lpq ⊣ Rpq)
    {ep : CY ⥤ CX} {ep' : CX ⥤ CY} (adjep : ep ⊣ ep')
    {eq : CZ ⥤ CY} {eq' : CY ⥤ CZ} (adjeq : eq ⊣ eq')
    {epq : CZ ⥤ CX} {epq' : CX ⥤ CZ} (adjepq : epq ⊣ epq')
    (sqp : ep' ⋙ ΦY.functor ≅ ΦX.functor ⋙ Rp) (sqq : eq' ⋙ ΦZ.functor ≅ ΦY.functor ⋙ Rq)
    (sqpq : epq' ⋙ ΦZ.functor ≅ ΦX.functor ⋙ Rpq)
    (cL : Lq ⋙ Lp ⟶ Lpq) (κR : Rpq ⟶ Rp ⋙ Rq)
    (hL : conjugateEquiv adjpq (adjq.comp adjp) cL = κR)
    (χ : eq ⋙ ep ⟶ epq) (cE : epq' ⟶ ep' ⋙ eq')
    (hE : conjugateEquiv adjepq (adjeq.comp adjep) χ = cE)
    (hsq : Functor.whiskerRight cE ΦZ.functor ≫ Functor.whiskerLeft ep' sqq.hom ≫
        Functor.whiskerRight sqp.hom Rq = sqpq.hom ≫ Functor.whiskerLeft ΦX.functor κR) :
    Functor.whiskerLeft Lq (Adjunction.leftAdjointUniq (adjp.comp ΦX.symm.toAdjunction)
          ((ΦY.symm.toAdjunction.comp adjep).ofNatIsoRight sqp)).hom ≫
        Functor.whiskerRight (Adjunction.leftAdjointUniq (adjq.comp ΦY.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjeq).ofNatIsoRight sqq)).hom ep ≫
        Functor.whiskerLeft ΦZ.inverse χ =
      Functor.whiskerRight cL ΦX.inverse ≫
        (Adjunction.leftAdjointUniq (adjpq.comp ΦX.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjepq).ofNatIsoRight sqpq)).hom := by
  have h1 : conjugateEquiv (ΦZ.symm.toAdjunction.comp adjepq)
      ((ΦZ.symm.toAdjunction.comp adjeq).comp adjep) (Functor.whiskerLeft ΦZ.inverse χ) =
        Functor.whiskerRight cE ΦZ.functor := by
    rw [← Adjunction.comp_assoc ΦZ.symm.toAdjunction adjeq adjep]
    exact (conjugateEquiv_whiskerLeft adjepq (adjeq.comp adjep) ΦZ.symm.toAdjunction χ).trans
      (by rw [hE]; rfl)
  have h2 : conjugateEquiv ((ΦZ.symm.toAdjunction.comp adjeq).comp adjep)
      (adjq.comp (ΦY.symm.toAdjunction.comp adjep))
      (Functor.whiskerRight (Adjunction.leftAdjointUniq (adjq.comp ΦY.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjeq).ofNatIsoRight sqq)).hom ep) =
        Functor.whiskerLeft ep' sqq.hom := by
    rw [Adjunction.comp_assoc adjq ΦY.symm.toAdjunction adjep]
    exact (conjugateEquiv_whiskerRight (ΦZ.symm.toAdjunction.comp adjeq)
      (adjq.comp ΦY.symm.toAdjunction) adjep _).trans
      (by rw [conj_leftAdjointUniq_ofNatIsoRight])
  have h3 : conjugateEquiv (adjq.comp (ΦY.symm.toAdjunction.comp adjep))
      (adjq.comp (adjp.comp ΦX.symm.toAdjunction))
      (Functor.whiskerLeft Lq (Adjunction.leftAdjointUniq (adjp.comp ΦX.symm.toAdjunction)
          ((ΦY.symm.toAdjunction.comp adjep).ofNatIsoRight sqp)).hom) =
        Functor.whiskerRight sqp.hom Rq :=
    (conjugateEquiv_whiskerLeft (ΦY.symm.toAdjunction.comp adjep)
      (adjp.comp ΦX.symm.toAdjunction) adjq _).trans
      (by rw [conj_leftAdjointUniq_ofNatIsoRight])
  have h4 : conjugateEquiv (ΦZ.symm.toAdjunction.comp adjepq) (adjpq.comp ΦX.symm.toAdjunction)
      (Adjunction.leftAdjointUniq (adjpq.comp ΦX.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjepq).ofNatIsoRight sqpq)).hom = sqpq.hom :=
    conj_leftAdjointUniq_ofNatIsoRight _ _ _
  have h5 : conjugateEquiv (adjpq.comp ΦX.symm.toAdjunction)
      (adjq.comp (adjp.comp ΦX.symm.toAdjunction)) (Functor.whiskerRight cL ΦX.inverse) =
        Functor.whiskerLeft ΦX.functor κR := by
    rw [Adjunction.comp_assoc adjq adjp ΦX.symm.toAdjunction]
    exact (conjugateEquiv_whiskerRight adjpq (adjq.comp adjp) ΦX.symm.toAdjunction cL).trans
      (by rw [hL]; rfl)
  apply (conjugateEquiv (ΦZ.symm.toAdjunction.comp adjepq)
    (adjq.comp (adjp.comp ΦX.symm.toAdjunction))).injective
  rwa [← conjugateEquiv_comp _ (adjq.comp (ΦY.symm.toAdjunction.comp adjep)) _,
    ← conjugateEquiv_comp _ ((ΦZ.symm.toAdjunction.comp adjeq).comp adjep) _,
    ← conjugateEquiv_comp _ (adjpq.comp ΦX.symm.toAdjunction) _, h1, h2, h3, h4, h5,
    Category.assoc]

/-- The square of left adjoints read through the equivalences, at one object. -/
theorem equivalenceSquare_hom_app {CT CT' MT MT' : Type*} [Category CT] [Category CT']
    [Category MT] [Category MT'] (ΦT : CT ≌ MT) (ΦT' : CT' ≌ MT') (L : MT ⥤ MT')
    (e : CT ⥤ CT') (ψ : L ⋙ ΦT'.inverse ≅ ΦT.inverse ⋙ e) (M : CT) :
    ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ ΦT'.counitIso.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ψ ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ΦT.unitIso.symm _ ≪≫
          Functor.leftUnitor _) _ :
        ΦT.functor ⋙ L ≅ e ⋙ ΦT'.functor).hom.app M =
      ΦT'.counitInv.app (L.obj (ΦT.functor.obj M)) ≫
        ΦT'.functor.map (ψ.hom.app (ΦT.functor.obj M) ≫ e.map (ΦT.unitInv.app M)) := by
  simp

/-- One step of the composition law: the inverse counit followed by the square of a mate is the
inverse counit followed by the mate. -/
theorem counitInv_comp_equivalenceSquare {CY CX MY MX : Type*} [Category CY] [Category CX]
    [Category MY] [Category MX] (ΦY : CY ≌ MY) (ΦX : CX ≌ MX) (Lp : MY ⥤ MX) (ep : CY ⥤ CX)
    (ψp : Lp ⋙ ΦX.inverse ≅ ΦY.inverse ⋙ ep) (N' : MY) :
    Lp.map (ΦY.counitInv.app N') ≫ ΦX.counitInv.app (Lp.obj (ΦY.functor.obj (ΦY.inverse.obj N'))) ≫
        ΦX.functor.map (ψp.hom.app (ΦY.functor.obj (ΦY.inverse.obj N')) ≫
          ep.map (ΦY.unitInv.app (ΦY.inverse.obj N'))) =
      ΦX.counitInv.app (Lp.obj N') ≫ ΦX.functor.map (ψp.hom.app N') := by
  have h1 : ΦX.inverse.map (Lp.map (ΦY.counitInv.app N')) ≫
      ψp.hom.app (ΦY.functor.obj (ΦY.inverse.obj N')) =
        ψp.hom.app N' ≫ ep.map (ΦY.inverse.map (ΦY.counitInv.app N')) :=
    ψp.hom.naturality (ΦY.counitInv.app N')
  have h2 := ΦY.inverse_counitInv_comp N'
  have hn : Lp.map (ΦY.counitInv.app N') ≫
      ΦX.counitInv.app (Lp.obj (ΦY.functor.obj (ΦY.inverse.obj N'))) =
        ΦX.counitInv.app (Lp.obj N') ≫
          ΦX.functor.map (ΦX.inverse.map (Lp.map (ΦY.counitInv.app N'))) :=
    ΦX.counitInv.naturality _
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ← Category.assoc, h1,
    Category.assoc, ← Functor.map_comp, h2, ep.map_id]
  exact congrArg _ (congrArg _ (Category.comp_id _))

/-- **The composition law of the squares read through the equivalences**, from the composition
law of the mates. -/
theorem equivalenceSquare_comp (ΦX : CX ≌ MX) (ΦY : CY ≌ MY) (ΦZ : CZ ≌ MZ)
    (Lp : MY ⥤ MX) (Lq : MZ ⥤ MY) (Lpq : MZ ⥤ MX) (ep : CY ⥤ CX) (eq : CZ ⥤ CY) (epq : CZ ⥤ CX)
    (ψp : Lp ⋙ ΦX.inverse ≅ ΦY.inverse ⋙ ep) (ψq : Lq ⋙ ΦY.inverse ≅ ΦZ.inverse ⋙ eq)
    (ψpq : Lpq ⋙ ΦX.inverse ≅ ΦZ.inverse ⋙ epq) (cL : Lq ⋙ Lp ⟶ Lpq) (χ : eq ⋙ ep ⟶ epq)
    (hψ : Functor.whiskerLeft Lq ψp.hom ≫ Functor.whiskerRight ψq.hom ep ≫
        Functor.whiskerLeft ΦZ.inverse χ = Functor.whiskerRight cL ΦX.inverse ≫ ψpq.hom)
    (βp : ΦY.functor ⋙ Lp ≅ ep ⋙ ΦX.functor) (βq : ΦZ.functor ⋙ Lq ≅ eq ⋙ ΦY.functor)
    (βpq : ΦZ.functor ⋙ Lpq ≅ epq ⋙ ΦX.functor)
    (hβp : ∀ M, βp.hom.app M = ΦX.counitInv.app (Lp.obj (ΦY.functor.obj M)) ≫
        ΦX.functor.map (ψp.hom.app (ΦY.functor.obj M) ≫ ep.map (ΦY.unitInv.app M)))
    (hβq : ∀ M, βq.hom.app M = ΦY.counitInv.app (Lq.obj (ΦZ.functor.obj M)) ≫
        ΦY.functor.map (ψq.hom.app (ΦZ.functor.obj M) ≫ eq.map (ΦZ.unitInv.app M)))
    (hβpq : ∀ M, βpq.hom.app M = ΦX.counitInv.app (Lpq.obj (ΦZ.functor.obj M)) ≫
        ΦX.functor.map (ψpq.hom.app (ΦZ.functor.obj M) ≫ epq.map (ΦZ.unitInv.app M))) :
    Functor.whiskerRight βq.hom Lp ≫ Functor.whiskerLeft eq βp.hom ≫
        Functor.whiskerRight χ ΦX.functor =
      Functor.whiskerLeft ΦZ.functor cL ≫ βpq.hom := by
  ext M
  have hψM := NatTrans.congr_app hψ (ΦZ.functor.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hψM ⊢
  have hnat : Lp.map (ΦY.functor.map (ψq.hom.app (ΦZ.functor.obj M) ≫ eq.map (ΦZ.unitInv.app M))) ≫
      βp.hom.app (eq.obj M) = βp.hom.app (ΦY.inverse.obj (Lq.obj (ΦZ.functor.obj M))) ≫
        ΦX.functor.map (ep.map (ψq.hom.app (ΦZ.functor.obj M) ≫ eq.map (ΦZ.unitInv.app M))) :=
    βp.hom.naturality _
  have hc : cL.app (ΦZ.functor.obj M) ≫ ΦX.counitInv.app (Lpq.obj (ΦZ.functor.obj M)) =
      ΦX.counitInv.app (Lp.obj (Lq.obj (ΦZ.functor.obj M))) ≫
        ΦX.functor.map (ΦX.inverse.map (cL.app (ΦZ.functor.obj M))) :=
    ΦX.counitInv.naturality _
  have hχ : χ.app (ΦZ.inverse.obj (ΦZ.functor.obj M)) ≫ epq.map (ΦZ.unitInv.app M) =
      ep.map (eq.map (ΦZ.unitInv.app M)) ≫ χ.app M := (χ.naturality _).symm
  rw [hβq, Functor.map_comp, Category.assoc, reassoc_of% hnat, hβp, ← Category.assoc,
    ← Category.assoc, counitInv_comp_equivalenceSquare, hβpq, ← Category.assoc, hc,
    Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  rw [Category.assoc, ← Functor.map_comp]
  refine congrArg (ΦX.counitInv.app _ ≫ ·) (congrArg ΦX.functor.map ?_)
  rw [← Category.assoc (ΦX.inverse.map _), ← hψM]
  simp only [Category.assoc, Functor.map_comp, hχ]

/-- The composition law of the squares of right adjoints, from its form at each object. -/
theorem sq_comp_of_app (ΦX : CX ≌ MX) (ΦY : CY ≌ MY) (ΦZ : CZ ≌ MZ)
    {Rp : MX ⥤ MY} {Rq : MY ⥤ MZ} {Rpq Rpq' : MX ⥤ MZ}
    {ep' : CX ⥤ CY} {eq' : CY ⥤ CZ} {epq' : CX ⥤ CZ}
    (sqp : ep' ⋙ ΦY.functor ≅ ΦX.functor ⋙ Rp) (sqq : eq' ⋙ ΦZ.functor ≅ ΦY.functor ⋙ Rq)
    (sqpq : epq' ⋙ ΦZ.functor ≅ ΦX.functor ⋙ Rpq) (cE : epq' ⟶ ep' ⋙ eq')
    (cR : Rp ⋙ Rq ≅ Rpq') (η : Rpq ⟶ Rpq')
    (h : ∀ N, ΦZ.functor.map (cE.app N) ≫ sqq.hom.app (ep'.obj N) ≫ Rq.map (sqp.hom.app N) ≫
        cR.hom.app (ΦX.functor.obj N) = sqpq.hom.app N ≫ (Functor.whiskerLeft ΦX.functor η).app N) :
    Functor.whiskerRight cE ΦZ.functor ≫ Functor.whiskerLeft ep' sqq.hom ≫
        Functor.whiskerRight sqp.hom Rq =
      sqpq.hom ≫ Functor.whiskerLeft ΦX.functor (η ≫ cR.inv) := by
  ext N
  have hN := h N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hN ⊢
  rw [← Category.assoc (sqpq.hom.app N), ← hN]
  simp

/-- `leftAdjointUniq_comp` with the composition law of the squares of right adjoints given at
each object. -/
theorem leftAdjointUniq_comp_of_app (ΦX : CX ≌ MX) (ΦY : CY ≌ MY) (ΦZ : CZ ≌ MZ)
    {Lp : MY ⥤ MX} {Rp : MX ⥤ MY} (adjp : Lp ⊣ Rp)
    {Lq : MZ ⥤ MY} {Rq : MY ⥤ MZ} (adjq : Lq ⊣ Rq)
    {Lpq : MZ ⥤ MX} {Rpq : MX ⥤ MZ} (adjpq : Lpq ⊣ Rpq)
    {ep : CY ⥤ CX} {ep' : CX ⥤ CY} (adjep : ep ⊣ ep')
    {eq : CZ ⥤ CY} {eq' : CY ⥤ CZ} (adjeq : eq ⊣ eq')
    {epq : CZ ⥤ CX} {epq' : CX ⥤ CZ} (adjepq : epq ⊣ epq')
    (sqp : ep' ⋙ ΦY.functor ≅ ΦX.functor ⋙ Rp) (sqq : eq' ⋙ ΦZ.functor ≅ ΦY.functor ⋙ Rq)
    (sqpq : epq' ⋙ ΦZ.functor ≅ ΦX.functor ⋙ Rpq) {Rpq' : MX ⥤ MZ}
    (cR : Rp ⋙ Rq ≅ Rpq') (η : Rpq ⟶ Rpq')
    (cL : Lq ⋙ Lp ⟶ Lpq) (hL : conjugateEquiv adjpq (adjq.comp adjp) cL = η ≫ cR.inv)
    (χ : eq ⋙ ep ⟶ epq) (cE : epq' ⟶ ep' ⋙ eq')
    (hE : conjugateEquiv adjepq (adjeq.comp adjep) χ = cE)
    (h : ∀ N, ΦZ.functor.map (cE.app N) ≫ sqq.hom.app (ep'.obj N) ≫ Rq.map (sqp.hom.app N) ≫
        cR.hom.app (ΦX.functor.obj N) = sqpq.hom.app N ≫ (Functor.whiskerLeft ΦX.functor η).app N) :
    Functor.whiskerLeft Lq (Adjunction.leftAdjointUniq (adjp.comp ΦX.symm.toAdjunction)
          ((ΦY.symm.toAdjunction.comp adjep).ofNatIsoRight sqp)).hom ≫
        Functor.whiskerRight (Adjunction.leftAdjointUniq (adjq.comp ΦY.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjeq).ofNatIsoRight sqq)).hom ep ≫
        Functor.whiskerLeft ΦZ.inverse χ =
      Functor.whiskerRight cL ΦX.inverse ≫
        (Adjunction.leftAdjointUniq (adjpq.comp ΦX.symm.toAdjunction)
          ((ΦZ.symm.toAdjunction.comp adjepq).ofNatIsoRight sqpq)).hom :=
  leftAdjointUniq_comp ΦX ΦY ΦZ adjp adjq adjpq adjep adjeq adjepq sqp sqq sqpq cL _ hL χ cE hE
    (sq_comp_of_app ΦX ΦY ΦZ sqp sqq sqpq cE cR η h)

/-- Cancel an isomorphism whiskered on the left against its inverse at the end of a composite. -/
theorem trans_isoWhiskerLeft_symm_trans {A₀ A₁ A₂ : Type*} [Category A₀] [Category A₁] [Category A₂]
    {F₁ F₂ F₃ : A₀ ⥤ A₂} {G : A₀ ⥤ A₁} {K L : A₁ ⥤ A₂} (a : F₁ ≅ F₂) (b : F₂ ≅ F₃)
    (c : F₃ ≅ G ⋙ K) (e : L ≅ K) :
    (a ≪≫ b ≪≫ c ≪≫ Functor.isoWhiskerLeft G e.symm) ≪≫ Functor.isoWhiskerLeft G e =
      a ≪≫ b ≪≫ c := by
  ext1
  simp [← Functor.whiskerLeft_comp]

/-- **Pasting of composition laws.**  Squares `τ_f : ε ⋙ L_f ≅ s_f ⋙ ε'` assembled from
identifications `κ : ε ≅ A ⋙ F`, squares `β_f : F ⋙ L_f ≅ e_f ⋙ F'` and `α_f : s_f ⋙ A' ≅ A ⋙ e_f`
compose as soon as the `β` and the `α` do. -/
theorem pastedSquare_comp {ZX ZY ZZ CX CY CZ MX MY MZ : Type*} [Category ZX] [Category ZY]
    [Category ZZ] [Category CX] [Category CY] [Category CZ] [Category MX] [Category MY]
    [Category MZ]
    (εX : ZX ⥤ MX) (εY : ZY ⥤ MY) (εZ : ZZ ⥤ MZ) (AX : ZX ⥤ CX) (AY : ZY ⥤ CY) (AZ : ZZ ⥤ CZ)
    (FX : CX ⥤ MX) (FY : CY ⥤ MY) (FZ : CZ ⥤ MZ)
    (κX : εX ≅ AX ⋙ FX) (κY : εY ≅ AY ⋙ FY) (κZ : εZ ≅ AZ ⋙ FZ)
    (Lp : MY ⥤ MX) (Lq : MZ ⥤ MY) (Lpq : MZ ⥤ MX) (ep : CY ⥤ CX) (eq : CZ ⥤ CY) (epq : CZ ⥤ CX)
    (sp : ZY ⥤ ZX) (sq : ZZ ⥤ ZY) (spq : ZZ ⥤ ZX)
    (βp : FY ⋙ Lp ≅ ep ⋙ FX) (βq : FZ ⋙ Lq ≅ eq ⋙ FY) (βpq : FZ ⋙ Lpq ≅ epq ⋙ FX)
    (αp : sp ⋙ AX ≅ AY ⋙ ep) (αq : sq ⋙ AY ≅ AZ ⋙ eq) (αpq : spq ⋙ AX ≅ AZ ⋙ epq)
    (cL : Lq ⋙ Lp ⟶ Lpq) (χ : eq ⋙ ep ⟶ epq) (cs : sq ⋙ sp ⟶ spq)
    (hβ : Functor.whiskerRight βq.hom Lp ≫ Functor.whiskerLeft eq βp.hom ≫
        Functor.whiskerRight χ FX = Functor.whiskerLeft FZ cL ≫ βpq.hom)
    (hα : Functor.whiskerRight αq.inv ep ≫ Functor.whiskerLeft sq αp.inv ≫
        Functor.whiskerRight cs AX = Functor.whiskerLeft AZ χ ≫ αpq.inv)
    (τp : εY ⋙ Lp ≅ sp ⋙ εX) (τq : εZ ⋙ Lq ≅ sq ⋙ εY) (τpq : εZ ⋙ Lpq ≅ spq ⋙ εX)
    (hτp : ∀ M, τp.hom.app M = Lp.map (κY.hom.app M) ≫ βp.hom.app (AY.obj M) ≫
      FX.map (αp.inv.app M) ≫ κX.inv.app (sp.obj M))
    (hτq : ∀ M, τq.hom.app M = Lq.map (κZ.hom.app M) ≫ βq.hom.app (AZ.obj M) ≫
      FY.map (αq.inv.app M) ≫ κY.inv.app (sq.obj M))
    (hτpq : ∀ M, τpq.hom.app M = Lpq.map (κZ.hom.app M) ≫ βpq.hom.app (AZ.obj M) ≫
      FX.map (αpq.inv.app M) ≫ κX.inv.app (spq.obj M)) :
    Functor.whiskerRight τq.hom Lp ≫ Functor.whiskerLeft sq τp.hom ≫
        Functor.whiskerRight cs εX = Functor.whiskerLeft εZ cL ≫ τpq.hom := by
  ext M
  have hβM := NatTrans.congr_app hβ (AZ.obj M)
  have hαM := NatTrans.congr_app hα M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hβM hαM ⊢
  have F2 : Lp.map (FY.map (αq.inv.app M)) ≫ βp.hom.app (AY.obj (sq.obj M)) =
      βp.hom.app (eq.obj (AZ.obj M)) ≫ FX.map (ep.map (αq.inv.app M)) :=
    βp.hom.naturality (αq.inv.app M)
  have F3 : κX.inv.app (sp.obj (sq.obj M)) ≫ εX.map (cs.app M) =
      FX.map (AX.map (cs.app M)) ≫ κX.inv.app (spq.obj M) := (κX.inv.naturality (cs.app M)).symm
  have F6 : Lp.map (Lq.map (κZ.hom.app M)) ≫ cL.app (FZ.obj (AZ.obj M)) =
      cL.app (εZ.obj M) ≫ Lpq.map (κZ.hom.app M) := cL.naturality (κZ.hom.app M)
  have F4 := congrArg FX.map hαM
  simp only [Functor.map_comp] at F4
  rw [hτq, hτp, hτpq]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Lp.map_comp_assoc (κY.inv.app _), Iso.inv_hom_id_app, Lp.map_id, Category.id_comp,
    reassoc_of% F2, F3, reassoc_of% F4, reassoc_of% hβM, reassoc_of% F6]

/-- The pasted square at one object. -/
theorem pastedSquare_hom_app {Z Z' C C' M M' : Type*} [Category Z] [Category Z'] [Category C]
    [Category C'] [Category M] [Category M'] {ε : Z ⥤ M} {ε' : Z' ⥤ M'} {A : Z ⥤ C}
    {A' : Z' ⥤ C'} {P F : C ⥤ M} {P' F' : C' ⥤ M'} (L : M ⥤ M') (e : C ⥤ C') (s : Z ⥤ Z')
    (ι : ε ≅ A ⋙ P) (r : P ≅ F) (β : F ⋙ L ≅ e ⋙ F') (α : s ⋙ A' ≅ A ⋙ e) (r' : P' ≅ F')
    (ι' : ε' ≅ A' ⋙ P') (X : Z) :
    (Functor.isoWhiskerRight ι L ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft A (Functor.isoWhiskerRight r L ≪≫ β) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α.symm F' ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft s (Functor.isoWhiskerLeft A' r'.symm ≪≫ ι'.symm)).hom.app X =
      L.map ((ι ≪≫ Functor.isoWhiskerLeft A r).hom.app X) ≫ β.hom.app (A.obj X) ≫
        F'.map (α.inv.app X) ≫ (ι' ≪≫ Functor.isoWhiskerLeft A' r').inv.app (s.obj X) := by
  simp

/-- A composition law of isomorphisms of composite functors, read on the inverses. -/
theorem whiskered_inv_comp {ZX ZY ZZ CX CY CZ : Type*} [Category ZX] [Category ZY] [Category ZZ]
    [Category CX] [Category CY] [Category CZ] {AX : ZX ⥤ CX} {AY : ZY ⥤ CY} {AZ : ZZ ⥤ CZ}
    {ep : CY ⥤ CX} {eq : CZ ⥤ CY} {epq : CZ ⥤ CX} {sp : ZY ⥤ ZX} {sq : ZZ ⥤ ZY} {spq : ZZ ⥤ ZX}
    (αp : sp ⋙ AX ≅ AY ⋙ ep) (αq : sq ⋙ AY ≅ AZ ⋙ eq) (αpq : spq ⋙ AX ≅ AZ ⋙ epq)
    (χ : eq ⋙ ep ≅ epq) (cs : sq ⋙ sp ≅ spq)
    (E : Functor.isoWhiskerLeft sq αp ≪≫ Functor.isoWhiskerRight αq ep ≪≫
        Functor.isoWhiskerLeft AZ χ = Functor.isoWhiskerRight cs AX ≪≫ αpq) :
    Functor.whiskerRight αq.inv ep ≫ Functor.whiskerLeft sq αp.inv ≫
        Functor.whiskerRight cs.hom AX = Functor.whiskerLeft AZ χ.hom ≫ αpq.inv := by
  ext M
  have hM := NatTrans.congr_app (congrArg Iso.hom E) M
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hM
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (αpq.hom.app M), Category.assoc, Category.assoc, ← hM, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc, ← ep.map_comp_assoc,
    Iso.inv_hom_id_app, ep.map_id, Category.id_comp]


/-- A composition law of squares of functors, read at one object. -/
theorem pastedSquare_comp_app {ZX ZY ZZ MX MY MZ : Type*} [Category ZX] [Category ZY]
    [Category ZZ] [Category MX] [Category MY] [Category MZ] {εX : ZX ⥤ MX} {εY : ZY ⥤ MY}
    {εZ : ZZ ⥤ MZ} {Lp : MY ⥤ MX} {Lq : MZ ⥤ MY} {Lpq : MZ ⥤ MX} {sp : ZY ⥤ ZX} {sq : ZZ ⥤ ZY}
    {spq : ZZ ⥤ ZX} {τp : εY ⋙ Lp ≅ sp ⋙ εX} {τq : εZ ⋙ Lq ≅ sq ⋙ εY}
    {τpq : εZ ⋙ Lpq ≅ spq ⋙ εX} {cL : Lq ⋙ Lp ⟶ Lpq} {cs : sq ⋙ sp ⟶ spq}
    (h : Functor.whiskerRight τq.hom Lp ≫ Functor.whiskerLeft sq τp.hom ≫
        Functor.whiskerRight cs εX = Functor.whiskerLeft εZ cL ≫ τpq.hom) (M : ZZ) :
    Lp.map (τq.hom.app M) ≫ τp.hom.app (sq.obj M) ≫ εX.map (cs.app M) =
      cL.app (εZ.obj M) ≫ τpq.hom.app M := by
  simpa using NatTrans.congr_app h M

/-- Moving the image of an isomorphism across an equation. -/
theorem comp_map_inv_of_comp_map_hom {D E : Type*} [Category D] [Category E]
    (G : D ⥤ E) {X Y : E} {Z₁ Z₂ : D} (a : X ⟶ Y) (b : Y ⟶ G.obj Z₁) (i : Z₁ ≅ Z₂)
    (c : X ⟶ G.obj Z₂) (h : a ≫ b ≫ G.map i.hom = c) : a ≫ b = c ≫ G.map i.inv := by
  rw [← h]
  simp [← G.map_comp]

/-- **The cube of pasted squares**: the composition laws along two factorizations of the same
morphism, and a transport between the two composites, give the cube. -/
theorem pastedSquare_cube {ZT ZW ZT' ZW' MT MW MT' MW' : Type*} [Category ZT] [Category ZW]
    [Category ZT'] [Category ZW'] [Category MT] [Category MW] [Category MT'] [Category MW']
    {εT : ZT ⥤ MT} {εW : ZW ⥤ MW} {εT' : ZT' ⥤ MT'} {εW' : ZW' ⥤ MW'}
    {Lp : MW ⥤ MW'} {Lq : MT ⥤ MW} {Lr : MT' ⥤ MW'} {Ls : MT ⥤ MT'} {Lpq Lrs : MT ⥤ MW'}
    {sp : ZW ⥤ ZW'} {sq : ZT ⥤ ZW} {sr : ZT' ⥤ ZW'} {ss : ZT ⥤ ZT'} {spq srs : ZT ⥤ ZW'}
    {τp : εW ⋙ Lp ≅ sp ⋙ εW'} {τq : εT ⋙ Lq ≅ sq ⋙ εW} {τr : εT' ⋙ Lr ≅ sr ⋙ εW'}
    {τs : εT ⋙ Ls ≅ ss ⋙ εT'} {τpq : εT ⋙ Lpq ≅ spq ⋙ εW'} {τrs : εT ⋙ Lrs ≅ srs ⋙ εW'}
    {cLpq : Lq ⋙ Lp ⟶ Lpq} {cLrs : Ls ⋙ Lr ⟶ Lrs} {cspq : sq ⋙ sp ≅ spq} {csrs : ss ⋙ sr ≅ srs}
    {eL : Lpq ⟶ Lrs} {es : spq ⟶ srs} (FS : Lq ⋙ Lp ⟶ Ls ⋙ Lr)
    (hpq : Functor.whiskerRight τq.hom Lp ≫ Functor.whiskerLeft sq τp.hom ≫
        Functor.whiskerRight cspq.hom εW' = Functor.whiskerLeft εT cLpq ≫ τpq.hom)
    (hrs : Functor.whiskerRight τs.hom Lr ≫ Functor.whiskerLeft ss τr.hom ≫
        Functor.whiskerRight csrs.hom εW' = Functor.whiskerLeft εT cLrs ≫ τrs.hom)
    (ht : τpq.hom ≫ Functor.whiskerRight es εW' = Functor.whiskerLeft εT eL ≫ τrs.hom)
    (hE : cLpq ≫ eL = FS ≫ cLrs) (F : ZT) :
    Lp.map (τq.hom.app F) ≫ τp.hom.app (sq.obj F) ≫ εW'.map ((cspq.hom ≫ es ≫ csrs.inv).app F) =
      FS.app (εT.obj F) ≫ Lr.map (τs.hom.app F) ≫ τr.hom.app (ss.obj F) := by
  have h1 := NatTrans.congr_app hpq F
  have h2 := NatTrans.congr_app hrs F
  have h3 := NatTrans.congr_app ht F
  have h4 := NatTrans.congr_app hE (εT.obj F)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h1 h2 h3 h4
  have h2' : Lr.map (τs.hom.app F) ≫ τr.hom.app (ss.obj F) =
      cLrs.app (εT.obj F) ≫ τrs.hom.app F ≫ εW'.map (csrs.inv.app F) := by
    rw [← reassoc_of% h2]
    simp [← εW'.map_comp]
  rw [NatTrans.comp_app, NatTrans.comp_app, εW'.map_comp, εW'.map_comp, reassoc_of% h1,
    reassoc_of% h3, h2', reassoc_of% h4]

/-- Two composites of an isomorphism with transports along equalities of objects agree. -/
theorem comp_eqToHom_eq_comp_inv_comp {C : Type*} [Category C] {A P P' Q Q' R : C} (m : A ⟶ P)
    (m' : Q ≅ Q') (e₁ : P = P') (e₂ : P' = R) (e₃ : P = Q') (e₄ : Q' = R) :
    (m ≫ eqToHom e₁) ≫ eqToHom e₂ = (m ≫ eqToHom e₃ ≫ m'.inv) ≫ m'.hom ≫ eqToHom e₄ := by
  simp

/-- **Conjugating a cube of squares**: replacing the pullbacks by isomorphic ones (`π`, `ζ`) on
both sides of the squares carries the cube to the conjugated cube. -/
theorem conjugatedSquare_cube {ZT ZW ZT' ZW' MT MW MT' MW' : Type*} [Category ZT] [Category ZW]
    [Category ZT'] [Category ZW'] [Category MT] [Category MW] [Category MT'] [Category MW']
    {εT : ZT ⥤ MT} {εW : ZW ⥤ MW} {εT' : ZT' ⥤ MT'} {εW' : ZW' ⥤ MW'}
    {Lp Ltp : MW ⥤ MW'} {Lq Ltq : MT ⥤ MW} {Lr Ltr : MT' ⥤ MW'} {Ls Lts : MT ⥤ MT'}
    {sp ztp : ZW ⥤ ZW'} {sq ztq : ZT ⥤ ZW} {sr ztr : ZT' ⥤ ZW'} {ss zts : ZT ⥤ ZT'}
    (πp : Ltp ≅ Lp) (πq : Ltq ≅ Lq) (πr : Ltr ≅ Lr) (πs : Lts ≅ Ls)
    (ζp : ztp ≅ sp) (ζq : ztq ≅ sq) (ζr : ztr ≅ sr) (ζs : zts ≅ ss)
    (τp : εW ⋙ Lp ≅ sp ⋙ εW') (τq : εT ⋙ Lq ≅ sq ⋙ εW) (τr : εT' ⋙ Lr ≅ sr ⋙ εW')
    (τs : εT ⋙ Ls ≅ ss ⋙ εT') (Zs : sq ⋙ sp ⟶ ss ⋙ sr) (Fs : Lq ⋙ Lp ⟶ Ls ⋙ Lr)
    (Ft : Ltq ⋙ Ltp ⟶ Lts ⋙ Ltr) (M : ZT)
    (hcube : Lp.map (τq.hom.app M) ≫ τp.hom.app (sq.obj M) ≫ εW'.map (Zs.app M) =
      Fs.app (εT.obj M) ≫ Lr.map (τs.hom.app M) ≫ τr.hom.app (ss.obj M))
    (hπ : Ltp.map (πq.hom.app (εT.obj M)) ≫ πp.hom.app (Lq.obj (εT.obj M)) ≫ Fs.app (εT.obj M) =
      Ft.app (εT.obj M) ≫ Ltr.map (πs.hom.app (εT.obj M)) ≫ πr.hom.app (Ls.obj (εT.obj M))) :
    Ltp.map (πq.hom.app (εT.obj M) ≫ τq.hom.app M ≫ εW.map (ζq.inv.app M)) ≫
        (πp.hom.app (εW.obj (ztq.obj M)) ≫ τp.hom.app (ztq.obj M) ≫
          εW'.map (ζp.inv.app (ztq.obj M))) ≫
        εW'.map (ζp.hom.app (ztq.obj M) ≫ sp.map (ζq.hom.app M) ≫ Zs.app M ≫
          sr.map (ζs.inv.app M) ≫ ζr.inv.app (zts.obj M)) =
      Ft.app (εT.obj M) ≫
        Ltr.map (πs.hom.app (εT.obj M) ≫ τs.hom.app M ≫ εT'.map (ζs.inv.app M)) ≫
        (πr.hom.app (εT'.obj (zts.obj M)) ≫ τr.hom.app (zts.obj M) ≫
          εW'.map (ζr.inv.app (zts.obj M))) := by
  have np := πp.hom.naturality (τq.hom.app M ≫ εW.map (ζq.inv.app M))
  have nr := πr.hom.naturality (τs.hom.app M ≫ εT'.map (ζs.inv.app M))
  have tp := τp.hom.naturality (ζq.inv.app M)
  have tr := τr.hom.naturality (ζs.inv.app M)
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map] at np nr tp tr
  have F1 : εW'.map (ζp.inv.app (ztq.obj M)) ≫ εW'.map (ζp.hom.app (ztq.obj M)) = 𝟙 _ := by
    rw [← εW'.map_comp, Iso.inv_hom_id_app, εW'.map_id]
  have F2 : εW'.map (sp.map (ζq.inv.app M)) ≫ εW'.map (sp.map (ζq.hom.app M)) = 𝟙 _ := by
    rw [← εW'.map_comp, ← sp.map_comp, Iso.inv_hom_id_app, sp.map_id, εW'.map_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% F1, reassoc_of% np, reassoc_of% tp, reassoc_of% F2, reassoc_of% hcube,
    reassoc_of% hπ, reassoc_of% nr, reassoc_of% tr]

/-- **The cube of comparisons of two families of pullbacks**: two comparisons `π` of pullbacks,
compatible with the composition laws on both sides and with transport, form a cube. -/
theorem comparison_cube {MT MW MT' MW' : Type*} [Category MT] [Category MW] [Category MT']
    [Category MW'] {Lp Ltp : MW ⥤ MW'} {Lq Ltq : MT ⥤ MW} {Lr Ltr : MT' ⥤ MW'} {Ls Lts : MT ⥤ MT'}
    {Lpq Lrs Ltpq Ltrs Kpq Krs : MT ⥤ MW'}
    (πp : Ltp ≅ Lp) (πq : Ltq ≅ Lq) (πr : Ltr ≅ Lr) (πs : Lts ≅ Ls) (πpq : Ltpq ≅ Lpq)
    (πrs : Ltrs ≅ Lrs) (cTpq : Kpq ≅ Ltq ⋙ Ltp) (cTrs : Krs ≅ Lts ⋙ Ltr) (trpq : Kpq ≅ Ltpq)
    (trrs : Krs ≅ Ltrs) (mpq : Lq ⋙ Lp ≅ Lpq) (mrs : Ls ⋙ Lr ≅ Lrs) (eM : Lpq = Lrs)
    (eT : Ltpq = Ltrs)
    (lpq : cTpq.inv ≫ trpq.hom ≫ πpq.hom =
      Functor.whiskerRight πq.hom Ltp ≫ Functor.whiskerLeft Lq πp.hom ≫ mpq.hom)
    (lrs : cTrs.inv ≫ trrs.hom ≫ πrs.hom =
      Functor.whiskerRight πs.hom Ltr ≫ Functor.whiskerLeft Ls πr.hom ≫ mrs.hom)
    (ht : πpq.hom ≫ eqToHom eM = eqToHom eT ≫ πrs.hom) (X : MT) :
    Ltp.map (πq.hom.app X) ≫ πp.hom.app (Lq.obj X) ≫ (mpq.hom ≫ eqToHom eM ≫ mrs.inv).app X =
      (cTpq.inv ≫ trpq.hom ≫ eqToHom eT ≫ trrs.inv ≫ cTrs.hom).app X ≫
        Ltr.map (πs.hom.app X) ≫ πr.hom.app (Ls.obj X) := by
  have key : Functor.whiskerRight πq.hom Ltp ≫ Functor.whiskerLeft Lq πp.hom ≫
      (mpq.hom ≫ eqToHom eM ≫ mrs.inv) =
      (cTpq.inv ≫ trpq.hom ≫ eqToHom eT ≫ trrs.inv ≫ cTrs.hom) ≫
        Functor.whiskerRight πs.hom Ltr ≫ Functor.whiskerLeft Ls πr.hom := by
    have lrs' : Functor.whiskerRight πs.hom Ltr ≫ Functor.whiskerLeft Ls πr.hom =
        cTrs.inv ≫ trrs.hom ≫ πrs.hom ≫ mrs.inv := by
      have h := congrArg (· ≫ mrs.inv) lrs
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
      exact h.symm
    rw [lrs', reassoc_of% lpq.symm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, reassoc_of% ht]
  simpa using NatTrans.congr_app key X

/-- The square of pullbacks read through comparisons on both sides, at one object. -/
theorem conjugatedSquare_hom_app {ZT ZT' MT MT' : Type*} [Category ZT] [Category ZT'] [Category MT]
    [Category MT'] {εT : ZT ⥤ MT} {εT' : ZT' ⥤ MT'} {L Lt : MT ⥤ MT'} {s zt : ZT ⥤ ZT'}
    {K K' : ZT ⥤ MT'} (c : K ≅ εT ⋙ Lt) (c' : K' ≅ zt ⋙ εT') (π : Lt ≅ L)
    (τ : εT ⋙ L ≅ s ⋙ εT') (ζ : zt ≅ s) (M : ZT) :
    c.inv.app M ≫ (c ≪≫ Functor.isoWhiskerLeft εT π ≪≫ τ ≪≫ Functor.isoWhiskerRight ζ.symm εT' ≪≫
      c'.symm).hom.app M ≫ c'.hom.app M =
      π.hom.app (εT.obj M) ≫ τ.hom.app M ≫ εT'.map (ζ.inv.app M) := by
  simp

/-- `conjugatedSquare_hom_app` for a square given by its definition. -/
theorem conjugatedSquare_hom_app_of_eq {ZT ZT' MT MT' : Type*} [Category ZT] [Category ZT']
    [Category MT] [Category MT'] {εT : ZT ⥤ MT} {εT' : ZT' ⥤ MT'} {L Lt : MT ⥤ MT'}
    {s zt : ZT ⥤ ZT'} {K K' : ZT ⥤ MT'} {c : K ≅ εT ⋙ Lt} {c' : K' ≅ zt ⋙ εT'} {π : Lt ≅ L}
    {τ : εT ⋙ L ≅ s ⋙ εT'} {ζ : zt ≅ s} {ρ : K ≅ K'}
    (hρ : ρ = c ≪≫ Functor.isoWhiskerLeft εT π ≪≫ τ ≪≫ Functor.isoWhiskerRight ζ.symm εT' ≪≫
      c'.symm) (M : ZT) :
    c.inv.app M ≫ ρ.hom.app M ≫ c'.hom.app M =
      π.hom.app (εT.obj M) ≫ τ.hom.app M ≫ εT'.map (ζ.inv.app M) := by
  subst hρ
  exact conjugatedSquare_hom_app c c' π τ ζ M

/-- `conjugatedSquare_cube` with the conjugated squares given by their formulas. -/
theorem conjugatedSquare_cube' {ZT ZW ZT' ZW' MT MW MT' MW' : Type*} [Category ZT] [Category ZW]
    [Category ZT'] [Category ZW'] [Category MT] [Category MW] [Category MT'] [Category MW']
    {εT : ZT ⥤ MT} {εW : ZW ⥤ MW} {εT' : ZT' ⥤ MT'} {εW' : ZW' ⥤ MW'}
    {Lp Ltp : MW ⥤ MW'} {Lq Ltq : MT ⥤ MW} {Lr Ltr : MT' ⥤ MW'} {Ls Lts : MT ⥤ MT'}
    {sp ztp : ZW ⥤ ZW'} {sq ztq : ZT ⥤ ZW} {sr ztr : ZT' ⥤ ZW'} {ss zts : ZT ⥤ ZT'}
    (πp : Ltp ≅ Lp) (πq : Ltq ≅ Lq) (πr : Ltr ≅ Lr) (πs : Lts ≅ Ls)
    (ζp : ztp ≅ sp) (ζq : ztq ≅ sq) (ζr : ztr ≅ sr) (ζs : zts ≅ ss)
    (τp : εW ⋙ Lp ≅ sp ⋙ εW') (τq : εT ⋙ Lq ≅ sq ⋙ εW) (τr : εT' ⋙ Lr ≅ sr ⋙ εW')
    (τs : εT ⋙ Ls ≅ ss ⋙ εT') (Zs : sq ⋙ sp ⟶ ss ⋙ sr) (Fs : Lq ⋙ Lp ⟶ Ls ⋙ Lr)
    (Ft : Ltq ⋙ Ltp ⟶ Lts ⋙ Ltr)
    (θp : ∀ N, Ltp.obj (εW.obj N) ⟶ εW'.obj (ztp.obj N))
    (θq : ∀ N, Ltq.obj (εT.obj N) ⟶ εW.obj (ztq.obj N))
    (θr : ∀ N, Ltr.obj (εT'.obj N) ⟶ εW'.obj (ztr.obj N))
    (θs : ∀ N, Lts.obj (εT.obj N) ⟶ εT'.obj (zts.obj N))
    (hθp : ∀ N, θp N = πp.hom.app (εW.obj N) ≫ τp.hom.app N ≫ εW'.map (ζp.inv.app N))
    (hθq : ∀ N, θq N = πq.hom.app (εT.obj N) ≫ τq.hom.app N ≫ εW.map (ζq.inv.app N))
    (hθr : ∀ N, θr N = πr.hom.app (εT'.obj N) ≫ τr.hom.app N ≫ εW'.map (ζr.inv.app N))
    (hθs : ∀ N, θs N = πs.hom.app (εT.obj N) ≫ τs.hom.app N ≫ εT'.map (ζs.inv.app N)) (M : ZT)
    (hcube : Lp.map (τq.hom.app M) ≫ τp.hom.app (sq.obj M) ≫ εW'.map (Zs.app M) =
      Fs.app (εT.obj M) ≫ Lr.map (τs.hom.app M) ≫ τr.hom.app (ss.obj M))
    (hπ : Ltp.map (πq.hom.app (εT.obj M)) ≫ πp.hom.app (Lq.obj (εT.obj M)) ≫ Fs.app (εT.obj M) =
      Ft.app (εT.obj M) ≫ Ltr.map (πs.hom.app (εT.obj M)) ≫ πr.hom.app (Ls.obj (εT.obj M))) :
    Ltp.map (θq M) ≫ θp (ztq.obj M) ≫
        εW'.map (ζp.hom.app (ztq.obj M) ≫ sp.map (ζq.hom.app M) ≫ Zs.app M ≫
          sr.map (ζs.inv.app M) ≫ ζr.inv.app (zts.obj M)) =
      Ft.app (εT.obj M) ≫ Ltr.map (θs M) ≫ θr (zts.obj M) := by
  rw [hθq, hθp, hθs, hθr]
  exact conjugatedSquare_cube πp πq πr πs ζp ζq ζr ζs τp τq τr τs Zs Fs Ft M hcube hπ

/-- **Conjugating a cube of squares, with the comparison cube filled in**: the squares
`ρ_f = c_f⁻¹ ≫ ρ_f ≫ c'_f` read off isomorphisms `ρ_f` conjugate to `π_f`, `τ_f`, `ζ_f` form a
cube as soon as the `τ_f` do and the `π_f` are compatible with the composition laws. -/
theorem conjugatedSquare_comparison_cube {ZT ZW ZT' ZW' MT MW MT' MW' : Type*} [Category ZT]
    [Category ZW] [Category ZT'] [Category ZW'] [Category MT] [Category MW] [Category MT']
    [Category MW'] {εT : ZT ⥤ MT} {εW : ZW ⥤ MW} {εT' : ZT' ⥤ MT'} {εW' : ZW' ⥤ MW'}
    {Lp Ltp : MW ⥤ MW'} {Lq Ltq : MT ⥤ MW} {Lr Ltr : MT' ⥤ MW'} {Ls Lts : MT ⥤ MT'}
    {sp ztp : ZW ⥤ ZW'} {sq ztq : ZT ⥤ ZW} {sr ztr : ZT' ⥤ ZW'} {ss zts : ZT ⥤ ZT'}
    {Zm₁ Zm₂ : ZT ⥤ ZW'} {Lpq Lrs Ltpq Ltrs Kpq Krs : MT ⥤ MW'}
    {cTpq : Kpq ≅ Ltq ⋙ Ltp} {cTrs : Krs ≅ Lts ⋙ Ltr} {trpq : Kpq ≅ Ltpq}
    {trrs : Krs ≅ Ltrs} {mpq : Lq ⋙ Lp ≅ Lpq} {mrs : Ls ⋙ Lr ≅ Lrs} {eM : Lpq = Lrs}
    {eT : Ltpq = Ltrs}
    (πp : Ltp ≅ Lp) (πq : Ltq ≅ Lq) (πr : Ltr ≅ Lr) (πs : Lts ≅ Ls) (πpq : Ltpq ≅ Lpq)
    (πrs : Ltrs ≅ Lrs)
    (ζp : ztp ≅ sp) (ζq : ztq ≅ sq) (ζr : ztr ≅ sr) (ζs : zts ≅ ss)
    (τp : εW ⋙ Lp ≅ sp ⋙ εW') (τq : εT ⋙ Lq ≅ sq ⋙ εW) (τr : εT' ⋙ Lr ≅ sr ⋙ εW')
    (τs : εT ⋙ Ls ≅ ss ⋙ εT') (Z₁ : sq ⋙ sp ⟶ Zm₁) (Z₂ : Zm₁ ⟶ Zm₂) (Z₃ : Zm₂ ⟶ ss ⋙ sr)
    {Kp Kp' : ZW ⥤ MW'} {Kq Kq' : ZT ⥤ MW} {Kr Kr' : ZT' ⥤ MW'} {Ks Ks' : ZT ⥤ MT'}
    (cp : Kp ≅ εW ⋙ Ltp) (cq : Kq ≅ εT ⋙ Ltq) (cr : Kr ≅ εT' ⋙ Ltr) (cs : Ks ≅ εT ⋙ Lts)
    (cp' : Kp' ≅ ztp ⋙ εW') (cq' : Kq' ≅ ztq ⋙ εW) (cr' : Kr' ≅ ztr ⋙ εW')
    (cs' : Ks' ≅ zts ⋙ εT') (ρp : Kp ≅ Kp') (ρq : Kq ≅ Kq') (ρr : Kr ≅ Kr') (ρs : Ks ≅ Ks')
    (hρp : ρp = cp ≪≫ Functor.isoWhiskerLeft εW πp ≪≫ τp ≪≫
      Functor.isoWhiskerRight ζp.symm εW' ≪≫ cp'.symm)
    (hρq : ρq = cq ≪≫ Functor.isoWhiskerLeft εT πq ≪≫ τq ≪≫
      Functor.isoWhiskerRight ζq.symm εW ≪≫ cq'.symm)
    (hρr : ρr = cr ≪≫ Functor.isoWhiskerLeft εT' πr ≪≫ τr ≪≫
      Functor.isoWhiskerRight ζr.symm εW' ≪≫ cr'.symm)
    (hρs : ρs = cs ≪≫ Functor.isoWhiskerLeft εT πs ≪≫ τs ≪≫
      Functor.isoWhiskerRight ζs.symm εT' ≪≫ cs'.symm)
    (lpq : cTpq.inv ≫ trpq.hom ≫ πpq.hom =
      Functor.whiskerRight πq.hom Ltp ≫ Functor.whiskerLeft Lq πp.hom ≫ mpq.hom)
    (lrs : cTrs.inv ≫ trrs.hom ≫ πrs.hom =
      Functor.whiskerRight πs.hom Ltr ≫ Functor.whiskerLeft Ls πr.hom ≫ mrs.hom)
    (ht : πpq.hom ≫ eqToHom eM = eqToHom eT ≫ πrs.hom) (M : ZT)
    (hcube : Lp.map (τq.hom.app M) ≫ τp.hom.app (sq.obj M) ≫ εW'.map ((Z₁ ≫ Z₂ ≫ Z₃).app M) =
      (mpq.hom ≫ eqToHom eM ≫ mrs.inv).app (εT.obj M) ≫ Lr.map (τs.hom.app M) ≫
        τr.hom.app (ss.obj M)) :
    Ltp.map (cq.inv.app M ≫ ρq.hom.app M ≫ cq'.hom.app M) ≫
        (cp.inv.app (ztq.obj M) ≫ ρp.hom.app (ztq.obj M) ≫ cp'.hom.app (ztq.obj M)) ≫
        εW'.map (ζp.hom.app (ztq.obj M) ≫ sp.map (ζq.hom.app M) ≫ Z₁.app M ≫ Z₂.app M ≫
          Z₃.app M ≫ sr.map (ζs.inv.app M) ≫ ζr.inv.app (zts.obj M)) =
      (cTpq.inv.app (εT.obj M) ≫ trpq.hom.app (εT.obj M) ≫ (eqToIso eT).hom.app (εT.obj M) ≫
          trrs.inv.app (εT.obj M) ≫ cTrs.hom.app (εT.obj M)) ≫
        Ltr.map (cs.inv.app M ≫ ρs.hom.app M ≫ cs'.hom.app M) ≫
        (cr.inv.app (zts.obj M) ≫ ρr.hom.app (zts.obj M) ≫ cr'.hom.app (zts.obj M)) := by
  have h := conjugatedSquare_cube' πp πq πr πs ζp ζq ζr ζs τp τq τr τs (Z₁ ≫ Z₂ ≫ Z₃)
    (mpq.hom ≫ eqToHom eM ≫ mrs.inv) (cTpq.inv ≫ trpq.hom ≫ eqToHom eT ≫ trrs.inv ≫ cTrs.hom)
    (fun N => cp.inv.app N ≫ ρp.hom.app N ≫ cp'.hom.app N)
    (fun N => cq.inv.app N ≫ ρq.hom.app N ≫ cq'.hom.app N)
    (fun N => cr.inv.app N ≫ ρr.hom.app N ≫ cr'.hom.app N)
    (fun N => cs.inv.app N ≫ ρs.hom.app N ≫ cs'.hom.app N)
    (conjugatedSquare_hom_app_of_eq hρp) (conjugatedSquare_hom_app_of_eq hρq)
    (conjugatedSquare_hom_app_of_eq hρr) (conjugatedSquare_hom_app_of_eq hρs) M hcube
    (comparison_cube πp πq πr πs πpq πrs cTpq cTrs trpq trrs mpq mrs eM eT lpq lrs ht (εT.obj M))
  simp only [NatTrans.comp_app, eqToIso.hom, Category.assoc] at h ⊢
  exact h

end Stacks.CategoryTheory.SquareComposition
