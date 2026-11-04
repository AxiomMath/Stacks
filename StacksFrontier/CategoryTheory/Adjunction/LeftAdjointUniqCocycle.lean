module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates

/-!
# Comparisons of left adjoints and composition isomorphisms

Let `p_f ⊣ P_f`, `p_g ⊣ P_g`, `p_{gf} ⊣ P_{gf}`, `p_c ⊣ P_c` and `q_f ⊣ Q_f`, `q_g ⊣ Q_g`,
`q_{gf} ⊣ Q_{gf}` be adjunctions, with comparisons `τ : P ≅ Q` of right adjoints and composition
isomorphisms `t : P_{gf} ≅ P_c`, `c : P_c ≅ P_g ⋙ P_f` and `σ : Q_g ⋙ Q_f ≅ Q_{gf}`. If the
comparisons `τ` are compatible with the composition isomorphisms of the right adjoints, then the
comparisons of left adjoints they induce are compatible with the induced composition
isomorphisms of the left adjoints.

## Main results

* `Stacks.CategoryTheory.leftAdjointUniq_comp_cocycle`: the comparisons of left adjoints are
  compatible with the composition isomorphisms when the comparisons of right adjoints are.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {CX : Type u₁} [Category.{v₁} CX] {CY : Type u₂} [Category.{v₂} CY]
  {CZ : Type u₃} [Category.{v₃} CZ]

/-- **Comparisons of left adjoints are compatible with composition when the comparisons of
right adjoints are.** The comparisons are `CategoryTheory.Adjunction.leftAdjointUniq` of the
adjunctions transported along `τ`; the composition isomorphisms of left adjoints are the
`leftAdjointUniq` comparisons induced by `t` and `c`, and the
`CategoryTheory.Adjunction.leftAdjointCompIso` of `σ`. -/
theorem leftAdjointUniq_comp_cocycle
    {pf qf : CX ⥤ CY} {pg qg : CY ⥤ CZ} {pgf qgf pc : CX ⥤ CZ}
    {Pf Qf : CY ⥤ CX} {Pg Qg : CZ ⥤ CY} {Pgf Qgf Pc : CZ ⥤ CX}
    (af : pf ⊣ Pf) (ag : pg ⊣ Pg) (agf : pgf ⊣ Pgf) (ac : pc ⊣ Pc)
    (bf : qf ⊣ Qf) (bg : qg ⊣ Qg) (bgf : qgf ⊣ Qgf)
    (τf : Pf ≅ Qf) (τg : Pg ≅ Qg) (τgf : Pgf ≅ Qgf)
    (c : Pc ≅ Pg ⋙ Pf) (t : Pgf ≅ Pc) (σ : Qg ⋙ Qf ≅ Qgf)
    (h : ∀ M, t.hom.app M ≫ c.hom.app M ≫ τf.hom.app (Pg.obj M) ≫ Qf.map (τg.hom.app M) =
      τgf.hom.app M ≫ σ.inv.app M) :
    ((Adjunction.leftAdjointUniq (ac.ofNatIsoRight c) (af.comp ag)).symm ≪≫
        (Adjunction.leftAdjointUniq (agf.ofNatIsoRight t) ac).symm).hom ≫
      (Adjunction.leftAdjointUniq (agf.ofNatIsoRight τgf) bgf).hom =
    Functor.whiskerRight (Adjunction.leftAdjointUniq (af.ofNatIsoRight τf) bf).hom pg ≫
      Functor.whiskerLeft qf (Adjunction.leftAdjointUniq (ag.ofNatIsoRight τg) bg).hom ≫
        (Adjunction.leftAdjointCompIso bf bg bgf σ).hom := by
  have hσ : conjugateEquiv bgf (bf.comp bg) (Adjunction.leftAdjointCompIso bf bg bgf σ).hom =
      σ.inv :=
    congrArg Iso.hom ((conjugateIsoEquiv bgf (bf.comp bg)).apply_symm_apply σ.symm)
  have hL : conjugateEquiv bgf (af.comp ag)
      (((Adjunction.leftAdjointUniq (ac.ofNatIsoRight c) (af.comp ag)).symm ≪≫
        (Adjunction.leftAdjointUniq (agf.ofNatIsoRight t) ac).symm).hom ≫
      (Adjunction.leftAdjointUniq (agf.ofNatIsoRight τgf) bgf).hom) =
        τgf.inv ≫ t.hom ≫ c.hom := by
    rw [← conjugateEquiv_comp bgf agf (af.comp ag), Iso.trans_hom, Iso.symm_hom, Iso.symm_hom,
      ← conjugateEquiv_comp agf ac (af.comp ag), leftAdjointUniq_inv, leftAdjointUniq_inv,
      conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
      conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom',
      conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom']
  have hR : conjugateEquiv bgf (af.comp ag)
      (Functor.whiskerRight (Adjunction.leftAdjointUniq (af.ofNatIsoRight τf) bf).hom pg ≫
        Functor.whiskerLeft qf (Adjunction.leftAdjointUniq (ag.ofNatIsoRight τg) bg).hom ≫
          (Adjunction.leftAdjointCompIso bf bg bgf σ).hom) =
        σ.inv ≫ Functor.whiskerRight τg.inv Qf ≫ Functor.whiskerLeft Pg τf.inv := by
    rw [← conjugateEquiv_comp bgf (bf.comp ag) (af.comp ag),
      ← conjugateEquiv_comp bgf (bf.comp bg) (bf.comp ag), hσ, conjugateEquiv_whiskerLeft,
      conjugateEquiv_whiskerRight, conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
      conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom, Category.assoc]
  apply (conjugateEquiv bgf (af.comp ag)).injective
  rw [hL, hR]
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj]
  rw [← cancel_epi (τgf.hom.app M), Iso.hom_inv_id_app_assoc, ← reassoc_of% (h M),
    ← Qf.map_comp_assoc, Iso.hom_inv_id_app, Qf.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id]

end Stacks.CategoryTheory

end
