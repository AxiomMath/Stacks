module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Comparisons of left adjoints along a change of the composition isomorphism

Let `G₁ ⊣ R_g`, `F₁ ⊣ R_f`, `H₁ ⊣ R_{gf}` and `H₂ ⊣ R₂` be adjunctions, with
`pc : R_{gf} ≅ R_f ⋙ R_g` and `pt : R_{gf} ≅ R₂`, and let `G₂ ⊣ S_g`, `F₂ ⊣ S_f`, `H₃ ⊣ S₃` be
adjunctions whose right adjoints are equal to `R_g`, `R_f`, `R₂`. The comparisons of left
adjoints induced by these data commute: comparing `G₁ ⋙ F₁` with `H₃` through `H₁` and `H₂` is
comparing it through `G₂ ⋙ F₂`. This is the shape of the compatibility of the pullbacks of
modules of the small étale ringed topoi of algebraic spaces with the pullbacks of Stacks 03LU
along a composite.

## Main results

* `Stacks.CategoryTheory.leftAdjointUniq_comp_change`.
* `Stacks.CategoryTheory.comp_trans_hom_eq_of_comp_hom_eq`: two such compatibilities compose.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {CX : Type u₁} [Category.{v₁} CX] {CY : Type u₂} [Category.{v₂} CY]
  {CZ : Type u₃} [Category.{v₃} CZ]

/-- **Comparisons of left adjoints along a change of the composition isomorphism.** All
comparisons are `CategoryTheory.Adjunction.leftAdjointUniq`; the proof compares conjugates. -/
theorem leftAdjointUniq_comp_change
    {G₁ G₂ : CZ ⥤ CY} {F₁ F₂ : CY ⥤ CX} {H₁ H₂ H₃ : CZ ⥤ CX}
    {Rf Sf : CX ⥤ CY} {Rg Sg : CY ⥤ CZ} {Rgf R₂ S₃ : CX ⥤ CZ}
    (aG : G₁ ⊣ Rg) (aF : F₁ ⊣ Rf) (aGF : H₁ ⊣ Rgf) (aT : H₂ ⊣ R₂)
    (mG : G₂ ⊣ Sg) (mF : F₂ ⊣ Sf) (mFG : H₃ ⊣ S₃)
    (pc : Rgf ≅ Rf ⋙ Rg) (pt : Rgf ≅ R₂)
    (hF : Rf = Sf) (hG : Rg = Sg) (h₃ : R₂ = S₃) (hc : Sf ⋙ Sg = Rf ⋙ Rg) :
    (Adjunction.leftAdjointUniq (aGF.ofNatIsoRight pc) (aG.comp aF)).inv ≫
        (Adjunction.leftAdjointUniq aGF (aT.ofNatIsoRight pt.symm)).hom ≫
          (Adjunction.leftAdjointUniq aT (mFG.ofNatIsoRight (eqToIso h₃).symm)).hom =
      Functor.whiskerRight
          (Adjunction.leftAdjointUniq aG (mG.ofNatIsoRight (eqToIso hG).symm)).hom F₁ ≫
        Functor.whiskerLeft G₂
          (Adjunction.leftAdjointUniq aF (mF.ofNatIsoRight (eqToIso hF).symm)).hom ≫
          (Adjunction.leftAdjointUniq ((mG.comp mF).ofNatIsoRight
            (eqToIso hc ≪≫ pc.symm ≪≫ pt ≪≫ eqToIso h₃)) mFG).hom := by
  subst hF hG h₃
  simp only [eqToIso_refl, Iso.refl_symm, Adjunction.ofNatIsoRight_refl, Iso.refl_trans]
  apply (conjugateEquiv mFG (aG.comp aF)).injective
  rw [← conjugateEquiv_comp mFG aGF (aG.comp aF), ← conjugateEquiv_comp mFG aT aGF,
    ← conjugateEquiv_comp mFG (mG.comp aF) (aG.comp aF),
    ← conjugateEquiv_comp mFG (mG.comp mF) (mG.comp aF),
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]
  simp only [conjugateEquiv_leftAdjointUniq_hom, leftAdjointUniq_inv,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom']
  simp

/-- **Two compatibilities of composition isomorphisms compose.** If `pᵢ` carry the composite
`x` to `m` and `qᵢ` carry `m` to `e`, then the `pᵢ ≪≫ qᵢ` carry `x` to `e`. -/
theorem comp_trans_hom_eq_of_comp_hom_eq {Tg Mg Eg : CX ⥤ CY} {Th Mh Eh : CY ⥤ CZ}
    {Thg Mhg Ehg : CX ⥤ CZ} (pg : Tg ≅ Mg) (qg : Mg ≅ Eg) (ph : Th ≅ Mh) (qh : Mh ≅ Eh)
    (phg : Thg ≅ Mhg) (qhg : Mhg ≅ Ehg) (x : Tg ⋙ Th ⟶ Thg) (m : Mg ⋙ Mh ⟶ Mhg)
    (e : Eg ⋙ Eh ⟶ Ehg)
    (hp : x ≫ phg.hom = Functor.whiskerRight pg.hom Th ≫ Functor.whiskerLeft Mg ph.hom ≫ m)
    (hq : m ≫ qhg.hom = Functor.whiskerLeft Mg qh.hom ≫ Functor.whiskerRight qg.hom Eh ≫ e) :
    x ≫ (phg ≪≫ qhg).hom =
      Functor.whiskerRight (pg ≪≫ qg).hom Th ≫ Functor.whiskerLeft Eg (ph ≪≫ qh).hom ≫ e := by
  ext M
  have hp' := NatTrans.congr_app hp M
  have hq' := NatTrans.congr_app hq M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at hp' hq'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc, reassoc_of% hp', hq']
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]

end Stacks.CategoryTheory

end
