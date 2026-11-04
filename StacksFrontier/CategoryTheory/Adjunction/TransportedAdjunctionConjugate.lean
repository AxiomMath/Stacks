module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Equivalence

/-!
# Comparisons of adjoints transported along equivalences in the two directions

Let `a : L ⊣ R` and `b : L' ⊣ R'` be adjunctions, related by equivalences `E_Y`, `E_X` (with
functors `Θ` and inverses `Ψ`). A comparison of right adjoints in the direction of `Ψ`,
`PC : R ⋙ Ψ ≅ Ψ ⋙ R'`, determines one in the direction of `Θ`, and likewise for left adjoints.
This file records that the comparisons read off in the two directions are conjugate:

* `Stacks.CategoryTheory.TransportedAdjunction.leftAdjointUniq_hom_app_of_unit`: the uniqueness of
  left adjoints `L ≅ Ψ ⋙ L' ⋙ Θ` is the conjugate of a comparison `Ψ ⋙ L' ≅ L ⋙ Ψ` compatible with
  the units;
* `Stacks.CategoryTheory.TransportedAdjunction.conj_baseChange`: an identity between base change
  maps, written through comparisons in the direction of `Ψ`, holds through their conjugates in the
  direction of `Θ`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.TransportedAdjunction

section LeftAdjoint

variable {𝒜 𝒜' ℬ ℬ' : Type*} [Category* 𝒜] [Category* 𝒜'] [Category* ℬ] [Category* ℬ']
  (EY : 𝒜 ≌ 𝒜') (EX : ℬ ≌ ℬ') {L : 𝒜' ⥤ ℬ'} {R : ℬ' ⥤ 𝒜'} (a : L ⊣ R)
  {L' : 𝒜 ⥤ ℬ} {R' : ℬ ⥤ 𝒜} (b : L' ⊣ R')
  (PC : R ⋙ EY.inverse ≅ EX.inverse ⋙ R') (PMI : R ≅ EX.inverse ⋙ R' ⋙ EY.functor)
  (Pc : EY.inverse ⋙ L' ≅ L ⋙ EX.inverse)

/-- **The uniqueness of left adjoints `L ≅ Ψ ⋙ L' ⋙ Θ`, against the transport of `b` along the
identification `PMI` of right adjoints, is the conjugate of a comparison `Pc : Ψ ⋙ L' ≅ L ⋙ Ψ`**,
as soon as `PMI` is the conjugate of a comparison `PC : R ⋙ Ψ ≅ Ψ ⋙ R'` and `Pc` is compatible with
the units through `PC`. -/
theorem leftAdjointUniq_hom_app_of_unit
    (hPMI : ∀ J, PMI.hom.app J = EY.counitIso.inv.app (R.obj J) ≫ EY.functor.map (PC.hom.app J))
    (hPc : ∀ K, b.unit.app (EY.inverse.obj K) ≫ R'.map (Pc.hom.app K) =
      EY.inverse.map (a.unit.app K) ≫ PC.hom.app (L.obj K)) (I : 𝒜') :
    (a.leftAdjointUniq ((EY.symm.toAdjunction.comp (b.comp EX.toAdjunction)).ofNatIsoRight
      PMI.symm)).hom.app I =
      EX.counitIso.inv.app (L.obj I) ≫ EX.functor.map (Pc.inv.app I) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_leftAdjointUniq_hom_app]
  have hPMI' : ∀ J, PMI.inv.app J =
      EY.functor.map (PC.inv.app J) ≫ EY.counitIso.hom.app (R.obj J) := by
    intro J
    rw [← cancel_epi (PMI.hom.app J), Iso.hom_inv_id_app, hPMI, Category.assoc,
      ← EY.functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  simp only [Equivalence.symm_functor, Functor.comp_obj, Equivalence.symm_inverse,
    Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app, Functor.id_obj,
    Adjunction.comp_unit_app, Equivalence.toAdjunction_unit, Equivalence.symm_unit,
    Functor.map_comp, Functor.whiskerLeft_app, hPMI', Category.assoc]
  have hPc' : b.unit.app (EY.inverse.obj I) = EY.inverse.map (a.unit.app I) ≫
      PC.hom.app (L.obj I) ≫ R'.map (Pc.inv.app I) := by
    rw [← reassoc_of% (hPc I), ← R'.map_comp, Iso.hom_inv_id_app]
    simp
  have n1 := EX.unit.naturality (Pc.inv.app I)
  have n2 := PC.hom.naturality (EX.counitInv.app (L.obj I) ≫ EX.functor.map (Pc.inv.app I))
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1 n2
  have hK : PC.hom.app (L.obj I) ≫ R'.map (Pc.inv.app I) ≫
      R'.map (EX.unit.app (L'.obj (EY.inverse.obj I))) ≫
      PC.inv.app (EX.functor.obj (L'.obj (EY.inverse.obj I))) =
      EY.inverse.map (R.map (EX.counitInv.app (L.obj I)) ≫
        R.map (EX.functor.map (Pc.inv.app I))) := by
    rw [← R'.map_comp_assoc, n1, Equivalence.unit_app_inverse, ← Functor.map_comp,
      ← reassoc_of% n2, Iso.hom_inv_id_app]
    simp
  have hK' := congrArg EY.functor.map hK
  simp only [Functor.map_comp] at hK'
  rw [hPc']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hK']
  have n3 := EY.counitIso.hom.naturality
    (a.unit.app I ≫ R.map (EX.counitInv.app (L.obj I)) ≫ R.map (EX.functor.map (Pc.inv.app I)))
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc, Functor.comp_obj,
    Functor.id_obj] at n3
  rw [n3]
  simp

end LeftAdjoint

section BaseChange

variable {VX VY VX' VY' RX RY RX' RY' : Type*} [Category* VX] [Category* VY] [Category* VX']
  [Category* VY'] [Category* RX] [Category* RY] [Category* RX'] [Category* RY']
  (EX : VX ≌ RX) (EY : VY ≌ RY) (EX' : VX' ≌ RX') (EY' : VY' ≌ RY')
  {fs : VX ⥤ VY} {gi : VY ⥤ VY'} {g'i : VX ⥤ VX'} {f's : VX' ⥤ VY'}
  {fr : RX ⥤ RY} {gp : RY ⥤ RY'} {g'p : RX ⥤ RX'} {f'r : RX' ⥤ RY'}
  (PCf : fr ⋙ EY.inverse ≅ EX.inverse ⋙ fs) (PCf' : f'r ⋙ EY'.inverse ≅ EX'.inverse ⋙ f's)
  (Pcg : EY.inverse ⋙ gi ≅ gp ⋙ EY'.inverse) (Pcg' : EX.inverse ⋙ g'i ≅ g'p ⋙ EX'.inverse)
  (bc : fs ⋙ gi ⟶ g'i ⋙ f's) (mbc : fr ⋙ gp ⟶ g'p ⋙ f'r)

/-- **A base change identity through comparisons in the direction of `Ψ` holds through their
conjugates in the direction of `Θ`.** If `Ψ` carries `mbc` to `bc` through the comparisons `PC` of
direct images and `Pc` of inverse images, then `Θ` carries `bc` to `mbc` through the conjugate
comparisons, written out here. -/
theorem conj_baseChange
    (hΨ : ∀ I, gi.map (PCf.hom.app I) ≫ bc.app (EX.inverse.obj I) ≫ f's.map (Pcg'.hom.app I) =
      Pcg.hom.app (fr.obj I) ≫ EY'.inverse.map (mbc.app I) ≫ PCf'.hom.app (g'p.obj I)) (M : VX) :
    (EY'.counitIso.inv.app (gp.obj (EY.functor.obj (fs.obj M))) ≫
        EY'.functor.map (Pcg.inv.app (EY.functor.obj (fs.obj M))) ≫
        EY'.functor.map (gi.map (EY.unitIso.inv.app (fs.obj M)))) ≫
      EY'.functor.map (bc.app M) ≫
      (EY'.functor.map (f's.map (EX'.unitIso.hom.app (g'i.obj M))) ≫
        EY'.functor.map (PCf'.inv.app (EX'.functor.obj (g'i.obj M))) ≫
        EY'.counitIso.hom.app (f'r.obj (EX'.functor.obj (g'i.obj M)))) =
    gp.map (EY.functor.map (fs.map (EX.unitIso.hom.app M)) ≫
        EY.functor.map (PCf.inv.app (EX.functor.obj M)) ≫
        EY.counitIso.hom.app (fr.obj (EX.functor.obj M))) ≫
      mbc.app (EX.functor.obj M) ≫
      f'r.map (EX'.counitIso.inv.app (g'p.obj (EX.functor.obj M)) ≫
        EX'.functor.map (Pcg'.inv.app (EX.functor.obj M)) ≫
        EX'.functor.map (g'i.map (EX.unitIso.inv.app M))) := by
  have hbc : bc.app M = gi.map (fs.map (EX.unitIso.hom.app M)) ≫ bc.app (EX.inverse.obj
      (EX.functor.obj M)) ≫ f's.map (g'i.map (EX.unitIso.inv.app M)) := by
    have h := bc.naturality (EX.unitIso.hom.app M)
    simp only [Functor.comp_map] at h
    rw [reassoc_of% h, ← f's.map_comp, ← g'i.map_comp, Iso.hom_inv_id_app]
    simp
  have hΨ' : bc.app (EX.inverse.obj (EX.functor.obj M)) =
      gi.map (PCf.inv.app (EX.functor.obj M)) ≫ Pcg.hom.app (fr.obj (EX.functor.obj M)) ≫
        EY'.inverse.map (mbc.app (EX.functor.obj M)) ≫
        PCf'.hom.app (g'p.obj (EX.functor.obj M)) ≫ f's.map (Pcg'.inv.app (EX.functor.obj M)) := by
    rw [← reassoc_of% (hΨ (EX.functor.obj M)), ← gi.map_comp_assoc, ← f's.map_comp,
      Iso.hom_inv_id_app]
    simp
  have L₁ : EY.unitIso.inv.app (fs.obj M) ≫ fs.map (EX.unitIso.hom.app M) ≫
      PCf.inv.app (EX.functor.obj M) =
        EY.inverse.map (EY.functor.map (fs.map (EX.unitIso.hom.app M)) ≫
          EY.functor.map (PCf.inv.app (EX.functor.obj M)) ≫
          EY.counitIso.hom.app (fr.obj (EX.functor.obj M))) := by
    simp
  have L₄ : ∀ (z : EX'.inverse.obj (g'p.obj (EX.functor.obj M)) ⟶ g'i.obj M),
      EY'.counitIso.inv.app (f'r.obj (g'p.obj (EX.functor.obj M))) ≫
        EY'.functor.map (PCf'.hom.app (g'p.obj (EX.functor.obj M))) ≫
        EY'.functor.map (f's.map z) ≫
        EY'.functor.map (f's.map (EX'.unitIso.hom.app (g'i.obj M))) ≫
        EY'.functor.map (PCf'.inv.app (EX'.functor.obj (g'i.obj M))) ≫
        EY'.counitIso.hom.app (f'r.obj (EX'.functor.obj (g'i.obj M))) =
      f'r.map (EX'.counitIso.inv.app (g'p.obj (EX.functor.obj M)) ≫ EX'.functor.map z) := by
    intro z
    have n1 := EX'.unitIso.hom.naturality z
    have n2 := PCf'.inv.naturality (EX'.counitIso.inv.app (g'p.obj (EX.functor.obj M)) ≫
      EX'.functor.map z)
    have n3 := EY'.counitIso.hom.naturality (f'r.map (EX'.counitIso.inv.app
      (g'p.obj (EX.functor.obj M)) ≫ EX'.functor.map z))
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n1 n2 n3
    have t : EX'.unitIso.hom.app (EX'.inverse.obj (g'p.obj (EX.functor.obj M))) =
        EX'.inverse.map (EX'.counitIso.inv.app (g'p.obj (EX.functor.obj M))) :=
      EX'.unit_app_inverse _
    rw [← EY'.functor.map_comp_assoc (f's.map z), ← f's.map_comp, n1, t, ← Functor.map_comp,
      ← EY'.functor.map_comp_assoc (f's.map _), n2]
    simp only [Functor.map_comp, Category.assoc]
    rw [← EY'.functor.map_comp_assoc (PCf'.hom.app _), Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp,
      ← EY'.functor.map_comp_assoc (EY'.inverse.map _), ← EY'.inverse.map_comp, ← f'r.map_comp, n3]
    simp
  set x := EY.functor.map (fs.map (EX.unitIso.hom.app M)) ≫
    EY.functor.map (PCf.inv.app (EX.functor.obj M)) ≫
    EY.counitIso.hom.app (fr.obj (EX.functor.obj M)) with hx
  have L₁' := congrArg (fun z => EY'.functor.map (gi.map z)) L₁
  simp only [Functor.map_comp] at L₁'
  have L₂ : Pcg.inv.app (EY.functor.obj (fs.obj M)) ≫ gi.map (EY.inverse.map x) ≫
      Pcg.hom.app (fr.obj (EX.functor.obj M)) = EY'.inverse.map (gp.map x) :=
    NatIso.naturality_1 Pcg x
  have L₂' := congrArg EY'.functor.map L₂
  simp only [Functor.map_comp] at L₂'
  have n5 := EY'.counitIso.inv.naturality (gp.map x ≫ mbc.app (EX.functor.obj M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n5
  have L₄' := L₄ (Pcg'.inv.app (EX.functor.obj M) ≫ g'i.map (EX.unitIso.inv.app M))
  simp only [Functor.map_comp, Category.assoc] at L₄'
  rw [hbc, hΨ']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% L₁', reassoc_of% L₂', ← EY'.functor.map_comp_assoc (EY'.inverse.map (gp.map x)),
    ← EY'.inverse.map_comp, ← reassoc_of% n5, L₄']

end BaseChange

end Stacks.CategoryTheory.TransportedAdjunction
