module

public import StacksFrontier.CategoryTheory.Localization.ExactDerivedComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Transporting the underived compatibility of identifications with compositors

`CategoryTheory.Functor.UnderivedCompCoherence` is the compatibility of identifications
`u : εK ⋙ hK ≅ gK ⋙ εK'` of functors with compositors on both sides.  This file proves that it is
preserved by the constructions an identification is usually assembled from:

* conjugating a square `P ⋙ E'⁻¹ ≅ E⁻¹ ⋙ Q` by equivalences
  (`CategoryTheory.Functor.equivalenceConjSquare`);
* pasting two squares (`CategoryTheory.Functor.pastedUnderivedSquare`);
* changing the spelling of the functors by isomorphisms, in particular by `eqToIso`
  (`CategoryTheory.Functor.transferredUnderivedSquare`), and comparing comparisons of left
  adjoints (`CategoryTheory.Functor.leftAdjointUniq_compCoherence`);
* passing to the homotopy categories
  (`CategoryTheory.Functor.underivedCompCoherence_mapHomotopyCategory`).

Nothing here is registered.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

section Equivalence

variable {Y W Y' W' : Type*} [Category* Y] [Category* W] [Category* Y'] [Category* W']

/-- A square `P ⋙ E'⁻¹ ≅ E⁻¹ ⋙ Q` conjugated by the equivalences `E` and `E'`. -/
def equivalenceConjSquare (E : Y ≌ W) (E' : Y' ≌ W') {P : W ⥤ W'} {Q : Y ⥤ Y'}
    (e : P ⋙ E'.inverse ≅ E.inverse ⋙ Q) : E.functor ⋙ P ≅ Q ⋙ E'.functor :=
  Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ E'.counitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ e) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight E.unitIso.symm _) _ ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor _) _

/-- The components of `CategoryTheory.Functor.equivalenceConjSquare`. -/
theorem equivalenceConjSquare_hom_app (E : Y ≌ W) (E' : Y' ≌ W') {P : W ⥤ W'} {Q : Y ⥤ Y'}
    (e : P ⋙ E'.inverse ≅ E.inverse ⋙ Q) (M : Y) :
    (equivalenceConjSquare E E' e).hom.app M =
      E'.counitInv.app (P.obj (E.functor.obj M)) ≫ E'.functor.map (e.hom.app (E.functor.obj M)) ≫
        E'.functor.map (Q.map (E.unitInv.app M)) := by
  simp [equivalenceConjSquare]

end Equivalence

section EquivalenceComp

variable {Y W Y' W' Y'' W'' : Type*} [Category* Y] [Category* W] [Category* Y'] [Category* W']
  [Category* Y''] [Category* W'']
  (E : Y ≌ W) (E' : Y' ≌ W') (E'' : Y'' ≌ W'')
  {Pg : W ⥤ W'} {Pf : W' ⥤ W''} {Pk : W ⥤ W''} {Qg : Y ⥤ Y'} {Qf : Y' ⥤ Y''} {Qk : Y ⥤ Y''}
  {eg : Pg ⋙ E'.inverse ≅ E.inverse ⋙ Qg} {ef : Pf ⋙ E''.inverse ≅ E'.inverse ⋙ Qf}
  {ek : Pk ⋙ E''.inverse ≅ E.inverse ⋙ Qk} {cP : Pg ⋙ Pf ≅ Pk} {cQ : Qg ⋙ Qf ≅ Qk}

/-- Conjugating by equivalences preserves the pasting coherence of squares. -/
theorem underivedCompCoherence_equivalenceConjSquare
    (h : Functor.isoWhiskerLeft Pg ef ≪≫ Functor.isoWhiskerRight eg Qf ≪≫
        Functor.isoWhiskerLeft E.inverse cQ = Functor.isoWhiskerRight cP E''.inverse ≪≫ ek) :
    UnderivedCompCoherence (equivalenceConjSquare E E' eg) (equivalenceConjSquare E' E'' ef)
      (equivalenceConjSquare E E'' ek) cQ.hom cP.hom := by
  have hc : ∀ N : W, ef.hom.app (Pg.obj N) ≫ Qf.map (eg.hom.app N) ≫ cQ.hom.app (E.inverse.obj N) =
      E''.inverse.map (cP.hom.app N) ≫ ek.hom.app N := fun N => by
    simpa using congrArg (fun i => i.hom.app N) h
  intro M
  have L3 := cQ.hom.naturality (E.unitInv.app M)
  simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at L3
  set N := E.functor.obj M
  set x := eg.hom.app N ≫ Qg.map (E.unitInv.app M)
  -- the natural map `Pf(E'(Z)) ⟶ E''(Qf Z)`
  have nat : ∀ {Z Z' : Y'} (z : Z ⟶ Z'), Pf.map (E'.functor.map z) ≫
      E''.counitInv.app (Pf.obj (E'.functor.obj Z')) ≫
        E''.functor.map (ef.hom.app (E'.functor.obj Z')) ≫
        E''.functor.map (Qf.map (E'.unitInv.app Z')) =
      E''.counitInv.app (Pf.obj (E'.functor.obj Z)) ≫
        E''.functor.map (ef.hom.app (E'.functor.obj Z)) ≫
        E''.functor.map (Qf.map (E'.unitInv.app Z)) ≫ E''.functor.map (Qf.map z) := by
    intro Z Z' z
    have n1 := E''.counitInv.naturality (Pf.map (E'.functor.map z))
    have n2 := ef.hom.naturality (E'.functor.map z)
    have n3 := E'.unitInv.naturality z
    simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1 n2 n3
    rw [reassoc_of% n1, ← E''.functor.map_comp_assoc, n2, Functor.map_comp_assoc,
      ← E''.functor.map_comp, ← Qf.map_comp, n3]
    simp only [Functor.map_comp]
  -- the triangle at `Pg N`
  have tri : Pf.map (E'.counitInv.app (Pg.obj N)) ≫
      E''.counitInv.app (Pf.obj (E'.functor.obj (E'.inverse.obj (Pg.obj N)))) ≫
        E''.functor.map (ef.hom.app (E'.functor.obj (E'.inverse.obj (Pg.obj N)))) ≫
          E''.functor.map (Qf.map (E'.unitInv.app (E'.inverse.obj (Pg.obj N)))) =
      E''.counitInv.app (Pf.obj (Pg.obj N)) ≫ E''.functor.map (ef.hom.app (Pg.obj N)) := by
    have n1 := E''.counitInv.naturality (Pf.map (E'.counitInv.app (Pg.obj N)))
    have n2 := ef.hom.naturality (E'.counitInv.app (Pg.obj N))
    have t := E'.inverse_counitInv_comp (Pg.obj N)
    simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1 n2
    rw [reassoc_of% n1, ← E''.functor.map_comp_assoc, n2, Functor.map_comp_assoc,
      ← E''.functor.map_comp, ← Qf.map_comp, t, Qf.map_id, E''.functor.map_id, Category.comp_id]
  have L1 := E''.counitInv.naturality (cP.hom.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at L1
  simp only [equivalenceConjSquare_hom_app]
  calc cP.hom.app N ≫ E''.counitInv.app (Pk.obj N) ≫ E''.functor.map (ek.hom.app N) ≫
        E''.functor.map (Qk.map (E.unitInv.app M))
      = E''.counitInv.app (Pf.obj (Pg.obj N)) ≫
          E''.functor.map (ef.hom.app (Pg.obj N) ≫ Qf.map x ≫ cQ.hom.app M) := by
        rw [reassoc_of% L1, ← E''.functor.map_comp_assoc, ← hc, ← E''.functor.map_comp]
        simp only [x, Functor.map_comp, Category.assoc, L3]
        rfl
    _ = Pf.map (E'.counitInv.app (Pg.obj N)) ≫ (Pf.map (E'.functor.map x) ≫
          E''.counitInv.app (Pf.obj (E'.functor.obj (Qg.obj M))) ≫
          E''.functor.map (ef.hom.app (E'.functor.obj (Qg.obj M))) ≫
          E''.functor.map (Qf.map (E'.unitInv.app (Qg.obj M)))) ≫
          E''.functor.map (cQ.hom.app M) := by
        rw [nat (Z' := Qg.obj M) x]
        simp only [Category.assoc, Functor.comp_obj]
        rw [reassoc_of% tri]
        simp only [Functor.map_comp]
    _ = _ := by
        simp only [x, Functor.map_comp, Category.assoc]
        rfl

end EquivalenceComp


section Paste

variable {Z Y W Z' Y' W' : Type*} [Category* Z] [Category* Y] [Category* W] [Category* Z']
  [Category* Y'] [Category* W']

/-- The pasting of a square `Φ ⋙ P ≅ Q ⋙ Φ'` with a square `R ⋙ A' ≅ A ⋙ Q`. -/
def pastedUnderivedSquare {A : Z ⥤ Y} {A' : Z' ⥤ Y'} {Φ : Y ⥤ W} {Φ' : Y' ⥤ W'} {R : Z ⥤ Z'}
    {Q : Y ⥤ Y'} {P : W ⥤ W'} (sq : Φ ⋙ P ≅ Q ⋙ Φ') (bc : R ⋙ A' ≅ A ⋙ Q) :
    (A ⋙ Φ) ⋙ P ≅ R ⋙ (A' ⋙ Φ') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ sq ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight bc.symm _ ≪≫ Functor.associator _ _ _

/-- The components of `CategoryTheory.Functor.pastedUnderivedSquare`. -/
theorem pastedUnderivedSquare_hom_app {A : Z ⥤ Y} {A' : Z' ⥤ Y'} {Φ : Y ⥤ W} {Φ' : Y' ⥤ W'}
    {R : Z ⥤ Z'} {Q : Y ⥤ Y'} {P : W ⥤ W'} (sq : Φ ⋙ P ≅ Q ⋙ Φ') (bc : R ⋙ A' ≅ A ⋙ Q) (M : Z) :
    (pastedUnderivedSquare sq bc).hom.app M = sq.hom.app (A.obj M) ≫ Φ'.map (bc.inv.app M) := by
  simp [pastedUnderivedSquare]

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- A square `ε ⋙ P ≅ R ⋙ ε'` read through isomorphisms `p ≅ P` and `R ≅ r`. -/
def transferredUnderivedSquare {ε : C ⥤ D} {ε' : C' ⥤ D'} {p P : D ⥤ D'} {R r : C ⥤ C'}
    (i : p ≅ P) (F : ε ⋙ P ≅ R ⋙ ε') (j : R ≅ r) : ε ⋙ p ≅ r ⋙ ε' :=
  Functor.isoWhiskerLeft ε i ≪≫ F ≪≫ Functor.isoWhiskerRight j ε'

/-- The components of `CategoryTheory.Functor.transferredUnderivedSquare`. -/
theorem transferredUnderivedSquare_hom_app {ε : C ⥤ D} {ε' : C' ⥤ D'} {p P : D ⥤ D'}
    {R r : C ⥤ C'} (i : p ≅ P) (F : ε ⋙ P ≅ R ⋙ ε') (j : R ≅ r) (M : C) :
    (transferredUnderivedSquare i F j).hom.app M =
      i.hom.app (ε.obj M) ≫ F.hom.app M ≫ ε'.map (j.hom.app M) := by
  simp [transferredUnderivedSquare]

end Paste

section PasteComp

variable {Z Y W Z' Y' W' Z'' Y'' W'' : Type*} [Category* Z] [Category* Y] [Category* W]
  [Category* Z'] [Category* Y'] [Category* W'] [Category* Z''] [Category* Y''] [Category* W'']
  {A : Z ⥤ Y} {A' : Z' ⥤ Y'} {A'' : Z'' ⥤ Y''} {Φ : Y ⥤ W} {Φ' : Y' ⥤ W'} {Φ'' : Y'' ⥤ W''}
  {Rg : Z ⥤ Z'} {Rf : Z' ⥤ Z''} {Rk : Z ⥤ Z''} {Qg : Y ⥤ Y'} {Qf : Y' ⥤ Y''} {Qk : Y ⥤ Y''}
  {Pg : W ⥤ W'} {Pf : W' ⥤ W''} {Pk : W ⥤ W''}
  {sqg : Φ ⋙ Pg ≅ Qg ⋙ Φ'} {sqf : Φ' ⋙ Pf ≅ Qf ⋙ Φ''} {sqk : Φ ⋙ Pk ≅ Qk ⋙ Φ''}
  {bcg : Rg ⋙ A' ≅ A ⋙ Qg} {bcf : Rf ⋙ A'' ≅ A' ⋙ Qf} {bck : Rk ⋙ A'' ≅ A ⋙ Qk}
  {cR : Rg ⋙ Rf ⟶ Rk} {cQ : Qg ⋙ Qf ⟶ Qk} {cP : Pg ⋙ Pf ⟶ Pk}

/-- Pasting preserves the compatibility with the compositors. -/
theorem underivedCompCoherence_pastedUnderivedSquare
    (hsq : UnderivedCompCoherence sqg sqf sqk cQ cP)
    (hbc : ∀ M : Z, bcf.hom.app (Rg.obj M) ≫ Qf.map (bcg.hom.app M) ≫ cQ.app (A.obj M) =
      A''.map (cR.app M) ≫ bck.hom.app M) :
    UnderivedCompCoherence (pastedUnderivedSquare sqg bcg) (pastedUnderivedSquare sqf bcf)
      (pastedUnderivedSquare sqk bck) cR cP := by
  intro M
  have hbc' : cQ.app (A.obj M) ≫ bck.inv.app M =
      Qf.map (bcg.inv.app M) ≫ bcf.inv.app (Rg.obj M) ≫ A''.map (cR.app M) := by
    rw [← cancel_epi (bcf.hom.app (Rg.obj M) ≫ Qf.map (bcg.hom.app M))]
    simp only [Category.assoc]
    rw [reassoc_of% (hbc M)]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc, Category.comp_id]
  have nsq := sqf.hom.naturality (bcg.inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at nsq
  simp only [pastedUnderivedSquare_hom_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% (hsq (A.obj M)), ← Functor.map_comp_assoc, ← Functor.map_comp, hbc']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nsq]

end PasteComp

section TransferComp

variable {C D C' D' C'' D'' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* C''] [Category* D'']
  {ε : C ⥤ D} {ε' : C' ⥤ D'} {ε'' : C'' ⥤ D''}
  {pg Pg : D ⥤ D'} {pf Pf : D' ⥤ D''} {pk Pk : D ⥤ D''}
  {Rg rg : C ⥤ C'} {Rf rf : C' ⥤ C''} {Rk rk : C ⥤ C''}
  {ig : pg ≅ Pg} {if' : pf ≅ Pf} {ik : pk ≅ Pk} {jg : Rg ≅ rg} {jf : Rf ≅ rf} {jk : Rk ≅ rk}
  {Fg : ε ⋙ Pg ≅ Rg ⋙ ε'} {Ff : ε' ⋙ Pf ≅ Rf ⋙ ε''} {Fk : ε ⋙ Pk ≅ Rk ⋙ ε''}
  {cR : Rg ⋙ Rf ⟶ Rk} {cP : Pg ⋙ Pf ⟶ Pk} {cA : rg ⋙ rf ⟶ rk} {cE : pg ⋙ pf ⟶ pk}

/-- Changing the spelling of the functors preserves the compatibility with the compositors, as
soon as the compositors correspond. -/
theorem underivedCompCoherence_transferredUnderivedSquare
    (hF : UnderivedCompCoherence Fg Ff Fk cR cP)
    (hi : ∀ N : D, cE.app N ≫ ik.hom.app N =
      pf.map (ig.hom.app N) ≫ if'.hom.app (Pg.obj N) ≫ cP.app N)
    (hj : ∀ M : C, cR.app M ≫ jk.hom.app M =
      jf.hom.app (Rg.obj M) ≫ rf.map (jg.hom.app M) ≫ cA.app M) :
    UnderivedCompCoherence (transferredUnderivedSquare ig Fg jg)
      (transferredUnderivedSquare if' Ff jf) (transferredUnderivedSquare ik Fk jk) cA cE := by
  intro M
  have ni := if'.hom.naturality (Fg.hom.app M ≫ ε'.map (jg.hom.app M))
  have nF := Ff.hom.naturality (jg.hom.app M)
  have nj := jf.hom.naturality (jg.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at ni nF nj
  simp only [transferredUnderivedSquare_hom_app, Functor.map_comp, Category.assoc]
  have ni' : pf.map (Fg.hom.app M) ≫ pf.map (ε'.map (jg.hom.app M)) ≫
      if'.hom.app (ε'.obj (rg.obj M)) =
      if'.hom.app (Pg.obj (ε.obj M)) ≫ Pf.map (Fg.hom.app M) ≫ Pf.map (ε'.map (jg.hom.app M)) := by
    simpa only [Functor.map_comp, Category.assoc] using ni
  rw [reassoc_of% (hi (ε.obj M)), reassoc_of% (hF M), ← Functor.map_comp, hj M]
  simp only [Functor.map_comp]
  have nj' := congrArg ε''.map nj
  simp only [Functor.map_comp] at nj'
  rw [reassoc_of% ni', reassoc_of% nF, reassoc_of% nj']

end TransferComp

section Homotopy

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']

/-- An identification of additive functors, read on homotopy categories, at the image of a
complex. -/
theorem mapHomotopyCategoryUnderivedIso_hom_app_quotient {ε : C ⥤ D} {ε' : C' ⥤ D'}
    {p : D ⥤ D'} {r : C ⥤ C'} [ε.Additive] [ε'.Additive] [p.Additive] [r.Additive]
    (u : ε ⋙ p ≅ r ⋙ ε') (c : ComplexShape ℤ) (K : HomologicalComplex C c) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (ε ⋙ p)) c ≪≫
        Stacks.Homology.mapHomotopyCategoryIso u c ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ ε')) c).symm).hom.app
          ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient D' c).map ((NatTrans.mapHomologicalComplex u.hom c).app K) := by
  show (HomotopyCategory.quotient D' c).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (ε ⋙ p)) c).hom.app K) ≫
    (HomotopyCategory.quotient D' c).map ((NatTrans.mapHomologicalComplex u.hom c).app K) ≫
    (HomotopyCategory.quotient D' c).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (r ⋙ ε')) c).inv.app K) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext i
  simp

end Homotopy

section HomotopyComp

variable {C₁ C₂ C₁' C₂' C₁'' C₂'' : Type*} [Category* C₁] [Category* C₂] [Category* C₁']
  [Category* C₂'] [Category* C₁''] [Category* C₂''] [Preadditive C₁] [Preadditive C₂]
  [Preadditive C₁'] [Preadditive C₂'] [Preadditive C₁''] [Preadditive C₂'']
  {ε : C₁ ⥤ C₂} {ε' : C₁' ⥤ C₂'} {ε'' : C₁'' ⥤ C₂''} [ε.Additive] [ε'.Additive] [ε''.Additive]
  {pg : C₂ ⥤ C₂'} {pf : C₂' ⥤ C₂''} {pk : C₂ ⥤ C₂''} [pg.Additive] [pf.Additive] [pk.Additive]
  {rg : C₁ ⥤ C₁'} {rf : C₁' ⥤ C₁''} {rk : C₁ ⥤ C₁''} [rg.Additive] [rf.Additive] [rk.Additive]
  {ug : ε ⋙ pg ≅ rg ⋙ ε'} {uf : ε' ⋙ pf ≅ rf ⋙ ε''} {uk : ε ⋙ pk ≅ rk ⋙ ε''}
  {cA : rg ⋙ rf ⟶ rk} {cE : pg ⋙ pf ⟶ pk} {c : ComplexShape ℤ}
  {ugH : ε.mapHomotopyCategory c ⋙ pg.mapHomotopyCategory c ≅
    rg.mapHomotopyCategory c ⋙ ε'.mapHomotopyCategory c}
  {ufH : ε'.mapHomotopyCategory c ⋙ pf.mapHomotopyCategory c ≅
    rf.mapHomotopyCategory c ⋙ ε''.mapHomotopyCategory c}
  {ukH : ε.mapHomotopyCategory c ⋙ pk.mapHomotopyCategory c ≅
    rk.mapHomotopyCategory c ⋙ ε''.mapHomotopyCategory c}
  {cAH : rg.mapHomotopyCategory c ⋙ rf.mapHomotopyCategory c ⟶ rk.mapHomotopyCategory c}
  {cEH : pg.mapHomotopyCategory c ⋙ pf.mapHomotopyCategory c ⟶ pk.mapHomotopyCategory c}

/-- **The compatibility with the compositors passes to the homotopy categories**, given the
quotient formulas of the identifications and of the compositors there. -/
theorem underivedCompCoherence_mapHomotopyCategory
    (hug : ∀ K : HomologicalComplex C₁ c, ugH.hom.app ((HomotopyCategory.quotient C₁ c).obj K) =
      (HomotopyCategory.quotient C₂' c).map ((NatTrans.mapHomologicalComplex ug.hom c).app K))
    (huf : ∀ K : HomologicalComplex C₁' c, ufH.hom.app ((HomotopyCategory.quotient C₁' c).obj K) =
      (HomotopyCategory.quotient C₂'' c).map ((NatTrans.mapHomologicalComplex uf.hom c).app K))
    (huk : ∀ K : HomologicalComplex C₁ c, ukH.hom.app ((HomotopyCategory.quotient C₁ c).obj K) =
      (HomotopyCategory.quotient C₂'' c).map ((NatTrans.mapHomologicalComplex uk.hom c).app K))
    (hcA : ∀ K : HomologicalComplex C₁ c, cAH.app ((HomotopyCategory.quotient C₁ c).obj K) =
      (HomotopyCategory.quotient C₁'' c).map ((NatTrans.mapHomologicalComplex cA c).app K))
    (hcE : ∀ K : HomologicalComplex C₂ c, cEH.app ((HomotopyCategory.quotient C₂ c).obj K) =
      (HomotopyCategory.quotient C₂'' c).map ((NatTrans.mapHomologicalComplex cE c).app K))
    (h : UnderivedCompCoherence ug uf uk cA cE) :
    UnderivedCompCoherence ugH ufH ukH cAH cEH := by
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have key : (NatTrans.mapHomologicalComplex cE c).app ((ε.mapHomologicalComplex c).obj K) ≫
      (NatTrans.mapHomologicalComplex uk.hom c).app K =
      (pf.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ug.hom c).app K) ≫
        (NatTrans.mapHomologicalComplex uf.hom c).app ((rg.mapHomologicalComplex c).obj K) ≫
        (ε''.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cA c).app K) := by
    ext i
    simpa using h (K.X i)
  have hcE' : cEH.app ((ε.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C₁ c).obj K)) =
      (HomotopyCategory.quotient C₂'' c).map
        ((NatTrans.mapHomologicalComplex cE c).app ((ε.mapHomologicalComplex c).obj K)) :=
    hcE _
  have huf' :
      ufH.hom.app ((rg.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C₁ c).obj K)) =
      (HomotopyCategory.quotient C₂'' c).map
        ((NatTrans.mapHomologicalComplex uf.hom c).app ((rg.mapHomologicalComplex c).obj K)) :=
    huf _
  rw [hcE', huk K, hug K, huf', hcA K]
  calc _ = (HomotopyCategory.quotient C₂'' c).map
        ((NatTrans.mapHomologicalComplex cE c).app ((ε.mapHomologicalComplex c).obj K) ≫
          (NatTrans.mapHomologicalComplex uk.hom c).app K) := (Functor.map_comp _ _ _).symm
    _ = (HomotopyCategory.quotient C₂'' c).map
        ((pf.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ug.hom c).app K) ≫
          (NatTrans.mapHomologicalComplex uf.hom c).app ((rg.mapHomologicalComplex c).obj K) ≫
          (ε''.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex cA c).app K)) := by
        rw [key]
    _ = _ := by
        rw [Functor.map_comp, Functor.map_comp]
        rfl

end HomotopyComp

section LeftAdjointUniq

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- The conjugate of the comparison of two left adjoints of one functor is the identity. -/
theorem conjugateEquiv_leftAdjointUniq_hom_self {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (adj' : L' ⊣ R) : conjugateEquiv adj' adj (Adjunction.leftAdjointUniq adj adj').hom = 𝟙 R := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun X ↦ (adj.homEquiv X _).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simp

/-- If the conjugate of `c.inv` is `e.hom`, then the conjugate of `c.hom` is `e.inv`. -/
private theorem conjugateEquiv_hom_eq_inv {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R') (c : L ≅ L') (e : R ≅ R')
    (h : conjugateEquiv adj adj' c.inv = e.hom) : conjugateEquiv adj' adj c.hom = e.inv := by
  have := conjugateEquiv_comm adj' adj (α := c.hom) (β := c.inv) (by simp)
  rw [h] at this
  exact (Iso.comp_hom_eq_id e).1 this

/-- Comparisons of left adjoints of the same right adjoints are compatible with compositors whose
conjugates are the same comparison of right adjoints. -/
theorem leftAdjointUniq_compCoherence {Rb rb : C ⥤ D} {Ra ra : D ⥤ E} {Rab rab : C ⥤ E}
    {Gb : D ⥤ C} {Ga : E ⥤ D} {Gab : E ⥤ C} (adjRa : Ra ⊣ Ga) (adjra : ra ⊣ Ga)
    (adjRb : Rb ⊣ Gb) (adjrb : rb ⊣ Gb) (adjRab : Rab ⊣ Gab) (adjrab : rab ⊣ Gab)
    (cR : Rb ⋙ Ra ≅ Rab) (cr : rb ⋙ ra ≅ rab) (e : Ga ⋙ Gb ≅ Gab)
    (hR : conjugateEquiv (adjRb.comp adjRa) adjRab cR.inv = e.hom)
    (hr : conjugateEquiv (adjrb.comp adjra) adjrab cr.inv = e.hom) (M : C) :
    cR.hom.app M ≫ (adjRab.leftAdjointUniq adjrab).hom.app M =
      (adjRa.leftAdjointUniq adjra).hom.app (Rb.obj M) ≫
        ra.map ((adjRb.leftAdjointUniq adjrb).hom.app M) ≫ cr.hom.app M := by
  have hR' := conjugateEquiv_hom_eq_inv _ _ cR e hR
  have hr' := conjugateEquiv_hom_eq_inv _ _ cr e hr
  have key : cR.hom ≫ (adjRab.leftAdjointUniq adjrab).hom =
      Functor.whiskerLeft Rb (adjRa.leftAdjointUniq adjra).hom ≫
        Functor.whiskerRight (adjRb.leftAdjointUniq adjrb).hom ra ≫ cr.hom := by
    apply (conjugateEquiv adjrab (adjRb.comp adjRa)).injective
    rw [← conjugateEquiv_comp adjrab adjRab (adjRb.comp adjRa),
      conjugateEquiv_leftAdjointUniq_hom_self, hR',
      ← conjugateEquiv_comp adjrab (adjRb.comp adjra) (adjRb.comp adjRa),
      ← conjugateEquiv_comp adjrab (adjrb.comp adjra) (adjRb.comp adjra), hr',
      conjugateEquiv_whiskerRight adjrb adjRb adjra, conjugateEquiv_leftAdjointUniq_hom_self,
      conjugateEquiv_whiskerLeft adjra adjRa adjRb, conjugateEquiv_leftAdjointUniq_hom_self]
    simp
  simpa using NatTrans.congr_app key M

/-- Compositors related by transport along equalities of functors correspond. -/
theorem eqToIso_compCoherence {pg Pg : C ⥤ D} {pf Pf : D ⥤ E} {pm Pm pk Pk : C ⥤ E}
    (eg : pg = Pg) (ef : pf = Pf) (em : pm = Pm) (ek : pk = Pk) (hmk : pm = pk) (hMK : Pm = Pk)
    (c₂ : Pg ⋙ Pf = pg ⋙ pf) (c : Pg ⋙ Pf ≅ Pm) (d : pg ⋙ pf ≅ pm)
    (hd : d = (eqToIso em ≪≫ c.symm ≪≫ eqToIso c₂).symm) (N : C) :
    (d ≪≫ eqToIso hmk).hom.app N ≫ (eqToIso ek).hom.app N =
      pf.map ((eqToIso eg).hom.app N) ≫ (eqToIso ef).hom.app (Pg.obj N) ≫
        (c ≪≫ eqToIso hMK).hom.app N := by
  subst hd eg ef em ek hMK
  simp

end LeftAdjointUniq

section TransferEqToIso

variable {C D C' D' C'' D'' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Category* C''] [Category* D'']
  {ε : C ⥤ D} {ε' : C' ⥤ D'} {ε'' : C'' ⥤ D''}
  {pg Pg : D ⥤ D'} {pf Pf : D' ⥤ D''} {pm Pm pk Pk : D ⥤ D''}
  {Rg rg : C ⥤ C'} {Rf rf : C' ⥤ C''} {Rk rk : C ⥤ C''} {jg : Rg ≅ rg} {jf : Rf ≅ rf} {jk : Rk ≅ rk}
  {Fg : ε ⋙ Pg ≅ Rg ⋙ ε'} {Ff : ε' ⋙ Pf ≅ Rf ⋙ ε''} {Fk : ε ⋙ Pk ≅ Rk ⋙ ε''}
  {cR : Rg ⋙ Rf ⟶ Rk} {cA : rg ⋙ rf ⟶ rk}

/-- `CategoryTheory.Functor.underivedCompCoherence_transferredUnderivedSquare` for transports
along equalities of functors, with the correspondence of the compositors given as an equation of
isomorphisms. -/
theorem underivedCompCoherence_transferredUnderivedSquare_eqToIso
    (eg : pg = Pg) (ef : pf = Pf) (em : pm = Pm) (ek : pk = Pk) (hmk : pm = pk) (hMK : Pm = Pk)
    (c₂ : Pg ⋙ Pf = pg ⋙ pf) (c : Pg ⋙ Pf ≅ Pm) (d : pg ⋙ pf ≅ pm)
    (hd : d = (eqToIso em ≪≫ c.symm ≪≫ eqToIso c₂).symm)
    (hF : UnderivedCompCoherence Fg Ff Fk cR (c ≪≫ eqToIso hMK).hom)
    (hj : ∀ M : C, cR.app M ≫ jk.hom.app M =
      jf.hom.app (Rg.obj M) ≫ rf.map (jg.hom.app M) ≫ cA.app M) :
    UnderivedCompCoherence (transferredUnderivedSquare (eqToIso eg) Fg jg)
      (transferredUnderivedSquare (eqToIso ef) Ff jf)
      (transferredUnderivedSquare (eqToIso ek) Fk jk)
      cA (d ≪≫ eqToIso hmk).hom :=
  underivedCompCoherence_transferredUnderivedSquare hF
    (fun N => eqToIso_compCoherence eg ef em ek hmk hMK c₂ c d hd N) hj

end TransferEqToIso

section HomotopyQuotient

variable {V W W' : Type*} [Category* V] [Category* W] [Category* W'] [Preadditive V]
  [Preadditive W] [Preadditive W'] {c : ComplexShape ℤ}

/-- `Functor.mapHomotopyCategoryCompIso` at the image of a complex. -/
theorem mapHomotopyCategoryCompIso_hom_app_quotient_natTrans {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W' c).map ((NatTrans.mapHomologicalComplex e.hom c).app K) := by
  show (HomotopyCategory.quotient W' c).map
    ((Functor.mapHomologicalComplexCompIso e c).hom.app K) = _
  congr 1

/-- A compositor on homotopy categories followed by an identification and a transport, at the
image of a complex. -/
theorem mapHomotopyCategoryCompIso_trans_eqToIso_hom_app_quotient {ι : Sort*}
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (P : ι → (V ⥤ W')) {i j : ι} [F.Additive]
    [G.Additive] [H.Additive] [(P i).Additive] [(P j).Additive] (h : i = j)
    (hh : (P i).mapHomotopyCategory c = (P j).mapHomotopyCategory c) (e : F ⋙ G ≅ H)
    (t : H ≅ P i) (K : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c ≪≫ Stacks.Homology.mapHomotopyCategoryIso t c ≪≫
        eqToIso hh).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W' c).map
        ((NatTrans.mapHomologicalComplex ((e ≪≫ t) ≪≫ eqToIso (congrArg P h)).hom c).app K) := by
  subst h
  show (HomotopyCategory.quotient W' c).map
      ((Functor.mapHomologicalComplexCompIso e c).hom.app K) ≫
    (HomotopyCategory.quotient W' c).map ((NatTrans.mapHomologicalComplex t.hom c).app K) ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Functor.map_comp]
  congr 1
  ext n
  simp

end HomotopyQuotient

end CategoryTheory.Functor
