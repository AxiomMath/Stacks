module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions

/-!
# Left derived functors intertwined by exact functors

Let `L₁ : C₁ ⥤ D₁`, `L₁' : C₁' ⥤ D₁'`, `L₂ : C₂ ⥤ D₂` and `L₂' : C₂' ⥤ D₂'` be localizations
(in the application: homotopy categories and derived categories of two pairs of abelian
categories), let `Lg : D₁ ⥤ D₁'` and `Mg : D₂ ⥤ D₂'` be left derived functors of `gK ⋙ L₁'` and
`hK ⋙ L₂'` with comparisons `αg` and `βg`, and let `ε` be functors `C₁ ⥤ C₂`, `C₁' ⥤ C₂'` and
`D₁ ⥤ D₂`, `D₁' ⥤ D₂'` compatible with the localizations (`e`, `e'`; for an exact functor of
abelian categories these are `CategoryTheory.Functor.mapDerivedCategoryFactorsh`).  An
identification `u : εK ⋙ hK ≅ gK ⋙ εK'` of the underived functors then induces, by the universal
property of the left derived functor `Lg ⋙ εD'`, a comparison `εD ⋙ Mg ⟶ Lg ⋙ εD'`
(`CategoryTheory.Functor.exactDerivedComparison`).  It is invertible when `Lg` is computed by a
resolving class that `εK` carries into objects at which `βg` is invertible.

These comparisons are compatible with composition
(`CategoryTheory.Functor.exactDerivedComparison_comp`): given composition isomorphisms of the
derived functors on both sides that are characterized by their comparisons in the usual way, the
compatibility of the derived comparisons with them reduces to the compatibility of the underived
identifications `u` with the underived compositors.

## Main definitions

* `CategoryTheory.Functor.exactDerivedCompCounit`: `εD ⋙ Mg`, read on `C₁`, compared with
  `gK ⋙ L₁' ⋙ εD'`.
* `CategoryTheory.Functor.exactDerivedComparison`: the induced comparison `εD ⋙ Mg ⟶ Lg ⋙ εD'`.
* `CategoryTheory.Functor.UnderivedCompCoherence`: the compatibility of underived identifications
  with underived compositors.

## Main results

* `CategoryTheory.Functor.exactDerivedComparison_app_fac`: its characterization on `C₁`.
* `CategoryTheory.Functor.isIso_exactDerivedComparison`: it is invertible, given a resolving
  class.
* `CategoryTheory.Functor.exactDerivedComparison_comp`: **compatibility with composition**, for
  any comparisons with the characterizing property of
  `CategoryTheory.Functor.exactDerivedComparison_app_fac`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

section Comparison

variable {C₁ D₁ C₁' D₁' C₂ D₂ C₂' D₂' : Type*} [Category* C₁] [Category* D₁] [Category* C₁']
  [Category* D₁'] [Category* C₂] [Category* D₂] [Category* C₂'] [Category* D₂']
  {L₁ : C₁ ⥤ D₁} {L₁' : C₁' ⥤ D₁'} {L₂ : C₂ ⥤ D₂} {L₂' : C₂' ⥤ D₂'}
  {εK : C₁ ⥤ C₂} {εK' : C₁' ⥤ C₂'} {εD : D₁ ⥤ D₂} {εD' : D₁' ⥤ D₂'}
  (e : L₁ ⋙ εD ≅ εK ⋙ L₂) (e' : L₁' ⋙ εD' ≅ εK' ⋙ L₂')
  {gK : C₁ ⥤ C₁'} {Lg : D₁ ⥤ D₁'} (αg : L₁ ⋙ Lg ⟶ gK ⋙ L₁')
  {hK : C₂ ⥤ C₂'} {Mg : D₂ ⥤ D₂'} (βg : L₂ ⋙ Mg ⟶ hK ⋙ L₂')
  (u : εK ⋙ hK ≅ gK ⋙ εK')

/-- The functor `εD ⋙ Mg` read on `C₁`, compared with `gK ⋙ L₁' ⋙ εD'`: the identification `e`,
then the comparison `βg` of `Mg`, then the underived identification `u`, then `e'`. -/
def exactDerivedCompCounit : L₁ ⋙ εD ⋙ Mg ⟶ (gK ⋙ L₁') ⋙ εD' where
  app X := Mg.map (e.hom.app X) ≫ βg.app (εK.obj X) ≫ L₂'.map (u.hom.app X) ≫
    e'.inv.app (gK.obj X)
  naturality X Y φ := by
    have h₁ := e.hom.naturality φ
    have h₂ := βg.naturality (εK.map φ)
    have h₃ := u.hom.naturality φ
    have h₄ := e'.inv.naturality (gK.map φ)
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ h₄ ⊢
    rw [← Mg.map_comp_assoc, h₁, Mg.map_comp_assoc, reassoc_of% h₂, ← L₂'.map_comp_assoc, h₃,
      L₂'.map_comp_assoc, h₄]
    simp only [Category.assoc]

/-- The component of `CategoryTheory.Functor.exactDerivedCompCounit` at `X : C₁` is the composite
of `Mg.map (e.hom.app X)`, `βg.app (εK.obj X)`, `L₂'.map (u.hom.app X)` and
`e'.inv.app (gK.obj X)`. -/
theorem exactDerivedCompCounit_app (X : C₁) :
    (exactDerivedCompCounit e e' βg u).app X =
      Mg.map (e.hom.app X) ≫ βg.app (εK.obj X) ≫ L₂'.map (u.hom.app X) ≫
        e'.inv.app (gK.obj X) :=
  rfl

/-- If `Lg` is a left derived functor of `gK ⋙ L₁'` and `gK ⋙ L₁'` inverts the morphisms of `W₁`
between objects of a resolving class `P`, then `Lg ⋙ εD'` is a left derived functor of
`gK ⋙ L₁' ⋙ εD'`. -/
theorem isLeftDerivedFunctor_comp_of_inverts_on_resolutions (W₁ : MorphismProperty C₁)
    [L₁.IsLocalization W₁] [W₁.HasRightCalculusOfFractions] [Lg.IsLeftDerivedFunctor αg W₁]
    (P : ObjectProperty C₁)
    (hP : ∀ X : C₁, ∃ (Y : C₁) (_ : P Y) (s : Y ⟶ X), W₁ s)
    (hF : ∀ {X Y : C₁} (s : X ⟶ Y), W₁ s → P X → P Y → IsIso ((gK ⋙ L₁').map s)) :
    (Lg ⋙ εD').IsLeftDerivedFunctor
      ((Functor.associator L₁ Lg εD').inv ≫ Functor.whiskerRight αg εD') W₁ :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions W₁ P hP (gK ⋙ L₁') hF L₁
    Lg αg εD'

variable (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  [(Lg ⋙ εD').IsLeftDerivedFunctor
    ((Functor.associator L₁ Lg εD').inv ≫ Functor.whiskerRight αg εD') W₁]

/-- **The comparison `εD ⋙ Mg ⟶ Lg ⋙ εD'` induced by an underived identification**
`u : εK ⋙ hK ≅ gK ⋙ εK'`, through the universal property of the left derived functor
`Lg ⋙ εD'` of `gK ⋙ L₁' ⋙ εD'`. -/
def exactDerivedComparison : εD ⋙ Mg ⟶ Lg ⋙ εD' :=
  (Lg ⋙ εD').leftDerivedLift ((Functor.associator L₁ Lg εD').inv ≫ Functor.whiskerRight αg εD')
    W₁ (εD ⋙ Mg) (exactDerivedCompCounit e e' βg u)

/-- **The characterization of `CategoryTheory.Functor.exactDerivedComparison` on `C₁`.** -/
theorem exactDerivedComparison_app_fac (X : C₁) :
    (exactDerivedComparison e e' αg βg u W₁).app (L₁.obj X) ≫ εD'.map (αg.app X) =
      Mg.map (e.hom.app X) ≫ βg.app (εK.obj X) ≫ L₂'.map (u.hom.app X) ≫
        e'.inv.app (gK.obj X) := by
  have h := (Lg ⋙ εD').leftDerived_fac_app
    ((Functor.associator L₁ Lg εD').inv ≫ Functor.whiskerRight αg εD') W₁ (εD ⋙ Mg)
    (exactDerivedCompCounit e e' βg u) X
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Category.id_comp] at h
  exact h.trans (exactDerivedCompCounit_app e e' βg u X)

/-- **`CategoryTheory.Functor.exactDerivedComparison` is invertible** when `Lg` is computed on a
resolving class `P` which `εK` carries into objects at which `βg` is invertible. -/
theorem isIso_exactDerivedComparison [W₁.HasRightCalculusOfFractions] (P : ObjectProperty C₁)
    (hP : ∀ X : C₁, ∃ (Y : C₁) (_ : P Y) (s : Y ⟶ X), W₁ s)
    (hF : ∀ {X Y : C₁} (s : X ⟶ Y), W₁ s → P X → P Y → IsIso ((gK ⋙ L₁').map s))
    (hβ : ∀ X : C₁, P X → IsIso (βg.app (εK.obj X))) :
    IsIso (exactDerivedComparison e e' αg βg u W₁) := by
  have hFG : ∀ {X Y : C₁} (s : X ⟶ Y), W₁ s → P X → P Y →
      IsIso (((gK ⋙ L₁') ⋙ εD').map s) := fun s hs hX hY => by
    have := hF s hs hX hY
    exact Functor.map_isIso εD' ((gK ⋙ L₁').map s)
  have hτ : ∀ X : C₁, P X → IsIso ((exactDerivedCompCounit e e' βg u).app X) := fun X hX => by
    have := hβ X hX
    rw [exactDerivedCompCounit_app]
    infer_instance
  have := LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions W₁ P hP
    ((gK ⋙ L₁') ⋙ εD') hFG L₁ (εD ⋙ Mg) (exactDerivedCompCounit e e' βg u) hτ
  exact ((Lg ⋙ εD').isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    ((Functor.associator L₁ Lg εD').inv ≫ Functor.whiskerRight αg εD') W₁ (εD ⋙ Mg)
    (exactDerivedCompCounit e e' βg u)).1 this

end Comparison

section Coherence

variable {C₁ D₁ C₁' D₁' C₁'' D₁'' C₂ D₂ C₂' D₂' C₂'' D₂'' : Type*} [Category* C₁] [Category* D₁]
  [Category* C₁'] [Category* D₁'] [Category* C₁''] [Category* D₁''] [Category* C₂]
  [Category* D₂] [Category* C₂'] [Category* D₂'] [Category* C₂''] [Category* D₂'']
  {L₁ : C₁ ⥤ D₁} {L₁' : C₁' ⥤ D₁'} {L₁'' : C₁'' ⥤ D₁''}
  {L₂ : C₂ ⥤ D₂} {L₂' : C₂' ⥤ D₂'} {L₂'' : C₂'' ⥤ D₂''}
  {εK : C₁ ⥤ C₂} {εK' : C₁' ⥤ C₂'} {εK'' : C₁'' ⥤ C₂''}
  {εD : D₁ ⥤ D₂} {εD' : D₁' ⥤ D₂'} {εD'' : D₁'' ⥤ D₂''}
  {e : L₁ ⋙ εD ≅ εK ⋙ L₂} {e' : L₁' ⋙ εD' ≅ εK' ⋙ L₂'} {e'' : L₁'' ⋙ εD'' ≅ εK'' ⋙ L₂''}
  {gK : C₁ ⥤ C₁'} {fK : C₁' ⥤ C₁''} {kK : C₁ ⥤ C₁''}
  {Lg : D₁ ⥤ D₁'} {Lf : D₁' ⥤ D₁''} {Lk : D₁ ⥤ D₁''}
  {αg : L₁ ⋙ Lg ⟶ gK ⋙ L₁'} {αf : L₁' ⋙ Lf ⟶ fK ⋙ L₁''} {αk : L₁ ⋙ Lk ⟶ kK ⋙ L₁''}
  {hgK : C₂ ⥤ C₂'} {hfK : C₂' ⥤ C₂''} {hkK : C₂ ⥤ C₂''}
  {Mg : D₂ ⥤ D₂'} {Mf : D₂' ⥤ D₂''} {Mk : D₂ ⥤ D₂''}
  {βg : L₂ ⋙ Mg ⟶ hgK ⋙ L₂'} {βf : L₂' ⋙ Mf ⟶ hfK ⋙ L₂''} {βk : L₂ ⋙ Mk ⟶ hkK ⋙ L₂''}
  {ug : εK ⋙ hgK ≅ gK ⋙ εK'} {uf : εK' ⋙ hfK ≅ fK ⋙ εK''} {uk : εK ⋙ hkK ≅ kK ⋙ εK''}
  {cA : gK ⋙ fK ⟶ kK} {sA : Lg ⋙ Lf ⟶ Lk} {cE : hgK ⋙ hfK ⟶ hkK} {sE : Mg ⋙ Mf ⟶ Mk}
  {φg : εD ⋙ Mg ⟶ Lg ⋙ εD'} {φf : εD' ⋙ Mf ⟶ Lf ⋙ εD''} {φk : εD ⋙ Mk ⟶ Lk ⋙ εD''}

variable (ug uf uk cA cE) in
/-- **The underived compatibility** of identifications `ug`, `uf`, `uk` of the underived functors
with underived compositors `cA : gK ⋙ fK ⟶ kK` and `cE : hgK ⋙ hfK ⟶ hkK`. -/
def UnderivedCompCoherence : Prop :=
  ∀ X : C₁, cE.app (εK.obj X) ≫ uk.hom.app X =
    hfK.map (ug.hom.app X) ≫ uf.hom.app (gK.obj X) ≫ εK''.map (cA.app X)

/-- The identity of `CategoryTheory.Functor.exactDerivedComparison_comp` at the image `L₁.obj X`
of an object `X : C₁`, after composition with `εD''.map (αk.app X)`. -/
theorem exactDerivedComparison_comp_app_aux
    (hsA : ∀ X : C₁, sA.app (L₁.obj X) ≫ αk.app X =
      Lf.map (αg.app X) ≫ αf.app (gK.obj X) ≫ L₁''.map (cA.app X))
    (hsE : ∀ X : C₂, sE.app (L₂.obj X) ≫ βk.app X =
      Mf.map (βg.app X) ≫ βf.app (hgK.obj X) ≫ L₂''.map (cE.app X))
    (hφg : ∀ X : C₁, φg.app (L₁.obj X) ≫ εD'.map (αg.app X) =
      Mg.map (e.hom.app X) ≫ βg.app (εK.obj X) ≫ L₂'.map (ug.hom.app X) ≫
        e'.inv.app (gK.obj X))
    (hφf : ∀ X : C₁', φf.app (L₁'.obj X) ≫ εD''.map (αf.app X) =
      Mf.map (e'.hom.app X) ≫ βf.app (εK'.obj X) ≫ L₂''.map (uf.hom.app X) ≫
        e''.inv.app (fK.obj X))
    (hφk : ∀ X : C₁, φk.app (L₁.obj X) ≫ εD''.map (αk.app X) =
      Mk.map (e.hom.app X) ≫ βk.app (εK.obj X) ≫ L₂''.map (uk.hom.app X) ≫
        e''.inv.app (kK.obj X))
    (hu : UnderivedCompCoherence ug uf uk cA cE)
    (X : C₁) :
    sE.app (εD.obj (L₁.obj X)) ≫ φk.app (L₁.obj X) ≫ εD''.map (αk.app X) =
      Mf.map (φg.app (L₁.obj X)) ≫ φf.app (Lg.obj (L₁.obj X)) ≫
        εD''.map (sA.app (L₁.obj X)) ≫ εD''.map (αk.app X) := by
  have nsE := sE.naturality (e.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at nsE
  have lhs : sE.app (εD.obj (L₁.obj X)) ≫ φk.app (L₁.obj X) ≫ εD''.map (αk.app X) =
      Mf.map (Mg.map (e.hom.app X)) ≫ Mf.map (βg.app (εK.obj X)) ≫
        βf.app (hgK.obj (εK.obj X)) ≫ L₂''.map (cE.app (εK.obj X)) ≫
          L₂''.map (uk.hom.app X) ≫ e''.inv.app (kK.obj X) := by
    rw [hφk X, ← reassoc_of% nsE, reassoc_of% (hsE (εK.obj X))]
  have nφf := φf.naturality (αg.app X)
  have nβf := βf.naturality (ug.hom.app X)
  have ne'' := e''.inv.naturality (cA.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at nφf nβf ne''
  have hg' : Mf.map (φg.app (L₁.obj X)) ≫ Mf.map (εD'.map (αg.app X)) ≫
      Mf.map (e'.hom.app (gK.obj X)) =
      Mf.map (Mg.map (e.hom.app X)) ≫ Mf.map (βg.app (εK.obj X)) ≫
        Mf.map (L₂'.map (ug.hom.app X)) := by
    simp only [← Functor.map_comp, ← Category.assoc]
    rw [hφg X]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj]
  have rhs : Mf.map (φg.app (L₁.obj X)) ≫ φf.app (Lg.obj (L₁.obj X)) ≫
      εD''.map (sA.app (L₁.obj X)) ≫ εD''.map (αk.app X) =
      Mf.map (Mg.map (e.hom.app X)) ≫ Mf.map (βg.app (εK.obj X)) ≫
        βf.app (hgK.obj (εK.obj X)) ≫ L₂''.map (hfK.map (ug.hom.app X)) ≫
          L₂''.map (uf.hom.app (gK.obj X)) ≫ L₂''.map (εK''.map (cA.app X)) ≫
            e''.inv.app (kK.obj X) := by
    rw [← εD''.map_comp, hsA X, εD''.map_comp, εD''.map_comp, ← reassoc_of% nφf]
    have hφf' := hφf (gK.obj X)
    have hmid : φf.app (L₁'.obj (gK.obj X)) ≫ εD''.map (αf.app (gK.obj X)) ≫
        εD''.map (L₁''.map (cA.app X)) =
        Mf.map (e'.hom.app (gK.obj X)) ≫ βf.app (εK'.obj (gK.obj X)) ≫
          L₂''.map (uf.hom.app (gK.obj X)) ≫ L₂''.map (εK''.map (cA.app X)) ≫
            e''.inv.app (kK.obj X) := by
      rw [reassoc_of% hφf', ← ne'']
    rw [hmid, reassoc_of% hg', reassoc_of% nβf]
  rw [lhs, rhs, ← L₂''.map_comp_assoc, hu X]
  simp only [Functor.map_comp, Category.assoc]

/-- **Comparisons of left derived functors under exact functors are compatible with
composition.**  Let `sA : Lg ⋙ Lf ⟶ Lk` and `sE : Mg ⋙ Mf ⟶ Mk` be characterized by underived
compositors `cA` and `cE` (`hsA`, `hsE`), and let `φg`, `φf`, `φk` be comparisons characterized by
underived identifications `ug`, `uf`, `uk` as in
`CategoryTheory.Functor.exactDerivedComparison_app_fac`.  If the underived identifications are
compatible with the underived compositors (`hu`), then so are the derived comparisons with the
derived compositors. -/
theorem exactDerivedComparison_comp (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
    [(Lk ⋙ εD'').IsLeftDerivedFunctor
      ((Functor.associator L₁ Lk εD'').inv ≫ Functor.whiskerRight αk εD'') W₁]
    (hsA : ∀ X : C₁, sA.app (L₁.obj X) ≫ αk.app X =
      Lf.map (αg.app X) ≫ αf.app (gK.obj X) ≫ L₁''.map (cA.app X))
    (hsE : ∀ X : C₂, sE.app (L₂.obj X) ≫ βk.app X =
      Mf.map (βg.app X) ≫ βf.app (hgK.obj X) ≫ L₂''.map (cE.app X))
    (hφg : ∀ X : C₁, φg.app (L₁.obj X) ≫ εD'.map (αg.app X) =
      Mg.map (e.hom.app X) ≫ βg.app (εK.obj X) ≫ L₂'.map (ug.hom.app X) ≫
        e'.inv.app (gK.obj X))
    (hφf : ∀ X : C₁', φf.app (L₁'.obj X) ≫ εD''.map (αf.app X) =
      Mf.map (e'.hom.app X) ≫ βf.app (εK'.obj X) ≫ L₂''.map (uf.hom.app X) ≫
        e''.inv.app (fK.obj X))
    (hφk : ∀ X : C₁, φk.app (L₁.obj X) ≫ εD''.map (αk.app X) =
      Mk.map (e.hom.app X) ≫ βk.app (εK.obj X) ≫ L₂''.map (uk.hom.app X) ≫
        e''.inv.app (kK.obj X))
    (hu : UnderivedCompCoherence ug uf uk cA cE)
    (M : D₁) :
    sE.app (εD.obj M) ≫ φk.app M =
      Mf.map (φg.app M) ≫ φf.app (Lg.obj M) ≫ εD''.map (sA.app M) := by
  let τ₁ : εD ⋙ Mg ⋙ Mf ⟶ Lk ⋙ εD'' := Functor.whiskerLeft εD sE ≫ φk
  let τ₂ : εD ⋙ Mg ⋙ Mf ⟶ Lk ⋙ εD'' :=
    { app := fun M => Mf.map (φg.app M) ≫ φf.app (Lg.obj M) ≫ εD''.map (sA.app M)
      naturality := fun M N ψ => by
        have h₁ := φg.naturality ψ
        have h₂ := φf.naturality (Lg.map ψ)
        have h₃ := sA.naturality ψ
        simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ ⊢
        rw [← Mf.map_comp_assoc, h₁, Mf.map_comp_assoc, reassoc_of% h₂, ← εD''.map_comp, h₃,
          εD''.map_comp]
        simp only [Category.assoc] }
  have key : τ₁ = τ₂ := by
    refine (Lk ⋙ εD'').leftDerived_ext
      ((Functor.associator L₁ Lk εD'').inv ≫ Functor.whiskerRight αk εD'') W₁ _ τ₁ τ₂ ?_
    ext X
    simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp, Category.assoc]
    exact exactDerivedComparison_comp_app_aux hsA hsE hφg hφf hφk hu X
  exact congrArg (fun τ : εD ⋙ Mg ⋙ Mf ⟶ Lk ⋙ εD'' => τ.app M) key

end Coherence

end CategoryTheory.Functor

end
