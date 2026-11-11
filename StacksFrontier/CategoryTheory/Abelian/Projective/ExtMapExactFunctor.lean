module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# `Ext.mapExactFunctor` on a class presented by a projective resolution

Let `F : C ⥤ D` be an exact functor of abelian categories, `R` a projective resolution of `X` in
`C`, `R'` a projective resolution of `X'` in `D`, `a : X' ⟶ F X`, and `φ : R' ⟶ F R` a morphism
of chain complexes lifting `a`. For a cocycle `f : R_n ⟶ Y` of `R`, this file computes the class
`a ∘ F(R.extMk f)` in `Ext^n(X', F Y)`: it is the class of the cocycle `φ_n ≫ F f` of `R'`.

Mathlib has `CategoryTheory.ProjectiveResolution.mk₀_comp_extMk` (the case `F = 𝟭`) and
`CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀`, `_comp` and `_extClass`, but nothing applying
`Ext.mapExactFunctor` to `extMk`. The injective-resolution analogue is
`Stacks.Cohomology.ModuleComparison.mapExactFunctor_extMk`; the localization bookkeeping lemmas
proved there are reused here.

## Main results

* `Stacks.ExtProjective.resolutionCochainMap`: the morphism `R'.cochainComplex ⟶ F R.cochainComplex`
  of cochain complexes indexed by `ℤ` induced by `φ`.
* `Stacks.ExtProjective.mk₀_comp_mapExactFunctor_extMk`: the formula
  `a ∘ F(R.extMk f) = R'.extMk (φ_n ≫ F f)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CochainComplex
  CochainComplex.HomComplex Localization

universe w w' v v' u u'

namespace Stacks.ExtProjective

section Localizer

variable {D : Type u} [Category.{v} D] {W : MorphismProperty D} {M : Type*} [AddMonoid M]
  [HasShift D M] [W.IsCompatibleWithShift M] [W.RespectsIso]

/-- **Moving a formal inverse past a morphism.** If `ψ ≫ s = s' ≫ g` with `s` and `s'` inverted,
then `g` followed by the formal inverse of `s` is the formal inverse of `s'` followed by `ψ`. -/
lemma mk₀_comp_mk₀Inv_eq {X X' K K' : D}
    [HasSmallLocalizedShiftedHom.{w} W M X X] [HasSmallLocalizedShiftedHom.{w} W M X' X']
    [HasSmallLocalizedShiftedHom.{w} W M K K] [HasSmallLocalizedShiftedHom.{w} W M K' K']
    [HasSmallLocalizedShiftedHom.{w} W M X' X] [HasSmallLocalizedShiftedHom.{w} W M X K]
    [HasSmallLocalizedShiftedHom.{w} W M X' K] [HasSmallLocalizedShiftedHom.{w} W M X' K']
    [HasSmallLocalizedShiftedHom.{w} W M K' K] [HasSmallLocalizedShiftedHom.{w} W M K' X']
    [HasSmallLocalizedShiftedHom.{w} W M K' X] [HasSmallLocalizedShiftedHom.{w} W M K X]
    [HasSmallLocalizedShiftedHom.{w} W M K X'] [HasSmallLocalizedShiftedHom.{w} W M X X']
    [HasSmallLocalizedShiftedHom.{w} W M X K'] [HasSmallLocalizedShiftedHom.{w} W M K K']
    (g : X' ⟶ X) (s : K ⟶ X) (hs : W s) (s' : K' ⟶ X') (hs' : W s') (ψ : K' ⟶ K)
    (h : ψ ≫ s = s' ≫ g) :
    (SmallShiftedHom.mk₀.{w} W (0 : M) rfl g).comp (SmallShiftedHom.mk₀Inv (0 : M) rfl s hs)
        (add_zero 0) =
      (SmallShiftedHom.mk₀Inv (0 : M) rfl s' hs').comp
        (SmallShiftedHom.mk₀.{w} W (0 : M) rfl ψ) (add_zero 0) := by
  apply (SmallShiftedHom.equiv W W.Q).injective
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk₀Inv,
    ShiftedHom.mk₀_comp_mk₀]
  congr 1
  have hs'' : W.Q.map s' ≫ (isoOfHom W.Q W s' hs').inv = 𝟙 _ := by
    rw [← isoOfHom_hom W.Q W s' hs', Iso.hom_inv_id]
  rw [← cancel_epi (isoOfHom W.Q W s' hs').hom, isoOfHom_hom, reassoc_of% hs'',
    ← Functor.map_comp_assoc, ← h, Functor.map_comp_assoc, ← isoOfHom_hom W.Q W s hs,
    Iso.hom_inv_id, Category.comp_id]

end Localizer

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  {X : C} (R : ProjectiveResolution X) {X' : D} (R' : ProjectiveResolution X')
  (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)

/-- The degree-`p` component of `resolutionCochainMap`. -/
def resolutionCochainMapF (p : ℤ) :
    R'.cochainComplex.X p ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).X p :=
  if h : p ≤ 0 then
    (R'.cochainComplexXIso p (-p).toNat (by lia)).hom ≫ φ.f (-p).toNat ≫
      F.map (R.cochainComplexXIso p (-p).toNat (by lia)).inv
  else 0

lemma resolutionCochainMapF_eq (p : ℤ) (k : ℕ) (hk : -(k : ℤ) = p) :
    resolutionCochainMapF F R R' φ p =
      (R'.cochainComplexXIso p k hk).hom ≫ φ.f k ≫ F.map (R.cochainComplexXIso p k hk).inv := by
  obtain rfl : k = (-p).toNat := by lia
  simp only [resolutionCochainMapF, show p ≤ 0 by lia, ↓reduceDIte]

/-- **The morphism of `ℤ`-indexed cochain complexes induced by `φ`.** In degree `-k` it is
`φ_k`, read through the identifications of `R'.cochainComplex.X (-k)` with `R'.complex.X k` and of
`R.cochainComplex.X (-k)` with `R.complex.X k`; in positive degrees it is zero. -/
def resolutionCochainMap :
    R'.cochainComplex ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex where
  f := resolutionCochainMapF F R R' φ
  comm' p q (hpq : p + 1 = q) := by
    by_cases hq : q ≤ 0
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, -(k : ℤ) = q := ⟨(-q).toNat, by lia⟩
      rw [resolutionCochainMapF_eq F R R' φ q k hk,
        resolutionCochainMapF_eq F R R' φ p (k + 1) (by lia),
        R'.cochainComplex_d p q (k + 1) k (by lia) hk, Functor.mapHomologicalComplex_obj_d,
        R.cochainComplex_d p q (k + 1) k (by lia) hk]
      have hc := φ.comm (k + 1) k
      simp only [Functor.mapHomologicalComplex_obj_d] at hc
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
      rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp, ← reassoc_of% hc]
    · have hz : IsZero (R.cochainComplex.X q) :=
        CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 q (by lia)
      have hz' : IsZero (R'.cochainComplex.X q) :=
        CochainComplex.isZero_of_isStrictlyLE R'.cochainComplex 0 q (by lia)
      rw [hz'.eq_of_tgt (R'.cochainComplex.d p q) 0, Functor.mapHomologicalComplex_obj_d,
        hz.eq_of_tgt (R.cochainComplex.d p q) 0, F.map_zero, zero_comp, comp_zero]

lemma resolutionCochainMap_f (p : ℤ) (k : ℕ) (hk : -(k : ℤ) = p) :
    (resolutionCochainMap F R R' φ).f p =
      (R'.cochainComplexXIso p k hk).hom ≫ φ.f k ≫ F.map (R.cochainComplexXIso p k hk).inv :=
  resolutionCochainMapF_eq F R R' φ p k hk

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The image of a projective resolution under an exact functor is cohomologically concentrated
in degree zero, from above. -/
instance isLE_mapHomologicalComplex_cochainComplex :
    CochainComplex.IsLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0 := by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')]
  infer_instance

/-- The image of a projective resolution under an exact functor is cohomologically concentrated
in degree zero, from below. -/
instance isGE_mapHomologicalComplex_cochainComplex :
    CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex) 0 := by
  simp only [HomologicalComplex.isSupported_iff_of_quasiIso
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')]
  infer_instance

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- **`resolutionCochainMap` lifts `a` on the augmentations.** -/
lemma resolutionCochainMap_comp_π' (a : X' ⟶ F.obj X)
    (hφ : φ.f 0 ≫ F.map (R.π.f 0) = R'.π.f 0 ≫ a) :
    resolutionCochainMap F R R' φ ≫
        (Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex)).inv ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π' ≫
            ((F.mapCochainComplexSingleFunctor 0).app X).hom =
      R'.π' ≫ (CochainComplex.singleFunctor D 0).map a := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    resolutionCochainMap_f F R R' φ 0 0 (by simp), R.π'_f_zero, R'.π'_f_zero]
  simp only [Iso.refl_inv, HomologicalComplex.id_f, Category.id_comp, Category.assoc,
    Functor.mapCochainComplexSingleFunctor, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simp only [Iso.inv_hom_id_assoc]
  have key : φ.f 0 ≫ F.map ((R.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom) = R'.π.f 0 ≫ a := by
    have h1 : (R.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom = R.π.f 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun x => R.π.f 0 ≫ x)
        (Iso.inv_hom_id _)).trans (Category.comp_id _))
    exact (congrArg (fun u => φ.f 0 ≫ F.map u) h1).trans hφ
  have k2 : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X').inv ≫
      ((CochainComplex.singleFunctor D 0).map a).f 0 =
        a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  rw [reassoc_of% key]
  congr 1
  exact (Category.assoc _ _ _).trans ((congrArg (fun x => R'.π.f 0 ≫ x) k2.symm).trans
    (Category.assoc _ _ _).symm)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- **A cocycle to a single complex, pushed along `F`.** -/
lemma cocycleMap_toSingleMk_postcomp {K : CochainComplex C ℤ} {Y : C} {p q n : ℤ}
    (g : K.X p ⟶ Y) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p) (hg : K.d p' p ≫ g = 0) :
    (Stacks.Cohomology.ModuleComparison.cocycleMap F
        (Cocycle.toSingleMk g h p' hp' hg)).postcomp
        ((F.mapCochainComplexSingleFunctor q).app Y).hom =
      Cocycle.toSingleMk (K := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (F.map g) h p' hp' (by
          rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp, hg, F.map_zero]) := by
  ext r t hrt
  by_cases hr : r = p
  · subst hr
    obtain rfl : t = q := by lia
    simp only [Cocycle.postcomp, Stacks.Cohomology.ModuleComparison.cocycleMap, Cocycle.mk_coe,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.map_v,
      Cocycle.toSingleMk_coe, Cochain.toSingleMk_v, Functor.map_comp,
      Functor.mapCochainComplexSingleFunctor, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc]
    rw [Iso.map_inv_hom_id_assoc]
  · simp only [Cocycle.postcomp, Stacks.Cohomology.ModuleComparison.cocycleMap, Cocycle.mk_coe,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.map_v,
      Cocycle.toSingleMk_coe, Cochain.toSingleMk_v_eq_zero _ _ _ _ _ hr, F.map_zero, zero_comp]

variable [HasExt.{w} C] [HasExt.{w'} D]

/-- **`a ∘ F(R.extMk f)` is computed on `R'`.** For an exact functor `F`, projective resolutions
`R` of `X` and `R'` of `X'`, a morphism `a : X' ⟶ F X` and a morphism of chain complexes
`φ : R' ⟶ F R` lifting `a`, the class `a ∘ F(R.extMk f)` of `Ext^n(X', F Y)` is the class of the
cocycle `φ_n ≫ F f` of `R'`. -/
theorem mk₀_comp_mapExactFunctor_extMk (a : X' ⟶ F.obj X)
    (hφ : φ.f 0 ≫ F.map (R.π.f 0) = R'.π.f 0 ≫ a)
    {Y : C} {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    (Ext.mk₀ a).comp ((R.extMk f m hm hf).mapExactFunctor F) (zero_add n) =
      R'.extMk (φ.f n ≫ F.map f) m hm (by
        rw [← Category.assoc, ← φ.comm, Category.assoc, Functor.mapHomologicalComplex_obj_d,
          ← F.map_comp, hf, F.map_zero, comp_zero]) := by
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let eX := (F.mapCochainComplexSingleFunctor 0).app X
  let eY := (F.mapCochainComplexSingleFunctor 0).app Y
  let eR := Iso.refl ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex)
  have hR : HomologicalComplex.quasiIso C (ComplexShape.up ℤ) R.π' :=
    (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  have hR' : HomologicalComplex.quasiIso D (ComplexShape.up ℤ) R'.π' :=
    (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  have hFR : HomologicalComplex.quasiIso D (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π') := Φ.map _ hR
  have hs : HomologicalComplex.quasiIso D (ComplexShape.up ℤ)
      (eR.inv ≫ Φ.functor.map R.π' ≫ eX.hom) :=
    @MorphismProperty.RespectsIso.precomp _ _ _ _ _ _ _ eR.inv (Iso.isIso_inv eR) _
      (@MorphismProperty.RespectsIso.postcomp _ _ _ _ _ _ _ eX.hom (Iso.isIso_hom eX) _ hFR)
  let x : Cocycle R.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ) :=
    Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (neg_add_cancel (n : ℤ))
      (-m) (by lia) (by simpa [R.cochainComplex_d _ _ m n rfl rfl])
  have hL : (R.extMk f m hm hf).mapExactFunctor F =
      Φ.smallShiftedHomMap eX eY
        ((SmallShiftedHom.mk₀Inv (0 : ℤ) rfl R.π' hR).comp
          (SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x)) (add_zero _)) := rfl
  have h1 := Φ.smallShiftedHomMap_comp eX eR eY (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl R.π' hR)
    (SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm x)) (add_zero _)
  have h2 := Stacks.Cohomology.ModuleComparison.smallShiftedHomMap_mk₀Inv Φ eR eX (0 : ℤ) rfl
    R.π' hR hFR
  have h3 := Φ.smallShiftedHomMap_mk eR eY (Cocycle.equivHomShift.symm x)
  have h4 := mk₀_comp_mk₀Inv_eq (M := ℤ) ((CochainComplex.singleFunctor D 0).map a) _ hs R'.π' hR'
    (resolutionCochainMap F R R' φ) (resolutionCochainMap_comp_π' F R R' φ a hφ)
  rw [hL, h1, h2, h3]
  change SmallShiftedHom.comp (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl
    ((CochainComplex.singleFunctor D 0).map a)) _ _ = _
  refine (SmallShiftedHom.comp_assoc _ _ _ _ (add_zero _) (add_zero _) (by simp)).symm.trans ?_
  refine (congrArg (fun z => SmallShiftedHom.comp z _ (add_zero _)) h4).trans ?_
  refine (SmallShiftedHom.comp_assoc _ _ _ _ (add_zero _) (add_zero _) (by simp)).trans ?_
  refine (congrArg (fun z => (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl R'.π' hR').comp z (add_zero _))
    (Stacks.Cohomology.ModuleComparison.smallShiftedHom_mk_comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (resolutionCochainMap F R R' φ)) _ (add_zero _))).trans ?_
  refine congrArg (fun z => (SmallShiftedHom.mk₀Inv (0 : ℤ) rfl R'.π' hR').comp
    (SmallShiftedHom.mk (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) z) (add_zero _)) ?_
  rw [ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map]
  refine (congrArg (fun u => resolutionCochainMap F R R' φ ≫ u) (Category.id_comp _)).trans ?_
  change resolutionCochainMap F R R' φ ≫
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Cocycle.equivHomShift.symm x) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (n : ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj Y)) ≫ eY.hom⟦(n : ℤ)⟧' = _
  rw [Stacks.Cohomology.ModuleComparison.cocycleMap_equivHomShift_symm,
    ← Cocycle.equivHomShift_symm_postcomp, ← Cocycle.equivHomShift_symm_precomp]
  congr 1
  simp only [x, eY]
  rw [cocycleMap_toSingleMk_postcomp, ← Cocycle.toSingleMk_precomp]
  congr 1
  rw [resolutionCochainMap_f F R R' φ (-n) n rfl, Functor.map_comp, Category.assoc,
    Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

end Stacks.ExtProjective
