module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Restriction
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.HomologySheafification

/-!
# Restriction of the values of the `Ext` presheaf

The identification of the cohomology of sections over `D(f)` of the internal Hom complex with
`Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f)` carries restriction from `D(f)` to `D(g)` to derived base change
along `R_f ⟶ R_g`.

## Main results

* `AlgebraicGeometry.AffineExt.sectionHomologyEquiv_restrict`: the identification of the values
  of the `Ext` presheaf commutes with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R))

/-- The components of `sectionComplexIsoS` are the adjoints, under extension and restriction of
scalars along `R ⟶ R_f`, of the components of `sectionComplexIso`. -/
lemma sectionComplexIsoS_hom_f_v (f : R) (n p q : ℤ) (hpq : p + n = q)
    (s : ((homModel R K L).obj.X n).val.obj (op (basicOpen R f))) :
    (((sectionComplexIsoS R K L f).hom.f n) s).v p q hpq =
      ((ModuleCat.extendRestrictScalarsAdj (locMap R f).hom).homEquiv _ _).symm
        ((((sectionComplexIso R K L (basicOpen R f)).hom.f n) s).v p q hpq) :=
  rfl

/-- The restriction maps of the section complexes of the internal Hom complex. -/
abbrev secRestrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf) (homModel R K L).obj
        (basicOpen R f) ⟶
      RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf) (homModel R K
          L).obj
        (basicOpen R g) :=
  sectionsComplexRestrict (homModel R K L).obj (homOfLE h).op

/-- The comparison `R_g ⊗ (R_f ⊗ P) ≅ R_g ⊗ P`, on complexes. -/
abbrev srcCompMap {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    (extC (locMap R g)).obj (srcModel R K) ⟶
      ((ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((extC (locMap R f)).obj (srcModel R K)) :=
  (NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).inv (ComplexShape.up ℤ)).app
    (srcModel R K)

/-- The base change map of the sections of the resolution, on complexes. -/
abbrev tgtCompMap {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    ((ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((sectionsS R (basicOpen R f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (resolution R L)) ⟶
      ((sectionsS R (basicOpen R g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (resolution R L) :=
  (NatTrans.mapHomologicalComplex (baseChangeRestrict R h) (ComplexShape.up ℤ)).app
    (resolution R L)

/-- **Restriction of a cocycle of sections, on Hom complexes over the localizations.** -/
lemma cycleCocycle_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) (n : ℤ)
    (c : ((RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf)
      (homModel R K L).obj (basicOpen R f)).cycles n : Type u)) :
    cycleCocycle _ _ n (HomologicalComplex.cyclesMap (sectionComplexIsoS R K L g).hom n
        (HomologicalComplex.cyclesMap (secRestrict R K L h) n c)) =
      ((Cocycle.map' (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom)
        (cycleCocycle _ _ n (HomologicalComplex.cyclesMap (sectionComplexIsoS R K L f).hom n
            c))).precomp
          (srcCompMap R K h)).postcomp (tgtCompMap R L h) := by
  apply Cocycle.ext
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cycleCocycle_coe, Cocycle.postcomp_coe, Cocycle.precomp_coe, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  rw [Cocycle.map', Cocycle.mk_coe, Cochain.map_v, cycleCocycle_coe]
  have e₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (sectionComplexIsoS R K L g).hom n) (HomologicalComplex.cyclesMap (secRestrict R K L h) n c)
  have e₂ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (secRestrict R K L h) n) c
  have e₃ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (sectionComplexIsoS R K L f).hom n) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e₁ e₂ e₃
  rw [e₁, e₂, e₃]
  exact (congrArg ((ModuleCat.extendRestrictScalarsAdj (locMap R g).hom).homEquiv _ _).symm
    (sectionComplexIso_restrict R K L h n p q hpq _)).trans
      ((homEquiv_symm_comp_restrictR R h _ _ _).trans (Category.assoc _ _ _).symm)

/-- The derived comparison `R_g ⊗ (R_f ⊗ -) ≅ R_g ⊗ -` on the class of a complex. -/
lemma extDCompIso_hom_app_Q {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extDCompIso R h).hom.app (DerivedCategory.Q.obj X) =
      (extD (resMap R h)).map
          ((ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapDerivedCategoryFactors.hom.app
              X) ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapDerivedCategoryFactors.hom.app
          ((extC (locMap R f)).obj X) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).hom
          (ComplexShape.up ℤ)).app X) ≫
        (ModuleCat.extendScalars.{u, u, u} (locMap R g).hom).mapDerivedCategoryFactors.inv.app X
            := by
  rw [extDCompIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q]
  simp only [Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso,
    Localization.Lifting.iso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The inverse of the derived comparison `R_g ⊗ (R_f ⊗ -) ≅ R_g ⊗ -` on the class of a complex,
followed by derived base change of the comparison for `R_f`. -/
lemma extDCompIso_inv_app_Q_comp {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extDCompIso R h).inv.app (DerivedCategory.Q.obj X) ≫ (extD (resMap R h)).map
        ((ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapDerivedCategoryFactors.hom.app X) =
      (ModuleCat.extendScalars.{u, u, u} (locMap R g).hom).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).inv
          (ComplexShape.up ℤ)).app X) ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapDerivedCategoryFactors.inv.app
          ((extC (locMap R f)).obj X) := by
  refine ((Iso.app (extDCompIso R h) _).inv_comp_eq).2 ?_
  rw [Iso.app_hom, extDCompIso_hom_app_Q]
  have hγ : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).hom
        (ComplexShape.up ℤ)).app X) ≫ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (extendScalarsCompIso R h).inv (ComplexShape.up ℤ)).app X) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id]
    exact DerivedCategory.Q.map_id _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hγ, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- **The source side of the comparison of restrictions.** -/
lemma srcExtIso_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    (srcExtIso R K g).inv ≫ DerivedCategory.Q.map (srcCompMap R K h) ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapDerivedCategoryFactors.inv.app
          ((extC (locMap R f)).obj (srcModel R K)) =
      (extDCompIso R h).inv.app K ≫ (extD (resMap R h)).map (srcExtIso R K f).inv := by
  have e := (extDCompIso R h).inv.naturality (srcModelIso R K).inv
  dsimp only [Functor.comp_map] at e
  rw [srcExtIso, srcExtIso, Iso.trans_inv, Iso.trans_inv, Functor.mapIso_inv, Functor.mapIso_inv,
    Iso.symm_inv, Iso.symm_inv, Iso.app_hom, Iso.app_hom, Functor.map_comp]
  refine Eq.symm ?_
  rw [← Category.assoc, ← e, Category.assoc, extDCompIso_inv_app_Q_comp]
  simp only [Category.assoc]

/-- On sections of an associated complex, the base change map of restriction is the comparison of
extensions of scalars. -/
lemma tgtCompMap_tilde {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    (NatTrans.mapHomologicalComplex (baseChangeRestrict R h) (ComplexShape.up ℤ)).app
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (srcModel R L)) =
      ((ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R f)
            (ComplexShape.up ℤ)).app (srcModel R L)).inv ≫
        (NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).hom (ComplexShape.up ℤ)).app
          (srcModel R L) ≫
        ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R g)
          (ComplexShape.up ℤ)).app (srcModel R L)).hom := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  have e := tildeBasicOpenIso_restrict R h ((srcModel R L).X p)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Iso.app_hom, Iso.app_inv,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    tildeBasicOpenNatIso, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  rw [e, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The explicit description of `tgtExtIso` as a composite of derived-category morphisms. -/
lemma tgtExtIso_hom (f : R) :
    haveI := quasiIsoSections R L f
    (tgtExtIso R L f).hom = inv (DerivedCategory.Q.map (((sectionsS R (basicOpen R
        f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (resolutionMap R L))) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R f)
        (ComplexShape.up ℤ)).app (srcModel R L)).inv ≫
      (ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapDerivedCategoryFactors.inv.app
        (srcModel R L) ≫
      (extD (locMap R f)).map (srcModelIso R L).hom :=
  rfl

/-- **The target side of the comparison of restrictions.** -/
lemma tgtExtIso_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    (extD (resMap R h)).map (tgtExtIso R L f).hom ≫ (extDCompIso R h).hom.app L =
      (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).mapDerivedCategoryFactors.hom.app
          (((sectionsS R (basicOpen R f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (resolution R L)) ≫
        DerivedCategory.Q.map (tgtCompMap R L h) ≫ (tgtExtIso R L g).hom := by
  have := quasiIsoSections R L f
  have := quasiIsoSections R L g
  let c := ComplexShape.up ℤ
  let Eρ := ModuleCat.extendScalars.{u, u, u} (resMap R h).hom
  let σf := ((sectionsS R (basicOpen R f)).mapHomologicalComplex c).map (resolutionMap R L)
  let σg := ((sectionsS R (basicOpen R g)).mapHomologicalComplex c).map (resolutionMap R L)
  have hσ := (NatTrans.mapHomologicalComplex (baseChangeRestrict R h) c).naturality
    (resolutionMap R L)
  rw [tgtCompMap_tilde] at hσ
  rw [← cancel_epi ((extD (resMap R h)).map (DerivedCategory.Q.map σf)), tgtExtIso_hom,
    tgtExtIso_hom]
  have e₁ := (extDCompIso R h).hom.naturality (srcModelIso R L).hom
  dsimp only [Functor.comp_map] at e₁
  simp only [Functor.map_comp, Category.assoc, e₁, extDCompIso_hom_app_Q]
  rw [← Functor.map_comp_assoc (extD (resMap R h)) (DerivedCategory.Q.map σf), IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [CochainComplex.HomComplex.map_inv_app_map_hom_app_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  congr 1
  have hσQ : DerivedCategory.Q.map (((ModuleCat.extendScalars.{u, u, u}
      (resMap R h).hom).mapHomologicalComplex c).map σf) ≫ DerivedCategory.Q.map (tgtCompMap R L
          h) =
      DerivedCategory.Q.map (((ModuleCat.extendScalars.{u, u, u} (resMap R
          h).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R f)
            (ComplexShape.up ℤ)).app (srcModel R L)).inv) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (extendScalarsCompIso R h).hom
          (ComplexShape.up ℤ)).app (srcModel R L)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R g)
          (ComplexShape.up ℤ)).app (srcModel R L)).hom ≫ DerivedCategory.Q.map σg := by
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (hσ.trans (Category.assoc _ _ _))
  rw [reassoc_of% hσQ, IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc DerivedCategory.Q
    ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R g) (ComplexShape.up ℤ)).app
      (srcModel R L)).hom, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The section complex of the internal Hom complex over `D(f)`. -/
abbrev secC (f : R) : CochainComplex AddCommGrpCat.{u} ℤ :=
  RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf) (homModel R K L).obj
    (basicOpen R f)

/-- The value of `sectionHomologyEquiv` on the homology class of a cycle is the shifted morphism
determined by the corresponding cocycle of the Hom complex over `R_f`. -/
lemma sectionHomologyEquiv_homologyπ (f : R) (n : ℤ) (c : ((secC R K L f).cycles n : Type u)) :
    haveI := isKInjective_sectionsS R f (resolution R L) (isKInjective_resolution R L)
    sectionHomologyEquiv R K L f n (ConcreteCategory.hom ((secC R K L f).homologyπ n) c) =
      (srcExtIso R K f).inv ≫ cohomologyClassAddEquivShiftedHom _ _ n
        (CohomologyClass.mk (cycleCocycle _ _ n
          (HomologicalComplex.cyclesMap (sectionComplexIsoS R K L f).hom n c))) ≫
        ((tgtExtIso R L f).hom)⟦n⟧' := by
  have := isKInjective_sectionsS R f (resolution R L) (isKInjective_resolution R L)
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (sectionComplexIsoS R K L f).hom n) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e
  have e' : sectionHomologyEquiv R K L f n (ConcreteCategory.hom ((secC R K L f).homologyπ n) c) =
      ((srcExtIso R K f).inv ≫ cohomologyClassAddEquivShiftedHom _ _ n
        (homologyAddEquiv _ _ n (ConcreteCategory.hom
          (HomologicalComplex.homologyMap (sectionComplexIsoS R K L f).hom n)
          (ConcreteCategory.hom ((secC R K L f).homologyπ n) c)))) ≫ ((tgtExtIso R L f).hom)⟦n⟧' :=
    rfl
  rw [e', Category.assoc]
  congr 3
  exact (congrArg (homologyAddEquiv _ _ n) e).trans (homologyAddEquiv_homologyπ _ _ n _)

/-- **The identification of the values of the `Ext` presheaf commutes with restriction.** For
`D(g) ⊆ D(f)`, restricting a cohomology class of sections of the internal Hom complex from `D(f)`
to `D(g)` corresponds to derived base change along `R_f ⟶ R_g` of `Ext` classes. -/
theorem sectionHomologyEquiv_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) (n : ℤ)
    (x : ((secC R K L f).homology n : Type u)) :
    sectionHomologyEquiv R K L g n
        (ConcreteCategory.hom (HomologicalComplex.homologyMap (secRestrict R K L h) n) x) =
      localizedExtRestrict R K L h n (sectionHomologyEquiv R K L f n x) := by
  have := isKInjective_sectionsS R f (resolution R L) (isKInjective_resolution R L)
  have := isKInjective_sectionsS R g (resolution R L) (isKInjective_resolution R L)
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((secC R K L f).homologyπ n)).1
    inferInstance x
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (secRestrict R K L h) n) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e
  rw [e, sectionHomologyEquiv_homologyπ, sectionHomologyEquiv_homologyπ, cycleCocycle_restrict,
    cohomologyClassAddEquivShiftedHom_map]
  rw [localizedExtRestrict]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (srcExtIso_restrict R K h)]
  congr 3
  rw [Functor.commShiftIso_hom_naturality_assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Iso.app_hom,
    tgtExtIso_restrict]

end AlgebraicGeometry.AffineExt
