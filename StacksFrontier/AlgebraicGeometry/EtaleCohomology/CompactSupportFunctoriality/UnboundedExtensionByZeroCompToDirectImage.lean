module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroCounitComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.DegreeZeroIsoUnit

/-!
# `Rj_! ⟶ Rj_*` along a composite of open immersions, on `D(X_étale, Λ)`

For open immersions `a : X ⟶ U` and `b : U ⟶ V` the map `j_! ⟶ j_*` of [Stacks, Tag 0F4L]
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroToDirectImage`) along `b ∘ a` is the composite
`(b ∘ a)_! ≅ b_! a_! ⟶ b_! a_* ⟶ b_* a_* ≅ (b ∘ a)_*`, on sheaves and on unbounded derived
categories. On sheaves this is a formal property of the adjoint triples `j_! ⊣ j^{-1} ⊣ j_*`.

## Main results

* `Stacks.EtaleCohomology.comp_toRightAdjoint_of_adjointTriples`: the formal statement, for
  three adjoint triples.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage`: the statement
  on sheaves.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_comp`: the
  statement on `D(X_étale, Λ)`.

## References

* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

section Algebra

/-- **The inclusions `j_! ⟶ j_*` of adjoint triples compose.** Let `La ⊣ Ra ⊣ Pa`,
`Lb ⊣ Rb ⊣ Pb` and `L ⊣ R ⊣ P` be adjoint triples whose first units are invertible, with
`L ≅ La ⋙ Lb`, `Rb ⋙ Ra ≅ R` and `Pa ⋙ Pb ≅ P` compatible with the units, and let `εa`, `εb`,
`ε` be the maps `unit ≫ P(unit⁻¹)` from the left to the right adjoints. Then `ε` is
`L ≅ La ⋙ Lb ⟶ La ⋙ Pb` through `εa` and `εb`, followed by `Pa ⋙ Pb ≅ P`. -/
theorem comp_toRightAdjoint_of_adjointTriples {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] {La : C₁ ⥤ C₂} {Ra : C₂ ⥤ C₁} {Pa : C₁ ⥤ C₂} {Lb : C₂ ⥤ C₃} {Rb : C₃ ⥤ C₂}
    {Pb : C₂ ⥤ C₃} {L : C₁ ⥤ C₃} {R : C₃ ⥤ C₁} {P : C₁ ⥤ C₃} (a₁ : La ⊣ Ra) (a₂ : Ra ⊣ Pa)
    (b₁ : Lb ⊣ Rb) (b₂ : Rb ⊣ Pb) (c₁ : L ⊣ R) (c₂ : R ⊣ P) [IsIso a₁.unit] [IsIso b₁.unit]
    [IsIso c₁.unit] (cL : L ≅ La ⋙ Lb) (cR : Rb ⋙ Ra ≅ R) (cP : Pa ⋙ Pb ≅ P)
    (εa : La ⟶ Pa) (εb : Lb ⟶ Pb) (ε : L ⟶ P)
    (hεa : ∀ F, εa.app F = a₂.unit.app (La.obj F) ≫ Pa.map (inv (a₁.unit.app F)))
    (hεb : ∀ F, εb.app F = b₂.unit.app (Lb.obj F) ≫ Pb.map (inv (b₁.unit.app F)))
    (hε : ∀ F, ε.app F = c₂.unit.app (L.obj F) ≫ P.map (inv (c₁.unit.app F)))
    (hP : ∀ M, c₂.unit.app M = b₂.unit.app M ≫ Pb.map (a₂.unit.app (Rb.obj M)) ≫
      cP.hom.app (Ra.obj (Rb.obj M)) ≫ P.map (cR.hom.app M))
    (hL : ∀ F, c₁.unit.app F = a₁.unit.app F ≫ Ra.map (b₁.unit.app (La.obj F)) ≫
      Ra.map (Rb.map (cL.inv.app F)) ≫ cR.hom.app (L.obj F)) (F : C₁) :
    cL.hom.app F ≫ Lb.map (εa.app F) ≫ εb.app (Pa.obj F) ≫ cP.hom.app F = ε.app F := by
  have hu : cR.hom.app (L.obj F) ≫ inv (c₁.unit.app F) =
      Ra.map (Rb.map (cL.hom.app F)) ≫ Ra.map (inv (b₁.unit.app (La.obj F))) ≫
        inv (a₁.unit.app F) := by
    rw [IsIso.comp_inv_eq, hL]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← Ra.map_comp_assoc,
      ← Rb.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have nbu : εa.app F ≫ b₁.unit.app (Pa.obj F) =
      b₁.unit.app (La.obj F) ≫ Rb.map (Lb.map (εa.app F)) := b₁.unit.naturality (εa.app F)
  have hb : Rb.map (Lb.map (εa.app F)) ≫ inv (b₁.unit.app (Pa.obj F)) =
      inv (b₁.unit.app (La.obj F)) ≫ εa.app F := by
    rw [eq_comm, IsIso.inv_comp_eq, ← Category.assoc, ← nbu, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have na : (Rb.map (cL.hom.app F) ≫ inv (b₁.unit.app (La.obj F))) ≫ a₂.unit.app (La.obj F) =
      a₂.unit.app (Rb.obj (L.obj F)) ≫
        Pa.map (Ra.map (Rb.map (cL.hom.app F) ≫ inv (b₁.unit.app (La.obj F)))) :=
    a₂.unit.naturality _
  have nb : (cL.hom.app F ≫ Lb.map (εa.app F)) ≫ b₂.unit.app (Lb.obj (Pa.obj F)) =
      b₂.unit.app (L.obj F) ≫ Pb.map (Rb.map (cL.hom.app F ≫ Lb.map (εa.app F))) :=
    b₂.unit.naturality _
  have nP : cP.hom.app (Ra.obj (Rb.obj (L.obj F))) ≫
      P.map (cR.hom.app (L.obj F) ≫ inv (c₁.unit.app F)) =
      Pb.map (Pa.map (cR.hom.app (L.obj F) ≫ inv (c₁.unit.app F))) ≫ cP.hom.app F :=
    (cP.hom.naturality _).symm
  rw [hε, hP, hεb]
  simp only [Category.assoc]
  rw [← P.map_comp, nP, hu, reassoc_of% nb]
  refine whisker_eq _ ?_
  simp only [← Pb.map_comp_assoc]
  congr 2
  rw [Rb.map_comp, Category.assoc, hb, hεa, ← Category.assoc (Rb.map (cL.hom.app F)),
    ← Category.assoc, na]
  simp only [Functor.map_comp, Category.assoc]

/-- The assembly of `etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_comp`, stated on
variables. -/
private theorem comp_unbounded_chain {D : Type*} [Category* D]
    {q₀ q₁ q₂ q₃ q₄ e₁ e₂ e₃ e₄ e₄' e₅ e₆ e₇ e₈ e₉ : D}
    (un : q₀ ⟶ e₁) (rab : e₁ ⟶ e₂) (Cc : e₂ ⟶ e₃) (EbX : e₃ ⟶ e₄) (εb₁ : e₄ ⟶ e₄')
    (εb₂ : e₄' ⟶ e₅) (l : e₅ ⟶ e₆)
    (hf : q₀ ⟶ e₂) (qc : q₀ ⟶ q₁) (gf : q₁ ⟶ e₇) (ebf : e₇ ⟶ e₃) (ebq : e₇ ⟶ e₈)
    (ebu : e₈ ⟶ e₄) (qGε : q₁ ⟶ q₂) (gf' : q₂ ⟶ e₈) (εbq : e₈ ⟶ e₉) (rbu : e₉ ⟶ e₅)
    (qεb : q₂ ⟶ q₃) (ub : q₃ ⟶ e₉) (qcP : q₃ ⟶ q₄) (uab : q₄ ⟶ e₆) (qε : q₀ ⟶ q₄)
    (h₁ : un ≫ rab = hf) (h₂ : hf ≫ Cc = qc ≫ gf ≫ ebf) (h₃ : ebf ≫ EbX = ebq ≫ ebu)
    (h₄ : gf ≫ ebq = qGε ≫ gf') (h₅ : ebu ≫ εb₁ ≫ εb₂ = εbq ≫ rbu)
    (h₆ : gf' ≫ εbq = qεb ≫ ub) (h₇ : ub ≫ rbu ≫ l = qcP ≫ uab)
    (hQ : qc ≫ qGε ≫ qεb ≫ qcP = qε) :
    un ≫ rab ≫ Cc ≫ EbX ≫ εb₁ ≫ εb₂ ≫ l = qε ≫ uab := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅,
    reassoc_of% h₆, h₇, ← hQ]
  simp only [Category.assoc]

end Algebra

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

section Sheaves

variable {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]

/-- **`j_! ⟶ j_*` along a composite of open immersions**, on sheaves of `Λ`-modules:
`(b ∘ a)_! ≅ b_! a_! ⟶ b_! a_* ⟶ b_* a_* ≅ (b ∘ a)_*` is the map along `b ∘ a`. -/
theorem etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).hom.app F ≫
        (etaleModuleExtensionByZero.{u, r} Λ b).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ a).app F) ≫
        (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ b).app
          ((etaleModuleDirectImage.{u, r} Λ a).obj F) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl).hom.app F =
      (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ (a ≫ b)).app F :=
  comp_toRightAdjoint_of_adjointTriples (etaleModuleExtensionByZeroAdj.{u, r} Λ a)
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ a) (etaleModuleExtensionByZeroAdj.{u, r} Λ b)
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ b)
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (a ≫ b))
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b) (etaleModuleRestrictionCompIso.{u, r} Λ a b)
    (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl) _ _ _
    (etaleModuleExtensionByZeroToDirectImage_app Λ a)
    (etaleModuleExtensionByZeroToDirectImage_app Λ b)
    (etaleModuleExtensionByZeroToDirectImage_app Λ (a ≫ b))
    (etaleModuleRestrictionDirectImageAdj_unit_comp Λ a b)
    (etaleModuleExtensionByZeroAdj_unit_comp Λ a b) F

end Sheaves

section Derived

/-- The map `j_! ⟶ Rj_*` on `D(U_étale, Λ)` for an open immersion `j`: the map `Rj_! ⟶ Rj_*`
read through `Rj_! ≅ j_!`. -/
abbrev etaleModuleExtensionByZeroToDirectImageUnbounded {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategory ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j :=
  (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).inv ≫
    etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j

/-- **`Rj_! ⟶ Rj_*` along a composite of open immersions**, on `D(X_étale, Λ)`: through
`R(b ∘ a)_! ≅ (b ∘ a)_! ≅ b_! ∘ a_!` it is `b_!` of `a_! ⟶ Ra_*`, followed by `b_! ⟶ Rb_*` at
`Ra_*` and by `Rb_* Ra_* ≅ R(b ∘ a)_*`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_comp {X U V : Scheme.{u}}
    (a : X ⟶ U) (b : U ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b] :
    etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ (a ≫ b) =
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ (a ≫ b) ≪≫
          Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
            (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b)).hom ≫
        Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImageUnbounded Λ a)
          (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a)
          (etaleModuleExtensionByZeroToDirectImageUnbounded Λ b) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ a b (a ≫ b) rfl).inv := by
  refine Functor.rightDerived_ext _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ (a ≫ b))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
    Category.assoc]
  let εaK := (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ a)
    (ComplexShape.up ℤ)).app K
  let ua := (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ a).app K
  have h₁ : (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ (a ≫ b)).app K ≫
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ (a ≫ b)).hom.app
        (DerivedCategory.Q.obj K) =
      (etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).mapDerivedCategoryFactors.inv.app K := by
    rw [etaleModuleDerivedExtensionByZeroUnboundedIso,
      Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor,
      Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app]
    simp
  have h₂ : (etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).mapDerivedCategoryFactors.inv.app K ≫
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
        (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b)).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).symm (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategoryFactors.inv.app
          (((etaleModuleExtensionByZero.{u, r} Λ a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory.map
          ((etaleModuleExtensionByZero.{u, r} Λ a).mapDerivedCategoryFactors.inv.app K) := by
    have hL : Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) (etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).mapDerivedCategory =
        (etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).mapDerivedCategoryFactors := rfl
    simp [Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso, Localization.liftNatTrans_app, hL]
  have h₃ : (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory.map
        ((etaleModuleExtensionByZero.{u, r} Λ a).mapDerivedCategoryFactors.inv.app K) ≫
      (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory.map
        ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ a).inv.app
            (DerivedCategory.Q.obj K) ≫
          (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ a).app
            (DerivedCategory.Q.obj K)) =
      (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory.map (DerivedCategory.Q.map εaK) ≫
        (etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategory.map ua :=
    ((Functor.map_comp _ _ _).symm.trans (congrArg _
      (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ a K))).trans
      (Functor.map_comp _ _ _)
  have h₄ := ((etaleModuleExtensionByZero.{u, r} Λ b).mapDerivedCategoryFactors.inv.naturality
    εaK).symm
  have h₅ := (etaleModuleExtensionByZeroToDirectImageUnbounded Λ b).naturality ua
  have h₆ := etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ b
    (((etaleModuleDirectImage.{u, r} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h₇ := conj_inv_chain _ _ _ _ _ _ _
    (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac Λ a b (a ≫ b) rfl K)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (Iso.hom_inv_id_app _ K)).trans (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app _ _)
  have hdeg : (NatIso.mapHomologicalComplex (etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).symm
          (ComplexShape.up ℤ)).inv.app K ≫
        ((etaleModuleExtensionByZero.{u, r} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).map
          εaK ≫
        (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ b)
          (ComplexShape.up ℤ)).app
          (((etaleModuleDirectImage.{u, r} Λ a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl) (ComplexShape.up ℤ)).hom.app K =
      (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ (a ≫ b))
          (ComplexShape.up ℤ)).app K := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Iso.symm_inv, εaK]
    exact etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ a b (K.X n)
  have hQ := congrArg DerivedCategory.Q.map hdeg
  simp only [Functor.map_comp] at hQ
  exact (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app Λ (a ≫ b) K).trans
    (comp_unbounded_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h₁ h₂ h₃ h₄ h₅ h₆ h₇.symm hQ).symm

end Derived

end Stacks.EtaleCohomology

end
