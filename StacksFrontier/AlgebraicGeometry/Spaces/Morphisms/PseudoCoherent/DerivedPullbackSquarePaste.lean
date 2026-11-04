module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeComparison

/-!
# Pasting the square isomorphisms of derived pullback

For a pseudofunctoriality datum `P` of derived pullback on algebraic spaces
(`AlgebraicGeometry.Space.DerivedPullbackComposition`), a commutative square
`u' ≫ t = t' ≫ u` has its square isomorphism `Lt'^* Lu^* ≅ Lu'^* Lt^*`
(`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso`).  This file proves that square
isomorphisms paste: for two squares stacked along a pair of factorisations `r ≫ t = q`, the
square isomorphism of the outer square is the composite of the two square isomorphisms and the
two composition comparisons.  It is the coherence that the descent of a glueing datum along the
stages of a directed system consumes, and it follows from the associativity coherence of `P`
alone.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPullbackComposition.limitComparisonIso`: the comparison over an
  intersection induced through an object downstairs.

## Main results

* `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_paste`.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.map_squareIso_conj_eq_of_paste`: the
  form in which a comparison over an intersection is moved down a stage.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DerivedPullbackComposition

variable (P : DerivedPullbackComposition B S hS)

/-- **Square isomorphisms paste.**  For two commutative squares stacked vertically,
`fl ≫ rU = rP ≫ fm` above `fm ≫ tU = tP ≫ fi`, with outer square `fl ≫ qU = qP ≫ fi` and
factorisations `rU ≫ tU = qU`, `rP ≫ tP = qP`, the square isomorphism of the outer square is the
composite of the comparison for `rP ≫ tP = qP`, the derived pullback along `rP` of the lower
square isomorphism, the upper square isomorphism, and the derived pullback along `fl` of the
comparison for `rU ≫ tU = qU`. -/
theorem squareIso_paste {Pl Pm Pi Ul Um Ui : AlgebraicSpaces B S hS}
    (rP : Pl ⟶ Pm) (tP : Pm ⟶ Pi) (qP : Pl ⟶ Pi) (hP : rP ≫ tP = qP)
    (rU : Ul ⟶ Um) (tU : Um ⟶ Ui) (qU : Ul ⟶ Ui) (hU : rU ≫ tU = qU)
    (fl : Pl ⟶ Ul) (fm : Pm ⟶ Um) (fi : Pi ⟶ Ui)
    (h₁ : fl ≫ rU = rP ≫ fm) (h₂ : fm ≫ tU = tP ≫ fi) (h₃ : fl ≫ qU = qP ≫ fi)
    (A : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Ui))
      _ _ (HasDerivedCategory.standard _)) :
    (P.squareIso fl qU qP fi h₃).hom.app A =
      (P.iso rP tP qP hP).inv.app ((smallEtaleDerivedModulePullback B S hS fi).obj A) ≫
        (smallEtaleDerivedModulePullback B S hS rP).map ((P.squareIso fm tU tP fi h₂).hom.app A) ≫
        (P.squareIso fl rU rP fm h₁).hom.app ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
        (smallEtaleDerivedModulePullback B S hS fl).map ((P.iso rU tU qU hU).hom.app A) := by
  have hk₁ : (fl ≫ rU) ≫ tU = fl ≫ qU := by rw [Category.assoc, hU]
  have hk₂ : rP ≫ (fm ≫ tU) = fl ≫ qU := by rw [← Category.assoc, ← h₁, Category.assoc, hU]
  have a₁ := congrArg Iso.hom (P.iso_assoc fl rU tU qU (fl ≫ rU) (fl ≫ qU) hU rfl hk₁ rfl A)
  have a₂ := congrArg Iso.hom (P.iso_assoc rP fm tU (fm ≫ tU) (fl ≫ rU) (fl ≫ qU) rfl h₁.symm
    hk₁ hk₂ A)
  have a₃ := congrArg Iso.hom (P.iso_assoc rP tP fi (fm ≫ tU) qP (fl ≫ qU) h₂.symm hP h₃.symm
    hk₂ A)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at a₁ a₂ a₃
  have b₁ : (smallEtaleDerivedModulePullback B S hS fl).map ((P.iso rU tU qU hU).hom.app A) =
      ((P.iso fl rU (fl ≫ rU) rfl).hom.app ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
        (P.iso (fl ≫ rU) tU (fl ≫ qU) hk₁).hom.app A) ≫
        (P.iso fl qU (fl ≫ qU) rfl).inv.app A := by
    rw [← Iso.app_inv, Iso.eq_comp_inv, Iso.app_hom]
    exact a₁.symm
  rw [squareIso_hom_app, squareIso_hom_app, squareIso_hom_app, b₁]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% a₂, ← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, ← reassoc_of% a₃, Iso.inv_hom_id_app_assoc]

/-- **The comparison over an intersection induced through an object downstairs.**  For squares
`fl ≫ qU = qP ≫ fi` and `gl ≫ qV = qP ≫ gi` and a square `gl ≫ jV = fl ≫ jU` over `Wl`, objects
`A` on `Ui` and `Bo` on `Vi` with `αU : Lq_U^*A ≅ Lj_U^*E` and `αV : Lq_V^*Bo ≅ Lj_V^*E` give an
isomorphism `Lq_P^*Lf_i^*A ≅ Lq_P^*Lg_i^*Bo`: the composite of the square isomorphisms with `αU`,
`αV⁻¹` and the square isomorphism at `E`. -/
def limitComparisonIso {Pl Pi Ul Ui Vl Vi Wl : AlgebraicSpaces B S hS}
    (fl : Pl ⟶ Ul) (qU : Ul ⟶ Ui) (qP : Pl ⟶ Pi) (fi : Pi ⟶ Ui) (h₃ : fl ≫ qU = qP ≫ fi)
    (gl : Pl ⟶ Vl) (qV : Vl ⟶ Vi) (gi : Pi ⟶ Vi) (k₃ : gl ≫ qV = qP ≫ gi)
    (jU : Ul ⟶ Wl) (jV : Vl ⟶ Wl) (w : gl ≫ jV = fl ≫ jU)
    (A : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Ui))
      _ _ (HasDerivedCategory.standard _))
    (Bo : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Vi))
      _ _ (HasDerivedCategory.standard _))
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Wl))
      _ _ (HasDerivedCategory.standard _))
    (αU : (smallEtaleDerivedModulePullback B S hS qU).obj A ≅
      (smallEtaleDerivedModulePullback B S hS jU).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS qV).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS jV).obj E) :
    (smallEtaleDerivedModulePullback B S hS qP).obj
        ((smallEtaleDerivedModulePullback B S hS fi).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS qP).obj
        ((smallEtaleDerivedModulePullback B S hS gi).obj Bo) :=
  (P.squareIso fl qU qP fi h₃).app A ≪≫ (smallEtaleDerivedModulePullback B S hS fl).mapIso αU ≪≫
    (P.squareIso gl jV fl jU w).app E ≪≫
    (smallEtaleDerivedModulePullback B S hS gl).mapIso αV.symm ≪≫
    ((P.squareIso gl qV qP gi k₃).app Bo).symm

/-- **Moving a comparison down a stage.**  Two stacked squares over the open piece
(`fl ≫ rU = rP ≫ fm` above `fm ≫ tU = tP ≫ fi`) and two over the étale piece
(`gl ≫ rV = rP ≫ gm` above `gm ≫ tV = tP ≫ gi`) share their maps `rP`, `tP` of the
intersections.  Let `c : Lt_P^*Lf_i^*A ≅ Lt_P^*Lg_i^*Bo` be an isomorphism whose image under the
map attached to `rP ≫ tP = qP` is the comparison
`AlgebraicGeometry.Space.DerivedPullbackComposition.limitComparisonIso` for the outer squares.
Then the isomorphism `cm : Lf_m^*Lt_U^*A ≅ Lg_m^*Lt_V^*Bo` obtained from `c` through the two lower
square isomorphisms has derived pullback along `rP` the same composite for the two upper squares,
with `αU` and `αV` precomposed with the comparisons for `rU ≫ tU = qU` and `rV ≫ tV = qV`. -/
theorem map_squareIso_conj_eq_of_paste {Pl Pm Pi Ul Um Ui Vl Vm Vi Wl : AlgebraicSpaces B S hS}
    (rP : Pl ⟶ Pm) (tP : Pm ⟶ Pi) (qP : Pl ⟶ Pi) (hP : rP ≫ tP = qP)
    (rU : Ul ⟶ Um) (tU : Um ⟶ Ui) (qU : Ul ⟶ Ui) (hU : rU ≫ tU = qU)
    (rV : Vl ⟶ Vm) (tV : Vm ⟶ Vi) (qV : Vl ⟶ Vi) (hV : rV ≫ tV = qV)
    (fl : Pl ⟶ Ul) (fm : Pm ⟶ Um) (fi : Pi ⟶ Ui)
    (h₁ : fl ≫ rU = rP ≫ fm) (h₂ : fm ≫ tU = tP ≫ fi) (h₃ : fl ≫ qU = qP ≫ fi)
    (gl : Pl ⟶ Vl) (gm : Pm ⟶ Vm) (gi : Pi ⟶ Vi)
    (k₁ : gl ≫ rV = rP ≫ gm) (k₂ : gm ≫ tV = tP ≫ gi) (k₃ : gl ≫ qV = qP ≫ gi)
    (jU : Ul ⟶ Wl) (jV : Vl ⟶ Wl) (w : gl ≫ jV = fl ≫ jU)
    (A : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Ui))
      _ _ (HasDerivedCategory.standard _))
    (Bo : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Vi))
      _ _ (HasDerivedCategory.standard _))
    (E : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Wl))
      _ _ (HasDerivedCategory.standard _))
    (αU : (smallEtaleDerivedModulePullback B S hS qU).obj A ≅
      (smallEtaleDerivedModulePullback B S hS jU).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS qV).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS jV).obj E)
    (αUm : (smallEtaleDerivedModulePullback B S hS rU).obj
        ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS jU).obj E)
    (hαUm : αUm.hom = (P.iso rU tU qU hU).hom.app A ≫ αU.hom)
    (αVm : (smallEtaleDerivedModulePullback B S hS rV).obj
        ((smallEtaleDerivedModulePullback B S hS tV).obj Bo) ≅
      (smallEtaleDerivedModulePullback B S hS jV).obj E)
    (hαVm : αVm.hom = (P.iso rV tV qV hV).hom.app Bo ≫ αV.hom)
    (c : (smallEtaleDerivedModulePullback B S hS tP).obj
        ((smallEtaleDerivedModulePullback B S hS fi).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS tP).obj
        ((smallEtaleDerivedModulePullback B S hS gi).obj Bo))
    (hc : P.factorHom rP tP qP hP _ _ c.hom =
      (P.limitComparisonIso fl qU qP fi h₃ gl qV gi k₃ jU jV w A Bo E αU αV).hom)
    (cm : (smallEtaleDerivedModulePullback B S hS fm).obj
        ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≅
      (smallEtaleDerivedModulePullback B S hS gm).obj
        ((smallEtaleDerivedModulePullback B S hS tV).obj Bo))
    (hcm : cm.hom = (P.squareIso fm tU tP fi h₂).inv.app A ≫ c.hom ≫
      (P.squareIso gm tV tP gi k₂).hom.app Bo) :
    (smallEtaleDerivedModulePullback B S hS rP).map cm.hom =
      (P.squareIso fl rU rP fm h₁).hom.app ((smallEtaleDerivedModulePullback B S hS tU).obj A) ≫
        (smallEtaleDerivedModulePullback B S hS fl).map αUm.hom ≫
        (P.squareIso gl jV fl jU w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS gl).map αVm.inv ≫
        (P.squareIso gl rV rP gm k₁).inv.app
          ((smallEtaleDerivedModulePullback B S hS tV).obj Bo) := by
  have hαVm' : αVm.inv = αV.inv ≫ (P.iso rV tV qV hV).inv.app Bo :=
    Iso.inv_ext (by rw [hαVm]; simp only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id_app, Functor.comp_obj])
  rw [hαUm, hαVm', hcm]
  have hc₀ : (smallEtaleDerivedModulePullback B S hS rP).map c.hom =
      (P.iso rP tP qP hP).hom.app _ ≫
        ((P.squareIso fl qU qP fi h₃).hom.app A ≫
          (smallEtaleDerivedModulePullback B S hS fl).map αU.hom ≫
          (P.squareIso gl jV fl jU w).hom.app E ≫
          (smallEtaleDerivedModulePullback B S hS gl).map αV.inv ≫
          (P.squareIso gl qV qP gi k₃).inv.app Bo) ≫
        (P.iso rP tP qP hP).inv.app _ := by
    have hc' := hc
    rw [factorHom, Iso.homCongr_apply, limitComparisonIso] at hc'
    simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Iso.symm_hom] at hc'
    rw [← hc']
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]
  have pU := P.squareIso_paste rP tP qP hP rU tU qU hU fl fm fi h₁ h₂ h₃ A
  have pV : (P.squareIso gl qV qP gi k₃).inv.app Bo =
      (smallEtaleDerivedModulePullback B S hS gl).map ((P.iso rV tV qV hV).inv.app Bo) ≫
        (P.squareIso gl rV rP gm k₁).inv.app ((smallEtaleDerivedModulePullback B S hS tV).obj Bo) ≫
        (smallEtaleDerivedModulePullback B S hS rP).map ((P.squareIso gm tV tP gi k₂).inv.app Bo) ≫
        (P.iso rP tP qP hP).hom.app ((smallEtaleDerivedModulePullback B S hS gi).obj Bo) := by
    rw [← Iso.app_inv]
    refine Iso.inv_ext ?_
    rw [Iso.app_hom, P.squareIso_paste rP tP qP hP rV tV qV hV gl gm gi k₁ k₂ k₃ Bo]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, hc₀, pU, pV, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end DerivedPullbackComposition

end AlgebraicGeometry.Space

end
