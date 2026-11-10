module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroBlockInclusionTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision

/-!
# `H⁰(Y_k̄, M|_{Y_k̄})` for `Y` finite over a finite field, with its Frobenius

Let `Y` be finite over a finite field `k`, `k̄` an algebraically closed extension of `k` and `M` a
sheaf of `Λ`-modules on `Y_étale`. The direct image along the finite morphism `Y_k̄ ⟶ Spec k̄` and
global sections over `Spec k̄` are exact, so `RΓ(Y_k̄, M|_{Y_k̄})` is computed by the complex of
global sections of `M|_{Y_k̄}` (`CategoryTheory.Functor.exactTwistIso`), which is concentrated in
degree `0`. Hence

`H⁰(Y_k̄, M|_{Y_k̄}) ≅ M|_{Y_k̄}(Y_k̄)`,

naturally in `M`, and the canonical Frobenius `π_Y^*` on the left is the canonical Frobenius twist
`Stacks.EtaleCohomology.sectionsTwistEndo` on the right.

The standard model `HasDerivedCategory.standard` is used because the canonical Frobenius action
`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo` is defined there.

## Main definitions

* `Stacks.EtaleCohomology.homologyZeroIsoXOfZero`: `H⁰(K) ≅ K⁰` when both differentials at `0`
  vanish.
* `Stacks.EtaleCohomology.geometricFibreCohomologyZeroIso`:
  `H⁰(Y_k̄, M|_{Y_k̄}) ≅ M|_{Y_k̄}(Y_k̄)`, and its functorial form
  `Stacks.EtaleCohomology.geometricFibreCohomologyZeroNatIso`.

## Main results

* `Stacks.EtaleCohomology.geometricFibreCohomologyZeroIso_hom_naturality`: it is natural in `M`.
* `Stacks.EtaleCohomology.geometricFibreCohomologyZeroIso_hom_frobenius`: it carries `π_Y^*` to
  the canonical Frobenius twist on sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### `H⁰` of a complex with vanishing differentials at `0` -/

section Homology

variable {A : Type*} [Category* A] [Abelian A]

/-- `H⁰(K) ≅ K⁰` for a cochain complex whose differentials into and out of degree `0` vanish. -/
def homologyZeroIsoXOfZero (K : CochainComplex A ℤ) (h₁ : K.d (-1) 0 = 0) (h₂ : K.d 0 1 = 0) :
    K.homology 0 ≅ K.X 0 :=
  (K.isoHomologyπ (-1) 0 (by simp) h₁).symm ≪≫ K.iCyclesIso 0 1 (by simp) h₂

/-- `homologyZeroIsoXOfZero` is natural in morphisms of complexes. -/
lemma homologyMap_comp_homologyZeroIsoXOfZero_hom {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (hK₁ : K.d (-1) 0 = 0) (hK₂ : K.d 0 1 = 0) (hL₁ : L.d (-1) 0 = 0) (hL₂ : L.d 0 1 = 0) :
    HomologicalComplex.homologyMap φ 0 ≫ (homologyZeroIsoXOfZero L hL₁ hL₂).hom =
      (homologyZeroIsoXOfZero K hK₁ hK₂).hom ≫ φ.f 0 := by
  rw [← cancel_epi (K.homologyπ 0)]
  simp [homologyZeroIsoXOfZero]

end Homology

/-! ### Pasting squares, on variables -/

section Paste

variable {C : Type*} [Category* C]

/-- Pasting five commutative squares along the top and bottom rows. -/
lemma paste_five_squares_comm {X₀ X₁ X₂ X₃ X₄ X₅ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : C}
    (e₁ : X₀ ⟶ X₁) (e₂ : X₁ ⟶ X₂) (e₃ : X₂ ⟶ X₃) (e₄ : X₃ ⟶ X₄) (e₅ : X₄ ⟶ X₅)
    (f₁ : Y₀ ⟶ Y₁) (f₂ : Y₁ ⟶ Y₂) (f₃ : Y₂ ⟶ Y₃) (f₄ : Y₃ ⟶ Y₄) (f₅ : Y₄ ⟶ Y₅)
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (a₃ : X₃ ⟶ Y₃) (a₄ : X₄ ⟶ Y₄) (a₅ : X₅ ⟶ Y₅)
    (h₁ : a₀ ≫ f₁ = e₁ ≫ a₁) (h₂ : a₁ ≫ f₂ = e₂ ≫ a₂) (h₃ : a₂ ≫ f₃ = e₃ ≫ a₃)
    (h₄ : a₃ ≫ f₄ = e₄ ≫ a₄) (h₅ : a₄ ≫ f₅ = e₅ ≫ a₅) :
    a₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = (e₁ ≫ e₂ ≫ e₃ ≫ e₄ ≫ e₅) ≫ a₅ := by
  simp only [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅, Category.assoc]

/-- A functor carries a commutative square to a commutative square. -/
lemma functor_map_comp_eq_of_comp_eq {D : Type*} [Category* D] (F : C ⥤ D) {X₀ X₁ Y₀ Y₁ : C}
    {a : X₀ ⟶ Y₀} {b : Y₀ ⟶ Y₁} {c : X₀ ⟶ X₁} {d : X₁ ⟶ Y₁} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end Paste

/-! ### `H⁰(Y_k̄, M|_{Y_k̄})` -/

section Sections

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom]

omit [Fintype k] [IsAlgClosed kbar] [Etale Y.hom] [IsFinite Y.hom] in
/-- The terms of the complex of global sections of `M|_{Y_k̄}` vanish outside degree `0`. -/
lemma isZero_frobeniusRestrictionSectionsComplex_X (M : EtaleModules.{u, 0} Λ Y.left) {n : ℤ}
    (hn : n ≠ 0) :
    IsZero
      ((frobeniusRestrictionSectionsComplex Λ Y kbar ((sheafSingleComplex Λ).obj M)).obj.X n) := by
  change IsZero ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
    ((etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M).X n))))
  exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)))

omit [Fintype k] [IsAlgClosed kbar] [Etale Y.hom] [IsFinite Y.hom] in
/-- The differential of the complex of global sections of `M|_{Y_k̄}` from degree `-1` to degree
`0` is zero. -/
lemma frobeniusRestrictionSectionsComplex_d_neg_one (M : EtaleModules.{u, 0} Λ Y.left) :
    (frobeniusRestrictionSectionsComplex Λ Y kbar ((sheafSingleComplex Λ).obj M)).obj.d (-1) 0 =
      0 :=
  (isZero_frobeniusRestrictionSectionsComplex_X Λ Y kbar M (by norm_num)).eq_of_src _ _

omit [Fintype k] [IsAlgClosed kbar] [Etale Y.hom] [IsFinite Y.hom] in
/-- The differential of the complex of global sections of `M|_{Y_k̄}` from degree `0` to degree `1`
is zero. -/
lemma frobeniusRestrictionSectionsComplex_d_zero (M : EtaleModules.{u, 0} Λ Y.left) :
    (frobeniusRestrictionSectionsComplex Λ Y kbar ((sheafSingleComplex Λ).obj M)).obj.d 0 1 = 0 :=
  (isZero_frobeniusRestrictionSectionsComplex_X Λ Y kbar M (by norm_num)).eq_of_tgt _ _

/-- **`H⁰(Y_k̄, M|_{Y_k̄}) ≅ M|_{Y_k̄}(Y_k̄)`** for `Y` finite étale over `k`: `RΓ(Y_k̄, -)` is
computed by global sections, termwise, and the complex is `M` placed in degree `0`. -/
def geometricFibreCohomologyZeroIso (M : EtaleModules.{u, 0} Λ Y.left) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0).obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
            (fieldBaseChangeRestriction.{u, 0} Λ Y kbar ((sheafSingleComplex Λ).obj M)))) ≅
      (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).obj M :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).mapIso
      (Functor.exactTwistIso
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((sheafSingleComplex Λ).obj M))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) 0).app _ ≪≫
    homologyZeroIsoXOfZero _ (frobeniusRestrictionSectionsComplex_d_neg_one Λ Y kbar M)
      (frobeniusRestrictionSectionsComplex_d_zero Λ Y kbar M) ≪≫
    (sectionsIso Λ Y kbar).app _ ≪≫
    (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)

omit [Fintype k] [Etale Y.hom] in
/-- **`geometricFibreCohomologyZeroIso` is natural in the sheaf.** -/
lemma geometricFibreCohomologyZeroIso_hom_naturality {M M' : EtaleModules.{u, 0} Λ Y.left}
    (φ : M ⟶ M') :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0).map
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
            ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
              ((sheafSingleComplex Λ).map φ)))) ≫
        (geometricFibreCohomologyZeroIso Λ Y kbar M').hom =
      (geometricFibreCohomologyZeroIso Λ Y kbar M).hom ≫
        (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).map φ := by
  set F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
  set F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))
  set ψ := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
    ((sheafSingleComplex Λ).map φ)
  set g := F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map ψ)
  have := Functor.isIso_twistComparison_of_exact F₁ F₂
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ((sheafSingleComplex Λ).obj M))
  have := Functor.isIso_twistComparison_of_exact F₁ F₂
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ((sheafSingleComplex Λ).obj M'))
  have hT := Functor.twistComparison_naturality F₁ F₂ ψ
  have hT' : CategoryTheory.inv (Functor.twistComparison F₁ F₂ _) ≫ DerivedCategory.Plus.Q.map g =
      F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ψ)) ≫ CategoryTheory.inv (Functor.twistComparison F₁ F₂ _) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hT
  have h₁ := functor_map_comp_eq_of_comp_eq (DerivedCategory.Plus.ι ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0) hT'.symm
  have h₂ := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) 0).hom.naturality g.hom
  simp only [Functor.comp_map] at h₂
  have h₃ := homologyMap_comp_homologyZeroIsoXOfZero_hom g.hom
    (frobeniusRestrictionSectionsComplex_d_neg_one Λ Y kbar M)
    (frobeniusRestrictionSectionsComplex_d_zero Λ Y kbar M)
    (frobeniusRestrictionSectionsComplex_d_neg_one Λ Y kbar M')
    (frobeniusRestrictionSectionsComplex_d_zero Λ Y kbar M')
  have h₄ := (sectionsIso Λ Y kbar).hom.naturality
    (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ).f 0)
  have h₅ : (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).map
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ).f 0) ≫
      (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M').hom =
      (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
      (restrictionSections Λ Y kbar (baseChangeTop Y kbar)).map φ := by
    rw [← Functor.map_comp, ← Functor.map_comp, HomologicalComplex.single_map_f_self,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact paste_five_squares_comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅

/-- **`H⁰(Y_k̄, -|_{Y_k̄}) ≅ Γ(Y_k̄, -|_{Y_k̄})`** as a natural isomorphism of functors of the
sheaf on `Y`. -/
def geometricFibreCohomologyZeroNatIso :
    sheafSingleComplex Λ ⋙ fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) ⋙
        etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0 ≅
      restrictionSections Λ Y kbar (baseChangeTop Y kbar) :=
  NatIso.ofComponents (geometricFibreCohomologyZeroIso Λ Y kbar)
    (fun φ => geometricFibreCohomologyZeroIso_hom_naturality Λ Y kbar φ)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [Etale Y.hom] [CharP kbar p] in
/-- **`geometricFibreCohomologyZeroIso` carries `π_Y^*` to the canonical Frobenius twist on
sections.** -/
lemma geometricFibreCohomologyZeroIso_hom_frobenius (M : EtaleModules.{u, 0} Λ Y.left) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0).map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
          ((sheafSingleComplex Λ).obj M)) ≫
        (geometricFibreCohomologyZeroIso Λ Y kbar M).hom =
      (geometricFibreCohomologyZeroIso Λ Y kbar M).hom ≫
        (sectionsTwistEndo Λ Y kbar p q hcard).app M := by
  set E := frobeniusRestrictionSectionsEndo Λ Y kbar p q hcard ((sheafSingleComplex Λ).obj M)
  have h₁ := functor_map_comp_eq_of_comp_eq
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0)
    (Functor.exactTwistIso_hom_comp
      (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
      (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
        (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((sheafSingleComplex Λ).obj M))
      (frobeniusRestrictionTwist Λ Y kbar p q hcard ((sheafSingleComplex Λ).obj M)))
  have h₂ := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) 0).hom.naturality E.hom
  simp only [Functor.comp_map] at h₂
  have h₃ := homologyMap_comp_homologyZeroIsoXOfZero_hom E.hom
    (frobeniusRestrictionSectionsComplex_d_neg_one Λ Y kbar M)
    (frobeniusRestrictionSectionsComplex_d_zero Λ Y kbar M)
    (frobeniusRestrictionSectionsComplex_d_neg_one Λ Y kbar M)
    (frobeniusRestrictionSectionsComplex_d_zero Λ Y kbar M)
  have h₄ := frobeniusRestrictionSectionsEndo_f_comp_sectionsIso_hom Λ Y kbar p q hcard
    ((sheafSingleComplex Λ).obj M) 0
  have h₅ := (sectionsTwistEndo Λ Y kbar p q hcard).naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom
  exact paste_five_squares_comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅.symm

end Sections

end Stacks.EtaleCohomology

end
