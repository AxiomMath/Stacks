module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# `Ext` out of the structure sheaf is cohomology

Let `X` be a scheme. Global sections of `𝒪_X`-modules are corepresented by the structure sheaf
`𝒪_X`: a morphism `𝒪_X ⟶ M` is determined by the image of the unit section, which is an
arbitrary global section of `M`. Hence the right derived functors of global sections are the
`Ext`-functors out of `𝒪_X`. This file records the vanishing form of that comparison.

## Main results

* `Stacks.AlgebraicGeometry.ExtUnit.sectionsForgetIsoCoyonedaUnit`: global sections, read as
  abelian groups, are corepresented by `𝒪_X`.
* `Stacks.AlgebraicGeometry.ExtUnit.subsingleton_ext_unit_of_isZero`: `Ext^n(𝒪_X, M)` vanishes
  when `H^n(X, M)` does.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ExtUnit

/-- If `T` preserves homology, the right derived functors of `G ⋙ T` are obtained by applying `T`
to the right derived functors of `G`. -/
def rightDerivedCompObjIso {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    (A : C) (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj A ≅ T.obj ((G.rightDerived n).obj A) := by
  let I := injectiveResolution A
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact I.isoRightDerivedObj (G ⋙ T) n ≪≫
    (HomologicalComplex.homologyFunctor E _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ T)) _).app I.cocomplex).symm ≪≫
    (K.sc n).mapHomologyIso T ≪≫
    T.mapIso (I.isoRightDerivedObj G n).symm

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X`, as a sheaf of `𝒪_X`-modules. -/
abbrev unitModule : SheafOfModules.{u} X.ringCatSheaf := SheafOfModules.unit X.ringCatSheaf

/-- Sections over `⊤`, in the `SheafOfModules` spelling of the category of `𝒪_X`-modules. -/
abbrev topSections :
    SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- Taking sections over `⊤` is additive. -/
instance additive_topSections : (topSections X).Additive := ⟨fun {_ _ _ _} => rfl⟩

/-- A morphism out of the structure sheaf is determined by the image of the unit section over
`⊤`, and every global section arises. -/
def unitHomAddEquiv (M : SheafOfModules.{u} X.ringCatSheaf) :
    M.val.obj (op ⊤) ≃+ (unitModule X ⟶ M) := by
  let e : (unitModule X ⟶ M) →+ M.val.obj (op ⊤) :=
    { toFun := fun φ => (SheafOfModules.Hom.val φ).app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op ⊤))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine AddEquiv.symm (AddEquiv.ofBijective e ⟨?_, ?_⟩)
  · intro φ ψ h
    apply (SheafOfModules.unitHomEquiv M).injective
    ext U
    have hφ := (M.unitHomEquiv φ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op
    have hψ := (M.unitHomEquiv ψ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op
    exact hφ.symm.trans ((congrArg (M.val.map _) h).trans hψ)
  · intro m
    refine ⟨(SheafOfModules.unitHomEquiv M).symm
      (PresheafOfModules.sectionsMk (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op m)
        (fun U V f => ?_)), ?_⟩
    · rw [← PresheafOfModules.map_comp_apply]
      rfl
    · change ((SheafOfModules.unitHomEquiv M) ((SheafOfModules.unitHomEquiv M).symm _)).val
        (op ⊤) = m
      rw [Equiv.apply_symm_apply]
      change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op (𝟙 (op ⊤)),
        PresheafOfModules.map_id]
      rfl

/-- The morphism `𝒪_X ⟶ M` attached to a global section `m` sends the unit section over `⊤` to
`m`. -/
@[simp]
theorem unitHomAddEquiv_app_one (M : SheafOfModules.{u} X.ringCatSheaf) (m : M.val.obj (op ⊤)) :
    (SheafOfModules.Hom.val (unitHomAddEquiv X M m)).app (op ⊤)
      (1 : X.ringCatSheaf.obj.obj (op ⊤)) = m :=
  (unitHomAddEquiv X M).symm_apply_apply m

/-- **Global sections are corepresented by the structure sheaf.** -/
def sectionsForgetIsoCoyonedaUnit :
    topSections X ⋙ forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) Ab.{u} ≅
      preadditiveCoyoneda.obj (op (unitModule X)) :=
  (NatIso.ofComponents (fun M => (unitHomAddEquiv X M).symm.toAddCommGrpIso) (by
    intro M N f
    ext φ
    rfl)).symm

/-- **`Ext^n(𝒪_X, M)` vanishes when `H^n(X, M)` does.** -/
theorem subsingleton_ext_unit_of_isZero [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (M : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (h : IsZero (((topSections X).rightDerived n).obj M)) :
    Subsingleton (Abelian.Ext.{u} (unitModule X) M n) := by
  let G := topSections X ⋙ forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) Ab.{u}
  have : G.Additive := Functor.additive_of_iso (sectionsForgetIsoCoyonedaUnit X).symm
  have : PreservesFiniteLimits G :=
    preservesFiniteLimits_of_natIso (sectionsForgetIsoCoyonedaUnit X).symm
  obtain ⟨e⟩ := ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived G (unitModule X)
    (sectionsForgetIsoCoyonedaUnit X) n
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (((Functor.map_isZero _ h).of_iso
    (rightDerivedCompObjIso (topSections X) (forget₂ _ Ab.{u}) M n)).of_iso (e.app M))

end Stacks.AlgebraicGeometry.ExtUnit

end
