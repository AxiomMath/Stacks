module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackRightUnitor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# The derived pullback of the structure sheaf along a composite

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi and
`e : (g ∘ f)^* ≅ h^*` an isomorphism of pullbacks of modules compatible with the
identifications `1 ≅ φ^*1` of the structure sheaves. Then the identifications
`Lφ^*(𝒪[0]) ≅ 𝒪[0]` are compatible with the composition law `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of
Stacks 0D6D followed by the action of `e`:

`Lf^*(Lg^*𝒪_Z) ≅ Lh^*𝒪_Z ≅ 𝒪_X` equals `Lf^*(Lg^*𝒪_Z) ≅ Lf^*𝒪_Y ≅ 𝒪_X`.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackComplex_map_pullbackSingleUnitMap`: the
  statement on the complexes `𝒪[0]`.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackCompIso_hom_app_unit_comp`: the
  statement on derived categories.

## Implementation notes

`𝒪_Z[0]` is a K-flat complex with flat terms, so every derived pullback in the statement is
computed on it by the comparison of Stacks 06YY, and the composition law is characterized there
by `derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app`. The
statement is then the image of an equation of maps of complexes concentrated in degree `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.Sheaves.RingedToposModules (pullbackModulesObjUnitIso)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c' c''

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}} {Z : RingedTopos.{u, c'', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (h : RingedToposHom X Z)

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- **The comparisons `φ^*(𝒪[0]) ⟶ 𝒪[0]` compose**: for `e : (g ∘ f)^* ≅ h^*` compatible with the
identifications `1 ≅ φ^*1`, the comparison for `h` after the compositor of Stacks 03D6 and `e` is
`f^*` of the comparison for `g` followed by the comparison for `f`. -/
theorem pullbackComplex_map_pullbackSingleUnitMap
    (e : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    (he : (pullbackModulesObjUnitIso h.toModulesHom).hom =
      (pullbackModulesObjUnitIso f.toModulesHom).hom ≫
        (f.toModulesHom.pullbackModules).map (pullbackModulesObjUnitIso g.toModulesHom).hom ≫
        (RingedToposHom.pullbackModulesCompIso f g).inv.app _ ≫ e.hom.app _) :
    (Functor.mapHomologicalComplexCompIso (RingedToposHom.pullbackModulesCompIso f g).symm
          (ComplexShape.up ℤ)).hom.app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) ≫
        (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app _ ≫
        pullbackSingleUnitMap h =
      (pullbackComplex f).map (pullbackSingleUnitMap g) ≫ pullbackSingleUnitMap f := by
  have key : (RingedToposHom.pullbackModulesCompIso f g).inv.app _ ≫ e.hom.app _ ≫
      (pullbackModulesObjUnitIso h.toModulesHom).inv =
      (f.toModulesHom.pullbackModules).map (pullbackModulesObjUnitIso g.toModulesHom).inv ≫
        (pullbackModulesObjUnitIso f.toModulesHom).inv := by
    simp only [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Category.assoc]
    rw [he, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have n₁ := (RingedToposHom.pullbackModulesCompIso f g).inv.naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).hom
  have n₂ := e.hom.naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).hom
  simp only [Functor.comp_map] at n₁
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, pullbackSingleUnitMap,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.map_comp, Category.assoc,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.symm_hom, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]
  rw [← reassoc_of% n₂, ← reassoc_of% n₁, reassoc_of% key]

omit [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J (Type u)] in
/-- `Lf^*(𝒪_D[0]) ≅ 𝒪_C[0]` written out: the comparison of Stacks 06YY between the two
localizations of `𝒪_D[0]`, followed by the image of the comparison of complexes. -/
lemma derivedPullbackUnitIsoGeneral_hom_eq_comparison :
    (derivedPullbackUnitIsoGeneral f).hom =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso _).inv.app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫
        (derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app ((pullbackComplex f).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫
        DerivedCategory.Q.map (pullbackSingleUnitMap f) := by
  rw [derivedPullbackUnitIsoGeneral_hom_eq]
  exact (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)] in
/-- The diagram chase behind `derivedPullbackCompIso_hom_app_unit_comp`, with every morphism a
variable. -/
private theorem unit_comp_chase {C D H K : Type*} [Category* C] [Category* D] [Category* H]
    [Category* K] (F : D ⥤ C) (Qh : H ⥤ C) (Q : K ⥤ C) (quot : K ⥤ H)
    {B₀ B₁ B₂ B₃ B₄ B₄' : D} {A₁ A₁' A₂ A₃ : C} {k₁ k₁' k₂ k₃ k₄ : K}
    {a : F.obj B₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ Qh.obj (quot.obj k₂)}
    {i : Qh.obj (quot.obj k₂) ⟶ Q.obj k₂} {p_h : k₂ ⟶ k₄}
    {a' : F.obj B₁ ⟶ A₁'} {b' : A₁' ⟶ A₃}
    {u₁ : B₀ ⟶ B₁} {u₂ : B₁ ⟶ B₂} {u₃ : B₂ ⟶ B₃} {u₄ : B₃ ⟶ B₄} {ιY : B₄' ≅ B₄}
    {y : F.obj B₂ ⟶ Qh.obj (quot.obj k₁)} {m : quot.obj k₁ ⟶ quot.obj k₂}
    {Φ₁ : k₁ ⟶ k₁'} {Φ₂ : k₁' ⟶ k₂} {j : Qh.obj (quot.obj k₁) ⟶ Q.obj k₁}
    {pg : k₁ ⟶ k₃} {p_f : k₃ ⟶ k₄} {wY : B₂ ⟶ B₄'} {r₆ : F.obj B₄' ⟶ Qh.obj (quot.obj k₃)}
    {w' : quot.obj k₁ ⟶ quot.obj k₃} {r₇ : Qh.obj (quot.obj k₃) ⟶ Q.obj k₃}
    (H₁ : F.map u₁ ≫ (a' ≫ b') = (a ≫ b) ≫ c)
    (H₂ : a' ≫ b' ≫ d = F.map u₂ ≫ y ≫ Qh.map m)
    (hm : m = quot.map (Φ₁ ≫ Φ₂))
    (H₃ : Qh.map (quot.map (Φ₁ ≫ Φ₂)) ≫ i = j ≫ Q.map (Φ₁ ≫ Φ₂))
    (Hc : Φ₁ ≫ Φ₂ ≫ p_h = pg ≫ p_f)
    (H₅a : wY ≫ ιY.hom = u₃ ≫ u₄)
    (H₅ : F.map wY ≫ r₆ = y ≫ Qh.map w')
    (H₅b : w' = quot.map pg)
    (H₆ : Qh.map (quot.map pg) ≫ r₇ = j ≫ Q.map pg) :
    a ≫ b ≫ (c ≫ d ≫ i ≫ Q.map p_h) =
      F.map (u₁ ≫ u₂ ≫ u₃ ≫ u₄) ≫ (F.map ιY.inv ≫ r₆ ≫ r₇ ≫ Q.map p_f) := by
  simp only [Category.assoc] at H₁
  have H₅a' : F.map u₃ ≫ F.map u₄ ≫ F.map ιY.inv = F.map wY := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, ← H₅a, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← reassoc_of% H₁, reassoc_of% H₂, hm, reassoc_of% H₃, ← Q.map_comp, Category.assoc, Hc,
    Q.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% H₅a', reassoc_of% H₅, H₅b, reassoc_of% H₆]

/-- **The identifications `Lφ^*(𝒪[0]) ≅ 𝒪[0]` are compatible with composition**: for
`e : (g ∘ f)^* ≅ h^*` compatible with the identifications `1 ≅ φ^*1`, the composition law
`Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D followed by the action of `e` and by
`Lh^*(𝒪_Z[0]) ≅ 𝒪_X[0]` is `Lf^*` of `Lg^*(𝒪_Z[0]) ≅ 𝒪_Y[0]` followed by
`Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`. -/
theorem derivedPullbackCompIso_hom_app_unit_comp
    (e : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    (he : (pullbackModulesObjUnitIso h.toModulesHom).hom =
      (pullbackModulesObjUnitIso f.toModulesHom).hom ≫
        (f.toModulesHom.pullbackModules).map (pullbackModulesObjUnitIso g.toModulesHom).hom ≫
        (RingedToposHom.pullbackModulesCompIso f g).inv.app _ ≫ e.hom.app _) :
    (derivedPullbackCompIso f g).hom.app ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) ≫
        (derivedPullbackIsoOfPullbackModulesIso e).hom.app _ ≫
        (derivedPullbackUnitIsoGeneral h).hom =
      (derivedPullback f).map (derivedPullbackUnitIsoGeneral g).hom ≫
        (derivedPullbackUnitIsoGeneral f).hom := by
  rw [derivedPullbackUnitIsoGeneral_hom_eq_comparison h,
    derivedPullbackUnitIsoGeneral_hom_eq_comparison g,
    derivedPullbackUnitIsoGeneral_hom_eq_comparison f, derivedPullbackCompIso_hom]
  exact unit_comp_chase (derivedPullback f) DerivedCategory.Qh DerivedCategory.Q
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (ιY := (DerivedCategory.quotientCompQhIso _).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    ((derivedPullbackCompComparison f g ≫
      (derivedPullbackIsoOfPullbackModulesIso e).hom).naturality
        ((DerivedCategory.quotientCompQhIso _).inv.app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))))
    (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app f g e
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))))
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm
    (DerivedCategory.quotientCompQhIso_hom_naturality _)
    (pullbackComplex_map_pullbackSingleUnitMap f g h e he)
    (DerivedCategory.quotientCompQhIso_hom_naturality (pullbackSingleUnitMap g))
    ((derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (pullbackSingleUnitMap g)))
    (Functor.mapHomotopyCategory_map _ _)
    (DerivedCategory.quotientCompQhIso_hom_naturality _)

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
