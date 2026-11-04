module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedPullComparisonComp
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomQuotient

/-!
# The composition comparison of derived pullbacks, read on complexes degreewise

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces and a complex `N` of
`𝒪_Z`-modules, the composition comparison of the derived pullback datum at `N`, followed by the
comparison of the derived pullback along `f ≫ g` with degreewise pullback, is the comparison along
`g` pushed along `f`, the comparison along `f`, and the localization of the degreewise composition
comparison of pullbacks of modules: the inverse of the compositor
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of Stacks 03D6 followed by the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`, which is the inverse of the composition
comparison of `AlgebraicGeometry.Space.modulePullbackDataTopos`
(`AlgebraicGeometry.Space.modulePullbackDataTopos_compIso_symm_eq`).

## Main results

* `Space.smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison_degreewise`:
  the composition comparison followed by the comparison with degreewise pullback, as above.

## Implementation notes

The degreewise comparison is kept in the spelling of the morphisms of ringed topoi: identifying it
with the comparison of `AlgebraicGeometry.Space.modulePullbackDataTopos` inside these statements
runs into elaboration timeouts.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

namespace AlgebraicGeometry.Space

/-- The identification of degreewise pullback read on the homotopy category, precomposed with the
homotopy quotient and localized, with degreewise pullback localized, is at a complex the
identification of the two localizations only. -/
theorem quotientCompQhIso_whisker_hom_app {V W : Type*} [Category V] [Abelian V]
    [Category W] [Abelian W] [HasDerivedCategory W] (F : V ⥤ W) [F.Additive]
    (M : CochainComplex V ℤ) :
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
          DerivedCategory.Qh ≪≫
        Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient W (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso W)).hom.app M =
      (DerivedCategory.quotientCompQhIso W).hom.app ((F.mapHomologicalComplex _).obj M) := by
  change DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The inverse of `AlgebraicGeometry.Space.quotientCompQhIso_whisker_hom_app`. -/
theorem quotientCompQhIso_whisker_inv_app {V W : Type*} [Category V] [Abelian V]
    [Category W] [Abelian W] [HasDerivedCategory W] (F : V ⥤ W) [F.Additive]
    (M : CochainComplex V ℤ) :
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
          DerivedCategory.Qh ≪≫
        Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient W (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso W)).inv.app M =
      (DerivedCategory.quotientCompQhIso W).inv.app ((F.mapHomologicalComplex _).obj M) := by
  rw [← Iso.app_inv, ← Iso.app_inv, Iso.inv_eq_inv]
  exact quotientCompQhIso_whisker_hom_app F M

/-- A morphism of homotopy categories between quotients of complexes which is the quotient of a
morphism of complexes, conjugated by the identifications of the two localizations, is the
localization of that morphism. -/
theorem quotientCompQhIso_inv_app_comp_Qh_map_comp {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {A B : CochainComplex C ℤ}
    (x : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj B) (y : A ⟶ B)
    (hx : x = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map y) :
    (DerivedCategory.quotientCompQhIso C).inv.app A ≫ DerivedCategory.Qh.map x ≫
        (DerivedCategory.quotientCompQhIso C).hom.app B =
      DerivedCategory.Q.map y := by
  subst hx
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Replacing the outer factors of a threefold composite by equal ones, with the objects
abstract. -/
theorem comp_comp_congr_of_eq {D : Type*} [Category D] {A B C E : D} {a a' : A ⟶ B} {b : B ⟶ C}
    {c c' : C ⟶ E} {d : A ⟶ E} (ha : a = a') (hc : c = c') (h : a' ≫ b ≫ c' = d) :
    a ≫ b ≫ c = d := by
  subst ha hc
  exact h

/-- Replacing the last factor of a threefold composite by an equal one, with the objects
abstract. -/
theorem comp_comp_eq_of_eq_of_eq {D : Type*} [Category D] {A B C E : D} {l : A ⟶ E} {a : A ⟶ B}
    {b : B ⟶ C} {x y : C ⟶ E} (h₁ : l = a ≫ b ≫ x) (h₂ : x = y) : l = a ≫ b ≫ y := by
  rw [h₁, h₂]

section DerivedPull

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The composition isomorphism of degreewise pullbacks along morphisms of ringed topoi followed
by the transport `AlgebraicGeometry.Space.pullbackModulesCompTransport`, on the homotopy category
at the quotient of a complex, is the quotient of the same composite applied degreewise. -/
theorem smallEtalePullbackMapHomotopyCompIso_trans_hom_app_quotient (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    (pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
          (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
        ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g).hom
            (ComplexShape.up ℤ)).app N) :=
  pullbackMapHomotopyCompIso_trans_hom_app_quotient (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g) (pullbackModulesCompTransport B S hS f g) N
    _ rfl

/-- **The degreewise composition comparison of pullbacks of modules, read on the homotopy category
and conjugated by the identifications of the two localizations, is its localization**: the last
three factors of `Space.smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison`
are the localization of the inverse of the compositor of Stacks 03D6 followed by the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`, applied degreewise. -/
theorem quotientCompModulePullbackIso_conj_compIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    (quotientCompModulePullbackIso B S hS f).inv.app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
            (ComplexShape.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
        (quotientCompModulePullbackIso B S hS (f ≫ g)).hom.app N =
      (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
        ((NatTrans.mapHomologicalComplex
        ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g).hom
            (ComplexShape.up ℤ)).app N) := by
  exact comp_comp_congr_of_eq (quotientCompQhIso_whisker_inv_app _ _)
    (quotientCompQhIso_whisker_hom_app _ _) (quotientCompQhIso_inv_app_comp_Qh_map_comp _ _
    (smallEtalePullbackMapHomotopyCompIso_trans_hom_app_quotient B S hS f g N))

/-- **The composition comparison of derived pullbacks, read on complexes, degreewise.** At the
localization of a complex `N`, the composition comparison of the derived pullback datum followed
by the comparison of the derived pullback along `f ≫ g` with degreewise pullback is the comparison
along `g` pushed along `f`, the comparison along `f`, and the localization of the inverse of the
compositor of Stacks 03D6 followed by `AlgebraicGeometry.Space.pullbackModulesCompTransport`,
applied degreewise. -/
theorem smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison_degreewise
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app (DerivedCategory.Q.obj N) ≫
        (derivedPullComparison B S hS (f ≫ g)).app N =
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) f).map
          ((derivedPullComparison B S hS g).app N) ≫
        (derivedPullComparison B S hS f).app
          ((((modulePullbackDataTopos B S hS).pull g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
          ((NatTrans.mapHomologicalComplex
          ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g).hom
            (ComplexShape.up ℤ)).app N) :=
  comp_comp_eq_of_eq_of_eq
    (smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison B S hS f g N)
    (quotientCompModulePullbackIso_conj_compIso B S hS f g N)

end DerivedPull

end AlgebraicGeometry.Space

end
