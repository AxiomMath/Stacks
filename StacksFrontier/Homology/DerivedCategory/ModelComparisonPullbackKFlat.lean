module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonQuotient

/-!
# The derived pullback at the two models, on K-flat complexes

For a morphism of ringed spaces `f : X ⟶ Y`, `StacksDraft.DerivedModel.derivedPullbackModelIso`
compares `Lf^*` at the standard model and at the locally small model of Tag 079Q through the
comparison equivalence `G`. On the class of a complex at which the comparison `Lf^* ⟶ f^*` is
invertible, in particular on a K-flat complex `K` ([Stacks, Tag 06YJ]), its component is the
canonical composite through `Q(f^* K)`: `G(Lf^*_std (Q K)) ≅ G(Q (f^* K)) = Q (f^* K) ≅
Lf^*_ls (Q K)`.

## Main results

* `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Qh_of_isIso` and
  `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Qh_of_kFlat` — the component at
  `Qh M`, through the comparisons of the two models at `M`.
* `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Q_comp` — at `Q K` for every complex
  `K`: the component followed by the comparison `Lf^*(Q K) ⟶ Q(f^* K)` at the locally small model
  is the image of that comparison at the standard model.
* `StacksDraft.DerivedModel.isIso_derivedPullback_map_quotientCompQhIso_inv_comp_of_kFlat` — that
  comparison is invertible on a K-flat complex, at any models.
* `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_Q_of_kFlat` — at `Q K` for `K`
  K-flat, the component is the canonical composite through `Q(f^* K)`.

The comparison `Lf^*(Q K) ⟶ Q(f^* K)` at a model is written out as the composite of
`DerivedCategory.quotientCompQhIso`, the comparison of the left derived functor at the class of
`K`, and `Functor.mapHomotopyCategoryFactors`; at the standard model it is
`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f K` by definition.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

namespace StacksDraft.DerivedModel

/-- The generic shape of `derivedPullbackModelIso_hom_app_Q_comp`. -/
private lemma hom_app_Q_comp_aux {D E E₁ : Type*} [Category D] [Category E] [Category E₁]
    (G : E₁ ⥤ E) (L : D ⥤ E) {a₁ b₁ c₁ d₁ e₁ : E₁} (u₁ : a₁ ⟶ b₁) (x₁ : b₁ ⟶ c₁)
    (y₁ : c₁ ⟶ d₁) (z₁ : d₁ ⟶ e₁) {A B B' : D} (q : A ⟶ B) (s : B ⟶ B') (r : A ⟶ B')
    (hr : q ≫ s = r) (φA : G.obj a₁ ⟶ L.obj A) (φB : G.obj b₁ ⟶ L.obj B)
    (hnat : G.map u₁ ≫ φB = φA ≫ L.map q) {P P' : E} (c : L.obj B' ⟶ P) (t : G.obj c₁ ⟶ P)
    (h₁ : φB ≫ L.map s ≫ c = G.map x₁ ≫ t) (y : P ⟶ P') (t' : G.obj d₁ ⟶ P')
    (h₂ : t ≫ y = G.map y₁ ≫ t') (z : P' ⟶ G.obj e₁) (h₃ : t' ≫ z = G.map z₁) :
    φA ≫ L.map r ≫ c ≫ y ≫ z = G.map (u₁ ≫ x₁ ≫ y₁ ≫ z₁) := by
  rw [← hr, L.map_comp, Category.assoc, ← Category.assoc φA, ← hnat, Category.assoc,
    reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp

/-- The generic shape of `derivedPullbackModelIso_hom_app_Q_of_kFlat`. -/
private lemma eq_comp_inv_aux {E : Type*} [Category E] {P Q R : E} (e : P ⟶ Q) (c : Q ⟶ R)
    [IsIso c] (t : P ⟶ R) (h : e ≫ c = t) : e = t ≫ inv c := by
  simp [← h]

/-- The generic shape of `derivedPullbackModelIso_hom_app_Qh_of_isIso`. -/
private lemma eq_comp_inv_comp_map_aux {D E : Type*} [Category D] [Category E] (L : D ⥤ E)
    {P Q R : E} {B B' : D} (e : P ⟶ L.obj B) (s : B' ≅ B) (c : L.obj B' ⟶ R) [IsIso c]
    (t₁ : P ⟶ Q) (t₂ : Q ⟶ R) (h : e ≫ L.map s.inv ≫ c = t₁ ≫ t₂) :
    e = t₁ ≫ t₂ ≫ inv c ≫ L.map s.hom := by
  rw [← Category.assoc t₁, ← h]
  simp [← L.map_comp]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`derivedPullbackModelIso` at the class of an object of the homotopy category**, where the
comparison `Lf^* ⟶ f^*` at the locally small model is invertible: the image of the comparison at
the standard model, then the inverse of the comparison at the locally small model, conjugated by
the identifications `shrinkComparisonQhIso` of the two localizations. -/
theorem derivedPullbackModelIso_hom_app_Qh_of_isIso
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    [IsIso ((@derivedPullbackComparison X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app M)] :
    (derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj M) =
      (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing
          X))).functor.map
          ((@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) inferInstance).app M) ≫
        (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        CategoryTheory.inv ((@derivedPullbackComparison X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app
              M) ≫
        (@derivedPullback X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            _)
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
          ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).hom.app M) :=
  eq_comp_inv_comp_map_aux _ _
    ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).app M) _ _ _
    (derivedPullbackModelIso_hom_app_comp f M)

/-- **`derivedPullbackModelIso` at the class of a K-flat complex** ([Stacks, Tag 06YJ]): the
comparison `Lf^* ⟶ f^*` at the locally small model is invertible there, so
`derivedPullbackModelIso_hom_app_Qh_of_isIso` applies. -/
theorem derivedPullbackModelIso_hom_app_Qh_of_kFlat
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    (derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing
          X))).functor.map
          ((@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) inferInstance).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        @CategoryTheory.inv _ _ _ _ ((@derivedPullbackComparison X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
          (@Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
            X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) K hK) ≫
        (@derivedPullback X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
            _)
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
          ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  @derivedPullbackModelIso_hom_app_Qh_of_isIso _ _ f _
    (@Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) K hK)

/-- **`derivedPullbackModelIso` at `Q K`, for every complex `K`.** The component, followed by the
comparison `Lf^*(Q K) ⟶ Q(f^* K)` at the locally small model, is the image under the comparison
equivalence of the comparison `Lf^*(Q K) ⟶ Q(f^* K)` at the standard model. Each comparison is
written out as `quotientCompQhIso`, the comparison of the left derived functor at the class of
`K`, and `mapHomotopyCategoryFactors`. -/
theorem derivedPullbackModelIso_hom_app_Q_comp
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K) ≫
      (@derivedPullback X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
        ((@DerivedCategory.quotientCompQhIso _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).inv.app K) ≫
      (@derivedPullbackComparison X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (@DerivedCategory.Qh _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).map
        (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (@DerivedCategory.quotientCompQhIso _ _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing
        X))).functor.map
      ((@derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance).map
          ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).inv.app K) ≫
        (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) inferInstance).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  hom_app_Q_comp_aux
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing X))).functor
    (@derivedPullback X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    ((@derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        inferInstance).map
      ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).inv.app K))
    ((@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K))
    ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing
        Y))).functor.map
      ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).inv.app K))
    ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    ((@DerivedCategory.quotientCompQhIso _ _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).inv.app K)
    (map_quotientCompQhIso_inv_app_comp_shrinkComparisonQhIso_inv_app _ K)
    ((derivedPullbackModelIso f).hom.app
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K))
    ((derivedPullbackModelIso f).hom.app
      ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    ((derivedPullbackModelIso f).hom.naturality
      ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).inv.app K))
    ((@derivedPullbackComparison X Y f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (derivedPullbackModelIso_hom_app_comp f _)
    ((@DerivedCategory.Qh _ _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).map
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K))
    ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.naturality
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K)).symm
    ((@DerivedCategory.quotientCompQhIso _ _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (shrinkComparisonQhIso_inv_app_quotient_comp _ _)

/-- **The comparison `Lf^*(Q K) ⟶ Q(f^* K)` is invertible on a K-flat complex**, at any models of
the two derived categories, passed explicitly ([Stacks, Tag 06YJ]). The comparison is written out
as `quotientCompQhIso`, the comparison of the left derived functor at the class of `K`, and
`mapHomotopyCategoryFactors`. -/
theorem isIso_derivedPullback_map_quotientCompQhIso_inv_comp_of_kFlat
    (hX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
    (hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    IsIso ((@derivedPullback X Y f hX hY inferInstance).map
          ((@DerivedCategory.quotientCompQhIso _ _ _ hY).inv.app K) ≫
        (@derivedPullbackComparison X Y f hX hY inferInstance).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (@DerivedCategory.Qh _ _ _ hX).map
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (@DerivedCategory.quotientCompQhIso _ _ _ hX).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  IsIso.comp_isIso'
    (Iso.isIso_hom ((@derivedPullback X Y f hX hY inferInstance).mapIso
      ((@DerivedCategory.quotientCompQhIso _ _ _ hY).app K).symm))
    (IsIso.comp_isIso'
      (@Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
        X Y f hX hY K hK)
      (IsIso.comp_isIso'
        (Iso.isIso_hom ((@DerivedCategory.Qh _ _ _ hX).mapIso
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)))
        (Iso.isIso_hom ((@DerivedCategory.quotientCompQhIso _ _ _ hX).app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))))

/-- **`derivedPullbackModelIso` at `Q K`, for `K` K-flat, is the canonical composite through
`Q(f^* K)`**: the image under the comparison equivalence of the comparison
`Lf^*(Q K) ⟶ Q(f^* K)` at the standard model, followed by the inverse of the comparison at the
locally small model, which is invertible by [Stacks, Tag 06YJ]. -/
theorem derivedPullbackModelIso_hom_app_Q_of_kFlat
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    (derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj K) =
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing
        X))).functor.map
      ((@derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance).map
          ((@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).inv.app K) ≫
        (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
            (HasDerivedCategory.standard _) inferInstance).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (@DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      @CategoryTheory.inv _ _ _ _ ((@derivedPullback X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
          ((@DerivedCategory.quotientCompQhIso _ _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).inv.app K) ≫
        (@derivedPullbackComparison X Y f
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (@DerivedCategory.Qh _ _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).map
          (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (@DerivedCategory.quotientCompQhIso _ _ _
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        (isIso_derivedPullback_map_quotientCompQhIso_inv_comp_of_kFlat f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) K hK) :=
  @eq_comp_inv_aux _ _ _ _ _ _ _
    (isIso_derivedPullback_map_quotientCompQhIso_inv_comp_of_kFlat f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) K hK) _
    (derivedPullbackModelIso_hom_app_Q_comp f K)

end StacksDraft.DerivedModel

end
