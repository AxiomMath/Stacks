module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence

/-!
# The derived tensor bifunctor at three independent universes

K-flat resolutions on a ringed site `AlgebraicGeometry.RingedSite.{c, v, w}`, the invariance of
the tensor product of K-flat complexes under quasi-isomorphisms, the derived category as a
localization of the K-flat complexes, and the derived tensor bifunctor
`Stacks.SheafOfModules.derivedTensorBifunctorGeneral` with its K-flat comparisons.
-/

/-! ### K-flat resolutions -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Every cochain complex of sheaves of modules on a ringed site receives a quasi-isomorphism
from a K-flat complex. This is the existence assertion of Stacks 06YS. -/
theorem exists_kFlat_quasiIso_general
    (G : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p :
      P ⟶ G),
      IsKFlat X.O P ∧ QuasiIso p :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize X.O G

end Stacks.SheafOfModules

end

/-! ### Tensoring with a quasi-isomorphism of K-flat complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- If a square of morphisms of complexes commutes and three of its sides are
quasi-isomorphisms, so is the fourth. -/
private theorem quasiIso_of_comp_eq_quasiIso_general
    {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] {A B C D : CochainComplex 𝒞 ℤ}
    (a : A ⟶ B) (b : B ⟶ D) (u : A ⟶ C) (v : C ⟶ D) (h : a ≫ b = u ≫ v)
    [QuasiIso a] [QuasiIso u] [QuasiIso v] : QuasiIso b := by
  have : QuasiIso (a ≫ b) := by
    rw [h]
    infer_instance
  exact (_root_.quasiIso_iff_comp_left a b).1 this

/-- A quasi-isomorphism `α` of K-flat complexes induces a quasi-isomorphism
`Tot(F ⊗ α)` for every complex `F`. This is Stacks 06YT. -/
theorem quasiIso_mapBifunctorMap_id_of_kFlat_right_general
    {P Q : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 F) α (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O)
      (ComplexShape.up ℤ)) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso_general X F
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O M hM α hα
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O Q hQ r hr
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O P hP r hr
  refine quasiIso_of_comp_eq_quasiIso_general
    (HomologicalComplex.mapBifunctorMap r (𝟙 P) _ _) _
    (HomologicalComplex.mapBifunctorMap (𝟙 M) α _ _)
    (HomologicalComplex.mapBifunctorMap r (𝟙 Q) _ _) ?_
  rw [HomologicalComplex.mapBifunctorMap_comp, HomologicalComplex.mapBifunctorMap_comp,
    Category.comp_id, Category.id_comp, Category.comp_id, Category.id_comp]

/-- A quasi-isomorphism `α` of K-flat complexes induces a quasi-isomorphism
`Tot(α ⊗ F)` for every complex `F`. This is the mirror image of Stacks 06YT. -/
theorem quasiIso_mapBifunctorMap_id_of_kFlat_left_general
    {P Q : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 F) (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O)
      (ComplexShape.up ℤ)) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso_general X F
  have := IsKFlat.quasiIso_mapBifunctorMap_id_right X.O M hM α hα
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O Q hQ r hr
  have := IsKFlat.quasiIso_mapBifunctorMap_id_left X.O P hP r hr
  refine quasiIso_of_comp_eq_quasiIso_general
    (HomologicalComplex.mapBifunctorMap (𝟙 P) r _ _) _
    (HomologicalComplex.mapBifunctorMap α (𝟙 M) _ _)
    (HomologicalComplex.mapBifunctorMap (𝟙 Q) r _ _) ?_
  rw [HomologicalComplex.mapBifunctorMap_comp, HomologicalComplex.mapBifunctorMap_comp,
    Category.comp_id, Category.id_comp, Category.comp_id, Category.id_comp]

/-- Stacks 06YT in the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling: the
quasi-isomorphism `α` of K-flat complexes sits in the right tensor slot. -/
theorem quasiIso_tensorComplex_obj_map_of_kFlat_general
    {P Q : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).map α) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso_general X F
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O M hM α hα
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O Q hQ r hr
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O P hP r hr
  exact quasiIso_of_comp_eq_quasiIso_general _ _ _ _
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map r).naturality α).symm

/-- Stacks 06YT in the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling, mirror image: the
quasi-isomorphism `α` of K-flat complexes sits in the left tensor slot. -/
theorem quasiIso_tensorComplex_map_app_of_kFlat_general
    {P Q : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (α : P ⟶ Q) (hα : QuasiIso α) (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q)
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map α).app F) := by
  obtain ⟨M, r, hM, hr⟩ := exists_kFlat_quasiIso_general X F
  have := IsKFlat.quasiIso_tensorComplex_map_app X.O M hM α hα
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O Q hQ r hr
  have := IsKFlat.quasiIso_tensorComplex_obj_map X.O P hP r hr
  exact quasiIso_of_comp_eq_quasiIso_general _ _ _ _
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map α).naturality r)

end Stacks.SheafOfModules

end

/-! ### The derived category as a localization of the K-flat complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Every object of the homotopy category receives a quasi-isomorphism from a K-flat one.
This is Stacks 06YS, stated as left resolutions for `Stacks.SheafOfModules.kFlatLocalizer`. -/
theorem kFlatLocalizer_hasLeftResolutions_general :
    (kFlatLocalizer.{c, v, w} X.O).HasLeftResolutions := by
  intro Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso_general X K
  exact ⟨{ X₁ := ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩
           w := (HomotopyCategory.quotient _ _).map p
           hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp }⟩

open ObjectProperty in
/-- The inclusion of the K-flat complexes into the homotopy category is a localized
equivalence: it induces an equivalence between the localization of the K-flat complexes at
their quasi-isomorphisms and the derived category. This is Stacks 0GSL applied to the K-flat
subcategory, whose hypotheses are Stacks 07A3 and Stacks 06YS. -/
theorem kFlatLocalizer_isLocalizedEquivalence_general :
    (kFlatLocalizer.{c, v, w} X.O).IsLocalizedEquivalence := by
  obtain ⟨hsat, hcompat⟩ :=
    quasiIso_isSaturated_and_isCompatibleWithTriangulation.{c, v, w} X.O
  let _ := hcompat
  exact (isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
      (kFlatObjects.{c, v, w} X.O)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      hsat).2.2 (kFlatLocalizer_hasLeftResolutions_general X)

variable [HasDerivedCategory.{d}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

/-- The functor from the K-flat complexes, as a subcategory of the homotopy category, to the
derived category. -/
abbrev kFlatQGeneral :
    (kFlatObjects.{c, v, w} X.O).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) :=
  (kFlatObjects X.O).ι ⋙ DerivedCategory.Qh

/-- The derived category of sheaves of modules on a ringed site is the localization of the
K-flat complexes at the quasi-isomorphisms between K-flat complexes. -/
theorem kFlatQ_isLocalization_general :
    (kFlatQGeneral.{c, v, w, d} X).IsLocalization (kFlatQuasiIso.{c, v, w} X.O) := by
  have := kFlatLocalizer_isLocalizedEquivalence_general X
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer X.O) DerivedCategory.Qh

end Stacks.SheafOfModules

end

/-! ### The derived tensor bifunctor -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- K-flatness as a property of cochain complexes of sheaves of modules. -/
abbrev kFlatComplexesGeneral :
    ObjectProperty (CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ) :=
  ObjectProperty.complexSubcategory (kFlatObjects.{c, v, w} X.O)

/-- `kFlatComplexesGeneral` is K-flatness of the complex. -/
theorem kFlatComplexes_iff_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatComplexesGeneral X K ↔ IsKFlat X.O K :=
  Iff.rfl

/-- A K-flat complex, as an object of the full subcategory of K-flat complexes. -/
abbrev kFlatObjGeneral
    (A : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) : (kFlatComplexesGeneral X).FullSubcategory :=
  ⟨A, hA⟩

variable [HasDerivedCategory.{d}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

attribute [local instance] kFlatQ_isLocalization_general
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex

/-- The functor from K-flat complexes to the derived category. -/
abbrev kFlatComplexQGeneral :
    (kFlatComplexesGeneral X).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (kFlatComplexesGeneral X).ι ⋙ DerivedCategory.Q

/-- The quasi-isomorphisms between K-flat complexes. -/
abbrev kFlatComplexQuasiIsoGeneral :
    MorphismProperty (kFlatComplexesGeneral X).FullSubcategory :=
  (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
        ℤ)).inverseImage
    (kFlatComplexesGeneral X).ι

/-- The derived category of sheaves of modules on a ringed site is the localization of the
K-flat complexes at the quasi-isomorphisms between them. -/
instance kFlatComplexQ_isLocalization_general :
    (kFlatComplexQGeneral X).IsLocalization (kFlatComplexQuasiIsoGeneral X) :=
  ObjectProperty.ι_comp_Q_isLocalization (kFlatObjects.{c, v, w} X.O)

/-- The total tensor product of a K-flat complex with an arbitrary complex, pushed into the
derived category. This is the bifunctor whose descent is the derived tensor product. -/
abbrev kFlatTensorToDerivedGeneral :
    (kFlatComplexesGeneral X).FullSubcategory ⥤
      CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (kFlatComplexesGeneral X).ι ⋙ Stacks.SheafOfModules.Tensor.tensorComplex X.O ⋙
    (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

/-- `kFlatTensorToDerivedGeneral` inverts quasi-isomorphisms between K-flat complexes in the first
variable and all quasi-isomorphisms in the second, simultaneously. The first is Stacks 06YT
and the second is Stacks 06YP. -/
theorem kFlatTensorToDerived_inverts_general :
    MorphismProperty.IsInvertedBy₂ (kFlatComplexQuasiIsoGeneral X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerivedGeneral X) := by
  rintro ⟨A, L⟩ ⟨B, L'⟩ ⟨c, g⟩ ⟨hc, hg⟩
  have hc' : QuasiIso c.hom := (HomologicalComplex.mem_quasiIso_iff c.hom).1 hc
  have hg' : QuasiIso g := (HomologicalComplex.mem_quasiIso_iff g).1 hg
  have h1 : QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map c.hom).app L) :=
    quasiIso_tensorComplex_map_app_of_kFlat_general X c.hom hc'
      ((kFlatComplexes_iff_general X _).1 A.2) ((kFlatComplexes_iff_general X _).1 B.2) L
  have h2 : QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B.obj).map g) :=
    IsKFlat.quasiIso_tensorComplex_obj_map X.O B.obj ((kFlatComplexes_iff_general X _).1 B.2) g hg'
  have e1 : IsIso (((kFlatTensorToDerivedGeneral X).map c).app L) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h1
  have e2 : IsIso (((kFlatTensorToDerivedGeneral X).obj B).map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h2
  rw [Functor.uncurry_obj_map]
  infer_instance

/-- The derived tensor product bifunctor on the derived category of sheaves of modules on a
ringed site. -/
def derivedTensorBifunctorGeneral :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Localization.lift₂ (kFlatTensorToDerivedGeneral X) (kFlatTensorToDerived_inverts_general X)
    (kFlatComplexQGeneral X) DerivedCategory.Q

/-- `derivedTensorBifunctorGeneral` descends `kFlatTensorToDerivedGeneral` along the two
localizations. -/
@[instance_reducible]
def derivedTensorBifunctorLiftingGeneral :
    Localization.Lifting₂ (kFlatComplexQGeneral X) DerivedCategory.Q
      (kFlatComplexQuasiIsoGeneral X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X) := by
  unfold derivedTensorBifunctorGeneral
  infer_instance

attribute [local instance] derivedTensorBifunctorLiftingGeneral

/-- The comparison isomorphism of bifunctors: on a K-flat first factor and an arbitrary
second factor, the derived tensor product is the ordinary total tensor product. -/
abbrev kFlatComparisonNatIsoGeneral :
    (((Functor.whiskeringLeft₂ _).obj (kFlatComplexQGeneral X)).obj
        DerivedCategory.Q).obj (derivedTensorBifunctorGeneral X) ≅
      kFlatTensorToDerivedGeneral X :=
  Localization.Lifting₂.iso (kFlatComplexQGeneral X) DerivedCategory.Q
    (kFlatComplexQuasiIsoGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X)

/-- For a K-flat complex `A` and an arbitrary complex `L`, the derived tensor product of their
classes is the class of their total tensor complex. -/
def kFlatComparisonGeneral
    (A : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A)
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)).obj
        (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj L) :=
  ((kFlatComparisonNatIsoGeneral X).app (kFlatObjGeneral X A hA)).app L

/-- The comparison isomorphism is natural in the K-flat first factor and in the arbitrary
second factor at once. The morphism of total tensor complexes is written as the composite of
the two one-variable images; `HomologicalComplex.mapBifunctorMap_eq_map₂_comp` identifies it
with `HomologicalComplex.mapBifunctorMap c g`. -/
theorem kFlatComparison_naturality_general
    {A B L L' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (hB : IsKFlat X.O B) (c : A ⟶ B) (g : L ⟶ L') :
    ((derivedTensorBifunctorGeneral X).map (DerivedCategory.Q.map c)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj B)).map
          (DerivedCategory.Q.map g) ≫
        (kFlatComparisonGeneral X B hB L').hom =
      (kFlatComparisonGeneral X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map c).app L ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).map g) := by
  have h := (Functor.uncurry.map (kFlatComparisonNatIsoGeneral X).hom).naturality
    ((⟨(⟨c⟩ : kFlatObjGeneral X A hA ⟶ kFlatObjGeneral X B hB), g⟩ :
      ((kFlatObjGeneral X A hA, L) : _ × _) ⟶ (kFlatObjGeneral X B hB, L')))
  simp only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Category.assoc] at h
  rw [Functor.map_comp]
  exact h

end Stacks.SheafOfModules

end
