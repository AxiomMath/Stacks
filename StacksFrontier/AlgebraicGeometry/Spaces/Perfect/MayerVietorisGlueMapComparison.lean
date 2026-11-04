module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FactorComparisonCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing

/-!
# The Mayer-Vietoris glue map and the derived adjunction

Let `R : A ⥤ D` and `Q : D ⥤ E` be composable functors with an identification `e : R ⋙ Q ≅ T`
and let `L ⊣ T` and `L' ⊣ R` be adjunctions.  The comparison
`CategoryTheory.Adjunction.factorLeftAdjointComparison` attached to that factorization is the
first map of a Mayer-Vietoris triangle; on an abelian category with exact functors there are
then two of them, the derived form of the comparison and the comparison of the derived
adjunctions, and Stacks 08HB is stated with the second while Stacks 08GV delivers the first.
This file identifies the two, on the pattern of
`CategoryTheory.Adjunction.mapDerivedCategory_counit_eq`, which does the same for the counit.

## Main results

* `CategoryTheory.Adjunction.mapDerivedCategory_factorLeftAdjointComparison` and its
  companion
  `…mapDerivedCategory_factorLeftAdjointComparison_app_eq_mayerVietorisGlueMap`:
  **the derived form of the transpose is the transpose of the derived form.**  The derived form
  of the comparison of left adjoints attached to a factorization, read through the comparisons
  for the two composites, is the comparison of left adjoints attached to the derived
  factorization, and so is the canonical first map
  `CategoryTheory.mayerVietorisGlueMap` of a Mayer-Vietoris triangle of the derived
  adjunctions.
* `AlgebraicGeometry.Space.mapDerivedCategory_edsShriekOpenComparison_app` and
  `AlgebraicGeometry.Space.mapDerivedCategory_edsShriekEtaleComparison_app`: that
  identification at the two comparisons out of the intersection of an elementary distinguished
  square.
* `CategoryTheory.Adjunction.mapDerivedCategory_unit_eq` and
  `CategoryTheory.Adjunction.mapDerivedCategory_unit_app`: **the derived form of the unit of an
  adjunction of exact functors is the unit of the derived adjunction**, the companion of the
  counit statement of
  `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisExtRestriction.lean`.  Both are
  lifts through `DerivedCategory.Q`, so `CategoryTheory.Localization.natTrans_ext` reduces the
  comparison to a degreewise identity on cochain complexes.
* `CategoryTheory.Functor.mapDerivedCategoryComp_assoc_inv`: **the associativity coherence of
  the comparison of the derived functor of a composite with the composite of the derived
  functors**, and
  `CategoryTheory.Functor.whiskerLeft_mapDerivedCategoryIdIso_hom`,
  `CategoryTheory.Functor.whiskerRight_mapDerivedCategoryIdIso_hom`: its two unit coherences.
* `CategoryTheory.mayerVietorisGlueMap_eq_factorLeftAdjointComparison_app`:
  `CategoryTheory.mayerVietorisGlueMap`, the first map of the Mayer-Vietoris triangle that
  Stacks 08HB is stated with, is the comparison of left adjoints attached to the
  factorization; both are the adjoint transpose of the same restricted unit.
* `CategoryTheory.Functor.mapDerivedCategoryComp_eq`: the two names the library carries for
  the comparison for a composite agree, which is what lets the whiskering statements
  `CategoryTheory.NatTrans.mapDerivedCategory_whiskerRight` and
  `CategoryTheory.NatTrans.mapDerivedCategory_whiskerLeft` be used alongside the
  Mayer-Vietoris development; they are restated in the latter names as
  `CategoryTheory.NatTrans.mapDerivedCategoryComp_whiskerRight` and
  `CategoryTheory.NatTrans.mapDerivedCategoryComp_whiskerLeft`.

## Implementation notes

The identification is the adjoint transpose and the coherences of the comparison for a
composite.  Both maps are transposes under the derived adjunction `L ⊣ T`, so it is enough to
compare the transposes, and those are natural transformations out of `T` on derived categories;
`CategoryTheory.Adjunction.whiskerLeft_unit_comp_whiskerRight_factorLeftAdjointComparison` and
`CategoryTheory.Adjunction.factorUnit_eq` write each side downstairs as a composite of
whiskerings of a unit, the whiskering statements and the unit statement carry those composites
to derived categories one factor at a time, and the associativity and unit coherences of the
comparison for a composite rebracket what comes out.

*The identification of iterated restriction that goes with this one.*  The two comparisons also
carry different identifications of iterated restriction with restriction to the intersection:
`AlgebraicGeometry.Space.edsRestrictCompOpen` is
`AlgebraicGeometry.Space.etaleModulePullbackComp`, built from
`SheafOfModules.pushforwardComp`, while `AlgebraicGeometry.Space.edsFactorIsoOpen`, which the
comparison of Stacks 08GV uses, is `AlgebraicGeometry.Space.etaleModulePullbackFactorIso`,
built from the comparison of Stacks 03LU transported along Stacks 03LW.  The two agree, which
is `AlgebraicGeometry.Space.edsRestrictCompOpen_eq_edsFactorIsoOpen` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisRestrictComparison.lean`; the two
together are assembled into the Mayer–Vietoris triangle of Stacks 08GV part (2) in its
canonical spelling in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisGlueingTag.lean`.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section Bridges

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The two names the library carries for the comparison of the derived functor of a composite
with the composite of the derived functors agree. -/
theorem Functor.mapDerivedCategoryComp_eq (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (Functor.mapDerivedCategoryComp F G).inv =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_
  rw [Functor.mapDerivedCategoryComp_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app]
  simp

end Bridges

section Coherence

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

/-- **The associativity coherence of the comparison for a composite.** -/
theorem Functor.mapDerivedCategoryComp_assoc_inv (X : C₁ ⥤ C₂) (Y : C₂ ⥤ C₃) (Z : C₃ ⥤ C₄)
    [X.Additive] [PreservesFiniteLimits X] [PreservesFiniteColimits X]
    [Y.Additive] [PreservesFiniteLimits Y] [PreservesFiniteColimits Y]
    [Z.Additive] [PreservesFiniteLimits Z] [PreservesFiniteColimits Z] :
    Functor.whiskerRight (Functor.mapDerivedCategoryComp X Y).inv Z.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp (X ⋙ Y) Z).inv =
      Functor.whiskerLeft X.mapDerivedCategory (Functor.mapDerivedCategoryComp Y Z).inv ≫
        (Functor.mapDerivedCategoryComp X (Y ⋙ Z)).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hnat := (Functor.mapDerivedCategoryComp Y Z).inv.naturality
    (X.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hnat
  rw [Functor.mapDerivedCategoryComp_inv_app_Q, Functor.mapDerivedCategoryComp_inv_app_Q,
    Functor.mapDerivedCategoryComp_inv_app_Q, ← reassoc_of% hnat,
    Functor.mapDerivedCategoryComp_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app,
    Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app,
    Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app,
    Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app]
  simp
  rfl

end Coherence

section Unit

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
/-- The unit of an adjunction of exact functors, degreewise on cochain complexes, read through
the two comparisons for the identity and for a composite. -/
private theorem unit_mapHomologicalComplex_key (adj : L ⊣ R) (K : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K =
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K ≫
        (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ R))
          (ComplexShape.up ℤ)).hom.app K := by
  ext i
  simp [Adjunction.mapHomologicalComplex]

/-- **The derived form of the unit of an adjunction of exact functors is the unit of the
derived adjunction.**  The companion of
`CategoryTheory.Adjunction.mapDerivedCategory_counit_eq`. -/
theorem Adjunction.mapDerivedCategory_unit_eq (adj : L ⊣ R) :
    NatTrans.mapDerivedCategory adj.unit =
      Functor.mapDerivedCategoryIdIso.hom ≫ (Adjunction.mapDerivedCategory adj).unit ≫
        (Functor.mapDerivedCategoryComp L R).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K => ?_
  have hA : Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app K) := by
    rw [← Functor.mapDerivedCategoryIdIso_hom_app_Q, Iso.hom_inv_id_app_assoc]
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.mapDerivedCategory_app_Q,
    Functor.mapDerivedCategoryComp_inv_app_Q, hA, Adjunction.mapDerivedCategory,
    Adjunction.localization_unit_app, unit_mapHomologicalComplex_key adj K]
  simp only [CatCommSq.iso, Iso.symm_hom, Category.assoc, Functor.map_comp]
  simp

/-- The unit of a derived adjunction at an object: the comparison of the derived functor of the
identity, the derived form of the unit, and the comparison for a composite. -/
theorem Adjunction.mapDerivedCategory_unit_app (adj : L ⊣ R) (Z : DerivedCategory C) :
    (Adjunction.mapDerivedCategory adj).unit.app Z =
      Functor.mapDerivedCategoryIdIso.inv.app Z ≫
        (NatTrans.mapDerivedCategory adj.unit).app Z ≫
        (Functor.mapDerivedCategoryComp L R).hom.app Z := by
  have h := NatTrans.congr_app (Adjunction.mapDerivedCategory_unit_eq adj) Z
  simp only [NatTrans.comp_app] at h
  rw [h]
  simp

end Unit

section GlueMap

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] (R : A ⥤ D) (Q : D ⥤ E) (T : A ⥤ E) (e : R ⋙ Q ≅ T) {L : E ⥤ A}
  {L' : D ⥤ A}

/-- **The canonical first map of a Mayer–Vietoris triangle is the comparison of left adjoints
attached to the factorization.**  Both are the adjoint transpose of the same restricted unit. -/
theorem mayerVietorisGlueMap_eq_factorLeftAdjointComparison_app (adj : L ⊣ T) (adj' : L' ⊣ R)
    (F : A) :
    mayerVietorisGlueMap adj adj' e F =
      (Adjunction.factorLeftAdjointComparison R Q T e adj adj').app F := by
  apply (adj.homEquiv (T.obj F) ((R ⋙ L').obj F)).injective
  rw [Adjunction.homEquiv_factorLeftAdjointComparison_app, Adjunction.factorUnit_app,
    mayerVietorisGlueMap]
  exact Equiv.apply_symm_apply _ _

/-- The restricted unit of a factorization, as a composite of whiskerings: the inverse of the
identification, the unit of `L' ⊣ R` whiskered on both sides, and the identification. -/
theorem Adjunction.factorUnit_eq (adj' : L' ⊣ R) :
    Adjunction.factorUnit R Q T e adj' =
      e.inv ≫ Functor.whiskerLeft R (Functor.whiskerRight adj'.unit Q) ≫
        Functor.whiskerLeft (R ⋙ L') e.hom := by
  ext F
  rw [Adjunction.factorUnit_app]
  simp

/-- **The comparison of left adjoints attached to a factorization is the adjoint transpose of
the restricted unit**, as an equality of natural transformations. -/
theorem Adjunction.whiskerLeft_unit_comp_whiskerRight_factorLeftAdjointComparison
    (adj : L ⊣ T) (adj' : L' ⊣ R) :
    Functor.whiskerLeft T adj.unit ≫
        Functor.whiskerRight (Adjunction.factorLeftAdjointComparison R Q T e adj adj') T =
      Adjunction.factorUnit R Q T e adj' := by
  ext F
  dsimp
  rw [← Adjunction.homEquiv_factorLeftAdjointComparison_app, Adjunction.homEquiv_unit]

end GlueMap

section DerivedComparison

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The derived form of the inverse of an isomorphism of exact functors is the inverse of the
derived form of the isomorphism. -/
theorem NatTrans.inv_mapDerivedCategory {F G : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    inv (NatTrans.mapDerivedCategory e.hom) =
      NatTrans.mapDerivedCategory e.inv := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← NatTrans.mapDerivedCategory_comp, e.hom_inv_id,
    NatTrans.mapDerivedCategory_id]

/-- The comparison of the derived functor of the identity with the identity, at the image of a
cochain complex, is the canonical factorization of the derived functor of the identity: the
degreewise comparison it is read through is itself an identity. -/
theorem Functor.mapDerivedCategoryIdIso_hom_app_Q_eq (P : CochainComplex C₁ ℤ) :
    Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C₁).mapDerivedCategoryFactors.hom.app P := by
  have hrefl : (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
    ext i
    simp
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Q P
  rw [hrefl] at h
  simp only [CategoryTheory.Functor.map_id] at h
  calc Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj P)
      = (𝟭 C₁).mapDerivedCategoryFactors.hom.app P ≫
          ((𝟭 C₁).mapDerivedCategoryFactors.inv.app P ≫
            Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj P)) := by
        rw [Iso.hom_inv_id_app_assoc]
    _ = _ := by rw [h]; exact Category.comp_id _

/-- The degreewise comparison for the composite of two functors, read through the identity
isomorphism, does not change the canonical factorization of the derived functor of the composite. -/
private theorem map_compIso_refl_comp_factors_inv {X Y Z : Type*} [Category X] [Abelian X]
    [HasDerivedCategory X] [Category Y] [Abelian Y] [Category Z] [Abelian Z]
    [HasDerivedCategory Z] (F : X ⥤ Y) (G : Y ⥤ Z)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex X ℤ) :
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K =
        (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  rw [Stacks.DerivedCategoryComparisons.mapHomologicalComplexCompIso_refl_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The right-unit coherence of the comparison for a composite.**  The comparison of the
derived functor of `F ⋙ 𝟭` with the composite of the derived functors is the comparison of the
derived functor of the identity with the identity, whiskered by `F`. -/
theorem Functor.whiskerLeft_mapDerivedCategoryIdIso_hom
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.whiskerLeft F.mapDerivedCategory Functor.mapDerivedCategoryIdIso.hom =
      (Functor.mapDerivedCategoryComp F (𝟭 C₂)).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_
  rw [Functor.mapDerivedCategoryComp_inv_app_Q]
  dsimp only [Functor.whiskerLeft_app]
  have htail : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ 𝟭 C₂)) (ComplexShape.up ℤ)).hom.app K) ≫
      (F ⋙ 𝟭 C₂).mapDerivedCategoryFactors.inv.app K =
      F.mapDerivedCategoryFactors.inv.app K :=
    map_compIso_refl_comp_factors_inv F (𝟭 C₂) K
  have hfi : F.mapDerivedCategoryFactors.hom.app K ≫
      F.mapDerivedCategoryFactors.inv.app K = 𝟙 _ :=
    Iso.hom_inv_id_app F.mapDerivedCategoryFactors K
  have hnat := Functor.mapDerivedCategoryIdIso.hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_obj] at hnat
  rw [htail, ← Functor.mapDerivedCategoryIdIso_hom_app_Q_eq, reassoc_of% hnat, hfi]
  exact (Category.comp_id _).symm

/-- **The left-unit coherence of the comparison for a composite**, the companion of
`CategoryTheory.Functor.whiskerLeft_mapDerivedCategoryIdIso_hom` for `𝟭 ⋙ G`. -/
theorem Functor.whiskerRight_mapDerivedCategoryIdIso_hom
    (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Functor.whiskerRight Functor.mapDerivedCategoryIdIso.hom G.mapDerivedCategory =
      (Functor.mapDerivedCategoryComp (𝟭 C₁) G).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_
  rw [Functor.mapDerivedCategoryComp_inv_app_Q]
  dsimp only [Functor.whiskerRight_app]
  have htail : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (𝟭 C₁ ⋙ G)) (ComplexShape.up ℤ)).hom.app K) ≫
      (𝟭 C₁ ⋙ G).mapDerivedCategoryFactors.inv.app K =
      G.mapDerivedCategoryFactors.inv.app K :=
    map_compIso_refl_comp_factors_inv (𝟭 C₁) G K
  have hfi : G.mapDerivedCategoryFactors.hom.app
        (((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      G.mapDerivedCategoryFactors.inv.app K = 𝟙 _ :=
    Iso.hom_inv_id_app G.mapDerivedCategoryFactors K
  rw [htail, hfi, Functor.mapDerivedCategoryIdIso_hom_app_Q_eq]
  exact (Category.comp_id _).symm

/-- Deriving a transformation of exact functors commutes with whiskering on the right, read
through the comparisons for the two composites.  This is
`CategoryTheory.NatTrans.mapDerivedCategory_whiskerRight` in the two names of the
Mayer-Vietoris development. -/
theorem NatTrans.mapDerivedCategoryComp_whiskerRight (F G : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (η : F ⟶ G) (H : C₂ ⥤ C₃)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (Functor.mapDerivedCategoryComp F H).inv ≫
        NatTrans.mapDerivedCategory (Functor.whiskerRight η H) =
      Functor.whiskerRight (NatTrans.mapDerivedCategory η) H.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp G H).inv := by
  rw [Functor.mapDerivedCategoryComp_eq, Functor.mapDerivedCategoryComp_eq]
  exact NatTrans.mapDerivedCategory_whiskerRight F G η H

/-- Deriving a transformation of exact functors commutes with whiskering on the left, read
through the comparisons for the two composites.  This is
`CategoryTheory.NatTrans.mapDerivedCategory_whiskerLeft` in the two names of the
Mayer-Vietoris development. -/
theorem NatTrans.mapDerivedCategoryComp_whiskerLeft (H : C₁ ⥤ C₂) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (F G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (η : F ⟶ G) :
    (Functor.mapDerivedCategoryComp H F).inv ≫
        NatTrans.mapDerivedCategory (Functor.whiskerLeft H η) =
      Functor.whiskerLeft H.mapDerivedCategory (NatTrans.mapDerivedCategory η) ≫
        (Functor.mapDerivedCategoryComp H G).inv := by
  rw [Functor.mapDerivedCategoryComp_eq, Functor.mapDerivedCategoryComp_eq]
  exact NatTrans.mapDerivedCategory_whiskerLeft H F G η

end DerivedComparison
section DerivedFactorComparison

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
  (R : A ⥤ D) (Q : D ⥤ E) (T : A ⥤ E) [R.Additive] [PreservesFiniteLimits R]
  [PreservesFiniteColimits R] [Q.Additive] [PreservesFiniteLimits Q]
  [PreservesFiniteColimits Q] [T.Additive] [PreservesFiniteLimits T]
  [PreservesFiniteColimits T] (e : R ⋙ Q ≅ T) {L : E ⥤ A} {L' : D ⥤ A}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

/-- The derived form of the restricted unit of a factorization, read through the comparisons for
the two composites, is the restricted unit of the derived factorization. -/
private theorem mapDerivedCategory_factorUnit (adj' : L' ⊣ R) :
    NatTrans.mapDerivedCategory (Adjunction.factorUnit R Q T e adj') ≫
        (Functor.mapDerivedCategoryComp (R ⋙ L') T).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryComp R L').hom T.mapDerivedCategory =
      Adjunction.factorUnit R.mapDerivedCategory Q.mapDerivedCategory T.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp R Q).symm ≪≫
          asIso (NatTrans.mapDerivedCategory e.hom))
        adj'.mapDerivedCategory := by
  have h6 : (Functor.mapDerivedCategoryComp (R ⋙ L') (R ⋙ Q)).inv ≫
      NatTrans.mapDerivedCategory (Functor.whiskerLeft (R ⋙ L') e.hom) =
      Functor.whiskerLeft (R ⋙ L').mapDerivedCategory
          (NatTrans.mapDerivedCategory e.hom) ≫
        (Functor.mapDerivedCategoryComp (R ⋙ L') T).inv :=
    NatTrans.mapDerivedCategoryComp_whiskerLeft (R ⋙ L') (R ⋙ Q) T e.hom
  have h7 : (Functor.mapDerivedCategoryComp R Q).inv ≫
      NatTrans.mapDerivedCategory
        (Functor.whiskerLeft R (Functor.whiskerRight adj'.unit Q)) =
      Functor.whiskerLeft R.mapDerivedCategory (NatTrans.mapDerivedCategory
          (Functor.whiskerRight adj'.unit Q)) ≫
        (Functor.mapDerivedCategoryComp R ((L' ⋙ R) ⋙ Q)).inv :=
    NatTrans.mapDerivedCategoryComp_whiskerLeft R (𝟭 D ⋙ Q) ((L' ⋙ R) ⋙ Q)
      (Functor.whiskerRight adj'.unit Q)
  have h8 : (Functor.mapDerivedCategoryComp (𝟭 D) Q).inv ≫
      NatTrans.mapDerivedCategory (Functor.whiskerRight adj'.unit Q) =
      Functor.whiskerRight (NatTrans.mapDerivedCategory adj'.unit)
          Q.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp (L' ⋙ R) Q).inv :=
    NatTrans.mapDerivedCategoryComp_whiskerRight (𝟭 D) (L' ⋙ R) adj'.unit Q
  have h8' : NatTrans.mapDerivedCategory (Functor.whiskerRight adj'.unit Q) =
      Functor.whiskerRight (Adjunction.mapDerivedCategory adj').unit Q.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryComp L' R).inv Q.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp (L' ⋙ R) Q).inv := by
    refine (cancel_epi (Functor.mapDerivedCategoryComp (𝟭 D) Q).inv).mp ?_
    rw [h8, Adjunction.mapDerivedCategory_unit_eq adj',
      ← Functor.whiskerRight_mapDerivedCategoryIdIso_hom Q]
    simp only [Functor.whiskerRight_comp, Category.assoc]
  have h8'' : NatTrans.mapDerivedCategory (Functor.whiskerRight adj'.unit Q) =
      Functor.whiskerRight (Adjunction.mapDerivedCategory adj').unit Q.mapDerivedCategory ≫
        Functor.whiskerLeft L'.mapDerivedCategory
          (Functor.mapDerivedCategoryComp R Q).inv ≫
        (Functor.mapDerivedCategoryComp L' (R ⋙ Q)).inv := by
    rw [h8', Functor.mapDerivedCategoryComp_assoc_inv L' R Q]
  have hassoc : Functor.whiskerRight (Functor.mapDerivedCategoryComp R L').inv
          (R ⋙ Q).mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp (R ⋙ L') (R ⋙ Q)).inv =
      Functor.whiskerLeft R.mapDerivedCategory
          (Functor.mapDerivedCategoryComp L' (R ⋙ Q)).inv ≫
        (Functor.mapDerivedCategoryComp R ((L' ⋙ R) ⋙ Q)).inv :=
    Functor.mapDerivedCategoryComp_assoc_inv R L' (R ⋙ Q)
  have hex := Functor.whiskerLeft_comp_whiskerRight
    (Functor.mapDerivedCategoryComp R L').inv (NatTrans.mapDerivedCategory e.hom)
  have h6' : NatTrans.mapDerivedCategory (Functor.whiskerLeft (R ⋙ L') e.hom) =
      (Functor.mapDerivedCategoryComp (R ⋙ L') (R ⋙ Q)).hom ≫
        Functor.whiskerLeft (R ⋙ L').mapDerivedCategory
          (NatTrans.mapDerivedCategory e.hom) ≫
        (Functor.mapDerivedCategoryComp (R ⋙ L') T).inv := by
    rw [← h6, Iso.hom_inv_id_assoc]
  have h7' : NatTrans.mapDerivedCategory
        (Functor.whiskerLeft R (Functor.whiskerRight adj'.unit Q)) =
      (Functor.mapDerivedCategoryComp R Q).hom ≫
        Functor.whiskerLeft R.mapDerivedCategory (NatTrans.mapDerivedCategory
          (Functor.whiskerRight adj'.unit Q)) ≫
        (Functor.mapDerivedCategoryComp R ((L' ⋙ R) ⋙ Q)).inv := by
    rw [← h7, Iso.hom_inv_id_assoc]
  have hww : Functor.whiskerLeft R.mapDerivedCategory (Functor.whiskerLeft L'.mapDerivedCategory
        (Functor.mapDerivedCategoryComp R Q).inv) =
      Functor.whiskerLeft (R.mapDerivedCategory ⋙ L'.mapDerivedCategory)
        (Functor.mapDerivedCategoryComp R Q).inv := rfl
  have hcancel : Functor.whiskerRight (Functor.mapDerivedCategoryComp R L').inv
          T.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryComp R L').hom T.mapDerivedCategory =
      𝟙 _ := by
    rw [← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id']
  rw [Adjunction.factorUnit_eq R Q T e adj',
    Adjunction.factorUnit_eq R.mapDerivedCategory Q.mapDerivedCategory T.mapDerivedCategory
      ((Functor.mapDerivedCategoryComp R Q).symm ≪≫
        asIso (NatTrans.mapDerivedCategory e.hom)) adj'.mapDerivedCategory,
    NatTrans.mapDerivedCategory_comp, NatTrans.mapDerivedCategory_comp,
    h7', h8'', h6']
  simp only [Functor.whiskerLeft_comp, Category.assoc, hww]
  rw [← reassoc_of% hassoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hex, hcancel]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv,
    Functor.whiskerLeft_comp, Category.assoc, Category.comp_id,
    ← NatTrans.inv_mapDerivedCategory]

/-- The adjoint transpose, under the derived adjunction `L ⊣ T`, of the derived form of the
comparison of left adjoints is the restricted unit of the derived factorization. -/
private theorem whiskerLeft_derivedUnit_comp (adj : L ⊣ T) (adj' : L' ⊣ R) :
    Functor.whiskerLeft T.mapDerivedCategory (Adjunction.mapDerivedCategory adj).unit ≫
        Functor.whiskerRight ((Functor.mapDerivedCategoryComp T L).inv ≫
          NatTrans.mapDerivedCategory
            (Adjunction.factorLeftAdjointComparison R Q T e adj adj') ≫
          (Functor.mapDerivedCategoryComp R L').hom) T.mapDerivedCategory =
      Adjunction.factorUnit R.mapDerivedCategory Q.mapDerivedCategory T.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp R Q).symm ≪≫
          asIso (NatTrans.mapDerivedCategory e.hom))
        adj'.mapDerivedCategory := by
  have hd := Adjunction.whiskerLeft_unit_comp_whiskerRight_factorLeftAdjointComparison
    R Q T e adj adj'
  have hwl : (Functor.mapDerivedCategoryComp T (𝟭 E)).inv ≫
      NatTrans.mapDerivedCategory (Functor.whiskerLeft T adj.unit) =
      Functor.whiskerLeft T.mapDerivedCategory
        (NatTrans.mapDerivedCategory adj.unit) ≫
      (Functor.mapDerivedCategoryComp T (L ⋙ T)).inv :=
    NatTrans.mapDerivedCategoryComp_whiskerLeft T (𝟭 E) (L ⋙ T) adj.unit
  have h1 : NatTrans.mapDerivedCategory (Functor.whiskerLeft T adj.unit) =
      Functor.whiskerLeft T.mapDerivedCategory (Adjunction.mapDerivedCategory adj).unit ≫
        Functor.whiskerLeft T.mapDerivedCategory (Functor.mapDerivedCategoryComp L T).inv ≫
        (Functor.mapDerivedCategoryComp T (L ⋙ T)).inv := by
    refine (cancel_epi (Functor.mapDerivedCategoryComp T (𝟭 E)).inv).mp ?_
    rw [hwl, Adjunction.mapDerivedCategory_unit_eq adj,
      ← Functor.whiskerLeft_mapDerivedCategoryIdIso_hom T]
    simp only [Functor.whiskerLeft_comp, Category.assoc]
  have hwr : (Functor.mapDerivedCategoryComp (T ⋙ L) T).inv ≫
      NatTrans.mapDerivedCategory (Functor.whiskerRight
        (Adjunction.factorLeftAdjointComparison R Q T e adj adj') T) =
      Functor.whiskerRight (NatTrans.mapDerivedCategory
          (Adjunction.factorLeftAdjointComparison R Q T e adj adj')) T.mapDerivedCategory ≫
      (Functor.mapDerivedCategoryComp (R ⋙ L') T).inv :=
    NatTrans.mapDerivedCategoryComp_whiskerRight (T ⋙ L) (R ⋙ L')
      (Adjunction.factorLeftAdjointComparison R Q T e adj adj') T
  have hassoc := Functor.mapDerivedCategoryComp_assoc_inv T L T
  have h2 : NatTrans.mapDerivedCategory (Adjunction.factorUnit R Q T e adj') =
      Functor.whiskerLeft T.mapDerivedCategory (Adjunction.mapDerivedCategory adj).unit ≫
        Functor.whiskerRight ((Functor.mapDerivedCategoryComp T L).inv ≫
          NatTrans.mapDerivedCategory
            (Adjunction.factorLeftAdjointComparison R Q T e adj adj')) T.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryComp (R ⋙ L') T).inv := by
    rw [← hd, NatTrans.mapDerivedCategory_comp, h1, Functor.whiskerRight_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hassoc, hwr]
  rw [← mapDerivedCategory_factorUnit R Q T e adj', h2]
  simp only [Functor.whiskerRight_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The derived form of the transpose is the transpose of the derived form.**  For composable
exact functors `R`, `Q` with `e : R ⋙ Q ≅ T` and adjunctions `L ⊣ T`, `L' ⊣ R` of exact
functors, the derived form of the comparison of left adjoints attached to the factorization,
read through the comparisons for the two composites, is the comparison of left adjoints attached
to the derived factorization. -/
theorem Adjunction.mapDerivedCategory_factorLeftAdjointComparison
    (adj : L ⊣ T) (adj' : L' ⊣ R) :
    (Functor.mapDerivedCategoryComp T L).inv ≫
        NatTrans.mapDerivedCategory
          (Adjunction.factorLeftAdjointComparison R Q T e adj adj') ≫
        (Functor.mapDerivedCategoryComp R L').hom =
      Adjunction.factorLeftAdjointComparison R.mapDerivedCategory Q.mapDerivedCategory
        T.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp R Q).symm ≪≫
          asIso (NatTrans.mapDerivedCategory e.hom))
        adj.mapDerivedCategory adj'.mapDerivedCategory := by
  ext F
  apply (adj.mapDerivedCategory.homEquiv (T.mapDerivedCategory.obj F)
    ((R.mapDerivedCategory ⋙ L'.mapDerivedCategory).obj F)).injective
  rw [Adjunction.homEquiv_factorLeftAdjointComparison_app, Adjunction.homEquiv_unit]
  exact NatTrans.congr_app (whiskerLeft_derivedUnit_comp R Q T e adj adj') F

/-- **The derived form of the comparison of left adjoints is the canonical first map of a
Mayer-Vietoris triangle of the derived adjunctions**, at an object: the derived form of the
transpose, read through the comparisons for the two composites, is the transpose of the derived
form. -/
theorem mapDerivedCategory_factorLeftAdjointComparison_app_eq_mayerVietorisGlueMap
    (adj : L ⊣ T) (adj' : L' ⊣ R) (F : DerivedCategory A) :
    ((Functor.mapDerivedCategoryComp T L).inv ≫
        NatTrans.mapDerivedCategory
          (Adjunction.factorLeftAdjointComparison R Q T e adj adj') ≫
        (Functor.mapDerivedCategoryComp R L').hom).app F =
      mayerVietorisGlueMap adj.mapDerivedCategory adj'.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp R Q).symm ≪≫
          asIso (NatTrans.mapDerivedCategory e.hom)) F := by
  rw [mayerVietorisGlueMap_eq_factorLeftAdjointComparison_app,
    Adjunction.mapDerivedCategory_factorLeftAdjointComparison]

end DerivedFactorComparison

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
    (edsInter B S hS hsq).2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
    (edsInter B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

section Open

variable [HasSheafify (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
    (edsOpen B S hS hsq).2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
    (edsOpen B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]

/-- **The derived form of the comparison out of the intersection through the open subspace is
the canonical first map of a Mayer–Vietoris triangle of the derived adjunctions.**  The
identification of iterated restriction with restriction to the intersection is the derived form
of the one the comparison is built on. -/
theorem mapDerivedCategory_edsShriekOpenComparison_app
    (adjU : shriekU ⊣ edsRestrictOpen B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq)
    (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ((Functor.mapDerivedCategoryComp (edsRestrictInter B S hS hsq) shriekP).inv ≫
        NatTrans.mapDerivedCategory
          (edsShriekOpenComparison B S hS hsq adjU adjP) ≫
        (Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq) shriekU).hom).app F =
      mayerVietorisGlueMap adjP.mapDerivedCategory adjU.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq)
            (edsRestrictFst B S hS hsq)).symm ≪≫
          asIso (NatTrans.mapDerivedCategory (edsFactorIsoOpen B S hS hsq).hom)) F := by
  rw [edsShriekOpenComparison]
  exact mapDerivedCategory_factorLeftAdjointComparison_app_eq_mayerVietorisGlueMap
    _ _ _ _ adjP adjU F

end Open

section Etale

variable [HasSheafify (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]

/-- **The derived form of the comparison out of the intersection through the étale algebraic
space is the canonical first map of a Mayer–Vietoris triangle of the derived adjunctions**, the
companion of `AlgebraicGeometry.Space.mapDerivedCategory_edsShriekOpenComparison_app`
for the second leg of the square. -/
theorem mapDerivedCategory_edsShriekEtaleComparison_app
    (adjV : shriekV ⊣ edsRestrictEtale B S hS hsq)
    (adjP : shriekP ⊣ edsRestrictInter B S hS hsq)
    (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ((Functor.mapDerivedCategoryComp (edsRestrictInter B S hS hsq) shriekP).inv ≫
        NatTrans.mapDerivedCategory
          (edsShriekEtaleComparison B S hS hsq adjV adjP) ≫
        (Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq) shriekV).hom).app F =
      mayerVietorisGlueMap adjP.mapDerivedCategory adjV.mapDerivedCategory
        ((Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq)
            (edsRestrictSnd B S hS hsq)).symm ≪≫
          asIso (NatTrans.mapDerivedCategory (edsFactorIsoEtale B S hS hsq).hom)) F := by
  rw [edsShriekEtaleComparison]
  exact mapDerivedCategory_factorLeftAdjointComparison_app_eq_mayerVietorisGlueMap
    _ _ _ _ adjP adjV F

end Etale

end AlgebraicGeometry.Space

end
