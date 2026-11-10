module

public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationIsoAgreement
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusShortExactBoundary

/-!
# The realization comparison of Stacks 01F1 and boundary maps

Let `X` be a ringed space and `0 → K₁ → K₂ → K₃ → 0` a short exact sequence of bounded below
complexes of `𝒪_X`-modules. Its derived global sections can be computed in two ways: in sheaves
of modules, or after forgetting to abelian sheaves ([Stacks, Tag 01F1]); the comparison is
`Stacks.Cohomology.RealizationShift.realizationTotal`. This file proves that this comparison
intertwines the two boundary morphisms `RΓ(K₃) ⟶ RΓ(K₁)[1]` attached to the sequence.

## Main results

* `Stacks.Cohomology.RealizationBoundary.abelianδ_comp_realizationTotal`: **the realization
  comparison carries the abelian boundary morphism to the module one.**

## Implementation notes

Both boundary morphisms are presented by the roof `K₃ ⟵ C(K₁ ⟶ K₂) ⟶ K₁[1]` through the mapping
cone, and a natural transformation commuting with the shift intertwines any two morphisms
presented by the same roof (`comp_shift_app_eq_of_roof`).

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.RightDerivedBoundary
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RealizationBoundary

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

/-- A morphism followed by an isomorphism and its inverse, with every object a variable. -/
private theorem comp_inv_hom_aux {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y)
    (i : Y ⟶ Z) (j : Z ⟶ Y) (h : i ≫ j = 𝟙 _) : (f ≫ i) ≫ j = f := by
  rw [Category.assoc, h, Category.comp_id]

/-- An equation with identities on both sides, with every object a variable. -/
private theorem eq_of_comp_ids {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X : D}
    {Z : C} (f g : X ⟶ F.obj Z) (j : X ⟶ X) (h : f ≫ F.map (𝟙 Z) = j ≫ g) (hj : j = 𝟙 X) :
    f = g := by
  subst hj
  simpa using h

section Generic

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [HasShift C ℤ]
  [HasShift D ℤ] {Φ Ψ : C ⥤ D} [Φ.CommShift ℤ] [Ψ.CommShift ℤ] (α : Φ ⟶ Ψ)
  [NatTrans.CommShift α ℤ]

omit [Preadditive C] in
/-- **A natural transformation commuting with the shift intertwines two morphisms
`Φ X₃ ⟶ (Φ X₁)⟦1⟧` and `Ψ X₃ ⟶ (Ψ X₁)⟦1⟧` presented by the same roof** `X₃ ⟵ C ⟶ X₁⟦1⟧`, as soon
as `Φ` inverts the first leg of the roof. -/
theorem comp_shift_app_eq_of_roof {X₁ X₃ Cn : C} (d : Cn ⟶ X₃) (m : Cn ⟶ X₁⟦(1 : ℤ)⟧)
    [IsIso (Φ.map d)] (δΦ : Φ.obj X₃ ⟶ (Φ.obj X₁)⟦(1 : ℤ)⟧)
    (δΨ : Ψ.obj X₃ ⟶ (Ψ.obj X₁)⟦(1 : ℤ)⟧)
    (hΦ : Φ.map d ≫ δΦ = Φ.map m ≫ (Φ.commShiftIso (1 : ℤ)).hom.app X₁)
    (hΨ : Ψ.map d ≫ δΨ = Ψ.map m ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app X₁) :
    δΦ ≫ (α.app X₁)⟦(1 : ℤ)⟧' = α.app X₃ ≫ δΨ := by
  rw [← cancel_epi (Φ.map d), reassoc_of% hΦ, NatTrans.shift_app_comm α (1 : ℤ) X₁,
    α.naturality_assoc, ← hΨ, α.naturality_assoc]

end Generic

section ShiftMap

/-- Two commutative squares pasted along a functor, with every object a variable. -/
private theorem paste_map {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {p q r s : D} {p' q' s' : C} (ab : p ⟶ r) (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s)
    (d : s ⟶ F.obj s') (i : p ⟶ F.obj p') (j : q ⟶ F.obj q') (y : p' ⟶ q') (z : q' ⟶ s')
    (hab : ab = a ≫ b) (e₁ : b ≫ c ≫ d = j ≫ F.map z) (e₂ : a ≫ j = i ≫ F.map y) :
    (ab ≫ c) ≫ d = i ≫ F.map (y ≫ z) := by
  rw [hab, Category.assoc, Category.assoc, e₁, reassoc_of% e₂, F.map_comp]

/-- Two commutative squares pasted, with every object a variable. -/
private theorem paste_sq {C : Type*} [Category* C] {p q q' r₁ s₁ t : C} (g : p ⟶ q)
    (x : q ⟶ q') (y : q' ⟶ t) (r : p ⟶ r₁) (w : r₁ ⟶ q') (s : r₁ ⟶ s₁) (tt : s₁ ⟶ t)
    (h₁ : g ≫ x = r ≫ w) (h₂ : w ≫ y = s ≫ tt) :
    g ≫ (x ≫ y) = (r ≫ s) ≫ tt := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- The connecting map of a composite with a functor commuting with the shift is the connecting
map of the image under that functor. -/
theorem _root_.CategoryTheory.Functor.comp_shiftMap_eq {C D A : Type*} [Category* C] [Category* D]
    [Category* A] [HasShift C ℤ] [HasShift D ℤ] (π : C ⥤ D) [π.CommShift ℤ] (H : D ⥤ A)
    [H.ShiftSequence ℤ] {Y Z : C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) (a a' : ℤ) (ha : 1 + a = a') :
    (π ⋙ H).shiftMap f a a' ha = H.shiftMap (Functor.mapδ π f) a a' ha := by
  change (H.shift a).map (π.map f) ≫ (𝟙 _ ≫ (H.shift a).map ((π.commShiftIso 1).hom.app Z) ≫
    𝟙 _ ≫ (H.shiftIso 1 a a' ha).hom.app (π.obj Z)) = _
  simp [Functor.shiftMap, Functor.mapδ]

/-- **An exact functor carries the connecting map on cohomology of a morphism `Y ⟶ Z[1]` to the
connecting map of its image**, through the comparison `Hⁿ(F K) ≅ F(Hⁿ K)`. -/
theorem mapDerivedCategoryHomologyIso_shiftMap {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {Y Z : DerivedCategory C₁} (f : Y ⟶ Z⟦(1 : ℤ)⟧) (a a' : ℤ) (ha : 1 + a = a') :
    (DerivedCategory.homologyFunctor C₂ 0).shiftMap (Functor.mapδ F.mapDerivedCategory f) a a' ha ≫
        (F.mapDerivedCategoryHomologyIso a').hom.app Z =
      (F.mapDerivedCategoryHomologyIso a).hom.app Y ≫
        F.map ((DerivedCategory.homologyFunctor C₁ 0).shiftMap f a a' ha) := by
  have e₁ := Stacks.Cohomology.RealizationShift.mapDerivedCategoryHomologyIso_shift F Z 1 a a' ha
  have e₂ := (F.mapDerivedCategoryHomologyIso a).hom.naturality f
  simp only [Functor.comp_map] at e₂
  exact paste_map F _ _ _ _ _ _ _ _ _
    ((DerivedCategory.homologyFunctor C₂ a).map_comp _ _) e₁ e₂

end ShiftMap

/-- A faithful functor commuting with the shift reflects equality of morphisms `Y ⟶ Z⟦1⟧` through
`Functor.mapδ`. -/
theorem _root_.CategoryTheory.Functor.mapδ_injective {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (π : C ⥤ D) [π.CommShift ℤ] [π.Faithful] {Y Z : C}
    {f g : Y ⟶ Z⟦(1 : ℤ)⟧} (h : Functor.mapδ π f = Functor.mapδ π g) : f = g := by
  apply π.map_injective
  simpa only [Functor.mapδ, cancel_mono] using h

section Cone

variable {A : Type*} [Category* A] [Abelian A] (S : ShortComplex (CochainComplex.Plus A))

/-- The comparison `C(K₁ ⟶ K₂) ⟶ K₃` of the mapping cone with the third term, as a morphism of
bounded below complexes. -/
def coneDesc : mappingConePlus S ⟶ S.X₃ :=
  ObjectProperty.homMk (CochainComplex.mappingCone.descShortComplex (toSC S))

/-- The third morphism `C(K₁ ⟶ K₂) ⟶ K₁⟦1⟧` of the mapping cone triangle, as a morphism of bounded
below complexes. -/
def coneδPlus : mappingConePlus S ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  (CochainComplex.Plus.ι A).preimage ((CochainComplex.mappingCone.triangle (toSC S).f).mor₃ ≫
    ((CochainComplex.Plus.ι A).commShiftIso (1 : ℤ)).inv.app S.X₁)

/-- The defining property of `coneδPlus`. -/
theorem mapδ_ι_coneδPlus :
    Functor.mapδ (CochainComplex.Plus.ι A) (coneδPlus S) =
      (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ := by
  dsimp only [Functor.mapδ, coneδPlus]
  rw [Functor.map_preimage]
  exact comp_inv_hom_aux _ _ _ (Iso.inv_hom_id_app _ _)

end Cone

section ConeDerived

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  (S : ShortComplex (CochainComplex.Plus A)) (hS : (toSC S).ShortExact)

/-- **The mapping cone presents the connecting morphism of a short exact sequence of bounded below
complexes in `D⁺`**: the comparison `C(K₁ ⟶ K₂) ⟶ K₃`, followed by `plusδ`, is the third morphism
of the mapping cone triangle. -/
theorem plusQ_map_coneDesc_comp_plusδ :
    DerivedCategory.Plus.Q.map (coneDesc S) ≫ plusδ S hS =
      Functor.mapδ DerivedCategory.Plus.Q (coneδPlus S) := by
  apply Functor.mapδ_injective DerivedCategory.Plus.ι
  have h := Functor.mapδ_commShift (Stacks.Cohomology.RealizationShift.plusQCompιIso A).hom
    (coneδPlus S)
  have e₁ : (Stacks.Cohomology.RealizationShift.plusQCompιIso A).hom.app (mappingConePlus S) =
      𝟙 _ := rfl
  have e₂ : (Stacks.Cohomology.RealizationShift.plusQCompιIso A).hom.app S.X₁ = 𝟙 _ := rfl
  rw [e₁, e₂] at h
  replace h := eq_of_comp_ids _ _ _ _ h rfl
  have hR : Functor.mapδ DerivedCategory.Plus.ι
        (Functor.mapδ DerivedCategory.Plus.Q (coneδPlus S)) =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex (toSC S)) ≫
        DerivedCategory.triangleOfSESδ hS :=
    (Functor.mapδ_comp _ _ _).symm.trans (h.trans ((Functor.mapδ_comp _ _ _).trans
      ((congrArg (Functor.mapδ DerivedCategory.Q) (mapδ_ι_coneδPlus S)).trans
        (DerivedCategory.descShortComplex_triangleOfSESδ hS).symm)))
  refine (Functor.comp_mapδ _ _ _).trans ?_
  refine (whisker_eq _ (mapδ_ι_plusδ S hS)).trans ?_
  exact hR.symm

end ConeDerived

section ConeMap

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] (T : A ⥤ B)
  [T.Additive] (S : ShortComplex (CochainComplex.Plus A))

/-- The functor induced on bounded below complexes by an additive functor is additive. -/
instance mapCochainComplexPlus_additive : T.mapCochainComplexPlus.Additive where
  map_add {_K _L} f g := ObjectProperty.hom_ext _ ((T.mapHomologicalComplex _).map_add (f := f.hom)
    (g := g.hom))

/-- The image of a short complex of bounded below complexes under the functor induced by an
additive functor. -/
abbrev mapPlus : ShortComplex (CochainComplex.Plus B) := S.map T.mapCochainComplexPlus

/-- An exact functor carries a short exact sequence of bounded below complexes to a short exact
sequence. -/
theorem toSC_mapPlus_shortExact [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hS : (toSC S).ShortExact) : (toSC (mapPlus T S)).ShortExact :=
  hS.map_of_exact (T.mapHomologicalComplex _)

/-- The image of the mapping cone under an additive functor is the mapping cone of the image, as
a morphism of bounded below complexes. -/
def coneMapIso : T.mapCochainComplexPlus.obj (mappingConePlus S) ⟶
    mappingConePlus (mapPlus T S) :=
  ObjectProperty.homMk (CochainComplex.mappingCone.mapHomologicalComplexIso (toSC S).f T).hom

/-- The image of the comparison of the mapping cone with the third term is the comparison of the
mapping cone of the image. -/
theorem coneMapIso_comp_coneDesc :
    coneMapIso T S ≫ coneDesc (mapPlus T S) =
      T.mapCochainComplexPlus.map (coneDesc S) :=
  ObjectProperty.hom_ext _
    (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex T (toSC S))

/-- **The image of the third morphism of the mapping cone triangle under an additive functor is the
third morphism of the mapping cone triangle of the image**, read through `coneMapIso`. -/
theorem mapδ_mapCochainComplexPlus_coneδPlus :
    Functor.mapδ T.mapCochainComplexPlus (coneδPlus S) =
      coneMapIso T S ≫ coneδPlus (mapPlus T S) := by
  apply Functor.mapδ_injective (CochainComplex.Plus.ι B)
  have : NatTrans.CommShift (T.mapCochainComplexPlusCompι).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have h := Functor.mapδ_commShift (T.mapCochainComplexPlusCompι).hom (coneδPlus S)
  replace h := eq_of_comp_ids _ _ _ _ h rfl
  refine (Functor.mapδ_comp _ _ _).symm.trans (h.trans ((Functor.mapδ_comp _ _ _).trans ?_))
  refine (congrArg (Functor.mapδ (T.mapHomologicalComplex (ComplexShape.up ℤ)))
    (mapδ_ι_coneδPlus S)).trans ?_
  refine (CochainComplex.mappingCone.map_δ (toSC S).f T).trans ?_
  exact (whisker_eq _ (mapδ_ι_coneδPlus (mapPlus T S)).symm).trans
    (Functor.comp_mapδ (CochainComplex.Plus.ι B) (coneMapIso T S)
      (coneδPlus (mapPlus T S))).symm

end ConeMap

section Realization

variable (X : RingedSpace.{u, u})

open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen)

/-- The target of the realization comparison: derived global sections in modules, the module
structure forgotten, on bounded below complexes. -/
abbrev moduleSide : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory AddCommGrpCat.{u} :=
  ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
      derivedSectionsOverOpen X ⊤) ⋙
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory

/-- The boundary morphism of a short exact sequence of bounded below complexes of modules, read in
the target of the realization comparison. -/
def moduleδ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) :
    (moduleSide X).obj S.X₃ ⟶ ((moduleSide X).obj S.X₁)⟦(1 : ℤ)⟧ :=
  Functor.mapδ (derivedSectionsOverOpen X ⊤ ⋙
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory)
    (DerivedCategory.triangleOfSESδ hS)

/-- In the target of the realization comparison, the boundary morphism `moduleδ` precomposed with
the image of `coneDesc` equals the image of the cone morphism `coneδPlus`, up to the shift
isomorphism. -/
theorem moduleδ_roof
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) :
    (moduleSide X).map (coneDesc S) ≫ moduleδ X S hS =
      (moduleSide X).map (coneδPlus S) ≫ ((moduleSide X).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  change _ = Functor.mapδ (moduleSide X) (coneδPlus S)
  rw [Functor.mapδ_comp, Functor.mapδ_comp, Functor.mapδ_comp, mapδ_ι_coneδPlus]
  have hq : DerivedCategory.Q.mapδ (CochainComplex.mappingCone.triangle (toSC S).f).mor₃ =
      DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex (toSC S)) ≫
        DerivedCategory.triangleOfSESδ hS :=
    (DerivedCategory.descShortComplex_triangleOfSESδ hS).symm
  refine Eq.trans ?_ (congrArg (fun g =>
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory.mapδ
      ((derivedSectionsOverOpen X ⊤).mapδ g)) hq).symm
  refine Eq.trans ?_ (congrArg (fun g =>
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory.mapδ g)
      (Functor.comp_mapδ (derivedSectionsOverOpen X ⊤) _ _)).symm
  refine Eq.trans ?_ (Functor.comp_mapδ
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory
      _ _).symm
  exact whisker_eq _ (Functor.mapδ_comp _ _ _)

/-- The source of the realization comparison: derived global sections of the underlying complex of
abelian sheaves, on bounded below complexes of modules. -/
abbrev abelianSide : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) ⋙
    DerivedCategory.Plus.ι

/-- The boundary morphism of the underlying short exact sequence of complexes of abelian sheaves,
read in the source of the realization comparison. -/
def abelianδ (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) :
    (abelianSide X).obj S.X₃ ⟶ ((abelianSide X).obj S.X₁)⟦(1 : ℤ)⟧ :=
  Functor.mapδ ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (plusδ (mapPlus (SheafOfModules.toSheaf (structureSheafRing X)) S)
      (toSC_mapPlus_shortExact _ S hS))

/-- In the source of the realization comparison, the boundary morphism `abelianδ` precomposed with
the image of `coneDesc` equals the image of the cone morphism `coneδPlus`, up to the shift
isomorphism. -/
theorem abelianδ_roof
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) :
    (abelianSide X).map (coneDesc S) ≫ abelianδ X S hS =
      (abelianSide X).map (coneδPlus S) ≫ ((abelianSide X).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  change _ = Functor.mapδ (abelianSide X) (coneδPlus S)
  rw [Functor.mapδ_comp, Functor.mapδ_comp, Functor.mapδ_comp,
    mapδ_mapCochainComplexPlus_coneδPlus, Functor.comp_mapδ,
    ← plusQ_map_coneDesc_comp_plusδ _ (toSC_mapPlus_shortExact _ S hS), Functor.comp_mapδ,
    Functor.comp_mapδ, Functor.comp_mapδ, Functor.comp_mapδ, ← Functor.mapδ_comp]
  change DerivedCategory.Plus.ι.map ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map
          (coneDesc S)))) ≫ _ = _
  rw [← coneMapIso_comp_coneDesc, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  rfl

/-- The comparison of the mapping cone with the third term becomes invertible in the source of the
realization comparison. -/
theorem isIso_abelianSide_map_coneDesc
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) : IsIso ((abelianSide X).map (coneDesc S)) := by
  have hq : QuasiIso ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map
      (coneDesc S)).hom := by
    rw [← coneMapIso_comp_coneDesc]
    have : QuasiIso (coneDesc (mapPlus (SheafOfModules.toSheaf (structureSheafRing X)) S)).hom :=
      CochainComplex.mappingCone.quasiIso_descShortComplex
        (toSC_mapPlus_shortExact (SheafOfModules.toSheaf (structureSheafRing X)) S hS)
    have : IsIso (coneMapIso (SheafOfModules.toSheaf (structureSheafRing X)) S).hom :=
      inferInstanceAs (IsIso (CochainComplex.mappingCone.mapHomologicalComplexIso _ _).hom)
    exact quasiIso_comp _ _
  have hQ : IsIso (DerivedCategory.Plus.Q.map
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map
        (coneDesc S))) := by
    rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι]
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (φ :=
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map
        (coneDesc S)).hom)).2 hq
  change IsIso (DerivedCategory.Plus.ι.map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus.map
          (coneDesc S)))))
  infer_instance

/-- **The realization comparison of Stacks 01F1 carries the boundary morphism of a short exact
sequence of complexes of abelian sheaves to the boundary morphism of the short exact sequence of
complexes of modules it comes from.** -/
theorem abelianδ_comp_realizationTotal
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) :
    abelianδ X S hS ≫ ((Stacks.Cohomology.RealizationShift.realizationTotal X).app S.X₁)⟦(1 : ℤ)⟧' =
      (Stacks.Cohomology.RealizationShift.realizationTotal X).app S.X₃ ≫ moduleδ X S hS := by
  have := isIso_abelianSide_map_coneDesc X S hS
  exact comp_shift_app_eq_of_roof (Stacks.Cohomology.RealizationShift.realizationTotal X)
    (coneDesc S) (coneδPlus S) _ _ (abelianδ_roof X S hS) (moduleδ_roof X S hS)

/-- **The realization comparison of Stacks 01F1 intertwines the connecting maps on cohomology** of
a short exact sequence of bounded below complexes of modules: the connecting map
`Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)` of the underlying sequence of abelian sheaves and the one of derived
global sections in modules. -/
theorem shortExactBoundary_comp_realizationIsoAt
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))))
    (hS : (toSC S).ShortExact) (a a' : ℤ) (ha : a + 1 = a') :
    shortExactBoundary (sectionsFunctor X.carrier ⊤)
        (mapPlus (SheafOfModules.toSheaf (structureSheafRing X)) S)
        (toSC_mapPlus_shortExact (SheafOfModules.toSheaf (structureSheafRing X)) S hS) a a' ha ≫
        (Stacks.Cohomology.RealizationShift.realizationIsoAt X S.X₁ a').hom =
      (Stacks.Cohomology.RealizationShift.realizationIsoAt X S.X₃ a).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ 0).shiftMap
            (Functor.mapδ (derivedSectionsOverOpen X ⊤) (DerivedCategory.triangleOfSESδ hS))
            a a' (by omega)) := by
  have h₀ : shortExactBoundary (sectionsFunctor X.carrier ⊤)
        (mapPlus (SheafOfModules.toSheaf (structureSheafRing X)) S)
        (toSC_mapPlus_shortExact (SheafOfModules.toSheaf (structureSheafRing X)) S hS) a a' ha =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftMap (abelianδ X S hS) a a'
        (by omega) := by
    refine (Functor.comp_shiftMap_eq DerivedCategory.Plus.ι
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) _ a a' (by omega)).trans ?_
    exact congrArg (fun g => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftMap g a a'
      (by omega)) (Functor.mapδ_comp _ _ _).symm
  have h₁ := abelianδ_comp_realizationTotal X S hS
  have h₂ := mapDerivedCategoryHomologyIso_shiftMap
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u})
    (Functor.mapδ (derivedSectionsOverOpen X ⊤) (DerivedCategory.triangleOfSESδ hS)) a a'
      (by omega)
  have h₃ : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftMap (abelianδ X S hS) a a'
        (by omega) ≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} a').map
          ((Stacks.Cohomology.RealizationShift.realizationTotal X).app S.X₁) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} a).map
          ((Stacks.Cohomology.RealizationShift.realizationTotal X).app S.X₃) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftMap
          (Functor.mapδ (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
            AddCommGrpCat.{u}).mapDerivedCategory
            (Functor.mapδ (derivedSectionsOverOpen X ⊤) (DerivedCategory.triangleOfSESδ hS)))
          a a' (by omega) := by
    change _ ≫ ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shift a').map _ =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shift a).map _ ≫ _
    rw [← Functor.shiftMap_comp, h₁, Functor.shiftMap_comp', moduleδ, Functor.mapδ_comp]
  rw [h₀]
  exact paste_sq _ _ _ _ _ _ _ h₃ h₂

end Realization

end Stacks.Cohomology.RealizationBoundary

end
