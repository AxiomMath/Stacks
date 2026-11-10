module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DeRham.GysinCupHodge

open Stacks.Cohomology.RealizationShift

section Generic

/-- The algebra of `homology_single_shift_naturality`, at variables. -/
private lemma naturality_chase {V : Type*} [Category* V] {P Q R S P' S' : V} (p : P ⟶ Q)
    (t : Q ⟶ R) (s : R ⟶ S) (s' : Q ⟶ S') (t' : S' ⟶ S) (tP : P ⟶ P') (g : P' ⟶ R)
    (hn : p ≫ t = tP ≫ g) (hs : t ≫ s = s' ≫ t') : tP ≫ g ≫ s = (p ≫ s') ≫ t' := by
  rw [← reassoc_of% hn, hs, Category.assoc]

/-- The algebra of `homology_single_shift_zero`, at variables. -/
private lemma zero_chase {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D)
    (H : D ⥤ E) {P Q : C} (a : P ≅ Q) {R : D} (b : R ≅ F.obj Q) :
    H.map (F.map a.inv) ≫ (H.map (F.map a.hom ≫ b.inv) ≫ H.map b.hom) = 𝟙 _ := by
  rw [← H.map_comp, ← H.map_comp, Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp, Iso.inv_hom_id, H.map_id]

/-- The algebra of `shiftHomologyIsoU_mapDerivedCategory`, at variables. -/
private lemma mapDerived_chase {V : Type*} [Category* V] {P Q R S T P' Q' : V} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ S) (d : S ⟶ T) (d' : P ⟶ P') (m : Q ⟶ Q') (x : P' ⟶ Q') (y : Q' ⟶ T)
    (r : P' ⟶ T) (ha : a ≫ m = d' ≫ x) (hb : b ≫ c ≫ d = m ≫ y) (hr : r = x ≫ y) :
    (a ≫ b ≫ c) ≫ d = d' ≫ r := by
  rw [hr, Category.assoc, Category.assoc, hb, reassoc_of% ha]

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

/-- A transformation commuting with the shift is compatible with the identifications
`Hᵐ(F(M[-a])) ≅ Hᵐ⁻ᵃ(F(M[0]))`. -/
theorem homology_single_shift_naturality {F G : DerivedCategory A ⥤ DerivedCategory B}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (M : A) (a m n : ℤ)
    (ha : -a + a = 0) (h : -a + m = n) :
    (DerivedCategory.homologyFunctor B m).map (τ.app ((DerivedCategory.singleFunctor A a).obj M)) ≫
        (DerivedCategory.homologyFunctor B m).map
          (G.map (((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 ha).inv.app M)) ≫
        (shiftHomologyIsoU G ((DerivedCategory.singleFunctor A 0).obj M) (-a) m n h).hom =
      ((DerivedCategory.homologyFunctor B m).map
          (F.map (((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 ha).inv.app M)) ≫
        (shiftHomologyIsoU F ((DerivedCategory.singleFunctor A 0).obj M) (-a) m n h).hom) ≫
        (DerivedCategory.homologyFunctor B n).map
          (τ.app ((DerivedCategory.singleFunctor A 0).obj M)) := by
  have e₁ := τ.naturality (((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 ha).inv.app M)
  have e₂ := shiftHomologyIsoU_naturality_of_commShift τ
    ((DerivedCategory.singleFunctor A 0).obj M) (-a) m n h
  exact naturality_chase _ _ _ _ _ _ _ ((Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.homologyFunctor B m).map e₁).trans (Functor.map_comp _ _ _))) e₂

/-- An exact functor carries the identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` of `F` to that of
`F` followed by it on derived categories. -/
theorem shiftHomologyIsoU_mapDerivedCategory {C : Type*} [Category* C] [HasShift C ℤ]
    {R : Type*} [Category* R] [Abelian R] [HasDerivedCategory R]
    (F : C ⥤ DerivedCategory R) [F.CommShift ℤ] (Φ : R ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (shiftHomologyIsoU (F ⋙ Φ.mapDerivedCategory) X s n n' h).hom ≫
        (Φ.mapDerivedCategoryHomologyIso n').hom.app (F.obj X) =
      (Φ.mapDerivedCategoryHomologyIso n).hom.app (F.obj (X⟦s⟧)) ≫
        Φ.map (shiftHomologyIsoU F X s n n' h).hom := by
  have hn := (Φ.mapDerivedCategoryHomologyIso n).hom.naturality ((F.commShiftIso s).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  refine (congrArg (· ≫ _) (shiftHomologyIsoU_comp_hom F Φ.mapDerivedCategory X s n n' h)).trans ?_
  exact mapDerived_chase _ _ _ _ _ _ _ _ _ hn
    (mapDerivedCategoryHomologyIso_shift Φ (F.obj X) s n n' h)
    ((congrArg Φ.map (Iso.trans_hom _ _)).trans (Φ.map_comp _ _))

/-- The identification `Hⁿ(F(M[0][-0])) ≅ Hⁿ(F(M[0]))` read through the single functors is the
identity. -/
theorem homology_single_shift_zero (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
    (M : A) (s n : ℤ) (hs : s = 0) (ha : s + 0 = 0) (h : s + n = n) :
    (DerivedCategory.homologyFunctor B n).map
        (F.map (((DerivedCategory.singleFunctors A).shiftIso s 0 0 ha).inv.app M)) ≫
      (shiftHomologyIsoU F ((DerivedCategory.singleFunctor A 0).obj M) s n n h).hom = 𝟙 _ := by
  subst hs
  let Y := (DerivedCategory.singleFunctor A 0).obj M
  have h₁ : ((DerivedCategory.singleFunctors A).shiftIso 0 0 0 ha).inv.app M =
      (shiftFunctorZero (DerivedCategory A) ℤ).inv.app Y :=
    SingleFunctors.shiftIso_zero_inv_app _ 0 M
  have h₂ : (F.commShiftIso (0 : ℤ)).hom.app Y =
      F.map ((shiftFunctorZero (DerivedCategory A) ℤ).hom.app Y) ≫
        (shiftFunctorZero (DerivedCategory B) ℤ).inv.app (F.obj Y) := by
    simp [Functor.commShiftIso_zero]
  have h₃ := Functor.shiftIso_zero_hom_app (DerivedCategory.homologyFunctor B 0) n (F.obj Y)
  change (DerivedCategory.homologyFunctor B n).map
      (F.map (((DerivedCategory.singleFunctors A).shiftIso 0 0 0 ha).inv.app M)) ≫
    ((DerivedCategory.homologyFunctor B n).map ((F.commShiftIso (0 : ℤ)).hom.app Y) ≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso 0 n n h).hom.app (F.obj Y)) = 𝟙 _
  rw [h₁, h₂, h₃]
  exact zero_chase F (DerivedCategory.homologyFunctor B n)
    ((shiftFunctorZero (DerivedCategory A) ℤ).app Y)
    ((shiftFunctorZero (DerivedCategory B) ℤ).app (F.obj Y))

/-- **The identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` is natural in `X`.** -/
theorem shiftHomologyIsoU_naturality {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C ⥤ DerivedCategory B) [F.CommShift ℤ] {X Y : C} (f : X ⟶ Y) (s n n' : ℤ)
    (h : s + n = n') :
    (DerivedCategory.homologyFunctor B n).map (F.map (f⟦s⟧')) ≫
        (shiftHomologyIsoU F Y s n n' h).hom =
      (shiftHomologyIsoU F X s n n' h).hom ≫
        (DerivedCategory.homologyFunctor B n').map (F.map f) := by
  have e₁ := (F.commShiftIso s).hom.naturality f
  have e₂ := (DerivedCategory.homologyFunctor B 0).shiftIso_hom_naturality s n n' h (F.map f)
  let H := DerivedCategory.homologyFunctor B n
  change H.map (F.map (f⟦s⟧')) ≫ (H.map ((F.commShiftIso s).hom.app Y) ≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app (F.obj Y)) =
    (H.map ((F.commShiftIso s).hom.app X) ≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app (F.obj X)) ≫
        (DerivedCategory.homologyFunctor B n').map (F.map f)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((H.map_comp _ _).symm.trans
    ((congrArg H.map e₁).trans (H.map_comp _ _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) e₂).trans (Category.assoc _ _ _).symm)))

end Generic

end Stacks.DeRham.GysinCupHodge
