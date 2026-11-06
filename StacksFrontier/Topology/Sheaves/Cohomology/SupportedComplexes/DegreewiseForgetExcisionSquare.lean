module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge

/-!
# A square of derived functors, read in degree `n`

Work in progress.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.DerivedIndexing

universe wA vA uA wB vB uB wC vC uC wA' vA' uA' wB' vB' uB'

/-! ### The composition comparison of derived functors, at a single object and on cohomology -/

section CompIso

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type uA} [Category.{vA} C₁] [Abelian C₁] [HasDerivedCategory.{wA} C₁]
  {C₂ : Type uB} [Category.{vB} C₂] [Abelian C₂] [HasDerivedCategory.{wB} C₂]
  {C₃ : Type uC} [Category.{vC} C₃] [Abelian C₃] [HasDerivedCategory.{wC} C₃]
  {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The chase behind the two coherences below: a comparison that splits as `p ≫ q`, followed by
`s`, where `q ≫ s` crosses to `t ≫ u` and `p ≫ t` splits as `v₁ ≫ v₂`.

Stated at an arbitrary category with the objects implicit and the morphisms explicit, as the
house style requires: at the concrete derived categories the objects along the chain have two
definitionally equal spellings each. -/
private theorem split_cross {D : Type*} [Category* D] {a b c z y w : D}
    (P : a ⟶ c) (p : a ⟶ b) (q : b ⟶ c) (s : c ⟶ z) (t : b ⟶ y) (u : y ⟶ z)
    (v₁ : a ⟶ w) (v₂ : w ⟶ y)
    (hP : P = p ≫ q) (h1 : q ≫ s = t ≫ u) (h2 : p ≫ t = v₁ ≫ v₂) :
    P ≫ s = v₁ ≫ v₂ ≫ u := by
  rw [hP, Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

/-- **The comparison `Fᴰ ⋙ Gᴰ ≅ Hᴰ` attached to `e : F ⋙ G ≅ H` splits** into the comparison of
the two descents of `F ⋙ G` and the descent of `e`.  Both sides lift the same transformation
through `DerivedCategory.Q`, where each is the three canonical factorizations with the degreewise
`e` in the middle.

`CategoryTheory.Functor.mapDerivedCategoryCompIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` are two constructions of the same
comparison at two different signatures; this is what lets the composition and isomorphism laws
proved for the second be used for the first. -/
theorem mapDerivedCategoryCompIso_hom_eq (e : F ⋙ G ≅ H) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ G) H e).hom :=
  rfl

/-- **The composition comparison at an object placed in degree `n`.** -/
theorem mapDerivedCategorySingleFunctor_compIso (e : F ⋙ G ≅ H) (n : ℤ) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C₁ n)
          (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom ≫
        (H.mapDerivedCategorySingleFunctor n).hom =
      Functor.whiskerRight (F.mapDerivedCategorySingleFunctor n).hom G.mapDerivedCategory ≫
        Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor n).hom ≫
          Functor.whiskerRight e.hom (DerivedCategory.singleFunctor C₃ n) :=
  split_cross _ _ _ _ _ _ _ _
    (congrArg (Functor.whiskerLeft (DerivedCategory.singleFunctor C₁ n))
        (mapDerivedCategoryCompIso_hom_eq e) |>.trans
      (Functor.whiskerLeft_comp _ _ _))
    (Functor.mapDerivedCategorySingleFunctor_isoOfNatIso (F ⋙ G) H e n)
    (Functor.mapDerivedCategorySingleFunctor_comp F G n)

/-- **The composition comparison on degree-`n` cohomology.** -/
theorem mapDerivedCategoryHomologyIso_compIso (e : F ⋙ G ≅ H) (n : ℤ) :
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom
          (DerivedCategory.homologyFunctor C₃ n) ≫
        (H.mapDerivedCategoryHomologyIso n).hom =
      Functor.whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (F.mapDerivedCategoryHomologyIso n).hom G ≫
          Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) e.hom := by
  simp only [Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso]
  exact split_cross _ _ _ _ _ _ _ _
    (congrArg (fun τ => Functor.whiskerRight τ (DerivedCategory.homologyFunctor C₃ n))
        (mapDerivedCategoryCompIso_hom_eq e) |>.trans
      (Functor.whiskerRight_comp _ _ _))
    (Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso (F ⋙ G) H e n)
    (Functor.mapDerivedCategoryHomologyFunctorIso_comp F G n)

end CompIso

/-! ### The crossing attached to two composition comparisons -/

section CompIsoPair

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type uA} [Category.{vA} C₁] [Abelian C₁] [HasDerivedCategory.{wA} C₁]
  {C₂ : Type uB} [Category.{vB} C₂] [Abelian C₂] [HasDerivedCategory.{wB} C₂]
  {C₃ : Type uC} [Category.{vC} C₃] [Abelian C₃] [HasDerivedCategory.{wC} C₃]
  {C₄ : Type uA'} [Category.{vA'} C₄] [Abelian C₄] [HasDerivedCategory.{wA'} C₄]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F₂ : C₁ ⥤ C₄) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (G₂ : C₄ ⥤ C₃) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  (N : C₁ ⥤ C₃) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
  (e₁ : F ⋙ G ≅ N) (e₂ : F₂ ⋙ G₂ ≅ N)

/-- The chase behind the two coherences below: the comparison for the second pair is cancelled
against its inverse, the two crossings are composed, and the comparison for the first pair is
read off.

Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem pair_chase {D : Type*} [Category* D] {o p q r z y₂ x₂ u : D}
    (pg : o ⟶ p) (p2 : p ⟶ q) (p1 : o ⟶ q) (s : q ⟶ z)
    (y1 : p ⟶ y₂) (y2 : y₂ ⟶ r) (h2 : r ⟶ z) (hinv2 : z ⟶ r)
    (x1 : o ⟶ x₂) (x2 : x₂ ⟶ u) (h1 : u ⟶ z) (cc : u ⟶ r)
    (hpg : pg ≫ p2 = p1) (hA2 : p2 ≫ s = y1 ≫ y2 ≫ h2)
    (hA1 : p1 ≫ s = x1 ≫ x2 ≫ h1)
    (hinv : h2 ≫ hinv2 = CategoryStruct.id r) (hc : h1 ≫ hinv2 = cc) :
    pg ≫ y1 ≫ y2 = x1 ≫ x2 ≫ cc := by
  rw [← hc, ← reassoc_of% hA1, ← hpg, Category.assoc, reassoc_of% hA2, hinv, Category.comp_id]

/-- **A crossing of two pairs of exact functors is compatible with the single functors.**  For
`e₁ : F ⋙ G ≅ N` and `e₂ : F₂ ⋙ G₂ ≅ N` the derived crossing `Fᴰ ⋙ Gᴰ ≅ F₂ᴰ ⋙ G₂ᴰ` built from
the two composition comparisons agrees, on an object placed in degree `0`, with the underived
crossing `e₁ ≪≫ e₂.symm`. -/
theorem crossingPair_single :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C₁ 0)
          (Functor.mapDerivedCategoryCompIsoOfCompIso e₁ ≪≫
            (Functor.mapDerivedCategoryCompIsoOfCompIso e₂).symm).hom ≫
        Functor.whiskerRight (F₂.mapDerivedCategorySingleFunctor 0).hom G₂.mapDerivedCategory ≫
          Functor.whiskerLeft F₂ (G₂.mapDerivedCategorySingleFunctor 0).hom =
      Functor.whiskerRight (F.mapDerivedCategorySingleFunctor 0).hom G.mapDerivedCategory ≫
        Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor 0).hom ≫
          Functor.whiskerRight (e₁ ≪≫ e₂.symm).hom (DerivedCategory.singleFunctor C₃ 0) := by
  refine pair_chase _ _ _ _ _ _ _
    (Functor.whiskerRight e₂.inv (DerivedCategory.singleFunctor C₃ 0)) _ _ _ _ ?_
    (mapDerivedCategorySingleFunctor_compIso e₂ 0)
    (mapDerivedCategorySingleFunctor_compIso e₁ 0) ?_ ?_
  · rw [← Functor.whiskerLeft_comp]
    congr 1
    simp
  · rw [← Functor.whiskerRight_comp]
    simp
  · exact (Functor.whiskerRight_comp _ _ _).symm

/-- **A crossing of two pairs of exact functors is compatible with degree-`n` cohomology.**  The
companion of `crossingPair_single`, for the other end of the chain. -/
theorem crossingPair_homology (n : ℤ) :
    Functor.whiskerRight
          (Functor.mapDerivedCategoryCompIsoOfCompIso e₁ ≪≫
            (Functor.mapDerivedCategoryCompIsoOfCompIso e₂).symm).hom
          (DerivedCategory.homologyFunctor C₃ n) ≫
        Functor.whiskerLeft F₂.mapDerivedCategory (G₂.mapDerivedCategoryHomologyIso n).hom ≫
          Functor.whiskerRight (F₂.mapDerivedCategoryHomologyIso n).hom G₂ =
      Functor.whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (F.mapDerivedCategoryHomologyIso n).hom G ≫
          Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) (e₁ ≪≫ e₂.symm).hom := by
  refine pair_chase _ _ _ _ _ _ _
    (Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) e₂.inv) _ _ _ _ ?_
    (mapDerivedCategoryHomologyIso_compIso e₂ n)
    (mapDerivedCategoryHomologyIso_compIso e₁ n) ?_ ?_
  · rw [← Functor.whiskerRight_comp]
    congr 1
    simp
  · rw [← Functor.whiskerLeft_comp]
    simp
  · exact (Functor.whiskerLeft_comp _ _ _).symm

end CompIsoPair

section Pull

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- **An exact functor applied after a functor of derived categories comes out of the degree-`n`
cohomology.** -/
def singleHomologyPullOuter (W : DerivedCategory A ⥤ DerivedCategory B) (F : B ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ (W ⋙ F.mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor C n ≅
      (DerivedCategory.singleFunctor A 0 ⋙ W ⋙ DerivedCategory.homologyFunctor B n) ⋙ F :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0 ⋙ W)
    (F.mapDerivedCategoryHomologyIso n)

/-- **An exact functor applied before a functor of derived categories comes out of the object
placed in degree `0`.** -/
def singleHomologyPullInner (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (W : DerivedCategory B ⥤ DerivedCategory C) (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ (F.mapDerivedCategory ⋙ W) ⋙
        DerivedCategory.homologyFunctor C n ≅
      F ⋙ DerivedCategory.singleFunctor B 0 ⋙ W ⋙ DerivedCategory.homologyFunctor C n :=
  Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0)
    (W ⋙ DerivedCategory.homologyFunctor C n)

/-- **`Hⁿ` at an object in degree `0`, of a morphism of functors of derived categories.** -/
abbrev singleHomologyMap {W W' : DerivedCategory A ⥤ DerivedCategory B} (τ : W ⟶ W') (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ W ⋙ DerivedCategory.homologyFunctor B n ⟶
      DerivedCategory.singleFunctor A 0 ⋙ W' ⋙ DerivedCategory.homologyFunctor B n :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor A 0)
    (Functor.whiskerRight τ (DerivedCategory.homologyFunctor B n))

/-- `singleHomologyPullOuter` is natural in the functor of derived categories. -/
theorem singleHomologyPullOuter_naturality {W W' : DerivedCategory A ⥤ DerivedCategory B}
    (τ : W ⟶ W') (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    singleHomologyMap (Functor.whiskerRight τ F.mapDerivedCategory) n ≫
        (singleHomologyPullOuter W' F n).hom =
      (singleHomologyPullOuter W F n).hom ≫
        Functor.whiskerRight (singleHomologyMap τ n) F := by
  ext X
  exact (F.mapDerivedCategoryHomologyIso n).hom.naturality (τ.app _)

/-- `singleHomologyPullInner` is natural in the functor of derived categories. -/
theorem singleHomologyPullInner_naturality (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {W W' : DerivedCategory B ⥤ DerivedCategory C} (τ : W ⟶ W')
    (n : ℤ) :
    singleHomologyMap (Functor.whiskerLeft F.mapDerivedCategory τ) n ≫
        (singleHomologyPullInner F W' n).hom =
      (singleHomologyPullInner F W n).hom ≫
        Functor.whiskerLeft F (singleHomologyMap τ n) := by
  ext X
  exact ((DerivedCategory.homologyFunctor C n).map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.homologyFunctor C n).map
      (τ.naturality ((F.mapDerivedCategorySingleFunctor 0).hom.app X)).symm).trans
      ((DerivedCategory.homologyFunctor C n).map_comp _ _))

/-- **The outer pull is the post-composition comparison of
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge`**,
which is the shape the bridge between the classical and the derived excision is stated at. -/
theorem singleHomologyPullOuter_hom (W : DerivedCategory A ⥤ DerivedCategory A) (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    (singleHomologyPullOuter W F n).hom = postCompSingleHomologyNatTrans F W n := rfl

/-- **The inner pull is the pre-composition comparison of
`StacksFrontier.Homology.DerivedIndexing.PreCompositionCoherence`**, likewise. -/
theorem singleHomologyPullInner_hom (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (W : DerivedCategory B ⥤ DerivedCategory C) (n : ℤ) :
    (singleHomologyPullInner F W n).hom = preCompSingleHomologyNatTrans F W n := rfl

/-- **The two pulls commute.**  Pulling an exact functor out of the cohomology and pulling
another out of the object placed in degree `0` act at the two ends of the chain, so the order
does not matter; the two routes differ by one naturality square of
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`. -/
theorem singleHomologyPull_comm (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {C' : Type*} [Category* C'] [Abelian C'] [HasDerivedCategory C']
    (W : DerivedCategory B ⥤ DerivedCategory C) (K : C ⥤ C') [K.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (n : ℤ) :
    (singleHomologyPullOuter (F.mapDerivedCategory ⋙ W) K n).hom ≫
        Functor.whiskerRight (singleHomologyPullInner F W n).hom K =
      (singleHomologyPullInner F (W ⋙ K.mapDerivedCategory) n).hom ≫
        Functor.whiskerLeft F (singleHomologyPullOuter W K n).hom := by
  ext X
  exact ((K.mapDerivedCategoryHomologyIso n).hom.naturality
    (W.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X))).symm

end Pull

/-! ### The degree-`n` reading of a comparison of total derived functors -/

section LegSource

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (S : A ⥤ A) [S.Additive]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The source corner**: the degree-`n` cohomology of `RS` followed by `Φ`, at an object placed
in degree `0`, is `RⁿS` followed by `Φ`.  The exact functor `Φ` comes out of the cohomology by
`singleHomologyPullOuter` and what is left is the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` for `S`. -/
def forgetLegSource (n : ℕ) :
    DerivedCategory.singleFunctor A 0 ⋙ (RS ⋙ Φ.mapDerivedCategory) ⋙
        DerivedCategory.homologyFunctor B (n : ℤ) ≅ S.rightDerived n ⋙ Φ :=
  singleHomologyPullOuter RS Φ (n : ℤ) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S RS αS hres n) Φ

/-- The source corner, written out: the pull followed by the bridge under `Φ`. -/
theorem forgetLegSource_hom (n : ℕ) :
    (forgetLegSource S Φ RS αS hres n).hom =
      (singleHomologyPullOuter RS Φ (n : ℤ)).hom ≫
        Functor.whiskerRight
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S RS αS
            hres n).hom Φ :=
  rfl

end LegSource

section LegTarget

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B] [HasDerivedCategory.{wB} B]
  (T : B ⥤ B) [T.Additive]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (RT : DerivedCategory B ⥤ DerivedCategory B)
  (αT : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RT)
  [RT.IsRightDerivedFunctor αT (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (hres' : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The target corner**: the degree-`n` cohomology of `Φ` followed by `RT`, at an object placed
in degree `0`, is `Φ` followed by `RⁿT`.  The exact functor `Φ` comes out of the object placed in
degree `0` by `singleHomologyPullInner` and what is left is the bridge for `T`. -/
def forgetLegTarget (n : ℕ) :
    DerivedCategory.singleFunctor A 0 ⋙ (Φ.mapDerivedCategory ⋙ RT) ⋙
        DerivedCategory.homologyFunctor B (n : ℤ) ≅ Φ ⋙ T.rightDerived n :=
  singleHomologyPullInner Φ RT (n : ℤ) ≪≫
    Functor.isoWhiskerLeft Φ
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived T RT αT hres' n)

/-- The target corner, written out: the pull followed by the bridge after `Φ`. -/
theorem forgetLegTarget_hom (n : ℕ) :
    (forgetLegTarget T Φ RT αT hres' n).hom =
      (singleHomologyPullInner Φ RT (n : ℤ)).hom ≫
        Functor.whiskerLeft Φ
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived T RT αT
            hres' n).hom :=
  rfl

end LegTarget

section Leg

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B] [HasDerivedCategory.{wB} B]
  (S : A ⥤ A) [S.Additive] (T : B ⥤ B) [T.Additive]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RT : DerivedCategory B ⥤ DerivedCategory B)
  (αT : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RT)
  [RT.IsRightDerivedFunctor αT (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (φ : RS ⋙ Φ.mapDerivedCategory ⟶ Φ.mapDerivedCategory ⋙ RT)
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hres' : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The degree-`n` reading of a comparison `RS ⋙ Φᴰ ⟶ Φᴰ ⋙ RT` of total right derived
functors**: a morphism `RⁿS ⋙ Φ ⟶ Φ ⋙ RⁿT` of the classical, `ℕ`-indexed right derived functors.

It is the degree-`n` cohomology of the comparison at an object placed in degree `0`, read through
the two corners.  This is the construction of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso`, at a bare
endofunctor-and-forgetful-functor datum. -/
def degreewiseForgetComparison (n : ℕ) : S.rightDerived n ⋙ Φ ⟶ Φ ⋙ T.rightDerived n :=
  (forgetLegSource S Φ RS αS hres n).inv ≫ singleHomologyMap φ (n : ℤ) ≫
    (forgetLegTarget T Φ RT αT hres' n).hom

/-- **What pins the degree-`n` reading down**: the degree-`n` cohomology of the comparison,
followed by the target corner, is the source corner followed by the reading. -/
theorem degreewiseForgetComparison_fac (n : ℕ) :
    singleHomologyMap φ (n : ℤ) ≫ (forgetLegTarget T Φ RT αT hres' n).hom =
      (forgetLegSource S Φ RS αS hres n).hom ≫
        degreewiseForgetComparison S T Φ RS αS RT αT φ hres hres' n :=
  (Iso.hom_inv_id_assoc (forgetLegSource S Φ RS αS hres n) _).symm

/-- **The degree-`n` reading of an invertible comparison is invertible.** -/
def degreewiseForgetIso (n : ℕ) [IsIso φ] : S.rightDerived n ⋙ Φ ≅ Φ ⋙ T.rightDerived n :=
  (forgetLegSource S Φ RS αS hres n).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0)
      (Functor.isoWhiskerRight (asIso φ) (DerivedCategory.homologyFunctor B (n : ℤ))) ≪≫
    forgetLegTarget T Φ RT αT hres' n

/-- `degreewiseForgetIso` is `degreewiseForgetComparison`. -/
theorem degreewiseForgetIso_hom (n : ℕ) [IsIso φ] :
    (degreewiseForgetIso S T Φ RS αS RT αT φ hres hres' n).hom =
      degreewiseForgetComparison S T Φ RS αS RT αT φ hres hres' n :=
  rfl

end Leg

/-! ### The two formal chases of the square -/

/-- The chase that assembles a crossing leg: the key equation holds before the last factor, and
the last factor crosses it.

Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem cross_assemble {D : Type*} [Category* D] {x y₁ y₂ w v z₁ z₂ u : D}
    (t : x ⟶ y₁) (p₃ : y₁ ⟶ y₂) (q₃ : y₂ ⟶ w) (b₃ : w ⟶ v)
    (p₂ : x ⟶ z₁) (q₂ : z₁ ⟶ z₂) (cc : z₂ ⟶ w) (b₂ : z₂ ⟶ u) (cv : u ⟶ v)
    (hkey : t ≫ p₃ ≫ q₃ = p₂ ≫ q₂ ≫ cc) (hex : b₂ ≫ cv = cc ≫ b₃) :
    t ≫ p₃ ≫ q₃ ≫ b₃ = (p₂ ≫ q₂ ≫ b₂) ≫ cv := by
  rw [reassoc_of% hkey, ← hex]
  simp only [Category.assoc]

/-- The ladder that turns the derived square into the degree-`n` one: the two sides of the
derived square agree, each leg is conjugated by the corner comparisons, and the source corner is
cancelled.

Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private theorem ladder {D : Type*} [Category* D]
    {q₀ q₁ q₂ q₃ r₁ r₂ p₀ p₁ p₂ p₃ s₁ s₂ : D}
    (a₁ : q₀ ⟶ q₁) (a₂ : q₁ ⟶ q₂) (a₃ : q₂ ⟶ q₃)
    (b₁ : q₀ ⟶ r₁) (b₂ : r₁ ⟶ r₂) (b₃ : r₂ ⟶ q₃)
    (k₀ : q₀ ⟶ p₀) (k₁ : q₁ ⟶ p₁) (k₂ : q₂ ⟶ p₂) (k₃ : q₃ ⟶ p₃)
    (l₁ : r₁ ⟶ s₁) (l₂ : r₂ ⟶ s₂)
    (d₁ : p₀ ⟶ p₁) (d₂ : p₁ ⟶ p₂) (d₃ : p₂ ⟶ p₃)
    (g₁ : p₀ ⟶ s₁) (g₂ : s₁ ⟶ s₂) (g₃ : s₂ ⟶ p₃)
    (k₀inv : p₀ ⟶ q₀) (hk : k₀inv ≫ k₀ = CategoryStruct.id p₀)
    (e₁ : a₁ ≫ k₁ = k₀ ≫ d₁) (e₂ : a₂ ≫ k₂ = k₁ ≫ d₂) (e₃ : a₃ ≫ k₃ = k₂ ≫ d₃)
    (f₁ : b₁ ≫ l₁ = k₀ ≫ g₁) (f₂ : b₂ ≫ l₂ = l₁ ≫ g₂) (f₃ : b₃ ≫ k₃ = l₂ ≫ g₃)
    (hsq : a₁ ≫ a₂ ≫ a₃ = b₁ ≫ b₂ ≫ b₃) :
    d₁ ≫ d₂ ≫ d₃ = g₁ ≫ g₂ ≫ g₃ := by
  have : IsSplitEpi k₀ := IsSplitEpi.mk' ⟨k₀inv, hk⟩
  rw [← cancel_epi k₀, ← reassoc_of% e₁, ← reassoc_of% e₂, ← e₃, reassoc_of% hsq, f₃,
    reassoc_of% f₂, reassoc_of% f₁]


/-! ### The bridge from the classical to the derived excision, in the shape of the square -/

section BridgeShape

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
    [HasDerivedCategory.{wA'} A']
  (S : A ⥤ A) [S.Additive] (S' : A' ⥤ A') [S'.Additive]
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects]
  (e : S ⋙ L ≅ L ⋙ S')
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RS' : DerivedCategory A' ⥤ DerivedCategory A')
  (αS' : S'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS')
  [RS'.IsRightDerivedFunctor αS' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  [(RS ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
    (Stacks.DerivedFunctor.postcomposeUnit S L RS αS)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(L.mapDerivedCategory ⋙ RS').IsRightDerivedFunctor
    (Stacks.DerivedFunctor.precomposeUnit L S' RS' αS')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hres' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The classical excision is the degree-`n` reading of the derived excision**, in the shape the
degree-`n` square consumes.  This is
`Stacks.DerivedIndexing.classicalExcision_eq_derivedExcision` with the two comparisons it is
stated at recognised as the two corners `forgetLegSource` and `forgetLegTarget`, which they are
on the nose. -/
theorem classicalExcision_bridge (n : ℕ) :
    singleHomologyMap (derivedExcisionNatIso S S' L e RS αS RS' αS').hom (n : ℤ) ≫
        (forgetLegTarget S' L RS' αS' hres' n).hom =
      (forgetLegSource S L RS αS hres n).hom ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S L (L ⋙ S') e n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L S' n).hom := by
  rw [forgetLegTarget_hom, forgetLegSource_hom, singleHomologyPullInner_hom,
    singleHomologyPullOuter_hom]
  exact (classicalExcision_eq_derivedExcision S S' L e RS αS RS' αS' hres hres' n).trans
    (Category.assoc _ _ _).symm

end BridgeShape

/-! ### The degree-`n` square -/

section Square

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
    [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [EnoughInjectives B']
    [HasDerivedCategory.{wB'} B']
  (S : A ⥤ A) [S.Additive] (S' : A' ⥤ A') [S'.Additive]
  (T : B ⥤ B) [T.Additive] (T' : B' ⥤ B') [T'.Additive]
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (M : B ⥤ B') [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (Φ' : A' ⥤ B') [Φ'.Additive] [PreservesFiniteLimits Φ'] [PreservesFiniteColimits Φ']
  (RS : DerivedCategory A ⥤ DerivedCategory A)
  (αS : S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS)
  [RS.IsRightDerivedFunctor αS (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RS' : DerivedCategory A' ⥤ DerivedCategory A')
  (αS' : S'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RS')
  [RS'.IsRightDerivedFunctor αS' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (RT : DerivedCategory B ⥤ DerivedCategory B)
  (αT : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RT)
  [RT.IsRightDerivedFunctor αT (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (RT' : DerivedCategory B' ⥤ DerivedCategory B')
  (αT' : T'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RT')
  [RT'.IsRightDerivedFunctor αT' (HomotopyCategory.quasiIso B' (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hA' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hB' : ∀ K : CochainComplex B' ℤ, ∃ (I : CochainComplex B' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (n : ℕ)

/-! #### The two corners that occur in two shapes -/

/-- **The excised corner in its two shapes.**  `Rⁿ Ṡ` read after `L` and `Φ'` can be reached
either by pulling `Φ'` out of the cohomology and then `L` out of the object in degree `0`, or the
other way round; the two routes agree by `singleHomologyPull_comm`. -/
theorem excisionCorner_shape :
    (singleHomologyPullOuter (L.mapDerivedCategory ⋙ RS') Φ' (n : ℤ)).hom ≫
        Functor.whiskerRight (forgetLegTarget S' L RS' αS' hA' n).hom Φ' =
      (singleHomologyPullInner L (RS' ⋙ Φ'.mapDerivedCategory) (n : ℤ)).hom ≫
        Functor.whiskerLeft L (forgetLegSource S' Φ' RS' αS' hA' n).hom := by
  rw [forgetLegTarget_hom, forgetLegSource_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, ← Category.assoc, singleHomologyPull_comm, Category.assoc]
  rfl

/-- **The forgotten corner in its two shapes**, the same statement on the other side of the
square. -/
theorem forgetCorner_shape :
    (singleHomologyPullOuter (Φ.mapDerivedCategory ⋙ RT) M (n : ℤ)).hom ≫
        Functor.whiskerRight (forgetLegTarget T Φ RT αT hB n).hom M =
      (singleHomologyPullInner Φ (RT ⋙ M.mapDerivedCategory) (n : ℤ)).hom ≫
        Functor.whiskerLeft Φ (forgetLegSource T M RT αT hB n).hom :=
  excisionCorner_shape T Φ M RT αT hB n

/-! #### The six legs -/

/-- **The excision leg**: the degree-`n` cohomology of the derived excision for `S`, read through
the two corners, is the classical excision whiskered with `Φ'`. -/
theorem degreewiseExcisionLeg
    (me : RS ⋙ L.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ RS')
    (Emod : S.rightDerived n ⋙ L ≅ L ⋙ S'.rightDerived n)
    (hme : singleHomologyMap me.hom (n : ℤ) ≫ (forgetLegTarget S' L RS' αS' hA' n).hom =
      (forgetLegSource S L RS αS hA n).hom ≫ Emod.hom) :
    singleHomologyMap (Functor.whiskerRight me.hom Φ'.mapDerivedCategory) (n : ℤ) ≫
        ((singleHomologyPullOuter (L.mapDerivedCategory ⋙ RS') Φ' (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegTarget S' L RS' αS' hA' n).hom Φ') =
      ((singleHomologyPullOuter (RS ⋙ L.mapDerivedCategory) Φ' (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegSource S L RS αS hA n).hom Φ') ≫
        Functor.whiskerRight Emod.hom Φ' := by
  rw [← Category.assoc, singleHomologyPullOuter_naturality, Category.assoc,
    ← Functor.whiskerRight_comp, hme, Functor.whiskerRight_comp, Category.assoc]

/-- **The forgetful leg on the open part**: the degree-`n` cohomology of [Stacks, Tag 0G74]
part (2) on `U`, read through the two corners, is the degree-`n` forgetful comparison whiskered
with `L`. -/
theorem degreewiseOpenForgetLeg
    (φ' : RS' ⋙ Φ'.mapDerivedCategory ⟶ Φ'.mapDerivedCategory ⋙ RT') :
    singleHomologyMap (Functor.whiskerLeft L.mapDerivedCategory φ') (n : ℤ) ≫
        ((singleHomologyPullInner L (Φ'.mapDerivedCategory ⋙ RT') (n : ℤ)).hom ≫
          Functor.whiskerLeft L (forgetLegTarget T' Φ' RT' αT' hB' n).hom) =
      ((singleHomologyPullOuter (L.mapDerivedCategory ⋙ RS') Φ' (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegTarget S' L RS' αS' hA' n).hom Φ') ≫
        Functor.whiskerLeft L
          (degreewiseForgetComparison S' T' Φ' RS' αS' RT' αT' φ' hA' hB' n) := by
  rw [excisionCorner_shape, ← Category.assoc, singleHomologyPullInner_naturality,
    Category.assoc, ← Functor.whiskerLeft_comp,
    degreewiseForgetComparison_fac S' T' Φ' RS' αS' RT' αT' φ' hA' hB' n,
    Functor.whiskerLeft_comp, Category.assoc]

/-- **The crossing leg on the open part**: the degree-`n` cohomology of the derived crossing,
read through the two corners, is the underived crossing whiskered with `Rⁿ Ṡ'`. -/
theorem degreewiseOpenCrossLeg
    (γ : L.mapDerivedCategory ⋙ Φ'.mapDerivedCategory ≅
      Φ.mapDerivedCategory ⋙ M.mapDerivedCategory)
    (c : L ⋙ Φ' ≅ Φ ⋙ M)
    (hγS : Functor.whiskerLeft (DerivedCategory.singleFunctor A 0) γ.hom ≫
        Functor.whiskerRight (Φ.mapDerivedCategorySingleFunctor 0).hom M.mapDerivedCategory ≫
          Functor.whiskerLeft Φ (M.mapDerivedCategorySingleFunctor 0).hom =
      Functor.whiskerRight (L.mapDerivedCategorySingleFunctor 0).hom Φ'.mapDerivedCategory ≫
        Functor.whiskerLeft L (Φ'.mapDerivedCategorySingleFunctor 0).hom ≫
          Functor.whiskerRight c.hom (DerivedCategory.singleFunctor B' 0)) :
    singleHomologyMap (Functor.whiskerRight γ.hom RT') (n : ℤ) ≫
        ((singleHomologyPullInner Φ (M.mapDerivedCategory ⋙ RT') (n : ℤ)).hom ≫
          Functor.whiskerLeft Φ (forgetLegTarget T' M RT' αT' hB' n).hom) =
      ((singleHomologyPullInner L (Φ'.mapDerivedCategory ⋙ RT') (n : ℤ)).hom ≫
          Functor.whiskerLeft L (forgetLegTarget T' Φ' RT' αT' hB' n).hom) ≫
        Functor.whiskerRight c.hom (T'.rightDerived n) := by
  rw [forgetLegTarget_hom, forgetLegTarget_hom, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp]
  have key := congrArg (fun τ => Functor.whiskerRight τ
    (RT' ⋙ DerivedCategory.homologyFunctor B' (n : ℤ))) hγS
  simp only [Functor.whiskerRight_comp] at key
  exact cross_assemble _ _ _ _ _ _ _ _ _ key
    (Functor.whiskerLeft_comp_whiskerRight c.hom
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived T' RT' αT'
        hB' n).hom)

/-- **The crossing leg on the ambient part**: the degree-`n` cohomology of the derived crossing
after `RS`, read through the two corners, is the underived crossing after `Rⁿ S`. -/
theorem degreewiseCrossLeg
    (γ : L.mapDerivedCategory ⋙ Φ'.mapDerivedCategory ≅
      Φ.mapDerivedCategory ⋙ M.mapDerivedCategory)
    (c : L ⋙ Φ' ≅ Φ ⋙ M)
    (hγH : Functor.whiskerRight γ.hom (DerivedCategory.homologyFunctor B' (n : ℤ)) ≫
        Functor.whiskerLeft Φ.mapDerivedCategory
            (M.mapDerivedCategoryHomologyIso (n : ℤ)).hom ≫
          Functor.whiskerRight (Φ.mapDerivedCategoryHomologyIso (n : ℤ)).hom M =
      Functor.whiskerLeft L.mapDerivedCategory
          (Φ'.mapDerivedCategoryHomologyIso (n : ℤ)).hom ≫
        Functor.whiskerRight (L.mapDerivedCategoryHomologyIso (n : ℤ)).hom Φ' ≫
          Functor.whiskerLeft (DerivedCategory.homologyFunctor A (n : ℤ)) c.hom) :
    singleHomologyMap (Functor.whiskerLeft RS γ.hom) (n : ℤ) ≫
        ((singleHomologyPullOuter (RS ⋙ Φ.mapDerivedCategory) M (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegSource S Φ RS αS hA n).hom M) =
      ((singleHomologyPullOuter (RS ⋙ L.mapDerivedCategory) Φ' (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegSource S L RS αS hA n).hom Φ') ≫
        Functor.whiskerLeft (S.rightDerived n) c.hom := by
  rw [forgetLegSource_hom, forgetLegSource_hom, Functor.whiskerRight_comp,
    Functor.whiskerRight_comp]
  have key := congrArg (fun τ => Functor.whiskerLeft
    (DerivedCategory.singleFunctor A 0 ⋙ RS) τ) hγH
  simp only [Functor.whiskerLeft_comp] at key
  exact cross_assemble _ _ _ _ _ _ _ _ _ key
    (Functor.whiskerLeft_comp_whiskerRight
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived S RS αS hA n).hom
      c.hom).symm

/-- **The forgetful leg on the ambient part**: the degree-`n` cohomology of [Stacks, Tag 0G74]
part (2) on `X`, read through the two corners, is the degree-`n` forgetful comparison whiskered
with `M`. -/
theorem degreewiseForgetLeg
    (φ : RS ⋙ Φ.mapDerivedCategory ⟶ Φ.mapDerivedCategory ⋙ RT) :
    singleHomologyMap (Functor.whiskerRight φ M.mapDerivedCategory) (n : ℤ) ≫
        ((singleHomologyPullOuter (Φ.mapDerivedCategory ⋙ RT) M (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegTarget T Φ RT αT hB n).hom M) =
      ((singleHomologyPullOuter (RS ⋙ Φ.mapDerivedCategory) M (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegSource S Φ RS αS hA n).hom M) ≫
        Functor.whiskerRight
          (degreewiseForgetComparison S T Φ RS αS RT αT φ hA hB n) M := by
  rw [← Category.assoc, singleHomologyPullOuter_naturality, Category.assoc,
    ← Functor.whiskerRight_comp,
    degreewiseForgetComparison_fac S T Φ RS αS RT αT φ hA hB n,
    Functor.whiskerRight_comp, Category.assoc]

/-- **The abelian excision leg**: the degree-`n` cohomology of the derived excision for `Ṡ`,
read through the two corners, is the classical abelian excision after `Φ`. -/
theorem degreewiseAbelianExcisionLeg
    (ae : RT ⋙ M.mapDerivedCategory ≅ M.mapDerivedCategory ⋙ RT')
    (Eab : T.rightDerived n ⋙ M ≅ M ⋙ T'.rightDerived n)
    (hae : singleHomologyMap ae.hom (n : ℤ) ≫ (forgetLegTarget T' M RT' αT' hB' n).hom =
      (forgetLegSource T M RT αT hB n).hom ≫ Eab.hom) :
    singleHomologyMap (Functor.whiskerLeft Φ.mapDerivedCategory ae.hom) (n : ℤ) ≫
        ((singleHomologyPullInner Φ (M.mapDerivedCategory ⋙ RT') (n : ℤ)).hom ≫
          Functor.whiskerLeft Φ (forgetLegTarget T' M RT' αT' hB' n).hom) =
      ((singleHomologyPullOuter (Φ.mapDerivedCategory ⋙ RT) M (n : ℤ)).hom ≫
          Functor.whiskerRight (forgetLegTarget T Φ RT αT hB n).hom M) ≫
        Functor.whiskerLeft Φ Eab.hom := by
  rw [forgetCorner_shape, ← Category.assoc, singleHomologyPullInner_naturality,
    Category.assoc, ← Functor.whiskerLeft_comp, hae, Functor.whiskerLeft_comp,
    Category.assoc]

/-! #### The square -/

/-- **A commuting square of total right derived functors commutes in every degree.**

Let `S`, `Ṡ` be additive endofunctors of `𝒜`, `𝒜'` and `T`, `Ṫ` additive endofunctors of `ℬ`,
`ℬ'`; let `L : 𝒜 ⥤ 𝒜'`, `M : ℬ ⥤ ℬ'`, `Φ : 𝒜 ⥤ ℬ`, `Φ' : 𝒜' ⥤ ℬ'` be exact, with
`c : L ⋙ Φ' ≅ Φ ⋙ M`.  Given total right derived functors of the four endofunctors with their
units, a derived excision `me` on the `𝒜` side and `ae` on the `ℬ` side, derived forgetful
comparisons `φ` and `φ'`, a derived crossing `γ` compatible with `c` on objects placed in degree
`0` and on cohomology, and classical excisions `Emod`, `Eab` compatible with the derived ones
through the bridge — if the derived square commutes, then so does the degree-`n` square of the
classical excisions and the degree-`n` forgetful comparisons `degreewiseForgetComparison`.

The proof is the ladder: each of the six legs of the derived square, read in degree `n` at an
object placed in degree `0`, is conjugated by the corner comparisons into its classical
counterpart, the derived square supplies the equality of the two conjugated composites, and the
source corner — an isomorphism — is cancelled. -/
theorem forgetExcisionDegreewiseSquare
    (me : RS ⋙ L.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ RS')
    (ae : RT ⋙ M.mapDerivedCategory ≅ M.mapDerivedCategory ⋙ RT')
    (φ : RS ⋙ Φ.mapDerivedCategory ⟶ Φ.mapDerivedCategory ⋙ RT)
    (φ' : RS' ⋙ Φ'.mapDerivedCategory ⟶ Φ'.mapDerivedCategory ⋙ RT')
    (γ : L.mapDerivedCategory ⋙ Φ'.mapDerivedCategory ≅
      Φ.mapDerivedCategory ⋙ M.mapDerivedCategory)
    (c : L ⋙ Φ' ≅ Φ ⋙ M)
    (Emod : S.rightDerived n ⋙ L ≅ L ⋙ S'.rightDerived n)
    (Eab : T.rightDerived n ⋙ M ≅ M ⋙ T'.rightDerived n)
    (hme : singleHomologyMap me.hom (n : ℤ) ≫ (forgetLegTarget S' L RS' αS' hA' n).hom =
      (forgetLegSource S L RS αS hA n).hom ≫ Emod.hom)
    (hae : singleHomologyMap ae.hom (n : ℤ) ≫ (forgetLegTarget T' M RT' αT' hB' n).hom =
      (forgetLegSource T M RT αT hB n).hom ≫ Eab.hom)
    (hγS : Functor.whiskerLeft (DerivedCategory.singleFunctor A 0) γ.hom ≫
        Functor.whiskerRight (Φ.mapDerivedCategorySingleFunctor 0).hom M.mapDerivedCategory ≫
          Functor.whiskerLeft Φ (M.mapDerivedCategorySingleFunctor 0).hom =
      Functor.whiskerRight (L.mapDerivedCategorySingleFunctor 0).hom Φ'.mapDerivedCategory ≫
        Functor.whiskerLeft L (Φ'.mapDerivedCategorySingleFunctor 0).hom ≫
          Functor.whiskerRight c.hom (DerivedCategory.singleFunctor B' 0))
    (hγH : Functor.whiskerRight γ.hom (DerivedCategory.homologyFunctor B' (n : ℤ)) ≫
        Functor.whiskerLeft Φ.mapDerivedCategory
            (M.mapDerivedCategoryHomologyIso (n : ℤ)).hom ≫
          Functor.whiskerRight (Φ.mapDerivedCategoryHomologyIso (n : ℤ)).hom M =
      Functor.whiskerLeft L.mapDerivedCategory
          (Φ'.mapDerivedCategoryHomologyIso (n : ℤ)).hom ≫
        Functor.whiskerRight (L.mapDerivedCategoryHomologyIso (n : ℤ)).hom Φ' ≫
          Functor.whiskerLeft (DerivedCategory.homologyFunctor A (n : ℤ)) c.hom)
    (hderived : Functor.whiskerRight me.hom Φ'.mapDerivedCategory ≫
        Functor.whiskerLeft L.mapDerivedCategory φ' ≫ Functor.whiskerRight γ.hom RT' =
      Functor.whiskerLeft RS γ.hom ≫ Functor.whiskerRight φ M.mapDerivedCategory ≫
        Functor.whiskerLeft Φ.mapDerivedCategory ae.hom) :
    Functor.whiskerRight Emod.hom Φ' ≫
        Functor.whiskerLeft L
            (degreewiseForgetComparison S' T' Φ' RS' αS' RT' αT' φ' hA' hB' n) ≫
          Functor.whiskerRight c.hom (T'.rightDerived n) =
      Functor.whiskerLeft (S.rightDerived n) c.hom ≫
        Functor.whiskerRight (degreewiseForgetComparison S T Φ RS αS RT αT φ hA hB n) M ≫
          Functor.whiskerLeft Φ Eab.hom := by
  have hsq := congrArg (fun τ => Functor.whiskerLeft (DerivedCategory.singleFunctor A 0)
    (Functor.whiskerRight τ (DerivedCategory.homologyFunctor B' (n : ℤ)))) hderived
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp] at hsq
  exact ladder _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Iso.inv_hom_id (singleHomologyPullOuter (RS ⋙ L.mapDerivedCategory) Φ' (n : ℤ) ≪≫
      Functor.isoWhiskerRight (forgetLegSource S L RS αS hA n) Φ'))
    (degreewiseExcisionLeg S S' L Φ' RS αS RS' αS' hA hA' n me Emod hme)
    (degreewiseOpenForgetLeg S' T' L Φ' RS' αS' RT' αT' hA' hB' n φ')
    (degreewiseOpenCrossLeg T' L M Φ Φ' RT' αT' hB' n γ c hγS)
    (degreewiseCrossLeg S L M Φ Φ' RS αS hA n γ c hγH)
    (degreewiseForgetLeg S T M Φ RS αS RT αT hA hB n φ)
    (degreewiseAbelianExcisionLeg T T' M Φ RT αT RT' αT' hB hB' n ae Eab hae)
    hsq

end Square

end Stacks.DerivedIndexing

end
