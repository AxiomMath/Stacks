module

public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# A derived bifunctor descended along K-flat right factors only

Let `F : A ⥤ B ⥤ D` be an additive bifunctor between abelian categories, and let `P` be a
property of objects of `K(B)` such that every object satisfying `P` is K-flat for `F`, the
objects satisfying `P` localize to `D(B)` at the quasi-isomorphisms, and `Tot(F(K, -))` carries
quasi-isomorphisms between complexes satisfying `P` to quasi-isomorphisms, for every complex
`K` of objects of `A`.  Then `Tot(F(-, -))` descends to a bifunctor

`D(A) ⥤ D(B) ⥤ D(D)`,

computed by `Tot(F(K, L))` whenever `L` satisfies `P`, with no hypothesis on `K`.  This is the
construction of a derived tensor product by K-flat resolutions of the second factor alone.

## Main definitions

* `CochainComplex.KFlatBifunctor.derivedBifunctorOfRight`: the descended bifunctor.
* `CochainComplex.KFlatBifunctor.comparisonOfRight`: its value at `(K, L)` with `L` satisfying
  `P` is the class of `Tot(F(K, L))`.

## Main results

* `CochainComplex.KFlatBifunctor.comparisonOfRight_naturality`: the comparison is natural in
  both complexes, the right-hand map being the total complex of the pair of morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

/-- Four commuting squares paste to a commuting square.  Stated in an arbitrary category so
that it applies by unification alone. -/
theorem paste_four_squares {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : C}
    {m₀ : X₀ ⟶ Y₀} {m₁ : X₁ ⟶ Y₁} {m₂ : X₂ ⟶ Y₂} {m₃ : X₃ ⟶ Y₃} {m₄ : X₄ ⟶ Y₄}
    {a₁ : X₀ ⟶ X₁} {a₂ : X₁ ⟶ X₂} {a₃ : X₂ ⟶ X₃} {a₄ : X₃ ⟶ X₄}
    {b₁ : Y₀ ⟶ Y₁} {b₂ : Y₁ ⟶ Y₂} {b₃ : Y₂ ⟶ Y₃} {b₄ : Y₃ ⟶ Y₄}
    (h₁ : m₀ ≫ b₁ = a₁ ≫ m₁) (h₂ : m₁ ≫ b₂ = a₂ ≫ m₂) (h₃ : m₂ ≫ b₃ = a₃ ≫ m₃)
    (h₄ : m₃ ≫ b₄ = a₄ ≫ m₄) :
    m₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ m₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  (P : ObjectProperty (HomotopyCategory B (ComplexShape.up ℤ))) (hP : P ≤ kFlatObjects F)

/-- `Tot(F(-, -))` with its first variable descended to `D(A)` and its second restricted to the
objects satisfying `P`. -/
abbrev derivedToModelsRight :
    DerivedCategory A ⥤ P.FullSubcategory ⥤ DerivedCategory D :=
  derivedToDerivedRight F ⋙ (Functor.whiskeringLeft _ _ _).obj (ObjectProperty.ιOfLE hP)

/-- The objects satisfying `P`, viewed in `D(B)`. -/
abbrev modelsRightQ : P.FullSubcategory ⥤ DerivedCategory B :=
  P.ι ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms between objects satisfying `P`. -/
abbrev modelsRightW : MorphismProperty P.FullSubcategory :=
  (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).inverseImage P.ι

variable (hW : ∀ (K : CochainComplex A ℤ) {L L' : CochainComplex B ℤ} (g : L ⟶ L'),
    P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) →
    P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L') → QuasiIso g →
      QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).map g))

omit [HasDerivedCategory B] in
include hW in
/-- At the class of a complex, the descent in the first variable inverts the
quasi-isomorphisms between objects satisfying `P`. -/
theorem isIso_derivedToModelsRight_obj_map (K : CochainComplex A ℤ)
    {L L' : P.FullSubcategory} (w : L ⟶ L') (hw : modelsRightW P w) :
    IsIso (((derivedToModelsRight F P hP).obj (DerivedCategory.Q.obj K)).map w) := by
  rcases L with ⟨L, hL⟩
  rcases L' with ⟨L', hL'⟩
  obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨L₀', rfl⟩ := HomotopyCategory.quotient_obj_surjective L'
  rcases w with ⟨w⟩
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_surjective w
  have hQ : IsIso (DerivedCategory.Q.map (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map g)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hW K g hL hL'
      ((HomologicalComplex.mem_quasiIso_iff g).1
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hw)))
  have hQh : IsIso ((DerivedCategory.Qh (C := D)).map
      (((homotopyBifunctor F).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g))) := by
    have e : (DerivedCategory.Qh (C := D)).map
        (((homotopyBifunctor F).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) =
        (totalComplexQhIso F K L₀).hom ≫ DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) ≫ (totalComplexQhIso F K L₀').inv := by
      rw [← reassoc_of% (totalComplexQhIso_naturality_right F K g), Iso.hom_inv_id,
        Category.comp_id]
    rw [e]
    infer_instance
  exact (NatIso.isIso_map_iff ((derivedToDerivedRightFac F).app K)
    ((ObjectProperty.ιOfLE hP).map _)).2 hQh

omit [HasDerivedCategory B] in
include hW in
/-- **The descent in the first variable inverts the quasi-isomorphisms between objects
satisfying `P`**, uniformly in the first variable.  Every object of `D(A)` is the class of a
complex, and there it is `isIso_derivedToModelsRight_obj_map`. -/
theorem modelsRightW_isInvertedBy :
    (modelsRightW P).IsInvertedBy (derivedToModelsRight F P hP).flip := by
  intro L L' w hw
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ ?_)
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso X)]
  exact isIso_derivedToModelsRight_obj_map F P hP hW _ w hw

variable [(modelsRightQ P).IsLocalization (modelsRightW P)]

/-- The descent of `Tot(F(-, -))` to `D(B) ⥤ D(A) ⥤ D(D)`. -/
def derivedBifunctorOfRightFlip : DerivedCategory B ⥤ DerivedCategory A ⥤ DerivedCategory D :=
  Localization.lift (derivedToModelsRight F P hP).flip (modelsRightW_isInvertedBy F P hP hW)
    (modelsRightQ P)

/-- The descent agrees with the descent in the first variable on the objects satisfying `P`. -/
def derivedBifunctorOfRightFac :
    modelsRightQ P ⋙ derivedBifunctorOfRightFlip F P hP hW ≅
      (derivedToModelsRight F P hP).flip :=
  Localization.fac _ _ _

/-- **The derived bifunctor of `F`, by resolutions of the second factor by objects satisfying
`P`**: `D(A) ⥤ D(B) ⥤ D(D)`. -/
def derivedBifunctorOfRight : DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory D :=
  (derivedBifunctorOfRightFlip F P hP hW).flip

/-- **A complex satisfying `P` in the second variable computes the derived bifunctor**: its
value at `(K, L)` is the class of `Tot(F(K, L))`, for an arbitrary complex `K`. -/
def comparisonOfRight (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hL : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) :
    ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (totalComplex F K L) :=
  ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).mapIso
      ((DerivedCategory.quotientCompQhIso B).app L).symm ≪≫
    ((derivedBifunctorOfRightFac F P hP hW).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).app
        (DerivedCategory.Q.obj K) ≪≫
    ((derivedToDerivedRightFac F).app K).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ ≪≫
    totalComplexQhIso F K L

/-- The four factors of `comparisonOfRight`. -/
theorem comparisonOfRight_hom (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hL : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) :
    (comparisonOfRight F P hP hW K L hL).hom =
      ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctorOfRightFac F P hP hW).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).app
            (DerivedCategory.Q.obj K) ≫
        ((derivedToDerivedRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ ≫
        (totalComplexQhIso F K L).hom :=
  rfl

/-- **Naturality of `comparisonOfRight` in the arbitrary first complex.** -/
theorem comparisonOfRight_naturality_left
    {K K' : CochainComplex A ℤ} (f : K ⟶ K') (L : CochainComplex B ℤ)
    (hL : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) :
    ((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        (comparisonOfRight F P hP hW K' L hL).hom =
      (comparisonOfRight F P hP hW K L hL).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app L) := by
  have hA : ((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K')).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) =
      ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).app
          ((modelsRightQ P).obj
            ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) :=
    (((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).naturality _).symm
  have hB : ((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).app
          ((modelsRightQ P).obj
            ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩) ≫
        ((derivedBifunctorOfRightFac F P hP hW).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).app
            (DerivedCategory.Q.obj K') =
      ((derivedBifunctorOfRightFac F P hP hW).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).app
            (DerivedCategory.Q.obj K) ≫
        ((derivedToDerivedRight F).map (DerivedCategory.Q.map f)).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ :=
    ((derivedBifunctorOfRightFac F P hP hW).hom.app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).naturality
        (DerivedCategory.Q.map f)
  have hC : ((derivedToDerivedRight F).map (DerivedCategory.Q.map f)).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ ≫
        ((derivedToDerivedRightFac F).hom.app K').app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ =
      ((derivedToDerivedRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ ≫
        ((totalToDerivedRight F).map f).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ :=
    NatTrans.congr_app ((derivedToDerivedRightFac F).hom.naturality f)
      (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ :
        (kFlatObjects F).FullSubcategory)
  exact paste_four_squares hA hB hC (totalComplexQhIso_naturality_left F f L)

/-- **Naturality of `comparisonOfRight` in the second complex.** -/
theorem comparisonOfRight_naturality_right
    (K : CochainComplex A ℤ) {L L' : CochainComplex B ℤ} (g : L ⟶ L')
    (hL : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L))
    (hL' : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L')) :
    ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        (comparisonOfRight F P hP hW K L' hL').hom =
      (comparisonOfRight F P hP hW K L hL).hom ≫
        DerivedCategory.Q.map
          (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K).map g) := by
  let w : (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
      P.FullSubcategory) ⟶ ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L', hL'⟩ :=
    ObjectProperty.homMk ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)
  have hA : ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L') =
      ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.quotientCompQhIso B).inv.app L) ≫
        ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((modelsRightQ P).map w) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (DerivedCategory.quotientCompQhIso_inv_naturality g)
  have hB : ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K)).map
          ((modelsRightQ P).map w) ≫
        ((derivedBifunctorOfRightFac F P hP hW).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L', hL'⟩).app
            (DerivedCategory.Q.obj K) =
      ((derivedBifunctorOfRightFac F P hP hW).hom.app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩).app
            (DerivedCategory.Q.obj K) ≫
        ((derivedToDerivedRight F).obj (DerivedCategory.Q.obj K)).map
          ((ObjectProperty.ιOfLE hP).map w) :=
    NatTrans.congr_app ((derivedBifunctorOfRightFac F P hP hW).hom.naturality w)
      (DerivedCategory.Q.obj K)
  have hC : ((derivedToDerivedRight F).obj (DerivedCategory.Q.obj K)).map
          ((ObjectProperty.ιOfLE hP).map w) ≫
        ((derivedToDerivedRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L', hP _ hL'⟩ =
      ((derivedToDerivedRightFac F).hom.app K).app
          ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hP _ hL⟩ ≫
        (DerivedCategory.Qh (C := D)).map
          (((homotopyBifunctor F).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).map
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map g)) :=
    ((derivedToDerivedRightFac F).hom.app K).naturality ((ObjectProperty.ιOfLE hP).map w)
  exact paste_four_squares hA hB hC (totalComplexQhIso_naturality_right F K g)

/-- **`comparisonOfRight` is natural in both complexes at once**, the right-hand map being the
total complex of the pair of morphisms. -/
theorem comparisonOfRight_naturality
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hL : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L))
    (hL' : P ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L')) :
    ((derivedBifunctorOfRight F P hP hW).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctorOfRight F P hP hW).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        (comparisonOfRight F P hP hW K' L' hL').hom =
      (comparisonOfRight F P hP hW K L hL).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ)) := by
  rw [comparisonOfRight_naturality_right F P hP hW K' g hL hL', ← Category.assoc,
    comparisonOfRight_naturality_left F P hP hW f L hL, Category.assoc, ← Functor.map_comp]
  exact congrArg _ (congrArg DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap_eq_map₂_comp F _ f g))

end CochainComplex.KFlatBifunctor

end
