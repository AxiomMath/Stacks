module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The unit of a monoidal functor is determined by its tensor structure

Let `F : C ⥤ D` be a functor between monoidal categories with a natural isomorphism
`δ : F (X ⊗ Y) ⟶ F X ⊗ F Y` satisfying the associativity axiom of an oplax monoidal functor, and
suppose `F 𝟙` is isomorphic to `𝟙`. Then there is a counit `F 𝟙 ⟶ 𝟙`, invertible, for which both
unit laws hold: `F` is an oplax monoidal functor with cotensorator `δ`, hence a strong monoidal
functor (Etingof–Gelaki–Nikshych–Ostrik, *Tensor categories*, Definition 2.4.1 and the remark
after it). The counit is the one that makes the left unit law hold at `𝟙`; associativity at
`(𝟙, 𝟙, X)` and at `(X, 𝟙, 𝟙)` propagates both unit laws to every `X`.

## Main definitions

* `CategoryTheory.OplaxOfAssoc.counit`: the counit `F 𝟙 ⟶ 𝟙`.
* `CategoryTheory.OplaxOfAssoc.oplaxMonoidal`: the oplax monoidal structure with cotensorator `δ`.

## Main results

* `CategoryTheory.OplaxOfAssoc.left_unitality`, `CategoryTheory.OplaxOfAssoc.right_unitality`.
* `CategoryTheory.OplaxOfAssoc.isIso_counit`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.OplaxOfAssoc

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]


/-- For `u ≅ 𝟙`, the morphism `A ⟶ B` whose right whiskering by `u` is a given `A ⊗ u ⟶ B ⊗ u`. -/
def preimageWhiskerRight {u : D} (φ : u ≅ 𝟙_ D) {A B : D} (g : A ⊗ u ⟶ B ⊗ u) : A ⟶ B :=
  (ρ_ A).inv ≫ A ◁ φ.inv ≫ g ≫ B ◁ φ.hom ≫ (ρ_ B).hom

/-- `preimageWhiskerRight` is a preimage under `- ▷ u`. -/
theorem preimageWhiskerRight_whiskerRight {u : D} (φ : u ≅ 𝟙_ D) {A B : D}
    (g : A ⊗ u ⟶ B ⊗ u) : preimageWhiskerRight φ g ▷ u = g := by
  rw [← cancel_mono (B ◁ φ.hom ≫ (ρ_ B).hom)]
  simp only [preimageWhiskerRight]
  rw [← whisker_exchange_assoc, whiskerRight_id_assoc]
  simp

/-- `preimageWhiskerRight` recovers `a` from its right whiskering `a ▷ u`. -/
private theorem preimageWhiskerRight_whiskerRight_eq {u : D} (φ : u ≅ 𝟙_ D) {A B : D}
    (a : A ⟶ B) : preimageWhiskerRight φ (a ▷ u) = a := by
  simp only [preimageWhiskerRight]
  rw [← whisker_exchange_assoc, whiskerRight_id_assoc]
  simp

/-- Right whiskering by an object isomorphic to the unit is injective. -/
theorem whiskerRight_injective {u : D} (φ : u ≅ 𝟙_ D) {A B : D} {a b : A ⟶ B}
    (h : a ▷ u = b ▷ u) : a = b := by
  rw [← preimageWhiskerRight_whiskerRight_eq φ a, ← preimageWhiskerRight_whiskerRight_eq φ b, h]

/-- Left whiskering by an object isomorphic to the unit is injective. -/
theorem whiskerLeft_injective {u : D} (φ : u ≅ 𝟙_ D) {A B : D} {a b : A ⟶ B}
    (h : u ◁ a = u ◁ b) : a = b := by
  have key : ∀ c : A ⟶ B, c = (λ_ A).inv ≫ φ.inv ▷ A ≫ u ◁ c ≫ φ.hom ▷ B ≫ (λ_ B).hom := by
    intro c
    rw [whisker_exchange_assoc]
    simp
  rw [key a, key b, h]

variable (F : C ⥤ D) (δ : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y) [∀ X Y, IsIso (δ X Y)]
  (natL : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
    δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X')
  (natR : ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
    δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y)
  (assoc : ∀ X Y Z : C,
    δ (X ⊗ Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ F.obj X ◁ δ Y Z)
  (φ : F.obj (𝟙_ C) ≅ 𝟙_ D)

/-- The comultiplication `F 𝟙 ⟶ F 𝟙 ⊗ F 𝟙`. -/
def comul : F.obj (𝟙_ C) ⟶ F.obj (𝟙_ C) ⊗ F.obj (𝟙_ C) :=
  F.map (λ_ (𝟙_ C)).inv ≫ δ (𝟙_ C) (𝟙_ C)

/-- The comultiplication `comul F δ` is an isomorphism. -/
instance : IsIso (comul F δ) := by
  unfold comul
  infer_instance

/-- The left unit comparison `F X ⟶ F 𝟙 ⊗ F X`. -/
def leftCmp (X : C) : F.obj X ⟶ F.obj (𝟙_ C) ⊗ F.obj X := F.map (λ_ X).inv ≫ δ (𝟙_ C) X

/-- The left unit comparison `leftCmp F δ X` is an isomorphism. -/
instance (X : C) : IsIso (leftCmp F δ X) := by
  unfold leftCmp
  infer_instance

/-- The right unit comparison `F X ⟶ F X ⊗ F 𝟙`. -/
def rightCmp (X : C) : F.obj X ⟶ F.obj X ⊗ F.obj (𝟙_ C) := F.map (ρ_ X).inv ≫ δ X (𝟙_ C)

/-- The right unit comparison `rightCmp F δ X` is an isomorphism. -/
instance (X : C) : IsIso (rightCmp F δ X) := by
  unfold rightCmp
  infer_instance

include natL natR assoc in
/-- Coassociativity of the left unit comparison, from associativity at `(𝟙, 𝟙, X)`. -/
theorem whiskerLeft_leftCmp (X : C) :
    F.obj (𝟙_ C) ◁ leftCmp F δ X =
      comul F δ ▷ F.obj X ≫ (α_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) (F.obj X)).hom := by
  rw [← cancel_epi (leftCmp F δ X)]
  have coh : (λ_ X).inv ≫ 𝟙_ C ◁ (λ_ X).inv =
      (λ_ X).inv ≫ (λ_ (𝟙_ C)).inv ▷ X ≫ (α_ (𝟙_ C) (𝟙_ C) X).hom := by monoidal
  calc leftCmp F δ X ≫ F.obj (𝟙_ C) ◁ leftCmp F δ X
      = F.map (λ_ X).inv ≫ (δ (𝟙_ C) X ≫ F.obj (𝟙_ C) ◁ F.map (λ_ X).inv) ≫
          F.obj (𝟙_ C) ◁ δ (𝟙_ C) X := by
        simp only [leftCmp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = F.map ((λ_ X).inv ≫ 𝟙_ C ◁ (λ_ X).inv) ≫ δ (𝟙_ C) (𝟙_ C ⊗ X) ≫
          F.obj (𝟙_ C) ◁ δ (𝟙_ C) X := by
        rw [natR]
        simp only [Functor.map_comp, Category.assoc]
    _ = F.map ((λ_ X).inv ≫ (λ_ (𝟙_ C)).inv ▷ X) ≫ (F.map (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
          δ (𝟙_ C) (𝟙_ C ⊗ X) ≫ F.obj (𝟙_ C) ◁ δ (𝟙_ C) X) := by
        rw [coh]
        simp only [Functor.map_comp, Category.assoc]
    _ = F.map (λ_ X).inv ≫ (F.map ((λ_ (𝟙_ C)).inv ▷ X) ≫ δ (𝟙_ C ⊗ 𝟙_ C) X) ≫
          δ (𝟙_ C) (𝟙_ C) ▷ F.obj X ≫ (α_ _ _ _).hom := by
        rw [← assoc]
        simp only [Functor.map_comp, Category.assoc]
    _ = leftCmp F δ X ≫ comul F δ ▷ F.obj X ≫ (α_ _ _ _).hom := by
        rw [← natL]
        simp only [leftCmp, comul, comp_whiskerRight, Category.assoc]

include natR in
/-- Coassociativity of the right unit comparison, from associativity at `(X, 𝟙, 𝟙)`. -/
theorem rightCmp_whiskerRight (X : C)
    (natL : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X')
    (assoc : ∀ X Y Z : C,
      δ (X ⊗ Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ F.obj X ◁ δ Y Z) :
    rightCmp F δ X ▷ F.obj (𝟙_ C) =
      F.obj X ◁ comul F δ ≫ (α_ (F.obj X) (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).inv := by
  rw [← cancel_epi (rightCmp F δ X),
    ← cancel_mono (α_ (F.obj X) (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).hom]
  have coh : (ρ_ X).inv ≫ (ρ_ X).inv ▷ 𝟙_ C ≫ (α_ X (𝟙_ C) (𝟙_ C)).hom =
      (ρ_ X).inv ≫ X ◁ (λ_ (𝟙_ C)).inv := by monoidal
  simp only [Category.assoc]
  calc rightCmp F δ X ≫ rightCmp F δ X ▷ F.obj (𝟙_ C) ≫ (α_ _ _ _).hom
      = F.map (ρ_ X).inv ≫ (δ X (𝟙_ C) ≫ F.map (ρ_ X).inv ▷ F.obj (𝟙_ C)) ≫
          δ X (𝟙_ C) ▷ F.obj (𝟙_ C) ≫ (α_ _ _ _).hom := by
        simp only [rightCmp, comp_whiskerRight, Category.assoc]
    _ = F.map ((ρ_ X).inv ≫ (ρ_ X).inv ▷ 𝟙_ C) ≫ (δ (X ⊗ 𝟙_ C) (𝟙_ C) ≫
          δ X (𝟙_ C) ▷ F.obj (𝟙_ C) ≫ (α_ _ _ _).hom) := by
        rw [natL]
        simp only [Functor.map_comp, Category.assoc]
    _ = F.map ((ρ_ X).inv ≫ (ρ_ X).inv ▷ 𝟙_ C ≫ (α_ X (𝟙_ C) (𝟙_ C)).hom) ≫
          δ X (𝟙_ C ⊗ 𝟙_ C) ≫ F.obj X ◁ δ (𝟙_ C) (𝟙_ C) := by
        rw [assoc]
        simp only [Functor.map_comp, Category.assoc]
    _ = F.map (ρ_ X).inv ≫ (F.map (X ◁ (λ_ (𝟙_ C)).inv) ≫ δ X (𝟙_ C ⊗ 𝟙_ C)) ≫
          F.obj X ◁ δ (𝟙_ C) (𝟙_ C) := by
        rw [coh]
        simp only [Functor.map_comp, Category.assoc]
    _ = rightCmp F δ X ≫ F.obj X ◁ comul F δ ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom := by
        rw [← natR]
        simp [rightCmp, comul, MonoidalCategory.whiskerLeft_comp]

/-- The counit `F 𝟙 ⟶ 𝟙`. -/
def counit : F.obj (𝟙_ C) ⟶ 𝟙_ D := preimageWhiskerRight φ (inv (comul F δ) ≫ (λ_ _).inv)

/-- The counit is a left counit of `comul`. -/
theorem comul_counit_whiskerRight :
    comul F δ ≫ counit F δ φ ▷ F.obj (𝟙_ C) = (λ_ (F.obj (𝟙_ C))).inv := by
  rw [counit, preimageWhiskerRight_whiskerRight, IsIso.hom_inv_id_assoc]

include natL natR assoc in
/-- The counit is also a right counit of `comul`. -/
theorem comul_counit_whiskerLeft :
    comul F δ ≫ F.obj (𝟙_ C) ◁ counit F δ φ = (ρ_ (F.obj (𝟙_ C))).inv := by
  have hco : F.obj (𝟙_ C) ◁ comul F δ =
      comul F δ ▷ F.obj (𝟙_ C) ≫ (α_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).hom :=
    whiskerLeft_leftCmp F δ natL natR assoc (𝟙_ C)
  apply whiskerRight_injective φ
  rw [← cancel_epi (comul F δ), ← cancel_mono (α_ (F.obj (𝟙_ C)) (𝟙_ D) (F.obj (𝟙_ C))).hom]
  have h1 : comul F δ ≫ (comul F δ ≫ F.obj (𝟙_ C) ◁ counit F δ φ) ▷ F.obj (𝟙_ C) ≫
      (α_ _ _ _).hom = comul F δ ≫ F.obj (𝟙_ C) ◁ (λ_ (F.obj (𝟙_ C))).inv := by
    rw [comp_whiskerRight, Category.assoc, associator_naturality_middle, ← Category.assoc
      (comul F δ ▷ _), ← hco, ← MonoidalCategory.whiskerLeft_comp, comul_counit_whiskerRight]
  have h2 : (ρ_ (F.obj (𝟙_ C))).inv ▷ F.obj (𝟙_ C) ≫ (α_ _ _ _).hom =
      F.obj (𝟙_ C) ◁ (λ_ (F.obj (𝟙_ C))).inv := by monoidal
  simp only [Category.assoc]
  rw [h1, h2]

include natL natR assoc in
/-- The left unit law. -/
theorem left_unitality (X : C) :
    (λ_ (F.obj X)).inv = F.map (λ_ X).inv ≫ δ (𝟙_ C) X ≫ counit F δ φ ▷ F.obj X := by
  apply whiskerLeft_injective φ
  have e1 : F.map (λ_ X).inv ≫ δ (𝟙_ C) X ≫ counit F δ φ ▷ F.obj X =
      leftCmp F δ X ≫ counit F δ φ ▷ F.obj X := by simp [leftCmp]
  have h2 : (ρ_ (F.obj (𝟙_ C))).inv ▷ F.obj X ≫ (α_ _ _ _).hom =
      F.obj (𝟙_ C) ◁ (λ_ (F.obj X)).inv := by monoidal
  rw [e1, MonoidalCategory.whiskerLeft_comp, whiskerLeft_leftCmp F δ natL natR assoc X,
    Category.assoc, ← associator_naturality_middle, ← Category.assoc, ← comp_whiskerRight,
    comul_counit_whiskerLeft F δ natL natR assoc φ, h2]

include natL natR assoc in
/-- The right unit law. -/
theorem right_unitality (X : C) :
    (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ counit F δ φ := by
  apply whiskerRight_injective φ
  have e1 : F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ counit F δ φ =
      rightCmp F δ X ≫ F.obj X ◁ counit F δ φ := by simp [rightCmp]
  have h2 : F.obj X ◁ (λ_ (F.obj (𝟙_ C))).inv ≫ (α_ _ _ _).inv =
      (ρ_ (F.obj X)).inv ▷ F.obj (𝟙_ C) := by monoidal
  rw [e1, comp_whiskerRight, rightCmp_whiskerRight F δ natR X natL assoc,
    Category.assoc, ← associator_inv_naturality_middle, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, comul_counit_whiskerRight, h2]

/-- The counit is invertible. -/
theorem isIso_counit : IsIso (counit F δ φ) := by
  have h : IsIso (counit F δ φ ▷ F.obj (𝟙_ C)) := by
    have : counit F δ φ ▷ F.obj (𝟙_ C) = inv (comul F δ) ≫ (λ_ _).inv := by
      rw [← comul_counit_whiskerRight F δ φ, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  rw [← preimageWhiskerRight_whiskerRight_eq φ (counit F δ φ)]
  unfold preimageWhiskerRight
  infer_instance

/-- **An associative `δ` with `F 𝟙 ≅ 𝟙` is oplax monoidal**: the counit is the one making the
left unit law hold at `𝟙`, and both unit laws then hold everywhere. -/
@[instance_reducible]
def oplaxMonoidal : F.OplaxMonoidal where
  η := counit F δ φ
  δ := δ
  δ_natural_left := natL
  δ_natural_right := natR
  oplax_associativity := assoc
  oplax_left_unitality := left_unitality F δ natL natR assoc φ
  oplax_right_unitality := right_unitality F δ natL natR assoc φ

/-- The cotensorator of `oplaxMonoidal` is `δ`. -/
theorem oplaxMonoidal_δ (X Y : C) :
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F (oplaxMonoidal F δ natL natR assoc φ) X Y = δ X Y :=
  rfl

/-- The cotensorator of the strong monoidal structure of an oplax monoidal functor with invertible
structure maps is the given one. -/
theorem δ_ofOplaxMonoidal (G : C ⥤ D) [G.OplaxMonoidal] [IsIso (Functor.OplaxMonoidal.η G)]
    [∀ X Y, IsIso (Functor.OplaxMonoidal.δ G X Y)] (X Y : C) :
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G
      (Functor.Monoidal.ofOplaxMonoidal G).toOplaxMonoidal X Y = Functor.OplaxMonoidal.δ G X Y :=
  rfl

end CategoryTheory.OplaxOfAssoc


end
