module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# A monoidal functor from an associative tensorator and an invertible unit object

Let `F : C ⥤ D` be a functor between monoidal categories carrying a natural isomorphism
`μ : F X ⊗ F Y ≅ F (X ⊗ Y)` which satisfies the associativity law of a monoidal functor, and
suppose that `F (𝟙_ C)` is isomorphic to `𝟙_ D` by *some* isomorphism. Then `F` is a monoidal
functor with tensorator `μ`: there is a unit comparison `ε : 𝟙_ D ≅ F (𝟙_ C)` for which both
unitality laws hold, and they follow from associativity alone.

This is Saavedra Rivano's observation that units in a monoidal category are determined by the
tensor product and the associativity constraint. The unit `ε` is pinned by the left unitality
law at `𝟙_ C`: as `F (𝟙_ C) ≅ 𝟙_ D`, whiskering on the right by `F (𝟙_ C)` is fully faithful, so
there is exactly one `ε` with `ε ▷ F (𝟙_ C) ≫ μ ≫ F λ = λ`. The associativity law at
`(𝟙, 𝟙, X)` makes `μ ≫ F λ : F 𝟙 ⊗ F X ⟶ F X` an action of the multiplication of `F 𝟙`, from
which left unitality at every `X` follows; at `(X, 𝟙, 𝟙)` it gives right unitality in the same
way, once right unitality at `𝟙` is deduced from left unitality at `𝟙`.

## Main definitions

* `CategoryTheory.Functor.CoreMonoidal.ofAssociativeTensorator`: the monoidal structure on `F`
  with tensorator `μ`.

## Main results

* `CategoryTheory.Functor.CoreMonoidal.ofAssociativeTensorator_μIso`: its tensorator is `μ`.

## References

* N. Saavedra Rivano, *Catégories Tannakiennes*, Lecture Notes in Math. 265, I.1.3.3.1.
* J. Kock, *Elementary remarks on units in monoidal categories*, Math. Proc. Cambridge Philos.
  Soc. 144 (2008).
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor.CoreMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} (μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
  (hnatl : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
    F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X'))
  (hnatr : ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
    F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f))
  (hassoc : ∀ X Y Z : C,
    (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
        (μIso X (Y ⊗ Z)).hom)
  (u : 𝟙_ D ≅ F.obj (𝟙_ C))

/-- Whiskering on the right by `F (𝟙_ C)` is fully faithful, `F (𝟙_ C)` being isomorphic to the
unit. -/
def tensorRightFullyFaithfulOfIsoUnit : (tensorRight (F.obj (𝟙_ C))).FullyFaithful :=
  (FullyFaithful.id D).ofIso ((rightUnitorNatIso D).symm ≪≫ (tensoringRight D).mapIso u)

/-- The multiplication `F 𝟙 ⊗ F 𝟙 ≅ F (𝟙 ⊗ 𝟙) ≅ F 𝟙` of the unit object. -/
def unitMulIso : F.obj (𝟙_ C) ⊗ F.obj (𝟙_ C) ≅ F.obj (𝟙_ C) :=
  μIso (𝟙_ C) (𝟙_ C) ≪≫ F.mapIso (λ_ (𝟙_ C))

/-- The left action `F 𝟙 ⊗ F X ≅ F (𝟙 ⊗ X) ≅ F X`. -/
def leftActIso (X : C) : F.obj (𝟙_ C) ⊗ F.obj X ≅ F.obj X :=
  μIso (𝟙_ C) X ≪≫ F.mapIso (λ_ X)

/-- The right action `F X ⊗ F 𝟙 ≅ F (X ⊗ 𝟙) ≅ F X`. -/
def rightActIso (X : C) : F.obj X ⊗ F.obj (𝟙_ C) ≅ F.obj X :=
  μIso X (𝟙_ C) ≪≫ F.mapIso (ρ_ X)

/-- **The unit comparison**: the unique `ε : 𝟙_ D ≅ F (𝟙_ C)` with
`ε ▷ F 𝟙 ≫ μ ≫ F λ = λ`. -/
def unitIsoOfAssociativeTensorator : 𝟙_ D ≅ F.obj (𝟙_ C) :=
  (tensorRightFullyFaithfulOfIsoUnit u).preimageIso
    ((λ_ (F.obj (𝟙_ C))) ≪≫ (unitMulIso μIso).symm)

include hnatl hnatr hassoc

/-- The unit comparison satisfies the left unitality law at `𝟙_ C`. -/
theorem unitIsoOfAssociativeTensorator_whiskerRight_comp :
    (unitIsoOfAssociativeTensorator μIso u).hom ▷ F.obj (𝟙_ C) ≫ (unitMulIso μIso).hom =
      (λ_ (F.obj (𝟙_ C))).hom := by
  have h : (unitIsoOfAssociativeTensorator μIso u).hom ▷ F.obj (𝟙_ C) =
      (λ_ (F.obj (𝟙_ C))).hom ≫ (unitMulIso μIso).inv :=
    (tensorRightFullyFaithfulOfIsoUnit u).map_preimage _
  rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The associativity law at `(𝟙, 𝟙, X)`**: the left action of `F 𝟙` on `F X` is compatible
with the multiplication of `F 𝟙`. -/
theorem whiskerLeft_leftActIso_comp (X : C) :
    F.obj (𝟙_ C) ◁ (leftActIso μIso X).hom ≫ (leftActIso μIso X).hom =
      (α_ (F.obj (𝟙_ C)) (F.obj (𝟙_ C)) (F.obj X)).inv ≫
        (unitMulIso μIso).hom ▷ F.obj X ≫ (leftActIso μIso X).hom := by
  have hC : 𝟙_ C ◁ (λ_ X).hom = (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ (λ_ (𝟙_ C)).hom ▷ X := by
    monoidal
  have ha := hassoc (𝟙_ C) (𝟙_ C) X
  rw [← Iso.inv_comp_eq] at ha
  simp only [leftActIso, unitMulIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, comp_whiskerRight]
  rw [reassoc_of% (hnatr (𝟙_ C) (λ_ X).hom), hC, ← reassoc_of% ha, ← F.map_comp_assoc,
    Iso.hom_inv_id_assoc, ← reassoc_of% (hnatl (λ_ (𝟙_ C)).hom X)]

/-- **Left unitality**, at every object. -/
theorem left_unitality_ofAssociativeTensorator (X : C) :
    (λ_ (F.obj X)).hom = (unitIsoOfAssociativeTensorator μIso u).hom ▷ F.obj X ≫
      (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by
  have key := unitIsoOfAssociativeTensorator_whiskerRight_comp μIso hnatl hnatr hassoc u
  have hact := whiskerLeft_leftActIso_comp μIso hnatl hnatr hassoc X
  set e := (unitIsoOfAssociativeTensorator μIso u).hom
  set φ := leftActIso μIso X
  set m := unitMulIso μIso
  have hφ : (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom = φ.hom := rfl
  have hD : (α_ (𝟙_ D) (F.obj (𝟙_ C)) (F.obj X)).inv ≫ (λ_ (F.obj (𝟙_ C))).hom ▷ F.obj X =
      (λ_ (F.obj (𝟙_ C) ⊗ F.obj X)).hom := by
    monoidal
  rw [hφ]
  refine (cancel_epi (𝟙_ D ◁ φ.hom)).1 ?_
  symm
  rw [whisker_exchange_assoc, hact, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, key, reassoc_of% hD, leftUnitor_naturality]

/-- Right unitality at `𝟙_ C`, from left unitality at `𝟙_ C`. -/
theorem whiskerLeft_unitIsoOfAssociativeTensorator_comp :
    F.obj (𝟙_ C) ◁ (unitIsoOfAssociativeTensorator μIso u).hom ≫ (unitMulIso μIso).hom =
      (ρ_ (F.obj (𝟙_ C))).hom := by
  have key := unitIsoOfAssociativeTensorator_whiskerRight_comp μIso hnatl hnatr hassoc u
  have hact := whiskerLeft_leftActIso_comp μIso hnatl hnatr hassoc (𝟙_ C)
  have hφ : leftActIso μIso (𝟙_ C) = unitMulIso μIso := rfl
  rw [hφ, Iso.eq_inv_comp] at hact
  set e := (unitIsoOfAssociativeTensorator μIso u).hom
  set m := unitMulIso μIso
  apply (tensorRightFullyFaithfulOfIsoUnit u).map_injective
  show _ ▷ _ = _ ▷ _
  refine (cancel_mono m.hom).1 ?_
  rw [comp_whiskerRight, Category.assoc, ← hact, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, key]
  have hD : (α_ (F.obj (𝟙_ C)) (𝟙_ D) (F.obj (𝟙_ C))).hom ≫
      F.obj (𝟙_ C) ◁ (λ_ (F.obj (𝟙_ C))).hom = (ρ_ (F.obj (𝟙_ C))).hom ▷ F.obj (𝟙_ C) := by
    monoidal
  rw [reassoc_of% hD]

/-- **The associativity law at `(X, 𝟙, 𝟙)`**: the right action of `F 𝟙` on `F X` is compatible
with the multiplication of `F 𝟙`. -/
theorem rightActIso_whiskerRight_comp (X : C) :
    (rightActIso μIso X).hom ▷ F.obj (𝟙_ C) ≫ (rightActIso μIso X).hom =
      (α_ (F.obj X) (F.obj (𝟙_ C)) (F.obj (𝟙_ C))).hom ≫
        F.obj X ◁ (unitMulIso μIso).hom ≫ (rightActIso μIso X).hom := by
  have hC : (ρ_ X).hom ▷ 𝟙_ C = (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ X ◁ (λ_ (𝟙_ C)).hom := by
    monoidal
  simp only [rightActIso, unitMulIso, Iso.trans_hom, Functor.mapIso_hom, comp_whiskerRight,
    Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [reassoc_of% (hnatl (ρ_ X).hom (𝟙_ C)), hC, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hassoc X (𝟙_ C) (𝟙_ C)), ← reassoc_of% (hnatr X (λ_ (𝟙_ C)).hom)]

/-- **Right unitality**, at every object. -/
theorem right_unitality_ofAssociativeTensorator (X : C) :
    (ρ_ (F.obj X)).hom = F.obj X ◁ (unitIsoOfAssociativeTensorator μIso u).hom ≫
      (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by
  have key := whiskerLeft_unitIsoOfAssociativeTensorator_comp μIso hnatl hnatr hassoc u
  have hact := rightActIso_whiskerRight_comp μIso hnatl hnatr hassoc X
  set e := (unitIsoOfAssociativeTensorator μIso u).hom
  set χ := rightActIso μIso X
  set m := unitMulIso μIso
  have hχ : (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom = χ.hom := rfl
  have hD : (α_ (F.obj X) (F.obj (𝟙_ C)) (𝟙_ D)).hom ≫ F.obj X ◁ (ρ_ (F.obj (𝟙_ C))).hom =
      (ρ_ (F.obj X ⊗ F.obj (𝟙_ C))).hom := by
    monoidal
  rw [hχ]
  refine (cancel_epi (χ.hom ▷ 𝟙_ D)).1 ?_
  symm
  rw [← whisker_exchange_assoc, hact, associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, key, reassoc_of% hD, rightUnitor_naturality]

/-- **A functor with an associative tensorator, whose value at the unit is isomorphic to the
unit, is monoidal** with that tensorator: the unit comparison is
`unitIsoOfAssociativeTensorator`, and both unitality laws follow from associativity. -/
def ofAssociativeTensorator : F.CoreMonoidal where
  εIso := unitIsoOfAssociativeTensorator μIso u
  μIso := μIso
  μIso_hom_natural_left := hnatl
  μIso_hom_natural_right := hnatr
  associativity := hassoc
  left_unitality := left_unitality_ofAssociativeTensorator μIso hnatl hnatr hassoc u
  right_unitality := right_unitality_ofAssociativeTensorator μIso hnatl hnatr hassoc u

/-- The tensorator of `ofAssociativeTensorator` is `μIso`. -/
@[simp]
theorem ofAssociativeTensorator_μIso (X Y : C) :
    (ofAssociativeTensorator μIso hnatl hnatr hassoc u).μIso X Y = μIso X Y := rfl

omit hnatl hnatr hassoc in
/-- The associativity law of a tensorator follows from the same law for its inverse, the shape in
which a comparison `F (X ⊗ Y) ≅ F X ⊗ F Y` is usually presented. -/
theorem associativity_of_oplax
    (hoplax : ∀ X Y Z : C,
      (μIso (X ⊗ Y) Z).inv ≫ (μIso X Y).inv ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ (μIso X (Y ⊗ Z)).inv ≫ F.obj X ◁ (μIso Y Z).inv)
    (X Y Z : C) :
    (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
        (μIso X (Y ⊗ Z)).hom := by
  rw [← cancel_epi ((μIso X Y).inv ▷ F.obj Z), ← cancel_epi (μIso (X ⊗ Y) Z).inv,
    reassoc_of% hoplax X Y Z]
  simp

end CategoryTheory.Functor.CoreMonoidal

end
