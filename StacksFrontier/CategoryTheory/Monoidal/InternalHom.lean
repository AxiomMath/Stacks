module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-! # Internal homs in a monoidal category

Stacks 0GWJ (Remark 4.43.12): a monoidal category `C` *has an internal hom* if there is a
bifunctor `hom : Cᵒᵖ ⥤ C ⥤ C` together with bijections `Mor(X, hom(Y, Z)) ≃ Mor(X ⊗ Y, Z)`
natural in `X`, `Y` and `Z`; equivalently `hom(Y, -)` is right adjoint to `- ⊗ Y`, which is the
convention opposite to Mathlib's `MonoidalClosed`.  From that data the source constructs five
canonical morphisms: evaluation `hom(X, Y) ⊗ X ⟶ Y`, composition
`hom(Y, Z) ⊗ hom(X, Y) ⟶ hom(X, Z)`, tensoring on the left `Z ⊗ hom(X, Y) ⟶ hom(X, Z ⊗ Y)`,
coevaluation `Y ⟶ hom(X, Y ⊗ X)`, and, when `C` is braided,
`hom(Y, Z) ⊗ X ⟶ hom(hom(X, Y), Z)`.  Each is characterised here by the equation the source
specifies it by, together with the uniqueness of a morphism satisfying that equation; the
associativity and unit constraints are inserted where needed to keep the composites well-typed.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Definition 1 (Internal hom).**
An internal hom on a monoidal category `C` consists of a bifunctor
`hom : Cᵒᵖ ⥤ C ⥤ C` (contravariant in the first variable, covariant in the second)
together with, for all objects `X, Y, Z`, a bijection
`Φ X Y Z : Mor(X, hom(Y, Z)) ≃ Mor(X ⊗ Y, Z)` that is natural in `X`, in `Y`, and
in `Z`.

This is the opening clause of Stacks 0GWJ: `C` *has an internal hom* if for every pair `X, Y`
there is an object `hom(X, Y)` with `Mor(X, hom(Y, Z)) = Mor(X ⊗ Y, Z)` functorially in
`X, Y, Z`. -/
@[stacks_fixed 0GWJ, sga "4 IV 10.2"]
structure InternalHom (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- The internal hom bifunctor in curried form: `hom(Y, Z) = (hom.obj (op Y)).obj Z`. -/
  hom : Cᵒᵖ ⥤ C ⥤ C
  /-- The natural bijection `Mor(X, hom(Y, Z)) ≃ Mor(X ⊗ Y, Z)`. -/
  Φ : ∀ (X Y Z : C), (X ⟶ (hom.obj (Opposite.op Y)).obj Z) ≃ (X ⊗ Y ⟶ Z)
  /-- Naturality of `Φ` in `X` (contravariant). -/
  naturality_left : ∀ {X X' Y Z : C} (g : X' ⟶ X)
      (f : X ⟶ (hom.obj (Opposite.op Y)).obj Z),
    Φ X' Y Z (g ≫ f) = (g ▷ Y) ≫ Φ X Y Z f
  /-- Naturality of `Φ` in `Z` (covariant). -/
  naturality_right : ∀ {X Y Z Z' : C} (k : Z ⟶ Z')
      (f : X ⟶ (hom.obj (Opposite.op Y)).obj Z),
    Φ X Y Z' (f ≫ (hom.obj (Opposite.op Y)).map k) = Φ X Y Z f ≫ k
  /-- Naturality of `Φ` in `Y` (contravariant). -/
  naturality_middle : ∀ {X Y Y' Z : C} (h : Y' ⟶ Y)
      (f : X ⟶ (hom.obj (Opposite.op Y)).obj Z),
    Φ X Y' Z (f ≫ (hom.map h.op).app Z) = (X ◁ h) ≫ Φ X Y Z f

namespace InternalHom

variable (ih : InternalHom C)

/-- The internal hom object `hom(Y, Z)`. -/
@[sga "3 I 1.7.3" "partial", sga "4 V 7.3.6.0"]
abbrev homObj (Y Z : C) : C := (ih.hom.obj (Opposite.op Y)).obj Z

/-- The inverse bijection ("currying") `Mor(X ⊗ Y, Z) ≃ Mor(X, hom(Y, Z))`. -/
abbrev Φinv (X Y Z : C) : (X ⊗ Y ⟶ Z) ≃ (X ⟶ ih.homObj Y Z) := (ih.Φ X Y Z).symm

-- Constructions (the five canonical morphisms, built explicitly as witnesses)

/-- **Construction of (1) Evaluation.**
`ev_{X,Y} := Φ (id_{hom(X,Y)})`, the image of the identity under `Φ`. -/
@[stacks 0GWJ "(1)", sga "7 VIII 1.6" "more general"]
def ev (X Y : C) : ih.homObj X Y ⊗ X ⟶ Y :=
  ih.Φ (ih.homObj X Y) X Y (𝟙 (ih.homObj X Y))

/-- **Construction of (2) Composition.**
`c_{X,Y,Z}` is the image under `Φ⁻¹` (using `X` as the tensoring object) of the
composite `hom(Y,Z) ⊗ hom(X,Y) ⊗ X → hom(Y,Z) ⊗ Y → Z` given by
`(id ⊗ ev_{X,Y})` followed by `ev_{Y,Z}`. -/
@[stacks 0GWJ "(2)"]
def comp (X Y Z : C) : ih.homObj Y Z ⊗ ih.homObj X Y ⟶ ih.homObj X Z :=
  ih.Φinv (ih.homObj Y Z ⊗ ih.homObj X Y) X Z
    ((α_ (ih.homObj Y Z) (ih.homObj X Y) X).hom
      ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z)

/-- **Construction of (3) Tensor on the left.**
`t_{X,Y,Z}` is the image under `Φ⁻¹` of `id_Z ⊗ ev_{X,Y} : Z ⊗ hom(X,Y) ⊗ X → Z ⊗ Y`. -/
@[stacks 0GWJ "(3)"]
def tensorLeftMor (X Y Z : C) : Z ⊗ ih.homObj X Y ⟶ ih.homObj X (Z ⊗ Y) :=
  ih.Φinv (Z ⊗ ih.homObj X Y) X (Z ⊗ Y)
    ((α_ Z (ih.homObj X Y) X).hom ≫ (Z ◁ ih.ev X Y))

/-- The auxiliary unit `u_X : 𝟙_ ⟶ hom(X, X)`, image of `λ_X` under `Φ⁻¹`. -/
def unitMor (X : C) : (𝟙_ C) ⟶ ih.homObj X X :=
  ih.Φinv (𝟙_ C) X X (λ_ X).hom

/-- **Construction of (4) Unit / coevaluation.**
`η_{X,Y} := ρ_Y⁻¹ ≫ (id_Y ⊗ u_X) ≫ t_{X,X,Y}`. -/
@[stacks 0GWJ "(4)"]
def coev (X Y : C) : Y ⟶ ih.homObj X (Y ⊗ X) :=
  (ρ_ Y).inv ≫ (Y ◁ ih.unitMor X) ≫ ih.tensorLeftMor X X Y

/-- **Construction of (5) Internalized currying (symmetric case).**
`d_{X,Y,Z}` is the image under `Φ⁻¹` (using `hom(X,Y)` as the tensoring object) of the
composite `hom(Y,Z) ⊗ X ⊗ hom(X,Y) → hom(Y,Z) ⊗ hom(X,Y) ⊗ X → hom(Y,Z) ⊗ Y → Z`,
where the first arrow uses the braiding `σ_{X, hom(X,Y)}`. -/
@[stacks 0GWJ "(5)"]
def internalCurryMor [BraidedCategory C] (X Y Z : C) :
    ih.homObj Y Z ⊗ X ⟶ ih.homObj (ih.homObj X Y) Z :=
  ih.Φinv (ih.homObj Y Z ⊗ X) (ih.homObj X Y) Z
    ((α_ (ih.homObj Y Z) X (ih.homObj X Y)).hom
      ≫ (ih.homObj Y Z ◁ (β_ X (ih.homObj X Y)).hom)
      ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z)

/-! ### The defining equations of the five canonical morphisms

The tag's content is the *construction* of the five morphisms, so the tags sit on the `def`s
above. What is recorded here is that each named morphism satisfies the defining equation the
source uses to specify it, and that it is the **only** morphism doing so — the latter is where
the bijectivity of `Φ` is used, and it is what makes the equations a characterisation rather
than a restatement of the definitions.
-/

/-- **(1) Evaluation** is characterised by `Φ⁻¹(ev_{X,Y}) = id_{hom(X,Y)}`. -/
@[simp]
theorem Φinv_ev (X Y : C) :
    ih.Φinv (ih.homObj X Y) X Y (ih.ev X Y) = 𝟙 (ih.homObj X Y) := by
  simp [ev, Φinv]

/-- `ev_{X,Y}` is the unique morphism `hom(X, Y) ⊗ X ⟶ Y` whose currying is the identity. -/
theorem eq_ev_of_Φinv_eq_id {X Y : C} (e : ih.homObj X Y ⊗ X ⟶ Y)
    (he : ih.Φinv (ih.homObj X Y) X Y e = 𝟙 (ih.homObj X Y)) : e = ih.ev X Y :=
  (ih.Φinv (ih.homObj X Y) X Y).injective (he.trans (ih.Φinv_ev X Y).symm)

/-- Two morphisms into `hom(Y, Z)` with the same image under `Φ` are equal. -/
private theorem eq_of_Φ_eq_Φ {X Y Z : C} {f g : X ⟶ ih.homObj Y Z} {h : X ⊗ Y ⟶ Z}
    (hf : ih.Φ X Y Z f = h) (hg : ih.Φ X Y Z g = h) : f = g :=
  (ih.Φ X Y Z).injective (hf.trans hg.symm)

/-- **(2) Composition** is characterised by
`Φ(c_{X,Y,Z}) = α ≫ (id ⊗ ev_{X,Y}) ≫ ev_{Y,Z}`. -/
@[simp]
theorem Φ_comp (X Y Z : C) :
    ih.Φ (ih.homObj Y Z ⊗ ih.homObj X Y) X Z (ih.comp X Y Z)
      = (α_ (ih.homObj Y Z) (ih.homObj X Y) X).hom
        ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z := by
  simp [comp, Φinv]

/-- `c_{X,Y,Z}` is the unique morphism with that image under `Φ`. -/
theorem eq_comp_of_Φ_eq {X Y Z : C} (c : ih.homObj Y Z ⊗ ih.homObj X Y ⟶ ih.homObj X Z)
    (hc : ih.Φ (ih.homObj Y Z ⊗ ih.homObj X Y) X Z c
      = (α_ (ih.homObj Y Z) (ih.homObj X Y) X).hom
        ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z) : c = ih.comp X Y Z :=
  ih.eq_of_Φ_eq_Φ hc (ih.Φ_comp X Y Z)

/-- **(3) Tensoring on the left** is characterised by
`Φ(t_{X,Y,Z}) = α ≫ (id_Z ⊗ ev_{X,Y})`. -/
@[simp]
theorem Φ_tensorLeftMor (X Y Z : C) :
    ih.Φ (Z ⊗ ih.homObj X Y) X (Z ⊗ Y) (ih.tensorLeftMor X Y Z)
      = (α_ Z (ih.homObj X Y) X).hom ≫ (Z ◁ ih.ev X Y) := by
  simp [tensorLeftMor, Φinv]

/-- `t_{X,Y,Z}` is the unique morphism with that image under `Φ`. -/
theorem eq_tensorLeftMor_of_Φ_eq {X Y Z : C} (t : Z ⊗ ih.homObj X Y ⟶ ih.homObj X (Z ⊗ Y))
    (ht : ih.Φ (Z ⊗ ih.homObj X Y) X (Z ⊗ Y) t
      = (α_ Z (ih.homObj X Y) X).hom ≫ (Z ◁ ih.ev X Y)) : t = ih.tensorLeftMor X Y Z :=
  ih.eq_of_Φ_eq_Φ ht (ih.Φ_tensorLeftMor X Y Z)

/-- The auxiliary unit `u_X` is characterised by `Φ(u_X) = λ_X`: it is the element of
`Mor(𝟙_, hom(X, X))` corresponding to the canonical isomorphism `𝟙_ ⊗ X → X`, which is
exactly how the source specifies it. -/
@[simp]
theorem Φ_unitMor (X : C) :
    ih.Φ (𝟙_ C) X X (ih.unitMor X) = (λ_ X).hom := by
  simp [unitMor, Φinv]

/-- `u_X` is the unique morphism `𝟙_ ⟶ hom(X, X)` with `Φ(u_X) = λ_X`. -/
theorem eq_unitMor_of_Φ_eq {X : C} (u : (𝟙_ C) ⟶ ih.homObj X X)
    (hu : ih.Φ (𝟙_ C) X X u = (λ_ X).hom) : u = ih.unitMor X :=
  ih.eq_of_Φ_eq_Φ hu (ih.Φ_unitMor X)

/-- **(4) Coevaluation** is built from (3) and the auxiliary unit `u_X`, exactly as in the
source: `η_{X,Y} = ρ_Y⁻¹ ≫ (id_Y ⊗ u_X) ≫ t_{X,X,Y}`. -/
theorem coev_eq (X Y : C) :
    ih.coev X Y = (ρ_ Y).inv ≫ (Y ◁ ih.unitMor X) ≫ ih.tensorLeftMor X X Y :=
  rfl

/-- **(5) Internalized currying** is characterised by its image under `Φ`: braid `X` past
`hom(X, Y)`, then evaluate twice. -/
@[simp]
theorem Φ_internalCurryMor [BraidedCategory C] (X Y Z : C) :
    ih.Φ (ih.homObj Y Z ⊗ X) (ih.homObj X Y) Z (ih.internalCurryMor X Y Z)
      = (α_ (ih.homObj Y Z) X (ih.homObj X Y)).hom
        ≫ (ih.homObj Y Z ◁ (β_ X (ih.homObj X Y)).hom)
        ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z := by
  simp [internalCurryMor, Φinv]

/-- `d_{X,Y,Z}` is the unique morphism with that image under `Φ`. -/
theorem eq_internalCurryMor_of_Φ_eq [BraidedCategory C] {X Y Z : C}
    (d : ih.homObj Y Z ⊗ X ⟶ ih.homObj (ih.homObj X Y) Z)
    (hd : ih.Φ (ih.homObj Y Z ⊗ X) (ih.homObj X Y) Z d
      = (α_ (ih.homObj Y Z) X (ih.homObj X Y)).hom
        ≫ (ih.homObj Y Z ◁ (β_ X (ih.homObj X Y)).hom)
        ≫ (ih.homObj Y Z ◁ ih.ev X Y) ≫ ih.ev Y Z) : d = ih.internalCurryMor X Y Z :=
  ih.eq_of_Φ_eq_Φ hd (ih.Φ_internalCurryMor X Y Z)

end InternalHom

end
