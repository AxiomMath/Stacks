module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute

/-!
# The category of right fractions (Stacks 04VH)

Let `C` be a category and let `W` be a right multiplicative system of morphisms of `C`.
The right-fractions construction of `W⁻¹C` has the objects of `C` as its objects, and as
morphisms `X ⟶ Y` the equivalence classes of *right fractions* `X ⟵s X' ⟶f Y` with
`s ∈ W`, two fractions being equivalent when they agree after pulling both back along a
pair of morphisms whose common composite with the denominators again lies in `W`. That
relation is Mathlib's `MorphismProperty.RightFractionRel`, and that it is an equivalence
relation — part (1) of the lemma — is Mathlib's `equivalenceRightFractionRel`.

Parts (2) and (3) are what this file proves. Composition of right fractions is only
defined after a choice of *right Ore square*: to compose `φ : X ⟵ X' ⟶ Y` with
`ψ : Y ⟵ Y' ⟶ Z` one first completes the cospan `X' ⟶ Y ⟵ Y'` to a square, which the
right Ore condition makes possible, and then composes along it. Part (2) says the result
is independent of the choice and descends to equivalence classes; part (3) says the
resulting composition on classes, with the classes of `(𝟙 X, 𝟙 X)` as identities, satisfies
the category axioms. Both are proved here for the canonical (choice-of-Ore-square)
composition `RightFraction.comp`, with `RightFraction.comp_rel_compOfOre` comparing it to
an arbitrary Ore square.

The resulting category is `RightLocalization W`, a copy of `C` carrying the localized category
structure. It is the explicit presentation of `W⁻¹C` that Stacks 04VH is about. The functor
`C ⥤ RightLocalization W`, `f ↦ (f, 𝟙)`, and its universal property (Stacks 04VK) are in
`StacksFrontier.CategoryTheory.Localization.RightFraction.UniversalProperty`. Stacks 04VL uses the
op-dual model `(LeftFraction.Localization W.op)ᵒᵖ` instead — see `rightFractionQ` in
`StacksFrontier.CategoryTheory.Localization.Comparison`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-! ### Part (1)

That the relation on right fractions is an equivalence relation is Mathlib's
`MorphismProperty.equivalenceRightFractionRel`, so the tag is attached there.
-/

add_to_stacks 04VH "(1)" CategoryTheory.MorphismProperty.equivalenceRightFractionRel

/-- The hom-set of the right-fractions model of `W⁻¹C`: the quotient of
`W.RightFraction X Y` by `MorphismProperty.RightFractionRel`. -/
@[sga "5 V 2.3.3" "Hom sets of E_S"]
def RightLocalization.Hom (X Y : C) : Type max u v :=
  Quot (RightFractionRel (W := W) (X := X) (Y := Y))

/-- The class of a right fraction in `RightLocalization.Hom W X Y`. -/
def RightLocalization.Hom.mk {X Y : C} (φ : W.RightFraction X Y) :
    RightLocalization.Hom W X Y :=
  Quot.mk _ φ

/-- Two right fractions have the same class exactly when they are equivalent. -/
theorem RightLocalization.Hom.mk_eq_mk_iff [W.HasRightCalculusOfFractions] {X Y : C}
    (φ φ' : W.RightFraction X Y) :
    RightLocalization.Hom.mk W φ = RightLocalization.Hom.mk W φ' ↔ RightFractionRel φ φ' :=
  (equivalenceRightFractionRel (W := W) X Y).quot_mk_eq_iff φ φ'

/-- The identity morphism on `X` in `W⁻¹C` is the class of the right fraction
`(𝟙 X, 𝟙 X)`. -/
def RightLocalization.Hom.id [W.ContainsIdentities] (X : C) : RightLocalization.Hom W X X :=
  RightLocalization.Hom.mk W (RightFraction.mk (𝟙 X) (W.id_mem X) (𝟙 X))

/-- Composition of right fractions along a given right Ore square.
Given `φ : X ⟵ X' ⟶ Y` and `ψ : Y ⟵ Y' ⟶ Z` together with `u : X'' ⟶ φ.X'` in `W` and
`h : X'' ⟶ ψ.X'`, the composite right fraction is `(u ≫ φ.s, h ≫ ψ.f)`. Commutativity
`u ≫ φ.f = h ≫ ψ.s` is not required to form it; it is what makes the result *the* composite,
see `RightFraction.homMk_op_compOfOre`. -/
def RightFraction.compOfOre [W.IsStableUnderComposition] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) {X'' : C} (u : X'' ⟶ φ.X')
    (h : X'' ⟶ ψ.X') (hu : W u) : W.RightFraction X Z :=
  RightFraction.mk (u ≫ φ.s) (W.comp_mem _ _ hu φ.hs) (h ≫ ψ.f)

/-- A choice of right Ore square for the cospan `φ.X' ⟶ Y ⟵ ψ.X'`, given by the right
calculus of fractions applied to `φ.f` and `ψ.s`. This is Mathlib's
`MorphismProperty.LeftFraction.rightFraction` for the left fraction `(φ.f, ψ.s)`. -/
noncomputable def RightFraction.oreSquare [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) : W.RightFraction φ.X' ψ.X' :=
  (LeftFraction.mk φ.f ψ.s ψ.hs).rightFraction

/-- The defining property of the chosen Ore square: `RightFraction.oreSquare W φ ψ` does complete
the cospan `φ.X' ⟶ Y ⟵ ψ.X'` to a commuting square, `s ≫ φ.f = f ≫ ψ.s`. This is the hypothesis
`RightFraction.compOfOre` needs, so it is what makes `RightFraction.comp` a legitimate
composition. -/
lemma RightFraction.oreSquare_fac [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) :
    (RightFraction.oreSquare W φ ψ).s ≫ φ.f = (RightFraction.oreSquare W φ ψ).f ≫ ψ.s :=
  LeftFraction.rightFraction_fac _

/-- Composition of right fractions, using the canonical choice of Ore square. -/
@[sga "4 VI 6.5"]
noncomputable def RightFraction.comp [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) : W.RightFraction X Z :=
  RightFraction.compOfOre W φ ψ
    (RightFraction.oreSquare W φ ψ).s (RightFraction.oreSquare W φ ψ).f
    (RightFraction.oreSquare W φ ψ).hs

/-! ### The opposite left-fraction localization

Passing to `Cᵒᵖ` turns a right fraction into a left fraction (`MorphismProperty.RightFraction.op`)
and `W` into a morphism property `W.op` with a *left* calculus of fractions, for which Mathlib
already builds the localized category `MorphismProperty.LeftFraction.Localization W.op`. The three
lemmas below identify `RightFraction.comp` with composition there, and `RightFractionRel` with
equality of classes. Every remaining statement of parts (2) and (3) then follows from the
corresponding structure on `LeftFraction.Localization W.op`.
-/

/-- Two right fractions are equivalent exactly when their opposites have the same class in
`MorphismProperty.LeftFraction.Localization W.op`. -/
lemma RightFraction.homMk_op_eq_iff_rightFractionRel [W.HasRightCalculusOfFractions] {X Y : C}
    (φ φ' : W.RightFraction X Y) :
    LeftFraction.Localization.homMk φ.op = LeftFraction.Localization.homMk φ'.op ↔
      RightFractionRel φ φ' :=
  (LeftFraction.Localization.homMk_eq_iff_leftFractionRel _ _).trans
    (leftFractionRel_op_iff φ φ')

/-- Composition of right fractions along an Ore square is composition in the opposite
left-fraction localization: the class of `RightFraction.compOfOre W φ ψ u h hu` is the composite
of the classes of `ψ.op` and `φ.op`. Since the right-hand side does not mention the Ore square,
this is simultaneously the independence of the choice of square and the well-definedness of
composition on equivalence classes. -/
@[sga "4 VI 6.5"]
lemma RightFraction.homMk_op_compOfOre [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) {X'' : C} (u : X'' ⟶ φ.X')
    (h : X'' ⟶ ψ.X') (hu : W u) (ho : u ≫ φ.f = h ≫ ψ.s) :
    LeftFraction.Localization.homMk (RightFraction.compOfOre W φ ψ u h hu).op =
      LeftFraction.Localization.homMk ψ.op ≫ LeftFraction.Localization.homMk φ.op :=
  (LeftFraction.Localization.homMk_comp_homMk ψ.op φ.op
    (LeftFraction.mk h.op u.op hu) (Quiver.Hom.unop_inj ho)).symm

/-- `RightFraction.homMk_op_compOfOre` for the canonical choice of Ore square. -/
lemma RightFraction.homMk_op_comp [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) :
    LeftFraction.Localization.homMk (RightFraction.comp W φ ψ).op =
      LeftFraction.Localization.homMk ψ.op ≫ LeftFraction.Localization.homMk φ.op :=
  RightFraction.homMk_op_compOfOre W φ ψ _ _ _ (RightFraction.oreSquare_fac W φ ψ)

/-- The class of the identity right fraction `(𝟙 X, 𝟙 X)` is the identity of
`MorphismProperty.LeftFraction.Localization W.op`. -/
lemma RightFraction.homMk_op_id [W.HasRightCalculusOfFractions] (X : C) :
    LeftFraction.Localization.homMk (RightFraction.mk (𝟙 X) (W.id_mem X) (𝟙 X)).op =
      𝟙 ((LeftFraction.Localization.Q W.op).obj (Opposite.op X)) :=
  rfl

/-- Any Ore-square composition is equivalent to the canonical one: given any `u ∈ W` and
`h` with `u ≫ φ.f = h ≫ ψ.s`, the representative `RightFraction.compOfOre` produces is
related to `RightFraction.comp`. -/
@[sga "4 VI 6.5" "c)"]
lemma RightFraction.comp_rel_compOfOre [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) {X'' : C} (u : X'' ⟶ φ.X')
    (h : X'' ⟶ ψ.X') (hu : W u) (ho : u ≫ φ.f = h ≫ ψ.s) :
    RightFractionRel (RightFraction.comp W φ ψ) (RightFraction.compOfOre W φ ψ u h hu) := by
  rw [← RightFraction.homMk_op_eq_iff_rightFractionRel W _ _,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_compOfOre W φ ψ u h hu ho]

/-- **Stacks 04VH (2)**.
The canonical composition of representatives respects the equivalence relation
in both arguments. Combined with `RightFraction.comp_rel_compOfOre`, which identifies it
with the composition along an arbitrary Ore square, this is well-definedness of
composition on the quotient. -/
@[stacks 04VH "(2)", sga "4 VI 6.5" "6.5 c)"]
theorem RightFraction.comp_rel_comp [W.HasRightCalculusOfFractions] {X Y Z : C}
    {φ φ' : W.RightFraction X Y} {ψ ψ' : W.RightFraction Y Z} (hφ : RightFractionRel φ φ')
    (hψ : RightFractionRel ψ ψ') :
    RightFractionRel (RightFraction.comp W φ ψ) (RightFraction.comp W φ' ψ') := by
  rw [← RightFraction.homMk_op_eq_iff_rightFractionRel W _ _,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_comp,
    (RightFraction.homMk_op_eq_iff_rightFractionRel W φ φ').2 hφ,
    (RightFraction.homMk_op_eq_iff_rightFractionRel W ψ ψ').2 hψ]

/-- Composition of classes of right fractions, induced by `RightFraction.comp`. -/
noncomputable def RightLocalization.Hom.comp [W.HasRightCalculusOfFractions] {X Y Z : C}
    (f : RightLocalization.Hom W X Y) (g : RightLocalization.Hom W Y Z) :
    RightLocalization.Hom W X Z :=
  Quot.liftOn₂ f g
    (fun φ ψ => RightLocalization.Hom.mk W (RightFraction.comp W φ ψ))
    (fun φ _ψ _ψ' hψ => Quot.sound <|
      RightFraction.comp_rel_comp W (RightFractionRel.refl φ) hψ)
    (fun _φ _φ' ψ hφ => Quot.sound <|
      RightFraction.comp_rel_comp W hφ (RightFractionRel.refl ψ))

/-- Composition of classes is computed by composing representatives. -/
@[simp]
theorem RightLocalization.Hom.comp_mk_mk [W.HasRightCalculusOfFractions] {X Y Z : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) :
    RightLocalization.Hom.comp W (RightLocalization.Hom.mk W φ)
        (RightLocalization.Hom.mk W ψ) =
      RightLocalization.Hom.mk W (RightFraction.comp W φ ψ) :=
  rfl

private lemma RightFraction.id_comp_rel [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) :
    RightFractionRel (RightFraction.comp W (RightFraction.mk (𝟙 X) (W.id_mem X) (𝟙 X)) φ) φ := by
  rw [← RightFraction.homMk_op_eq_iff_rightFractionRel W _ _,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_id, Category.comp_id]

private lemma RightFraction.comp_id_rel [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) :
    RightFractionRel (RightFraction.comp W φ (RightFraction.mk (𝟙 Y) (W.id_mem Y) (𝟙 Y))) φ := by
  rw [← RightFraction.homMk_op_eq_iff_rightFractionRel W _ _,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_id, Category.id_comp]

/-- The `id_comp` axiom of `RightLocalization.category`: composing the identity class of
`(𝟙 X, 𝟙 X)` with a class of right fractions returns that class. -/
theorem RightLocalization.Hom.id_comp [W.HasRightCalculusOfFractions] {X Y : C}
    (f : RightLocalization.Hom W X Y) :
    RightLocalization.Hom.comp W (RightLocalization.Hom.id W X) f = f := by
  induction f using Quot.ind with
  | _ φ => exact Quot.sound (RightFraction.id_comp_rel W φ)

/-- The `comp_id` axiom of `RightLocalization.category`: composing a class of right fractions with
the identity class of `(𝟙 Y, 𝟙 Y)` returns that class. -/
theorem RightLocalization.Hom.comp_id [W.HasRightCalculusOfFractions] {X Y : C}
    (f : RightLocalization.Hom W X Y) :
    RightLocalization.Hom.comp W f (RightLocalization.Hom.id W Y) = f := by
  induction f using Quot.ind with
  | _ φ => exact Quot.sound (RightFraction.comp_id_rel W φ)

private lemma RightFraction.comp_assoc_rel [W.HasRightCalculusOfFractions] {X Y Z T : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) (χ : W.RightFraction Z T) :
    RightFractionRel (RightFraction.comp W (RightFraction.comp W φ ψ) χ)
      (RightFraction.comp W φ (RightFraction.comp W ψ χ)) := by
  rw [← RightFraction.homMk_op_eq_iff_rightFractionRel W _ _,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_comp,
    RightFraction.homMk_op_comp, RightFraction.homMk_op_comp, Category.assoc]

/-- The `assoc` axiom of `RightLocalization.category`: composition of classes of right fractions is
associative. The two bracketings use different Ore squares; `RightFraction.comp_assoc_rel`
identifies both with composition in `MorphismProperty.LeftFraction.Localization W.op`, where
associativity is already available. -/
theorem RightLocalization.Hom.assoc [W.HasRightCalculusOfFractions] {X Y Z T : C}
    (f : RightLocalization.Hom W X Y) (g : RightLocalization.Hom W Y Z)
    (h : RightLocalization.Hom W Z T) :
    RightLocalization.Hom.comp W (RightLocalization.Hom.comp W f g) h =
      RightLocalization.Hom.comp W f (RightLocalization.Hom.comp W g h) := by
  induction f using Quot.ind with
  | _ φ =>
    induction g using Quot.ind with
    | _ ψ =>
      induction h using Quot.ind with
      | _ χ => exact Quot.sound (RightFraction.comp_assoc_rel W φ ψ χ)

/-- The carrier type of the right-fractions model `W⁻¹C` of the localization: the same as
`C` as a type, but distinguished so that the localized category structure can be installed
as an instance. -/
def RightLocalization (_ : MorphismProperty C) : Type u := C

/-- The type-tag wrapper from `C` to `RightLocalization W`. -/
def RightLocalization.of (W : MorphismProperty C) (X : C) : RightLocalization W := X

/-- The underlying object of a localized object. -/
def RightLocalization.out {W : MorphismProperty C} (X : RightLocalization W) : C := X

/-- **Stacks 04VH (3)**.
The objects of the right-fractions model `W⁻¹C` are the objects of `C`, the hom-sets are
`RightLocalization.Hom W X Y`, identities are `RightLocalization.Hom.id W X`, and
composition is `RightLocalization.Hom.comp W`. The category axioms are
`RightLocalization.Hom.id_comp`, `.comp_id` and `.assoc`. -/
@[stacks 04VH "(3)", sga "4 VI 6.5"]
noncomputable instance RightLocalization.category [W.HasRightCalculusOfFractions] :
    Category (RightLocalization W) where
  Hom X Y := RightLocalization.Hom W (RightLocalization.out X) (RightLocalization.out Y)
  id X := RightLocalization.Hom.id W (RightLocalization.out X)
  comp f g := RightLocalization.Hom.comp W f g
  id_comp f := RightLocalization.Hom.id_comp W f
  comp_id f := RightLocalization.Hom.comp_id W f
  assoc f g h := RightLocalization.Hom.assoc W f g h

end CategoryTheory.MorphismProperty
