module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Glueing a family of schemes along a common open subscheme

A family of schemes `Y i`, indexed by a type `J`, each containing a copy of a fixed scheme `W` as
an open subscheme through an open immersion `j i : W ⟶ Y i`, glues to a single scheme: the
colimit of the star-shaped diagram `W ⟶ Y i`. The charts `Y i` are open immersions into the glued
scheme, they agree on `W`, they cover it as soon as `J` is nonempty, and two different charts meet
exactly in `W`. A family of morphisms `Y i ⟶ T` agreeing on `W` descends to the glued scheme, and
any property of morphisms that is local on the source and holds for each of them holds for the
descended morphism.

## Main definitions

* `AlgebraicGeometry.StarGlue.diagram`: the star-shaped diagram, of shape `WidePushoutShape J`.
* `AlgebraicGeometry.StarGlue.glued`: the glued scheme, the colimit of the diagram.
* `AlgebraicGeometry.StarGlue.ι`: the charts.
* `AlgebraicGeometry.StarGlue.desc`: the morphism out of the glued scheme determined by a family
  of morphisms agreeing on `W`.

## Main results

* `AlgebraicGeometry.StarGlue.glue_condition`: the charts agree on `W`.
* `AlgebraicGeometry.StarGlue.ι_jointly_surjective`: the charts cover the glued scheme.
* `AlgebraicGeometry.StarGlue.exists_eq_of_ι_eq_ι`: two different charts meet exactly in `W`.
* `AlgebraicGeometry.StarGlue.ι_desc`: the descended morphism restricts to the given ones.
* `AlgebraicGeometry.StarGlue.desc_mem`: a property local on the source holds for the descended
  morphism as soon as it holds for the given ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.StarGlue

variable {J : Type} {W : Scheme.{u}} (Y : J → Scheme.{u}) (j : ∀ i, W ⟶ Y i)
  [∀ i, IsOpenImmersion (j i)]

/-- The star-shaped diagram `W ⟶ Y i`, of shape `WidePushoutShape J`. -/
def diagram : WidePushoutShape J ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan W Y j

/-- Every morphism of the star-shaped diagram is an open immersion. -/
instance isOpenImmersion_diagram_map :
    ∀ {a b : WidePushoutShape J} (f : a ⟶ b), IsOpenImmersion ((diagram Y j).map f) := by
  intro a b f
  cases f with
  | id => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init i => exact inferInstanceAs (IsOpenImmersion (j i))

/-- The scheme obtained by glueing the `Y i` along the common open subscheme `W`. -/
def glued : Scheme.{u} := colimit (diagram Y j)

/-- The `i`-th chart of the glueing. -/
def ι (i : J) : Y i ⟶ glued Y j := colimit.ι (diagram Y j) (some i)

/-- Each chart of the glueing is an open immersion. -/
instance isOpenImmersion_ι (i : J) : IsOpenImmersion (ι Y j i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram Y j) (some i)))

/-- The cover of the glued scheme by the diagram. -/
def openCover : (glued Y j).OpenCover :=
  Scheme.IsLocallyDirected.openCover (diagram Y j)

/-- The morphisms of `openCover` are the colimit inclusions of the diagram. -/
theorem openCover_f (a : WidePushoutShape J) :
    (openCover Y j).f a = colimit.ι (diagram Y j) a := rfl

/-- The schemes of `openCover` are the objects of the diagram. -/
theorem openCover_X (a : WidePushoutShape J) :
    (openCover Y j).X a = (diagram Y j).obj a := rfl

/-- The chart of `W` factors through every chart. -/
theorem ι_none_eq (i : J) : colimit.ι (diagram Y j) none = j i ≫ ι Y j i :=
  (colimit.w (diagram Y j) (WidePushoutShape.Hom.init i)).symm

/-- The charts agree on the common open subscheme `W`. -/
@[reassoc]
theorem glue_condition (i i' : J) : j i ≫ ι Y j i = j i' ≫ ι Y j i' :=
  (ι_none_eq Y j i).symm.trans (ι_none_eq Y j i')

/-- **The charts cover the glued scheme**, as soon as there is at least one. -/
theorem ι_jointly_surjective [Nonempty J] (x : glued Y j) : ∃ (i : J) (y : Y i), ι Y j i y = x := by
  obtain ⟨a, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram Y j) x
  match a with
  | none =>
    obtain ⟨i⟩ := ‹Nonempty J›
    let y' : W := y
    refine ⟨i, j i y', ?_⟩
    rw [← hy]
    exact (congrArg (fun φ : W ⟶ glued Y j => φ y') (ι_none_eq Y j i)).symm
  | some i => exact ⟨i, y, hy⟩

/-- **Two different charts meet exactly in `W`.** -/
theorem exists_eq_of_ι_eq_ι {i i' : J} (hii' : i ≠ i') {a : Y i} {b : Y i'}
    (h : ι Y j i a = ι Y j i' b) : ∃ w : W, j i w = a ∧ j i' w = b := by
  obtain ⟨k, fi, fj, w, hw₁, hw₂⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram Y j)).mp h
  cases k with
  | none =>
    cases fi
    cases fj
    exact ⟨w, hw₁, hw₂⟩
  | some k =>
    cases fi
    cases fj
    exact absurd rfl hii'

/-- **A morphism out of the glued scheme is determined by its restrictions to the charts.** -/
theorem hom_ext [Nonempty J] {T : Scheme.{u}} {a b : glued Y j ⟶ T}
    (h : ∀ i, ι Y j i ≫ a = ι Y j i ≫ b) : a = b := by
  refine colimit.hom_ext fun x => ?_
  match x with
  | none =>
    obtain ⟨i⟩ := ‹Nonempty J›
    change colimit.ι (diagram Y j) none ≫ a = colimit.ι (diagram Y j) none ≫ b
    rw [ι_none_eq Y j i]
    exact (Category.assoc _ _ _).trans
      ((congrArg (j i ≫ ·) (h i)).trans (Category.assoc _ _ _).symm)
  | some i => exact h i

section Desc

variable {T : Scheme.{u}} (g : ∀ i, Y i ⟶ T) (g₀ : W ⟶ T) (hg : ∀ i, j i ≫ g i = g₀)

/-- The cocone on the star given by a family of morphisms agreeing on the common open. -/
def cocone : Cocone (diagram Y j) where
  pt := T
  ι :=
    { app := fun a => match a with
        | none => g₀
        | some i => g i
      naturality := by
        intro a b f
        cases f with
        | id => simp
        | init i => simpa [diagram] using hg i }

/-- The morphism out of the glued scheme determined by a family of morphisms agreeing on the
common open subscheme. -/
def desc : glued Y j ⟶ T := colimit.desc _ (cocone Y j g g₀ hg)

/-- The descended morphism restricts to `g i` on the `i`-th chart. -/
@[reassoc (attr := simp)]
theorem ι_desc (i : J) : ι Y j i ≫ desc Y j g g₀ hg = g i :=
  colimit.ι_desc (cocone Y j g g₀ hg) (some i)

/-- **A property local on the source holds for the descended morphism** as soon as it holds for
each of the given morphisms and for their common restriction to `W`. -/
theorem desc_mem (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (hP : ∀ i, P (g i)) (hP₀ : P g₀) : P (desc Y j g g₀ hg) := by
  have key : ∀ a : WidePushoutShape J, P (colimit.ι (diagram Y j) a ≫ desc Y j g g₀ hg) := by
    intro a
    have e : colimit.ι (diagram Y j) a ≫ desc Y j g g₀ hg = (cocone Y j g g₀ hg).ι.app a :=
      colimit.ι_desc (cocone Y j g g₀ hg) a
    rw [e]
    match a with
    | none => exact hP₀
    | some i => exact hP i
  exact IsZariskiLocalAtSource.of_openCover (openCover Y j) fun a => key a

end Desc

end AlgebraicGeometry.StarGlue
