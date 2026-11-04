module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Glueing a family of schemes along a common open subscheme

Let `W` be a scheme and let `gᵢ : W ⟶ Xᵢ` be a family of open immersions. The schemes `Xᵢ` glue
along `W` to a single scheme in which every `Xᵢ` is an open subscheme, all the charts agree on
`W`, and the charts cover the glued scheme (as soon as the family is nonempty). A family of
morphisms `Xᵢ ⟶ T` restricting to one and the same morphism on `W` descends to the glued scheme.

The glued scheme is the colimit of the wide span `W ⟶ Xᵢ`, a diagram of open immersions of the
locally directed shape `CategoryTheory.Limits.WidePushoutShape`, which Mathlib provides through
`AlgebraicGeometry.Scheme.IsLocallyDirected`; no cocycle condition has to be checked because every
transition passes through `W`. This generalises the two-member glueing
`AlgebraicGeometry.SpanGlue` to an arbitrary index type.

## Main definitions

* `AlgebraicGeometry.WideSpanGlue.glued`: the glued scheme.
* `AlgebraicGeometry.WideSpanGlue.ι`: the charts, which are open immersions.
* `AlgebraicGeometry.WideSpanGlue.desc`: the morphism out of the glued scheme determined by a
  compatible family of morphisms out of the pieces.

## Main results

* `AlgebraicGeometry.WideSpanGlue.glue_condition`: any two charts agree on `W`.
* `AlgebraicGeometry.WideSpanGlue.ι_jointly_surjective`: the charts cover the glued scheme.
* `AlgebraicGeometry.WideSpanGlue.ι_desc`: the descended morphism restricts to the given ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.WideSpanGlue

variable {J : Type u} {W : Scheme.{u}} (X : J → Scheme.{u}) (g : ∀ i, W ⟶ X i)
  [∀ i, IsOpenImmersion (g i)]

/-- The wide span `W ⟶ Xᵢ`, as a diagram of shape `WidePushoutShape J`. -/
def diagram : WidePushoutShape J ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan W X g

/-- Every morphism of the wide span `W ⟶ Xᵢ` is an open immersion. -/
instance isOpenImmersion_diagram_map :
    ∀ {i j : WidePushoutShape J} (f : i ⟶ j), IsOpenImmersion ((diagram X g).map f) := by
  intro i j f
  cases f with
  | id => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init i => dsimp [diagram]; infer_instance

/-- The scheme obtained by glueing the `Xᵢ` along the common open subscheme `W`. -/
def glued : Scheme.{u} := colimit (diagram X g)

/-- The `i`-th chart of the glueing. -/
def ι (i : J) : X i ⟶ glued X g := colimit.ι (diagram X g) (some i)

/-- Every chart `Xᵢ ⟶ glued X g` is an open immersion. -/
instance isOpenImmersion_ι (i : J) : IsOpenImmersion (ι X g i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram X g) (some i)))

/-- The chart of the common open subscheme factors through every chart. -/
theorem ι_none_eq (i : J) : colimit.ι (diagram X g) none = g i ≫ ι X g i :=
  (colimit.w (diagram X g) (WidePushoutShape.Hom.init i)).symm

/-- **The glueing condition.** Any two charts agree on the common open subscheme. -/
@[reassoc]
theorem glue_condition (i j : J) : g i ≫ ι X g i = g j ≫ ι X g j :=
  (ι_none_eq X g i).symm.trans (ι_none_eq X g j)

/-- **The charts cover the glued scheme**, as soon as there is at least one chart. -/
theorem ι_jointly_surjective [Nonempty J] (x : glued X g) : ∃ (i : J) (y : X i), ι X g i y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram X g) x
  match i with
  | none =>
    obtain ⟨i₀⟩ := ‹Nonempty J›
    refine ⟨i₀, g i₀ y, ?_⟩
    rw [← hy, ι_none_eq X g i₀]
    rfl
  | some i => exact ⟨i, y, hy⟩

section Desc

variable {T : Scheme.{u}} (q : ∀ i, X i ⟶ T) (q₀ : W ⟶ T) (hq : ∀ i, g i ≫ q i = q₀)

/-- The cocone on the wide span given by a family of morphisms restricting to `q₀` on `W`. -/
def cocone : Cocone (diagram X g) where
  pt := T
  ι :=
    { app := fun i => match i with
        | none => q₀
        | some i => q i
      naturality := by
        intro i j f
        cases f with
        | id => simp
        | init i => simpa [diagram] using hq i }

/-- The morphism out of the glued scheme determined by a family of morphisms out of the pieces
agreeing on the common open subscheme. -/
def desc : glued X g ⟶ T := colimit.desc _ (cocone X g q q₀ hq)

/-- The descended morphism restricts on every chart to the given morphism. -/
@[reassoc (attr := simp)]
theorem ι_desc (i : J) : ι X g i ≫ desc X g q q₀ hq = q i :=
  colimit.ι_desc (cocone X g q q₀ hq) (some i)

end Desc

end AlgebraicGeometry.WideSpanGlue

end
