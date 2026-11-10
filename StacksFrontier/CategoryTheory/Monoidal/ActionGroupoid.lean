module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# The action groupoid of a group object acting on an object

Let `G` be a group object of a cartesian monoidal category with pullbacks, acting on an object
`X`. Then `X` and `G ⊗ X` are the objects and the arrows of a groupoid object: the source of
`(g, x)` is `x`, its target is `g • x`, the identity at `x` is `(1, x)`, the inverse of `(g, x)`
is `(g⁻¹, g • x)`, and composition is multiplication in `G`.

## Main definitions

* `Stacks.Groupoids.GroupoidObjectData` is a groupoid object with a prescribed object of objects
  and object of arrows.
* `Stacks.Groupoids.ActionGroupoid.composition`, `Stacks.Groupoids.ActionGroupoid.identity` and
  `Stacks.Groupoids.ActionGroupoid.inverse` are the composition, identity and inverse maps of
  the action groupoid.

## Main results

* `Stacks.Groupoids.ActionGroupoid.composition_left_identity`,
  `Stacks.Groupoids.ActionGroupoid.composition_right_identity`,
  `Stacks.Groupoids.ActionGroupoid.composition_left_inverse`,
  `Stacks.Groupoids.ActionGroupoid.composition_right_inverse` and
  `Stacks.Groupoids.ActionGroupoid.composition_assoc` are the unit, inverse and associativity
  axioms of the action groupoid, on generalized points.

## Implementation notes

The objects and the arrows are parameters of `Stacks.Groupoids.GroupoidObjectData` rather than
fields, so that a construction producing a groupoid object on a prescribed pair of objects keeps
those objects rather than replacing them by isomorphic ones. Associativity and the unit and
inverse laws are stated on generalized points, which avoids choosing a model for the object of
composable triples.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0234](https://stacks.math.columbia.edu/tag/0234)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe v u

namespace Stacks.Groupoids

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section Data

variable [HasPullbacks C]

/-- A groupoid object in `C` with object of objects `U` and object of arrows `R`.

The fields `identity` and `inverse` are included as data, although they are uniquely determined
by `source`, `target` and `comp`. -/
structure GroupoidObjectData (U R : C) where
  /-- The source of an arrow. -/
  source : R ⟶ U
  /-- The target of an arrow. -/
  target : R ⟶ U
  /-- Composition of composable arrows.  The first projection is the arrow applied last. -/
  comp : pullback source target ⟶ R
  /-- The identity arrow at an object. -/
  identity : U ⟶ R
  /-- The inverse of an arrow. -/
  inverse : R ⟶ R
  source_identity : identity ≫ source = 𝟙 U
  target_identity : identity ≫ target = 𝟙 U
  source_inverse : inverse ≫ source = target
  target_inverse : inverse ≫ target = source
  source_comp : comp ≫ source = pullback.snd source target ≫ source
  target_comp : comp ≫ target = pullback.fst source target ≫ target
  left_identity : ∀ (T : C) (f : T ⟶ R)
      (w : (f ≫ target ≫ identity) ≫ source = f ≫ target),
    pullback.lift (f ≫ target ≫ identity) f w ≫ comp = f
  right_identity : ∀ (T : C) (f : T ⟶ R)
      (w : f ≫ source = (f ≫ source ≫ identity) ≫ target),
    pullback.lift f (f ≫ source ≫ identity) w ≫ comp = f
  left_inverse : ∀ (T : C) (f : T ⟶ R)
      (w : (f ≫ inverse) ≫ source = f ≫ target),
    pullback.lift (f ≫ inverse) f w ≫ comp = f ≫ source ≫ identity
  right_inverse : ∀ (T : C) (f : T ⟶ R)
      (w : f ≫ source = (f ≫ inverse) ≫ target),
    pullback.lift f (f ≫ inverse) w ≫ comp = f ≫ target ≫ identity
  assoc : ∀ (T : C) (f g h : T ⟶ R)
      (wfg : f ≫ source = g ≫ target) (wgh : g ≫ source = h ≫ target)
      (w₁ : (pullback.lift f g wfg ≫ comp) ≫ source = h ≫ target)
      (w₂ : f ≫ source = (pullback.lift g h wgh ≫ comp) ≫ target),
    pullback.lift (pullback.lift f g wfg ≫ comp) h w₁ ≫ comp =
      pullback.lift f (pullback.lift g h wgh ≫ comp) w₂ ≫ comp

end Data

namespace ActionGroupoid

variable (G X : C) [GrpObj G]

/-- The identity map of the action groupoid: it sends `x` to `(1,x)`. -/
def identity : X ⟶ G ⊗ X :=
  lift (toUnit X ≫ η[G]) (𝟙 X)

/-- The source of the identity arrow at `x` is `x`. -/
theorem identity_source : identity G X ≫ snd G X = 𝟙 X := by
  simp [identity]

variable [ModObj G X]

/-- The inverse map of the action groupoid: it sends `(g,x)` to `(g⁻¹,g • x)`. -/
def inverse : G ⊗ X ⟶ G ⊗ X :=
  lift (fst G X ≫ ι[G]) γ[G, X]

/-- The target of the identity arrow at `x` is `x`. -/
theorem identity_target : identity G X ≫ γ[G, X] = 𝟙 X := by
  let _ : MulAction (X ⟶ G) (X ⟶ X) :=
    Hom.mulAction (C := C) (M := G) (X := X) X
  simpa [identity, Hom.smul_def, Hom.one_def] using
    (one_smul (X ⟶ G) (𝟙 X))

/-- The source of the inverse of an arrow is its target. -/
theorem inverse_source : inverse G X ≫ snd G X = γ[G, X] := by
  simp [inverse]

/-- The target of the inverse of an arrow is its source. -/
theorem inverse_target : inverse G X ≫ γ[G, X] = snd G X := by
  let _ : MulAction (G ⊗ X ⟶ G) (G ⊗ X ⟶ X) :=
    Hom.mulAction (C := C) (M := G) (X := X) (G ⊗ X)
  simpa [inverse, Hom.smul_def, Hom.inv_def] using
    (inv_smul_smul (fst G X) (snd G X))

/-- The inverse map of the action groupoid is an involution. -/
theorem inverse_comp_inverse : inverse G X ≫ inverse G X = 𝟙 (G ⊗ X) := by
  apply CartesianMonoidalCategory.hom_ext (C := C)
  · simp [inverse]
  · rw [Category.id_comp, Category.assoc, inverse_source, inverse_target]

section Composition

variable [HasPullbacks C]

/-- Composition of arrows in the action groupoid: it sends `((g,x),(g',x'))` to `(gg',x')`. -/
noncomputable def composition :
    pullback (snd G X) γ[G, X] ⟶ G ⊗ X :=
  lift
      (lift
        (pullback.fst (snd G X) γ[G, X] ≫ fst G X)
        (pullback.snd (snd G X) γ[G, X] ≫ fst G X) ≫ μ[G])
      (pullback.snd (snd G X) γ[G, X] ≫ snd G X)

/-- The first component of a composite arrow in the action groupoid is the product of the first
components of its two factors. -/
theorem composition_fst :
    composition G X ≫ fst G X =
      lift (pullback.fst (snd G X) γ[G, X] ≫ fst G X)
        (pullback.snd (snd G X) γ[G, X] ≫ fst G X) ≫ μ[G] := by
  simp [composition]

/-- The source of a composite arrow in the action groupoid is the source of its second
factor. -/
theorem composition_source :
    composition G X ≫ snd G X = pullback.snd (snd G X) γ[G, X] ≫ snd G X := by
  simp [composition]

/-- The target of a composite arrow in the action groupoid is the target of its first
factor. -/
theorem composition_target :
    composition G X ≫ γ[G, X] = pullback.fst (snd G X) γ[G, X] ≫ γ[G, X] := by
  let a := pullback.fst (snd G X) γ[G, X] ≫ fst G X
  let b := pullback.snd (snd G X) γ[G, X] ≫ fst G X
  let x := pullback.snd (snd G X) γ[G, X] ≫ snd G X
  have hb : b • x = pullback.fst (snd G X) γ[G, X] ≫ snd G X := by
    calc
      b • x = lift b x ≫ γ[G, X] := Hom.smul_def _ _ _
      _ = pullback.snd (snd G X) γ[G, X] ≫ γ[G, X] := by
        congr 1
        ext <;> simp [b, x]
      _ = pullback.fst (snd G X) γ[G, X] ≫ snd G X := pullback.condition.symm
  calc
    composition G X ≫ γ[G, X] = (a * b) • x := by
      change lift (lift a b ≫ μ[G]) x ≫ γ[G, X] = (a * b) • x
      rw [← Hom.smul_def, Hom.mul_def]
    _ = a • (b • x) := mul_smul _ _ _
    _ = a • (pullback.fst (snd G X) γ[G, X] ≫ snd G X) := by rw [hb]
    _ = pullback.fst (snd G X) γ[G, X] ≫ γ[G, X] := by
      rw [Hom.smul_def]
      congr 1
      ext <;> simp [a]

/-- Composition in the action groupoid, evaluated on a composable pair of generalized
points. -/
theorem composition_eval {T : C} (f g : T ⟶ G ⊗ X)
    (w : f ≫ snd G X = g ≫ γ[G,X]) :
    pullback.lift f g w ≫ composition G X =
      lift ((f ≫ fst G X) * (g ≫ fst G X)) (g ≫ snd G X) := by
  apply CartesianMonoidalCategory.hom_ext (C := C)
  · simp only [composition, Category.assoc, comp_lift_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Hom.mul_def]
  · simp only [composition, Category.assoc, CartesianMonoidalCategory.lift_snd,
      pullback.lift_snd_assoc]

/-- A composite of generalized points equals `h` once the products of the first components and the
sources agree. -/
private theorem composition_lift_eq {T : C} (f g h : T ⟶ G ⊗ X)
    (w : f ≫ snd G X = g ≫ γ[G,X]) (h₁ : (f ≫ fst G X) * (g ≫ fst G X) = h ≫ fst G X)
    (h₂ : g ≫ snd G X = h ≫ snd G X) : pullback.lift f g w ≫ composition G X = h := by
  rw [composition_eval G X]
  exact CartesianMonoidalCategory.hom_ext _ _ (by simpa using h₁) (by simpa using h₂)

/-- Composing an arrow with the identity arrow at its target returns the arrow. -/
theorem composition_left_identity (T : C) (f : T ⟶ G ⊗ X)
    (w : (f ≫ γ[G,X] ≫ identity G X) ≫ snd G X = f ≫ γ[G,X]) :
    pullback.lift (f ≫ γ[G, X] ≫ identity G X) f w ≫ composition G X = f :=
  composition_lift_eq G X _ _ _ w (by simp [identity, Hom.mul_def]) rfl

/-- Composing the identity arrow at the source of an arrow with that arrow returns the
arrow. -/
theorem composition_right_identity (T : C) (f : T ⟶ G ⊗ X)
    (w : f ≫ snd G X = (f ≫ snd G X ≫ identity G X) ≫ γ[G,X]) :
    pullback.lift f (f ≫ snd G X ≫ identity G X) w ≫ composition G X = f :=
  composition_lift_eq G X _ _ _ w (by simp [identity, Hom.mul_def]) (by simp [identity])

/-- Composing an arrow with its inverse returns the identity arrow at its source. -/
theorem composition_left_inverse (T : C) (f : T ⟶ G ⊗ X)
    (w : (f ≫ inverse G X) ≫ snd G X = f ≫ γ[G,X]) :
    pullback.lift (f ≫ inverse G X) f w ≫ composition G X =
      f ≫ snd G X ≫ identity G X :=
  composition_lift_eq G X _ _ _ w
    (by simpa [inverse, identity, Hom.inv_def, Hom.one_def] using inv_mul_cancel (f ≫ fst G X))
    (by simp [identity])

/-- Composing the inverse of an arrow with the arrow returns the identity arrow at its
target. -/
theorem composition_right_inverse (T : C) (f : T ⟶ G ⊗ X)
    (w : f ≫ snd G X = (f ≫ inverse G X) ≫ γ[G,X]) :
    pullback.lift f (f ≫ inverse G X) w ≫ composition G X =
      f ≫ γ[G, X] ≫ identity G X :=
  composition_lift_eq G X _ _ _ w
    (by simpa [inverse, identity, Hom.inv_def, Hom.one_def] using mul_inv_cancel (f ≫ fst G X))
    (by simp [inverse, identity])

/-- Composition in the action groupoid is associative, on composable triples of generalized
points. -/
theorem composition_assoc (T : C) (f g h : T ⟶ G ⊗ X)
    (wfg : f ≫ snd G X = g ≫ γ[G,X]) (wgh : g ≫ snd G X = h ≫ γ[G,X])
    (w₁ : (pullback.lift f g wfg ≫ composition G X) ≫ snd G X = h ≫ γ[G,X])
    (w₂ : f ≫ snd G X = (pullback.lift g h wgh ≫ composition G X) ≫ γ[G,X]) :
    pullback.lift (pullback.lift f g wfg ≫ composition G X) h w₁ ≫ composition G X =
      pullback.lift f (pullback.lift g h wgh ≫ composition G X) w₂ ≫ composition G X := by
  rw [composition_eval G X, composition_eval G X, composition_eval G X, composition_eval G X]
  apply CartesianMonoidalCategory.hom_ext (C := C) <;> simp [mul_assoc]

end Composition

end ActionGroupoid

end Stacks.Groupoids

end
