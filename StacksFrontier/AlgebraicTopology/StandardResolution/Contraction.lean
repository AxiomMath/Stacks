module

public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement
public import StacksFrontier.AlgebraicTopology.ExtraDegeneracyLast

/-!
# Contracting Godement's standard resolution at a section of the augmentation

Let `Y : C ⥤ C` be an endofunctor, let `d : Y ⟶ 𝟭 C` be a transformation of functors and let `B`
be an object of `C` whose component `d_B : Y B ⟶ B` admits a section `θ : B ⟶ Y B`, that is
`θ ≫ d_B = 𝟙 B`. The morphisms `s n = Yⁿ⁺¹ θ : Yⁿ⁺¹ B ⟶ Yⁿ⁺² B` then contract Godement's standard
resolution `n ↦ Yⁿ⁺¹ B` of `B`: they insert a new *innermost* copy of `Y`, and Godement's faces
count the copies of `Y` from the outside, so it is the *last* face which cancels `s n`, while the
remaining faces commute past it by naturality of `d`. That is an `ExtraDegeneracyLast`, the mirror
image of Mathlib's `ExtraDegeneracy`.

Nothing beyond the naturality of `d` and the single identity `θ ≫ d_B = 𝟙 B` is used: no
comultiplication on `Y`, hence no comonad structure, and no coalgebra structure on `B`. In
particular the contraction exists for *any* section `θ` of `d_B`, and not only for the section
`θ = U η_E` carried by a free object `B = U E` of an adjunction `U ⊣ V` with `Y = U ∘ V`.

## Main definitions

* `CategoryTheory.Godement.contraction`: the contraction `s n = Yⁿ⁺¹ θ`, given by the recursion
  `s 0 = Y θ` and `s (n + 1) = Y (s n)`.
* `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast.ofGodement`: that contraction as
  an `ExtraDegeneracyLast` of any augmented simplicial object pinned to Godement's model at `B` —
  its terms the iterates `Yⁿ⁺¹ B`, its faces Godement's faces, its augmentation `d_B`.

## Main results

* `CategoryTheory.Godement.contraction_comp_face`: every face but the last commutes past the
  contraction; this is the naturality of `d`.
* `CategoryTheory.Godement.contraction_comp_face_last`: the last face cancels the contraction;
  this is `Yⁿ⁺¹` applied to `θ ≫ d_B = 𝟙 B`.

## References

* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory.Godement

variable {C : Type u} [Category.{v} C] {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) {B : C}

/-- The contraction of Godement's standard resolution `n ↦ Yⁿ⁺¹ B` attached to a section `θ` of
the augmentation `d_B : Y B ⟶ B`: the morphism `s n = Yⁿ⁺¹ θ`, which inserts a new innermost copy
of `Y`. It is given by the recursion `s 0 = Y θ` and `s (n + 1) = Y (s n)`. -/
public noncomputable def contraction (θ : B ⟶ Y.obj B) :
    (n : ℕ) → (Y.iterate (n + 1)).obj B ⟶ (Y.iterate (n + 2)).obj B
  | 0 => Y.map θ
  | n + 1 => Y.map (contraction θ n)

variable (θ : B ⟶ Y.obj B)

/-- The contraction in degree `0`. -/
public theorem contraction_zero : contraction θ 0 = Y.map θ := rfl

/-- The contraction in degree `n + 1` is the contraction in degree `n` whiskered by `Y`. -/
public theorem contraction_succ (n : ℕ) :
    contraction θ (n + 1) = Y.map (contraction θ n) := rfl

/-- `Y` applied to an identity of composites. -/
private theorem map_comp_congr {P Q R S : C} {f : P ⟶ Q} {g : Q ⟶ R} {f' : P ⟶ S} {g' : S ⟶ R}
    (h : f ≫ g = f' ≫ g') :
    Y.map f ≫ Y.map g = Y.map f' ≫ Y.map g' := by
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- `Y` applied to a splitting. -/
private theorem map_comp_congr_id {P Q : C} {f : P ⟶ Q} {g : Q ⟶ P} (h : f ≫ g = 𝟙 P) :
    Y.map f ≫ Y.map g = 𝟙 (Y.obj P) := by
  rw [← Functor.map_comp, h, Functor.map_id]

/-- The zeroth face is the outermost component of `d`, so it carries `s 0` to the composite
`d_B ≫ θ`: this is the naturality of `d` at `θ`. -/
public theorem contraction_zero_comp_face_zero :
    contraction θ 0 ≫ (face d 1 0).app B = d.app B ≫ θ :=
  d.naturality θ

/-- The zeroth face commutes past the contraction: this is again the naturality of `d`. -/
public theorem contraction_comp_face_zero (n : ℕ) :
    contraction θ (n + 1) ≫ (face d (n + 2) 0).app B =
      (face d (n + 1) 0).app B ≫ contraction θ n := by
  rw [Prep.face_zero, Prep.face_zero]
  exact d.naturality (contraction θ n)

/-- Every face but the last commutes past the contraction. -/
public theorem contraction_comp_face (n : ℕ) (i : Fin (n + 2)) :
    contraction θ (n + 1) ≫ (face d (n + 2) i.castSucc).app B =
      (face d (n + 1) i).app B ≫ contraction θ n := by
  induction n with
  | zero =>
      refine Fin.cases (contraction_comp_face_zero d θ 0) (fun j => ?_) i
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact map_comp_congr (contraction_zero_comp_face_zero d θ)
  | succ n ih =>
      exact Fin.cases (contraction_comp_face_zero d θ (n + 1))
        (fun j => map_comp_congr (ih j)) i

variable (hθ : θ ≫ d.app B = 𝟙 B)

include hθ

/-- The last face cancels the contraction: `Yⁿ⁺¹(θ ≫ d_B) = Yⁿ⁺¹ 𝟙`. -/
public theorem contraction_comp_face_last (n : ℕ) :
    contraction θ n ≫ (face d (n + 1) (Fin.last (n + 1))).app B = 𝟙 _ := by
  induction n with
  | zero => exact map_comp_congr_id hθ
  | succ n ih => exact map_comp_congr_id ih

end CategoryTheory.Godement

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast

/-- **Godement's standard resolution of an object whose augmentation admits a section is
contractible.** Any augmented simplicial object of `C` pinned to Godement's model at `B` — its
terms the iterates `Yⁿ⁺¹ B`, its faces Godement's faces, its augmentation the component `d_B` —
carries an extra degeneracy at the last face, namely `s n = Yⁿ⁺¹ θ`. -/
public noncomputable def ofGodement {C : Type u} [Category.{v} C] {Y : C ⥤ C} (d : Y ⟶ 𝟭 C)
    {B : C} (θ : B ⟶ Y.obj B) (hθ : θ ≫ d.app B = 𝟙 B)
    (X : SimplicialObject.Augmented C)
    (h : ∀ n : ℕ, X.left.obj (op ⦋n⦌) = (Y.iterate (n + 1)).obj B)
    (hX : X.right = B)
    (hδ : ∀ (n : ℕ) (j : Fin (n + 2)), X.left.δ j =
      eqToHom (h (n + 1)) ≫ (Godement.face d (n + 1) j).app B ≫ eqToHom (h n).symm)
    (hε : X.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ d.app B ≫ eqToHom hX.symm) :
    SimplicialObject.Augmented.ExtraDegeneracyLast X where
  s' := eqToHom hX ≫ θ ≫ eqToHom (h 0).symm
  s n := eqToHom (h n) ≫ Godement.contraction θ n ≫ eqToHom (h (n + 1)).symm
  s'_comp_ε := by
    rw [hε]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc θ, hθ, Category.id_comp, eqToHom_trans, eqToHom_refl]
  s₀_comp_δ₀ := by
    rw [hδ 0 0, hε]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (Godement.contraction θ 0),
      Godement.contraction_zero_comp_face_zero d θ, Category.assoc]
  s_comp_δ_last n := by
    rw [hδ n (Fin.last (n + 1))]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (Godement.contraction θ n),
      Godement.contraction_comp_face_last d θ hθ n, Category.id_comp, eqToHom_trans,
      eqToHom_refl]
  s_comp_δ n i := by
    rw [hδ (n + 1) i.castSucc, hδ n i]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (Godement.contraction θ (n + 1)),
      Godement.contraction_comp_face d θ n i, Category.assoc]

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracyLast

end
