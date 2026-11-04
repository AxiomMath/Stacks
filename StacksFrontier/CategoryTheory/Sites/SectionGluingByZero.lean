module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Gluing a section against zero along a two-member cover

Let `F` be a sheaf with values in a preadditive category on a site `(C, J)`, and let
`i : A ⟶ V` and `j : D ⟶ V` be two monomorphisms which together cover `V`. A section of `F`
on `A` which restricts to zero on every object mapping into both `A` and `D` extends uniquely to
a section on `V` which restricts to the given one along `i` and to zero along `j`.

If the empty family covers `V`, then every morphism into `F(V)` is zero.

## Main definitions

* `CategoryTheory.Presheaf.glueSectionByZero` — the extension of a section on `A` by zero on
  `D`.

## Main results

* `CategoryTheory.Presheaf.glueSectionByZero_compat` — the two prescribed restrictions are a
  compatible family as soon as the section vanishes on the overlap.
* `CategoryTheory.Presheaf.glueSectionByZero_graph` and
  `CategoryTheory.Presheaf.glueSectionByZero_compl` — the extension restricts to the given
  section along `i` and to zero along `j`.
* `CategoryTheory.Presheaf.glueSectionByZero_unique` — a section on `V` is determined by its
  restrictions along `i` and `j`.
* `CategoryTheory.Presheaf.eq_zero_of_isEmptyCover` — every section over an object covered by
  the empty family vanishes.

## References

* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]

/-- The two prescribed restrictions `a` along `i` and `0` along `j` form a compatible family
for the cover `{i, j}`, provided `a` restricts to zero on every object mapping into both `A`
and `D` over `V`. -/
public theorem glueSectionByZero_compat [Preadditive A] {E : A} {V P D : C}
    (F : Cᵒᵖ ⥤ A) (i : P ⟶ V) (j : D ⟶ V) [Mono i] [Mono j]
    (a : E ⟶ F.obj (Opposite.op P))
    (hzero : ∀ ⦃S : C⦄ (f : S ⟶ P) (g : S ⟶ D),
      f ≫ i = g ≫ j → a ≫ F.map (Opposite.op f) = 0) :
    ∀ ⦃S : C⦄ ⦃b c : WalkingPair⦄
      (p : S ⟶ pairFunction P D b) (q : S ⟶ pairFunction P D c),
      p ≫ WalkingPair.casesOn b i j = q ≫ WalkingPair.casesOn c i j →
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          b a 0) ≫ F.map (Opposite.op p) =
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          c a 0) ≫ F.map (Opposite.op q) := by
  rintro S (_ | _) (_ | _) p q hpq
  · obtain rfl := (cancel_mono i).1 (by simpa using hpq)
    simp
  · exact (hzero p q (by simpa using hpq)).trans zero_comp.symm
  · exact zero_comp.trans (hzero q p (by simpa using hpq.symm)).symm
  · obtain rfl := (cancel_mono j).1 (by simpa using hpq)
    simp

/-- The section on `V` obtained by amalgamating a section `a` on `P` with the zero section on
`D`, for a cover of `V` by the two monomorphisms `i : P ⟶ V` and `j : D ⟶ V`. -/
public noncomputable def glueSectionByZero [Preadditive A] {E : A} {V P D : C}
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf J F)
    (i : P ⟶ V) (j : D ⟶ V) [Mono i] [Mono j]
    (hcover : Sieve.ofTwoArrows i j ∈ J V)
    (a : E ⟶ F.obj (Opposite.op P))
    (hcompat : ∀ ⦃S : C⦄ ⦃b c : WalkingPair⦄
      (p : S ⟶ pairFunction P D b) (q : S ⟶ pairFunction P D c),
      p ≫ WalkingPair.casesOn b i j = q ≫ WalkingPair.casesOn c i j →
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          b a 0) ≫ F.map (Opposite.op p) =
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          c a 0) ≫ F.map (Opposite.op q)) :
    E ⟶ F.obj (Opposite.op V) :=
  hF.amalgamateOfArrows (fun b : WalkingPair => WalkingPair.casesOn b i j)
    hcover (fun b => WalkingPair.casesOn
      (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k))) b a 0) hcompat

/-- The glued section restricts to the prescribed section along `i`. -/
public theorem glueSectionByZero_graph [Preadditive A] {E : A} {V P D : C}
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf J F)
    (i : P ⟶ V) (j : D ⟶ V) [Mono i] [Mono j]
    (hcover : Sieve.ofTwoArrows i j ∈ J V)
    (a : E ⟶ F.obj (Opposite.op P))
    (hcompat : ∀ ⦃S : C⦄ ⦃b c : WalkingPair⦄
      (p : S ⟶ pairFunction P D b) (q : S ⟶ pairFunction P D c),
      p ≫ WalkingPair.casesOn b i j = q ≫ WalkingPair.casesOn c i j →
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          b a 0) ≫ F.map (Opposite.op p) =
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          c a 0) ≫ F.map (Opposite.op q)) :
    glueSectionByZero J F hF i j hcover a hcompat ≫ F.map (Opposite.op i) = a :=
  hF.amalgamateOfArrows_map _ _ _ _ WalkingPair.left

/-- The glued section restricts to zero along `j`. -/
public theorem glueSectionByZero_compl [Preadditive A] {E : A} {V P D : C}
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf J F)
    (i : P ⟶ V) (j : D ⟶ V) [Mono i] [Mono j]
    (hcover : Sieve.ofTwoArrows i j ∈ J V)
    (a : E ⟶ F.obj (Opposite.op P))
    (hcompat : ∀ ⦃S : C⦄ ⦃b c : WalkingPair⦄
      (p : S ⟶ pairFunction P D b) (q : S ⟶ pairFunction P D c),
      p ≫ WalkingPair.casesOn b i j = q ≫ WalkingPair.casesOn c i j →
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          b a 0) ≫ F.map (Opposite.op p) =
        (WalkingPair.casesOn (motive := fun k => E ⟶ F.obj (Opposite.op (pairFunction P D k)))
          c a 0) ≫ F.map (Opposite.op q)) :
    glueSectionByZero J F hF i j hcover a hcompat ≫ F.map j.op = 0 :=
  hF.amalgamateOfArrows_map _ _ _ _ WalkingPair.right

/-- A section over `V` is determined by its restrictions along the two members of a cover of
`V`. -/
public theorem glueSectionByZero_unique {E : A} {V P D : C}
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf J F)
    (i : P ⟶ V) (j : D ⟶ V) (hcover : Sieve.ofTwoArrows i j ∈ J V)
    {x y : E ⟶ F.obj (Opposite.op V)}
    (hi : x ≫ F.map i.op = y ≫ F.map i.op)
    (hj : x ≫ F.map j.op = y ≫ F.map j.op) :
    x = y :=
  hF.hom_ext_ofArrows (X := pairFunction P D) (fun b => WalkingPair.casesOn b i j) hcover
    fun b => by cases b <;> assumption

/-- If the empty family covers `V`, then every morphism into the sections of a sheaf over `V`
is zero. -/
public theorem eq_zero_of_isEmptyCover [Preadditive A] {F : Cᵒᵖ ⥤ A} {V : C} {E : A}
    (J : GrothendieckTopology C) (hF : Presheaf.IsSheaf J F)
    (hcover : Sieve.ofArrows (fun e : PEmpty => e.elim)
      (fun e : PEmpty => e.elim) ∈ J V)
    (f : E ⟶ F.obj (Opposite.op V)) : f = 0 :=
  hF.hom_ext_ofArrows (X := fun e : PEmpty => e.elim) (fun e => e.elim) hcover fun e => e.elim

end CategoryTheory.Presheaf

end
