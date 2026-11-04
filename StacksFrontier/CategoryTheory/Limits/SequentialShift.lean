module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Shifting the index of a colimit cocone on a sequential diagram

Let `F : ℕ ⥤ C` and let `c` be a colimit cocone on `F`. For every `n` the cocone whose leg at
`j` is the leg of `c` at `n + j` is again colimiting: the shift `j ↦ n + j` is cofinal in `ℕ`,
so nothing is lost by starting the diagram later.

This is what identifies the stage-`n` cocone of Stacks Tag 0EXB — whose legs are the
coprojections `𝒪_X ⟶ colim_j 𝒪_X` at stage `n + j`, not at stage `j` — with a colimit cocone
of the Frobenius tower, which is the shape in which
`Stacks.NoncommChangeOfRings.Colimit.isColimitCocone` takes its diagram of rings.

## Main definitions

* `CategoryTheory.Limits.natShift`: the functor `j ↦ n + j` of `ℕ`.
* `CategoryTheory.Limits.unshiftCocone`: the cocone on `F` which descends a cocone on the
  shifted diagram.

## Main results

* `CategoryTheory.Limits.comp_map_succ_step`: one step of an induction peeling a transition off
  a morphism out of a fixed object into the diagram.
* `CategoryTheory.Limits.isColimitWhiskerNatShift`: **shifting the index of a colimit cocone on
  a sequential diagram keeps it colimiting.**

## Implementation notes

`c.whisker (natShift n)` is a cocone on `natShift n ⋙ F` whose leg at `j` is `c.ι.app (n + j)`.
Its descent of a cocone `t` is the descent along `c` of `unshiftCocone`, whose leg at `m` is the
transition `m ⟶ n + m` followed by `t.ι.app m`. Two facts make this work: `t.ι.app m` already
absorbs the transition `n + m ⟶ n + m + 1`, and `ℕ` is a preorder, so there is a single
morphism `m ⟶ n + m` and no coherence to check — every comparison of transitions below is
`Subsingleton.elim`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (F : ℕ ⥤ C)

/-- The index shift `j ↦ n + j` of `ℕ`. -/
def natShift (n : ℕ) : ℕ ⥤ ℕ :=
  Monotone.functor (f := fun j => n + j) fun _ _ h => Nat.add_le_add_left h n

/-- The shift `natShift n` sends `j` to `n + j`. -/
@[simp] lemma natShift_obj (n j : ℕ) : (natShift n).obj j = n + j := rfl

/-- **One step of an induction peeling a transition of a sequential diagram off a morphism out
of a fixed object.** Given `t : R ⟶ F.obj a` and a transition `g : a ⟶ b + 1` factoring as
`u : a ⟶ b` followed by the step `v : b ⟶ b + 1`, the composite `t ≫ F.map g` is read through
`t ≫ F.map u` and `F.map v`.

It is stated here, over a variable category, because every object in it has exactly one
spelling. At a use site `R` and `F.obj a` are typically definitionally equal and spelled
differently — `R` the fixed object, `F.obj a` the value of the diagram — and in a goal mixing
the two no rewrite fires, `Category.assoc` least of all. -/
lemma comp_map_succ_step {R : C} {a b : ℕ} (t : R ⟶ F.obj a) (u : a ⟶ b) (v : b ⟶ b + 1)
    (g : a ⟶ b + 1) (hg : g = u ≫ v) (s : R ⟶ F.obj b) (hs : t ≫ F.map u = s)
    (ψ : F.obj b ⟶ F.obj (b + 1)) (hψ : F.map v = ψ) (z : R ⟶ F.obj (b + 1))
    (hz : s ≫ ψ = z) : t ≫ F.map g = z := by
  subst hg hs hψ hz
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The leg at `m` of a cocone on the shifted diagram, with its source read as `F.obj (n + m)`.
Keeping that one spelling of the source is what lets `rw` work below: `(natShift n ⋙ F).obj m`
is the same object, but a goal mixing the two is not type-correct under the `implicit`
transparency level and every rewrite in it fails. -/
def shiftLeg (n : ℕ) (t : Cocone (natShift n ⋙ F)) (m : ℕ) : F.obj (n + m) ⟶ t.pt :=
  t.ι.app m

/-- The legs `shiftLeg F n t` are compatible with the transitions `n + m ⟶ n + m'` of `F`. -/
lemma shiftLeg_w (n : ℕ) (t : Cocone (natShift n ⋙ F)) {m m' : ℕ} (g : m ⟶ m') :
    F.map (homOfLE (Nat.add_le_add_left (leOfHom g) n)) ≫ shiftLeg F n t m' =
      shiftLeg F n t m :=
  t.w g

/-- The cocone on `F` whose leg at `m` is the transition `m ⟶ n + m` followed by the leg at `m`
of a cocone on the shifted diagram. -/
noncomputable def unshiftCocone (n : ℕ) (t : Cocone (natShift n ⋙ F)) : Cocone F where
  pt := t.pt
  ι :=
    { app := fun m => F.map (homOfLE (Nat.le_add_left m n)) ≫ shiftLeg F n t m
      naturality := fun {m m'} g => by
        have key : homOfLE (Nat.le_add_left m n) ≫
              homOfLE (Nat.add_le_add_left (leOfHom g) n) =
            g ≫ homOfLE (Nat.le_add_left m' n) := Subsingleton.elim _ _
        have main : F.map g ≫ (F.map (homOfLE (Nat.le_add_left m' n)) ≫ shiftLeg F n t m') =
            F.map (homOfLE (Nat.le_add_left m n)) ≫ shiftLeg F n t m := by
          rw [← shiftLeg_w F n t g, ← Category.assoc, ← F.map_comp, ← key, F.map_comp,
            Category.assoc]
        exact main.trans (Category.comp_id _).symm }

/-- The leg of `unshiftCocone F n t` at `n + j` is the leg `shiftLeg F n t j`. -/
lemma unshiftCocone_ι_app_add (n : ℕ) (t : Cocone (natShift n ⋙ F)) (j : ℕ) :
    (unshiftCocone F n t).ι.app (n + j) = shiftLeg F n t j := by
  have key : homOfLE (Nat.le_add_left (n + j) n) =
      homOfLE (Nat.add_le_add_left (leOfHom (homOfLE (Nat.le_add_left j n))) n) :=
    Subsingleton.elim _ _
  have main : F.map (homOfLE (Nat.le_add_left (n + j) n)) ≫ shiftLeg F n t (n + j) =
      shiftLeg F n t j := by
    rw [key, shiftLeg_w F n t (homOfLE (Nat.le_add_left j n))]
  exact main

/-- **Shifting the index of a colimit cocone on a sequential diagram keeps it colimiting.** The
leg of `c.whisker (natShift n)` at `j` is the leg of `c` at `n + j`. -/
noncomputable def isColimitWhiskerNatShift {c : Cocone F} (hc : IsColimit c) (n : ℕ) :
    IsColimit (c.whisker (natShift n)) where
  desc t := hc.desc (unshiftCocone F n t)
  fac t j := by
    have h : c.ι.app (n + j) ≫ hc.desc (unshiftCocone F n t) =
        (unshiftCocone F n t).ι.app (n + j) := hc.fac (unshiftCocone F n t) (n + j)
    exact h.trans (unshiftCocone_ι_app_add F n t j)
  uniq t x hx :=
    hc.uniq (unshiftCocone F n t) x fun m => by
      have hcw : F.map (homOfLE (Nat.le_add_left m n)) ≫ c.ι.app (n + m) = c.ι.app m :=
        c.w (homOfLE (Nat.le_add_left m n))
      have hxm : c.ι.app (n + m) ≫ x = shiftLeg F n t m := hx m
      have main : F.map (homOfLE (Nat.le_add_left m n)) ≫ (c.ι.app (n + m) ≫ x) =
          F.map (homOfLE (Nat.le_add_left m n)) ≫ shiftLeg F n t m := by rw [hxm]
      exact ((congrArg (fun y => y ≫ x) hcw).symm.trans (Category.assoc _ _ _)).trans main

end CategoryTheory.Limits

end
