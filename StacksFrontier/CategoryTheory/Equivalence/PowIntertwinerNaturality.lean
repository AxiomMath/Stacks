module

public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner

/-!
# The intertwiner of integer iterates is natural when the comparison it is built from is

`StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner` transports a comparison
`α M : R (e M) ≅ e' (R M)` to every integer iterate, as `Stacks.Equivalence.powIntertwineObj`.
That construction is stated objectwise and proves no naturality, deliberately: its own
implementation notes record that naturality of the result needs naturality of `α`, which is a
strictly stronger input than the objectwise family.

This file supplies exactly that step. Given the naturality of `α` as a hypothesis, every iterate
of the comparison is natural: `powIntertwineObj_naturality` below.

## Main results

* `Stacks.Equivalence.inverseIntertwineObj_naturality`: the comparison for the quasi-inverses is
  natural. This is the step that makes the negative iterates work, since
  `Stacks.Equivalence.powIntertwineObj` sends a negative exponent to an iterate of the
  quasi-inverses.
* `Stacks.Equivalence.powNatIntertwineObj_naturality`: the comparison for natural-number iterates
  is natural, by the induction `Stacks.Equivalence.powNatIntertwineObj` itself recurses along.
* `Stacks.Equivalence.powIntertwineObj_naturality`: **the comparison for integer iterates is
  natural.** A negative exponent is reduced to the previous result applied to the quasi-inverses.

## Implementation notes

Naturality of `α` is taken as an explicit hypothesis rather than by asking for a natural
isomorphism of functors `e.functor ⋙ R ≅ R ⋙ e'.functor`. The two are interchangeable, and the
hypothesis form is the one that composes with `powIntertwineObj`, whose `α` argument is an
objectwise family; asking for the functor form would force every caller to build a
`NatIso.ofComponents` first and would then have to take it apart again at each component.

The recursion of `powNatIntertwineObj` at `n + 2` reduces the exponent at the object `e M`, so
the induction here is on the *statement for every pair of objects* at a fixed exponent, and the
inductive hypothesis is used at the morphism `e.functor.map g` rather than at `g`. That is why
the induction is written over `n` with `M`, `N` and `g` universally quantified inside.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Stacks.Equivalence

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A functor carries an equality of two composites to an equality of the composites of images. -/
private theorem map_comp_eq_map_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {W X Z Y' : C} {f : W ⟶ X} {g : X ⟶ Z} {f' : W ⟶ Y'}
    {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **The comparison for the quasi-inverses is natural.** Unfolding
`Stacks.Equivalence.inverseIntertwineObj`, the claim is the naturality of the unit of `e'`
followed, inside `e'.inverse`, by the naturality of `α` and of the counit of `e`. -/
theorem inverseIntertwineObj_naturality (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (hα : ∀ {M N : A} (g : M ⟶ N), R.map (e.functor.map g) ≫ (α N).hom =
      (α M).hom ≫ e'.functor.map (R.map g))
    {M N : A} (g : M ⟶ N) :
    R.map (e.inverse.map g) ≫ (inverseIntertwineObj e e' R α N).hom =
      (inverseIntertwineObj e e' R α M).hom ≫ e'.inverse.map (R.map g) := by
  -- The three ingredients, each stated in the shape `rw` needs.
  have key : ∀ P : A, (inverseIntertwineObj e e' R α P).hom =
      e'.unit.app (R.obj (e.inverse.obj P)) ≫
        e'.inverse.map ((α (e.inverse.obj P)).inv ≫ R.map (e.counit.app P)) := fun _ => rfl
  have hunit : R.map (e.inverse.map g) ≫ e'.unit.app (R.obj (e.inverse.obj N)) =
      e'.unit.app (R.obj (e.inverse.obj M)) ≫
        e'.inverse.map (e'.functor.map (R.map (e.inverse.map g))) :=
    e'.unit.naturality _
  have hαg : (α (e.inverse.obj M)).inv ≫ R.map (e.functor.map (e.inverse.map g)) =
      e'.functor.map (R.map (e.inverse.map g)) ≫ (α (e.inverse.obj N)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hα (e.inverse.map g)
  have hcounit : R.map (e.functor.map (e.inverse.map g)) ≫ R.map (e.counit.app N) =
      R.map (e.counit.app M) ≫ R.map g :=
    map_comp_eq_map_comp R (e.counit.naturality g)
  rw [key, key]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc, hunit]
  simp only [Category.assoc, ← Functor.map_comp]
  refine congrArg (e'.unit.app (R.obj (e.inverse.obj M)) ≫ e'.inverse.map ·) ?_
  rw [← Category.assoc, ← hαg]
  simp only [Category.assoc]
  rw [hcounit, Functor.map_comp]

/-- **The comparison for natural-number iterates is natural.** The induction is the one
`Stacks.Equivalence.powNatIntertwineObj` recurses along: the exponent `n + 2` is reduced to
`n + 1` at the object `e M`, so the inductive hypothesis is applied at `e.functor.map g`. -/
theorem powNatIntertwineObj_naturality (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (hα : ∀ {M N : A} (g : M ⟶ N), R.map (e.functor.map g) ≫ (α N).hom =
      (α M).hom ≫ e'.functor.map (R.map g)) :
    ∀ (n : ℕ) {M N : A} (g : M ⟶ N),
      R.map ((e.powNat n).functor.map g) ≫ (powNatIntertwineObj e e' R α n N).hom =
        (powNatIntertwineObj e e' R α n M).hom ≫ (e'.powNat n).functor.map (R.map g)
  | 0, M, N, g => by
      change R.map g ≫ 𝟙 (R.obj N) = 𝟙 (R.obj M) ≫ R.map g
      rw [Category.comp_id, Category.id_comp]
  | 1, _, _, g => hα g
  | n + 2, M, N, g => by
      have ih := powNatIntertwineObj_naturality e e' R α hα (n + 1) (e.functor.map g)
      -- The recursion of `powNatIntertwineObj` at `n + 2`, which holds by `rfl`.
      have step : (e'.powNat (n + 1)).functor.map (R.map (e.functor.map g)) ≫
          (e'.powNat (n + 1)).functor.map (α N).hom =
            (e'.powNat (n + 1)).functor.map (α M).hom ≫
              (e'.powNat (n + 1)).functor.map (e'.functor.map (R.map g)) :=
        map_comp_eq_map_comp _ (hα g)
      -- Both iterates at `n + 2` reduce to `n + 1`, innermost, definitionally, so the whole
      -- goal is restated at `n + 1` by `change`: rewriting with those identities instead would
      -- leave a term that is not type-correct at `implicit` transparency.
      change R.map ((e.powNat (n + 1)).functor.map (e.functor.map g)) ≫
          ((powNatIntertwineObj e e' R α (n + 1) (e.functor.obj N)).hom ≫
            (e'.powNat (n + 1)).functor.map (α N).hom) =
        ((powNatIntertwineObj e e' R α (n + 1) (e.functor.obj M)).hom ≫
            (e'.powNat (n + 1)).functor.map (α M).hom) ≫
          (e'.powNat (n + 1)).functor.map (e'.functor.map (R.map g))
      rw [← Category.assoc, ih]
      simp only [Category.assoc]
      rw [step]

/-- **The comparison for integer iterates is natural.** For a negative exponent the comparison is
the natural-number iterate of the one built for the quasi-inverses, whose naturality is
`Stacks.Equivalence.inverseIntertwineObj_naturality`. -/
theorem powIntertwineObj_naturality (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M))
    (hα : ∀ {M N : A} (g : M ⟶ N), R.map (e.functor.map g) ≫ (α N).hom =
      (α M).hom ≫ e'.functor.map (R.map g)) :
    ∀ (n : ℤ) {M N : A} (g : M ⟶ N),
      R.map ((e ^ n).functor.map g) ≫ (powIntertwineObj e e' R α n N).hom =
        (powIntertwineObj e e' R α n M).hom ≫ (e' ^ n).functor.map (R.map g)
  | Int.ofNat n, _, _, g => powNatIntertwineObj_naturality e e' R α hα n g
  | Int.negSucc n, _, _, g =>
      powNatIntertwineObj_naturality e.symm e'.symm R
        (fun P => inverseIntertwineObj e e' R α P)
        (fun {_ _} h => inverseIntertwineObj_naturality e e' R α hα h) (n + 1) g

end Stacks.Equivalence

end
