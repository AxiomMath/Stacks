module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Composing a pullback square with a monomorphism

A commutative square

```
P --fst--> X
|          |
snd        f
|          |
v          v
Y --g----> Z
```

which is a pullback remains one after composing both of its bottom-right arrows with a single
monomorphism `m : Z ⟶ W`, and conversely.

## Main results

* `CategoryTheory.IsPullback.comp_mono`: a pullback square composed with a monomorphism is a
  pullback square.
* `CategoryTheory.IsPullback.of_comp_mono`: the converse — if the enlarged square is a pullback
  then so is the original one, the commutativity of the original one being taken as a
  hypothesis.
* `CategoryTheory.IsPullback.comp_mono_iff`: for a commutative square, the two conditions are
  equivalent.
* `CategoryTheory.IsPullback.of_comp_mono'`: the same converse with no commutativity hypothesis
  at all.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- If the square
with sides `fst`, `snd`, `f`, `g` is a pullback and `m` is a monomorphism, then the square with
sides `fst`, `snd`, `f ≫ m`, `g ≫ m` is a pullback. -/
public theorem IsPullback.comp_mono {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (m : Z ⟶ W) [Mono m] :
    IsPullback fst snd (f ≫ m) (g ≫ m) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono f g m _ h.isLimit)

/-- If the square with sides `fst`, `snd`, `f`, `g` commutes, `m` is a monomorphism and the square
with sides `fst`, `snd`, `f ≫ m`, `g ≫ m` is a pullback, then the square with sides `fst`, `snd`,
`f`, `g` is a pullback. -/
public theorem IsPullback.of_comp_mono {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} {m : Z ⟶ W} [Mono m] (w : fst ≫ f = snd ≫ g)
    (h : IsPullback fst snd (f ≫ m) (g ≫ m)) : IsPullback fst snd f g where
  w := w
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk w
      (fun s => h.lift s.fst s.snd (by
        rw [← Category.assoc, ← Category.assoc, s.condition]))
      (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _)
      (fun s u hu₁ hu₂ =>
        h.hom_ext (hu₁.trans (h.lift_fst _ _ _).symm) (hu₂.trans (h.lift_snd _ _ _).symm))⟩

/-- If `m` is a monomorphism and the square with sides `fst`, `snd`, `f ≫ m`, `g ≫ m` is a
pullback, then the square with sides `fst`, `snd`, `f`, `g` is a pullback. -/
public theorem IsPullback.of_comp_mono' {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (m : Z ⟶ W) [Mono m] (h : IsPullback fst snd (f ≫ m) (g ≫ m)) :
    IsPullback fst snd f g :=
  IsPullback.of_comp_mono ((cancel_mono m).mp (by simpa only [Category.assoc] using h.w)) h

/-- Enlarging a commutative square along a monomorphism neither creates nor destroys the
pullback property. -/
public theorem IsPullback.comp_mono_iff {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (m : Z ⟶ W) [Mono m] (sq : CommSq fst snd f g) :
    IsPullback fst snd (f ≫ m) (g ≫ m) ↔ IsPullback fst snd f g :=
  ⟨fun h => IsPullback.of_comp_mono sq.w h, fun h => h.comp_mono m⟩

end CategoryTheory

end
