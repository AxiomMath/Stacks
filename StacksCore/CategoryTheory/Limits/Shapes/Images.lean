module

public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-! # Image maps of commutative squares

`factorThruImage_comp_image_map_homMk'`: the map `image k ⟶ image l` induced by a commutative
square `m ≫ l = k ≫ n` is compatible with the `factorThruImage`s, `factorThruImage k ≫ image.map …
= m ≫ factorThruImage l`. This is Mathlib's `image.factor_map` for the square `Arrow.homMk' m n w`,
stated on plain morphisms so that `simp` and `rw` can use it (Mathlib's `image.map_homMk'_ι` is
the analogous statement for the `image.ι`s). Used for the level maps of the image filtration of
filtered objects (`StacksCore.CategoryTheory.Filtration.Basic`). -/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- The image map of a commutative square `m ≫ l = k ≫ n` is compatible with the
`factorThruImage`s: `factorThruImage k ≫ image.map (Arrow.homMk' m n w) = m ≫ factorThruImage l`.
The `factorThruImage` analogue of Mathlib's `image.map_homMk'_ι`. -/
@[reassoc (attr := simp)]
lemma factorThruImage_comp_image_map_homMk' {X Y P Q : C} {k : X ⟶ Y} [HasImage k] {l : P ⟶ Q}
    [HasImage l] {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n) [HasImageMap (Arrow.homMk' _ _ w)] :
    factorThruImage k ≫ image.map (Arrow.homMk' _ _ w) = m ≫ factorThruImage l :=
  image.factor_map (Arrow.homMk' (f := k) (g := l) m n w)

end CategoryTheory.Limits
