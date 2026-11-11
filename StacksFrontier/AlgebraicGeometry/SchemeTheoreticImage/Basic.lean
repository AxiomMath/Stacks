module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the scheme-theoretic image

A commutative square
```
X ⟶ A
↓f   ↓g
Y ⟶ B
```
of schemes, with horizontal maps `x : X ⟶ A` and `y : Y ⟶ B`, induces a morphism
`x.image ⟶ y.image` of scheme-theoretic images: the kernel ideal of `y` is contained in the
kernel ideal of `x ≫ g = f ≫ y`, so the closed immersion `x.imageι ≫ g` factors through the
closed subscheme `y.image` of `B`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.imageMap` is the induced morphism of scheme-theoretic images.
* `AlgebraicGeometry.Scheme.Hom.imageIsoOfIsIso` is the resulting identification
  `x.image ≅ (x ≫ g).image` for `g` an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.imageMap_imageι` and
  `AlgebraicGeometry.Scheme.Hom.toImage_imageMap`: the two commutativities characterising
  `imageMap`.
* `AlgebraicGeometry.Scheme.Hom.imageMap_id` and
  `AlgebraicGeometry.Scheme.Hom.imageMap_comp`: `imageMap` is functorial.
* `AlgebraicGeometry.Scheme.Hom.isProper_imageMap`,
  `AlgebraicGeometry.Scheme.Hom.isClosedImmersion_imageMap`,
  `AlgebraicGeometry.Scheme.Hom.isAffineHom_imageMap` and
  `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_imageMap`: `imageMap` inherits properness,
  being a closed immersion, affineness and being locally of finite type from `g`.
* `AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_comp_eq_imageι`: if `x` factors through
  a closed immersion, then so does `x.imageι`, by a closed immersion.
* `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType` and
  `AlgebraicGeometry.isNoetherian_image`: a scheme of finite type over a Noetherian scheme is
  Noetherian, and in particular the scheme-theoretic image of any morphism to a Noetherian
  scheme is Noetherian.

## Implementation notes

`imageMap` is defined by `AlgebraicGeometry.IsClosedImmersion.lift` against `y.imageι`, so
`imageMap_imageι` is `AlgebraicGeometry.IsClosedImmersion.lift_fac` and every identity between
`imageMap`s is proved by cancelling the monomorphism `y.imageι`.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 01R9](https://stacks.math.columbia.edu/tag/01R9), the induced morphism of
  scheme-theoretic images.
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks 01T6, Noetherian case.** If `f : X ⟶ Y` is quasi-compact and locally of finite type
(that is, of finite type) and `Y` is Noetherian, then `X` is Noetherian. The locally Noetherian
case is `AlgebraicGeometry.isLocallyNoetherian_of_locallyOfFiniteType`. -/
@[stacks 01T6 "Noetherian case: `f` quasi-compact and locally of finite type, `Y` Noetherian"]
lemma isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-- A closed subscheme of a Noetherian scheme is Noetherian. -/
@[ega "I 6.1.4" "special case"]
lemma isNoetherian_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsNoetherian Y] : IsNoetherian X :=
  isNoetherian_of_locallyOfFiniteType f

namespace Scheme.Hom

variable {X Y Z A B C : Scheme.{u}}

/-- The morphism of scheme-theoretic images induced by a commutative square: for `x : X ⟶ A`,
`y : Y ⟶ B`, `f : X ⟶ Y` and `g : A ⟶ B` with `x ≫ g = f ≫ y`, the closed immersion
`x.imageι ≫ g` factors through the closed subscheme `y.image` of `B`. -/
@[stacks 01R9]
noncomputable def imageMap (x : X ⟶ A) (y : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : x ≫ g = f ≫ y) : x.image ⟶ y.image :=
  IsClosedImmersion.lift y.imageι (x.imageι ≫ g) (by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
      Scheme.IdealSheafData.ker_subschemeι, ← Scheme.Hom.ker_comp, h]
    exact f.le_ker_comp y)

/-- The induced morphism `imageMap x y f g h` followed by the closed immersion `y.imageι` is
`x.imageι ≫ g`. -/
@[reassoc (attr := simp), stacks 01R9]
lemma imageMap_imageι (x : X ⟶ A) (y : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : x ≫ g = f ≫ y) : imageMap x y f g h ≫ y.imageι = x.imageι ≫ g :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `x.toImage` followed by the induced morphism `imageMap x y f g h` is
`f ≫ y.toImage`. -/
@[reassoc (attr := simp), stacks 01R9]
lemma toImage_imageMap (x : X ⟶ A) (y : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : x ≫ g = f ≫ y) : x.toImage ≫ imageMap x y f g h = f ≫ y.toImage := by
  rw [← cancel_mono y.imageι]
  simp [h]

/-- The morphism of scheme-theoretic images induced by the identity square on `x` is the
identity. -/
@[simp]
lemma imageMap_id (x : X ⟶ A) : imageMap x x (𝟙 X) (𝟙 A) (by simp) = 𝟙 x.image := by
  rw [← cancel_mono x.imageι]
  simp

/-- The morphism of scheme-theoretic images induced by the pasting of two commutative
squares is the composite of the induced morphisms. -/
lemma imageMap_comp (x : X ⟶ A) (y : Y ⟶ B) (z : Z ⟶ C) (f : X ⟶ Y) (f' : Y ⟶ Z)
    (g : A ⟶ B) (g' : B ⟶ C) (h : x ≫ g = f ≫ y) (h' : y ≫ g' = f' ≫ z) :
    imageMap x y f g h ≫ imageMap y z f' g' h' =
      imageMap x z (f ≫ f') (g ≫ g')
        (by rw [← Category.assoc, h, Category.assoc, h', Category.assoc]) := by
  rw [← cancel_mono z.imageι]
  simp only [Category.assoc, imageMap_imageι]
  rw [← Category.assoc, imageMap_imageι, Category.assoc]

section Properties

variable (x : X ⟶ A) (y : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B) (h : x ≫ g = f ≫ y)

/-- The induced morphism of scheme-theoretic images is proper if `g` is. -/
lemma isProper_imageMap [IsProper g] : IsProper (imageMap x y f g h) :=
  @IsProper.of_comp _ _ _ (imageMap x y f g h) y.imageι
    (by rw [imageMap_imageι]; infer_instance) _

/-- The induced morphism of scheme-theoretic images is a closed immersion if `g` is. -/
lemma isClosedImmersion_imageMap [IsClosedImmersion g] :
    IsClosedImmersion (imageMap x y f g h) :=
  @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (imageMap x y f g h) y.imageι _
    (by rw [imageMap_imageι]; infer_instance)

/-- The induced morphism of scheme-theoretic images is affine if `g` is. -/
lemma isAffineHom_imageMap [IsAffineHom g] : IsAffineHom (imageMap x y f g h) :=
  @IsAffineHom.of_comp _ _ _ (imageMap x y f g h) y.imageι
    (by rw [imageMap_imageι]; infer_instance) _

/-- The induced morphism of scheme-theoretic images is locally of finite type if `g` is. -/
lemma locallyOfFiniteType_imageMap [LocallyOfFiniteType g] :
    LocallyOfFiniteType (imageMap x y f g h) :=
  @locallyOfFiniteType_of_comp _ _ _ (imageMap x y f g h) y.imageι
    (by rw [imageMap_imageι]; infer_instance)

end Properties

/-- The scheme-theoretic image is unchanged, as a closed subscheme of the target, by an
isomorphism of the target. -/
@[simps! hom inv]
noncomputable def imageIsoOfIsIso (x : X ⟶ A) (g : A ⟶ B) [IsIso g] :
    x.image ≅ (x ≫ g).image where
  hom := imageMap x (x ≫ g) (𝟙 X) g (Category.id_comp _).symm
  inv := imageMap (x ≫ g) x (𝟙 X) (inv g) (by simp)
  hom_inv_id := by rw [imageMap_comp]; simp
  inv_hom_id := by rw [imageMap_comp]; simp

/-- If `x : X ⟶ B` factors through a closed immersion `i : A ⟶ B`, then so does the closed
immersion `x.imageι`, and the factoring morphism `x.image ⟶ A` is again a closed immersion. -/
@[ega "I 9.5.1" "minimality clause"]
lemma exists_isClosedImmersion_comp_eq_imageι {x : X ⟶ B} (i : A ⟶ B) [IsClosedImmersion i]
    (a : X ⟶ A) (ha : a ≫ i = x) :
    ∃ p : x.image ⟶ A, IsClosedImmersion p ∧ p ≫ i = x.imageι := by
  have hker : i.ker ≤ x.imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← ha]
    exact a.le_ker_comp i
  refine ⟨IsClosedImmersion.lift i x.imageι hker, ?_, IsClosedImmersion.lift_fac i x.imageι hker⟩
  exact @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (IsClosedImmersion.lift i x.imageι hker)
    i _ (by rw [IsClosedImmersion.lift_fac]; infer_instance)

end Scheme.Hom

/-- The scheme-theoretic image of a morphism to a Noetherian scheme is Noetherian. -/
instance isNoetherian_image {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] :
    IsNoetherian f.image :=
  isNoetherian_of_isClosedImmersion f.imageι

end AlgebraicGeometry

end
