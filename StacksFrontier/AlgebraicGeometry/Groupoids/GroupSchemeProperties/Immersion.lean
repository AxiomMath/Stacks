module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.LocallyClosedImage

/-!
# Immersions of group schemes over a field are closed immersions

A group scheme over a base scheme `S` is a group object in schemes over `S`, and such a group
object is the same thing as a groupoid scheme over `S` with one object: the object scheme is the
terminal object of the over category, the arrow scheme is the group scheme, and the source and
target maps are the unique morphism to the terminal object.

Under this identification a homomorphism of group schemes becomes a morphism of groupoid
schemes which is the identity on objects, so over a field its image on arrows is closed as soon
as it is locally closed (Stacks 04Q9). An immersion has locally closed image, so an immersion
of group schemes over a field is a closed immersion, and an immersed subgroup scheme over a
field is a closed subgroup scheme.

## Main definitions

* `AlgebraicGeometry.groupoidSchemeOfGrp` is a group scheme over `S`, viewed as a groupoid
  scheme over `S` with one object.
* `AlgebraicGeometry.groupoidSchemeHomOfGrpHom` is a homomorphism of group schemes, viewed as a
  morphism of the associated groupoid schemes.

## Main results

* `AlgebraicGeometry.isClosedImmersion_of_isImmersion`: an immersion of group schemes over a
  field is a closed immersion.

## References

* [Stacks Project, Tag 047D](https://stacks.math.columbia.edu/tag/047D)
* [Stacks Project, Tag 047T](https://stacks.math.columbia.edu/tag/047T)
* [Stacks Project, Tag 04Q9](https://stacks.math.columbia.edu/tag/04Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj CategoryTheory.GrpObj
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-! ### A group scheme as a groupoid scheme with one object -/

/-- A pair of generalized points of an object of a cartesian monoidal category, lifted to the
fibre product of two copies of the morphism to the terminal object, is the pair itself. -/
private theorem lift_comp_liftFstSnd {S : Scheme.{u}} {X T : Over S} (f g : T ⟶ X)
    (w : f ≫ toUnit X = g ≫ toUnit X) :
    pullback.lift f g w ≫
      CartesianMonoidalCategory.lift (pullback.fst (toUnit X) (toUnit X))
        (pullback.snd (toUnit X) (toUnit X)) = CartesianMonoidalCategory.lift f g := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd, pullback.lift_fst, pullback.lift_snd]

/-- Multiplying a composable pair of generalized points of a group scheme is multiplying the
pair itself. -/
private theorem lift_comp_liftFstSnd_mul {S : Scheme.{u}} {X T : Over S} [MonObj X]
    (f g : T ⟶ X) (w : f ≫ toUnit X = g ≫ toUnit X) :
    pullback.lift f g w ≫
        CartesianMonoidalCategory.lift (pullback.fst (toUnit X) (toUnit X))
          (pullback.snd (toUnit X) (toUnit X)) ≫ μ[X] =
      CartesianMonoidalCategory.lift f g ≫ μ[X] := by
  rw [← Category.assoc, lift_comp_liftFstSnd]

/-- A group scheme over `S`, viewed as a groupoid scheme over `S` with one object: the object
scheme is the terminal object of the over category and the arrow scheme is the group scheme. -/
@[implicit_reducible]
noncomputable def groupoidSchemeOfGrp {S : Scheme.{u}} (G : Grp (Over S)) :
    GroupoidScheme S where
  objects := 𝟙_ (Over S)
  arrows := G.X
  source := toUnit G.X
  target := toUnit G.X
  comp := CartesianMonoidalCategory.lift (pullback.fst (toUnit G.X) (toUnit G.X))
    (pullback.snd (toUnit G.X) (toUnit G.X)) ≫ μ[G.X]
  identity := η[G.X]
  inverse := ι[G.X]
  source_identity := toUnit_unique _ _
  target_identity := toUnit_unique _ _
  source_inverse := toUnit_unique _ _
  target_inverse := toUnit_unique _ _
  source_comp := toUnit_unique _ _
  target_comp := toUnit_unique _ _
  left_identity T f w := by
    rw [lift_comp_liftFstSnd_mul (X := G.X) _ _ (toUnit_unique _ _)]
    simpa only [← Category.assoc,
      show f ≫ toUnit G.X = toUnit T from toUnit_unique _ _] using
      MonObj.lift_comp_one_left (toUnit T) f
  right_identity T f w := by
    rw [lift_comp_liftFstSnd_mul (X := G.X) _ _ (toUnit_unique _ _)]
    simpa only [← Category.assoc,
      show f ≫ toUnit G.X = toUnit T from toUnit_unique _ _] using
      MonObj.lift_comp_one_right f (toUnit T)
  left_inverse T f w := by
    rw [lift_comp_liftFstSnd_mul (X := G.X) _ _ (toUnit_unique _ _)]
    simp
  right_inverse T f w := by
    rw [lift_comp_liftFstSnd_mul (X := G.X) _ _ (toUnit_unique _ _)]
    simp
  assoc T f g h wfg wgh w₁ w₂ := by
    simp only [lift_comp_liftFstSnd_mul]
    exact MonObj.lift_lift_assoc f g h

/-- A homomorphism of group schemes over `S`, viewed as a morphism of the associated groupoid
schemes; it is the identity on the one object. -/
@[implicit_reducible]
noncomputable def groupoidSchemeHomOfGrpHom {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H) :
    GroupoidScheme.Hom (groupoidSchemeOfGrp G) (groupoidSchemeOfGrp H) where
  mapObjects := 𝟙 (𝟙_ (Over S))
  mapArrows := f.hom.hom
  map_source := toUnit_unique _ _
  map_target := toUnit_unique _ _
  map_identity := by
    change 𝟙 _ ≫ η[H.X] = η[G.X] ≫ f.hom.hom
    simp
  map_comp T f₁ f₂ w w' := by
    dsimp [groupoidSchemeOfGrp] at f₁ f₂ w w' ⊢
    change (pullback.lift f₁ f₂ w ≫
        CartesianMonoidalCategory.lift (pullback.fst _ _) (pullback.snd _ _)) ≫
          μ[G.X] ≫ f.hom.hom =
      (pullback.lift (f₁ ≫ f.hom.hom) (f₂ ≫ f.hom.hom) w' ≫
        CartesianMonoidalCategory.lift (pullback.fst _ _) (pullback.snd _ _)) ≫ μ[H.X]
    rw [lift_comp_liftFstSnd, lift_comp_liftFstSnd, IsMonHom.mul_hom, ← Category.assoc,
      CartesianMonoidalCategory.lift_map]

/-! ### Immersions of group schemes over a field -/

/-- **Stacks Project, Tag 047T.** Every immersion of group schemes over a field is a closed
immersion. -/
@[stacks 047T]
theorem isClosedImmersion_of_isImmersion {k : Type u} [Field k]
    {G' G : Grp (Over (Spec (.of k)))} (i : G' ⟶ G)
    [IsImmersion i.hom.hom.left] : IsClosedImmersion i.hom.hom.left := by
  have hobjects : (groupoidSchemeOfGrp G').objects = (groupoidSchemeOfGrp G).objects := rfl
  have hfield : (groupoidSchemeOfGrp G').objects.left = Spec (.of k) := rfl
  have hmapObjects : (groupoidSchemeHomOfGrpHom i).mapObjects = eqToHom hobjects := rfl
  have hlc : IsLocallyClosed
      (Set.range (groupoidSchemeHomOfGrpHom i).mapArrows.left.base) :=
    IsImmersion.isLocallyClosed_range (f := i.hom.hom.left)
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  exact isClosed_range_mapArrows_of_isLocallyClosed (groupoidSchemeHomOfGrpHom i) hobjects
    hfield hmapObjects hlc

end AlgebraicGeometry

end
