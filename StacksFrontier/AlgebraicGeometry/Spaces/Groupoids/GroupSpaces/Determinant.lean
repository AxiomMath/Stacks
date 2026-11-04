module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.DeterminantBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.GeneralLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Multiplicative

/-!
# The determinant of the general linear group algebraic space

Let `B` be an algebraic space over a scheme `S` and let `n` be a natural number.  The
determinant is a morphism of group algebraic spaces `det : GLₙ,B ⟶ Gₘ,B` over `B`, and it is
the base change to `B` of the determinant morphism of group schemes over `S`.

## Main definitions

* `CategoryTheory.overProdFstMap` is the morphism `B ⨯ P ⟶ B ⨯ P'` over `B` induced by a
  morphism `P ⟶ P'` of group objects, and `CategoryTheory.overProdFstMap_isMonHom` is the
  statement that it is again a morphism of group objects.
* `AlgebraicGeometry.Space.determinantPointsOnSite` is the determinant morphism of group
  schemes over `S`, read on the functors of points restricted to the big fppf site over `S`.
* `AlgebraicGeometry.Space.determinantGroupSpaceMorphism`: **Stacks 043N**, the determinant as a
  morphism of group algebraic spaces over `B`.

## Main results

* `CategoryTheory.isMonHom_of_points` reduces being a morphism of monoid objects to
  multiplicativity on points, and `CategoryTheory.isMonHom_whiskerRight_forget` says that a
  morphism of presheaves of groups is a morphism of the underlying group objects in presheaves
  of sets.
* `AlgebraicGeometry.Space.determinantGroupSpaceMorphism_hom`: **Stacks 043N**, the underlying
  morphism over `B` is the product of the identity of `B` with the base change of the
  determinant morphism over `S`; this is the assertion that `det` on `GLₙ,B` *is* the base
  change of `det` on `GLₙ,S`.
* `AlgebraicGeometry.Space.determinantSpaceHom_apply`: **Stacks 043N**, on every scheme `T` over
  `B` the morphism sends a point of `GLₙ,B`, that is an invertible `n × n` matrix over
  `Γ(T, 𝒪_T)`, to its determinant, viewed as a global unit.

## Implementation notes

Both group algebraic spaces are base changes of group schemes over `S` belonging to the big
fppf site, as constructed in **Stacks 043M** and **Stacks 043J**; their underlying presheaves
over `B` are the products of `B` with the restrictions to the site of the functors of points of
`GLₙ,S` and `Gₘ,S`, and their group structures are the ones induced by those functors of
points.  The determinant morphism is therefore produced by functoriality: the determinant
morphism of group schemes over `S` of **Stacks 022X** induces a morphism of the two presheaves
of groups on the site, hence a morphism of the group objects underlying them in presheaves of
sets, hence the morphism `1_B × det` of group objects over `B`.  Nothing is chosen, so there is
no compatibility to check separately, and the identification of the morphism with a base change
is a definitional unfolding rather than a theorem about an abstractly obtained morphism.

That `1_B × det` is a morphism of group objects over `B` is checked on points, where the group
law is the prescribed one: `CategoryTheory.isMonHom_of_points` reduces the unit and
multiplication squares to statements about morphisms out of an arbitrary test object, and there
the morphism acts by postcomposition with `det`.

Stacks states this for `n ≥ 1`.  It is stated here for every `n : ℕ`, since **Stacks 022W**
constructs `GLₙ,S` for all `n`; for `n = 0` both group schemes have trivial fibres over `S` on
the points side and the determinant is the empty product, namely the unit.

## References

* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 022W](https://stacks.math.columbia.edu/tag/022W)
* [Stacks Project, Tag 022X](https://stacks.math.columbia.edu/tag/022X)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 043J](https://stacks.math.columbia.edu/tag/043J)
* [Stacks Project, Tag 043M](https://stacks.math.columbia.edu/tag/043M)
* [Stacks Project, Tag 043N](https://stacks.math.columbia.edu/tag/043N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w v u

namespace CategoryTheory

/-! ### Morphisms of monoid objects, tested on points -/

section Points

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism of a category with finite products between two monoid objects is a morphism of
monoid objects as soon as it is multiplicative on the points of every test object. -/
lemma isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (hone : ∀ {Z : C}, (1 : Z ⟶ X) ≫ f = 1)
    (hmul : ∀ {Z : C} (g₁ g₂ : Z ⟶ X), (g₁ * g₂) ≫ f = (g₁ ≫ f) * (g₂ ≫ f)) :
    IsMonHom f where
  one_hom := by
    have h : ∀ {W : C} [MonObj W], (1 : 𝟙_ C ⟶ W) = η[W] := fun {W} _ => by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _), Category.id_comp]
    rw [← h, ← h, hone]
  mul_hom := by
    have h : (fst X X * snd X X) = μ[X] := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hf : (f ⊗ₘ f) = lift (fst X X ≫ f) (snd X X ≫ f) := by
      apply hom_ext <;> simp
    rw [← h, hmul, hf, Hom.mul_def]

end Points

/-! ### Morphisms of presheaves of groups -/

section PresheafOfGroups

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves of groups is a morphism of the group objects which they define in
the category of presheaves of sets. -/
instance isMonHom_whiskerRight_forget {F G : Cᵒᵖ ⥤ GrpCat.{w}} (α : F ⟶ G) :
    IsMonHom (Functor.whiskerRight α (forget GrpCat)) where
  one_hom := by
    ext X x
    exact map_one (α.app X).hom
  mul_hom := by
    ext X x
    change (α.app X).hom ((MonObj.mul (X := F ⋙ forget GrpCat)).app X x) = _
    rw [show ((MonObj.mul (X := F ⋙ forget GrpCat)).app X x) = x.1 * x.2 from rfl, map_mul]
    rfl

end PresheafOfGroups

/-! ### Functoriality of the product with a group object -/

section OverProd

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryProducts C]
  (B : C) {P P' : C} [GrpObj P] [GrpObj P'] [CartesianMonoidalCategory (Over B)]

/-- The morphism `B ⨯ P ⟶ B ⨯ P'` over `B` induced by a morphism `P ⟶ P'` of group objects. -/
noncomputable def overProdFstMap (q : P ⟶ P') :
    (Over.mk (prod.fst : B ⨯ P ⟶ B) : Over B) ⟶ Over.mk (prod.fst : B ⨯ P' ⟶ B) :=
  Over.homMk (prod.map (𝟙 B) q)

/-- On points, `CategoryTheory.overProdFstMap` is postcomposition with the given morphism. -/
lemma overProdFstHomMulEquiv_comp_map (q : P ⟶ P') (X : Over B)
    (x : X ⟶ Over.mk (prod.fst : B ⨯ P ⟶ B)) :
    overProdFstHomMulEquiv B P' X (x ≫ overProdFstMap B q) =
      overProdFstHomMulEquiv B P X x ≫ q := by
  rw [overProdFstHomMulEquiv_apply, overProdFstHomMulEquiv_apply]
  simp [overProdFstMap]

/-- `CategoryTheory.overProdFstMap` is a morphism of group objects over `B`: on points it is
postcomposition with a morphism of group objects, hence multiplicative. -/
instance overProdFstMap_isMonHom (q : P ⟶ P') [IsMonHom q] :
    IsMonHom (overProdFstMap B q) :=
  isMonHom_of_points _
    (fun {Z} => (overProdFstHomMulEquiv B P' Z).injective (by
      rw [overProdFstHomMulEquiv_comp_map, map_one, map_one, MonObj.one_comp]))
    (fun {Z} g₁ g₂ => (overProdFstHomMulEquiv B P' Z).injective (by
      rw [overProdFstHomMulEquiv_comp_map, map_mul, map_mul,
        overProdFstHomMulEquiv_comp_map, overProdFstHomMulEquiv_comp_map, MonObj.mul_comp]))

end OverProd

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (n : ℕ)

/-- The determinant morphism of group schemes over `S` of **Stacks 022X**, read on the functors
of points restricted to the big fppf site over `S`. -/
noncomputable def determinantPointsOnSite :
    generalLinearPointsOnSite 𝒞 S hS n ⟶ multiplicativeGroupPointsOnSite 𝒞 S hS :=
  Functor.whiskerLeft (toSchemeOver 𝒞 S hS).op
    (yonedaGrp.map (determinantGroupSchemeMorphism n S))

/-- `AlgebraicGeometry.Space.determinantPointsOnSite` is the restriction to the site of the
determinant morphism of group schemes over `S`. -/
theorem determinantPointsOnSite_eq :
    determinantPointsOnSite 𝒞 S hS n =
      Functor.whiskerLeft (toSchemeOver 𝒞 S hS).op
        (yonedaGrp.map (determinantGroupSchemeMorphism n S)) :=
  rfl

/-- The morphism `GLₙ,B ⟶ Gₘ,B` over `B` underlying the determinant morphism of group
algebraic spaces: the product of the identity of `B` with the determinant morphism of group
schemes over `S`, the two group algebraic spaces being the products of `B` with the functors of
points of `GLₙ,S` and of `Gₘ,S` restricted to the site. -/
noncomputable def determinantSpaceHom (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (Over.mk (prod.fst :
        B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B) : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B) :=
  overProdFstMap B (Functor.whiskerRight (determinantPointsOnSite 𝒞 S hS n) (forget GrpCat))

/-- `AlgebraicGeometry.Space.determinantSpaceHom` is a morphism of group objects over `B`. -/
instance determinantSpaceHom_isMonHom (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    IsMonHom (determinantSpaceHom 𝒞 S hS n B) :=
  overProdFstMap_isMonHom B _

/-- **Stacks Project, Tag 043N.** The determinant, as a morphism of group algebraic spaces
`GLₙ,B ⟶ Gₘ,B` over an algebraic space `B` over `S`.  It is the base change to `B` of the
determinant morphism of group schemes over `S`. -/
@[stacks 043N]
noncomputable def determinantGroupSpaceMorphism (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    generalLinearSpace 𝒞 S hS n B hB ⟶ multiplicativeGroupSpace 𝒞 S hS B hB :=
  ObjectProperty.homMk
    (show Grp.mk (Over.mk (prod.fst :
          B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) ⟶
        Grp.mk (Over.mk (prod.fst :
          B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ B)) from
      Grp.homMk (determinantSpaceHom 𝒞 S hS n B))

/-- **Stacks Project, Tag 043N.** The morphism over `B` underlying the determinant morphism of
group algebraic spaces is the product of the identity of `B` with the determinant morphism of
group schemes over `S`; that is, `det` on `GLₙ,B` is the base change of `det` on `GLₙ,S`. -/
@[stacks 043N "base change of the determinant morphism over the base scheme"]
theorem determinantGroupSpaceMorphism_hom (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    (determinantGroupSpaceMorphism 𝒞 S hS n B hB).hom.hom.hom =
      determinantSpaceHom 𝒞 S hS n B :=
  rfl

/-- On points, `AlgebraicGeometry.Space.determinantSpaceHom` is postcomposition with the
determinant morphism of group schemes over `S`. -/
theorem yonedaEquiv_determinantSpaceHom (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    yonedaEquiv ((x ≫ determinantSpaceHom 𝒞 S hS n B).left ≫
        (prod.snd : B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ _)) =
      (yonedaGrp.map (determinantGroupSchemeMorphism n S)).app
        (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))
        (yonedaEquiv (x.left ≫
          (prod.snd : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ _))) := by
  have key : (x ≫ determinantSpaceHom 𝒞 S hS n B).left ≫
        (prod.snd : B ⨯ (multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat) ⟶ _) =
      (x.left ≫ (prod.snd : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ _)) ≫
        Functor.whiskerRight (determinantPointsOnSite 𝒞 S hS n) (forget GrpCat) :=
    overProdFstHomMulEquiv_comp_map B _ (Over.mk b) x
  rw [key, yonedaEquiv_comp]
  rfl

/-- **Stacks Project, Tag 043N.** On every scheme `T` over `B` the determinant morphism of group
algebraic spaces sends a point of `GLₙ,B`, that is an invertible `n × n` matrix over the global
sections of `T`, to its determinant, viewed as a global unit.  Its underlying morphism over `B`
is `AlgebraicGeometry.Space.determinantSpaceHom`, by
`AlgebraicGeometry.Space.determinantGroupSpaceMorphism_hom`. -/
@[stacks 043N "the determinant on points"]
theorem determinantSpaceHom_apply (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (T : BigFppfOver 𝒞 S hS) (b : yoneda.obj T ⟶ B)
    (x : (Over.mk b : Over B) ⟶
      Over.mk (prod.fst : B ⨯ (generalLinearPointsOnSite 𝒞 S hS n ⋙ forget GrpCat) ⟶ B)) :
    multiplicativeGroupSpacePoints 𝒞 S hS B T b (x ≫ determinantSpaceHom 𝒞 S hS n B) =
      Matrix.GeneralLinearGroup.det (generalLinearSpacePoints 𝒞 S hS n B T b x) := by
  rw [multiplicativeGroupSpacePoints_apply, generalLinearSpacePoints_apply,
    yonedaEquiv_determinantSpaceHom]
  exact determinantGroupSchemeMorphism_apply n S
    (Opposite.op ((toSchemeOver 𝒞 S hS).obj T)) _

end AlgebraicGeometry.Space

end
