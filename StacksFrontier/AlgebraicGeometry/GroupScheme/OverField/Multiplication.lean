module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplication on a group scheme over a field is open

Multiplication on a group scheme over a field is an open map on underlying topological
spaces, and so is multiplication by a family of translations parametrized by an auxiliary
scheme.  Both statements come from the shear automorphism of `G ⊗ G` which turns
multiplication into a projection, and projections of a fibre product of schemes are open.

## Main results

* `AlgebraicGeometry.isOpenMap_mul`: multiplication on a group scheme over a field is open.
* `AlgebraicGeometry.isOpen_image_mul_of_open`: the image of the parametrized translates of
  an open subset of a group scheme is open.

## Implementation notes

A group scheme over `Spec K` is represented by a group object in the category of schemes over
`Spec K`. Its monoidal product is the fibre product over `Spec K`, so the underlying morphism
of `μ[G]` is exactly the multiplication morphism in the source, and the open subscheme `T × U`
is represented by the inverse image of `U` under the second projection from `T ⊗ G`.

## References

* [Stacks Project, Tag 047K](https://stacks.math.columbia.edu/tag/047K)
* [Stacks Project, Tag 0B7N](https://stacks.math.columbia.edu/tag/0B7N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

/-- A morphism of `Over` schemes that factors as an isomorphism followed by an open morphism is
open on underlying spaces. -/
private lemma isOpenMap_of_hom_comp_eq {S : Scheme.{u}} {X Y Z : Over S} (e : X ≅ Y) (p : Y ⟶ Z)
    (hp : IsOpenMap p.left.base) (f : X ⟶ Z) (h : e.hom ≫ p = f) : IsOpenMap f.left.base := by
  subst h
  exact hp.comp ((Over.forget _).mapIso e).hom.homeomorph.isOpenMap

/-- **Stacks Project, Tag 047K.** The multiplication morphism of a group scheme over a field is
open. -/
@[stacks 047K]
lemma isOpenMap_mul {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] :
    IsOpenMap μ[G].left := by
  let e : (G ⊗ G) ≅ (G ⊗ G) :=
    { hom := lift μ[G] (snd G G)
      inv := lift (fst G G / snd G G) (snd G G)
      hom_inv_id := by apply hom_ext <;> simp [GrpObj.comp_div, MonObj.mul_eq_mul]
      inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul] }
  exact isOpenMap_of_hom_comp_eq e (fst G G)
    (show IsOpenMap (pullback.fst G.hom G.hom) from Scheme.Hom.isOpenMap _) _ (by simp [e])

/-- The automorphism of `A ⊗ G` translating the second coordinate by the `A`-point `t` of the
group scheme `G`. -/
private noncomputable def translationIso {k : Type u} [Field k]
    (A G : Over (Spec (.of k))) [GrpObj G] (t : A ⟶ G) : (A ⊗ G) ≅ (A ⊗ G) where
  hom := lift (fst A G) (lift (fst A G ≫ t) (snd A G) ≫ μ[G])
  inv := lift (fst A G) (lift ((fst A G ≫ t)⁻¹) (snd A G) ≫ μ[G])
  hom_inv_id := by apply hom_ext <;> simp [GrpObj.comp_inv, MonObj.comp_mul, MonObj.mul_eq_mul]
  inv_hom_id := by apply hom_ext <;> simp [MonObj.comp_mul, MonObj.mul_eq_mul]

/-- Translating the second coordinate of `A ⊗ G` by an `A`-point of `G` and then multiplying is
an open map, being the second projection composed with an automorphism. -/
private lemma isOpenMap_translate {k : Type u} [Field k]
    (A G : Over (Spec (.of k))) [GrpObj G] (t : A ⟶ G) :
    IsOpenMap (lift (fst A G ≫ t) (snd A G) ≫ μ[G]).left.base :=
  isOpenMap_of_hom_comp_eq (translationIso A G t) (snd A G) (pullback.snd A.hom G.hom).isOpenMap
    _ (by simp [translationIso])

/-- **Stacks Project, Tag 0B7N.** The image of `T × U` under parametrized
multiplication is open. -/
@[stacks 0B7N]
lemma isOpen_image_mul_of_open {k : Type u} [Field k]
    (G T : Over (Spec (.of k))) [GrpObj G] (ψ : T ⟶ G)
    (U : G.left.Opens) :
    IsOpen (Set.image (lift (fst T G ≫ ψ) (snd T G) ≫ μ[G]).left.base
      ((snd T G).left.base ⁻¹' (U : Set G.left))) :=
  isOpenMap_translate T G ψ _ (U.2.preimage (snd T G).left.continuous)

end AlgebraicGeometry

end
