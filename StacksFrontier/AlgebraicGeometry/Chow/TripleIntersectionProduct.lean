module

public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductAssociativity
public import StacksCore.Tactic.StacksAttribute

/-!
# The triple intersection product and the substrate of its associativity

This module supplies the fibre-product geometry that the proof of Stacks 0FC1 runs on, and which
the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductAssociativity`
name as the obstruction to stating the source's chain of equalities at all: *the identification of
the pullback of the diagonal along a test morphism of the triple product with `(Y ×_X Z) ×_k W`.*

## Main definitions

* `Stacks.Chow.pullbackCongrFst` and `Stacks.Chow.pullbackCongrSnd` — replacing one leg of a fibre
  product by an isomorphic one.
* `Stacks.Chow.fibreProductToExteriorProduct` — the canonical morphism `Y ×_X Z ⟶ Y ×_S Z`.
* `Stacks.Chow.pullbackDiagonalExteriorTestIso` — **the substrate identification.**

## References

* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Replacing one leg of a fibre product by an isomorphic one -/

section Reindex

variable {A B T E : Scheme.{u}} {u' : A ⟶ E} {u : B ⟶ E}

/-- Replacing the first leg `u' : A ⟶ E` of a fibre product by an isomorphic morphism
`u : B ⟶ E`, the isomorphism `D : A ≅ B` being compatible with the two legs. -/
def pullbackCongrFst (D : A ≅ B) (hD : D.hom ≫ u = u') (v : T ⟶ E) :
    (pullback u' v : Scheme.{u}) ≅ (pullback u v : Scheme.{u}) where
  hom := pullback.lift (pullback.fst u' v ≫ D.hom) (pullback.snd u' v) (by
    rw [Category.assoc, hD]; exact pullback.condition)
  inv := pullback.lift (pullback.fst u v ≫ D.inv) (pullback.snd u v) (by
    rw [Category.assoc, ← hD, Iso.inv_hom_id_assoc]; exact pullback.condition)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- The first projection of `pullbackCongrFst D hD v` is the first projection followed by
`D.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackCongrFst_hom_fst (D : A ≅ B) (hD : D.hom ≫ u = u') (v : T ⟶ E) :
    (pullbackCongrFst D hD v).hom ≫ pullback.fst u v = pullback.fst u' v ≫ D.hom :=
  pullback.lift_fst _ _ _

/-- `pullbackCongrFst D hD v` preserves the second projection. -/
@[reassoc (attr := simp)]
theorem pullbackCongrFst_hom_snd (D : A ≅ B) (hD : D.hom ≫ u = u') (v : T ⟶ E) :
    (pullbackCongrFst D hD v).hom ≫ pullback.snd u v = pullback.snd u' v :=
  pullback.lift_snd _ _ _

end Reindex

/-! ### The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` -/

section FibreToExterior

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ X)

/-- Over the base, `Y ×_S Z ⟶ X ×_S X` followed by the structure morphism of `X ×_S X` is the
structure morphism of `Y ×_S Z`. This is
`Stacks.Chow.exteriorToSelfProduct_comp_selfProductStructure` read over a bare base scheme. -/
@[reassoc]
theorem exteriorToSelfProductMap_comp_base :
    exteriorToSelfProductMap sX a b ≫ (pullback.fst sX sX ≫ sX) =
      pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX) := by
  rw [← Category.assoc, pullback.lift_fst, Category.assoc]

/-- The diagonal is a morphism over the base. -/
@[reassoc]
theorem diagonal_comp_base : pullback.diagonal sX ≫ (pullback.fst sX sX ≫ sX) = sX := by
  rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]

/-- The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` from the fibre product over `X` to the fibre
product over the base. -/
def fibreProductToExteriorProduct :
    (pullback a b : Scheme.{u}) ⟶ (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u}) :=
  pullback.map a b (a ≫ sX) (b ≫ sX) (𝟙 Y) (𝟙 Z) sX (by simp) (by simp)

/-- The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` preserves the first projection. -/
@[reassoc (attr := simp)]
theorem fibreProductToExteriorProduct_fst :
    fibreProductToExteriorProduct sX a b ≫ pullback.fst (a ≫ sX) (b ≫ sX) =
      pullback.fst a b := by
  simp [fibreProductToExteriorProduct]

/-- The canonical morphism `Y ×_X Z ⟶ Y ×_S Z` preserves the second projection. -/
@[reassoc (attr := simp)]
theorem fibreProductToExteriorProduct_snd :
    fibreProductToExteriorProduct sX a b ≫ pullback.snd (a ≫ sX) (b ≫ sX) =
      pullback.snd a b := by
  simp [fibreProductToExteriorProduct]

/-- The structure morphism of `Y ×_S Z` over the base restricts along `Y ×_X Z ⟶ Y ×_S Z` to the
structure morphism of `Y ×_X Z`. -/
@[reassoc]
theorem fibreProductToExteriorProduct_comp_structure :
    fibreProductToExteriorProduct sX a b ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) =
      pullback.fst a b ≫ (a ≫ sX) := by
  rw [← Category.assoc, fibreProductToExteriorProduct_fst]

/-- The second projection of the pullback of the diagonal along `Y ×_S Z ⟶ X ×_S X` carries the
structure morphism of `Y ×_S Z` to the structure morphism of that pullback. -/
@[reassoc]
theorem pullbackDiagonal_snd_comp_structure :
    pullback.snd (pullback.diagonal sX) (exteriorToSelfProductMap sX a b) ≫
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) =
      pullback.fst (pullback.diagonal sX) (exteriorToSelfProductMap sX a b) ≫ sX := by
  rw [← exteriorToSelfProductMap_comp_base sX a b, ← Category.assoc,
    ← pullback.condition (f := pullback.diagonal sX)
      (g := exteriorToSelfProductMap sX a b), Category.assoc, diagonal_comp_base]

/-- The identification `(Y ×_S Z) ×_{X ×_S X} X ≅ Y ×_X Z` of
`CategoryTheory.Limits.pullbackDiagonalMapIdIso` carries the canonical morphism
`Y ×_X Z ⟶ Y ×_S Z` to the second projection of the pullback of the diagonal. -/
@[reassoc]
theorem pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct :
    (pullbackDiagonalMapIdIso a b sX).hom ≫ fibreProductToExteriorProduct sX a b =
      pullback.snd (pullback.diagonal sX) (exteriorToSelfProductMap sX a b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreProductToExteriorProduct_fst, pullbackDiagonalMapIdIso_hom_fst]
  · rw [Category.assoc, fibreProductToExteriorProduct_snd, pullbackDiagonalMapIdIso_hom_snd]

/-- The identification of `CategoryTheory.Limits.pullbackDiagonalMapIdIso` is a morphism over the
base: it carries the structure morphism of `Y ×_X Z` to the structure morphism of the pullback of
the diagonal. This is
`Stacks.Chow.pullbackDiagonalMapIdIso_hom_comp_structure` read over a bare base scheme. -/
@[reassoc]
theorem pullbackDiagonalMapIdIso_hom_comp_base :
    (pullbackDiagonalMapIdIso a b sX).hom ≫ (pullback.fst a b ≫ (a ≫ sX)) =
      pullback.fst (pullback.diagonal sX) (exteriorToSelfProductMap sX a b) ≫ sX := by
  rw [← fibreProductToExteriorProduct_comp_structure sX a b, ← Category.assoc,
    pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct,
    pullbackDiagonal_snd_comp_structure]

end FibreToExterior

/-! ### The substrate identification -/

section Substrate

variable {S X Y Z T : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ X)

/-- **The substrate identification of Stacks 0FC1.** Let `a : Y ⟶ X` and `b : Z ⟶ X` be
morphisms over a base `S` and let `r : T ⟶ Y ×_S Z` be arbitrary. Then the pullback of the
diagonal `X ⟶ X ×_S X` along `T ⟶ Y ×_S Z ⟶ X ×_S X` is the fibre product of `r` with the
canonical morphism `Y ×_X Z ⟶ Y ×_S Z`:

`T ×_{X ×_S X} X ≅ (Y ×_X Z) ×_{Y ×_S Z} T`.

Taking `T` to be a triple product and `r` one of its two projections, the right-hand side is
`(Y ×_X Z) ×_S W`, which is what the proof of Stacks 0FC1 needs: it is the scheme the first
Gysin pullback of the chain lands on, and the scheme the second one is capped against. -/
def pullbackDiagonalExteriorTestIso
    (r : T ⟶ (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u})) :
    (pullback (pullback.diagonal sX) (r ≫ exteriorToSelfProductMap sX a b) : Scheme.{u}) ≅
      (pullback (fibreProductToExteriorProduct sX a b) r : Scheme.{u}) :=
  (pullbackLeftPullbackSndIso (pullback.diagonal sX) (exteriorToSelfProductMap sX a b) r).symm ≪≫
    pullbackCongrFst (pullbackDiagonalMapIdIso a b sX)
      (pullbackDiagonalMapIdIso_hom_comp_fibreProductToExteriorProduct sX a b) r

/-- `pullbackDiagonalExteriorTestIso` carries the second projection to `T` to the second
projection of the pullback of the diagonal. -/
@[reassoc (attr := simp)]
theorem pullbackDiagonalExteriorTestIso_hom_snd
    (r : T ⟶ (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u})) :
    (pullbackDiagonalExteriorTestIso sX a b r).hom ≫
        pullback.snd (fibreProductToExteriorProduct sX a b) r =
      pullback.snd (pullback.diagonal sX) (r ≫ exteriorToSelfProductMap sX a b) := by
  simp [pullbackDiagonalExteriorTestIso]

/-- The first projection of the substrate identification, followed by the canonical morphism
`Y ×_X Z ⟶ Y ×_S Z`, is the second projection of the pullback of the diagonal followed by the
test morphism. -/
@[reassoc]
theorem pullbackDiagonalExteriorTestIso_hom_fst_comp
    (r : T ⟶ (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u})) :
    (pullbackDiagonalExteriorTestIso sX a b r).hom ≫
        (pullback.fst (fibreProductToExteriorProduct sX a b) r ≫
          fibreProductToExteriorProduct sX a b) =
      pullback.snd (pullback.diagonal sX) (r ≫ exteriorToSelfProductMap sX a b) ≫ r := by
  rw [pullback.condition (f := fibreProductToExteriorProduct sX a b) (g := r), ← Category.assoc,
    pullbackDiagonalExteriorTestIso_hom_snd]

/-- `pullbackDiagonalExteriorTestIso` is a morphism over the base: it carries the structure
morphism of `(Y ×_X Z) ×_{Y ×_S Z} T` to the structure morphism of the pullback of the diagonal. -/
@[reassoc]
theorem pullbackDiagonalExteriorTestIso_hom_fst
    (r : T ⟶ (pullback (a ≫ sX) (b ≫ sX) : Scheme.{u})) :
    (pullbackDiagonalExteriorTestIso sX a b r).hom ≫
        (pullback.fst (fibreProductToExteriorProduct sX a b) r ≫
          (pullback.fst a b ≫ (a ≫ sX))) =
      pullback.fst (pullback.diagonal sX) (r ≫ exteriorToSelfProductMap sX a b) ≫ sX := by
  simp only [pullbackDiagonalExteriorTestIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackCongrFst_hom_fst_assoc, pullbackDiagonalMapIdIso_hom_comp_base,
    pullbackLeftPullbackSndIso_inv_fst_assoc]

end Substrate

/-! ### The two factorwise diagonals of a triple product -/

section Triple

variable {S X Y Z W : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X) (b : Z ⟶ X) (g : W ⟶ X)

/-- The test morphism `(Y ×_S Z) ×_S W ⟶ X ×_S X` remembering the first two factors. This is the
source's `Δ₁₂` read as a test morphism of the triple product: capping the degree-`d` Gysin class
of the diagonal of `X` against it is the operation the source writes `Δ₁₂^! ∩ -`, so no triple
self-product `X ×_S X ×_S X` is needed. -/
abbrev firstPartialDiagonalTest :
    (pullback (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) : Scheme.{u}) ⟶
      (pullback sX sX : Scheme.{u}) :=
  pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
    exteriorToSelfProductMap sX a b

/-- The test morphism `Y ×_S (Z ×_S W) ⟶ X ×_S X` remembering the last two factors, the source's
`Δ₂₃`. -/
abbrev secondPartialDiagonalTest :
    (pullback (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) : Scheme.{u}) ⟶
      (pullback sX sX : Scheme.{u}) :=
  pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫
    exteriorToSelfProductMap sX b g

/-- `Δ₂₃` read on the left-bracketed triple product, through the associator. Both factorwise
diagonals are then test morphisms of one and the same scheme, which is what lets the two
composites of the second step of the proof of Stacks 0FC1 be compared. -/
abbrev secondPartialDiagonalTestLeft :
    (pullback (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) : Scheme.{u}) ⟶
      (pullback sX sX : Scheme.{u}) :=
  (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom ≫ secondPartialDiagonalTest sX a b g

/-- **The substrate identification at `Δ₁₂`.** The pullback of the diagonal of `X` along the
test morphism `Δ₁₂` of the left-bracketed triple product is `(Y ×_X Z) ×_S W`. -/
def firstPartialDiagonalPullbackIso :
    (pullback (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) : Scheme.{u}) ≅
      (pullback ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) : Scheme.{u}) :=
  pullbackDiagonalExteriorTestIso sX a b
      (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX)) ≪≫
    pullbackRightPullbackFstIso (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX)
      (fibreProductToExteriorProduct sX a b) ≪≫
    pullback.congrHom
      (by rw [fibreProductToExteriorProduct_comp_structure, Category.assoc]) rfl

/-- **The substrate identification at `Δ₂₃`.** The pullback of the diagonal of `X` along the
test morphism `Δ₂₃` of the right-bracketed triple product is `Y ×_S (Z ×_X W)`. -/
def secondPartialDiagonalPullbackIso :
    (pullback (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) : Scheme.{u}) ≅
      (pullback (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) : Scheme.{u}) :=
  pullbackDiagonalExteriorTestIso sX b g
      (pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX))) ≪≫
    pullbackSymmetry _ _ ≪≫
    pullbackLeftPullbackSndIso (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX))
      (fibreProductToExteriorProduct sX b g) ≪≫
    pullback.congrHom rfl
      (by rw [fibreProductToExteriorProduct_comp_structure, Category.assoc])

/-- The first projection of `firstPartialDiagonalPullbackIso` to `Y ×_X Z`, followed by the
canonical morphism to `Y ×_S Z`, is the projection of the pullback of the diagonal to the
left-bracketed triple product followed by its first projection. -/
@[reassoc]
theorem firstPartialDiagonalPullbackIso_hom_fst :
    (firstPartialDiagonalPullbackIso sX a b g).hom ≫
        (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫
          fibreProductToExteriorProduct sX a b) =
      pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) := by
  rw [firstPartialDiagonalPullbackIso]
  simp only [Iso.trans_hom, pullback.congrHom_hom, pullback.map, Category.assoc,
    Category.comp_id, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc]
  exact pullbackDiagonalExteriorTestIso_hom_fst_comp sX a b _

/-- The projection of `firstPartialDiagonalPullbackIso` to `W` is the projection of the pullback
of the diagonal to the left-bracketed triple product followed by its second projection. -/
@[reassoc]
theorem firstPartialDiagonalPullbackIso_hom_snd :
    (firstPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.snd ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) =
      pullback.snd (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫
        pullback.snd (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) := by
  rw [firstPartialDiagonalPullbackIso]
  simp only [Iso.trans_hom, pullback.congrHom_hom, pullback.map, Category.assoc,
    Category.comp_id, pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd,
    pullbackDiagonalExteriorTestIso_hom_snd_assoc]

/-- The second projection of `secondPartialDiagonalPullbackIso` to `Z ×_X W`, followed by the
canonical morphism to `Z ×_S W`, is the projection of the pullback of the diagonal to the
right-bracketed triple product followed by its second projection. -/
@[reassoc]
theorem secondPartialDiagonalPullbackIso_hom_snd :
    (secondPartialDiagonalPullbackIso sX a b g).hom ≫
        (pullback.snd (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫
          fibreProductToExteriorProduct sX b g) =
      pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫
        pullback.snd (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) := by
  rw [secondPartialDiagonalPullbackIso]
  simp only [Iso.trans_hom, pullback.congrHom_hom, pullback.map, Category.assoc,
    Category.comp_id, pullback.lift_snd_assoc, pullbackLeftPullbackSndIso_hom_snd_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  exact pullbackDiagonalExteriorTestIso_hom_fst_comp sX b g _

/-- The projection of `secondPartialDiagonalPullbackIso` to `Y` is the projection of the pullback
of the diagonal to the right-bracketed triple product followed by its first projection. -/
@[reassoc]
theorem secondPartialDiagonalPullbackIso_hom_fst :
    (secondPartialDiagonalPullbackIso sX a b g).hom ≫
        pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) =
      pullback.snd (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫
        pullback.fst (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) := by
  rw [secondPartialDiagonalPullbackIso]
  simp only [Iso.trans_hom, pullback.congrHom_hom, pullback.map, Category.assoc,
    Category.comp_id, pullback.lift_fst, pullbackLeftPullbackSndIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackDiagonalExteriorTestIso_hom_snd_assoc]

/-! ### The structure morphisms of the two factorwise diagonals -/

/-- Pulling back the diagonal along `t`, the second projection followed by `t` is a morphism over
the base. -/
private theorem pullbackDiagonal_snd_comp_base {T : Scheme.{u}}
    (t : T ⟶ (pullback sX sX : Scheme.{u})) :
    pullback.snd (pullback.diagonal sX) t ≫ t ≫ (pullback.fst sX sX ≫ sX) =
      pullback.fst (pullback.diagonal sX) t ≫ sX := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, diagonal_comp_base]

/-- `Δ₁₂` is a morphism over the base, from the left-bracketed triple product. -/
@[reassoc]
theorem firstPartialDiagonalTest_comp_base :
    firstPartialDiagonalTest sX a b g ≫ (pullback.fst sX sX ≫ sX) =
      pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) := by
  rw [Category.assoc, exteriorToSelfProductMap_comp_base]

/-- `Δ₂₃` is a morphism over the base, from the right-bracketed triple product. -/
@[reassoc]
theorem secondPartialDiagonalTest_comp_base :
    secondPartialDiagonalTest sX a b g ≫ (pullback.fst sX sX ≫ sX) =
      pullback.fst (a ≫ sX) (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX) := by
  rw [Category.assoc, exteriorToSelfProductMap_comp_base, ← pullback.condition]

/-- `Δ₂₃` read on the left-bracketed triple product is a morphism over the base. -/
@[reassoc]
theorem secondPartialDiagonalTestLeft_comp_base :
    secondPartialDiagonalTestLeft sX a b g ≫ (pullback.fst sX sX ≫ sX) =
      pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) := by
  rw [Category.assoc, secondPartialDiagonalTest_comp_base, tripleProductAssoc_hom_comp_base]

/-- The substrate identification at `Δ₁₂` is a morphism over the base, so Chow classes may be
pushed forward along it. -/
@[reassoc]
theorem firstPartialDiagonalPullbackIso_hom_comp_base :
    (firstPartialDiagonalPullbackIso sX a b g).hom ≫
        (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫
          ((pullback.fst a b ≫ a) ≫ sX)) =
      pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX := by
  have h := firstPartialDiagonalPullbackIso_hom_fst_assoc sX a b g
    (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
  simp only [Category.assoc, fibreProductToExteriorProduct_comp_structure] at h ⊢
  rw [h, ← pullbackDiagonal_snd_comp_base sX (firstPartialDiagonalTest sX a b g),
    firstPartialDiagonalTest_comp_base]

/-- The substrate identification at `Δ₂₃` is a morphism over the base. -/
@[reassoc]
theorem secondPartialDiagonalPullbackIso_hom_comp_base :
    (secondPartialDiagonalPullbackIso sX a b g).hom ≫
        (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX)) =
      pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫ sX := by
  rw [secondPartialDiagonalPullbackIso_hom_fst_assoc, ← secondPartialDiagonalTest_comp_base,
    pullbackDiagonal_snd_comp_base]

end Triple

/-! ### The three steps of the source's chain -/

section Chain

variable (k : Type u) [Field k] (G : GysinSystem (fieldChowSituation k))
  (hpp : ProperPushforwardDescends (fieldChowSituation k))
  {X Y Z W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
  (a : Y ⟶ X) [LocallyOfFiniteType a] (b : Z ⟶ X) [LocallyOfFiniteType b]
  (g : W ⟶ X) [LocallyOfFiniteType g] (d : ℤ)
  (Dc : BivariantClass (fieldChowSituation k) G sX
    (selfProductStructure (fieldChowSituation k) sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) d)
  (n m l : ℤ)

/-- **Stacks 0FBY in the first variable of the exterior product**, at the Gysin class of the
diagonal. Capping a class `ξ` on `Y ×_k Z` with `Δ^!` — which lands it on `Y ×_X Z` — and then
taking the exterior product with a class `γ` on `W` is the same as taking the exterior product
first and capping the result on `Y ×_k Z ×_k W` with `Δ^!` against the test morphism `Δ₁₂`, the
two sides being compared by the substrate identification
`Stacks.Chow.firstPartialDiagonalPullbackIso`.

This is the source's first step. It is a statement about **one** bivariant class and the exterior
product, quantified over every `ξ` and `γ`: it mentions neither a second cap operation, nor three
Chow classes, nor the associator, and so it is not the conclusion of Stacks 0FC1 in disguise.

The only carrier of Stacks 0FBY in this repository is the fundamental-class special case,
`Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass` of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting`, whose own key records that it
is
"NOT for a general `α ∈ CH_n(X)`": its first factor is the fundamental class of an integral scheme
flat over the base. The class the first step below needs there is the exterior product `α × β`,
which is not of that shape, and the carried case is in the second variable besides. The general
case is unavailable, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting` record why: making
`β ↦ α × β` a `Stacks.Chow.BivariantClass` needs all three conditions of Stacks 0B76 for the
exterior product and none of them is available. Besides Stacks 0FBY itself the first step
also uses condition (1) of Stacks 0B76 for the exterior product, to move the pushforward along
`(Y ×_k Z) ×_{X ×_k X} X ≅ Y ×_X Z` out through `× γ`; that too has no carrier, and it is why the
left-hand side below displays that pushforward explicitly. -/
def CommutesDiagonalCapExteriorFirst : Prop :=
  ∀ (xi : chowGroup (fieldChowSituation k)
      (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (n + m))
    (gamma : chowGroup (fieldChowSituation k) (g ≫ sX) l),
    (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
        ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) (n + m - d) l)
      ((chowGroupCongr (fieldChowSituation k) (Category.assoc (pullback.fst a b) a sX).symm
            (n + m - d))
          ((properChowPushforward (fieldChowSituation k)
              (pullback.fst (pullback.diagonal sX)
                (exteriorToSelfProduct (fieldChowSituation k) sX a b) ≫ sX)
              (pullback.fst a b ≫ (a ≫ sX)) (pullbackDiagonalMapIdIso a b sX).hom
              (pullbackDiagonalMapIdIso_hom_comp_structure (fieldChowSituation k) sX a b)
              (n + m - d) (hpp _ _ _ _ _))
            ((Dc.cap (exteriorToSelfProduct (fieldChowSituation k) sX a b) (n + m))
              ((chowGroupCongr (fieldChowSituation k)
                  (exteriorToSelfProduct_comp_selfProductStructure
                    (fieldChowSituation k) sX a b).symm (n + m)).toAddMonoidHom xi)))
        ⊗ₜ[ℤ] gamma) =
      (chowPushforwardOfIso (fieldChowSituation k)
          (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
          (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫
            ((pullback.fst a b ≫ a) ≫ sX))
          (firstPartialDiagonalPullbackIso sX a b g).hom
          (firstPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + m - d + l))
        ((chowGroupDegreeEquiv (fieldChowSituation k)
            (pullback.fst (pullback.diagonal sX) (firstPartialDiagonalTest sX a b g) ≫ sX)
            (by ring : n + m + l - d = n + m - d + l))
          ((Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l))
            ((chowGroupCongr (fieldChowSituation k)
                (firstPartialDiagonalTest_comp_base sX a b g).symm
                (n + m + l)).toAddMonoidHom
              ((chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
                  (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) (n + m) l)
                (xi ⊗ₜ[ℤ] gamma)))))

/-- **Stacks 0FBY in the second variable of the exterior product**, at the Gysin class of the
diagonal: the exterior product of `α` with `Δ^!(η)` is `Δ^!` capped against the test morphism
`Δ₂₃` of `Y ×_k Z ×_k W`, read through the substrate identification
`Stacks.Chow.secondPartialDiagonalPullbackIso`.

This is the source's penultimate step, and it is Stacks 0FBY as the source states it. The
repository's notion of the exterior product is second-variable only — there is no Chow-level
symmetry of `Stacks.Chow.chowExteriorProduct`, the one symmetry statement being the coefficient
level `Stacks.Chow.exteriorProductCoeff_pullbackSymmetry` — so this does not follow from
`Stacks.Chow.CommutesDiagonalCapExteriorFirst` and is carried separately. Like that one it
mentions one bivariant class and the exterior product only, and like that one it is not covered by
the repository's single carrier of Stacks 0FBY,
`Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass`, which asks that the first factor
be the fundamental class of an integral scheme flat over the base; here it is an arbitrary
`α ∈ CH_n(Y)`. -/
def CommutesDiagonalCapExteriorSecond : Prop :=
  ∀ (alpha : chowGroup (fieldChowSituation k) (a ≫ sX) n)
    (eta : chowGroup (fieldChowSituation k)
      (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) (m + l)),
    (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) (a ≫ sX)
        ((pullback.fst b g ≫ b) ≫ sX) n (m + l - d))
      (alpha ⊗ₜ[ℤ]
        (chowGroupCongr (fieldChowSituation k) (Category.assoc (pullback.fst b g) b sX).symm
            (m + l - d))
          ((properChowPushforward (fieldChowSituation k)
              (pullback.fst (pullback.diagonal sX)
                (exteriorToSelfProduct (fieldChowSituation k) sX b g) ≫ sX)
              (pullback.fst b g ≫ (b ≫ sX)) (pullbackDiagonalMapIdIso b g sX).hom
              (pullbackDiagonalMapIdIso_hom_comp_structure (fieldChowSituation k) sX b g)
              (m + l - d) (hpp _ _ _ _ _))
            ((Dc.cap (exteriorToSelfProduct (fieldChowSituation k) sX b g) (m + l))
              ((chowGroupCongr (fieldChowSituation k)
                  (exteriorToSelfProduct_comp_selfProductStructure
                    (fieldChowSituation k) sX b g).symm (m + l)).toAddMonoidHom eta)))) =
      (chowPushforwardOfIso (fieldChowSituation k)
          (pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫ sX)
          (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX))
          (secondPartialDiagonalPullbackIso sX a b g).hom
          (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + (m + l - d)))
        ((chowGroupDegreeEquiv (fieldChowSituation k)
            (pullback.fst (pullback.diagonal sX) (secondPartialDiagonalTest sX a b g) ≫ sX)
            (by ring : n + (m + l) - d = n + (m + l - d)))
          ((Dc.cap (secondPartialDiagonalTest sX a b g) (n + (m + l)))
            ((chowGroupCongr (fieldChowSituation k)
                (secondPartialDiagonalTest_comp_base sX a b g).symm
                (n + (m + l))).toAddMonoidHom
              ((chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) (a ≫ sX)
                  (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) n (m + l))
                (alpha ⊗ₜ[ℤ] eta)))))

/-- **Stacks 0FBP for the Gysin class of the diagonal**, in the instance the proof of Stacks 0FC1
consumes: the two orders in which `Δ^!` may be capped against the two factorwise diagonals
`Δ₁₂` and `Δ₂₃` of one triple product agree, after the transports that carry the two results into
the Chow group of `Y ×_X (Z ×_X W)`.

This is a statement about **one** bivariant class, the two factorwise diagonals and **one**
arbitrary class `x` on the triple product. It mentions no exterior product, no three Chow
classes and no product operation, so it is not the conclusion of Stacks 0FC1 in disguise. It is
Stacks 0FBP: the Gysin class of a closed subscheme commutes with every bivariant class, here with
itself along the two legs. The repository's carriers of that tag,
`Stacks.Chow.virtualNormalGysinClass_bivariantCommute` and its two sharper forms in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommuting`, prove exactly this shape —
`Stacks.Chow.BivariantCommute` of Stacks 0FA2 — for a `Stacks.Chow.virtualNormalGysinClass`; what
is missing in order to apply them to `Δ^!` restricted along the two legs is Stacks 0FBJ, the
base-change compatibility of Gysin maps, which would identify such a restriction (Stacks 0F9Z,
`Stacks.Chow.bivariantRestriction`) with the Gysin class of the base-changed diagonal.

Stacks 0FBJ is carried in this repository, but only at the level of sheaves: the carrier is
`Stacks.Chow.VirtualNormalBundle.baseChange` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange`, which says
that the pullback of a virtual normal bundle is a virtual normal bundle for the base-changed
immersion. The half that is needed here is the one about *classes*, that the Gysin class of the
base change is the restriction of the Gysin class, and that has no carrier: no module in this
repository mentions `Stacks.Chow.virtualNormalGysinClass` and `Stacks.Chow.bivariantRestriction`
together. A second obstruction is presentational — `Stacks.Chow.bivariantRestriction` produces a
class whose structure morphisms are `pullback.fst f h ≫ sX` and `h ≫ sY`, where
`Stacks.Chow.BivariantCommute` asks for `i ≫ sX` and `sX` with the coherence proof `rfl`, and
nothing here transports a `Stacks.Chow.BivariantClass` between two presentations of the same
morphism. -/
def DiagonalGysinCommuteOnTripleProduct : Prop :=
  ∀ x : chowGroup (fieldChowSituation k)
      (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)) (g ≫ sX) ≫
        (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))) (n + m + l),
    (chowGroupDegreeEquiv (fieldChowSituation k)
        (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
        (intersectionProductAssocDegree n m l d))
      ((properChowPushforward (fieldChowSituation k)
          (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
          (tripleProductAssoc a b g).hom
          (tripleProductAssoc_hom_comp_structureMorphism (fieldChowSituation k) sX a b g)
          (n + m - d + l - d) (hpp _ _ _ _ _))
        ((properChowPushforward (fieldChowSituation k)
            (pullback.fst (pullback.diagonal sX)
              (exteriorToSelfProduct (fieldChowSituation k) sX (pullback.fst a b ≫ a) g) ≫ sX)
            (pullback.fst (pullback.fst a b ≫ a) g ≫ ((pullback.fst a b ≫ a) ≫ sX))
            (pullbackDiagonalMapIdIso (pullback.fst a b ≫ a) g sX).hom
            (pullbackDiagonalMapIdIso_hom_comp_structure (fieldChowSituation k) sX
              (pullback.fst a b ≫ a) g) (n + m - d + l - d) (hpp _ _ _ _ _))
          ((Dc.cap (exteriorToSelfProduct (fieldChowSituation k) sX (pullback.fst a b ≫ a) g)
              (n + m - d + l))
            ((chowGroupCongr (fieldChowSituation k)
                (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sX
                  (pullback.fst a b ≫ a) g).symm (n + m - d + l)).toAddMonoidHom
              ((chowPushforwardOfIso (fieldChowSituation k)
                  (pullback.fst (pullback.diagonal sX)
                    (firstPartialDiagonalTest sX a b g) ≫ sX)
                  (pullback.fst ((pullback.fst a b ≫ a) ≫ sX) (g ≫ sX) ≫
                    ((pullback.fst a b ≫ a) ≫ sX))
                  (firstPartialDiagonalPullbackIso sX a b g).hom
                  (firstPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + m - d + l))
                ((chowGroupDegreeEquiv (fieldChowSituation k)
                    (pullback.fst (pullback.diagonal sX)
                      (firstPartialDiagonalTest sX a b g) ≫ sX)
                    (by ring : n + m + l - d = n + m - d + l))
                  ((Dc.cap (firstPartialDiagonalTest sX a b g) (n + m + l))
                    ((chowGroupCongr (fieldChowSituation k)
                        (firstPartialDiagonalTest_comp_base sX a b g).symm
                        (n + m + l)).toAddMonoidHom x)))))))) =
      (properChowPushforward (fieldChowSituation k)
          (pullback.fst (pullback.diagonal sX)
            (exteriorToSelfProduct (fieldChowSituation k) sX a (pullback.fst b g ≫ b)) ≫ sX)
          (pullback.fst a (pullback.fst b g ≫ b) ≫ (a ≫ sX))
          (pullbackDiagonalMapIdIso a (pullback.fst b g ≫ b) sX).hom
          (pullbackDiagonalMapIdIso_hom_comp_structure (fieldChowSituation k) sX a
            (pullback.fst b g ≫ b)) (n + (m + l - d) - d) (hpp _ _ _ _ _))
        ((Dc.cap (exteriorToSelfProduct (fieldChowSituation k) sX a (pullback.fst b g ≫ b))
            (n + (m + l - d)))
          ((chowGroupCongr (fieldChowSituation k)
              (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sX a
                (pullback.fst b g ≫ b)).symm (n + (m + l - d))).toAddMonoidHom
            ((chowPushforwardOfIso (fieldChowSituation k)
                (pullback.fst (pullback.diagonal sX)
                  (secondPartialDiagonalTest sX a b g) ≫ sX)
                (pullback.fst (a ≫ sX) ((pullback.fst b g ≫ b) ≫ sX) ≫ (a ≫ sX))
                (secondPartialDiagonalPullbackIso sX a b g).hom
                (secondPartialDiagonalPullbackIso_hom_comp_base sX a b g) (n + (m + l - d)))
              ((chowGroupDegreeEquiv (fieldChowSituation k)
                  (pullback.fst (pullback.diagonal sX)
                    (secondPartialDiagonalTest sX a b g) ≫ sX)
                  (by ring : n + (m + l) - d = n + (m + l - d)))
                ((Dc.cap (secondPartialDiagonalTest sX a b g) (n + (m + l)))
                  ((chowGroupCongr (fieldChowSituation k)
                      (secondPartialDiagonalTest_comp_base sX a b g).symm
                      (n + (m + l))).toAddMonoidHom
                    ((chowGroupDegreeEquiv (fieldChowSituation k)
                        (pullback.fst (a ≫ sX)
                          (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                        (add_assoc n m l))
                      ((chowPushforwardOfIso (fieldChowSituation k)
                          (pullback.fst (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX))
                              (g ≫ sX) ≫ (pullback.fst (a ≫ sX) (b ≫ sX) ≫ (a ≫ sX)))
                          (pullback.fst (a ≫ sX)
                            (pullback.fst (b ≫ sX) (g ≫ sX) ≫ (b ≫ sX)) ≫ (a ≫ sX))
                          (tripleProductAssoc (a ≫ sX) (b ≫ sX) (g ≫ sX)).hom
                          (tripleProductAssoc_hom_comp_base (a ≫ sX) (b ≫ sX) (g ≫ sX))
                          (n + m + l))
                        x))))))))

/-- **Stacks Project, Tag 0FC1.** Associativity of the intersection product of Stacks 0FC0: for
`X` a scheme over a field `k` whose diagonal carries a Gysin class `Δ^!` of degree `d`, and `Y`,
`Z`, `W` locally of finite type over `X`,

`(α · β) · γ = α · (β · γ)`   in   `CH_*(Y ×_X Z ×_X W)`,

read through the associator of the triple fibre product over `X` and the matching of the two
degrees, which is `Stacks.Chow.IsAssociativeIntersectionProduct`.

This is the source's chain of five equalities. The two instances of Stacks 0FBY are carried, as
`Stacks.Chow.CommutesDiagonalCapExteriorFirst` and
`Stacks.Chow.CommutesDiagonalCapExteriorSecond` — the repository's one carrier of that tag is the
fundamental-class case and does not cover either of them — and Stacks 0FBP is carried as
`Stacks.Chow.DiagonalGysinCommuteOnTripleProduct`, whose carriers here would apply but for the
class half of Stacks 0FBJ. The docstrings of those three say exactly what they assume and why
none of them is this conclusion. Stacks 0FBZ, associativity of the exterior
product, is **proved** in this repository and is consumed here as
`Stacks.Chow.chowExteriorProduct_assoc`; Stacks 0F9Z is free, the cap operation of
`Stacks.Chow.BivariantClass` being indexed by an arbitrary test morphism, so that `Δ₁₂^!` and
`Δ₂₃^!` are cap operations of `Δ^!` itself and no triple self-product of `X` is needed; and the
fibre-product identification the chain runs on is **proved** above, as
`Stacks.Chow.pullbackDiagonalExteriorTestIso` with its two instances
`Stacks.Chow.firstPartialDiagonalPullbackIso` and
`Stacks.Chow.secondPartialDiagonalPullbackIso`. -/
@[stacks 0FC1 "associativity (α·β)·γ = α·(β·γ) of the Stacks 0FC0 product over a field, via the \
source's five-step chain; 0FBZ comes from this repository and the chain's fibre-product \
identification is proved here; carried are 0FBY in both variables (only its fundamental-class \
case is carried here) and 0FBP (needs the class half of 0FBJ), plus 02S1 and 02S2"]
theorem isAssociativeIntersectionProduct
    (hfirst : CommutesDiagonalCapExteriorFirst k G hpp sX a b g d Dc n m l)
    (hsecond : CommutesDiagonalCapExteriorSecond k G hpp sX a b g d Dc n m l)
    (hcommute : DiagonalGysinCommuteOnTripleProduct k G hpp sX a b g d Dc n m l) :
    IsAssociativeIntersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl) G sX a b g d Dc
      n m l hpp := by
  intro A B C
  simp only [intersectionProductReassoc, intersectionProduct, diagonalGysinProduct,
    AddMonoidHom.coe_comp, Function.comp_apply]
  rw [hfirst _ C, hsecond A _, ← chowExteriorProduct_assoc k (a ≫ sX) (b ≫ sX) (g ≫ sX)
    n m l A B C]
  exact hcommute _

end Chain

end Stacks.Chow

end
