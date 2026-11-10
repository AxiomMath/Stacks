module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation

/-!
# The pair groupoid on a categorical product and the relation of a groupoid scheme

For an `S`-scheme `U` the groupoid scheme `(U, U ×_S U, pr₁, pr₀, pr₀₂)` has every pair of
points of `U` as an arrow.  The pre-relation `j = (t, s)` of a groupoid scheme with scheme of
objects `U` is the map on arrows of a morphism of groupoid schemes into it which is the
identity on objects.

## Main definitions

* `AlgebraicGeometry.prodPairGroupoid` is the groupoid scheme `(U, U ×_S U, pr₁, pr₀, pr₀₂)`.
* `AlgebraicGeometry.groupoidPreRelationHom` is the morphism of groupoid schemes into it whose
  map on arrows is `AlgebraicGeometry.groupoidPreRelation`.

## Implementation notes

The scheme of arrows is the categorical product `U ⨯ U` in `CategoryTheory.Over S`, which is
the fibre product `U ×_S U`, rather than the fibre product of the underlying schemes used by
`AlgebraicGeometry.pairGroupoid`.  This is the model in which `prod.lift t s`, hence
`AlgebraicGeometry.groupoidPreRelation`, takes its values.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The groupoid scheme `(U, U ×_S U, pr₁, pr₀, pr₀₂)` on an `S`-scheme `U`, in which every
pair of points of `U` is an arrow. -/
noncomputable def prodPairGroupoid (U : Over S) : GroupoidScheme S where
  objects := U
  arrows := U ⨯ U
  source := prod.snd
  target := prod.fst
  comp := prod.lift (pullback.fst prod.snd prod.fst ≫ prod.fst)
    (pullback.snd prod.snd prod.fst ≫ prod.snd)
  identity := diag U
  inverse := (prod.braiding U U).hom
  source_identity := by simp
  target_identity := by simp
  source_inverse := by simp
  target_inverse := by simp
  source_comp := by simp
  target_comp := by simp
  left_identity := by intros; apply prod.hom_ext <;>
    simp
  right_identity := by intros; apply prod.hom_ext <;>
    simp
  left_inverse := by intros; apply prod.hom_ext <;>
    simp
  right_inverse := by intros; apply prod.hom_ext <;>
    simp
  assoc := by intros; apply prod.hom_ext <;>
    simp

/-- The scheme of objects of `prodPairGroupoid U` is `U`. -/
@[simp]
lemma prodPairGroupoid_objects (U : Over S) : (prodPairGroupoid U).objects = U := rfl

/-- The scheme of arrows of `prodPairGroupoid U` is `U ⨯ U`. -/
@[simp]
lemma prodPairGroupoid_arrows (U : Over S) : (prodPairGroupoid U).arrows = (U ⨯ U) := rfl

/-- The source morphism of `prodPairGroupoid U` is the second projection `pr₁`. -/
@[simp]
lemma prodPairGroupoid_source (U : Over S) : (prodPairGroupoid U).source = prod.snd := rfl

/-- The target morphism of `prodPairGroupoid U` is the first projection `pr₀`. -/
@[simp]
lemma prodPairGroupoid_target (U : Over S) : (prodPairGroupoid U).target = prod.fst := rfl

/-- The composition of `prodPairGroupoid U` is `pr₀₂`, sending `((a, b), (b, c))` to `(a, c)`. -/
@[simp]
lemma prodPairGroupoid_comp (U : Over S) :
    (prodPairGroupoid U).comp = prod.lift (pullback.fst prod.snd prod.fst ≫ prod.fst)
      (pullback.snd prod.snd prod.fst ≫ prod.snd) := rfl

/-- The identity of `prodPairGroupoid U` is the diagonal `U ⟶ U ⨯ U`. -/
@[simp]
lemma prodPairGroupoid_identity (U : Over S) : (prodPairGroupoid U).identity = diag U := rfl

/-- The inverse of `prodPairGroupoid U` is the braiding `U ⨯ U ≅ U ⨯ U`. -/
@[simp]
lemma prodPairGroupoid_inverse (U : Over S) :
    (prodPairGroupoid U).inverse = (prod.braiding U U).hom := rfl

/-- The pre-relation `j = (t, s)` of a groupoid scheme, as the map on arrows of a morphism of
groupoid schemes into the pair groupoid on its scheme of objects which is the identity on
objects. -/
noncomputable def groupoidPreRelationHom (G : GroupoidScheme S) :
    GroupoidScheme.Hom G (prodPairGroupoid G.objects) where
  mapObjects := 𝟙 _
  mapArrows := prod.lift G.target G.source
  map_source := by simp [prodPairGroupoid]
  map_target := by simp [prodPairGroupoid]
  map_identity := by
    apply prod.hom_ext <;>
      simp [prodPairGroupoid, G.target_identity, G.source_identity]
  map_comp := by
    intros
    dsimp only [prodPairGroupoid, GroupoidScheme.compose]
    apply prod.hom_ext <;>
      simp [G.target_comp, G.source_comp]

/-- The map on objects of `groupoidPreRelationHom G` is the identity of `G.objects`. -/
@[simp]
lemma groupoidPreRelationHom_mapObjects (G : GroupoidScheme S) :
    (groupoidPreRelationHom G).mapObjects = 𝟙 G.objects := rfl

/-- The map on arrows of `groupoidPreRelationHom G` is `groupoidPreRelation G`. -/
@[simp]
lemma groupoidPreRelationHom_mapArrows (G : GroupoidScheme S) :
    (groupoidPreRelationHom G).mapArrows = groupoidPreRelation G := rfl

end AlgebraicGeometry

end
