module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.GaloisSelfProduct

/-!
# Base change of smooth projective schemes along a field extension

Let `k'/k` be an extension of fields. For a smooth projective scheme `X` over `k` the base change
`X_{k'} = X ×_{Spec(k)} Spec(k')` is smooth and projective over `k'`, smooth and projective
morphisms being stable under base change, and a morphism `f : X ⟶ Y` over `k` base changes to a
morphism `f_{k'} : X_{k'} ⟶ Y_{k'}` over `k'`. This is the functor on which Lemma 0FVT of the
Stacks Project compares two sets of data (D0), (D1), (D2'): the functorial isomorphisms
`H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` of its hypothesis (3) are natural in `X` along this functor.

The morphism of bases is `Spec(k') ⟶ Spec(k)` of `Stacks.Chow.fieldExtensionBaseChangeSituation`,
so that `X_{k'}` is the scheme on which the base-change map of Chow groups of Lemma 0FVJ lands.

## Main definitions

* `Stacks.WeilDeRham.fieldBaseChange`: the functor `X ↦ X_{k'}` from smooth projective schemes
  over `k` to smooth projective schemes over `k'`.
* `Stacks.WeilDeRham.fieldBaseChangeProj`: the projection `X_{k'} ⟶ X`.

## Main results

* `Stacks.WeilDeRham.isPullback_fieldBaseChangeProj`: `X_{k'}` is the fibre product of `X` and
  `Spec(k')` over `Spec(k)`.
* `Stacks.WeilDeRham.fieldBaseChange_map_comp_proj`: the projections are natural in `X`.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

variable {k k'}

/-- **The base change `X_{k'} = X ×_{Spec(k)} Spec(k')`** of a smooth projective scheme over `k`,
as a smooth projective scheme over `k'`. -/
abbrev fieldBaseChangeObj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (SmoothProjectiveScheme k').FullSubcategory :=
  mk (pullback.snd X.obj.hom (specStructure k k')) inferInstance
    (IsProjective.of_isPullback
      (IsPullback.of_hasPullback X.obj.hom (specStructure k k')).flip (isProjective X))

/-- The base change `f_{k'} : X_{k'} ⟶ Y_{k'}` of a morphism `f : X ⟶ Y` over `k`. -/
def fieldBaseChangeMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    fieldBaseChangeObj (k' := k') X ⟶ fieldBaseChangeObj Y :=
  homMk (pullback.lift (pullback.fst X.obj.hom (specStructure k k') ≫ (toScheme k).map f)
      (pullback.snd X.obj.hom (specStructure k k'))
      ((Category.assoc _ _ _).trans ((congrArg _ (w f)).trans pullback.condition)))
    (pullback.lift_snd _ _ _)

/-- The base change `f_{k'}` followed by the projection `Y_{k'} ⟶ Y` is the projection
`X_{k'} ⟶ X` followed by `f`. -/
theorem fieldBaseChangeMap_fst {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    (toScheme k').map (fieldBaseChangeMap (k' := k') f) ≫
        pullback.fst Y.obj.hom (specStructure k k') =
      pullback.fst X.obj.hom (specStructure k k') ≫ (toScheme k).map f :=
  pullback.lift_fst _ _ _

/-- The base change `f_{k'} : X_{k'} ⟶ Y_{k'}` commutes with the projections to `Spec(k')`. -/
theorem fieldBaseChangeMap_snd {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    (toScheme k').map (fieldBaseChangeMap (k' := k') f) ≫
        pullback.snd Y.obj.hom (specStructure k k') =
      pullback.snd X.obj.hom (specStructure k k') :=
  pullback.lift_snd _ _ _

variable (k k')

/-- **The base change functor `X ↦ X_{k'}`** from smooth projective schemes over `k` to smooth
projective schemes over `k'`. -/
def fieldBaseChange : (SmoothProjectiveScheme k).FullSubcategory ⥤
    (SmoothProjectiveScheme k').FullSubcategory where
  obj X := fieldBaseChangeObj X
  map f := fieldBaseChangeMap f
  map_id X := hom_ext' (pullback.hom_ext
    ((fieldBaseChangeMap_fst (𝟙 X)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    ((fieldBaseChangeMap_snd (𝟙 X)).trans (Category.id_comp _).symm))
  map_comp f g := by
    apply hom_ext'
    apply pullback.hom_ext
    · rw [fieldBaseChangeMap_fst, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        Category.assoc, fieldBaseChangeMap_fst, ← Category.assoc, ← Category.assoc,
        fieldBaseChangeMap_fst]
    · rw [fieldBaseChangeMap_snd, CategoryTheory.Functor.map_comp, Category.assoc,
        fieldBaseChangeMap_snd, fieldBaseChangeMap_snd]

variable {k k'}

/-- The underlying scheme of `X_{k'}` is the fibre product `X ×_{Spec(k)} Spec(k')`. -/
@[simp]
theorem toScheme_obj_fieldBaseChange (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (toScheme k').obj ((fieldBaseChange k k').obj X) =
      pullback X.obj.hom (specStructure k k') :=
  rfl

/-- The structure morphism of `X_{k'}` is the projection `X ×_{Spec(k)} Spec(k') ⟶ Spec(k')`. -/
@[simp]
theorem fieldBaseChange_obj_hom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((fieldBaseChange k k').obj X).obj.hom = pullback.snd X.obj.hom (specStructure k k') :=
  rfl


/-- **The projection `X_{k'} ⟶ X`.** -/
def fieldBaseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (toScheme k').obj ((fieldBaseChange k k').obj X) ⟶ (toScheme k).obj X :=
  pullback.fst X.obj.hom (specStructure k k')

/-- **`X_{k'}` is the fibre product `X ×_{Spec(k)} Spec(k')`**, with the projection to `X` and
its structure morphism to `Spec(k')`. -/
theorem isPullback_fieldBaseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback (fieldBaseChangeProj (k' := k') X) ((fieldBaseChange k k').obj X).obj.hom
      X.obj.hom (specStructure k k') :=
  IsPullback.of_hasPullback X.obj.hom (specStructure k k')

/-- The projection `X_{k'} ⟶ X` lies over `Spec(k') ⟶ Spec(k)`. -/
@[reassoc]
theorem fieldBaseChangeProj_comp_hom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    fieldBaseChangeProj (k' := k') X ≫ X.obj.hom =
      ((fieldBaseChange k k').obj X).obj.hom ≫ specStructure k k' :=
  pullback.condition

/-- **The projections are natural**: `f_{k'}` followed by `Y_{k'} ⟶ Y` is `X_{k'} ⟶ X`
followed by `f`. -/
@[reassoc (attr := simp)]
theorem fieldBaseChange_map_comp_proj {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    (toScheme k').map ((fieldBaseChange k k').map f) ≫ fieldBaseChangeProj Y =
      fieldBaseChangeProj X ≫ (toScheme k).map f :=
  fieldBaseChangeMap_fst f

/-- The square formed by `f`, `f_{k'}` and the two projections is cartesian. -/
theorem isPullback_fieldBaseChange_map {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    IsPullback ((toScheme k').map ((fieldBaseChange k k').map f)) (fieldBaseChangeProj X)
      (fieldBaseChangeProj Y) ((toScheme k).map f) := by
  have h₁ := isPullback_fieldBaseChangeProj (k' := k') Y
  have h₂ := isPullback_fieldBaseChangeProj (k' := k') X
  refine IsPullback.of_right ?_ (fieldBaseChange_map_comp_proj f) h₁.flip
  have : (toScheme k').map ((fieldBaseChange k k').map f) ≫ ((fieldBaseChange k k').obj Y).obj.hom =
      ((fieldBaseChange k k').obj X).obj.hom :=
    w ((fieldBaseChange k k').map f)
  rw [this]
  have hw : (toScheme k).map f ≫ Y.obj.hom = X.obj.hom := w f
  rw [hw]
  exact h₂.flip

end Stacks.WeilDeRham

end
