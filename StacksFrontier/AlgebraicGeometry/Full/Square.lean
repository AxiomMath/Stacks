module

public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.OverSquare

/-!
# Transporting a pair of base-changed morphisms across a base-change square

Let
```
V --v--> L
|        |
q        p
↓        ↓
U --u--> S
```
be a commutative square in a category with pullbacks, and let `X Y : Over S`.  A morphism
`φ` between the base changes of `X` and `Y` along `u`, and a morphism `ψ` between their base
changes along `p`, are *compatible* when their further base changes to `V` agree through the
comparison isomorphism `CategoryTheory.Over.pullbackSquareObjIso`.  This file records the two
consequences of that compatibility which are needed to glue `φ` and `ψ` into a single morphism
`X ⟶ Y` by descent.

The first, `CategoryTheory.Over.pullbackSquare_fst_comp_left`, says that the two ways of
reaching `Y` from the iterated base change `V ×_U (U ×_S X)` — restrict with `φ`, or cross the
comparison and restrict with `ψ` — agree.  This is the equality a descent argument must verify
on the overlap of two members of a covering family.

The second, `CategoryTheory.Over.pullbackSquareObjIso_lift_fst`, identifies the composite of
the comparison isomorphism with the projection to `L ×_S X`: a map into the iterated base
change built from a map to `U ×_S X` and a map to `V` is carried to the map into `L ×_S X`
with the expected components.  This is what turns a pair of maps into the two members of the
covering family into a single map into the overlap.

## Main results

* `CategoryTheory.Limits.comp_pullback_snd_comp`
* `CategoryTheory.Over.pullback_map_left_comp_fst`
* `CategoryTheory.Over.pullbackSquare_fst_comp_left`
* `CategoryTheory.Over.pullbackSquareObjIso_lift_fst`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A morphism into a pullback composed down to the common target, computed through either
projection. -/
theorem comp_pullback_snd_comp {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (k : W ⟶ pullback f g) :
    (k ≫ pullback.snd f g) ≫ g = (k ≫ pullback.fst f g) ≫ f := by
  rw [Category.assoc, Category.assoc, pullback.condition]

end CategoryTheory.Limits

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {S U L V : C} {u : U ⟶ S} {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U}

/-- The first projection of a base change intertwines a morphism of `Over S` with its base
change. -/
theorem pullback_map_left_comp_fst {T T' : C} (r : T ⟶ T') {X Y : Over T'} (f : X ⟶ Y) :
    ((Over.pullback r).map f).left ≫ pullback.fst Y.hom r =
      pullback.fst X.hom r ≫ f.left := by
  simp [Over.pullback_map_left]

/-- **The overlap equation for a compatible pair of base-changed morphisms.**  If `φ` and `ψ`
base-change `X ⟶ Y` along `u` and along `p` respectively, and their further base changes to `V`
agree through the comparison isomorphism of the square `q ≫ u = v ≫ p`, then restricting with
`φ` and crossing the comparison to restrict with `ψ` give the same morphism from the iterated
base change down to `Y`. -/
theorem pullbackSquare_fst_comp_left (w : q ≫ u = v ≫ p) {X Y : Over S}
    (φ : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Y)
    (ψ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (hφψ : (Over.pullback q).map φ ≫ (pullbackSquareObjIso w Y).hom =
      (pullbackSquareObjIso w X).hom ≫ (Over.pullback v).map ψ) :
    pullback.fst (pullback.snd X.hom u) q ≫ φ.left ≫ pullback.fst Y.hom u =
      (pullbackSquareObjIso w X).hom.left ≫
        pullback.fst (pullback.snd X.hom p) v ≫ ψ.left ≫ pullback.fst Y.hom p := by
  have hleft : ((Over.pullback q).map φ).left ≫ (pullbackSquareObjIso w Y).hom.left =
      (pullbackSquareObjIso w X).hom.left ≫ ((Over.pullback v).map ψ).left :=
    congrArg CommaMorphism.left hφψ
  erw [← reassoc_of% pullback_map_left_comp_fst q φ]
  erw [← pullbackSquareObjIso_hom_left_fst w Y]
  rw [reassoc_of% hleft]
  erw [reassoc_of% pullback_map_left_comp_fst v ψ]
  rfl

/-- **Crossing the comparison isomorphism of a base-change square.**  A morphism into the
iterated base change `V ×_U (U ×_S X)`, given by a morphism `g₁` to `U ×_S X` and a morphism
`e` to `V`, is carried by the comparison isomorphism to the morphism into `L ×_S X` with
components `e ≫ v` and the common projection to `X`. -/
theorem pullbackSquareObjIso_lift_fst (w : q ≫ u = v ≫ p) {X : Over S} {Z : C}
    (g₁ : Z ⟶ Limits.pullback X.hom u) (g₂ : Z ⟶ Limits.pullback X.hom p) (e : Z ⟶ V)
    (h₁ : g₁ ≫ pullback.snd X.hom u = e ≫ q)
    (h₂ : g₂ ≫ pullback.snd X.hom p = e ≫ v)
    (h₃ : g₁ ≫ pullback.fst X.hom u = g₂ ≫ pullback.fst X.hom p) :
    pullback.lift g₁ e h₁ ≫ (pullbackSquareObjIso w X).hom.left ≫
      pullback.fst (pullback.snd X.hom p) v = g₂ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, pullbackSquareObjIso_hom_left_fst, ← Category.assoc,
      pullback.lift_fst, h₃]
  · rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc (pullbackSquareObjIso w X).hom.left,
      pullbackSquareObjIso_hom_left_snd, ← Category.assoc, pullback.lift_snd, h₂]

end CategoryTheory.Over

end
