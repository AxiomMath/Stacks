module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change along a commutative square

Let
```
V --v--> L
|        |
q        p
↓        ↓
U --u--> S
```
be a commutative square in a category with pullbacks. Pulling an object of `Over S` back
first along `u` and then along `q` gives the same result, up to a canonical isomorphism, as
pulling it back first along `p` and then along `v`: both compute the pullback along the
composite `V ⟶ S`. This file constructs that isomorphism, naturally in the object of
`Over S`, and records its compatibility with the two projections down to the object itself.

The construction is the uniqueness of a pullback: by the pasting law both iterated pullbacks
are pullbacks of the same cospan `· ⟶ S ⟵ V`, so `IsPullback.isoIsPullback` identifies them,
and the characterizing equations `IsPullback.isoIsPullback_hom_fst` and
`IsPullback.isoIsPullback_hom_snd` are exactly the required compatibilities.

## Main definitions

* `CategoryTheory.Over.pullbackSquareIso`: the natural isomorphism
  `Over.pullback u ⋙ Over.pullback q ≅ Over.pullback p ⋙ Over.pullback v` attached to a
  commutative square `q ≫ u = v ≫ p`.

## Main results

* `CategoryTheory.Over.isPullback_pullback_snd_pullback`: the iterated pullback along `u`
  then `q` is a pullback of the cospan `· ⟶ S ⟵ V` along the composite `q ≫ u`.
* `CategoryTheory.Over.pullbackSquareObjIso_hom_left_fst`: the comparison isomorphism
  commutes with the projections to the object of `Over S`.
* `CategoryTheory.Over.pullbackSquareObjIso_hom_left_snd`: the comparison isomorphism
  commutes with the projections to `V`.

## Implementation notes

The simp set used in the proofs mentions `pullback.lift_fst`, `pullback.lift_snd` and their
associated variants explicitly: they are not simp lemmas, and `Over.pullback` is defined by
a `pullback.lift`, so without them the naturality square does not reduce.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {S U L V : C} {u : U ⟶ S} {p : L ⟶ S} {v : V ⟶ L} {q : V ⟶ U}

/-- Pulling `X : Over S` back along `u : U ⟶ S` and then along `q : V ⟶ U` computes the
pullback of `X.hom` along the composite `q ≫ u`. -/
theorem isPullback_pullback_snd_pullback (X : Over S) :
    IsPullback (pullback.fst (pullback.snd X.hom u) q ≫ pullback.fst X.hom u)
      (pullback.snd (pullback.snd X.hom u) q) X.hom (q ≫ u) :=
  (IsPullback.of_hasPullback (pullback.snd X.hom u) q).paste_horiz
    (IsPullback.of_hasPullback X.hom u)

/-- Pulling `X : Over S` back along `p : L ⟶ S` and then along `v : V ⟶ L` computes the
pullback of `X.hom` along the composite `q ≫ u`, for any commutative square
`q ≫ u = v ≫ p`. -/
theorem isPullback_pullback_snd_pullback' (w : q ≫ u = v ≫ p) (X : Over S) :
    IsPullback (pullback.fst (pullback.snd X.hom p) v ≫ pullback.fst X.hom p)
      (pullback.snd (pullback.snd X.hom p) v) X.hom (q ≫ u) :=
  w ▸ isPullback_pullback_snd_pullback (u := p) (q := v) X

/-- The comparison isomorphism, at a single object of `Over S`, between the two iterated base
changes attached to a commutative square `q ≫ u = v ≫ p`. -/
noncomputable def pullbackSquareObjIso (w : q ≫ u = v ≫ p) (X : Over S) :
    (Over.pullback u ⋙ Over.pullback q).obj X ≅ (Over.pullback p ⋙ Over.pullback v).obj X :=
  Over.isoMk ((isPullback_pullback_snd_pullback X).isoIsPullback _ _
    (isPullback_pullback_snd_pullback' w X)) (by simp)

/-- The comparison isomorphism `pullbackSquareObjIso w X` commutes with the projections of the
two iterated pullbacks to `X.left`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareObjIso_hom_left_fst (w : q ≫ u = v ≫ p) (X : Over S) :
    (pullbackSquareObjIso w X).hom.left ≫ pullback.fst (pullback.snd X.hom p) v ≫
        pullback.fst X.hom p =
      pullback.fst (pullback.snd X.hom u) q ≫ pullback.fst X.hom u :=
  (isPullback_pullback_snd_pullback X).isoIsPullback_hom_fst _ _
    (isPullback_pullback_snd_pullback' w X)

/-- The comparison isomorphism `pullbackSquareObjIso w X` commutes with the projections of the
two iterated pullbacks to `V`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareObjIso_hom_left_snd (w : q ≫ u = v ≫ p) (X : Over S) :
    (pullbackSquareObjIso w X).hom.left ≫ pullback.snd (pullback.snd X.hom p) v =
      pullback.snd (pullback.snd X.hom u) q :=
  (isPullback_pullback_snd_pullback X).isoIsPullback_hom_snd _ _
    (isPullback_pullback_snd_pullback' w X)

/-- Base change along a commutative square `q ≫ u = v ≫ p`: pulling back along `u` and then
along `q` is naturally isomorphic to pulling back along `p` and then along `v`. -/
noncomputable def pullbackSquareIso (w : q ≫ u = v ≫ p) :
    Over.pullback u ⋙ Over.pullback q ≅ Over.pullback p ⋙ Over.pullback v :=
  NatIso.ofComponents (pullbackSquareObjIso w) (by
    intro X Y f
    ext
    apply (isPullback_pullback_snd_pullback' w Y).hom_ext
    · simp [Over.pullback_obj_hom, Over.pullback_obj_left, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp [Over.pullback_obj_hom, Over.pullback_obj_left, pullback.lift_snd])

/-- The component of `pullbackSquareIso w` at `X : Over S` is `pullbackSquareObjIso w X`. -/
@[simp]
theorem pullbackSquareIso_hom_app (w : q ≫ u = v ≫ p) (X : Over S) :
    (pullbackSquareIso w).hom.app X = (pullbackSquareObjIso w X).hom :=
  rfl

end CategoryTheory.Over

end
