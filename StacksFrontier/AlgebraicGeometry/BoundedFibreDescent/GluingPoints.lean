module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData

/-!
# The gluing isomorphism of a descent datum on literal fibre products

The gluing isomorphism of a descent datum is an isomorphism over a product taken in the category
of schemes over the base. Transported to the literal fibre products `V_i ×_S X_j` and
`X_i ×_S V_j`, it carries the first projection to the structure map of the `i`-th component and
is carried by the structure map of the `j`-th component to the second projection. On points this
says that the gluing isomorphism moves a point of `V_i` to a point of `V_j` lying over any
prescribed point of `X_j` in the same fibre of the family.

## Main results

* `AlgebraicGeometry.DescentData.gluingPullbackIso_hom_fst'` and
  `AlgebraicGeometry.DescentData.gluingPullbackIso_hom_snd` compute the two projections of the
  transported gluing isomorphism.  The primed name on the first marks the weaker hypotheses:
  it is stated for a family indexed by an arbitrary type, whereas the unprimed
  `gluingPullbackIso_hom_fst` is the single-morphism form.
* `AlgebraicGeometry.DescentData.exists_structureMap_eq` says that the image of the structure map
  of a component is a union of fibres of the family: a point in the fibre of `f j` over the image
  of a point of `V_i` is the image of a point of `V_j`.

## Implementation notes

The two projection formulas are obtained from `gluing_hom_fst` and
`gluing_hom_snd_structureMap` by applying the forgetful functor to schemes and inserting the
projection formulas for `CategoryTheory.Over.prodLeftIsoPullback`. Both are stated with the
structure map on the side on which it is not absorbed, so neither needs an inverse.

The point-level statement is deduced from the second projection formula together with the
existence of a point of a fibre product above any pair of points with the same image; no
separatedness or finiteness hypothesis is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

private lemma gluingPullbackIso_hom_comp (D : DescentData f) (i j : ι) {W : Scheme.{u}}
    (g : pullback (f i) ((D.obj j).hom ≫ f j) ⟶ W) :
    (D.gluingPullbackIso i j).hom ≫ g =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
        (D.gluing i j).hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom ≫ g := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]

/-- The transported gluing isomorphism carries the first projection of `X_i ×_S V_j` to the
first projection of `V_i ×_S X_j` followed by the structure map of the `i`-th component. -/
@[reassoc]
lemma gluingPullbackIso_hom_fst' (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom ≫ pullback.fst (f i) ((D.obj j).hom ≫ f j) =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ (D.obj i).hom := by
  have h := congrArg (·.left) (D.gluing_hom_fst i j)
  simp only [Over.comp_left] at h
  rw [gluingPullbackIso_hom_comp]
  erw [Over.prodLeftIsoPullback_hom_fst, h]
  simp

/-- The transported gluing isomorphism followed by the second projection of `X_i ×_S V_j` and the
structure map of the `j`-th component is the second projection of `V_i ×_S X_j`. -/
@[reassoc]
lemma gluingPullbackIso_hom_snd (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom ≫ pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫
        (D.obj j).hom =
      pullback.snd ((D.obj i).hom ≫ f i) (f j) := by
  have h := congrArg (·.left) (D.gluing_hom_snd_structureMap i j)
  simp only [Over.comp_left] at h
  rw [gluingPullbackIso_hom_comp]
  erw [Over.prodLeftIsoPullback_hom_snd_assoc, h]
  simp

/-- Given a point of the `i`-th component of a descent datum and a point of `X j` in the same
fibre of the family, the gluing isomorphism produces a point of the `j`-th component above the
latter. -/
theorem exists_structureMap_eq (D : DescentData f) (i j : ι)
    (v : (D.obj i).left) (x : X j) (h : f i ((D.obj i).hom v) = f j x) :
    ∃ w : (D.obj j).left, (D.obj j).hom w = x := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (D.obj i).hom ≫ f i) (g := f j) v x (by rw [Scheme.Hom.comp_apply]; exact h)
  refine ⟨pullback.snd (f i) ((D.obj j).hom ≫ f j) ((D.gluingPullbackIso i j).hom z), ?_⟩
  rw [← Scheme.Hom.comp_apply (pullback.snd (f i) ((D.obj j).hom ≫ f j)) (D.obj j).hom,
    ← Scheme.Hom.comp_apply, D.gluingPullbackIso_hom_snd i j, hz]

end AlgebraicGeometry.DescentData

end
