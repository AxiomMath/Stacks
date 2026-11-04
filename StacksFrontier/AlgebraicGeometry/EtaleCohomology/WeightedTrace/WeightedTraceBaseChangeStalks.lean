module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso

/-!
# Stalkwise ingredients for base change of the weighted trace

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `w` be an
integer-valued function on `X`. The trace map of Stacks 0GKG is characterised by its behaviour on
geometric stalks, the predicate
`AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction`. This file
collects stalkwise facts comparing that behaviour across a cartesian square, as in part (2) of
Stacks 0GKH.

Three things are provided. First, a summandwise criterion for the characterising property, so that
it can be verified one point of a geometric fibre at a time. Second, the behaviour of the
base-change comparison of the two direct sums of stalks of Stacks 0F5J on a single summand. Third,
the elementary bookkeeping: the weight of a point of the geometric fibre of the base change is the
weight of its image, and a germ may be moved across the identification of the stalks at two equal
geometric points.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleGerm_eqToHom` — moving a germ across the identification of
  the stalks at two geometric points with the same residue field and equal structure morphisms.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_of_fiberStalkOf` — **the summandwise
  criterion.** A morphism `f_! f^{-1}F ⟶ F` has the weighted trace behaviour on geometric stalks
  as soon as, on the summand of the stalk decomposition of Stacks 0F5F indexed by a point `x` of
  the geometric fibre, it is multiplication by the weight of `x`. This is the converse of
  `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_fiberStalkOf`.
* `AlgebraicGeometry.SmallEtale.fiberPointBaseChange_weight` — the weight pulled back along the
  horizontal morphism of a cartesian square, at a point of the geometric fibre of the base change,
  is the weight at the corresponding point of the original geometric fibre.
* `AlgebraicGeometry.SmallEtale.fiberStalksBaseChangeEquiv_fiberStalkOf` and
  `AlgebraicGeometry.SmallEtale.fiberStalksBaseChangeEquiv_symm_fiberStalkOf` — the base-change
  comparison of the two direct sums of stalks carries the summand indexed by a point of the
  geometric fibre of `f'` to the summand indexed by its image in the geometric fibre of `f`, and
  conversely.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Transport

/-- Moving a germ across the identification of the stalks at two geometric points with the same
residue field and equal structure morphisms. -/
public theorem etaleGerm_eqToHom (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (r : Type u) [Field r] [IsAlgClosed r] {m m' : Spec (.of r) ⟶ S} (hm : m = m')
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
    (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS ⟨r, m⟩).obj W)
    (q' : (geometricPointFiber B S hS ⟨r, m'⟩).obj W) (hq : q.1 = q'.1)
    (a : P.obj (op W)) :
    (eqToHom (congrArg (fun z => etaleStalk B S hS z P)
        (congrArg (fun k => ({ residueField := r, hom := k } : GeometricPoint S)) hm)))
        (etaleGerm B S hS ⟨r, m⟩ P W q a) =
      etaleGerm B S hS ⟨r, m'⟩ P W q' a := by
  cases hm
  obtain ⟨qv, hqv⟩ := q
  obtain ⟨qv', hqv'⟩ := q'
  cases (hq : qv = qv')
  simp

end Transport

section Criterion

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The summandwise criterion for the weighted trace behaviour on geometric stalks.** A
morphism `τ : f_! f^{-1}F ⟶ F` has the behaviour on geometric stalks which characterises the
trace of Stacks 0GKG as soon as it carries a germ of `f^{-1}F` at a point `x` of a geometric
fibre, placed in the summand of the decomposition of Stacks 0F5F indexed by `x`, to the weight of
`x` times the corresponding germ of `F`.

This is the converse of `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_fiberStalkOf`. -/
public theorem hasWeightedTraceStalks_of_fiberStalkOf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
    (h : ∀ (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
      (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
        ((abPullback.{u, v} B f).obj F).obj)),
      (colim.map (Functor.whiskerLeft
          (CategoryOfElements.π (geometricPointFiber B Y.obj Y.property s)).op τ.1))
        ((fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).inv
          (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z)) =
        w (x.1 default) • (fiberPointPullbackStalkIso.{u, v} B f s F x).hom z) :
    HasWeightedTraceStalks.{u, v} B f w F τ := by
  intro s
  refine fiberStalks_hom_ext.{u, v} B f s fun x z => ?_
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((h s x z).trans (weightedTraceStalkMap_fiberStalkOf.{u, v} B f w F s x z).symm)

end Criterion

section Summand

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The summand inclusion of the direct sum of stalks over a geometric fibre, at its own
index. -/
public theorem fiberStalkOf_apply_self (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)) :
    (fiberStalkOf.{u, v} B f s F x z) x = z := by
  let _inst : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.of_eq_same (β := fun y : GeometricFiberPoint B f s =>
    ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x z

/-- The summand inclusion of the direct sum of stalks over a geometric fibre vanishes at every
other index. -/
public theorem fiberStalkOf_apply_of_ne {x y : GeometricFiberPoint B f s} (h : x ≠ y)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)) :
    (fiberStalkOf.{u, v} B f s F x z) y = 0 := by
  let _inst : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.of_eq_of_ne (β := fun y : GeometricFiberPoint B f s =>
    ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x y z (Ne.symm h)

end Summand

section BaseChange

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The weight pulled back along the horizontal morphism of a cartesian square, evaluated at a
point of the geometric fibre of the base change, is the weight at the corresponding point of the
original geometric fibre. -/
public theorem fiberPointBaseChange_weight (sq : IsPullback p f' f g) (w : X.obj → ℤ)
    (t : GeometricPoint Y'.obj) (x : GeometricFiberPoint B f' t) :
    (w ∘ B.inclusion.map p) (x.1 default) =
      w ((fiberPointBaseChange B p f' f g sq t x).1 default) := by
  show w ((B.inclusion.map p) (x.1 default)) =
    w ((x.1 ≫ B.inclusion.map p) default)
  rw [Scheme.Hom.comp_apply]

/-- The base-change comparison of the two direct sums of stalks of Stacks 0F5J carries the
summand indexed by the image in the geometric fibre of `f` of a point `x` of the geometric fibre
of `f'` to the summand indexed by `x`, through the identification of the two stalks. -/
public theorem fiberStalksBaseChangeEquiv_fiberStalkOf (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f' t)
    (z : ↑(etaleStalk B X.obj X.property
      ((fiberPointBaseChange B p f' f g sq t x).toGeometricPoint B f
        (t.map (B.inclusion.map g))) F.obj)) :
    fiberStalksBaseChangeEquiv B p f' f g sq t F
        (fiberStalkOf.{u, v} B f (t.map (B.inclusion.map g)) F
          (fiberPointBaseChange B p f' f g sq t x) z) =
      fiberStalkOf.{u, v} B f' t ((abPullback.{u, v} B p).obj F) x
        ((fiberStalkBaseChangeIso B p f' f g sq t F x).hom z) := by
  refine DFinsupp.ext fun y => ?_
  rw [fiberStalksBaseChangeEquiv_apply B p f' f g sq t F _ y]
  by_cases hxy : x = y
  · subst hxy
    rw [fiberStalkOf_apply_self.{u, v} B f (t.map (B.inclusion.map g)) F
      (fiberPointBaseChange B p f' f g sq t x) z]
    exact (fiberStalkOf_apply_self.{u, v} B f' t ((abPullback.{u, v} B p).obj F) x _).symm
  · have hne : fiberPointBaseChange B p f' f g sq t x ≠
        fiberPointBaseChange B p f' f g sq t y := fun hh =>
      hxy ((fiberPointBaseChange_bijective B p f' f g sq t).1 hh)
    rw [fiberStalkOf_apply_of_ne.{u, v} B f (t.map (B.inclusion.map g)) F hne z, map_zero]
    exact (fiberStalkOf_apply_of_ne.{u, v} B f' t ((abPullback.{u, v} B p).obj F) hxy _).symm

/-- The inverse of the base-change comparison of the two direct sums of stalks carries the
summand indexed by a point `x` of the geometric fibre of `f'` to the summand indexed by its image
in the geometric fibre of `f`. -/
public theorem fiberStalksBaseChangeEquiv_symm_fiberStalkOf (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f' t)
    (u : ↑(etaleStalk B X'.obj X'.property (x.toGeometricPoint B f' t)
      ((abPullback.{u, v} B p).obj F).obj)) :
    (fiberStalksBaseChangeEquiv B p f' f g sq t F).symm
        (fiberStalkOf.{u, v} B f' t ((abPullback.{u, v} B p).obj F) x u) =
      fiberStalkOf.{u, v} B f (t.map (B.inclusion.map g)) F
        (fiberPointBaseChange B p f' f g sq t x)
        ((fiberStalkBaseChangeIso B p f' f g sq t F x).inv u) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [fiberStalksBaseChangeEquiv_fiberStalkOf B p f' f g sq t F x]
  congr 1
  simp

end BaseChange

end AlgebraicGeometry.SmallEtale

end
