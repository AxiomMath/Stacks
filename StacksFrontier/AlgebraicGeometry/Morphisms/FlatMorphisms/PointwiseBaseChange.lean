module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness at a point under base change

Flatness of a morphism of schemes at a point is preserved by an arbitrary base change, and it
descends along a base change of a flat morphism.  Together the two say that for a cartesian
square whose horizontal base morphism is flat, a point of the fibre product is a point of
flatness of the base-changed morphism exactly when its image is a point of flatness of the
original one.  This is the pointwise half of the flat locus of
[Stacks, Tag 047C] for the structure sheaf.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.isFlatAt_of_isPullback`: preservation under an arbitrary base change.
* `AlgebraicGeometry.isFlatAt_of_comp`: flat permanence at a point.
* `AlgebraicGeometry.isFlatAt_iff_of_isPullback`: the equivalence, over a flat base morphism.
* `AlgebraicGeometry.isFlatAt_of_flat_comp_ι`: a morphism flat on an open subscheme of its
  source is flat at every point of that open.

## Implementation notes

Preservation is `AlgebraicGeometry.isFlatAt_pullback_fst_of_isFlatAt`, which is stated for the
canonical fibre product, transported along the comparison isomorphism of an arbitrary cartesian
square; the transport is `AlgebraicGeometry.isFlatAt_comp_of_isIso`.

Descent is flat permanence: the stalk of the fibre product is flat over the stalk of the base
and faithfully flat over the stalk of the original source, a flat local homomorphism of local
rings being faithfully flat.  No finiteness hypothesis is used anywhere.

## References

* [Stacks Project, Tag 047C](https://stacks.math.columbia.edu/tag/047C)
* [Stacks Project, Tag 039V](https://stacks.math.columbia.edu/tag/039V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Precomposing with an isomorphism of schemes does not affect flatness at a point. -/
public theorem isFlatAt_comp_of_isIso {P Q A : Scheme.{u}} (e : P ⟶ Q) [IsIso e]
    (q : Q ⟶ A) (t : P) (hflat : IsFlatAt q.toLRSHom.toShHom (e t)) :
    IsFlatAt (e ≫ q).toLRSHom.toShHom t := by
  have hbij : Function.Bijective (e.stalkMap t).hom := ConcreteCategory.bijective_of_isIso _
  have hcomp : ((q.stalkMap (e t) ≫ e.stalkMap t).hom).Flat := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.Flat.comp_iff_of_bijective_left hbij).mpr hflat
  have heq := congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp e q t)
  change ((e ≫ q).stalkMap t).hom.Flat
  exact heq ▸ hcomp

/-- **Base change of flatness at a point.**  In a cartesian square the projection to the new
base is flat at a point as soon as the morphism it is a base change of is flat at the image
point. -/
public theorem isFlatAt_of_isPullback {P A X' Y' : Scheme.{u}} {p : P ⟶ A} {q : P ⟶ X'}
    {w : A ⟶ Y'} {f : X' ⟶ Y'} (hsq : IsPullback p q w f) (t : P)
    (hflat : IsFlatAt f.toLRSHom.toShHom (q t)) :
    IsFlatAt p.toLRSHom.toShHom t := by
  have hsnd : (pullback.snd w f) (hsq.isoPullback.hom t) = q t := by
    rw [← Scheme.Hom.comp_apply, hsq.isoPullback_hom_snd]
  have hbase : IsFlatAt (pullback.fst w f).toLRSHom.toShHom (hsq.isoPullback.hom t) :=
    isFlatAt_pullback_fst_of_isFlatAt w f _ (by rwa [hsnd])
  exact hsq.isoPullback_hom_fst ▸
    isFlatAt_comp_of_isIso hsq.isoPullback.hom (pullback.fst w f) t hbase

/-- **Flat permanence at a point.**  If `a` is flat at `x` and `a ≫ b` is flat at `x`, then `b`
is flat at `a x`: the stalk of the source is faithfully flat over the stalk at `a x`, a flat
local homomorphism of local rings being faithfully flat. -/
public theorem isFlatAt_of_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X)
    (ha : IsFlatAt a.toLRSHom.toShHom x)
    (hab : IsFlatAt (a ≫ b).toLRSHom.toShHom x) :
    IsFlatAt b.toLRSHom.toShHom (a x) := by
  change (((a ≫ b).stalkMap x).hom).Flat at hab
  have heq : ((a ≫ b).stalkMap x).hom
      = (a.stalkMap x).hom.comp (b.stalkMap (a x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp a b x)
  rw [heq] at hab
  change ((a.stalkMap x).hom).Flat at ha
  change ((b.stalkMap (a x)).hom).Flat
  let C := Z.presheaf.stalk (b (a x))
  let A := Y.presheaf.stalk (a x)
  let M := X.presheaf.stalk x
  let _ : Algebra C A := (b.stalkMap (a x)).hom.toAlgebra
  let _ : Algebra A M := (a.stalkMap x).hom.toAlgebra
  let _ : Algebra C M := ((a.stalkMap x).hom.comp (b.stalkMap (a x)).hom).toAlgebra
  have _ : IsScalarTower C A M := IsScalarTower.of_algebraMap_eq' rfl
  have _ : Module.Flat A M := ha
  have _ : Module.Flat C M := hab
  have _ : IsLocalHom (algebraMap A M) := inferInstanceAs (IsLocalHom (a.stalkMap x).hom)
  have _ : Module.FaithfullyFlat A M := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat M

/-- A morphism flat on an open subscheme of its source is flat at every point of that open. -/
public theorem isFlatAt_of_flat_comp_ι {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    (hU : Flat (U.ι ≫ f)) {x : X} (hx : x ∈ U) : IsFlatAt f.toLRSHom.toShHom x :=
  isFlatAt_of_comp U.ι f ⟨x, hx⟩ (Flat.stalkMap U.ι ⟨x, hx⟩) (Flat.stalkMap (U.ι ≫ f) ⟨x, hx⟩)

/-- **Flatness at a point, over a flat base change.**  For a cartesian square whose base
morphism `q` is flat, a point of the new source is a point of flatness of the base-changed
morphism exactly when its image is a point of flatness of the original morphism. -/
public theorem isFlatAt_iff_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {p : X' ⟶ X} {q : Y' ⟶ Y} (hp : IsPullback p f' f q) [Flat q] (x' : X') :
    IsFlatAt f'.toLRSHom.toShHom x' ↔ IsFlatAt f.toLRSHom.toShHom (p x') := by
  have _ : Flat p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip inferInstance
  refine ⟨fun h => ?_, fun h => isFlatAt_of_isPullback hp.flip x' h⟩
  have hcomp : IsFlatAt (p ≫ f).toLRSHom.toShHom x' := by
    change (((p ≫ f).stalkMap x').hom).Flat
    rw [hp.w, congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f' q x')]
    exact RingHom.Flat.comp (Flat.stalkMap q (f' x')) h
  exact isFlatAt_of_comp p f x' (Flat.stalkMap p x') hcomp

end AlgebraicGeometry
