module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Cohomological dimension along an integral morphism

Let `f : X ⟶ Y` be an integral morphism of quasi-compact and quasi-separated schemes. Then
`cd(X) ≤ cd(Y)`. Integral morphisms have vanishing higher direct images (Stacks 03QP), so the
Leray spectral sequence degenerates to `H^q(X, F) = H^q(Y, f_*F)`, and `f_*F` is torsion when
`F` is (Stacks 0DDD (1) in degree zero).

This is the step of the proof of Stacks 0F0V that disposes of the case `dim X = 0`, where the
structure morphism `X ⟶ Spec K` is finite, and that reduces the general case, through a finite
Noether normalization `X ⟶ 𝔸^d_K`, to the affine space `𝔸^d_K`.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_of_isIntegralHom`: `cd(X) ≤ cd(Y)`
  for `f : X ⟶ Y` integral.

## Implementation notes

The comparison of cohomology groups is
`Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`, which is Stacks 03YU read through
the exactness of `f_*` for an integral `f`; the torsion of `f_*F` is
`Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb`. The `Ext`-groups at the
coefficient universe `u + 1` are those of
`Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology`, made a high-priority
local instance so that instance search does not try the universe-polymorphic instances of the
imported modules.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- Direct image of abelian sheaves on the small étale sites is additive, at the coefficient
universe `u + 1`, so that instance search does not try the universe-polymorphic instance for
`Stacks.EtaleCohomology.etaleAbelianDirectImage`. -/
local instance (priority := high) additive_smallEtaleDirectImageAb {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} f).Additive where
  map_add := rfl

/-- **Cohomological dimension does not increase along an integral morphism.** For an integral
morphism `f : X ⟶ Y` of quasi-compact and quasi-separated schemes, `cd(X) ≤ cd(Y)`: for a
torsion abelian sheaf `F` on `X_ét` the cohomology `H^q(X, F)` is `H^q(Y, f_*F)`, and `f_*F` is
a torsion abelian sheaf on `Y_ét`. -/
public theorem etaleCohomologicalDimension_le_of_isIntegralHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegralHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] :
    etaleCohomologicalDimension X ≤ etaleCohomologicalDimension Y := by
  refine etaleCohomologicalDimension_le X _ fun F hF q hq => ?_
  have hT : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} f).obj F) :=
    Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb.{0} f F hF
  have h := isEtaleCohomologyBound_etaleCohomologicalDimension Y _ hT q hq
  exact (Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv f F q).toEquiv
    |>.subsingleton_congr.2 h

/-- **A direct image along an integral morphism is acyclic for a further direct image when the
composite is integral.** For `i : D ⟶ Y` and `g : Y ⟶ S` with `i` and `i ≫ g` integral and an
abelian sheaf `H` on `D_ét`, `R^pg_*(i_*H) = 0` for `p > 0`: `i_*` is exact (Stacks 03QP) and
preserves injectives, so `R^pg_*(i_*H) = R^p(i ≫ g)_*H`, which vanishes because `(i ≫ g)_*` is
exact. With `i` the inclusion of a closed subscheme mapping isomorphically to `S`, this is the
step of the proof of Stacks 0F0V which kills the terms `R^pg_*R^qj_*𝓕` with `p, q > 0`. -/
public theorem isZero_rightDerived_smallEtaleDirectImageAb_obj_of_isIntegralHom {D Y S : Scheme.{u}}
    (i : D ⟶ Y) (g : Y ⟶ S) [IsIntegralHom i] [IsIntegralHom (i ≫ g)]
    (H : Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    IsZero (((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g).rightDerived p).obj
      ((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} i).obj H)) := by
  have hexi := Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom i
  have hexig := Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom (i ≫ g)
  have : PreservesFiniteLimits (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} i) :=
    ((exactFunctor_iff _).1 hexi).1
  have : (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} i).PreservesInjectiveObjects :=
    Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects i
  have hA : ∀ q : ℕ, 0 < q →
      IsZero (((Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} i).rightDerived q).obj H) :=
    fun q hq => Functor.isZero_rightDerived_of_exactFunctor _ hexi H q hq
  refine (Functor.isZero_rightDerived_of_exactFunctor _ hexig H p hp).of_iso ?_
  exact (Stacks.RightDerivedComp.objIso (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} i)
      (injectiveResolution H) hA (Stacks.EtaleCohomology.smallEtaleDirectImageAb.{u + 1} g)
        p).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso i g)
      p).app H

end AlgebraicGeometry.Scheme

end
