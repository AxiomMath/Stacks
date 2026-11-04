module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsion cohomology under unbounded derived direct and inverse image on small étale sites

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. This file shows that
the unbounded derived direct image `Rf_*` of
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAb` carries a bounded below object of
`D(X_étale)` with torsion cohomology sheaves to an object with torsion cohomology sheaves, and that
the derived inverse image `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb` along any morphism
preserves torsion cohomology sheaves.

The first statement is the torsion clause of part (2) of Tag 0DDD, read on the unbounded derived
category. It is deduced from part (1) of Tag 0DDD
(`Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb`) by the
dévissage along truncations of `DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE`, torsion
sheaves being a Serre subcategory, the higher direct images being the cohomology of `Rf_*` on a
sheaf placed in degree zero (`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`).

## Main results

* `Stacks.EtaleCohomology.torsionCohomologyProperty_smallEtaleDerivedPushforwardAb` — the
  unbounded derived direct image of a bounded below object with torsion cohomology sheaves has
  torsion cohomology sheaves.
* `Stacks.EtaleCohomology.torsionCohomologyProperty_smallEtaleDerivedPullbackAb` — the derived
  inverse image preserves torsion cohomology sheaves.

## References

* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Torsion

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The unbounded derived direct image along a quasi-compact and quasi-separated morphism of a
bounded below object with torsion cohomology sheaves has torsion cohomology sheaves** (the torsion
clause of part (2) of Tag 0DDD, on the unbounded derived category).

On a torsion sheaf placed in degree zero the cohomology of `Rf_*` is the higher direct images,
which are torsion (part (1) of Tag 0DDD,
`Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb`);
torsion sheaves form a Serre subcategory, so the dévissage along the truncation triangles,
`DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE`, passes to bounded below objects. -/
theorem torsionCohomologyProperty_smallEtaleDerivedPushforwardAb {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (K : smallEtaleDerivedCategory X) (m : ℤ)
    (hK : K.IsGE m) (hKt : torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    torsionCohomologyProperty.{u + 1} (smallEtaleTopology Y)
      ((smallEtaleDerivedPushforwardAb f).obj K) := by
  have : (smallEtaleDerivedPushforwardAb f).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective _ (smallEtaleDerivedPushforwardAb f)
      (smallEtaleDerivedPushforwardAbUnit f)
  have hB : WeakSerre.IsWeakSerre (torsionSheafProperty.{u + 1} (smallEtaleTopology Y)) :=
    WeakSerre.isWeakSerre_of_isWeakSerreClass _
  have hR : ∀ (L : smallEtaleDerivedCategory X) (n : ℤ), L.IsGE n →
      ((smallEtaleDerivedPushforwardAb f).obj L).IsGE n := fun L n hL => by
    have := hL
    exact Stacks.DerivedFunctor.isGE_totalRightDerived_obj (smallEtalePushforwardAb f) L n
  refine (DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE
    (smallEtaleDerivedPushforwardAb f) _ hB hR K m hK fun q => ?_).2
  have := hR _ 0 (inferInstance : ((DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor _ q).obj K)).IsGE 0)
  refine ⟨⟨0, fun n hn => DerivedCategory.isZero_of_isGE _ 0 n hn⟩, fun n => ?_⟩
  rcases lt_or_ge n 0 with hn | hn
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre _ hB _ (DerivedCategory.isZero_of_isGE _ 0 n hn)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact torsionSheafProperty_of_iso _
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (smallEtalePushforwardAb f)
        (smallEtaleDerivedPushforwardAb f) (smallEtaleDerivedPushforwardAbUnit f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective _ n).symm
      (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0} f n _ (hKt q))

/-- **The derived inverse image preserves torsion cohomology sheaves.** For a morphism of schemes
`g : Y ⟶ X` and an object `K` of `D(X_étale)` with torsion cohomology sheaves, `g⁻¹K` has torsion
cohomology sheaves. Inverse image is exact, so `Hⁱ(g⁻¹K) ≅ g⁻¹Hⁱ(K)`, and the inverse image
`Stacks.EtaleCohomology.smallEtalePullbackAb` is isomorphic to the one for which torsion is
preserved, `Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage`. -/
@[sga "4 IX 1.2" "(iv)"]
theorem torsionCohomologyProperty_smallEtaleDerivedPullbackAb {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : smallEtaleDerivedCategory X)
    (hK : torsionCohomologyProperty.{u + 1} (smallEtaleTopology X) K) :
    torsionCohomologyProperty.{u + 1} (smallEtaleTopology Y)
      ((smallEtaleDerivedPullbackAb g).obj K) := fun i =>
  torsionSheafProperty_of_iso _
    (((smallEtalePullbackAb g).mapDerivedCategoryHomologyIso i).app K ≪≫
      (smallEtalePullbackAbIsoInverseImage g).app _).symm
    (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} g _ (hK i))

end Stacks.EtaleCohomology

end
