module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of an integral closure over a Dedekind domain

Let `A` be a Dedekind domain with fraction field `K`, let `L` be a field extension of `K`, and
let `B` be an integral closure of `A` in `L`. Then `B` is flat over `A`: the structure map
`A → L` is injective, so `L` is torsion free over `A`, hence so is the subring `B`, and over a
Dedekind domain every torsion free module is flat.

If `B` is moreover finite as an `A`-module, then `Spec B ⟶ Spec A` is flat and locally of finite
presentation, hence universally open; consequently every base change of it is an open map.

## Main results

* `IsIntegralClosure.flat`: an integral closure of a Dedekind domain in an extension of its
  fraction field is flat.
* `integralClosure.flat`: the same statement for the concrete integral closure.
* `IsIntegralClosure.universallyOpen_specMap_algebraMap`: for a finite such integral closure the
  morphism `Spec B ⟶ Spec A` is universally open.
* `IsIntegralClosure.isOpenMap_of_isPullback`: hence any base change of `Spec B ⟶ Spec A` is an
  open map.

## References

* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w t

/-- The structure map of a field extension of the fraction field of a domain is injective. -/
private theorem IsFractionRing.algebraMap_injective_of_isScalarTower (A : Type u) (K : Type v)
    (L : Type w) [CommRing A] [IsDomain A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] : Function.Injective (algebraMap A L) := by
  rw [IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)

/-- **An integral closure of a Dedekind domain in an extension of its fraction field is flat.**
Indeed `B` is torsion free over `A`, since it embeds into `L`, and over a Dedekind domain torsion
free modules are flat. -/
@[ega "0 6.3.4" "special case"]
theorem IsIntegralClosure.flat (A : Type u) (K : Type v) (L : Type w) {B : Type t} [CommRing A]
    [IsDedekindDomain A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [CommRing B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] : Module.Flat A B :=
  have : Module.IsTorsionFree A L := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (IsFractionRing.algebraMap_injective_of_isScalarTower A K L)
  have : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  inferInstance

/-- The integral closure of a Dedekind domain in an extension of its fraction field is flat. -/
theorem integralClosure.flat (A : Type u) (K : Type v) (L : Type w) [CommRing A]
    [IsDedekindDomain A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] : Module.Flat A (integralClosure A L) :=
  IsIntegralClosure.flat A K L

/-- **`Spec B ⟶ Spec A` is universally open** for `B` a finite integral closure of a Dedekind
domain `A` in an extension `L` of its fraction field: the morphism is flat because `B` is, and it
is locally of finite presentation because `A` is Noetherian and `B` is a finite `A`-module. -/
theorem IsIntegralClosure.universallyOpen_specMap_algebraMap (A : Type u) (K : Type v)
    (L : Type w) {B : Type u} [CommRing A] [IsDedekindDomain A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [CommRing B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Module.Finite A B] :
    UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr (IsIntegralClosure.flat A K L)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom,
      RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact UniversallyOpen.of_flat _

/-- Any base change of `Spec B ⟶ Spec A` is an open map, for `B` a finite integral closure of a
Dedekind domain `A` in an extension `L` of its fraction field. -/
theorem IsIntegralClosure.isOpenMap_of_isPullback (A : Type u) (K : Type v) (L : Type w)
    {B : Type u} [CommRing A] [IsDedekindDomain A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [CommRing B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Module.Finite A B] {W Y : Scheme.{u}} {c : W ⟶ Y} {d : W ⟶ Spec (.of B)}
    {q : Y ⟶ Spec (.of A)}
    (hsq : IsPullback c d q (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    IsOpenMap c.base :=
  have : UniversallyOpen c := MorphismProperty.of_isPullback (P := @UniversallyOpen) hsq.flip
    (IsIntegralClosure.universallyOpen_specMap_algebraMap A K L)
  c.isOpenMap

end
