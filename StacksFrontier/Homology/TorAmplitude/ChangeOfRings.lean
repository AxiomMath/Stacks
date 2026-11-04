module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Homology.TorAmplitude.Termwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude and restriction of scalars along a flat ring map

Let `A → B` be a map of commutative rings which makes `B` a flat `A`-module. A complex of
`B`-modules with Tor amplitude in `[a, b]` over `B` keeps that Tor-amplitude bound when
regarded as a complex of `A`-modules. This is Stacks 066J.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_restrictScalars`: restriction of scalars along a
  flat ring map preserves a Tor-amplitude bound, Stacks 066J.

## Implementation notes

Tor amplitude of an object of the derived category is expressed here by the equivalent
condition of Stacks 0654: the object is represented by a complex of flat modules which is
strictly bounded, i.e. by a complex satisfying `StacksDraft.TorAmplitude.Termwise.IsComplexOfFlats`
  together with
`CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`. In this form the statement
makes no reference to a derived tensor product, so the two rings and the module category may
live in independent universes.

Given such a representative `E` over `B`, its restriction of scalars is a representative over
`A`: its terms are flat over `A` because flatness composes along `A → B` (`Module.Flat.trans`),
the strict bounds are preserved because restriction of scalars is applied termwise, and the
identification in the derived category comes from the fact that restriction of scalars is exact
and therefore its localization commutes with `DerivedCategory.Q`
(`CategoryTheory.Functor.mapDerivedCategoryFactors`).

## References

* [Stacks Project, Tag 066J](https://stacks.math.columbia.edu/tag/066J)
-/

open CategoryTheory

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- Restriction of scalars preserves finite limits. Mathlib derives exactness of
`ModuleCat.restrictScalars` from its adjunctions, which constrains the universe of the module
category; the limit-by-limit instances hold for an arbitrary module universe. -/
@[sga "4 IV 11.1.6" "special case"]
private instance preservesFiniteLimits_restrictScalars {A : Type u} {B : Type v}
    [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{w} f) := by
  constructor
  intro J _ _
  constructor
  intro K
  infer_instance

/-- Restriction of scalars preserves finite colimits, for an arbitrary module universe. -/
private instance preservesFiniteColimits_restrictScalars {A : Type u} {B : Type v}
    [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{w} f) := by
  constructor
  intro J _ _
  constructor
  intro K
  infer_instance

/-- **Stacks 066J.** A complex of `B`-modules with Tor amplitude in `[a, b]` retains that
Tor-amplitude bound after restriction of scalars along a flat ring map `A → B`. -/
@[stacks 066J]
theorem hasTorAmplitudeIn_restrictScalars
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B]
    (K : CochainComplex (ModuleCat.{w} B) ℤ) (a b : ℤ)
    (hK : ∃ E : CochainComplex (ModuleCat.{w} B) ℤ,
      StacksDraft.TorAmplitude.Termwise.IsComplexOfFlats E ∧ E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj E)) :
    ∃ E : CochainComplex (ModuleCat.{w} A) ℤ,
      StacksDraft.TorAmplitude.Termwise.IsComplexOfFlats E ∧ E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        Nonempty ((DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{w} (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :
            DerivedCategory (ModuleCat.{w} A)) ≅
          DerivedCategory.Q.obj E) := by
  obtain ⟨E, hEflat, hEge, hEle, ⟨e⟩⟩ := hK
  let F := ModuleCat.restrictScalars.{w} (algebraMap A B)
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, ?_, ?_, ?_, ?_⟩
  · intro i
    let _ := hEflat i
    let _ : Module A (E.X i) := Module.compHom (E.X i) (algebraMap A B)
    let _ : IsScalarTower A B (E.X i) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact Module.Flat.trans A B (E.X i)
  · exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := E) F a).2 hEge
  · exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := E) F b).2 hEle
  · exact ⟨(F.mapDerivedCategoryFactors.app K).symm ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app E⟩

end

end StacksDraft.TorAmplitude
