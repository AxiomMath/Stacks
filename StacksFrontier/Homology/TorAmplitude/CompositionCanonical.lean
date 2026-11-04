module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Composition
public import StacksFrontier.Homology.TorAmplitude.FlatResolution

/-!
# Tor amplitude and derived tensor products, at the canonical derived tensor product

At the canonical derived tensor product of Stacks 0BYI, Tor amplitudes add under derived tensor
product (Stacks 0B66), and restriction of scalars along a ring map `A → B` of Tor dimension at
most `d` sends a complex of Tor amplitude in `[a, b]` to one of Tor amplitude in `[a - d, b]`
(Stacks 066K), with the two rings and the carriers of the complex in independent universes.

## Main definitions

* `StacksDraft.TorAmplitude.moduleLift`: the embedding `ModuleCat.{v} R ⥤
  ModuleCat.{max u v w} (ULift.{max v w} R)` of the modules of a ring `R : Type u` into a common
  ambient universe, changing neither the ring nor the module structure.
* `StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift`: Tor amplitude of an object of
  `D(ModuleCat.{v} R)` measured, after `moduleLift`, at the canonical derived tensor product of
  the lifted ring.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_derivedTensorProduct`: Stacks 0B66 at the
  canonical derived tensor product.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_of_torDimensionLE`:
  Stacks 066K at the canonical derived tensor product, with the two rings and the carriers of the
  complex in independent universes.

## References

* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedTensor

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-! ### Transport along an isomorphism of the derived category -/

/-- The canonical Tor amplitude of Stacks 0652 only depends on the isomorphism class of the
object of the derived category. -/
private lemma hasTorAmplitudeCanonical_of_iso (R : Type u) [CommRing R]
    {X Y : DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R X a b) : HasTorAmplitudeCanonical R Y a b :=
  (hasTorAmplitudeIn_canonical_iff R Y a b).mp
    (hasTorAmplitudeIn_of_iso _ e ((hasTorAmplitudeIn_canonical_iff R X a b).mpr h))

/-! ### Stacks 0B66 at the canonical derived tensor product -/

/-- Let `A → B` be a map of commutative rings and let `K` and `L` be complexes of `B`-modules. If
`K` has Tor amplitude in `[a, b]` as a complex of `B`-modules and `L`, after restriction of
scalars, has Tor amplitude in `[c, d]` as a complex of `A`-modules, then `K ⊗_B^L L`, after
restriction of scalars, has Tor amplitude in `[a + c, b + d]` as a complex of `A`-modules.

All three Tor amplitudes are those of Stacks 0652 at the canonical derived tensor product of
Stacks 0BYI, and `K ⊗_B^L L` is that canonical derived tensor product over `B`. -/
@[stacks 0B66]
public theorem hasTorAmplitudeCanonical_derivedTensorProduct
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K L : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hK : HasTorAmplitudeCanonical B (DerivedCategory.Q.obj K) a b)
    (hL : HasTorAmplitudeCanonical A
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj L)) c d) :
    HasTorAmplitudeCanonical A
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (((canonicalDerivedTensorProduct B).tensor.obj (DerivedCategory.Q.obj K)).obj
          (DerivedCategory.Q.obj L))) (a + c) (b + d) :=
  (hasTorAmplitudeIn_canonical_iff A _ (a + c) (b + d)).mp
    (hasTorAmplitudeIn_derivedTensor A B (canonicalDerivedTensorProduct A)
      (canonicalDerivedTensorProduct B) (canonicalTensorComparison B)
      (canonicalTensorIsLeftDerived B) K L a b c d
      ((hasTorAmplitudeIn_canonical_iff B _ a b).mpr hK)
      ((hasTorAmplitudeIn_canonical_iff A _ c d).mpr hL))

/-! ### Stacks 066K at the canonical derived tensor product, in one universe -/

/-- Let `A → B` be a map of commutative rings and let the two rings and the carriers of the
complexes all live in one universe. If `B` has Tor dimension at most `d` as an `A`-module, that
is, if `B` placed in degree zero has Tor amplitude in `[-d, 0]` over `A`, then a complex `K` of
`B`-modules with Tor amplitude in `[a, b]` over `B` has Tor amplitude in `[a - d, b]` over `A`,
all Tor amplitudes taken at the canonical derived tensor product. -/
private theorem hasTorAmplitudeCanonical_restrictScalars_of_torDimensionLE
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b d : ℤ)
    (hB : HasTorAmplitudeCanonical A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) (-d) 0)
    (hK : HasTorAmplitudeCanonical B (DerivedCategory.Q.obj K) a b) :
    HasTorAmplitudeCanonical A
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) (a - d) b :=
  (hasTorAmplitudeIn_canonical_iff A _ (a - d) b).mp
    (hasTorAmplitudeIn_restrictScalars_of_torDimensionLE A B (canonicalDerivedTensorProduct A)
      (canonicalDerivedTensorProduct B) (canonicalTensorComparison B)
      (canonicalTensorIsLeftDerived B) K a b d
      ((hasTorAmplitudeIn_canonical_iff A _ (-d) 0).mpr hB)
      ((hasTorAmplitudeIn_canonical_iff B _ a b).mpr hK))

/-! ### Stacks 066K at independent universes -/

/-- Lift a ring `R : Type u` and the carriers of its modules into the single universe
`max u v w`, changing neither the ring nor the module structure. -/
public noncomputable abbrev moduleLift (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v w} (ULift.{max v w} R) :=
  ModuleCat.uliftFunctor.{max u w, v} R ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- `StacksDraft.TorAmplitude.moduleLift` preserves finite limits. -/
public instance moduleLift_preservesFiniteLimits (R : Type u) [CommRing R] :
    PreservesFiniteLimits (moduleLift.{u, v, w} R) :=
  comp_preservesFiniteLimits _ _

/-- `StacksDraft.TorAmplitude.moduleLift` preserves finite colimits. -/
public instance moduleLift_preservesFiniteColimits (R : Type u) [CommRing R] :
    PreservesFiniteColimits (moduleLift.{u, v, w} R) :=
  comp_preservesFiniteColimits _ _

/-- Tor amplitude in `[a, b]` for an object of `D(ModuleCat.{v} R)`, where `R : Type u`, measured
at the canonical derived tensor product of the lifted ring `ULift.{max v w} R` after transporting
along `moduleLift`. Here `u` is the universe of the ring, `v` that of the module carriers and `w`
an auxiliary ambient universe. -/
public def HasTorAmplitudeCanonicalLift {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) : Prop :=
  HasTorAmplitudeCanonical (ULift.{max v w} R)
    ((moduleLift.{u, v, w} R).mapDerivedCategory.obj K) a b

/-- Let `f : A → B` be a map of commutative rings and let `K` be a complex of `B`-modules; the
two rings and the carriers of `K` live in three independent universes. If `B` has Tor dimension
at most `d` as an `A`-module, that is, if `B` placed in degree zero has Tor amplitude in
`[-d, 0]` over `A`, then `K`, after restriction of scalars along `f`, has Tor amplitude in
`[a - d, b]` over `A`.

Tor amplitude is `HasTorAmplitudeCanonicalLift`, that is, Stacks 0652 at the canonical derived
tensor product of Stacks 0BYI on the ring lifted into the ambient universe. -/
@[stacks 066K]
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_of_torDimensionLE
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (K : CochainComplex (ModuleCat.{w} B) ℤ) (a b d : ℤ)
    (hB : HasTorAmplitudeCanonicalLift.{u, v, w}
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) (-d) 0)
    (hK : HasTorAmplitudeCanonicalLift.{v, w, u} (DerivedCategory.Q.obj K) a b) :
    HasTorAmplitudeCanonicalLift.{u, w, v}
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{w} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      (a - d) b := by
  let A' := ULift.{max v w} A
  let B' := ULift.{max u w} B
  let f' : A' →+* B' := f.ulift
  let _ : Algebra A' B' := f'.toAlgebra
  let L := ((moduleLift.{v, w, u} B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hK' : HasTorAmplitudeCanonical B' (DerivedCategory.Q.obj L) a b :=
    hasTorAmplitudeCanonical_of_iso B'
      ((moduleLift.{v, w, u} B).mapDerivedCategoryFactors.app K) a b hK
  have hB' : HasTorAmplitudeCanonical A'
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A') 0).obj
        ((ModuleCat.restrictScalars (algebraMap A' B')).obj (ModuleCat.of B' B'))) (-d) 0 :=
    hasTorAmplitudeCanonical_of_iso A'
      (((moduleLift.{u, v, w} A).mapDerivedCategorySingleFunctor 0).app
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) (-d) 0 hB
  exact hasTorAmplitudeCanonical_of_iso A'
    ((ModuleCat.restrictScalars (algebraMap A' B')).mapDerivedCategoryFactors.app L ≪≫
      ((moduleLift.{u, w, v} A).mapDerivedCategoryFactors.app
        (((ModuleCat.restrictScalars.{w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)).symm) (a - d) b
    (hasTorAmplitudeCanonical_restrictScalars_of_torDimensionLE A' B' L a b d hB' hK')

end

end StacksDraft.TorAmplitude
