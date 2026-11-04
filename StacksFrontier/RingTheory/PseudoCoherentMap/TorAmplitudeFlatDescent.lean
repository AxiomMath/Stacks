module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.TorAmplitude.Local
import all StacksFrontier.Homology.TorAmplitude.Local

/-!
# A Tor-amplitude bound for a module descends along a flat algebra

Let `R → S` be a flat homomorphism of commutative rings and let `N` be an `S`-module. If `N`,
placed in degree zero, has Tor amplitude in `[a, b]` over `S`, then `N` read as an `R`-module has
Tor amplitude in `[a, b]` over `R`.

This is the step by which the source's proof of [stacks 069C] (3) ⟹ (1) feeds its hypothesis — a
Tor-amplitude bound over the *localisation* `A_p` — to [stacks 068X], which reads the bound over
`A` itself.

## Main results

* `RingHom.hasTorAmplitudeCanonical_single_restrictScalars_of_flat`: the descent itself.
* `RingHom.isPerfect_of_isZero`: a zero object of the derived category is perfect.

## Implementation notes

The descent is `StacksDraft.TorAmplitude.hasTorAmplitude_restrictScalars_of_flat`, which is
stated for the projective-resolution Tor amplitude of [stacks 0DJF] and is `private` where it is
proved, so it is reached by `import all`. The passage between that rendering and the canonical
one of [stacks 0652] is
`AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`,
which assumes no bound on the complex, and the single complex of the restricted module is the
restriction of the single complex by `HomologicalComplex.singleMapHomologicalComplex`.

`RingHom.isPerfect_of_isZero` duplicates a `private` declaration of
`StacksFrontier.RingTheory.PseudoCoherentMap.CompleteIntersection`; the two should be unified, and
this is the public one.

## References

* [The Stacks Project, Lemma 15.83.1 (068X)](https://stacks.math.columbia.edu/tag/068X)
* [The Stacks Project, Lemma 15.68.18 (0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
* [The Stacks Project, Lemma 37.61.11 (069C)](https://stacks.math.columbia.edu/tag/069C)
-/

@[expose] public section

universe u

open CategoryTheory StacksDraft.TorAmplitude
open AlgebraicGeometry.AffineRelativeTorAmplitude AlgebraicGeometry.BaseChangeTorAmplitude

attribute [local instance] HasDerivedCategory.standard

namespace RingHom

/-- A Tor-amplitude bound for a module over a flat algebra descends to the base ring: if `S` is
flat over `R` and the `S`-module `N`, placed in degree zero, has Tor amplitude in `[a, b]` over
`S`, then `N` read as an `R`-module has Tor amplitude in `[a, b]` over `R`. -/
public theorem hasTorAmplitudeCanonical_single_restrictScalars_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (N : ModuleCat.{u} S) (a b : ℤ)
    (h : HasTorAmplitudeCanonical S
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N) a b) :
    HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R S)).obj N)) a b := by
  have h1 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) a b :=
    (hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).mp
      (hasTorAmplitudeCanonical_of_iso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app N) a b h)
  have h2 := hasTorAmplitude_restrictScalars_of_flat (R := R)
    ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) a b h1
  have e : (CochainComplex.restrictScalars (algebraMap R S)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R S)).obj N) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars (algebraMap R S)) (ComplexShape.up ℤ) 0).app N
  exact hasTorAmplitudeCanonical_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
      ((ModuleCat.restrictScalars (algebraMap R S)).obj N)).symm a b
    ((hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b).mpr
      (AlgebraicGeometry.hasTorAmplitude0DJF_of_isoComplex e h2))

/-- A zero object of the derived category is perfect: the zero complex represents it. -/
public theorem isPerfect_of_isZero {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : CategoryTheory.Limits.IsZero K) :
    StacksDraft.Perfect.IsPerfect K := by
  let P : CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.zero
  have hP : CategoryTheory.Limits.IsZero P := HomologicalComplex.isZero_zero
  have hPX (i : ℤ) : CategoryTheory.Limits.IsZero (P.X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero hP
  refine ⟨P, 0, 0, ?_, ?_, ?_, ?_, ⟨hK.iso (DerivedCategory.Q.map_isZero hP)⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ => hPX i
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ => hPX i
  all_goals
    intro i
    have := ModuleCat.isZero_iff_subsingleton.mp (hPX i)
    infer_instance

end RingHom

end
