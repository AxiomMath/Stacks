module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.FpqcTorAmplitude
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcQuasicoherence
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of a derived object and an fpqc covering of schemes

Let `{f_i : Y_i ⟶ X}` be an fpqc covering of schemes and let `E` be an object of `D(𝒪_X)`.
Stacks 09UG says that `E` is perfect if and only if every derived pullback `Lf_i^*E` is perfect.

## Main results

All in the namespace `Stacks.Cohomology.PerfectComplexes.FpqcDescent`:

* `forall_isPerfect_derivedPullback_of_isPerfect`: the derived pullback of a perfect object to
  every member of a family of morphisms of schemes is perfect.
* `isQuasicoherent_homology_of_forall_isPerfect_derivedPullback`: if every `Lf_i^*E` is perfect,
  the cohomology sheaves of `E` are quasi-coherent.
* `isPerfect_of_forall_isPerfect_derivedPullback`: if every `Lf_i^*E` is perfect, `E` is perfect.
* `isPerfect_iff_forall_isPerfect_derivedPullback`: `E` is perfect if and only if every
  `Lf_i^*E` is perfect.

## The proof

Pullback preserves perfectness (Stacks 09UA). Conversely, let every `Lf_i^*E` be perfect. Each
`Lf_i^*E` is pseudo-coherent, so its cohomology sheaves are quasi-coherent (Stacks 08E5); the
members of the covering are flat, so `H^p(Lf_i^*E) ≅ f_i^*H^p(E)`, and quasi-coherence descends
along an fpqc covering, `Stacks.Descent.isQuasicoherent_of_pullback_fpqc`. So `E ∈ D_QCoh(𝒪_X)`,
and pseudo-coherence descends (Stacks 09UE, in the form
`Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_forall_fpqc`), as does
locally finite Tor dimension (Stacks 09UD, in the form
`locallyHasFiniteTorDimension_of_forall_isPerfect_derivedPullback` of the namespace above).
A pseudo-coherent object of locally finite Tor dimension is perfect (Stacks 08CQ).

## Implementation notes

An fpqc covering of `X` is a family of morphisms of schemes whose associated presieve lies in
`AlgebraicGeometry.Scheme.fpqcPrecoverage X`, the fpqc precoverage of Mathlib. The forward
implication needs nothing about the family, so it is stated for an arbitrary one.

The derived pullback is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`
along the underlying morphism of ringed spaces, and perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect` read at the underlying ringed space, both at
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 09UG](https://stacks.math.columbia.edu/tag/09UG)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 09UD](https://stacks.math.columbia.edu/tag/09UD)
* [Stacks Project, Tag 09UE](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

namespace Stacks.Cohomology.PerfectComplexes.FpqcDescent

universe u v

attribute [local instance 2000] HasDerivedCategory.standard

section Forward

-- `forall_isPerfect_derivedPullback_of_isPerfect` is stated at the standard `Abelian` instance
-- `SheafOfModules.instAbelian` on sheaves of modules, not at the second instance
-- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` the imports below bring.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **Derived pullback preserves perfectness, member by member.** If `E ∈ D(𝒪_X)` is perfect
then the derived pullback `Lf_i^*E` is perfect for every member of a family of morphisms of
schemes `{f_i : Y_i ⟶ X}`, in particular for every member of an fpqc covering.

Derived pullback preserves perfectness along an arbitrary morphism of ringed spaces (Stacks
09UA), so no hypothesis on the family is needed. -/
@[sga "6 IV 2.7" "special case"]
public theorem forall_isPerfect_derivedPullback_of_isPerfect {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : IsPerfect (X := X.toRingedSpace) E) (i : I) :
    IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (f i).toLRSHom.toShHom E hE

end Forward

/-- A perfect object of `D(𝒪_X)` is pseudo-coherent, as a ringed-space object. -/
private theorem isPseudoCoherent'_of_isPerfect {X : RingedSpace.{u, u}}
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsPerfect E) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent E :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)

/-- A perfect object of `D(𝒪_X)` is `m`-pseudo-coherent for every `m`. -/
public theorem isPseudoCoherentFrom_of_isPerfect {X : RingedSpace.{u, u}}
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsPerfect E) (m : ℤ) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom E m :=
  (AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall E).1
    (isPseudoCoherent'_of_isPerfect E hE) m

/-- **The cohomology sheaves of an object whose pullbacks to an fpqc covering are perfect are
quasi-coherent.** Each `Lf_i^*E` is pseudo-coherent, hence has quasi-coherent cohomology sheaves
(Stacks 08E5); flatness of `f_i` gives `H^p(Lf_i^*E) ≅ f_i^*H^p(E)`, and quasi-coherence descends
along an fpqc covering. -/
public theorem isQuasicoherent_homology_of_forall_isPerfect_derivedPullback {X : Scheme.{u}}
    {I : Type v} (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : ∀ i, IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E)) (p : ℤ) :
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) p).obj E).IsQuasicoherent := by
  refine Stacks.Descent.isQuasicoherent_of_pullback_fpqc f hf _ fun i => ?_
  have hflat : Flat (f i) :=
    Stacks.Cohomology.PseudoCoherence.FpqcDescent.flat_of_mem_fpqcPrecoverage Y f hf i
  exact (SheafOfModules.isQuasicoherent (Y i).ringCatSheaf).prop_of_iso
    (AlgebraicGeometry.RingedSpace.derivedPullbackHomologyIso (f i).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (f i)) p E)
    (AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent (Y i) _
      (isPseudoCoherent'_of_isPerfect _ (hE i)) p)

/-- **The converse of Stacks 09UG.** Let `{f_i : Y_i ⟶ X}` be an fpqc covering of schemes and
let `E ∈ D(𝒪_X)`. If every derived pullback `Lf_i^*E` is perfect, then `E` is perfect. -/
public theorem isPerfect_of_forall_isPerfect_derivedPullback {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : ∀ i, IsPerfect (X := (Y i).toRingedSpace)
      ((derivedPullback (f i).toLRSHom.toShHom).obj E)) :
    IsPerfect (X := X.toRingedSpace) E := by
  have hEi : ∀ (i : I) (m : ℤ), AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom
      (X := (Y i).toRingedSpace) ((derivedPullback (f i).toLRSHom.toShHom).obj E) m :=
    fun i => isPseudoCoherentFrom_of_isPerfect _ (hE i)
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E :=
    (AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall E).2 fun m =>
      Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_forall_fpqc Y f hf E
        (isQuasicoherent_homology_of_forall_isPerfect_derivedPullback Y f hf E hE) m
        fun i => hEi i m
  exact isPerfect_of_isPseudoCoherent_of_forall_isPerfect_derivedPullback Y f hf E
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).2 hpc) hE

/-- **Stacks 09UG.** Let `{f_i : Y_i ⟶ X}` be an fpqc covering of schemes and let
`E ∈ D(𝒪_X)`. Then `E` is perfect if and only if each derived pullback `Lf_i^*E` is perfect. -/
@[stacks 09UG]
public theorem isPerfect_iff_forall_isPerfect_derivedPullback {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    IsPerfect (X := X.toRingedSpace) E ↔
      ∀ i, IsPerfect (X := (Y i).toRingedSpace)
        ((derivedPullback (f i).toLRSHom.toShHom).obj E) :=
  ⟨fun hE i => forall_isPerfect_derivedPullback_of_isPerfect Y f E hE i,
    isPerfect_of_forall_isPerfect_derivedPullback Y f hf E⟩

end Stacks.Cohomology.PerfectComplexes.FpqcDescent

end
