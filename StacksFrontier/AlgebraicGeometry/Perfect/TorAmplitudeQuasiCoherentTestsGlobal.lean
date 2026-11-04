module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsRestrict
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08EA on a quasi-separated scheme

Let `X` be a quasi-separated scheme and `E` an object of `D_QCoh(𝒪_X)`. Then `E` has Tor
amplitude in `[a, b]` if and only if `H^i(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every
quasi-coherent `𝒪_X`-module `ℱ`.

The implication (1) ⟹ (2) is specialisation of the quantifier and is
`Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude`. This file
assembles the converse out of the four steps the source takes.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_derivedRestrictModules`: restriction to an open
  subscheme preserves quasi-coherence of the cohomology sheaves.
* `AlgebraicGeometry.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent` — **Stacks 08EA, (2)
  implies (1).**
* `AlgebraicGeometry.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent` — **Stacks 08EA.**

## Implementation notes

The four steps and the declarations carrying them:

1. Tor amplitude in a fixed interval is local on an open covering, so it is enough to prove it
   on each member of the covering by affine opens —
   `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`.
2. Condition (2) restricts to an affine open of a quasi-separated scheme, because `j_*` makes
   `QCoh(𝒪_X) → QCoh(𝒪_U)` essentially surjective (Stacks 01LC) —
   `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.restrictModules`.
3. Condition (2), and quasi-coherence of the cohomology sheaves, cross the isomorphism
   `U ≅ Spec Γ(U, 𝒪_U)` —
   `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.derivedPullback_schemeIso` and
   Stacks 08DW part (1), `Stacks.Duality.isQuasicoherent_homology_derivedPullback'`.
4. On `Spec A` condition (2) implies Tor amplitude, by Stacks 06Z0 and the affine criterion
   Stacks 08E9 — `AlgebraicGeometry.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_spec`.
   Tor amplitude then comes back across the isomorphism by
   `Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff`.

`a ≤ b` is not used. The source assumes it, but no step here does: the locality statement
carries the interval unchanged whatever its shape, and the affine criterion is stated without
it.

The quasi-coherence of the restricted cohomology sheaves in step 1 is the computation carried
out inline in the proof of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_iff_forall_fpqc`; it is
recorded here as a statement.

## References

* [Stacks Project, Lemma 36.10.6 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Lemma 36.10.2 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 26.24.1 (Tag 01LC)](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.TransportAlongIso (ringedSpaceIsoOfSchemeIso)

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Restriction to an open subscheme preserves quasi-coherence of the cohomology sheaves.**
Restriction commutes with the cohomology functors, and the restriction of a quasi-coherent
module is quasi-coherent. -/
theorem isQuasicoherent_homology_derivedRestrictModules {X : Scheme.{u}} (U : X.Opens)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (n : ℤ)
    (hE : ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) n).obj
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj
        E)).IsQuasicoherent := by
  have hres : ((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace U).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj
        E)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U).app _).symm
      (@Scheme.Modules.isQuasicoherent_restrictFunctor U.toScheme X U.ι inferInstance
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) hE)
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace U) n).app E).symm
    hres

/-- **Stacks 08EA, (2) implies (1), on an affine open of a quasi-separated scheme.** The
restriction of `E` to an affine open `U` has Tor amplitude in `[a, b]`. -/
private theorem hasTorAmplitude_derivedRestrictModules_of_tests {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsAffineOpen U)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent
      X.toRingedSpace E a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (X.toRingedSpace.restrict U.isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) a b := by
  have : IsAffine U.toScheme := hU
  refine (Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff
    (ringedSpaceIsoOfSchemeIso U.toScheme.isoSpec.symm) _ a b).1 ?_
  refine hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_spec _ a b (fun n => ?_) ?_
  · exact Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      U.toScheme.isoSpec.inv _
      (fun m => isQuasicoherent_homology_derivedRestrictModules U E m (hqc m)) n
  · exact Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.derivedPullback_schemeIso
      U.toScheme.isoSpec.symm _ a b
      (Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.restrictModules U E a b h)

/-- **Stacks 08EA, (2) implies (1).** Let `X` be a quasi-separated scheme and let `E` be an
object of `D_QCoh(𝒪_X)`. If `H^i(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every quasi-coherent
`𝒪_X`-module `ℱ`, then `E` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent
      X.toRingedSpace E a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b :=
  Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top X.toRingedSpace E a b
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X)
    fun U => hasTorAmplitude_derivedRestrictModules_of_tests (U : X.Opens) U.2 E a b hqc h

/-- **Stacks 08EA.** Let `X` be a quasi-separated scheme, `E` an object of `D_QCoh(𝒪_X)` and
`a ≤ b`. The following are equivalent:

1. `E` has Tor amplitude in `[a, b]`;
2. `H^i(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪_X`-module `ℱ`.

Neither direction uses `a ≤ b`. -/
@[stacks 08EA]
theorem hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent X.toRingedSpace E a b :=
  ⟨Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude E a b,
    hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent E a b hqc⟩

end AlgebraicGeometry

end
