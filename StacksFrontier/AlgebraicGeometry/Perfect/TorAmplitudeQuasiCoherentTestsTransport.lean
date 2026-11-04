module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism

/-!
# Condition (2) of Stacks 08EA crosses an isomorphism

Condition (2) of Stacks 08EA — the derived tensor product of `E` with every quasi-coherent module
has no cohomology outside `[a, b]` — is transported along an isomorphism of schemes `S ≅ W`, using
that pullback along an isomorphism of schemes preserves quasi-coherence.

## Main results

* `Stacks.Cohomology.TorAmplitude.isQuasicoherent_modulePullback_schemeIso`: the degreewise
  pullback along an isomorphism of schemes preserves quasi-coherence.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.derivedPullback_schemeIso`:
  **condition (2) of Stacks 08EA crosses an isomorphism of schemes**, at the same interval.

## References

* [Stacks Project, Lemma 36.10.3 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StrictlyPerfect RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackAlongIso
open Stacks.Cohomology.TransportAlongIso (ringedSpaceIsoOfSchemeIso)

namespace Stacks.Cohomology.TorAmplitude

open _root_.AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Degreewise pullback along an isomorphism of schemes preserves quasi-coherence.** -/
theorem isQuasicoherent_modulePullback_schemeIso {S W : Scheme.{u}} (ψ : S ≅ W)
    (G : OXMod.{u, u} S.toRingedSpace) (hG : G.IsQuasicoherent) :
    ((modulePullback (ringedSpaceIsoOfSchemeIso ψ).inv).obj G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback ψ.inv).app G)
    (@Scheme.Modules.isQuasicoherent_restrictFunctor W S ψ.inv inferInstance G hG)

variable {S W : Scheme.{u}} (ψ : S ≅ W)

/-- **Condition (2) of Stacks 08EA crosses an isomorphism of schemes**, at the same interval:
if the derived tensor product of `E` with every quasi-coherent module on `W` has no cohomology
outside `[a, b]`, then the same holds for the transport of `E` to `S`. -/
theorem HasTorAmplitudeOnQuasicoherent.derivedPullback_schemeIso
    (E : DerivedCategory (OXMod.{u, u} W.toRingedSpace)) (a b : ℤ)
    (h : HasTorAmplitudeOnQuasicoherent W.toRingedSpace E a b) :
    HasTorAmplitudeOnQuasicoherent S.toRingedSpace
      ((derivedPullback (ringedSpaceIsoOfSchemeIso ψ).hom).obj E) a b := by
  set e := ringedSpaceIsoOfSchemeIso ψ
  intro G hG i hi
  set G' := (modulePullback e.inv).obj G
  have hG'qc : G'.IsQuasicoherent := isQuasicoherent_modulePullback_schemeIso ψ G hG
  set Z : DerivedCategory (OXMod.{u, u} W.toRingedSpace) :=
    ((derTensor W.toRingedSpace).tensor.obj E).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} W.toRingedSpace) 0).obj G')
  have h0 : IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} W.toRingedSpace) i).obj Z) := h G' hG'qc i hi
  have h1 : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} S.toRingedSpace) i).obj
      ((derivedPullback e.hom).obj Z)) :=
    IsZero.of_iso ((modulePullback e.hom).map_isZero h0)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} S.toRingedSpace) i).mapIso
          ((derivedPullbackIsoMapDerivedCategory e).app Z) ≪≫
        (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (modulePullback e.hom) i).app Z)
  refine IsZero.of_iso h1 ((DerivedCategory.homologyFunctor
    (OXMod.{u, u} S.toRingedSpace) i).mapIso ?_)
  refine ?_ ≪≫ ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso e.hom).app
    (E, (DerivedCategory.singleFunctor (OXMod.{u, u} W.toRingedSpace) 0).obj G')).symm
  refine ((derTensor S.toRingedSpace).tensor.obj
    ((derivedPullback e.hom).obj E)).mapIso ?_
  refine ?_ ≪≫ ((derivedPullbackIsoMapDerivedCategory e).app _ ≪≫
    ((modulePullback e.hom).mapDerivedCategorySingleFunctor 0).app G').symm
  exact (DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0).mapIso
    ((Stacks.DerivedPullback.Composition.modulePullbackComp e.hom e.inv).app G ≪≫
      eqToIso (by rw [e.hom_inv_id]) ≪≫ (modulePullbackId S.toRingedSpace).app G).symm

end Stacks.Cohomology.TorAmplitude

end
