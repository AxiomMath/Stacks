module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Flatness
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Profinite.Characterization
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Faithfully flat ind-Zariski covers by w-local rings

Every commutative ring has a faithfully flat ind-Zariski extension whose prime spectrum is
w-local and whose space of connected components is extremally disconnected.

## Main results

* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indZariski_wLocal_extremallyDisconnected`:
  the cover.

## Implementation notes

The cover is built in two steps. The w-localization `A → A_w` of Tag 0975 is faithfully flat and
ind-Zariski with `Spec A_w` w-local, but `π₀(Spec A_w)` need not be extremally disconnected; Tag
090D covers that quasi-compact Hausdorff space by an extremally disconnected one `T`, and Tag 097D
realizes `T` over `π₀(Spec A_w)` by an ind-Zariski algebra `A_w → B` whose spectrum is the fibre
product `Spec A_w ×_{π₀(Spec A_w)} T` and whose component space is `T`. The fibre product of a
w-local space along a profinite map to its component space is w-local by Tag 096C, so `Spec B` is
w-local, and `π₀(Spec B) ≅ T` is extremally disconnected. Faithful flatness of `A_w → B` comes
from an ind-Zariski map identifying local rings together with surjectivity of `Spec B → Spec A_w`,
which is read off the cartesian square from the surjectivity of `T → π₀(Spec A_w)`.

The two assertions about `Spec B` are condition (3) of Tag 09AZ, so the target ring satisfies all
of the equivalent conditions there.

The cartesian square of Tag 097D is stated in a universe that may exceed those of its two inputs,
so its corners appear through `ULift`; since all the rings and spaces here share one universe,
the square is transported to the un-lifted fibre product of Tag 096C by an explicit
homeomorphism.

## References

* [Stacks Project, Tag 09B0](https://stacks.math.columbia.edu/tag/09B0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

universe u

/-- **Stacks 09B0.** Every ring has a faithfully flat ind-Zariski extension whose spectrum is
w-local and whose space of connected components is extremally disconnected. -/
@[stacks 09B0]
theorem exists_faithfullyFlat_indZariski_wLocal_extremallyDisconnected (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      (algebraMap A B).FaithfullyFlat ∧
        IsIndZariski.{u, u, u} A B ∧
          WLocalSpace (PrimeSpectrum B) ∧
            ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum B)) := by
  classical
  have hmap : algebraMap A (stratificationColimitRing (A := A)) =
      stratificationColimitAlgebraMap (A := A) := RingHom.algebraMap_toAlgebra _
  have hAwff : (algebraMap A (stratificationColimitRing (A := A))).FaithfullyFlat :=
    hmap ▸ stratificationColimit_faithfullyFlat (A := A)
  have : WLocalSpace (PrimeSpectrum (stratificationColimitRing (A := A))) :=
    stratificationLimitScheme_wLocal (A := A)
  have : T2Space (ConnectedComponents (PrimeSpectrum (stratificationColimitRing (A := A)))) :=
    (connectedComponents_isProfinite _).1
  -- Cover `π₀(Spec A_w)` by an extremally disconnected quasi-compact Hausdorff space.
  obtain ⟨T, _, _, _, hTED, π, hπcont, hπsurj⟩ := exists_extremallyDisconnected_cover
    (ConnectedComponents (PrimeSpectrum (stratificationColimitRing (A := A))))
  have hTprof : IsProfiniteStacks T :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected T).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨B, hB, algAwB, hAwBInd, g, e, -, hpb⟩ :=
    exists_indZariski_of_profinite_component_map (stratificationColimitRing (A := A)) T hTprof
      ⟨π, hπcont⟩
  let : CommRing B := hB
  let : Algebra (stratificationColimitRing (A := A)) B := algAwB
  let : Algebra A B :=
    ((algebraMap (stratificationColimitRing (A := A)) B).comp
      (algebraMap A (stratificationColimitRing (A := A)))).toAlgebra
  let : IsScalarTower A (stratificationColimitRing (A := A)) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- The fibre product of Tag 096C, and the identification of `Spec B` with it.
  let S : ProfiniteBaseChangeOfComponentMap.{u} :=
    { X := TopCat.of (PrimeSpectrum (stratificationColimitRing (A := A)))
      T := TopCat.of T
      spectralSpace := inferInstance
      profinite := hTprof
      toConnectedComponents := TopCat.ofHom ⟨π, hπcont⟩ }
  let : WLocalSpace S.X := ‹WLocalSpace (PrimeSpectrum (stratificationColimitRing (A := A)))›
  let : WLocalSpace S.Y := wLocalSpace_pullback S
  let fLift : TopCat.of (ULift.{u, u} (PrimeSpectrum (stratificationColimitRing (A := A)))) ⟶
      TopCat.of (ULift.{u, u}
        (ConnectedComponents (PrimeSpectrum (stratificationColimitRing (A := A))))) :=
    TopCat.ofHom ⟨fun x => ULift.up (ConnectedComponents.mk x.down),
      continuous_uliftUp.comp
        (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩
  let gLift : TopCat.of (ULift.{u, u} T) ⟶ TopCat.of (ULift.{u, u}
      (ConnectedComponents (PrimeSpectrum (stratificationColimitRing (A := A))))) :=
    TopCat.ofHom ⟨fun t => ULift.up (π t.down),
      continuous_uliftUp.comp (hπcont.comp continuous_uliftDown)⟩
  let unlift :
      {p : ULift.{u, u} (PrimeSpectrum (stratificationColimitRing (A := A))) × ULift.{u, u} T //
          fLift.hom p.1 = gLift.hom p.2} ≃ₜ
        {p : PrimeSpectrum (stratificationColimitRing (A := A)) × T //
          S.componentMap.hom p.1 = S.toConnectedComponents.hom p.2} :=
    (Homeomorph.ulift.prodCongr Homeomorph.ulift).subtype (fun p => by
      show (ULift.up (ConnectedComponents.mk p.1.down) = ULift.up (π p.2.down)) ↔
        ConnectedComponents.mk p.1.down = π p.2.down
      exact ULift.up_inj)
  let eB : PrimeSpectrum B ≃ₜ S.Y :=
    (TopCat.homeoOfIso hpb.isoPullback).trans
      ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift)).trans
        (unlift.trans (TopCat.homeoOfIso
          (TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents)).symm))
  have hBw : WLocalSpace (PrimeSpectrum B) := wLocalSpace_of_homeomorph eB
  have hBcomponents : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum B)) :=
    extremallyDisconnected_of_homeo e.symm
  -- Faithful flatness of `A_w → B`.
  have hcomapSurj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap (stratificationColimitRing (A := A)) B)) := by
    intro p
    obtain ⟨t, ht⟩ := hπsurj (ConnectedComponents.mk p)
    let pA : TopCat.of PUnit ⟶
        TopCat.of (ULift.{u} (PrimeSpectrum (stratificationColimitRing (A := A)))) :=
      TopCat.ofHom ⟨fun _ => ULift.up p, continuous_const⟩
    let pT : TopCat.of PUnit ⟶ TopCat.of (ULift.{u} T) :=
      TopCat.ofHom ⟨fun _ => ULift.up t, continuous_const⟩
    refine ⟨(hpb.lift pA pT (by ext _; simpa [pA, pT] using ht.symm)).hom PUnit.unit, ?_⟩
    exact congrArg ULift.down (ConcreteCategory.congr_hom
      (hpb.lift_fst pA pT (by ext _; simpa [pA, pT] using ht.symm)) PUnit.unit)
  have hBff : (algebraMap (stratificationColimitRing (A := A)) B).FaithfullyFlat :=
    faithfullyFlat_of_comap_surjective_of_identifiesLocalRings _ B
      (identifiesLocalRings_of_isIndZariski _ B hAwBInd) hcomapSurj
  refine ⟨B, inferInstance, inferInstance, ?_, ?_, hBw, hBcomponents⟩
  · exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hAwff hBff
  · exact Algebra.IsIndZariski.comp A (stratificationColimitRing (A := A)) B
      stratificationColimit_isIndZariski hAwBInd

end AlgebraicGeometry.ProEtale

end
