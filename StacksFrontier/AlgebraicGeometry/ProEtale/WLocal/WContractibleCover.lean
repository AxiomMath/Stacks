module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleTFAE
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WLocalIndEtaleSquare
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Profinite.Characterization
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Faithfully flat ind-étale covers by w-contractible rings

Every commutative ring admits a faithfully flat ind-étale map to a w-contractible commutative
ring.

The cover is built in two steps. A ring map inducing algebraic residue field extensions admits a
square of faithfully flat ind-étale extensions with w-local spectra, and applying that to the
identity of `A` produces a faithfully flat ind-étale `A → C` with `Spec C` w-local and the local
rings of `C` at its maximal ideals strictly henselian. What may still fail for `C` is extremal
disconnectedness of `π₀(Spec C)`; a quasi-compact Hausdorff space is covered by an extremally
disconnected one, and realizing that cover over `π₀(Spec C)` by an ind-Zariski algebra `C → D`
exhibits `Spec D` as the fibre product `Spec C ×_{π₀(Spec C)} T`. Such a fibre product of a
w-local space is w-local, its closed points are exactly the points over the closed points of
`Spec C` — so the local rings of `D` at its maximal ideals are again strictly henselian — and
`π₀(Spec D)` is homeomorphic to `T`. The three conditions characterizing w-contractibility then
hold for `D`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_indZariski_wLocal_of_profinite_component_cover`: a profinite
  cover of `π₀(Spec C)` is realized by a faithfully flat ind-Zariski extension with w-local
  spectrum, matching closed points, and component space the given cover.
* `AlgebraicGeometry.ProEtale.strictlyHenselianLocalRing_of_isIndZariski_of_closedPoints`: strict
  henselianity of the local rings at maximal ideals passes along such an extension.
* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_ind_etale_wContractible`: the cover.

## Implementation notes

The cartesian square realizing a profinite space over a component space is stated in a universe
that may exceed those of its two inputs, so its corners appear through `ULift`; since all the
rings and spaces here share one universe, the square is transported to the un-lifted fibre
product by an explicit homeomorphism.

## References

* [Stacks Project, Tag 096C](https://stacks.math.columbia.edu/tag/096C)
* [Stacks Project, Tag 097D](https://stacks.math.columbia.edu/tag/097D)
* [Stacks Project, Tag 0983](https://stacks.math.columbia.edu/tag/0983)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

universe u

/-- **Stacks 097D and 096C combined.** Let `Spec C` be w-local and let `T` be a profinite space
with a continuous surjection onto `π₀(Spec C)`. Then `T` is realized by a faithfully flat
ind-Zariski algebra `C → D`: the spectrum of `D` is the fibre product
`Spec C ×_{π₀(Spec C)} T`, hence w-local with closed points exactly the points over the closed
points of `Spec C`, and `π₀(Spec D)` is homeomorphic to `T`. Being a fibre product, a point of
`Spec D` is determined by its images in `Spec C` and in `T`. -/
theorem exists_indZariski_wLocal_of_profinite_component_cover (C : Type u) [CommRing C]
    [WLocalSpace (PrimeSpectrum C)] (T : Type u) [TopologicalSpace T] (hT : IsProfiniteStacks T)
    (f : C(T, ConnectedComponents (PrimeSpectrum C))) (hfsurj : Function.Surjective f) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D) (g : C(PrimeSpectrum D, T)),
      (algebraMap C D).FaithfullyFlat ∧
        IsIndZariski.{u, u, u} C D ∧
          WLocalSpace (PrimeSpectrum D) ∧
            Nonempty (ConnectedComponents (PrimeSpectrum D) ≃ₜ T) ∧
              closedPoints (PrimeSpectrum D) =
                PrimeSpectrum.comap (algebraMap C D) ⁻¹' closedPoints (PrimeSpectrum C) ∧
                Function.Injective
                  fun p : PrimeSpectrum D => (PrimeSpectrum.comap (algebraMap C D) p, g p) := by
  classical
  obtain ⟨D, hD, algCD, hCDind, g, e, -, hpb⟩ :=
    exists_indZariski_of_profinite_component_map C T hT f
  let : CommRing D := hD
  let : Algebra C D := algCD
  let S : ProfiniteBaseChangeOfComponentMap.{u} :=
    { X := TopCat.of (PrimeSpectrum C)
      T := TopCat.of T
      spectralSpace := inferInstance
      profinite := hT
      toConnectedComponents := TopCat.ofHom f }
  let : WLocalSpace S.X := ‹WLocalSpace (PrimeSpectrum C)›
  let : WLocalSpace S.Y := wLocalSpace_pullback S
  let fLift : TopCat.of (ULift.{u, u} (PrimeSpectrum C)) ⟶
      TopCat.of (ULift.{u, u} (ConnectedComponents (PrimeSpectrum C))) :=
    TopCat.ofHom ⟨fun x => ULift.up (ConnectedComponents.mk x.down),
      continuous_uliftUp.comp (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩
  let gLift : TopCat.of (ULift.{u, u} T) ⟶
      TopCat.of (ULift.{u, u} (ConnectedComponents (PrimeSpectrum C))) :=
    TopCat.ofHom ⟨fun t => ULift.up (f t.down),
      continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩
  let unlift :
      {p : ULift.{u, u} (PrimeSpectrum C) × ULift.{u, u} T // fLift.hom p.1 = gLift.hom p.2} ≃ₜ
        {p : PrimeSpectrum C × T //
          S.componentMap.hom p.1 = S.toConnectedComponents.hom p.2} :=
    (Homeomorph.ulift.prodCongr Homeomorph.ulift).subtype (fun p => by
      show (ULift.up (ConnectedComponents.mk p.1.down) = ULift.up (f p.2.down)) ↔
        ConnectedComponents.mk p.1.down = f p.2.down
      exact ULift.up_inj)
  let eD : PrimeSpectrum D ≃ₜ S.Y :=
    (TopCat.homeoOfIso hpb.isoPullback).trans
      ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift)).trans
        (unlift.trans (TopCat.homeoOfIso
          (TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents)).symm))
  have heD (p : PrimeSpectrum D) :
      S.toX (eD p) = PrimeSpectrum.comap (algebraMap C D) p := by
    show pullback.fst S.componentMap S.toConnectedComponents
      ((TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents).inv
        (unlift ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift))
          ((TopCat.homeoOfIso hpb.isoPullback) p)))) = _
    rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]
    calc
      _ = (pullback.fst fLift gLift (hpb.isoPullback.hom p)).down := by
        show ((TopCat.pullbackIsoProdSubtype fLift gLift).hom
          (hpb.isoPullback.hom p)).1.1.down = _
        rw [TopCat.pullbackIsoProdSubtype_hom_apply]
      _ = PrimeSpectrum.comap (algebraMap C D) p := by
        have hfst := ConcreteCategory.congr_hom hpb.isoPullback_hom_fst p
        change pullback.fst fLift gLift (hpb.isoPullback.hom p) =
          ULift.up (PrimeSpectrum.comap (algebraMap C D) p) at hfst
        exact congrArg ULift.down hfst
  have hclosedIff {z : PrimeSpectrum D} :
      IsClosed ({eD z} : Set S.Y) ↔ IsClosed ({z} : Set (PrimeSpectrum D)) := by
    simpa using eD.isClosed_image (s := {z})
  have hclosedEq : closedPoints (PrimeSpectrum D) =
      PrimeSpectrum.comap (algebraMap C D) ⁻¹' closedPoints (PrimeSpectrum C) := by
    refine Set.ext fun z => ?_
    have h1 : z ∈ closedPoints (PrimeSpectrum D) ↔ eD z ∈ closedPoints S.Y := by
      rw [mem_closedPoints_iff, mem_closedPoints_iff]
      exact hclosedIff.symm
    have h2 : eD z ∈ closedPoints S.Y ↔ S.toX (eD z) ∈ closedPoints S.X := by
      rw [closedPoints_pullback S]
      exact Iff.rfl
    rw [h1, h2, Set.mem_preimage, heD z]
  have hcomapSurj : Function.Surjective (PrimeSpectrum.comap (algebraMap C D)) := by
    intro p
    obtain ⟨t, ht⟩ := hfsurj (ConnectedComponents.mk p)
    let pC : TopCat.of PUnit ⟶ TopCat.of (ULift.{u} (PrimeSpectrum C)) :=
      TopCat.ofHom ⟨fun _ => ULift.up p, continuous_const⟩
    let pT : TopCat.of PUnit ⟶ TopCat.of (ULift.{u} T) :=
      TopCat.ofHom ⟨fun _ => ULift.up t, continuous_const⟩
    refine ⟨(hpb.lift pC pT ?_).hom PUnit.unit,
      congrArg ULift.down (ConcreteCategory.congr_hom (hpb.lift_fst pC pT ?_) PUnit.unit)⟩ <;>
      (ext _; simpa [pC, pT] using ht.symm)
  have hginj : Function.Injective
      fun p : PrimeSpectrum D => (PrimeSpectrum.comap (algebraMap C D) p, g p) := by
    intro p p' hpp'
    let kp : TopCat.of PUnit ⟶ TopCat.of (PrimeSpectrum D) :=
      TopCat.ofHom ⟨fun _ => p, continuous_const⟩
    let kp' : TopCat.of PUnit ⟶ TopCat.of (PrimeSpectrum D) :=
      TopCat.ofHom ⟨fun _ => p', continuous_const⟩
    have hk : kp = kp' :=
      hpb.hom_ext
        (TopCat.hom_ext (ContinuousMap.ext fun _ =>
          congrArg ULift.up (congrArg Prod.fst hpp')))
        (TopCat.hom_ext (ContinuousMap.ext fun _ =>
          congrArg ULift.up (congrArg Prod.snd hpp')))
    exact ConcreteCategory.congr_hom hk PUnit.unit
  exact ⟨D, inferInstance, inferInstance, g,
    faithfullyFlat_of_comap_surjective_of_identifiesLocalRings C D
      (identifiesLocalRings_of_isIndZariski C D hCDind) hcomapSurj,
    hCDind, wLocalSpace_of_homeomorph eD, ⟨e⟩, hclosedEq, hginj⟩

/-- Strict henselianity of the local rings at maximal ideals passes to an ind-Zariski extension
whose closed points lie over closed points: such an extension identifies local rings, so the
local ring at a maximal ideal of the extension is the local ring of the base at a maximal
ideal. -/
theorem strictlyHenselianLocalRing_of_isIndZariski_of_closedPoints (C D : Type u) [CommRing C]
    [CommRing D] [Algebra C D] (hCD : IsIndZariski.{u, u, u} C D)
    (hclosed : closedPoints (PrimeSpectrum D) ⊆
      PrimeSpectrum.comap (algebraMap C D) ⁻¹' closedPoints (PrimeSpectrum C))
    (hCsh : ∀ (m : Ideal C) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m))
    (m : Ideal D) [hm : m.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime m) := by
  let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
  have : (m.comap (algebraMap C D)).IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap (algebraMap C D) p)).mp
      (mem_closedPoints_iff.mp (hclosed (mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hm))))
  let : StrictlyHenselianLocalRing (Localization.AtPrime (m.comap (algebraMap C D))) :=
    hCsh (m.comap (algebraMap C D))
  exact strictlyHenselianLocalRing_of_ringEquiv
    (RingEquiv.ofBijective
      (Localization.localRingHom (m.comap (algebraMap C D)) m (algebraMap C D) rfl)
      (identifiesLocalRings_of_isIndZariski C D hCD m))

/-- **Stacks 0983.** Every commutative ring has a faithfully flat ind-étale map to a
w-contractible ring. -/
@[stacks 0983]
theorem exists_faithfullyFlat_ind_etale_wContractible (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧
        (ObjectProperty.ind.{u}
          (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom f)) ∧
        ProetaleWContractible.IsWContractible.{u, u} D) := by
  classical
  obtain ⟨C, Dsq, hCR, _hDsqR, algAC, _algADsq, _algBDsq, _algCDsq, _htowerABD, _htowerACD,
      hACff, hACet, _hBDff, _hBDind, hCw, _hDsqw, _hCDmap, _hclosedDsq, _hsurjA, _hsurjB,
      hCsh⟩ :=
    exists_wLocal_faithfullyFlat_indEtale_extensions A A
      (isAlgebraic_residueField_specMap A A fun q _ =>
        (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A A inferInstance
          (q.comap (algebraMap A A)) q rfl).2)
  let : CommRing C := hCR
  let : Algebra A C := algAC
  let : WLocalSpace (PrimeSpectrum C) := hCw
  have : T2Space (ConnectedComponents (PrimeSpectrum C)) :=
    (connectedComponents_isProfinite (PrimeSpectrum C)).1
  obtain ⟨T, _, _, _, hTED, π, hπcont, hπsurj⟩ :=
    exists_extremallyDisconnected_cover (ConnectedComponents (PrimeSpectrum C))
  have hTprof : IsProfiniteStacks T :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected T).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨D, hD, algCD, -, hCDff, hCDind, hDw, ⟨e⟩, hDclosed, -⟩ :=
    exists_indZariski_wLocal_of_profinite_component_cover C T hTprof ⟨π, hπcont⟩ hπsurj
  let : CommRing D := hD
  let : Algebra C D := algCD
  let : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have hDsh : ∀ (m : Ideal D) [m.IsMaximal],
      StrictlyHenselianLocalRing (Localization.AtPrime m) := fun m _ =>
    strictlyHenselianLocalRing_of_isIndZariski_of_closedPoints C D hCDind hDclosed.subset hCsh m
  have hDED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) := by
    let : ExtremallyDisconnected T := hTED
    exact extremallyDisconnected_of_homeo e.symm
  have hDprops : WLocalSpace (PrimeSpectrum D) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) ∧
        ∀ (m : Ideal D) [m.IsMaximal],
          StrictlyHenselianLocalRing (Localization.AtPrime m) :=
    ⟨hDw, hDED, hDsh⟩
  exact ⟨D, inferInstance, algebraMap A D,
    RingHom.FaithfullyFlat.stableUnderComposition _ _ hACff hCDff,
    indEtaleUnder_of_indEtale A D (StacksDraft.indEtale_comp
      (indEtale_of_indEtaleUnder A C hACet) (indEtale_of_isIndZariski C D hCDind)),
    ((wContractible_tfae D).out 3 1).mp hDprops⟩

end AlgebraicGeometry.ProEtale

end
