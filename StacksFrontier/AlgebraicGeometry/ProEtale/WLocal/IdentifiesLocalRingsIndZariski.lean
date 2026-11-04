module

public import Mathlib.AlgebraicGeometry.Spec
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ProfiniteComponentRealization
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.IdentifiesLocalRingsIso
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackWLocal
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Chevalley
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# A w-local map identifying local rings is ind-Zariski

Let `A → B` be a ring map identifying local rings, with `Spec A` and `Spec B` w-local and
`Spec B → Spec A` w-local. Then `A → B` is ind-Zariski.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_of_wLocalMap_identifiesLocalRings`: the ind-Zariski
  property of such a ring map.

## Implementation notes

The proof realizes the profinite space `π₀(Spec B)` over `π₀(Spec A)` by an ind-Zariski algebra
`A → C`, so that `Spec C` is the fibre product `Spec A ×_{π₀(Spec A)} π₀(Spec B)`. That fibre
product is w-local with closed points lying over the closed points of `Spec A`, and `Spec B`
maps to it over `Spec A`; since `C` identifies local rings over `A`, that continuous map comes
from a unique algebra homomorphism `C → B`, which is w-local and bijective on connected
components, hence an isomorphism. Transporting the ind-Zariski presentation of `C` across it
gives the conclusion.

The two rings have independent universes `u` and `v`. The realization of Tag 097D produces an
algebra in `max u v`, so `B` is compared with `C` after being lifted there, and the base is
lifted as well in the one step where the full faithfulness of `Spec` on algebras identifying
local rings is applied.

## References

* [Stacks Project, Tag 097F](https://stacks.math.columbia.edu/tag/097F)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ProEtale

/-- A homeomorphism matches up the closed points of its source and target. -/
private theorem closedPoint_iff_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    x ∈ closedPoints X ↔ e x ∈ closedPoints Y :=
  (Set.ext_iff.mp e.isClosedEmbedding.preimage_closedPoints x).symm

private noncomputable def connectedComponentsHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (fun y => by
    have hs : e ⁻¹' {y} = {e.symm y} := by
      ext x
      exact e.eq_symm_apply.symm
    rw [hs]
    exact isConnected_singleton)

private noncomputable def connectedComponentsHomeomorphULift {X : Type u} [TopologicalSpace X] :
    ConnectedComponents (ULift.{v} X) ≃ₜ ULift.{v} (ConnectedComponents X) :=
  (connectedComponentsHomeomorph (Homeomorph.ulift (X := X))).trans
    (Homeomorph.ulift (X := ConnectedComponents X)).symm

private theorem connectedComponentsHomeomorphULift_mk {X : Type u} [TopologicalSpace X]
    (x : X) :
    connectedComponentsHomeomorphULift (X := X) (ConnectedComponents.mk (ULift.up x)) =
      ULift.up (ConnectedComponents.mk x) := by
  simp [connectedComponentsHomeomorphULift, connectedComponentsHomeomorph,
    Topology.IsCoinducing.connectedComponentsHomeomorph_mk]
  rfl

/-- Identifying local rings transfers along ring equivalences of the source and the target
that commute with the structure maps. -/
private theorem bijective_localRingHom_of_equiv {R S P Q : Type*} [CommRing R] [CommRing S]
    [CommRing P] [CommRing Q] (eR : R ≃+* S) (eP : P ≃+* Q) (fR : R →+* P) (fS : S →+* Q)
    (hcomm : fS.comp eR.toRingHom = eP.toRingHom.comp fR)
    (h : ∀ (q : Ideal Q) [q.IsPrime], Function.Bijective
      ⇑(Localization.localRingHom (q.comap fS) q fS rfl)) :
    ∀ (q : Ideal P) [q.IsPrime], Function.Bijective
      ⇑(Localization.localRingHom (q.comap fR) q fR rfl) := by
  intro q hq
  let qQ : Ideal Q := q.comap eP.symm.toRingHom
  let : qQ.IsPrime := Ideal.comap_isPrime _ _
  have hq' : q = qQ.comap eP.toRingHom := by
    ext x
    simp [qQ]
  have hp : q.comap fR = (qQ.comap fS).comap eR.toRingHom := by
    ext x
    rw [hq']
    exact Iff.of_eq (congrArg (· ∈ qQ) (congrFun (congrArg DFunLike.coe hcomm) x).symm)
  let eLocP := Localization.localRingEquiv q qQ eP hq'
  let eLocR := Localization.localRingEquiv (q.comap fR) (qQ.comap fS) eR hp
  have hEq : eLocP.toRingHom.comp (Localization.localRingHom (q.comap fR) q fR rfl) =
      (Localization.localRingHom (qQ.comap fS) qQ fS rfl).comp eLocR.toRingHom := by
    apply IsLocalization.ringHom_ext (q.comap fR).primeCompl
    ext x
    have hx := congrArg (fun k => k x) hcomm
    have h1 : eLocP (algebraMap P _ (fR x)) = algebraMap Q _ (eP (fR x)) :=
      Localization.localRingHom_to_map q qQ eP.toRingHom hq' _
    have h2 : eLocR (algebraMap R _ x) = algebraMap S _ (eR x) :=
      Localization.localRingHom_to_map _ _ eR.toRingHom hp x
    change eLocP (Localization.localRingHom (q.comap fR) q fR rfl (algebraMap R _ x)) =
      Localization.localRingHom (qQ.comap fS) qQ fS rfl (eLocR (algebraMap R _ x))
    rw [Localization.localRingHom_to_map, h1, h2, Localization.localRingHom_to_map]
    exact congrArg _ hx.symm
  refine (eLocP.bijective.of_comp_iff' _).mp ?_
  change Function.Bijective
    ⇑(eLocP.toRingHom.comp (Localization.localRingHom (q.comap fR) q fR rfl))
  rw [hEq]
  exact (h qQ).comp eLocR.bijective

/-- A w-local morphism between w-local affine spectra that identifies local rings
is ind-Zariski. -/
@[stacks 097F]
theorem isIndZariski_of_wLocalMap_identifiesLocalRings
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum A)]
    [WLocalSpace (PrimeSpectrum B)]
    (hlocal : Algebra.IdentifiesLocalRings A B)
    (hwlocal : IsWLocalMap (PrimeSpectrum.comap (algebraMap A B))) :
    IsIndZariski.{u, v, max u v} A B := by
  classical
  let X := PrimeSpectrum A
  let Y := PrimeSpectrum B
  let T := ConnectedComponents Y
  let fAB : C(Y, X) :=
    ⟨PrimeSpectrum.comap (algebraMap A B), PrimeSpectrum.continuous_comap _⟩
  let fCT : C(T, ConnectedComponents X) :=
    ⟨fAB.continuous.connectedComponentsMap,
      fAB.continuous.connectedComponentsMap_continuous⟩
  have hpi0 := connectedComponents_isProfinite Y
  have hTprof : IsProfiniteStacks T :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected T).2 ⟨hpi0.2.1, hpi0.1, hpi0.2.2⟩
  obtain ⟨C, _, _, hACind, gT, eT, heT, hpull⟩ :=
    exists_indZariski_of_profinite_component_map A T hTprof fCT
  let XU := ULift.{v} X
  let TU := ULift.{u} T
  let hXw : WLocalSpace XU :=
    wLocalSpace_of_homeomorph (Homeomorph.ulift (X := X))
  let : CompactSpace T := hpi0.2.1
  let : T2Space T := hpi0.1
  let : TotallyDisconnectedSpace T := hpi0.2.2
  let : TotallyDisconnectedSpace TU :=
    (Homeomorph.ulift (X := T)).symm.totallyDisconnectedSpace
  have hTUprof : IsProfiniteStacks TU :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected TU).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  let eCC := connectedComponentsHomeomorphULift (X := X)
  let fLift : TopCat.of XU ⟶ TopCat.of (ULift.{v} (ConnectedComponents X)) :=
    TopCat.ofHom ⟨fun x => ULift.up (ConnectedComponents.mk x.down),
      continuous_uliftUp.comp
        (ConnectedComponents.continuous_coe.comp continuous_uliftDown)⟩
  let gLift : TopCat.of TU ⟶ TopCat.of (ULift.{v} (ConnectedComponents X)) :=
    TopCat.ofHom ⟨fun t => ULift.up (fCT t.down),
      continuous_uliftUp.comp (fCT.continuous.comp continuous_uliftDown)⟩
  let toConn : TopCat.of TU ⟶ TopCat.of (ConnectedComponents XU) :=
    TopCat.ofHom ⟨fun t => eCC.symm (ULift.up (fCT t.down)),
      eCC.symm.continuous_toFun.comp gLift.hom.continuous⟩
  let S : ProfiniteBaseChangeOfComponentMap.{max u v} :=
    ⟨TopCat.of XU, TopCat.of TU, hXw.toSpectralSpace, hTUprof, toConn⟩
  let : WLocalSpace XU := hXw
  let : WLocalSpace S.Y :=
    wLocalSpace_pullback S
  let liftPullback :=
    { p : XU × TU // fLift.hom p.1 = gLift.hom p.2 }
  let plainPullback :=
    { p : XU × TU // S.componentMap.hom p.1 = S.toConnectedComponents.hom p.2 }
  let unlift : liftPullback ≃ₜ plainPullback := Homeomorph.setCongr (by
    ext p
    show ULift.up (ConnectedComponents.mk p.1.down) = ULift.up (fCT p.2.down) ↔
      ConnectedComponents.mk p.1 = eCC.symm (ULift.up (fCT p.2.down))
    rw [← eCC.injective.eq_iff, connectedComponentsHomeomorphULift_mk, eCC.apply_symm_apply])
  let eC : PrimeSpectrum C ≃ₜ S.Y :=
    (TopCat.homeoOfIso hpull.isoPullback).trans
      ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift)).trans
        (unlift.trans (TopCat.homeoOfIso
          (TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents)).symm))
  have heC_toX (p : PrimeSpectrum C) :
      S.toX (eC p) = ULift.up (PrimeSpectrum.comap (algebraMap A C) p) := by
    have hfst := congrArg (fun k => k p) hpull.isoPullback_hom_fst
    show pullback.fst S.componentMap S.toConnectedComponents
      ((TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents).inv
        (unlift ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift))
          ((TopCat.homeoOfIso hpull.isoPullback) p)))) = _
    rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]
    calc
      _ = pullback.fst fLift gLift (hpull.isoPullback.hom p) := by
        show ((TopCat.pullbackIsoProdSubtype fLift gLift).hom
          (hpull.isoPullback.hom p)).1.1 = _
        rw [TopCat.pullbackIsoProdSubtype_hom_apply]
      _ = ULift.up (PrimeSpectrum.comap (algebraMap A C) p) := hfst
  have heC_toT (p : PrimeSpectrum C) :
      S.toT (eC p) = ULift.up (gT p) := by
    have hsnd := congrArg (fun k => k p) hpull.isoPullback_hom_snd
    show pullback.snd S.componentMap S.toConnectedComponents
      ((TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents).inv
        (unlift ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype fLift gLift))
          ((TopCat.homeoOfIso hpull.isoPullback) p)))) = _
    rw [TopCat.pullbackIsoProdSubtype_inv_snd_apply]
    calc
      _ = pullback.snd fLift gLift (hpull.isoPullback.hom p) := by
        show ((TopCat.pullbackIsoProdSubtype fLift gLift).hom
          (hpull.isoPullback.hom p)).1.2 = _
        rw [TopCat.pullbackIsoProdSubtype_hom_apply]
      _ = ULift.up (gT p) := hsnd
  let B' := ULift.{u} B
  let eBAlg : B' ≃ₐ[A] B := ULift.algEquiv
  let eBSpec := PrimeSpectrum.homeomorphOfRingEquiv eBAlg.toRingEquiv
  let : WLocalSpace (PrimeSpectrum B') := wLocalSpace_of_homeomorph eBSpec
  have hAB' : Algebra.IdentifiesLocalRings A B' :=
    bijective_localRingHom_of_equiv (RingEquiv.refl A) eBAlg.toRingEquiv _ _
      (by ext a; exact (eBAlg.commutes a).symm) hlocal
  have hprime (p : PrimeSpectrum B') :
      PrimeSpectrum.comap (algebraMap A B') p =
        PrimeSpectrum.comap (algebraMap A B) (eBSpec p) := rfl
  let fB : TopCat.of (PrimeSpectrum B') ⟶ S.X :=
    TopCat.ofHom ⟨fun p => ULift.up (PrimeSpectrum.comap (algebraMap A B') p),
      continuous_uliftUp.comp (PrimeSpectrum.continuous_comap _)⟩
  let kB : TopCat.of (PrimeSpectrum B') ⟶ S.T :=
    TopCat.ofHom ⟨fun p => ULift.up (ConnectedComponents.mk (eBSpec p)),
      continuous_uliftUp.comp
        (ConnectedComponents.continuous_coe.comp eBSpec.continuous_toFun)⟩
  have hcompat : fB ≫ S.componentMap = kB ≫ S.toConnectedComponents := by
    ext p
    apply eCC.injective
    show eCC (ConnectedComponents.mk
        (ULift.up (PrimeSpectrum.comap (algebraMap A B') p))) =
      eCC (eCC.symm (ULift.up (fCT (ConnectedComponents.mk (eBSpec p)))))
    rw [connectedComponentsHomeomorphULift_mk, eCC.apply_symm_apply]
    rfl
  let q : TopCat.of (PrimeSpectrum B') ⟶ S.Y := pullback.lift fB kB hcompat
  have hqX (p : PrimeSpectrum B') :
      S.toX (q p) = ULift.up (PrimeSpectrum.comap (algebraMap A B') p) := by
    show ((pullback.lift fB kB hcompat) ≫
      pullback.fst S.componentMap S.toConnectedComponents).hom p = _
    rw [pullback.lift_fst]
    rfl
  have hqT (p : PrimeSpectrum B') :
      S.toT (q p) = ULift.up (ConnectedComponents.mk (eBSpec p)) := by
    show ((pullback.lift fB kB hcompat) ≫
      pullback.snd S.componentMap S.toConnectedComponents).hom p = _
    rw [pullback.lift_snd]
    rfl
  let g : C(PrimeSpectrum B', PrimeSpectrum C) :=
    ⟨fun p => eC.symm (q p), eC.symm.continuous_toFun.comp q.hom.continuous⟩
  have hg_over (p : PrimeSpectrum B') :
      PrimeSpectrum.comap (algebraMap A C) (g p) =
        PrimeSpectrum.comap (algebraMap A B') p := by
    apply ULift.up_injective
    calc
      ULift.up (PrimeSpectrum.comap (algebraMap A C) (g p)) = S.toX (eC (g p)) :=
        (heC_toX (g p)).symm
      _ = S.toX (q p) := by simp [g]
      _ = ULift.up (PrimeSpectrum.comap (algebraMap A B') p) := hqX p
  have hAClocal : Algebra.IdentifiesLocalRings A C :=
    identifiesLocalRings_of_isIndZariski A C hACind
  let A' := ULift.{max u v} A
  let : Algebra A' C := ULift.algebra' A C
  let : Algebra A' B' := ULift.algebra' A B'
  have hA'Clocal : Algebra.IdentifiesLocalRings A' C :=
    bijective_localRingHom_of_equiv ULift.ringEquiv (RingEquiv.refl C) _ _
      (by ext a; rfl) hAClocal
  have hg_over' (p : PrimeSpectrum B') :
      PrimeSpectrum.comap (algebraMap A' C) (g p) =
        PrimeSpectrum.comap (algebraMap A' B') p := by
    apply PrimeSpectrum.ext
    ext a
    exact Iff.of_eq (congrArg (fun z : PrimeSpectrum A => a.down ∈ z.asIdeal)
      (hg_over p))
  let gSpec : Spec.topObj (CommRingCat.of B') ⟶ Spec.topObj (CommRingCat.of C) :=
    TopCat.ofHom g
  have hgSpec :
      gSpec ≫ Spec.topMap (CommRingCat.ofHom (algebraMap A' C)) =
        Spec.topMap (CommRingCat.ofHom (algebraMap A' B')) := by
    ext p
    exact hg_over' p
  obtain ⟨φ, hφ, _⟩ :=
    existsUnique_algHom_of_specTopMap_over A' C B' hA'Clocal gSpec hgSpec
  let : Algebra C B' := φ.toRingHom.toAlgebra
  let : IsScalarTower A C B' :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes' (ULift.up a)).symm
  have hSpecAlg : PrimeSpectrum.comap (algebraMap C B') = g := by
    show PrimeSpectrum.comap φ.toRingHom = g
    funext p
    exact congrArg (fun k => k p) hφ
  have hlocalCB :=
    identifiesLocalRings_of_left_of_comp
      A C B' hAClocal hAB'
  let : WLocalSpace (PrimeSpectrum C) := wLocalSpace_of_homeomorph eC
  have hwlocalCB : IsWLocalMap (PrimeSpectrum.comap (algebraMap C B')) := by
    rw [hSpecAlg]
    refine ⟨⟨g.continuous, ?_⟩, ?_⟩
    · intro U hU hUc
      simpa [← hSpecAlg] using
        PrimeSpectrum.isCompact_preimage_comap_of_isOpen
          (algebraMap C B') U hU hUc
    · intro p hp
      have hpB : eBSpec p ∈ closedPoints Y := (closedPoint_iff_homeomorph eBSpec p).mp hp
      have hpX : PrimeSpectrum.comap (algebraMap A B) (eBSpec p) ∈ closedPoints X :=
        hwlocal.closedPoints_subset_preimage_closedPoints hpB
      have hqY : q p ∈ closedPoints S.Y := by
        rw [closedPoints_pullback S]
        show S.toX (q p) ∈ closedPoints XU
        rw [hqX, hprime p]
        exact (closedPoint_iff_homeomorph
          ((Homeomorph.ulift (X := X)).symm) _).mp hpX
      exact (closedPoint_iff_homeomorph eC (g p)).mpr (by simpa [g] using hqY)
  let eBcc := connectedComponentsHomeomorph eBSpec
  have hcomponents : Function.Bijective
      (PrimeSpectrum.continuous_comap (algebraMap C B')).connectedComponentsMap := by
    have hfactor (x : ConnectedComponents (PrimeSpectrum B')) :
        eT ((PrimeSpectrum.continuous_comap (algebraMap C B')).connectedComponentsMap x) =
          eBcc x := by
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe x
      rw [Continuous.connectedComponentsMap_mk, heT]
      simp only [eBcc, connectedComponentsHomeomorph,
        Topology.IsCoinducing.connectedComponentsHomeomorph_mk]
      rw [congrFun hSpecAlg p]
      apply ULift.up_injective
      calc
        ULift.up (gT (g p)) = S.toT (eC (g p)) := (heC_toT (g p)).symm
        _ = S.toT (q p) := by simp [g]
        _ = ULift.up (ConnectedComponents.mk (eBSpec p)) := hqT p
    refine ⟨fun x y hxy => by simpa [hfactor] using congrArg eT hxy,
      fun y => ⟨eBcc.symm (eT y), by simpa using hfactor (eBcc.symm (eT y))⟩⟩
  have hφbij : Function.Bijective ⇑φ :=
    bijective_of_wLocalMap_identifiesLocalRings hlocalCB hwlocalCB hcomponents
  let φA : C →ₐ[A] B' := {
    toRingHom := φ.toRingHom
    commutes' := fun a => φ.commutes' (ULift.up a)
  }
  let eCB : C ≃ₐ[A] B' := AlgEquiv.ofBijective φA hφbij
  let eLift : ULift.{u} C ≃ₐ[A] ULift.{u} B :=
    (ULift.algEquiv (R := A) (A := C)).trans eCB
  show ObjectProperty.ind.{max u v}
    (fun D : CommAlgCat.{max u v} A => Algebra.IsLocalIso A D)
    (CommAlgCat.of A (ULift.{u} B))
  exact (ObjectProperty.ind.{max u v}
    (fun D : CommAlgCat.{max u v} A => Algebra.IsLocalIso A D)).prop_of_iso
      (CommAlgCat.isoMk eLift) hACind

end AlgebraicGeometry.ProEtale

end
