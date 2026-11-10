module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.HenselizationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Impurities over the henselization and over elementary étale neighbourhoods

In a pre-pure situation an impurity whose test family is an elementary étale neighbourhood of the
distinguished point of the base gives rise to an impurity over the henselization of the base at
that point, and conversely.

## Main results

* `AlgebraicGeometry.exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood` compares
  impurities over the henselization with impurities over elementary étale neighbourhoods.

## References

* [Stacks Project, Tag 05J3](https://stacks.math.columbia.edu/tag/05J3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The local ring of an elementary étale neighbourhood at its distinguished point maps to the
henselization of the base, compatibly with the maps from the local ring of the base. -/
private theorem exists_elementary_stalk_map_to_henselization
    {S : Scheme.{u}} (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    ∃ f : U.scheme.presheaf.stalk U.point →+* henselizationRing S s, IsLocalHom f ∧
      f.comp (stalkMap S s ⟨U, hU⟩) =
        algebraMap (S.presheaf.stalk s) (henselizationRing S s) := by
  let Ue : ElementaryEtaleNeighborhood S s := ⟨U, hU⟩
  let R := S.presheaf.stalk s
  let A := U.scheme.presheaf.stalk U.point
  let H := henselizationRing S s
  let : Algebra R A := (stalkMap S s Ue).toAlgebra
  have : IsLocalHom (algebraMap R A) := by
    change IsLocalHom (stalkMap S s Ue)
    dsimp [stalkMap]
    infer_instance
  have hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R A)) := by
    have hmap : IsLocalRing.ResidueField.map (algebraMap R A) = U.residueFieldMap.hom := by
      ext z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change IsLocalRing.residue A (stalkMap S s Ue r) =
        U.residueFieldMap.hom (IsLocalRing.residue R r)
      have hcomm : CommRingCat.ofHom (stalkMap S s Ue) ≫ U.scheme.residue U.point =
          S.residue s ≫ U.residueFieldMap := by
        have hcong : (S.presheaf.stalkCongr (.of_eq U.map_point.symm)).hom ≫
            S.residue (U.toBase U.point) =
            S.residue s ≫ (S.residueFieldCongr U.map_point).inv := by
          rw [Scheme.residueFieldCongr_inv]
          exact (Scheme.residue_residueFieldCongr S U.map_point.symm).symm
        calc
          CommRingCat.ofHom (stalkMap S s Ue) ≫ U.scheme.residue U.point =
              (S.presheaf.stalkCongr (Inseparable.of_eq U.map_point.symm)).hom ≫
                (U.toBase.stalkMap U.point ≫ U.scheme.residue U.point) := by
            rw [stalkMap, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
            rfl
          _ = (S.presheaf.stalkCongr (.of_eq U.map_point.symm)).hom ≫
                (S.residue (U.toBase U.point) ≫ U.toBase.residueFieldMap U.point) := by
            rw [← Scheme.residue_residueFieldMap U.toBase U.point]
          _ = (S.residue s ≫ (S.residueFieldCongr U.map_point).inv) ≫
                U.toBase.residueFieldMap U.point := by
            rw [← Category.assoc, hcong]
          _ = S.residue s ≫ U.residueFieldMap := by
            simp [EtaleNeighborhood.residueFieldMap, Category.assoc]
      exact ConcreteCategory.congr_hom hcomm r
    rw [hmap]
    exact (ConcreteCategory.bijective_of_isIso U.residueFieldMap).2
  have : HenselianLocalRing H :=
    IsLocalRing.IsHenselization.henselian (R := R) (L := IsLocalRing.ResidueField R)
  obtain ⟨f, hf, -⟩ := StacksDraft.existsUnique_isLocalHom_of_indEtale
    (A := R) (B := A) (C := H) (indEtale_elementaryStalkMap S s Ue) hres
  exact ⟨f.toRingHom, ⟨hf.map_nonunit⟩, RingHom.ext fun r => f.commutes r⟩

/-- Membership in the relative assassin is invariant under an isomorphism of modules. -/
private lemma mem_relativeAssassin_of_iso {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules}
    (e : F ≅ G) {x : X} (hx : x ∈ Stacks.Divisors.relativeAssassin f F) :
    x ∈ Stacks.Divisors.relativeAssassin f G := by
  rw [Stacks.Divisors.mem_relativeAssassin] at hx ⊢
  obtain ⟨s, y, hy, hyx⟩ := hx
  exact ⟨s, y, Stacks.Divisors.associatedPoints_congr
      ((Scheme.Modules.pullback (f.fiberι s)).mapIso e) ▸ hy, hyx⟩

/-- In a pre-pure situation, an impurity over the henselization of the base at the distinguished
point exists if and only if one exists over an elementary étale neighbourhood of that point. -/
@[stacks 05J3 "parts (1) and (2)"]
theorem exists_isImpurity_henselization_iff_elementaryEtaleNeighborhood
    (P : PrePureSituation.{u}) :
    (∃ (D : ImpurityDiagram P) (e : D.T ≅ henselization P.S P.s),
      D.g = e.hom ≫ henselizationToBase P.S P.s ∧ IsImpurity P D) ↔
    (∃ (D : ImpurityDiagram P) (hD : Etale D.g), IsImpurity P D ∧
      EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := hD
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood P.S P.s)) := by
  constructor
  · rintro ⟨D, e, hbase, hImp⟩
    exact exists_isImpurity_elementaryEtaleNeighborhood_of_henselization P
      (henselizationRing P.S P.s) ⟨D, e, by rw [hbase]; rfl, hImp⟩
  · rintro ⟨D, hD, hImp, hElem⟩
    let U : EtaleNeighborhood P.S P.s :=
      { scheme := D.T
        point := D.t
        toBase := D.g
        etale_toBase := hD
        map_point := D.mapsToChosenPoint }
    let Ue : ElementaryEtaleNeighborhood P.S P.s := ⟨U, hElem⟩
    let R := P.S.presheaf.stalk P.s
    let A := D.T.presheaf.stalk D.t
    let H := henselizationRing P.S P.s
    let Hs := henselization P.S P.s
    let gH := henselizationToBase P.S P.s
    obtain ⟨f, hf, hfac⟩ := exists_elementary_stalk_map_to_henselization P.s U hElem
    let : Algebra R A := (stalkMap P.S P.s Ue).toAlgebra
    let : Algebra R H := henselizationRingAlgebra P.S P.s
    let : Algebra A H := f.toAlgebra
    have hscalarMap (r : R) : algebraMap R H r = algebraMap A H (stalkMap P.S P.s Ue r) := by
      change algebraMap R H r = f (stalkMap P.S P.s Ue r)
      exact (RingHom.congr_fun hfac r).symm
    let : IsScalarTower R A H := IsScalarTower.of_algebraMap_eq hscalarMap
    let : IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H := inferInstance
    have hIndA : StacksDraft.IndEtale R A := indEtale_elementaryStalkMap P.S P.s Ue
    have hIndAH : StacksDraft.IndEtale A H :=
      StacksDraft.indEtale_of_comp hIndA
        (StacksDraft.indEtale_of_isHenselization (IsLocalRing.ResidueField R))
    have hfFlat : f.Flat :=
      RingHom.flat_algebraMap_iff.mpr (CommAlgCat.flat_of_ind_etale
        (StacksDraft.indEtale_iff.mp hIndAH))
    let : IsLocalHom f := hf
    let e : Inseparable (D.g.base D.t) P.s := Inseparable.of_eq D.mapsToChosenPoint
    have hfacCat : P.S.presheaf.stalkSpecializes e.specializes ≫ D.g.stalkMap D.t ≫
        CommRingCat.ofHom f = CommRingCat.ofHom (algebraMap R H) := by
      apply CommRingCat.hom_ext
      ext r
      exact (hscalarMap r).symm
    have hfacSpec : Spec.map (D.g.stalkMap D.t ≫ CommRingCat.ofHom f) ≫
        Spec.map (P.S.presheaf.stalkSpecializes e.specializes) =
        Spec.map (CommRingCat.ofHom (algebraMap R H)) := by
      simpa only [Spec.map_comp, Category.assoc] using congrArg Spec.map hfacCat
    let i : Hs ⟶ D.T := Spec.map (CommRingCat.ofHom f) ≫ D.T.fromSpecStalk D.t
    have hbase : i ≫ D.g = gH := by
      dsimp [i, gH, henselizationToBase]
      have hcombine : Spec.map (CommRingCat.ofHom f) ≫ Spec.map (D.g.stalkMap D.t) =
          Spec.map (D.g.stalkMap D.t ≫ CommRingCat.ofHom f) :=
        (Spec.map_comp (D.g.stalkMap D.t) (CommRingCat.ofHom f)).symm
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk (f := D.g) (x := D.t),
        ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := P.S) e.specializes, ← Category.assoc,
        hcombine, ← Category.assoc, hfacSpec]
    let : Flat (Spec.map (CommRingCat.ofHom f)) := Flat.SpecMap_iff.mpr hfFlat
    let : Flat (D.T.fromSpecStalk D.t) := flat_fromSpecStalk D.T D.t
    let : Flat i := inferInstance
    let tH : Hs := IsLocalRing.closedPoint (CommRingCat.of H)
    have hSpecClosed : (Spec.map (CommRingCat.ofHom f)).base tH = IsLocalRing.closedPoint A := by
      change PrimeSpectrum.comap f (IsLocalRing.closedPoint H) = _
      exact IsLocalRing.comap_closedPoint f
    have hiClosed : i.base tH = D.t := by
      change D.T.fromSpecStalk D.t ((Spec.map (CommRingCat.ofHom f)).base tH) = D.t
      rw [hSpecClosed]
      exact Scheme.fromSpecStalk_closedPoint
    have hchosen : gH.base tH = P.s := by
      calc
        gH.base tH = (i ≫ D.g).base tH := congrArg (fun k : Hs ⟶ P.S => k tH) hbase.symm
        _ = D.g.base (i.base tH) := rfl
        _ = P.s := by rw [hiClosed]; exact D.mapsToChosenPoint
    have hspecTarget : D.t' ⤳ i.base tH := by simpa [hiClosed] using D.specializes
    obtain ⟨tH', htH'tH, hitH'⟩ := Flat.generalizingMap i hspecTarget
    let Q := pullback D.toT i
    let q : Q ⟶ Hs := pullback.snd D.toT i
    let r : Q ⟶ D.X_T := pullback.fst D.toT i
    have hxiBase : D.toT.base D.xi = i.base tH' := by rw [D.xi_liesOver, hitH']
    let Tr : Scheme.Pullback.Triplet D.toT i := Scheme.Pullback.Triplet.mk' D.xi tH' hxiBase
    obtain ⟨p, Z, hZ, hp⟩ := exists_isGenericPoint_mem_irreducibleComponents Tr.tensor
    let xiH : Q := Tr.SpecTensorTo p
    have hrxi : r xiH = D.xi := Tr.fst_SpecTensorTo_apply p
    have houter : IsPullback (r ≫ D.toX) q P.f (i ≫ D.g) :=
      (IsPullback.of_hasPullback D.toT i).paste_horiz D.isPullback
    have hPB : IsPullback (r ≫ D.toX) q P.f gH := by simpa [hbase] using houter
    let D' : ImpurityDiagram P :=
      { T := Hs
        g := gH
        t' := tH'
        t := tH
        specializes := htH'tH
        mapsToChosenPoint := hchosen
        X_T := Q
        toX := r ≫ D.toX
        toT := q
        isPullback := hPB
        xi := xiH
        xi_liesOver := Tr.snd_SpecTensorTo_apply p }
    let Fold := D.pulledBack P
    let : Fold.IsQuasicoherent :=
      @SheafOfModules.modulePullback_isQuasicoherent D.X_T.toRingedSpace P.X.toRingedSpace
        D.toX.toLRSHom.toShHom P.F P.isQuasicoherent
    let : LocallyOfFiniteType D.toT :=
      locallyOfFiniteType_isStableUnderBaseChange.of_isPullback D.isPullback P.locallyOfFiniteType
    have hxiNested : xiH ∈ Stacks.Divisors.relativeAssassin q
        ((Scheme.Modules.pullback r).obj Fold) := by
      rw [mem_relativeAssassin_pullback_iff]
      refine ⟨?_, ?_⟩
      · change r xiH ∈ Stacks.Divisors.relativeAssassin D.toT Fold
        rw [hrxi]
        exact hImp.1
      · have he : (⟨Scheme.Pullback.Triplet.ofPoint xiH, Scheme.Pullback.SpecOfPoint xiH⟩ :
            Σ T : Scheme.Pullback.Triplet D.toT i, Spec T.tensor) = ⟨Tr, p⟩ :=
          (Scheme.Pullback.carrierEquiv (f := D.toT) (g := i)).apply_symm_apply ⟨Tr, p⟩
        let Good : (Σ T : Scheme.Pullback.Triplet D.toT i, Spec T.tensor) → Prop :=
          fun z => ∃ Z ∈ irreducibleComponents (Spec z.1.tensor), IsGenericPoint z.2 Z
        change Good ⟨Scheme.Pullback.Triplet.ofPoint xiH, Scheme.Pullback.SpecOfPoint xiH⟩
        exact he.symm ▸ (show Good ⟨Tr, p⟩ from ⟨Z, hZ, hp⟩)
    let eQ : D'.pulledBack P ≅ (Scheme.Modules.pullback r).obj Fold :=
      (Scheme.Modules.pullbackComp r D.toX).symm.app P.F
    have hxiMem : xiH ∈ Stacks.Divisors.relativeAssassin q (D'.pulledBack P) :=
      mem_relativeAssassin_of_iso q eQ.symm hxiNested
    have hdisj : closure {xiH} ∩ Set.range (q.fiberι tH) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      have hspec : xiH ⤳ y := specializes_iff_mem_closure.mpr hy.1
      have hspec' : D.xi ⤳ r y := by
        have hmap' := hspec.map r.continuous
        rwa [hrxi] at hmap'
      have hqy : q y = tH := by
        have hy' : y ∈ Set.range (q.fiberι tH) := hy.2
        rwa [q.range_fiberι] at hy'
      have hcoord : D.toT (r y) = D.t := by
        have hcomp := congrArg (fun k : Q ⟶ D.T => k y)
          (pullback.condition : r ≫ D.toT = q ≫ i)
        change D.toT (r y) = i (q y) at hcomp
        exact hcomp.trans ((congrArg i hqy).trans hiClosed)
      have hbad : r y ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
        ⟨specializes_iff_mem_closure.mp hspec', by rw [D.toT.range_fiberι]; exact hcoord⟩
      rwa [hImp.2] at hbad
    exact ⟨D', Iso.refl _, rfl, hxiMem, hdisj⟩

end AlgebraicGeometry

end
