module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Impurities
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.FlatPointedBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Impurities ascend through a flat pointed base change

An impurity of a finite type quasi-coherent module over the distinguished point of the base
remains an impurity after a pointed base change which is flat at the new distinguished point.
This is the engine of the descent of purity along a flat base change.

## Main definitions

* `AlgebraicGeometry.FlatPointedBaseChangeSituation.toPrePureSituation` forgets the base change
  and retains the pre-pure situation it is a base change of.

## Main results

* `AlgebraicGeometry.exists_specializes_of_isFlatAt`: a morphism which is flat at a point is
  generalizing there, in the pointwise form: every generalization of the image of the point is
  the image of a generalization of the point.
* `AlgebraicGeometry.exists_specializes_pullback_of_isFlatAt`: a specialization in the source of
  a morphism and a point of a base change which is flat there are both realized by a
  specialization in the fibre product.
* `AlgebraicGeometry.exists_impurity_after_flatPointedBaseChange`: an impurity over the
  distinguished point of the base gives an impurity on the base-changed morphism, lying over the
  original specialization.

## Implementation notes

The conclusion supplies an impurity diagram on the base-changed pre-pure situation. Since a
pre-pure situation records its schemes as data, the identifications of the base-changed situation
with the chosen fibre products are stated as equalities of schemes together with the compatible
transports of the morphisms, the module and the distinguished points; the test scheme of the
resulting impurity diagram is identified with the chosen fibre product `T ×_S S'`, and the
projections of its two test points and of its associated point are recorded.

The two auxiliary existence results are proved by passing to spectra of stalks: flatness at a
point is flatness of the stalk map, so the comparison morphism of spectra of stalks is flat, and
`Mathlib`'s description of the points of a fibre product in terms of its triplets transports a
specialization found there back to the fibre product of the original schemes.

## References

* [Stacks Project, Tag 05J9](https://stacks.math.columbia.edu/tag/05J9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes which is flat at `x` is generalizing at `x`: every generalization `y`
of the image of `x` is the image of a generalization of `x`. -/
public theorem exists_specializes_of_isFlatAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x) {y : Y} (hy : y ⤳ f.base x) :
    ∃ x' : X, x' ⤳ x ∧ f.base x' = y := by
  let A := Y.presheaf.stalk (f.base x)
  let B := X.presheaf.stalk x
  let φ : A ⟶ B := f.stalkMap x
  have hφ : φ.hom.Flat := hflat
  have hgen : GeneralizingMap (PrimeSpectrum.comap φ.hom) :=
    RingHom.Flat.generalizingMap_comap hφ
  obtain ⟨p, hp⟩ : y ∈ Set.range (Y.fromSpecStalk (f.base x)) := by
    rwa [Scheme.range_fromSpecStalk]
  have hclosed : PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint B) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint φ.hom
  have hbase : p ⤳ PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint B) :=
    hclosed ▸ IsLocalRing.specializes_closedPoint p
  obtain ⟨q, hq, hqmap⟩ := hgen hbase
  refine ⟨X.fromSpecStalk x q, ?_, ?_⟩
  · exact ((IsLocalRing.specializes_closedPoint q).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
  · have hmap := Scheme.SpecMap_stalkMap_fromSpecStalk (f := f) (x := x)
    calc
      f.base (X.fromSpecStalk x q) = (X.fromSpecStalk x ≫ f) q := rfl
      _ = (Spec.map φ ≫ Y.fromSpecStalk (f.base x)) q :=
        congrArg (fun g : Spec B ⟶ Y => g q) hmap.symm
      _ = Y.fromSpecStalk (f.base x) ((Spec.map φ) q) := rfl
      _ = Y.fromSpecStalk (f.base x) p := by
        have hmapPoint : (Spec.map φ) q = p := by
          show (specOrderIsoPrimeSpectrum A).symm
              (OrderDual.toDual (PrimeSpectrum.comap φ.hom q)) =
            (specOrderIsoPrimeSpectrum A).symm (OrderDual.toDual p)
          exact congrArg (fun z : PrimeSpectrum A =>
            (specOrderIsoPrimeSpectrum A).symm (OrderDual.toDual z)) hqmap
        exact congrArg (Y.fromSpecStalk (f.base x)) hmapPoint
      _ = y := hp

/-- Let `f : T ⟶ S` and `g : S' ⟶ S` be morphisms, let `t' ⤳ t` be a specialization in `T` and
let `s'` be a point of `S'` with the same image as `t`, at which `g` is flat. Then the
specialization is realized in `T ×_S S'` over `s'`: there are points `z' ⤳ z` of the fibre
product projecting to `t'` and `t` and with `z` projecting to `s'`. -/
public theorem exists_specializes_pullback_of_isFlatAt {T S S' : Scheme.{u}} (f : T ⟶ S)
    (g : S' ⟶ S) (t' t : T) (s' : S') (ht : t' ⤳ t) (hpoint : f.base t = g.base s')
    (hflat : IsFlatAt g.toLRSHom.toShHom s') :
    ∃ z' z : ↑(pullback f g),
      pullback.fst f g z' = t' ∧ pullback.fst f g z = t ∧ pullback.snd f g z = s' ∧ z' ⤳ z := by
  let R := S.presheaf.stalk (f.base t)
  let A := S'.presheaf.stalk s'
  let B := T.presheaf.stalk t
  let e : Inseparable (g.base s') (f.base t) := Inseparable.of_eq hpoint.symm
  let σ := (S.presheaf.stalkCongr e).inv
  have hσeq : σ = S.presheaf.stalkSpecializes e.le := rfl
  let γ : R ⟶ A := σ ≫ g.stalkMap s'
  have : IsIso σ := inferInstance
  have hσbij : Function.Bijective σ.hom := ConcreteCategory.bijective_of_isIso σ
  have hσflat : σ.hom.Flat := RingHom.Flat.of_bijective hσbij
  have hγflat : γ.hom.Flat := by
    show (g.stalkMap s').hom.comp σ.hom |>.Flat
    exact RingHom.Flat.comp hσflat hflat
  let α : Spec A ⟶ Spec R := Spec.map γ
  let β : Spec B ⟶ Spec R := Spec.map (f.stalkMap t)
  have : Flat α := Flat.SpecMap_iff.2 hγflat
  have : Flat (pullback.snd α β) := inferInstance
  let Z := pullback α β
  have hclosed : α (IsLocalRing.closedPoint A) = β (IsLocalRing.closedPoint B) := by
    simp [α, β]
    rfl
  obtain ⟨z, hzA, hzB⟩ := Scheme.Pullback.exists_preimage_pullback (f := α) (g := β)
    (IsLocalRing.closedPoint A) (IsLocalRing.closedPoint B) hclosed
  obtain ⟨q, hq⟩ : t' ∈ Set.range (T.fromSpecStalk t) := by
    rwa [Scheme.range_fromSpecStalk]
  have hqSpec : q ⤳ pullback.snd α β z := hzB ▸ IsLocalRing.specializes_closedPoint q
  have hzflat' : IsFlatAt (pullback.snd α β).toLRSHom.toShHom z := Flat.stalkMap _ z
  obtain ⟨z', hz'z, hz'q⟩ := exists_specializes_of_isFlatAt (pullback.snd α β) z hzflat' hqSpec
  let m : Z ⟶ pullback f g := pullback.lift (pullback.snd α β ≫ T.fromSpecStalk t)
    (pullback.fst α β ≫ S'.fromSpecStalk s') (by
      calc
        pullback.snd α β ≫ T.fromSpecStalk t ≫ f =
            pullback.snd α β ≫ β ≫ S.fromSpecStalk (f.base t) := by
          rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := f) (x := t)]
        _ = pullback.fst α β ≫ α ≫ S.fromSpecStalk (f.base t) := by
          rw [← pullback.condition_assoc]
        _ = pullback.fst α β ≫ Spec.map (g.stalkMap s') ≫
              Spec.map σ ≫ S.fromSpecStalk (f.base t) := by
          simp [α, γ, Spec.map_comp]
        _ = pullback.fst α β ≫ Spec.map (g.stalkMap s') ≫ S.fromSpecStalk (g.base s') := by
          rw [hσeq, Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := S) e.le]
        _ = pullback.fst α β ≫ S'.fromSpecStalk s' ≫ g := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk (f := g) (x := s')])
  have hmfst : m ≫ pullback.fst f g = pullback.snd α β ≫ T.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd f g = pullback.fst α β ≫ S'.fromSpecStalk s' :=
    pullback.lift_snd _ _ _
  refine ⟨m z', m z, ?_, ?_, ?_, hz'z.map (Scheme.Hom.continuous m)⟩
  · show (m ≫ pullback.fst f g) z' = t'
    rw [hmfst]
    simp [hz'q, hq]
  · show (m ≫ pullback.fst f g) z = t
    rw [hmfst, Scheme.Hom.comp_apply, hzB]
    exact Scheme.fromSpecStalk_closedPoint
  · show (m ≫ pullback.snd f g) z = s'
    rw [hmsnd, Scheme.Hom.comp_apply, hzA]
    exact Scheme.fromSpecStalk_closedPoint

/-- The pre-pure situation underlying a flat pointed base change: the finite type morphism, the
module and the distinguished point of the base, with the base change forgotten. -/
public abbrev FlatPointedBaseChangeSituation.toPrePureSituation
    (H : FlatPointedBaseChangeSituation.{u}) : PrePureSituation.{u} where
  S := H.S
  X := H.X
  f := H.f
  F := H.F
  s := H.s

/-- **Stacks Project, proof of Tag 05J9.** An impurity over the distinguished point `s` of the
base ascends to one over the distinguished point `s'` after a pointed base change which is flat
at `s'`. -/
public theorem exists_impurity_after_flatPointedBaseChange
    (H : FlatPointedBaseChangeSituation.{u})
    (D : ImpurityDiagram H.toPrePureSituation)
    (hD : IsImpurity H.toPrePureSituation D) :
    ∃ (P' : PrePureSituation.{u}) (D₁ : ImpurityDiagram P') (eS : P'.S = H.S')
      (eX : P'.X = pullback H.f H.g) (eT : D₁.T = pullback D.g H.g),
      (eqToHom eX.symm ≫ P'.f ≫ eqToHom eS = pullback.snd H.f H.g) ∧
      HEq P'.F ((Scheme.Modules.pullback (pullback.fst H.f H.g)).obj H.F) ∧
      (eS ▸ P'.s = H.s') ∧
      (D₁.g ≫ eqToHom eS = eqToHom eT ≫ pullback.snd D.g H.g) ∧
      IsImpurity P' D₁ ∧
      (pullback.fst D.g H.g) (eT ▸ D₁.t') = D.t' ∧
      (pullback.fst D.g H.g) (eT ▸ D₁.t) = D.t ∧
      (pullback.snd D.g H.g) (eT ▸ D₁.t) = H.s' ∧
      (pullback.fst H.f H.g) ((eqToHom eX) (D₁.toX D₁.xi)) = D.toX D.xi := by
  let P' : PrePureSituation :=
    { S := H.S'
      X := pullback H.f H.g
      f := pullback.snd H.f H.g
      F := (Scheme.Modules.pullback (pullback.fst H.f H.g)).obj H.F
      isFiniteType := SheafOfModules.pullback_isFiniteType
        (pullback.fst H.f H.g).toLRSHom.toShHom H.F
      isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent
        (pullback H.f H.g).toRingedSpace H.X.toRingedSpace
        (pullback.fst H.f H.g).toLRSHom.toShHom H.F H.FIsQuasicoherent
      s := H.s' }
  let T₁ := pullback D.g H.g
  let π := pullback.fst D.g H.g
  let ρ := pullback.snd D.g H.g
  let q : pullback D.toT π ⟶ T₁ := pullback.snd D.toT π
  let r : pullback D.toT π ⟶ D.X_T := pullback.fst D.toT π
  let Q := pullback D.toT π
  let xmap : Q ⟶ pullback H.f H.g := pullback.lift (f := H.f) (g := H.g)
    (r ≫ D.toX) (q ≫ ρ) (by
      calc
        r ≫ D.toX ≫ H.f = r ≫ D.toT ≫ D.g := by rw [D.isPullback.w]
        _ = q ≫ π ≫ D.g := by rw [← pullback.condition_assoc]
        _ = q ≫ ρ ≫ H.g := by
          simpa [Category.assoc] using congrArg (fun k => q ≫ k)
            (pullback.condition : π ≫ D.g = ρ ≫ H.g))
  have hpoint : D.g.base D.t = H.g.base H.s' := by
    calc
      D.g.base D.t = H.s := D.mapsToChosenPoint
      _ = H.g.base H.s' := H.mapsTo.symm
  obtain ⟨t₁', t₁, htproj, htbase, htsnd, htsp⟩ :=
    exists_specializes_pullback_of_isFlatAt D.g H.g D.t' D.t H.s' D.specializes
      (by simpa [ρ] using hpoint) H.flatAt
  have hxi' : D.toT.base D.xi = π.base t₁' := by rw [D.xi_liesOver, htproj]
  let Tr : Scheme.Pullback.Triplet D.toT π := Scheme.Pullback.Triplet.mk' D.xi t₁' hxi'
  obtain ⟨p, Z, hZ, hp⟩ := exists_isGenericPoint_mem_irreducibleComponents Tr.tensor
  let xi₁ : Q := Tr.SpecTensorTo p
  have hmap : xmap ≫ pullback.fst H.f H.g = r ≫ D.toX := pullback.lift_fst _ _ _
  let D₁ : ImpurityDiagram P' := by
    refine
      { T := T₁
        g := ρ
        t' := t₁'
        t := t₁
        specializes := htsp
        mapsToChosenPoint := htsnd
        X_T := Q
        toX := xmap
        toT := q
        isPullback := ?_
        xi := xi₁
        xi_liesOver := Tr.snd_SpecTensorTo_apply p }
    have houter' : IsPullback (xmap ≫ pullback.fst H.f H.g) q H.f (ρ ≫ H.g) := by
      have hbot : π ≫ D.g = ρ ≫ H.g := pullback.condition
      simpa only [hmap, ← hbot] using
        (IsPullback.of_hasPullback D.toT π).paste_horiz D.isPullback
    exact IsPullback.of_right houter' (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback H.f H.g)
  let Fold := D.pulledBack H.toPrePureSituation
  let eQ : D₁.pulledBack P' ≅ (Scheme.Modules.pullback r).obj Fold :=
    (Scheme.Modules.pullbackComp xmap (pullback.fst H.f H.g)).app H.F ≪≫
      (Scheme.Modules.pullbackCongr hmap).app H.F ≪≫
        (Scheme.Modules.pullbackComp r D.toX).symm.app H.F
  have : LocallyOfFiniteType D.toT :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback D.isPullback H.fLocallyOfFiniteType
  have : LocallyOfFiniteType q := inferInstance
  have : Fold.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent D.X_T.toRingedSpace H.X.toRingedSpace
      D.toX.toLRSHom.toShHom H.F H.FIsQuasicoherent
  have hrxi : r xi₁ = D.xi := Tr.fst_SpecTensorTo_apply p
  have hxiNested : xi₁ ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback r).obj Fold) := by
    rw [mem_relativeAssassin_pullback_iff]
    refine ⟨?_, ?_⟩
    · show r xi₁ ∈ Stacks.Divisors.relativeAssassin D.toT Fold
      rw [hrxi]
      exact hD.1
    · have he : (⟨Scheme.Pullback.Triplet.ofPoint xi₁, Scheme.Pullback.SpecOfPoint xi₁⟩ :
          Σ T : Scheme.Pullback.Triplet D.toT π, Spec T.tensor) = ⟨Tr, p⟩ :=
        (Scheme.Pullback.carrierEquiv (f := D.toT) (g := π)).apply_symm_apply ⟨Tr, p⟩
      let Good : (Σ T : Scheme.Pullback.Triplet D.toT π, Spec T.tensor) → Prop :=
        fun z => ∃ Z ∈ irreducibleComponents (Spec z.1.tensor), IsGenericPoint z.2 Z
      show Good ⟨Scheme.Pullback.Triplet.ofPoint xi₁, Scheme.Pullback.SpecOfPoint xi₁⟩
      exact he.symm ▸ (show Good ⟨Tr, p⟩ from ⟨Z, hZ, hp⟩)
  have hxiMem : xi₁ ∈ Stacks.Divisors.relativeAssassin q (D₁.pulledBack P') :=
    relativeAssassin_eq_of_moduleIso q eQ.symm ▸ hxiNested
  have hdisj : closure {xi₁} ∩ Set.range (q.fiberι t₁) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    have hspec' : D.xi ⤳ r y := by
      have hmap' := (specializes_iff_mem_closure.mpr hy.1 : xi₁ ⤳ y).map r.continuous
      rwa [hrxi] at hmap'
    have hqy : q y = t₁ := by
      simpa [q.range_fiberι] using hy.2
    have hcoord : D.toT (r y) = D.t := by
      have hcomp := congrArg (fun k : Q ⟶ D.T => k y)
        (pullback.condition : r ≫ D.toT = q ≫ π)
      change D.toT (r y) = π (q y) at hcomp
      calc
        D.toT (r y) = π (q y) := hcomp
        _ = π t₁ := congrArg π hqy
        _ = D.t := by simpa [π] using htbase
    have hfiber : r y ∈ Set.range (D.toT.fiberι D.t) := by
      rwa [D.toT.range_fiberι]
    have hbad : r y ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
      ⟨specializes_iff_mem_closure.mp hspec', hfiber⟩
    rw [hD.2] at hbad
    exact hbad
  refine ⟨P', D₁, rfl, rfl, rfl, rfl, HEq.rfl, rfl, rfl, ⟨hxiMem, hdisj⟩, htproj, htbase,
    htsnd, ?_⟩
  calc
    pullback.fst H.f H.g (xmap xi₁) = D.toX (r xi₁) := by
      simpa [Scheme.Hom.comp_apply] using congrArg (fun f : Q ⟶ H.X => f xi₁) hmap
    _ = D.toX D.xi := congrArg D.toX hrxi

end AlgebraicGeometry
