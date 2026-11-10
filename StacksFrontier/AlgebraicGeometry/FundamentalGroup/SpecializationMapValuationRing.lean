module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.RingTheory.Valuation.StrictlyHenselian

import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapDiscreteValuationRing

/-!
# Realizing a specialization map over a strictly henselian valuation ring

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres, let `s'` and `s` be
geometric points of `S` and let `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map. Then `sp`
is isomorphic to the specialization map `sp_R` of a base change `X_R ⟶ Spec R` for a strictly
henselian valuation ring `R` over `S` with algebraically closed fraction field, the specialization
being the one from the generic point of `Spec R` to its closed point.

"Isomorphic" is not defined in the source; what its proof produces, and what is proved here, is a
commutative square whose two vertical maps are isomorphisms of topological groups:
`π₁(X_{s̄'}) ≅ π₁((X_R)_{η̄})` and `π₁(X_{s̄}) ≅ π₁((X_R)_{ō})` intertwining `sp` and `sp_R`.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing`
  — **Tag 0C0M**: the realization of a specialization map over a strictly henselian valuation
  ring with algebraically closed fraction field.
* `AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_valuationRing` — the same for any
  input `h0A48` in place of Tag 0A48.

## Implementation notes

The valuation ring is the one the source's proof names: the given specialization map carries with
it the strict henselization `A` of `𝒪_{S,s}` and the ring map `A → κ(s̄')` used to build it, and
`IsLocalRing.exists_factor_valuationRing_strictlyHenselian` (Stacks 00IA, with Stacks 0BSQ and
00IC) dominates the image of that map by a valuation subring `R ⊆ κ(s̄')` which is strictly
henselian and has algebraically closed residue field. Its fraction field is `κ(s̄')` itself, so the
generic point of `Spec R` already carries a geometric point with algebraically closed residue
field, and the closed point carries `AlgebraicGeometry.closedGeometricPoint`. No Noetherian
hypothesis is needed, in contrast with the discrete valuation ring of Stacks 0C0N
(`AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing`).

Because the geometric point `s̄'` factors through `Spec R` *exactly* — the composite
`Spec κ(s̄') ⟶ Spec R ⟶ Spec A` is the morphism `p'` recorded in the given specialization map —
the generic geometric fibre of `X_R ⟶ Spec R` is compared with `X_{s̄'}` by a plain common
geometric fibre, with no extension of algebraically closed fields intervening.

The construction is carried out in
`AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_valuationRing` for any input
`h0A48 : ProperHenselianFiniteEtaleEquivalence`, the same input
`AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing` takes;
the registered statement
`AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing`
supplies it by `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence` (Tag 0A48).

## References

* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA)
* [Stacks Project, Tag 0BSQ](https://stacks.math.columbia.edu/tag/0BSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The fraction ring of a valuation subring of an algebraically closed field is algebraically
closed: the field itself is a fraction field of the subring. -/
private theorem isAlgClosed_fractionRing_valuationSubring {K : Type u} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : IsAlgClosed (FractionRing V) :=
  IsAlgClosed.of_ringEquiv K (FractionRing V) (FractionRing.algEquiv V K).symm.toRingEquiv

/-! ### Tag 0C0M -/

/-- **Stacks 0C0M, granted Tag 0A48 (`h0A48`).** Let `f : X ⟶ S` be a proper morphism with
geometrically connected fibres, let `s'` and `s` be geometric points of `S`, and let
`sp : π₁(X_{s'}) → π₁(X_s)` be a specialization map. Then there are a strictly henselian valuation
ring `R` with algebraically closed fraction field and algebraically closed residue field, a
morphism `r : Spec R ⟶ S` carrying the generic point of `Spec R` to the image of `s'` and its
closed point to the image of `s`, and a specialization map
`sp_R : π₁((X_R)_{η̄}) → π₁((X_R)_{ō})` of the base change `X_R ⟶ Spec R` from the generic to the
closed point, such that `sp` and `sp_R` are intertwined by isomorphisms of topological groups on
the source and on the target.

The geometric points `η̄` and `ō` are the points themselves, as in the source's
`sp_R : π₁(X_η) → π₁(X_s)` (both residue fields being algebraically closed): the field of `η̄` is
a fraction field of `R` through `R → κ(η̄)`, and `R → κ(ō)` is surjective. -/
-- Not registered itself: the registered form of Stacks 0C0M is
-- `exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing` below, which
-- supplies `h0A48` by `properHenselianFiniteEtaleEquivalence` (Tag 0A48, proved from Tag 088C).
-- `h0A48` is consumed at the valuation ring `V` constructed in the proof, to produce `sp_R`, and
-- at the henselian points of an extension of algebraically closed fields, through Tag 0A49.
theorem exists_isSpecializationMap_isomorphic_over_valuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u}) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R)
      (_ : StrictlyHenselianLocalRing R) (_ : IsAlgClosed (FractionRing R))
      (_ : IsAlgClosed (ResidueField R))
      (r : Spec (.of R) ⟶ S) (η o : GeometricPoint (Spec (.of R)))
      (yη : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) η))
      (yo : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) o))
      (spR : EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
      η.hom default = genericPoint (Spec (.of R)) ∧
      o.hom default = closedPoint R ∧
      @IsFractionRing R _ η.residueField _ (Spec.preimage η.hom).hom.toAlgebra ∧
      Function.Surjective (Spec.preimage o.hom).hom ∧
      r (η.hom default) = s'.hom default ∧
      r (o.hom default) = s.hom default ∧
      IsSpecializationMap (pullback.snd f r) η o yη yo spR ∧
      ∃ (eη : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη)
        (eo : EtaleFundamentalGroup (fiberOverGeometricPoint f s) x ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
        ∀ γ, eo (sp γ) = spR (eη γ) := by
  classical
  simp only [IsSpecializationMap] at hsp
  obtain ⟨A, hAring, hAloc, hAalg, ⟨hstrict⟩, p', hp', p, hp, hclosed, hXA, hi, t, hform⟩ := hsp
  let := hAring
  let := hAloc
  let := hAalg
  let z : S := s.hom (closedPoint s.residueField)
  let gA : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫ S.fromSpecStalk z
  obtain ⟨V, hVmem, hVloc, hVsh, hVres⟩ :=
    IsLocalRing.exists_factor_valuationRing_strictlyHenselian (Spec.preimage p').hom
  let φ : A →+* V := (Spec.preimage p').hom.codRestrict V.toSubring hVmem
  let := hVloc
  let := hVsh
  let := hVres
  have hVfrac : IsAlgClosed (FractionRing V) := isAlgClosed_fractionRing_valuationSubring V
  refine ⟨V, inferInstance, inferInstance, inferInstance, hVsh, hVfrac, hVres, ?_⟩
  let q : Spec (.of V) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
  let r : Spec (.of V) ⟶ S := q ≫ gA
  let η : GeometricPoint (Spec (.of V)) :=
    { residueField := s'.residueField
      hom := Spec.map (CommRingCat.ofHom (algebraMap V s'.residueField)) }
  let o : GeometricPoint (Spec (.of V)) := closedGeometricPoint V
  have hηq : η.hom ≫ q = p' := by
    have h : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap V s'.residueField)
        = Spec.preimage p' := CommRingCat.hom_ext (by ext a; rfl)
    change Spec.map (CommRingCat.ofHom (algebraMap V s'.residueField))
      ≫ Spec.map (CommRingCat.ofHom φ) = p'
    rw [← Spec.map_comp, h, Spec.map_preimage]
  have hηgeneric : η.hom default = genericPoint (Spec (.of V)) := by
    have hdef : (default : Spec (.of s'.residueField))
        = genericPoint (Spec (.of s'.residueField)) := Subsingleton.elim _ _
    change Spec.map (CommRingCat.ofHom (algebraMap V s'.residueField))
      (default : Spec (.of s'.residueField)) = _
    rw [hdef, genericPoint_eq_bot_of_affine (CommRingCat.of V)]
    refine specMap_genericPoint_eq_of_ker (algebraMap V s'.residueField) (⊥ : Ideal V) fun a ↦ ?_
    rw [Ideal.mem_bot]
    exact ⟨fun ha ↦ Subtype.ext ha, fun ha ↦ by rw [ha, map_zero]⟩
  have hoclosed : o.hom default = closedPoint V :=
    (congrArg o.hom (Subsingleton.elim _ _)).trans (closedGeometricPoint_liesOver V)
  have hηA : q (η.hom default) = p' default := by
    have h := congrArg (fun w => w default) hηq
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using h
  have hqc : q (closedPoint V) = closedPoint A := IsLocalRing.comap_closedPoint φ
  have : ConnectedSpace (pullback f r : Scheme.{u}) :=
    connectedSpace_pullback_spec_of_isProper f V r
  let fV := pullback.snd f r
  have : IsProper fV := inferInstanceAs (IsProper (pullback.snd f r))
  have : GeometricallyConnected fV :=
    inferInstanceAs (GeometricallyConnected (pullback.snd f r))
  have : ConnectedSpace (fiberOverGeometricPoint fV η) :=
    connectedSpace_fiberOverGeometricPoint fV η
  have : ConnectedSpace (fiberOverGeometricPoint fV o) :=
    connectedSpace_fiberOverGeometricPoint fV o
  let yη := Stacks.Etale.ofPoint (S := fiberOverGeometricPoint fV η) (Classical.arbitrary _)
  let yo := Stacks.Etale.ofPoint (S := fiberOverGeometricPoint fV o) (Classical.arbitrary _)
  let BV : Scheme.{u} := pullback fV (𝟙 (Spec (.of V)))
  have : ConnectedSpace BV := connectedSpace_pullback_spec_of_isProper fV V (𝟙 (Spec (.of V)))
  let eV : BV ≅ pullback f r := asIso (pullback.fst fV (𝟙 _))
  let iVη := fiberOverGeometricPointMap fV η (𝟙 _) η.hom (Category.comp_id _)
  let iVo := fiberOverGeometricPointMap fV o (𝟙 _) o.hom (Category.comp_id _)
  have hiVo : (finiteEtaleBaseChange iVo).IsEquivalence := by
    have hcomp : iVo = pullback.fst fV o.hom ≫ eV.inv := by
      rw [← cancel_mono eV.hom, Category.assoc, eV.inv_hom_id, Category.comp_id]
      exact pullback.lift_fst _ _ _
    rw [hcomp]
    exact isEquivalence_finiteEtaleBaseChange_comp _ _
      (h0A48 V fV inferInstance) (isEquivalence_finiteEtaleBaseChange_of_iso eV.symm)
  let tV := (nonempty_finiteEtaleFiberFunctorIso BV (yη.map iVη) (yo.map iVo)).some
  let dV := (etaleFundamentalGroupContinuousMulEquiv tV).trans
    (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence iVo yo).symm
  let spR : EtaleFundamentalGroup (fiberOverGeometricPoint fV η) yη →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint fV o) yo :=
    (ContinuousMonoidHom.toContinuousMonoidHom dV).comp (etaleFundamentalGroupMap iVη yη)
  have hspRform : ∀ γ, etaleFundamentalGroupMap iVo yo (spR γ)
      = etaleFundamentalGroupMulEquiv tV (etaleFundamentalGroupMap iVη yη γ) := by
    intro γ
    change etaleFundamentalGroupMap iVo yo
      ((etaleFundamentalGroupMulEquivOfIsEquivalence iVo yo).symm
        (etaleFundamentalGroupMulEquiv tV (etaleFundamentalGroupMap iVη yη γ))) = _
    rw [← etaleFundamentalGroupMulEquivOfIsEquivalence_apply]
    exact (etaleFundamentalGroupMulEquivOfIsEquivalence iVo yo).apply_symm_apply _
  have hspR : IsSpecializationMap fV η o yη yo spR :=
    isSpecializationMap_of_identity_factorization V fV η yη yo spR hiVo tV hspRform
  have hηfrac : @IsFractionRing V _ η.residueField _ (Spec.preimage η.hom).hom.toAlgebra := by
    rw [show Spec.preimage η.hom = CommRingCat.ofHom (algebraMap V s'.residueField) from
      Spec.preimage_map _, CommRingCat.hom_ofHom]
    convert ValuationSubring.instIsFractionRingSubtypeMem V
    exact Algebra.algebra_ext _ _ fun _ => rfl
  have hosurj : Function.Surjective (Spec.preimage o.hom).hom := by
    rw [show Spec.preimage o.hom = CommRingCat.ofHom (residue V) from Spec.preimage_map _]
    exact residue_surjective
  refine ⟨r, η, o, yη, yo, spR, hηgeneric, hoclosed, hηfrac, hosurj, ?_, ?_, hspR, ?_⟩
  · change gA (q (η.hom default)) = s'.hom default
    rw [hηA]
    have h := congrArg (fun w => w default) hp'
    simpa [gA, Scheme.Hom.comp_base] using h
  · change gA (q (o.hom default)) = s.hom default
    rw [hoclosed, hqc, ← hclosed]
    have h := congrArg (fun w => w (closedPoint s.residueField)) hp
    exact h.trans (congrArg s.hom (Subsingleton.elim _ _))
  · let : ConnectedSpace (pullback f gA : Scheme.{u}) := hXA
    let fA := pullback.snd f gA
    let j : (pullback f r : Scheme.{u}) ⟶ (pullback f gA : Scheme.{u}) :=
      pullback.lift (pullback.fst f r) (pullback.snd f r ≫ q) (by
        simpa [r, Category.assoc] using pullback.condition (f := f) (g := r))
    have hj : IsPullback j (pullback.snd f r) fA q := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f gA)
      rw [show j ≫ pullback.fst f gA = pullback.fst f r from pullback.lift_fst _ _ _]
      exact IsPullback.of_hasPullback f r
    let k : BV ⟶ (pullback f gA : Scheme.{u}) := eV.hom ≫ j
    let sA' : GeometricPoint (Spec (.of A)) :=
      { residueField := s'.residueField, hom := p' }
    let sA : GeometricPoint (Spec (.of A)) := { residueField := s.residueField, hom := p }
    let iA' := fiberOverGeometricPointMap f s' gA p' hp'
    let iA := fiberOverGeometricPointMap f s gA p hp
    have hiA' : IsPullback iA' (pullback.snd f s'.hom) fA sA'.hom :=
      isPullback_fiberOverGeometricPointMap f s' gA p' hp'
    have hiA : IsPullback iA (pullback.snd f s.hom) fA sA.hom :=
      isPullback_fiberOverGeometricPointMap f s gA p hp
    have hiV (g : GeometricPoint (Spec (.of V))) :
        IsPullback (fiberOverGeometricPointMap fV g (𝟙 _) g.hom (Category.comp_id _) ≫ k)
          (pullback.snd fV g.hom) fA (g.map q).hom := by
      have e : fiberOverGeometricPointMap fV g (𝟙 _) g.hom (Category.comp_id _) ≫ eV.hom
          = pullback.fst fV g.hom := pullback.lift_fst _ _ _
      rw [show k = eV.hom ≫ j from rfl, ← Category.assoc, e]
      exact (IsPullback.of_hasPullback fV g.hom).paste_horiz hj
    have hclosedA : sA.hom default = (o.map q).hom default := by
      change p default = q (o.hom default)
      rw [hoclosed, hqc, ← hclosed]
      exact congrArg p (Subsingleton.elim _ _)
    have hgenericA : sA'.hom default = (η.map q).hom default := hηA.symm
    have hk : (finiteEtaleBaseChange k).IsEquivalence := by
      refine isEquivalence_finiteEtaleBaseChange_cancel_right iVo k hiVo ?_
      exact isEquivalence_finiteEtaleBaseChange_of_isPullback_liesOver_eq fA h0A48
        sA (o.map q) hclosedA iA (pullback.snd f s.hom) hiA
        (iVo ≫ k) (pullback.snd fV o.hom) (hiV o) hi
    obtain ⟨W, hW, a, b, ha, hb, hab⟩ := exists_common_geometricFibre fA h0A48
      sA' (η.map q) hgenericA iA' (pullback.snd f s'.hom) hiA'
      (iVη ≫ k) (pullback.snd fV η.hom) (hiV η)
    let : ConnectedSpace W := hW
    let zW := Stacks.Etale.ofPoint (S := W) (Classical.arbitrary _)
    have := hi
    let dA := (etaleFundamentalGroupContinuousMulEquiv t).trans
      (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence iA x).symm
    refine exists_intertwining_of_factorizations iA' iVη k a b hab ha hb hk
      x' x yη yo zW dA dV sp spR ?_ ?_
    · intro γ
      change sp γ = (etaleFundamentalGroupMulEquivOfIsEquivalence iA x).symm
        (etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap iA' x' γ))
      rw [← hform γ, ← etaleFundamentalGroupMulEquivOfIsEquivalence_apply]
      exact ((etaleFundamentalGroupMulEquivOfIsEquivalence iA x).symm_apply_apply (sp γ)).symm
    · intro γ
      rfl

/-- **Stacks Project, Tag 0C0M.** Let `f : X ⟶ S` be a proper morphism with geometrically
connected fibres, let `s'` and `s` be geometric points of `S` and let
`sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map. Then there are a strictly henselian
valuation ring `R` with algebraically closed fraction field (and algebraically closed residue
field) and a morphism `r : Spec R ⟶ S` sending the generic point `η` of `Spec R` to the image of
`s'` and its closed point `o` to the image of `s`, such that `sp` is isomorphic to the
specialization map `sp_R : π₁((X_R)_η) → π₁((X_R)_o)` of the base change `X_R ⟶ Spec R`: there
are isomorphisms of topological groups `π₁(X_{s̄'}) ≅ π₁((X_R)_η)` and `π₁(X_{s̄}) ≅ π₁((X_R)_o)`
intertwining `sp` and `sp_R`.

The geometric points `η` and `o` of `Spec R` are the generic and closed points themselves: the
field of `η` is a fraction field of `R`, and `R` maps onto the field of `o`. This is
`exists_isSpecializationMap_isomorphic_over_valuationRing` with its input Tag 0A48 supplied by
`properHenselianFiniteEtaleEquivalence`. -/
@[stacks 0C0M]
theorem exists_isSpecializationMap_isomorphic_over_strictlyHenselianValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : ValuationRing R)
      (_ : StrictlyHenselianLocalRing R) (_ : IsAlgClosed (FractionRing R))
      (_ : IsAlgClosed (ResidueField R))
      (r : Spec (.of R) ⟶ S) (η o : GeometricPoint (Spec (.of R)))
      (yη : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) η))
      (yo : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) o))
      (spR : EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
      η.hom default = genericPoint (Spec (.of R)) ∧
      o.hom default = closedPoint R ∧
      @IsFractionRing R _ η.residueField _ (Spec.preimage η.hom).hom.toAlgebra ∧
      Function.Surjective (Spec.preimage o.hom).hom ∧
      r (η.hom default) = s'.hom default ∧
      r (o.hom default) = s.hom default ∧
      IsSpecializationMap (pullback.snd f r) η o yη yo spR ∧
      ∃ (eη : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη)
        (eo : EtaleFundamentalGroup (fiberOverGeometricPoint f s) x ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
        ∀ γ, eo (sp γ) = spR (eη γ) :=
  exists_isSpecializationMap_isomorphic_over_valuationRing f s' s x' x sp hsp
    properHenselianFiniteEtaleEquivalence

end AlgebraicGeometry

end
