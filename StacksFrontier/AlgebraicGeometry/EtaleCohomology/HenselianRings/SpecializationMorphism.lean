module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationLifting
public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# The specialization morphism of strict henselizations

A geometric point `t` of the strict henselization of a scheme `S` at a geometric point `s`
determines a unique morphism from the strict henselization of `S` at the image of `t` in `S` to
the strict henselization at `s`. The morphism lies over `S` and carries the canonical geometric
point of its source to `t`.

## Main definitions

* `AlgebraicGeometry.specializationMorphism` is that morphism.

## Main results

* `AlgebraicGeometry.strictHenselizationToBase_closedPoint` computes the image in `S` of the
  closed point of a strict henselization.
* `AlgebraicGeometry.existsUnique_specializationMorphism` characterizes the specialization
  morphism uniquely by its triangle over `S` and its triangle of geometric points.

## References

* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.Henselian.EtaleLifting

universe u

namespace AlgebraicGeometry

/-- An algebra map out of a separable extension factors through the separable closure of the
base in the target. -/
private def algHomIntoSeparableClosure (K : Type u) (E : Type u) (F : Type u)
    [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra.IsSeparable K E]
    (f : E →ₐ[K] F) : E →ₐ[K] separableClosure K F where
  toFun x := ⟨f x, by
    rw [mem_separableClosure_iff, IsSeparable, minpoly.algHom_eq f f.injective]
    exact Algebra.IsSeparable.isSeparable K x⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)
  map_zero' := Subtype.ext f.map_zero
  map_add' x y := Subtype.ext (f.map_add x y)
  commutes' r := Subtype.ext (f.commutes r)

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The closed point of the strict henselization at a geometric point maps to the image of that
geometric point in the scheme. -/
public theorem strictHenselizationToBase_closedPoint (s : GeometricPoint S) :
    strictHenselizationToBase B S hS s (closedPoint ↥(etaleLocalRing B S hS s)) =
      s.hom (closedPoint s.residueField) := by
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let A := etaleLocalRing B S hS s
  let f : ↥R →+* ↥A := structureSheafStalkFromLocalRing B S hS s
  have : IsLocalHom f := inferInstanceAs (IsLocalHom (algebraMap ↥R ↥A))
  have hclosed : Spec.map (CommRingCat.ofHom f) (closedPoint (↥A : Type u)) =
      closedPoint (↥R : Type u) :=
    PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap f)
  change (S.fromSpecStalk (s.hom (closedPoint s.residueField)))
      (Spec.map (CommRingCat.ofHom f) (closedPoint (↥A : Type u))) = _
  rw [hclosed, Scheme.fromSpecStalk_closedPoint]

/-- The image in `S` of a point of the strict henselization at a geometric point `s` specializes
to the image of `s`. -/
private theorem specializes_strictHenselizationToBase (s : GeometricPoint S)
    (x : PrimeSpectrum ↥(etaleLocalRing B S hS s)) :
    strictHenselizationToBase B S hS s x ⤳ s.hom (closedPoint s.residueField) := by
  have hx : x ⤳ closedPoint (↥(etaleLocalRing B S hS s) : Type u) :=
    IsLocalRing.specializes_closedPoint x
  exact (strictHenselizationToBase B S hS s).base.hom.map_specializes hx |>.trans_eq
    (congrArg _ (strictHenselizationToBase_closedPoint B S hS s))

/-- The prime of the ordinary local ring at the image of `s` which a point `x` of the strict
henselization contracts to is the contraction of the maximal ideal of the ordinary local ring at
the image of `x`. -/
private theorem comap_asIdeal_eq_comap_maximalIdeal (s : GeometricPoint S)
    (x : PrimeSpectrum ↥(etaleLocalRing B S hS s)) :
    Ideal.comap (algebraMap ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
          ↥(etaleLocalRing B S hS s)) x.asIdeal =
      Ideal.comap (S.presheaf.stalkSpecializes
          (specializes_strictHenselizationToBase B S hS s x)).hom
        (maximalIdeal ↥(S.presheaf.stalk (strictHenselizationToBase B S hS s x))) := by
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let A := etaleLocalRing B S hS s
  let y : S := (strictHenselizationToBase B S hS s) x
  let Ry := S.presheaf.stalk y
  have hys := specializes_strictHenselizationToBase B S hS s x
  let hR : ↥R →+* ↥Ry := (S.presheaf.stalkSpecializes hys).hom
  let z : Spec (.of ↥R) := Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥A)) x
  let w : Spec (.of ↥R) := PrimeSpectrum.comap hR (closedPoint (↥Ry : Type u))
  have hz : (S.fromSpecStalk (s.hom (closedPoint s.residueField))) z = y := rfl
  have hw : (S.fromSpecStalk (s.hom (closedPoint s.residueField))) w = y := by
    have h := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hys
    have h' := congrArg
      (fun f : Spec (.of ↥Ry) ⟶ S => f.base.hom (closedPoint (↥Ry : Type u))) h
    simp only [Scheme.Hom.comp_base] at h'
    change (S.fromSpecStalk (s.hom (closedPoint s.residueField))).base.hom w =
      (S.fromSpecStalk y).base.hom (closedPoint (↥Ry : Type u)) at h'
    rwa [Scheme.fromSpecStalk_closedPoint] at h'
  have hzw : z = w :=
    (IsPreimmersion.isEmbedding (S.fromSpecStalk (s.hom (closedPoint s.residueField)))).injective
      (hz.trans hw.symm)
  exact congrArg PrimeSpectrum.asIdeal hzw

/-- Restricting along a stalk specialization map does not change the composite to the scheme. -/
private theorem spec_map_comp_stalkSpecializes_fromSpecStalk {S : Scheme.{u}} {x y : S}
    (h : x ⤳ y) {T : Type u} [CommRing T] (u : ↥(S.presheaf.stalk x) →+* T) :
    Spec.map (CommRingCat.ofHom (u.comp (S.presheaf.stalkSpecializes h).hom)) ≫
        S.fromSpecStalk y =
      Spec.map (CommRingCat.ofHom u) ≫ S.fromSpecStalk x := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom u) ≫ ·)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h)

/-- Two ring maps which agree after composing with `Spec` and `fromSpecStalk` are equal. -/
private theorem ringHom_eq_of_spec_map_comp_fromSpecStalk_eq {S : Scheme.{u}} {x : S}
    {T : Type u} [CommRing T] {a b : ↥(S.presheaf.stalk x) →+* T}
    (h : Spec.map (CommRingCat.ofHom a) ≫ S.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom b) ≫ S.fromSpecStalk x) : a = b :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

/-- Evaluating a germ at `s` in the residue field of a point `x` of the strict henselization is
evaluating it in the residue field of the image of `x`, followed by the residue-field map of the
structure morphism. -/
private theorem residueFieldIso_inv_comp_algebraMap_eq (s : GeometricPoint S)
    (x : PrimeSpectrum ↥(etaleLocalRing B S hS s)) :
    (((Scheme.Spec.residueFieldIso (.of ↥(etaleLocalRing B S hS s)) x).inv.hom).comp
          (algebraMap ↥(etaleLocalRing B S hS s) x.asIdeal.ResidueField)).comp
        (algebraMap ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
          ↥(etaleLocalRing B S hS s)) =
      ((strictHenselizationToBase B S hS s).residueFieldMap x).hom.comp
        ((residue ↥(S.presheaf.stalk (strictHenselizationToBase B S hS s x))).comp
          (S.presheaf.stalkSpecializes
            (specializes_strictHenselizationToBase B S hS s x)).hom) := by
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let A := etaleLocalRing B S hS s
  let X := Spec (.of ↥A)
  let q : Ideal ↥A := x.asIdeal
  let y : S := (strictHenselizationToBase B S hS s) x
  let Ry := S.presheaf.stalk y
  have hys := specializes_strictHenselizationToBase B S hS s x
  let hR : ↥R →+* ↥Ry := (S.presheaf.stalkSpecializes hys).hom
  let eX := Scheme.Spec.residueFieldIso (.of ↥A) x
  let fxy := (strictHenselizationToBase B S hS s).residueFieldMap x
  have hscheme :
      Spec.map (CommRingCat.ofHom
        ((eX.inv.hom.comp (algebraMap ↥A q.ResidueField)).comp (algebraMap ↥R ↥A))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
      Spec.map (CommRingCat.ofHom (fxy.hom.comp ((residue (↥Ry : Type u)).comp hR))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) := by
    have h0 : Spec.map (CommRingCat.ofHom
          ((eX.inv.hom.comp (algebraMap ↥A q.ResidueField)).comp (algebraMap ↥R ↥A))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
        (Spec.map eX.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A q.ResidueField))) ≫
          strictHenselizationToBase B S hS s := by
      rw [show CommRingCat.ofHom
            ((eX.inv.hom.comp (algebraMap ↥A q.ResidueField)).comp (algebraMap ↥R ↥A)) =
          CommRingCat.ofHom (algebraMap ↥R ↥A) ≫
            (CommRingCat.ofHom (algebraMap ↥A q.ResidueField) ≫ eX.inv) from rfl,
        Spec.map_comp, Spec.map_comp]
      simp only [strictHenselizationToBase, Category.assoc]
    have hLHS : Spec.map (CommRingCat.ofHom
          ((eX.inv.hom.comp (algebraMap ↥A q.ResidueField)).comp (algebraMap ↥R ↥A))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
        X.fromSpecResidueField x ≫ strictHenselizationToBase B S hS s :=
      h0.trans (congrArg (fun m => m ≫ strictHenselizationToBase B S hS s)
        (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of ↥A) x))
    have hRHS : Spec.map (CommRingCat.ofHom
          (fxy.hom.comp ((residue (↥Ry : Type u)).comp hR))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
        Spec.map fxy ≫ S.fromSpecResidueField y := by
      refine (spec_map_comp_stalkSpecializes_fromSpecStalk hys
        (fxy.hom.comp (residue (↥Ry : Type u)))).trans ?_
      exact (congrArg (· ≫ S.fromSpecStalk y)
        (Spec.map_comp (CommRingCat.ofHom (residue (↥Ry : Type u))) fxy)).trans
        (Category.assoc _ _ _)
    rw [hLHS, hRHS]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (strictHenselizationToBase B S hS s) x).symm
  exact ringHom_eq_of_spec_map_comp_fromSpecStalk_eq hscheme

/-- The specialization morphism of strict henselizations exists and is unique: a geometric point
`t` of the strict henselization at `s` determines exactly one morphism from the strict
henselization at the image of `t` in `S` to the strict henselization at `s` which lies over `S`
and carries the canonical geometric point of its source to `t`. -/
@[stacks 0GJ4 "specialization_morphism_of_strict_henselizations"]
public theorem existsUnique_specializationMorphism (s : GeometricPoint S)
    (t : GeometricPoint (strictHenselization B S hS s)) :
    let T := strictHenselization B S hS s
    let p := strictHenselizationToBase B S hS s
    let tS := t.map p
    ∃! c : strictHenselization B S hS tS ⟶ T,
      (c ≫ p = strictHenselizationToBase B S hS tS) ∧
      (geometricPointToStrictHenselization B S hS tS ≫ c = t.hom) := by
  dsimp only
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let A := etaleLocalRing B S hS s
  let X := Spec (.of ↥A)
  let F := t.residueField
  let x : PrimeSpectrum ↥A := t.hom (closedPoint F)
  let q : Ideal ↥A := x.asIdeal
  let : q.IsPrime := x.2
  let tS := t.map (strictHenselizationToBase B S hS s)
  let y : S := (strictHenselizationToBase B S hS s) x
  have hys : y ⤳ s.hom (closedPoint s.residueField) :=
    specializes_strictHenselizationToBase B S hS s x
  let Ry := S.presheaf.stalk y
  let K := (ResidueField (↥Ry : Type u))
  let E := (X.residueField x : Type u)
  let fxy := (strictHenselizationToBase B S hS s).residueFieldMap x
  let fyΩ := Scheme.descResidueField (Scheme.stalkClosedPointTo tS.hom)
  let fxΩ := Scheme.descResidueField (Scheme.stalkClosedPointTo t.hom)
  let : Algebra K E := fxy.hom.toAlgebra
  let : Algebra K F := fyΩ.hom.toAlgebra
  have hres : fxy ≫ fxΩ = fyΩ := by
    dsimp [fxy, fxΩ, fyΩ, tS, GeometricPoint.map]
    exact (Scheme.descResidueField_stalkClosedPointTo_comp
      (strictHenselizationToBase B S hS s) t.hom).symm
  let fEΩ : E →ₐ[K] F :=
    { toRingHom := fxΩ.hom
      commutes' := fun r => by
        change fxΩ.hom (fxy.hom r) = fyΩ.hom r
        exact congrArg (fun g : K →+* F => g r) (congrArg CommRingCat.Hom.hom hres) }
  have hsep : Algebra.IsSeparable K E := by
    dsimp only [K, E, fxy]
    exact isSeparable_residueField_strictHenselizationToBase B S hS s x
  let Ksep := separableClosure (ResidueField (↥Ry : Type u)) F
  let φ := algHomIntoSeparableClosure K E F fEΩ
  let Tt := IsLocalRing.henselizationTower (↥Ry) Ksep
  let C := Tt.strictHenselization
  let : Algebra (↥Ry) ↥(etaleLocalRing B S hS tS) := etaleLocalRingAlgebra B S hS tS
  let : IsLocalHom (algebraMap (↥Ry) C) := by
    rw [IsScalarTower.algebraMap_eq (↥Ry) Tt.henselization C]
    infer_instance
  let e := etaleLocalRing_strictHenselization_canonical B S hS tS Tt
  let eAlg : C ≃ₐ[↑Ry] ↥(etaleLocalRing B S hS tS) :=
    { e.1 with commutes' := fun r => e.2.1 r }
  let hR : ↥R →+* ↥Ry := (S.presheaf.stalkSpecializes hys).hom
  let gR : ↥R →+* C := (algebraMap (↥Ry) C).comp hR
  let : Algebra ↥R C := gR.toAlgebra
  let p0 : Ideal ↥R := q.comap (algebraMap ↥R ↥A)
  let : p0.IsPrime := Ideal.IsPrime.comap _
  let eX := Scheme.Spec.residueFieldIso (.of ↥A) x
  let τ : q.ResidueField →+* ResidueField C :=
    (Tt.strictHenselizationResidueEquiv).toRingHom.comp (φ.toRingHom.comp eX.inv.hom)
  have hcontract : p0 = (maximalIdeal (↥Ry : Type u)).comap hR :=
    comap_asIdeal_eq_comap_maximalIdeal B S hS s x
  have hsource : (eX.inv.hom.comp (algebraMap ↥A q.ResidueField)).comp
      (algebraMap ↥R ↥A) = fxy.hom.comp ((residue (↥Ry : Type u)).comp hR) :=
    residueFieldIso_inv_comp_algebraMap_eq B S hS s x
  have hp : p0 = (maximalIdeal C).comap (algebraMap ↥R C) := by
    rw [hcontract, ← IsLocalRing.maximalIdeal_comap (algebraMap (↥Ry) C), Ideal.comap_comap]
    rfl
  have hτ : τ.comp (residueFieldMapFib p0 q rfl) = residueFieldMapBase p0 hp := by
    refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_)
    have hr : τ (algebraMap ↥A q.ResidueField (algebraMap ↥R ↥A r)) =
        residue C (algebraMap ↥R C r) := by
      change Tt.strictHenselizationResidueEquiv
          (φ (eX.inv.hom (algebraMap ↥A q.ResidueField (algebraMap ↥R ↥A r)))) =
        residue C ((algebraMap (↥Ry) C) (hR r))
      rw [show eX.inv.hom (algebraMap ↥A q.ResidueField (algebraMap ↥R ↥A r)) =
        algebraMap K E (residue (↥Ry : Type u) (hR r)) from (RingHom.ext_iff.mp hsource) r]
      rw [φ.commutes]
      exact IsLocalRing.HenselizationTower.strictHenselizationResidueEquiv_residue Tt (hR r)
    simpa only [RingHom.coe_comp, Function.comp_apply, residueFieldMapFib,
      Ideal.ResidueField.map_algebraMap, residueFieldMapBase,
      Ideal.ResidueField.lift_algebraMap] using hr
  have hindLift : (CommAlgCat.etale.{u} ↥R).ind.{u} (CommAlgCat.of ↥R (ULift.{u} ↥A)) :=
    indEtale_etaleLocalRing B S hS s
  obtain ⟨f, hf, hfu⟩ : ∃! f : ↥A →ₐ[↥R] C,
      q = (maximalIdeal C).comap (f : ↥A →+* C) ∧
        InducesResidueMap q (f : ↥A →+* C) τ :=
    ⟨algHom hindLift p0 hp q rfl τ hτ, algHom_spec hindLift p0 hp q rfl τ hτ,
      fun d hd => algHom_unique hindLift p0 hp q rfl τ hτ d hd⟩
  let : Algebra ↥R ↥(etaleLocalRing B S hS tS) :=
    ((algebraMap (↥Ry) ↥(etaleLocalRing B S hS tS)).comp hR).toAlgebra
  let g : ↥A →ₐ[↥R] ↥(etaleLocalRing B S hS tS) :=
    { toRingHom := eAlg.toRingEquiv.toRingHom.comp f.toRingHom
      commutes' := fun r => by
        change eAlg (f (algebraMap ↥R ↥A r)) =
          algebraMap ↥R ↥(etaleLocalRing B S hS tS) r
        rw [f.commutes]
        change eAlg (algebraMap (↥Ry) C (hR r)) = _
        exact e.2.1 (hR r) }
  let c : strictHenselization B S hS tS ⟶ X := Spec.map (CommRingCat.ofHom g.toRingHom)
  have ht : Spec.map (CommRingCat.ofHom
      (fxΩ.hom.comp (eX.inv.hom.comp (algebraMap ↥A q.ResidueField)))) = t.hom := by
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change Spec.map fxΩ ≫ Spec.map eX.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥A q.ResidueField)) = t.hom
    rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F X t.hom
  refine ⟨c, ?_, ?_⟩
  · constructor
    · change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥A)) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥Ry)
          ↥(etaleLocalRing B S hS tS))) ≫ S.fromSpecStalk y
      have hg : g.toRingHom.comp (algebraMap ↥R ↥A) =
          (algebraMap (↥Ry) ↥(etaleLocalRing B S hS tS)).comp hR :=
        RingHom.ext g.commutes
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hg,
        spec_map_comp_stalkSpecializes_fromSpecStalk hys]
    · change Spec.map (CommRingCat.ofHom
          (structureSheafStalkToGeometricField B S hS tS)) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) = t.hom
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← ht]
      apply congrArg (fun hom => Spec.map (CommRingCat.ofHom hom))
      ext a
      change structureSheafStalkToGeometricField B S hS tS (e.1 (f a)) = _
      rw [e.2.2]
      have hfa := congrArg (fun hom : ↥A →+* ResidueField C => hom a) hf.2
      change τ (algebraMap ↥A q.ResidueField a) = residue C (f a) at hfa
      rw [← hfa]
      change ((Tt.strictHenselizationResidueEquiv.symm
        (Tt.strictHenselizationResidueEquiv
          (φ (eX.inv.hom (algebraMap ↥A q.ResidueField a))))) : F) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
  · intro d hd
    let dRing := (Spec.homEquiv d).hom
    have hdSpec : Spec.map (CommRingCat.ofHom dRing) = d :=
      Spec.homEquiv.symm_apply_apply d
    have hdBase : dRing.comp (algebraMap ↥R ↥A) =
        (algebraMap (↥Ry) ↥(etaleLocalRing B S hS tS)).comp hR := by
      have hright := spec_map_comp_stalkSpecializes_fromSpecStalk hys
        (algebraMap (↥Ry) ↥(etaleLocalRing B S hS tS))
      have hleft : Spec.map (CommRingCat.ofHom (dRing.comp (algebraMap ↥R ↥A))) ≫
          S.fromSpecStalk (s.hom (closedPoint s.residueField)) =
          d ≫ strictHenselizationToBase B S hS s := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hdSpec]
        rfl
      exact ringHom_eq_of_spec_map_comp_fromSpecStalk_eq (hleft.trans (hd.1.trans hright.symm))
    let dAlg : ↥A →ₐ[↥R] C :=
      { toRingHom := eAlg.symm.toRingEquiv.toRingHom.comp dRing
        commutes' := fun r => by
          change eAlg.symm (dRing (algebraMap ↥R ↥A r)) = algebraMap ↥R C r
          rw [show dRing (algebraMap ↥R ↥A r) =
            algebraMap (↥Ry) ↥(etaleLocalRing B S hS tS) (hR r) from
              congrArg (fun hom : ↥R →+* ↥(etaleLocalRing B S hS tS) => hom r) hdBase]
          exact eAlg.symm.commutes (hR r) }
    have hdPoint : (structureSheafStalkToGeometricField B S hS tS).comp dRing =
        fxΩ.hom.comp (eX.inv.hom.comp (algebraMap ↥A q.ResidueField)) := by
      have heq : Spec.map (CommRingCat.ofHom
          ((structureSheafStalkToGeometricField B S hS tS).comp dRing)) =
          Spec.map (CommRingCat.ofHom
            (fxΩ.hom.comp (eX.inv.hom.comp (algebraMap ↥A q.ResidueField)))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hdSpec, ht]
        exact hd.2
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective heq)
    have hdResidue : InducesResidueMap q dAlg.toRingHom τ := by
      ext a
      have hpoint := congrArg (fun hom : ↥A →+* F => hom a) hdPoint
      change structureSheafStalkToGeometricField B S hS tS (dRing a) =
        fxΩ.hom (eX.inv.hom (algebraMap ↥A q.ResidueField a)) at hpoint
      have heval' : e.1 (dAlg a) = dRing a := eAlg.apply_symm_apply (dRing a)
      have heval :=
        (congrArg (structureSheafStalkToGeometricField B S hS tS) heval').symm.trans
          (e.2.2 (dAlg a))
      have hsub : Tt.strictHenselizationResidueEquiv.symm (residue C (dAlg a)) =
          φ (eX.inv.hom (algebraMap ↥A q.ResidueField a)) :=
        Subtype.ext (heval.symm.trans hpoint)
      have heq := congrArg Tt.strictHenselizationResidueEquiv hsub
      rw [RingEquiv.apply_symm_apply] at heq
      exact heq.symm
    have hdIdeal : q = (maximalIdeal C).comap dAlg.toRingHom :=
      calc
        q = RingHom.ker (algebraMap ↥A q.ResidueField) :=
          (Ideal.ker_algebraMap_residueField q).symm
        _ = RingHom.ker (τ.comp (algebraMap ↥A q.ResidueField)) :=
          (RingHom.ker_comp_of_injective _ τ.injective).symm
        _ = RingHom.ker ((residue C).comp dAlg.toRingHom) := by rw [hdResidue]
        _ = (RingHom.ker (residue C)).comap dAlg.toRingHom := (RingHom.comap_ker _ _).symm
        _ = (maximalIdeal C).comap dAlg.toRingHom := by rw [IsLocalRing.ker_residue]
    have hdAlg := hfu dAlg ⟨hdIdeal, hdResidue⟩
    rw [← hdSpec]
    apply congrArg (fun hom : ↥A →+* ↥(etaleLocalRing B S hS tS) =>
      Spec.map (CommRingCat.ofHom hom))
    change dRing = g.toRingHom
    ext a
    have heq := congrArg (fun hom : ↥A →ₐ[↥R] C => eAlg (hom a)) hdAlg
    exact (eAlg.apply_symm_apply (dRing a)).symm.trans heq

/-- The specialization morphism of strict henselizations attached to a geometric point of the
strict henselization at `s`: the unique morphism over `S` from the strict henselization at the
image of that point in `S` to the strict henselization at `s` which carries the canonical
geometric point of its source to the given one. -/
@[stacks 0GJ4 "specialization_morphism_of_strict_henselizations"]
public def specializationMorphism (s : GeometricPoint S)
    (t : GeometricPoint (strictHenselization B S hS s)) :
    strictHenselization B S hS (t.map (strictHenselizationToBase B S hS s)) ⟶
      strictHenselization B S hS s :=
  (existsUnique_specializationMorphism B S hS s t).exists.choose

end AlgebraicGeometry

end
