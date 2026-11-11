module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.CRISExtensionCoproductMap

/-!
# Divided power differentials as the diagonal conormal module, in `CRIS(C/A)`

In Situation 07MD, let `X = (B, J, δ)` be an object of the big crystalline category `CRIS(C/A)`
and `Y = (B(1), J(1), δ(1))` a coproduct of `X` with itself in `CRIS(C/A)`, with coprojections
`s₀, s₁` and `K = Ker(B(1) → B)`.  This file constructs the canonical `B`-linear identification
`Ω_{B/A,δ} ≅ K / (K² + (K ∩ J(1))^{[2]})` carrying `d b` to the class of `s₁ b - s₀ b`, and
proves Stacks Lemma 07HV.

## Main results

* `Crystalline.DividedPowerThickening.dividedPowerDifferentialsEquivDiagonalConormal` — the
  canonical identification.
* `Crystalline.DividedPowerThickening.dividedPowerDifferentialsEquivDiagonalConormal_apply` — it
  sends `d b` to the class of `s₁ b - s₀ b`.
* `Crystalline.DividedPowerThickening.isSubDPIdeal_and_existsUnique_dividedPowerDifferentialsEquiv`
  — Stacks 07HV: both parts of the lemma, the identification being the unique `B`-linear
  isomorphism with `d b ↦ [s₁ b - s₀ b]`.

## Implementation notes

The map from differentials to the conormal module comes from the universal property of divided
power differentials applied to the derivation `b ↦ [s₁ b - s₀ b]`.  The map back comes from the
universal property of the coproduct in `CRIS(C/A)` against the first-order thickening `B ⊕ Ω` of
`X`, which is an object of `CRIS(C/A)` through `C → B/J = (B ⊕ Ω)/(J ⊕ Ω)`; the two maps
`B → B ⊕ Ω` given by `b ↦ b` and `b ↦ b + d b` are morphisms of `CRIS(C/A)`.

The conormal module is a `B`-module through the first coprojection `s₀`.

These declarations generalize those of the same names in the namespace `Crystalline`, which are
stated for the full subcategory `Cris(C/A)`.

## References

* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DividedPowerRing

universe u v w

namespace Crystalline

namespace DividedPowerThickening

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : DividedPowerThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

/-- The module of divided power differentials is a module over the opposite ring. -/
private noncomputable instance dividedPowerDifferentialsModuleOpp [Algebra S.A X.ring] :
    Module X.ringᵐᵒᵖ (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) :=
  Module.compHom _ (RingEquiv.toOpposite X.ring).symm.toRingHom

private instance dividedPowerDifferentialsCentral [Algebra S.A X.ring] :
    IsCentralScalar X.ring (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) :=
  ⟨by intro a m; change MulOpposite.unop (MulOpposite.op a) • m = a • m; rfl⟩

/-- Restricting scalars along `s₀` and then the diagonal map is the identity on `X`. -/
private theorem isScalarTower_dividedPowerDifferentials
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    let _ : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    let _ : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
    let _ : Module Y.ring (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) :=
      Module.compHom _ (diagonalMap h).hom.toRingHom
    IsScalarTower X.ring Y.ring
      (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) := by
  intro _ _ _
  refine IsScalarTower.of_algebraMap_smul (fun a m ↦ ?_)
  change (diagonalMap h).hom.toRingHom (s₀.hom.toRingHom a) • m = a • m
  rw [diagonalMap_s₀ h]

/-- The linear map from the diagonal conormal module to the divided power differentials, induced
by the coordinate map of the coproduct map into `B ⊕ Ω`. -/
private noncomputable def diagonalConormalToDividedPowerDifferentials
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    diagonalConormal h →ₗ[X.ring]
      dividedPowerDifferentials (A := S.A) X.ring.dividedPowers := by
  classical
  letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  letI : Module X.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.toRingHom
  letI : Module Y.ring
      (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) :=
    Module.compHom _ (diagonalMap h).hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.ring)
  let c := diagonalKernelCoordinateMap h
    (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) d
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h _ d
  exact ((diagonalRelations h).liftQ c hc).restrictScalars X.ring |>.comp
    (diagonalConormalLinearEquiv h).toLinearMap

/-- The derivation `b ↦ [s₁ b - s₀ b]`, as an `A`-derivation into the diagonal conormal module. -/
private noncomputable def diagonalDifferenceKaehlerDerivation
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    letI : Module S.A (diagonalConormal h) :=
      Module.compHom (diagonalConormal h) X.fromBase.toRingHom
    letI : IsScalarTower S.A X.ring (diagonalConormal h) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Derivation S.A X.ring (diagonalConormal h) :=
  letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  letI : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.fromBase.toRingHom
  letI : IsScalarTower S.A X.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let d := diagonalDifferenceDerivation h
  { toFun := d.1
    map_add' := d.1.map_add
    map_smul' := by
      intro a b
      change d.1 (X.fromBase.toRingHom a * b) =
        X.fromBase.toRingHom a • d.1 b
      rw [d.1.leibniz, d.map_ringHom]
      simp
    map_one_eq_zero' := d.1.map_one_eq_zero
    leibniz' := d.1.leibniz }

/-- The linear map from divided power differentials to the diagonal conormal module, induced by
the divided power derivation `b ↦ [s₁ b - s₀ b]`. -/
private noncomputable def dividedPowerDifferentialsToDiagonalConormal
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentials (A := S.A) X.ring.dividedPowers →ₗ[X.ring]
      diagonalConormal h := by
  classical
  letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  letI : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.fromBase.toRingHom
  letI : IsScalarTower S.A X.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let d := diagonalDifferenceDerivation h
  let D := diagonalDifferenceKaehlerDerivation h
  let L : Ω[X.ring⁄S.A] →ₗ[X.ring]
      diagonalConormal h := D.liftKaehlerDifferential
  let R := dividedPowerDifferentialRelations (A := S.A) X.ring.dividedPowers
  have hR : R ≤ LinearMap.ker L := by
    change Submodule.span X.ring
      (Set.range fun z : X.ring.ideal × ℕ ↦
        dividedPowerDifferentialRelation X.ring.dividedPowers z.1 z.2) ≤
      LinearMap.ker L
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, n⟩, rfl⟩
    change L (KaehlerDifferential.D S.A X.ring
        (X.ring.dividedPowers.dpow (n + 1) x) -
      X.ring.dividedPowers.dpow n x • KaehlerDifferential.D S.A X.ring x) = 0
    dsimp only [L]
    rw [map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    change d.1 (X.ring.dividedPowers.dpow (n + 1) x) -
      X.ring.dividedPowers.dpow n x • d.1 x = 0
    have hx : x.1 ∈ X.ring.ideal := x.2
    exact sub_eq_zero.mpr (d.map_dpow (n + 1) (by omega) x.1 hx)
  exact R.liftQ L hR

private theorem diagonalConormalToDividedPowerDifferentials_difference
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (b : X.ring) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    diagonalConormalToDividedPowerDifferentials h (diagonalDifference h b) =
      dividedPowerDifferential (A := S.A) X.ring.dividedPowers b := by
  classical
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  let : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let : Module X.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.toRingHom
  let : Module Y.ring
      (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) :=
    Module.compHom _ (diagonalMap h).hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.ring)
  let c := diagonalKernelCoordinateMap h
    (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) d
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h _ d
  have h0 := diagonalExtensionCoproductMap_inl h
    (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) d b
  have h1 := diagonalExtensionCoproductMap_inr h
    (dividedPowerDifferentials (A := S.A) X.ring.dividedPowers) d b
  change ((diagonalRelations h).liftQ c hc)
      (diagonalConormalLinearEquiv h (diagonalDifference h b)) = _
  rw [diagonalConormalLinearEquiv_apply]
  change c ⟨s₁.hom.toRingHom b - s₀.hom.toRingHom b, _⟩ = _
  change ((diagonalExtensionCoproductMap h _ d).hom.toRingHom
      (s₁.hom.toRingHom b - s₀.hom.toRingHom b)).snd = _
  rw [map_sub, h1, h0]
  change (graphRingHom d b).snd - (TrivSqZeroExt.inl b).snd = _
  simp [graphRingHom, graphFun, d, universalDividedPowerDerivation]
  rfl

/-- The map to the conormal module sends `d b` to the class of `s₁ b - s₀ b`. -/
private theorem dividedPowerDifferentialsToDiagonalConormal_apply
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (b : X.ring) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentialsToDiagonalConormal h
      (dividedPowerDifferential (A := S.A) X.ring.dividedPowers b) =
        diagonalDifference h b := by
  classical
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  let : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.fromBase.toRingHom
  let : IsScalarTower S.A X.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  dsimp only [dividedPowerDifferentialsToDiagonalConormal]
  exact Derivation.liftKaehlerDifferential_comp_D (diagonalDifferenceKaehlerDerivation h) b

private noncomputable instance diagonalConormalModuleOpp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Module X.ringᵐᵒᵖ (diagonalConormal h) :=
  Module.compHom _ (RingEquiv.toOpposite X.ring).symm.toRingHom

private noncomputable instance diagonalConormalCentral
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
  IsCentralScalar X.ring (diagonalConormal h) :=
  ⟨by intro a m; change MulOpposite.unop (MulOpposite.op a) • m = a • m; rfl⟩

private theorem diagonalClass_zero
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClass h 0 = 0 := by
  have hr : diagonalClassRep h 0 = 0 := by
    apply Subtype.ext
    change 0 - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom 0) = 0
    rw [map_zero, map_zero]
    simp
  change Submodule.Quotient.mk (diagonalClassRep h 0) = 0
  rw [hr]
  simp

private theorem diagonalClass_one
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClass h 1 = 0 := by
  have hr : diagonalClassRep h 1 = 0 := by
    apply Subtype.ext
    change 1 - s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom 1) = 0
    rw [map_one, map_one]
    simp
  change Submodule.Quotient.mk (diagonalClassRep h 1) = 0
  rw [hr]
  simp

private noncomputable def diagonalClassGraphRingHom
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
    Y.ring →+* TrivSqZeroExt X.ring (diagonalConormal h) := by
  classical
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let q : Y.ring →+* X.ring := (diagonalMap h).hom.toRingHom
  refine {
    toFun := fun y ↦ (q y, diagonalClass h y)
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · exact TrivSqZeroExt.ext (map_one q) (diagonalClass_one h)
  · exact fun y z => TrivSqZeroExt.ext (map_mul q y z) (diagonalClass_mul h y z)
  · exact TrivSqZeroExt.ext (map_zero q) (diagonalClass_zero h)
  · exact fun y z => TrivSqZeroExt.ext (map_add q y z) (diagonalClass_add h y z)

private noncomputable def diagonalClassGraphDPMorphism
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
    DividedPowers.DPMorphism Y.ring.dividedPowers
      (Classical.choose (firstOrderExtension_dividedPowers X.ring
        (diagonalConormal h))) := by
  classical
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let δ := Classical.choose
    (firstOrderExtension_dividedPowers X.ring (diagonalConormal h))
  let φ := diagonalClassGraphRingHom h
  have hcoords := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.ring (diagonalConormal h))).1
  have hfst (y : Y.ring) : (φ y).fst = (diagonalMap h).hom.toRingHom y := rfl
  refine DividedPowers.DPMorphism.mk' (f := φ) ?_
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change (diagonalMap h).hom.toRingHom y ∈ X.ring.ideal
    exact (Ideal.map_le_iff_le_comap.mp (diagonalMap h).hom.ideal_comp) hy
  · intro n y hy
    have hy' : φ y ∈ firstOrderExtensionIdeal X.ring (diagonalConormal h) :=
      (Ideal.map_le_iff_le_comap.mp (diagonalMap h).hom.ideal_comp) hy
    by_cases hn0 : n = 0
    · subst n
      change δ.dpow 0 (φ y) = φ (Y.ring.dividedPowers.dpow 0 y)
      rw [δ.dpow_zero hy', Y.ring.dividedPowers.dpow_zero hy]
      apply TrivSqZeroExt.ext
      · change 1 = (diagonalClassGraphRingHom h 1).fst
        simp [diagonalClassGraphRingHom]
      · change 0 = diagonalClass h 1
        exact (diagonalClass_one h).symm
    · by_cases hn1 : n = 1
      · subst n
        change δ.dpow 1 (φ y) = φ (Y.ring.dividedPowers.dpow 1 y)
        rw [δ.dpow_one hy', Y.ring.dividedPowers.dpow_one hy]
      · have hn2 : 2 ≤ n := by omega
        have hc := hcoords n (φ y) hn2 hy'
        have hqdp : (diagonalMap h).hom.toRingHom
            (Y.ring.dividedPowers.dpow n y) =
              X.ring.dividedPowers.dpow n
                ((diagonalMap h).hom.toRingHom y) :=
          (diagonalMap h).hom.isDPMorphism.dpow_comp y hy |>.symm
        have hclass := diagonalClass_dpow h n y hn2 hy
        apply TrivSqZeroExt.ext
        · calc
            (δ.dpow n (φ y)).fst =
                X.ring.dividedPowers.dpow n
                  ((diagonalMap h).hom.toRingHom y) := hc.1
            _ = (diagonalMap h).hom.toRingHom
                (Y.ring.dividedPowers.dpow n y) := hqdp.symm
            _ = (φ (Y.ring.dividedPowers.dpow n y)).fst := (hfst _).symm
        · calc
            (δ.dpow n (φ y)).snd =
                X.ring.dividedPowers.dpow (n - 1)
                  ((diagonalMap h).hom.toRingHom y) • diagonalClass h y := hc.2
            _ = diagonalClass h (Y.ring.dividedPowers.dpow n y) := hclass.symm
            _ = (φ (Y.ring.dividedPowers.dpow n y)).snd := rfl

private theorem diagonalClassGraph_quotientMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
    Ideal.quotientMap (firstOrderExtensionIdeal X.ring (diagonalConormal h))
      (diagonalClassGraphDPMorphism h).toRingHom
      (Ideal.map_le_iff_le_comap.mp
        (diagonalClassGraphDPMorphism h).ideal_comp) =
      (firstOrderExtensionQuotientMap X.ring (diagonalConormal h)).comp
        (DividedPowerRing.quotientRingHom (diagonalMap h).hom) := by
  classical
  let : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let φ := diagonalClassGraphDPMorphism h
  ext z
  -- `ext` has reduced the quotient variable to a representative in the ring.
  let y := z
  simp only [RingHom.comp_apply]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  change φ.toRingHom y - TrivSqZeroExt.inl ((diagonalMap h).hom.toRingHom y) ∈
    firstOrderExtensionIdeal X.ring (diagonalConormal h)
  change (TrivSqZeroExt.fstHom X.ring X.ring (diagonalConormal h)).toRingHom
      (φ.toRingHom y - TrivSqZeroExt.inl ((diagonalMap h).hom.toRingHom y)) ∈
    X.ring.ideal
  change (diagonalClassGraphRingHom h y).fst -
      (diagonalMap h).hom.toRingHom y ∈ X.ring.ideal
  change (diagonalMap h).hom.toRingHom y -
      (diagonalMap h).hom.toRingHom y ∈ X.ring.ideal
  simpa only [sub_self] using X.ring.ideal.zero_mem

private noncomputable def diagonalClassGraphMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Y ⟶ firstOrderExtensionThickening X (diagonalConormal h) := by
  classical
  letI : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let E := firstOrderExtensionThickening X (diagonalConormal h)
  letI : CommRing (firstOrderExtension X.ring (diagonalConormal h)) := E.ring.commRing
  let φ := diagonalClassGraphDPMorphism h
  refine { hom := φ, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    apply TrivSqZeroExt.ext
    · have hb := congrArg (fun f : DividedPowers.DPMorphism
          S.A.dividedPowers X.ring.dividedPowers => f.toRingHom a)
        (diagonalMap h).fromBase_comp
      change (diagonalMap h).hom.toRingHom
        (Y.fromBase.toRingHom a) = X.fromBase.toRingHom a at hb
      exact hb
    · have hs := congrArg (fun f : DividedPowers.DPMorphism
          S.A.dividedPowers Y.ring.dividedPowers => f.toRingHom a)
        s₀.fromBase_comp
      change s₀.hom.toRingHom (X.fromBase.toRingHom a) =
        Y.fromBase.toRingHom a at hs
      have hz := diagonalClass_s₀ h (X.fromBase.toRingHom a)
      change diagonalClass h (Y.fromBase.toRingHom a) = 0
      rw [← hs]
      exact hz
  · change (Ideal.quotientMap (firstOrderExtensionIdeal X.ring (diagonalConormal h)) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)).comp Y.toQuotient =
      E.toQuotient
    rw [diagonalClassGraph_quotientMap h]
    change ((firstOrderExtensionQuotientMap X.ring (diagonalConormal h)).comp
      (DividedPowerRing.quotientRingHom (diagonalMap h).hom)).comp
        Y.toQuotient = E.toQuotient
    rw [RingHom.comp_assoc, (diagonalMap h).toQuotient_comp]

/-- The first coprojection followed by the coproduct map is the zero map into the extension. -/
private theorem inl_comp_diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring X.fromBase.toRingHom M) :
    (BinaryCofan.mk s₀ s₁).inl ≫ diagonalExtensionCoproductMap h M d =
      firstOrderExtensionMapZero X M := by
  simpa [diagonalExtensionCoproductMap] using BinaryCofan.IsColimit.inl_desc h
    (firstOrderExtensionMapZero X M) (firstOrderExtensionMapGraph X M d)

/-- The second coprojection followed by the coproduct map is the graph map into the extension. -/
private theorem inr_comp_diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring X.fromBase.toRingHom M) :
    (BinaryCofan.mk s₀ s₁).inr ≫ diagonalExtensionCoproductMap h M d =
      firstOrderExtensionMapGraph X M d := by
  simpa [diagonalExtensionCoproductMap] using BinaryCofan.IsColimit.inr_desc h
    (firstOrderExtensionMapZero X M) (firstOrderExtensionMapGraph X M d)

private theorem diagonalClassGraphMap_eq_coproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClassGraphMap h =
      diagonalExtensionCoproductMap h (diagonalConormal h)
        (diagonalDifferenceDerivation h) := by
  let M := diagonalConormal h
  let d := diagonalDifferenceDerivation h
  let f₀ := firstOrderExtensionMapZero X M
  let f₁ := firstOrderExtensionMapGraph X M d
  have h0 : (BinaryCofan.mk s₀ s₁).inl ≫ diagonalClassGraphMap h = f₀ := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    apply TrivSqZeroExt.ext
    · exact diagonalMap_s₀ h x
    · change diagonalClass h (s₀.hom.toRingHom x) = 0
      exact diagonalClass_s₀ h x
  have h1 : (BinaryCofan.mk s₀ s₁).inr ≫ diagonalClassGraphMap h = f₁ := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    apply TrivSqZeroExt.ext
    · exact diagonalMap_s₁ h x
    · change diagonalClass h (s₁.hom.toRingHom x) = diagonalDifference h x
      exact diagonalClass_s₁ h x
  exact BinaryCofan.IsColimit.hom_ext h
    (h0.trans (inl_comp_diagonalExtensionCoproductMap h M d).symm)
    (h1.trans (inr_comp_diagonalExtensionCoproductMap h M d).symm)

private theorem diagonalClassGraphMap_factorization
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    let Ω := dividedPowerDifferentials (A := S.A) X.ring.dividedPowers
    let M := diagonalConormal h
    let d := universalDividedPowerDerivation (A := S.A) (B := X.ring)
    (diagonalExtensionCoproductMap h Ω d ≫
      firstOrderExtensionLinearMap X Ω M
        (dividedPowerDifferentialsToDiagonalConormal h)) =
      diagonalClassGraphMap h := by
  classical
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  let Ω := dividedPowerDifferentials (A := S.A) X.ring.dividedPowers
  let M := diagonalConormal h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.ring)
  let dM := diagonalDifferenceDerivation h
  let β := dividedPowerDifferentialsToDiagonalConormal h
  let ψΩ := diagonalExtensionCoproductMap h Ω d
  let ψM := diagonalExtensionCoproductMap h M dM
  let F : firstOrderExtensionThickening X Ω ⟶ firstOrderExtensionThickening X M :=
    firstOrderExtensionLinearMap X Ω M β
  have hF0 : firstOrderExtensionMapZero X Ω ≫ F =
      firstOrderExtensionMapZero X M := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    apply TrivSqZeroExt.ext
    · change (TrivSqZeroExt.map β (TrivSqZeroExt.inl x)).fst =
        (TrivSqZeroExt.inl x).fst
      simp
    · change (TrivSqZeroExt.map β (TrivSqZeroExt.inl x)).snd =
        (TrivSqZeroExt.inl x).snd
      simp
  have hF1 : firstOrderExtensionMapGraph X Ω d ≫ F =
      firstOrderExtensionMapGraph X M dM := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    change TrivSqZeroExt.map β (graphRingHom d x) = graphRingHom dM x
    apply TrivSqZeroExt.ext
    · calc
        (TrivSqZeroExt.map β (graphRingHom d x)).fst =
            (graphRingHom d x).fst := TrivSqZeroExt.fst_map _ _
        _ = x := rfl
        _ = (graphRingHom dM x).fst := rfl
    · calc
        (TrivSqZeroExt.map β (graphRingHom d x)).snd =
            β ((graphRingHom d x).snd) := TrivSqZeroExt.snd_map _ _
        _ = β (dividedPowerDifferential (A := S.A)
            X.ring.dividedPowers x) := rfl
        _ = diagonalDifference h x :=
          dividedPowerDifferentialsToDiagonalConormal_apply h x
        _ = (graphRingHom dM x).snd := rfl
  have hcomp0 : (BinaryCofan.mk s₀ s₁).inl ≫ (ψΩ ≫ F) =
      (BinaryCofan.mk s₀ s₁).inl ≫ ψM := by
    calc
      (BinaryCofan.mk s₀ s₁).inl ≫ (ψΩ ≫ F) =
          ((BinaryCofan.mk s₀ s₁).inl ≫ ψΩ) ≫ F := (Category.assoc _ _ _).symm
      _ = (firstOrderExtensionMapZero X Ω) ≫ F :=
        by rw [inl_comp_diagonalExtensionCoproductMap]
      _ = firstOrderExtensionMapZero X M := hF0
      _ = (BinaryCofan.mk s₀ s₁).inl ≫ ψM := (inl_comp_diagonalExtensionCoproductMap h M dM).symm
  have hcomp1 : (BinaryCofan.mk s₀ s₁).inr ≫ (ψΩ ≫ F) =
      (BinaryCofan.mk s₀ s₁).inr ≫ ψM := by
    calc
      (BinaryCofan.mk s₀ s₁).inr ≫ (ψΩ ≫ F) =
          ((BinaryCofan.mk s₀ s₁).inr ≫ ψΩ) ≫ F := (Category.assoc _ _ _).symm
      _ = (firstOrderExtensionMapGraph X Ω d) ≫ F :=
        by rw [inr_comp_diagonalExtensionCoproductMap]
      _ = firstOrderExtensionMapGraph X M dM := hF1
      _ = (BinaryCofan.mk s₀ s₁).inr ≫ ψM := (inr_comp_diagonalExtensionCoproductMap h M dM).symm
  calc
    ψΩ ≫ F = ψM := BinaryCofan.IsColimit.hom_ext h hcomp0 hcomp1
    _ = diagonalClassGraphMap h := by
      rw [diagonalClassGraphMap_eq_coproductMap h]

/-- The map back to differentials is a left inverse. -/
private theorem diagonalConormalMaps_leftInverse
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    (diagonalConormalToDividedPowerDifferentials h).comp
      (dividedPowerDifferentialsToDiagonalConormal h) = LinearMap.id := by
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  apply LinearMap.ext
  intro ω
  have hmem : ω ∈ Submodule.span X.ring
      (Set.range (dividedPowerDifferential (A := S.A) X.ring.dividedPowers)) := by
    rw [dividedPowerDifferentials_span X.ring.dividedPowers]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem ω hω =>
      rcases hω with ⟨b, rfl⟩
      change diagonalConormalToDividedPowerDifferentials h
          (dividedPowerDifferentialsToDiagonalConormal h
            (dividedPowerDifferential (A := S.A) X.ring.dividedPowers b)) = _
      rw [dividedPowerDifferentialsToDiagonalConormal_apply,
        diagonalConormalToDividedPowerDifferentials_difference]
      rfl
  | zero => simp
  | add ω η hω hη ihω ihη => rw [map_add, ihω, ihη]; simp
  | smul a ω hω ih => rw [map_smul, ih]; simp

private theorem diagonalClass_kernel
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (k : diagonalKernel h) :
    diagonalClass h k.1 = Submodule.Quotient.mk k := by
  change Submodule.Quotient.mk (diagonalClassRep h k.1) =
    Submodule.Quotient.mk k
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change k.1 - s₀.hom.toRingHom
    ((diagonalMap h).hom.toRingHom k.1) = k.1
  have hkq : (diagonalMap h).hom.toRingHom k.1 = 0 :=
    RingHom.mem_ker.mp k.2
  rw [hkq, map_zero, sub_zero]

/-- The map back to differentials is a right inverse. -/
private theorem diagonalConormalMaps_rightInverse
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    (dividedPowerDifferentialsToDiagonalConormal h).comp
      (diagonalConormalToDividedPowerDifferentials h) = LinearMap.id := by
  classical
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  let Ω := dividedPowerDifferentials (A := S.A) X.ring.dividedPowers
  let M := diagonalConormal h
  let : Algebra X.ring Y.ring := s₀.hom.toRingHom.toAlgebra
  let : Module Y.ring Ω := Module.compHom Ω (diagonalMap h).hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.ring)
  let c := diagonalKernelCoordinateMap h Ω d
  let β := dividedPowerDifferentialsToDiagonalConormal h
  let α := diagonalConormalToDividedPowerDifferentials h
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h Ω d
  have hcoord (k : diagonalKernel h) : β (c k) = diagonalClass h k.1 := by
    let z : TrivSqZeroExt X.ring Ω :=
      (diagonalExtensionCoproductMap h Ω d).hom.toRingHom k.1
    have hfac := diagonalClassGraphMap_factorization h
    have hval := congrArg (fun g : Y ⟶ firstOrderExtensionThickening X M =>
      g.hom.toRingHom k.1) hfac
    have hval' : TrivSqZeroExt.map β z =
        (diagonalClassGraphMap h).hom.toRingHom k.1 := by
      change TrivSqZeroExt.map β
        ((diagonalExtensionCoproductMap h Ω d).hom.toRingHom k.1) =
        (diagonalClassGraphMap h).hom.toRingHom k.1 at hval
      exact hval
    have hsnd := congrArg TrivSqZeroExt.snd hval'
    have hsnd' : β
        z.snd =
        diagonalClass h k.1 := by
      rw [TrivSqZeroExt.snd_map] at hsnd
      change β (c k) = diagonalClass h k.1 at hsnd
      exact hsnd
    change β (c k) = diagonalClass h k.1 at hsnd'
    exact hsnd'
  apply LinearMap.ext
  intro m
  apply (diagonalConormalLinearEquiv h).injective
  obtain ⟨k, hk⟩ := Submodule.mkQ_surjective (diagonalRelations h)
    (diagonalConormalLinearEquiv h m)
  change (diagonalConormalLinearEquiv h)
      (β (((diagonalRelations h).liftQ c hc)
        (diagonalConormalLinearEquiv h m))) =
    (diagonalConormalLinearEquiv h) m
  rw [← hk]
  change (diagonalConormalLinearEquiv h) (β (c k)) =
    Submodule.Quotient.mk k
  rw [hcoord k, diagonalClass_kernel h k]
  rfl

end DividedPowerThickening

end Crystalline

end

public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Crystalline

namespace DividedPowerThickening

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : DividedPowerThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

/-- The canonical identification `Ω_{B/A,δ} ≅ K / (K² + (K ∩ J(1))^{[2]})` of the divided power
differentials of an object `X = (B, J, δ)` of `CRIS(C/A)` with the diagonal conormal module of a
coproduct of `X` with itself in `CRIS(C/A)`.  It carries `d b` to the class of `s₁ b - s₀ b`, see
`dividedPowerDifferentialsEquivDiagonalConormal_apply`. -/
public noncomputable def dividedPowerDifferentialsEquivDiagonalConormal
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentials (A := S.A) X.ring.dividedPowers ≃ₗ[X.ring] diagonalConormal h :=
  letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  LinearEquiv.ofLinearMap (dividedPowerDifferentialsToDiagonalConormal h)
    (diagonalConormalToDividedPowerDifferentials h) (diagonalConormalMaps_rightInverse h)
    (diagonalConormalMaps_leftInverse h)

/-- The canonical identification sends `d b` to the class of `s₁ b - s₀ b`. -/
public theorem dividedPowerDifferentialsEquivDiagonalConormal_apply
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) (b : X.ring) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentialsEquivDiagonalConormal h
        (dividedPowerDifferential (A := S.A) X.ring.dividedPowers b) =
      diagonalDifference h b :=
  dividedPowerDifferentialsToDiagonalConormal_apply h b

/-- **Stacks Project, Tag 07HV.** In Situation 07MD, let `(B, J, δ)` be an object of `CRIS(C/A)`
and let `(B(1), J(1), δ(1))` be its coproduct with itself in `CRIS(C/A)`, with coprojections
`s₀, s₁`.  Denote `K = Ker(B(1) → B)`.  Then `K ∩ J(1) ⊂ J(1)` is preserved by the divided power
structure, and `Ω_{B/A,δ} = K / (K² + (K ∩ J(1))^{[2]})` canonically: there is exactly one
`B`-linear isomorphism carrying `d b` to the class of `s₁ b - s₀ b` for every `b ∈ B`. -/
@[stacks 07HV "both parts, for an object of CRIS(C/A) and its self-coproduct in CRIS(C/A)"]
public theorem isSubDPIdeal_and_existsUnique_dividedPowerDifferentialsEquiv
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    Y.ring.dividedPowers.IsSubDPIdeal (diagonalKernel h ⊓ Y.ring.ideal) ∧
      ∃! e : dividedPowerDifferentials (A := S.A) X.ring.dividedPowers ≃ₗ[X.ring]
          diagonalConormal h,
        ∀ b : X.ring,
          e (dividedPowerDifferential (A := S.A) X.ring.dividedPowers b) =
            diagonalDifference h b := by
  let : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  refine ⟨diagonalKernel_isSubDPIdeal h, dividedPowerDifferentialsEquivDiagonalConormal h,
    dividedPowerDifferentialsEquivDiagonalConormal_apply h, fun e he ↦ ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on_range
    (dividedPowerDifferentials_span (A := S.A) X.ring.dividedPowers) fun b ↦ ?_
  change e _ = dividedPowerDifferentialsEquivDiagonalConormal h _
  rw [he, dividedPowerDifferentialsEquivDiagonalConormal_apply]

end DividedPowerThickening

end Crystalline

end
