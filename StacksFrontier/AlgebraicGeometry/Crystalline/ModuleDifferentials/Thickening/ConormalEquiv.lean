module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.ExtensionCoproductMap

/-!
# Divided power differentials as the diagonal conormal module

The two mutually inverse linear maps between the diagonal conormal module and the module of
divided power differentials of `X`, and the resulting canonical identification
`Crystalline.dividedPowerDifferentialsEquivDiagonalConormal`, carrying `db` to the class of
`s₁ b - s₀ b`.

## Implementation notes

The map from differentials to the conormal module comes from the universal property of divided
power differentials applied to the derivation `b ↦ [s₁ b - s₀ b]`.  The map back comes from the
universal property of the coproduct against the first-order thickening of `X` by the module of
divided power differentials: a divided power derivation of `X` into a module is the same thing as
a map of thickenings from `X` to that first-order thickening, so the two coprojections of the
coproduct give two such maps whose difference is the required class.

## References

* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DividedPowerRing

universe u v w

namespace Crystalline

open DividedPowerThickening

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : CrystallineThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

/-- The module of divided power differentials is a module over the opposite ring. -/
private noncomputable instance dividedPowerDifferentialsModuleOpp [Algebra S.A X.1.ring] :
    Module X.1.ringᵐᵒᵖ (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) :=
  Module.compHom _ (RingEquiv.toOpposite X.1.ring).symm.toRingHom

private instance dividedPowerDifferentialsCentral [Algebra S.A X.1.ring] :
    IsCentralScalar X.1.ring (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) :=
  ⟨by intro a m; change MulOpposite.unop (MulOpposite.op a) • m = a • m; rfl⟩

/-- Restricting scalars along `s₀` and then the diagonal map is the identity on `X`. -/
private theorem isScalarTower_dividedPowerDifferentials
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    let _ : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    let _ : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
    let _ : Module Y.1.ring (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) :=
      Module.compHom _ (diagonalMap h).hom.hom.toRingHom
    IsScalarTower X.1.ring Y.1.ring
      (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) := by
  intro _ _ _
  refine IsScalarTower.of_algebraMap_smul (fun a m ↦ ?_)
  change (diagonalMap h).hom.hom.toRingHom (s₀.hom.hom.toRingHom a) • m = a • m
  rw [diagonalMap_s₀ h]

private noncomputable def diagonalConormalToDividedPowerDifferentials
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    diagonalConormal h →ₗ[X.1.ring]
      dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers := by
  classical
  letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  letI : Module X.1.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.hom.toRingHom
  letI : Module Y.1.ring
      (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) :=
    Module.compHom _ (diagonalMap h).hom.hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.1.ring)
  let c := diagonalKernelCoordinateMap h
    (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) d
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h _ d
  exact ((diagonalRelations h).liftQ c hc).restrictScalars X.1.ring |>.comp
    (diagonalConormalLinearEquiv h).toLinearMap

private noncomputable def diagonalDifferenceKaehlerDerivation
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    letI : Module S.A (diagonalConormal h) :=
      Module.compHom (diagonalConormal h) X.1.fromBase.toRingHom
    letI : IsScalarTower S.A X.1.ring (diagonalConormal h) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Derivation S.A X.1.ring (diagonalConormal h) :=
  letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  letI : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.1.fromBase.toRingHom
  letI : IsScalarTower S.A X.1.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let d := diagonalDifferenceDerivation h
  { toFun := d.1
    map_add' := d.1.map_add
    map_smul' := by
      intro a b
      change d.1 (X.1.fromBase.toRingHom a * b) =
        X.1.fromBase.toRingHom a • d.1 b
      rw [d.1.leibniz, d.map_ringHom]
      simp
    map_one_eq_zero' := d.1.map_one_eq_zero
    leibniz' := d.1.leibniz }

private noncomputable def dividedPowerDifferentialsToDiagonalConormal
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers →ₗ[X.1.ring]
      diagonalConormal h := by
  classical
  letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  letI : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.1.fromBase.toRingHom
  letI : IsScalarTower S.A X.1.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let d := diagonalDifferenceDerivation h
  let D := diagonalDifferenceKaehlerDerivation h
  let L : Ω[X.1.ring⁄S.A] →ₗ[X.1.ring]
      diagonalConormal h := D.liftKaehlerDifferential
  let R := dividedPowerDifferentialRelations (A := S.A) X.1.ring.dividedPowers
  have hR : R ≤ LinearMap.ker L := by
    change Submodule.span X.1.ring
      (Set.range fun z : X.1.ring.ideal × ℕ ↦
        dividedPowerDifferentialRelation X.1.ring.dividedPowers z.1 z.2) ≤
      LinearMap.ker L
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, n⟩, rfl⟩
    change L (KaehlerDifferential.D S.A X.1.ring
        (X.1.ring.dividedPowers.dpow (n + 1) x) -
      X.1.ring.dividedPowers.dpow n x • KaehlerDifferential.D S.A X.1.ring x) = 0
    dsimp only [L]
    rw [map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    change d.1 (X.1.ring.dividedPowers.dpow (n + 1) x) -
      X.1.ring.dividedPowers.dpow n x • d.1 x = 0
    have hx : x.1 ∈ X.1.ring.ideal := x.2
    exact sub_eq_zero.mpr (d.map_dpow (n + 1) (by omega) x.1 hx)
  exact R.liftQ L hR

private theorem diagonalConormalToDividedPowerDifferentials_difference
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (b : X.1.ring) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    diagonalConormalToDividedPowerDifferentials h (diagonalDifference h b) =
      dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers b := by
  classical
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let : Module X.1.ring ((diagonalKernel h) ⧸ diagonalRelations h) :=
    Module.compHom ((diagonalKernel h) ⧸ diagonalRelations h)
      s₀.hom.hom.toRingHom
  let : Module Y.1.ring
      (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) :=
    Module.compHom _ (diagonalMap h).hom.hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.1.ring)
  let c := diagonalKernelCoordinateMap h
    (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) d
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h _ d
  have h0 := diagonalExtensionCoproductMap_inl h
    (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) d b
  have h1 := diagonalExtensionCoproductMap_inr h
    (dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers) d b
  change ((diagonalRelations h).liftQ c hc)
      (diagonalConormalLinearEquiv h (diagonalDifference h b)) = _
  rw [diagonalConormalLinearEquiv_apply]
  change c ⟨s₁.hom.hom.toRingHom b - s₀.hom.hom.toRingHom b, _⟩ = _
  change ((diagonalExtensionCoproductMap h _ d).hom.hom.toRingHom
      (s₁.hom.hom.toRingHom b - s₀.hom.hom.toRingHom b)).snd = _
  rw [map_sub, h1, h0]
  change (graphRingHom d b).snd - (TrivSqZeroExt.inl b).snd = _
  simp [graphRingHom, graphFun, d, universalDividedPowerDerivation]
  rfl

private theorem dividedPowerDifferentialsToDiagonalConormal_apply
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (b : X.1.ring) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    dividedPowerDifferentialsToDiagonalConormal h
      (dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers b) =
        diagonalDifference h b := by
  classical
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let : Module S.A (diagonalConormal h) :=
    Module.compHom (diagonalConormal h) X.1.fromBase.toRingHom
  let : IsScalarTower S.A X.1.ring (diagonalConormal h) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  dsimp only [dividedPowerDifferentialsToDiagonalConormal]
  exact Derivation.liftKaehlerDifferential_comp_D (diagonalDifferenceKaehlerDerivation h) b

private noncomputable instance diagonalConormalModuleOpp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Module X.1.ringᵐᵒᵖ (diagonalConormal h) :=
  Module.compHom _ (RingEquiv.toOpposite X.1.ring).symm.toRingHom

private noncomputable instance diagonalConormalCentral
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
  IsCentralScalar X.1.ring (diagonalConormal h) :=
  ⟨by intro a m; change MulOpposite.unop (MulOpposite.op a) • m = a • m; rfl⟩

private theorem diagonalClass_zero
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClass h 0 = 0 := by
  have hr : diagonalClassRep h 0 = 0 := by
    apply Subtype.ext
    change 0 - s₀.hom.hom.toRingHom ((diagonalMap h).hom.hom.toRingHom 0) = 0
    rw [map_zero, map_zero]
    simp
  change Submodule.Quotient.mk (diagonalClassRep h 0) = 0
  rw [hr]
  simp

private theorem diagonalClass_one
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClass h 1 = 0 := by
  have hr : diagonalClassRep h 1 = 0 := by
    apply Subtype.ext
    change 1 - s₀.hom.hom.toRingHom ((diagonalMap h).hom.hom.toRingHom 1) = 0
    rw [map_one, map_one]
    simp
  change Submodule.Quotient.mk (diagonalClassRep h 1) = 0
  rw [hr]
  simp

private noncomputable def diagonalClassGraphRingHom
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
    Y.1.ring →+* TrivSqZeroExt X.1.ring (diagonalConormal h) := by
  classical
  letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let q : Y.1.ring →+* X.1.ring := (diagonalMap h).hom.hom.toRingHom
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
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
    DividedPowers.DPMorphism Y.1.ring.dividedPowers
      (Classical.choose (firstOrderExtension_dividedPowers X.1.ring
        (diagonalConormal h))) := by
  classical
  letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let δ := Classical.choose
    (firstOrderExtension_dividedPowers X.1.ring (diagonalConormal h))
  let φ := diagonalClassGraphRingHom h
  have hcoords := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.1.ring (diagonalConormal h))).1
  have hfst (y : Y.1.ring) : (φ y).fst = (diagonalMap h).hom.hom.toRingHom y := rfl
  refine DividedPowers.DPMorphism.mk' (f := φ) ?_
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change (diagonalMap h).hom.hom.toRingHom y ∈ X.1.ring.ideal
    exact (Ideal.map_le_iff_le_comap.mp (diagonalMap h).hom.hom.ideal_comp) hy
  · intro n y hy
    have hy' : φ y ∈ firstOrderExtensionIdeal X.1.ring (diagonalConormal h) :=
      (Ideal.map_le_iff_le_comap.mp (diagonalMap h).hom.hom.ideal_comp) hy
    by_cases hn0 : n = 0
    · subst n
      change δ.dpow 0 (φ y) = φ (Y.1.ring.dividedPowers.dpow 0 y)
      rw [δ.dpow_zero hy', Y.1.ring.dividedPowers.dpow_zero hy]
      apply TrivSqZeroExt.ext
      · change 1 = (diagonalClassGraphRingHom h 1).fst
        simp [diagonalClassGraphRingHom]
      · change 0 = diagonalClass h 1
        exact (diagonalClass_one h).symm
    · by_cases hn1 : n = 1
      · subst n
        change δ.dpow 1 (φ y) = φ (Y.1.ring.dividedPowers.dpow 1 y)
        rw [δ.dpow_one hy', Y.1.ring.dividedPowers.dpow_one hy]
      · have hn2 : 2 ≤ n := by omega
        have hc := hcoords n (φ y) hn2 hy'
        have hqdp : (diagonalMap h).hom.hom.toRingHom
            (Y.1.ring.dividedPowers.dpow n y) =
              X.1.ring.dividedPowers.dpow n
                ((diagonalMap h).hom.hom.toRingHom y) :=
          (diagonalMap h).hom.hom.isDPMorphism.dpow_comp y hy |>.symm
        have hclass := diagonalClass_dpow h n y hn2 hy
        apply TrivSqZeroExt.ext
        · calc
            (δ.dpow n (φ y)).fst =
                X.1.ring.dividedPowers.dpow n
                  ((diagonalMap h).hom.hom.toRingHom y) := hc.1
            _ = (diagonalMap h).hom.hom.toRingHom
                (Y.1.ring.dividedPowers.dpow n y) := hqdp.symm
            _ = (φ (Y.1.ring.dividedPowers.dpow n y)).fst := (hfst _).symm
        · calc
            (δ.dpow n (φ y)).snd =
                X.1.ring.dividedPowers.dpow (n - 1)
                  ((diagonalMap h).hom.hom.toRingHom y) • diagonalClass h y := hc.2
            _ = diagonalClass h (Y.1.ring.dividedPowers.dpow n y) := hclass.symm
            _ = (φ (Y.1.ring.dividedPowers.dpow n y)).snd := rfl

private theorem diagonalClassGraph_quotientMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
    Ideal.quotientMap (firstOrderExtensionIdeal X.1.ring (diagonalConormal h))
      (diagonalClassGraphDPMorphism h).toRingHom
      (Ideal.map_le_iff_le_comap.mp
        (diagonalClassGraphDPMorphism h).ideal_comp) =
      (firstOrderExtensionQuotientMap X.1.ring (diagonalConormal h)).comp
        (DividedPowerRing.quotientRingHom (diagonalMap h).hom.hom) := by
  classical
  let : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let φ := diagonalClassGraphDPMorphism h
  ext z
  -- `ext` has reduced the quotient variable to a representative in the ring.
  let y := z
  simp only [RingHom.comp_apply]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  change φ.toRingHom y - TrivSqZeroExt.inl ((diagonalMap h).hom.hom.toRingHom y) ∈
    firstOrderExtensionIdeal X.1.ring (diagonalConormal h)
  change (TrivSqZeroExt.fstHom X.1.ring X.1.ring (diagonalConormal h)).toRingHom
      (φ.toRingHom y - TrivSqZeroExt.inl ((diagonalMap h).hom.hom.toRingHom y)) ∈
    X.1.ring.ideal
  change (diagonalClassGraphRingHom h y).fst -
      (diagonalMap h).hom.hom.toRingHom y ∈ X.1.ring.ideal
  change (diagonalMap h).hom.hom.toRingHom y -
      (diagonalMap h).hom.hom.toRingHom y ∈ X.1.ring.ideal
  simpa only [sub_self] using X.1.ring.ideal.zero_mem

private noncomputable def diagonalClassGraphCrystallineMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Y ⟶ firstOrderExtensionCrystalline X (diagonalConormal h) := by
  classical
  letI : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let E := firstOrderExtensionThickening X (diagonalConormal h)
  letI : CommRing (firstOrderExtension X.1.ring (diagonalConormal h)) := E.ring.commRing
  let φ := diagonalClassGraphDPMorphism h
  refine ObjectProperty.homMk ?_
  refine { hom := φ, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    apply TrivSqZeroExt.ext
    · have hb := congrArg (fun f : DividedPowers.DPMorphism
          S.A.dividedPowers X.1.ring.dividedPowers => f.toRingHom a)
        (diagonalMap h).hom.fromBase_comp
      change (diagonalMap h).hom.hom.toRingHom
        (Y.1.fromBase.toRingHom a) = X.1.fromBase.toRingHom a at hb
      exact hb
    · have hs := congrArg (fun f : DividedPowers.DPMorphism
          S.A.dividedPowers Y.1.ring.dividedPowers => f.toRingHom a)
        s₀.hom.fromBase_comp
      change s₀.hom.hom.toRingHom (X.1.fromBase.toRingHom a) =
        Y.1.fromBase.toRingHom a at hs
      have hz := diagonalClass_s₀ h (X.1.fromBase.toRingHom a)
      change diagonalClass h (Y.1.fromBase.toRingHom a) = 0
      rw [← hs]
      exact hz
  · change (Ideal.quotientMap (firstOrderExtensionIdeal X.1.ring (diagonalConormal h)) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)).comp Y.1.toQuotient =
      E.toQuotient
    rw [diagonalClassGraph_quotientMap h]
    change ((firstOrderExtensionQuotientMap X.1.ring (diagonalConormal h)).comp
      (DividedPowerRing.quotientRingHom (diagonalMap h).hom.hom)).comp
        Y.1.toQuotient = E.toQuotient
    rw [RingHom.comp_assoc, (diagonalMap h).hom.toQuotient_comp]

/-- The first coprojection followed by the coproduct map is the zero map into the extension. -/
private theorem inl_comp_diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring X.1.fromBase.toRingHom M) :
    (BinaryCofan.mk s₀ s₁).inl ≫ diagonalExtensionCoproductMap h M d =
      firstOrderExtensionMapZeroCrystalline X M := by
  simpa [diagonalExtensionCoproductMap] using BinaryCofan.IsColimit.inl_desc h
    (firstOrderExtensionMapZeroCrystalline X M) (firstOrderExtensionMapGraphCrystalline X M d)

/-- The second coprojection followed by the coproduct map is the graph map into the extension. -/
private theorem inr_comp_diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring X.1.fromBase.toRingHom M) :
    (BinaryCofan.mk s₀ s₁).inr ≫ diagonalExtensionCoproductMap h M d =
      firstOrderExtensionMapGraphCrystalline X M d := by
  simpa [diagonalExtensionCoproductMap] using BinaryCofan.IsColimit.inr_desc h
    (firstOrderExtensionMapZeroCrystalline X M) (firstOrderExtensionMapGraphCrystalline X M d)

private theorem diagonalClassGraphCrystallineMap_eq_coproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    diagonalClassGraphCrystallineMap h =
      diagonalExtensionCoproductMap h (diagonalConormal h)
        (diagonalDifferenceDerivation h) := by
  let M := diagonalConormal h
  let d := diagonalDifferenceDerivation h
  let f₀ := firstOrderExtensionMapZeroCrystalline X M
  let f₁ := firstOrderExtensionMapGraphCrystalline X M d
  have h0 : (BinaryCofan.mk s₀ s₁).inl ≫ diagonalClassGraphCrystallineMap h = f₀ := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    apply TrivSqZeroExt.ext
    · exact diagonalMap_s₀ h x
    · change diagonalClass h (s₀.hom.hom.toRingHom x) = 0
      exact diagonalClass_s₀ h x
  have h1 : (BinaryCofan.mk s₀ s₁).inr ≫ diagonalClassGraphCrystallineMap h = f₁ := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    apply TrivSqZeroExt.ext
    · exact diagonalMap_s₁ h x
    · change diagonalClass h (s₁.hom.hom.toRingHom x) = diagonalDifference h x
      exact diagonalClass_s₁ h x
  exact BinaryCofan.IsColimit.hom_ext h
    (h0.trans (inl_comp_diagonalExtensionCoproductMap h M d).symm)
    (h1.trans (inr_comp_diagonalExtensionCoproductMap h M d).symm)

private theorem diagonalClassGraphCrystallineMap_factorization
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    let Ω := dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers
    let M := diagonalConormal h
    let d := universalDividedPowerDerivation (A := S.A) (B := X.1.ring)
    (diagonalExtensionCoproductMap h Ω d ≫
      ObjectProperty.homMk (by
        dsimp [firstOrderExtensionCrystalline]
        exact firstOrderExtensionLinearMap X Ω M
          (dividedPowerDifferentialsToDiagonalConormal h))) =
      diagonalClassGraphCrystallineMap h := by
  classical
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let Ω := dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers
  let M := diagonalConormal h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.1.ring)
  let dM := diagonalDifferenceDerivation h
  let β := dividedPowerDifferentialsToDiagonalConormal h
  let ψΩ := diagonalExtensionCoproductMap h Ω d
  let ψM := diagonalExtensionCoproductMap h M dM
  let F : firstOrderExtensionCrystalline X Ω ⟶ firstOrderExtensionCrystalline X M :=
    ObjectProperty.homMk (firstOrderExtensionLinearMap X Ω M β)
  have hF0 : firstOrderExtensionMapZeroCrystalline X Ω ≫ F =
      firstOrderExtensionMapZeroCrystalline X M := by
    apply ObjectProperty.hom_ext
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
  have hF1 : firstOrderExtensionMapGraphCrystalline X Ω d ≫ F =
      firstOrderExtensionMapGraphCrystalline X M dM := by
    apply ObjectProperty.hom_ext
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
            X.1.ring.dividedPowers x) := rfl
        _ = diagonalDifference h x :=
          dividedPowerDifferentialsToDiagonalConormal_apply h x
        _ = (graphRingHom dM x).snd := rfl
  have hcomp0 : (BinaryCofan.mk s₀ s₁).inl ≫ (ψΩ ≫ F) =
      (BinaryCofan.mk s₀ s₁).inl ≫ ψM := by
    calc
      (BinaryCofan.mk s₀ s₁).inl ≫ (ψΩ ≫ F) =
          ((BinaryCofan.mk s₀ s₁).inl ≫ ψΩ) ≫ F := (Category.assoc _ _ _).symm
      _ = (firstOrderExtensionMapZeroCrystalline X Ω) ≫ F :=
        by rw [inl_comp_diagonalExtensionCoproductMap]
      _ = firstOrderExtensionMapZeroCrystalline X M := hF0
      _ = (BinaryCofan.mk s₀ s₁).inl ≫ ψM := (inl_comp_diagonalExtensionCoproductMap h M dM).symm
  have hcomp1 : (BinaryCofan.mk s₀ s₁).inr ≫ (ψΩ ≫ F) =
      (BinaryCofan.mk s₀ s₁).inr ≫ ψM := by
    calc
      (BinaryCofan.mk s₀ s₁).inr ≫ (ψΩ ≫ F) =
          ((BinaryCofan.mk s₀ s₁).inr ≫ ψΩ) ≫ F := (Category.assoc _ _ _).symm
      _ = (firstOrderExtensionMapGraphCrystalline X Ω d) ≫ F :=
        by rw [inr_comp_diagonalExtensionCoproductMap]
      _ = firstOrderExtensionMapGraphCrystalline X M dM := hF1
      _ = (BinaryCofan.mk s₀ s₁).inr ≫ ψM := (inr_comp_diagonalExtensionCoproductMap h M dM).symm
  calc
    ψΩ ≫ F = ψM := BinaryCofan.IsColimit.hom_ext h hcomp0 hcomp1
    _ = diagonalClassGraphCrystallineMap h := by
      rw [diagonalClassGraphCrystallineMap_eq_coproductMap h]

private theorem diagonalConormalMaps_leftInverse
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    (diagonalConormalToDividedPowerDifferentials h).comp
      (dividedPowerDifferentialsToDiagonalConormal h) = LinearMap.id := by
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  apply LinearMap.ext
  intro ω
  have hmem : ω ∈ Submodule.span X.1.ring
      (Set.range (dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers)) := by
    rw [dividedPowerDifferentials_span X.1.ring.dividedPowers]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem ω hω =>
      rcases hω with ⟨b, rfl⟩
      change diagonalConormalToDividedPowerDifferentials h
          (dividedPowerDifferentialsToDiagonalConormal h
            (dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers b)) = _
      rw [dividedPowerDifferentialsToDiagonalConormal_apply,
        diagonalConormalToDividedPowerDifferentials_difference]
      rfl
  | zero => simp
  | add ω η hω hη ihω ihη => rw [map_add, ihω, ihη]; simp
  | smul a ω hω ih => rw [map_smul, ih]; simp

private theorem diagonalClass_kernel
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (k : diagonalKernel h) :
    diagonalClass h k.1 = Submodule.Quotient.mk k := by
  change Submodule.Quotient.mk (diagonalClassRep h k.1) =
    Submodule.Quotient.mk k
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change k.1 - s₀.hom.hom.toRingHom
    ((diagonalMap h).hom.hom.toRingHom k.1) = k.1
  have hkq : (diagonalMap h).hom.hom.toRingHom k.1 = 0 :=
    RingHom.mem_ker.mp k.2
  rw [hkq, map_zero, sub_zero]

private theorem diagonalConormalMaps_rightInverse
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    (dividedPowerDifferentialsToDiagonalConormal h).comp
      (diagonalConormalToDividedPowerDifferentials h) = LinearMap.id := by
  classical
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let Ω := dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers
  let M := diagonalConormal h
  let : Algebra X.1.ring Y.1.ring := s₀.hom.hom.toRingHom.toAlgebra
  let : Module Y.1.ring Ω := Module.compHom Ω (diagonalMap h).hom.hom.toRingHom
  have := isScalarTower_dividedPowerDifferentials h
  let d := universalDividedPowerDerivation (A := S.A) (B := X.1.ring)
  let c := diagonalKernelCoordinateMap h Ω d
  let β := dividedPowerDifferentialsToDiagonalConormal h
  let α := diagonalConormalToDividedPowerDifferentials h
  have hc : diagonalRelations h ≤ LinearMap.ker c :=
    diagonalKernelCoordinateMap_killsRelations h Ω d
  have hcoord (k : diagonalKernel h) : β (c k) = diagonalClass h k.1 := by
    let z : TrivSqZeroExt X.1.ring Ω :=
      (diagonalExtensionCoproductMap h Ω d).hom.hom.toRingHom k.1
    have hfac := diagonalClassGraphCrystallineMap_factorization h
    have hval := congrArg (fun g : Y ⟶ firstOrderExtensionCrystalline X M =>
      g.hom.hom.toRingHom k.1) hfac
    have hval' : TrivSqZeroExt.map β z =
        (diagonalClassGraphCrystallineMap h).hom.hom.toRingHom k.1 := by
      change TrivSqZeroExt.map β
        ((diagonalExtensionCoproductMap h Ω d).hom.hom.toRingHom k.1) =
        (diagonalClassGraphCrystallineMap h).hom.hom.toRingHom k.1 at hval
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

/-- The canonical identification of divided power differentials with the diagonal
conormal module on the affine crystalline site, carrying `db` to the difference of the
two coprojections. -/
public theorem exists_dividedPowerDifferentialsEquivDiagonalConormal
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    Nonempty (letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
      {e : dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers ≃ₗ[X.1.ring]
          diagonalConormal h //
        ∀ b : X.1.ring,
          e (dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers b) =
            diagonalDifference h b}) := by
  let : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let α := diagonalConormalToDividedPowerDifferentials h
  let β := dividedPowerDifferentialsToDiagonalConormal h
  let hαβ := diagonalConormalMaps_leftInverse h
  let hβα := diagonalConormalMaps_rightInverse h
  let e : dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers ≃ₗ[X.1.ring]
      diagonalConormal h := LinearEquiv.ofLinearMap β α hβα hαβ
  refine ⟨⟨e, ?_⟩⟩
  intro b
  change β (dividedPowerDifferential (A := S.A)
    X.1.ring.dividedPowers b) = diagonalDifference h b
  exact dividedPowerDifferentialsToDiagonalConormal_apply h b

/-- A chosen identification of the divided power differentials of `X` with the diagonal
conormal module, carrying `db` to `diagonalDifference h b`. -/
@[stacks 07HV "canonical identification"]
public noncomputable def dividedPowerDifferentialsEquivDiagonalConormal
    (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    {e : dividedPowerDifferentials (A := S.A) X.1.ring.dividedPowers ≃ₗ[X.1.ring]
        diagonalConormal h //
      ∀ b : X.1.ring,
        e (dividedPowerDifferential (A := S.A) X.1.ring.dividedPowers b) =
          diagonalDifference h b} :=
  Classical.choice (exists_dividedPowerDifferentialsEquivDiagonalConormal h)

end Crystalline

end
