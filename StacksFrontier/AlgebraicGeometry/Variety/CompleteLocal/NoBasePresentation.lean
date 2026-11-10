module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk

/-!
# A completed local ring without a ground-field-compatible presentation

There is a locally Noetherian scheme over a field whose completed local ring cannot be
presented, as an algebra over that field, by a quotient of a formal power series ring over
the residue field.

## Main results

* `AlgebraicGeometry.exists_no_quotient_mvPowerSeries_algEquiv_completedLocalRing` gives such
  a scheme and point.

## Implementation notes

The residue field carries its canonical algebra structure from the structure morphism of the
scheme. The completion carries the canonical algebra structure through the stalk. Thus an
algebra equivalence in the conclusion is precisely a ground-field-compatible presentation.

The counterexample is the ring of dual numbers over the rational function field in one
variable over `ZMod 3`, made an algebra over that field by sending the variable to
`X ^ 3 + ε`.  Its residue field contains a cube root of the image of the variable, while the
ring itself contains none, so no presentation over the residue field can be compatible with
the ground field.

## References

* [Stacks Project, Tag 0C52](https://stacks.math.columbia.edu/tag/0C52)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped DualNumber
open DualNumber TrivSqZeroExt

universe u

namespace AlgebraicGeometry

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The rational function field in one variable over `ZMod 3`, the ground field of the
counterexample. -/
private abbrev counterexampleField := RatFunc (ZMod 3)

/-- In characteristic three, cubing a dual number kills its nilpotent part. -/
private theorem dualNumber_cube {K : Type} [Field K] [CharP K 3] (z : DualNumber K) :
    z ^ 3 = inl (z.fst ^ 3) := by
  ext
  · simp [pow_succ]
  · simp [pow_succ]
    ring_nf
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    linear_combination (fst z ^ 2 * snd z) * h3

/-- The maximal ideal of a ring of dual numbers has square zero. -/
private theorem dualNumber_maximalIdeal_sq (K : Type) [Field K] :
    (IsLocalRing.maximalIdeal (DualNumber K)) ^ 2 = ⊥ := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow]
  simp

/-- A ring of dual numbers is complete for its maximal-adic topology, its maximal ideal
having square zero. -/
private theorem dualNumber_isAdicComplete (K : Type) [Field K] :
    IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber K)) (DualNumber K) := by
  let I := IsLocalRing.maximalIdeal (DualNumber K)
  have hI : I ^ 2 = ⊥ := dualNumber_maximalIdeal_sq K
  have : IsHausdorff I (DualNumber K) := ⟨fun x hx => by simpa [hI] using hx 2⟩
  have : IsPrecomplete I (DualNumber K) := ⟨by
    intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_total n 2 with hn | hn
    · exact hf hn
    · have heq : f 2 = f n := by simpa [hI] using hf hn
      rw [heq]
      exact SModEq.rfl⟩
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }

/-- The image of the variable under the ground-field map of the counterexample: the cube of
the variable, deformed by the nilpotent. -/
private noncomputable def deformedParameter : DualNumber counterexampleField :=
  inl (RatFunc.X ^ 3) + (ε : DualNumber counterexampleField)

/-- Evaluation of polynomials over `ZMod 3` at the deformed parameter. -/
private noncomputable def polynomialToDualNumber :
    Polynomial (ZMod 3) →+* DualNumber counterexampleField :=
  (Polynomial.aeval deformedParameter).toRingHom

/-- A nonzero polynomial evaluates to a unit at the deformed parameter, because the cube of
the variable is transcendental. -/
private theorem polynomialToDualNumber_isUnit (q : Polynomial (ZMod 3)) (hq : q ≠ 0) :
    IsUnit (polynomialToDualNumber q) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  apply isUnit_iff_ne_zero.mpr
  have htrans : Transcendental (ZMod 3) (RatFunc.X ^ 3) :=
    RatFunc.transcendental_X.pow (by norm_num)
  have hinj : Function.Injective
      (Polynomial.aeval (RatFunc.X ^ 3) : Polynomial (ZMod 3) → RatFunc (ZMod 3)) :=
    transcendental_iff_injective.mp htrans
  have hmap : ((TrivSqZeroExt.fstHom (ZMod 3) counterexampleField counterexampleField).toRingHom
      |>.comp polynomialToDualNumber) =
      (Polynomial.aeval (RatFunc.X ^ 3)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [polynomialToDualNumber]
    · simp [polynomialToDualNumber, deformedParameter]
  have hfst := congrArg (fun f : Polynomial (ZMod 3) →+* counterexampleField => f q) hmap
  rw [RingHom.comp_apply] at hfst
  change (polynomialToDualNumber q).fst = _ at hfst
  rw [hfst]
  intro hq'
  apply hq
  apply hinj
  simpa using hq'

/-- The ground-field map of the counterexample, sending the variable to the deformed
parameter. -/
private noncomputable def groundFieldMap :
    counterexampleField →+* DualNumber counterexampleField :=
  (IsLocalization.lift (M := nonZeroDivisors (Polynomial (ZMod 3)))
    (g := polynomialToDualNumber) (by
      intro q
      apply polynomialToDualNumber_isUnit
      simp [nonZeroDivisors])).comp
    (RatFunc.toFractionRingAlgEquiv (ZMod 3) (Polynomial (ZMod 3))).toRingEquiv.toRingHom

/-- The variable of the rational function field, viewed in the fraction field of the
polynomial ring. -/
private theorem ratFunc_X_toFractionRing :
    (RatFunc.toFractionRingAlgEquiv (ZMod 3) (Polynomial (ZMod 3))).toRingEquiv
      (RatFunc.X : counterexampleField) =
        algebraMap (Polynomial (ZMod 3))
          (FractionRing (Polynomial (ZMod 3))) Polynomial.X := by
  rw [← RatFunc.algebraMap_X]
  exact (RatFunc.toFractionRingAlgEquiv (ZMod 3) (Polynomial (ZMod 3))).commutes _

/-- The ground-field map sends the variable to the deformed parameter. -/
private theorem groundFieldMap_parameter :
    groundFieldMap (RatFunc.X : counterexampleField) = deformedParameter := by
  change (IsLocalization.lift (M := nonZeroDivisors (Polynomial (ZMod 3)))
      (g := polynomialToDualNumber) (by
        intro q
        apply polynomialToDualNumber_isUnit
        simp [nonZeroDivisors]))
      ((RatFunc.toFractionRingAlgEquiv (ZMod 3) (Polynomial (ZMod 3))).toRingEquiv
        (RatFunc.X : counterexampleField)) = deformedParameter
  rw [ratFunc_X_toFractionRing]
  simp [deformedParameter, polynomialToDualNumber]

/-- The deformed parameter has no cube root in the ring of dual numbers. -/
private theorem no_cube_in_dualNumber :
    ∀ z : DualNumber counterexampleField,
      z ^ 3 ≠ groundFieldMap (RatFunc.X : counterexampleField) := by
  intro z hz
  have hs : (z ^ 3).snd = 0 := by rw [dualNumber_cube]; rfl
  rw [groundFieldMap_parameter] at hz
  have h := congrArg TrivSqZeroExt.snd hz
  simp [hs, deformedParameter] at h

/-- The ground field of the counterexample, lifted to an arbitrary universe. -/
private abbrev liftedBaseField := ULift.{u, 0} counterexampleField

/-- The counterexample ring, lifted to an arbitrary universe. -/
private abbrev liftedExampleRing := ULift.{u, 0} (DualNumber counterexampleField)

/-- The universe lift of the ground field is a ring equivalence. -/
private noncomputable def liftedBaseFieldEquiv : liftedBaseField ≃+* counterexampleField :=
  ULift.ringEquiv.{0, u}

private noncomputable instance : Field liftedBaseField :=
  let h : IsField counterexampleField := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    exact ⟨a⁻¹, mul_inv_cancel₀ ha⟩
  (liftedBaseFieldEquiv.toMulEquiv).isField h |>.toField

/-- The universe lift of the counterexample ring is a ring equivalence. -/
private noncomputable def liftedExampleRingEquiv :
    liftedExampleRing ≃+* DualNumber counterexampleField := ULift.ringEquiv.{0, u}

private instance : IsLocalRing liftedExampleRing :=
  liftedExampleRingEquiv.symm.isLocalRing

private instance : IsNoetherianRing liftedExampleRing :=
  isNoetherianRing_of_ringEquiv (DualNumber counterexampleField)
    liftedExampleRingEquiv.symm

/-- The ground-field map of the counterexample, transported to the lifted universe. -/
private noncomputable def liftedGroundFieldMap :
    ULift.{u, 0} counterexampleField →+* ULift.{u, 0} (DualNumber counterexampleField) :=
  liftedExampleRingEquiv.symm.toRingHom.comp
    (groundFieldMap.comp liftedBaseFieldEquiv.toRingHom)

private noncomputable instance : Algebra liftedBaseField liftedExampleRing :=
  liftedGroundFieldMap.toAlgebra

/-- The lifted ground-field map sends the variable to the lifted deformed parameter. -/
private theorem liftedGroundFieldMap_parameter :
    liftedGroundFieldMap (ULift.up.{u, 0} (RatFunc.X : counterexampleField)) =
      ULift.up.{u, 0} deformedParameter := by
  change ULift.up (groundFieldMap (RatFunc.X : counterexampleField)) = _
  exact congrArg ULift.up groundFieldMap_parameter

/-- The image of the variable has no cube root in the lifted counterexample ring. -/
private theorem no_cube_in_liftedRing :
    ∀ z : liftedExampleRing,
      z ^ 3 ≠ liftedGroundFieldMap (ULift.up.{u, 0} (RatFunc.X : counterexampleField)) := by
  intro z hz
  apply no_cube_in_dualNumber (liftedExampleRingEquiv z)
  have h := congrArg liftedExampleRingEquiv hz
  rw [liftedGroundFieldMap_parameter] at h
  change liftedExampleRingEquiv (z ^ 3) = deformedParameter at h
  simpa only [map_pow, groundFieldMap_parameter] using h

/-- Completeness for the maximal-adic topology transfers along a ring equivalence of local
rings. -/
private theorem isAdicComplete_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    (h : IsAdicComplete (IsLocalRing.maximalIdeal S) S) :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  have hcomplete : IsAdicComplete ((IsLocalRing.maximalIdeal R).map e) S := by
    simpa [IsLocalRing.map_ringEquiv_maximalIdeal e] using h
  exact (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal R) e).1 hcomplete

/-- The lifted counterexample ring is complete for its maximal-adic topology. -/
private theorem liftedExampleRing_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal liftedExampleRing) liftedExampleRing :=
  isAdicComplete_maximalIdeal_of_ringEquiv liftedExampleRingEquiv
    (dualNumber_isAdicComplete counterexampleField)

/-- The closed point of the spectrum of the lifted counterexample ring. -/
private noncomputable def counterexamplePointSpec : Spec (.of liftedExampleRing) :=
  IsLocalRing.closedPoint liftedExampleRing

private instance : counterexamplePointSpec.asIdeal.IsPrime := counterexamplePointSpec.isPrime

private instance : IsLocalization counterexamplePointSpec.asIdeal.primeCompl liftedExampleRing :=
  IsLocalization.self (by
    intro s hs
    change s ∉ IsLocalRing.maximalIdeal liftedExampleRing at hs
    exact IsLocalRing.notMem_maximalIdeal.mp hs)

/-- The stalk at the closed point is the ring itself, the ring being local. -/
private noncomputable def closedPointStalkEquiv :
    (Spec (.of liftedExampleRing)).presheaf.stalk
      counterexamplePointSpec ≃+* liftedExampleRing := by
  let m : Ideal liftedExampleRing := counterexamplePointSpec.asIdeal
  let e : Localization.AtPrime m ≃ₐ[liftedExampleRing] liftedExampleRing :=
    IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) liftedExampleRing
  let eStalk := (Spec.stalkIso (.of liftedExampleRing)
    counterexamplePointSpec).commRingCatIsoToRingEquiv
  exact eStalk.trans e.toRingEquiv

/-- Under the identification of the stalk with the ring, the structure morphism sends the
variable to the image of the lifted ground-field map. -/
private theorem stalk_groundFieldMap_parameter :
    let X := Spec (.of liftedExampleRing)
    let f := Spec.map (CommRingCat.ofHom liftedGroundFieldMap)
    let x : X := counterexamplePointSpec
    letI : Algebra liftedBaseField (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    closedPointStalkEquiv
      (algebraMap liftedBaseField (X.presheaf.stalk x)
        (ULift.up (RatFunc.X : counterexampleField))) =
      liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField)) := by
  dsimp only
  have hfront :
      (Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫
        (Spec.map (CommRingCat.ofHom liftedGroundFieldMap)).appTop =
      CommRingCat.ofHom liftedGroundFieldMap ≫
        (Scheme.ΓSpecIso (.of liftedExampleRing)).inv :=
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom liftedGroundFieldMap)).symm
  have hcat :
      (Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫
          (Spec.map (CommRingCat.ofHom liftedGroundFieldMap)).appTop ≫
            (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp) =
        CommRingCat.ofHom liftedGroundFieldMap ≫
          (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
            (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp) := by
    simpa only [Category.assoc] using congrArg
      (fun g => g ≫ (Spec (.of liftedExampleRing)).presheaf.germ ⊤
        counterexamplePointSpec (by simp)) hfront
  have hval := congrArg (fun g : CommRingCat.of liftedBaseField ⟶
      CommRingCat.of ((Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec) =>
    g.hom (ULift.up (RatFunc.X : counterexampleField))) hcat
  have hlocal :
      CommRingCat.ofHom (algebraMap liftedExampleRing
        (Localization.AtPrime counterexamplePointSpec.asIdeal)) =
        (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
          (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp) ≫
            (Spec.stalkIso (.of liftedExampleRing) counterexamplePointSpec).hom := by
    simpa [Category.assoc] using
      (Spec.algebraMap_stalkIso_inv_assoc (x := counterexamplePointSpec)
        (h := (Spec.stalkIso (.of liftedExampleRing) counterexamplePointSpec).hom))
  have hcomp :
      (Spec.stalkIso (.of liftedExampleRing) counterexamplePointSpec).commRingCatIsoToRingEquiv
        ((CommRingCat.Hom.hom
          (CommRingCat.ofHom liftedGroundFieldMap ≫
            (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
              (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
          (ULift.up (RatFunc.X : counterexampleField))) =
      algebraMap liftedExampleRing (Localization.AtPrime counterexamplePointSpec.asIdeal)
        (liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField))) := by
    change (CommRingCat.Hom.hom
        (CommRingCat.ofHom liftedGroundFieldMap ≫
          (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
            (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp) ≫
              (Spec.stalkIso (.of liftedExampleRing) counterexamplePointSpec).hom))
        (ULift.up (RatFunc.X : counterexampleField)) = _
    rw [← hlocal]
    simp
  change closedPointStalkEquiv
      ((CommRingCat.Hom.hom
        ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫
          (Spec.map (CommRingCat.ofHom liftedGroundFieldMap)).appTop ≫
            (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
        (ULift.up (RatFunc.X : counterexampleField))) = _
  calc
    _ = closedPointStalkEquiv
        ((CommRingCat.Hom.hom
          (CommRingCat.ofHom liftedGroundFieldMap ≫
            (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
              (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
          (ULift.up (RatFunc.X : counterexampleField))) := congrArg closedPointStalkEquiv hval
    _ = _ := by
      change (IsLocalization.algEquiv counterexamplePointSpec.asIdeal.primeCompl
          (Localization.AtPrime counterexamplePointSpec.asIdeal) liftedExampleRing).toRingEquiv
        ((Spec.stalkIso (.of liftedExampleRing) counterexamplePointSpec).commRingCatIsoToRingEquiv
          ((CommRingCat.Hom.hom
            (CommRingCat.ofHom liftedGroundFieldMap ≫
              (Scheme.ΓSpecIso (.of liftedExampleRing)).inv ≫
                (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
            (ULift.up (RatFunc.X : counterexampleField)))) = _
      rw [hcomp]
      exact (IsLocalization.algEquiv counterexamplePointSpec.asIdeal.primeCompl
        (Localization.AtPrime counterexamplePointSpec.asIdeal) liftedExampleRing).commutes _

/-- The stalk at the closed point is complete for its maximal-adic topology. -/
private theorem closedPointStalk_isAdicComplete :
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        ((Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec))
      ((Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec) :=
  isAdicComplete_maximalIdeal_of_ringEquiv closedPointStalkEquiv liftedExampleRing_isAdicComplete

/-- The completed local ring at the closed point is the counterexample ring itself, the ring
being already complete. -/
private noncomputable def completedStalkToRing :
    Scheme.completedLocalRing (Spec (.of liftedExampleRing)) counterexamplePointSpec ≃+*
      liftedExampleRing := by
  let S := (Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec
  let I := IsLocalRing.maximalIdeal S
  have : IsAdicComplete I S := closedPointStalk_isAdicComplete
  exact ((AdicCompletion.ofAlgEquiv I).symm.toRingEquiv).trans closedPointStalkEquiv

/-- Under the identification of the completed local ring with the ring, the ground field acts
through the lifted ground-field map. -/
private theorem completedGroundFieldMap_parameter :
    let X := Spec (.of liftedExampleRing)
    let f : X ⟶ Spec (.of liftedBaseField) :=
      Spec.map (CommRingCat.ofHom liftedGroundFieldMap)
    let x : X := counterexamplePointSpec
    letI : Algebra liftedBaseField (Scheme.completedLocalRing X x) :=
      Scheme.completedLocalRingAlgebra (k := liftedBaseField) f x
    completedStalkToRing
      (algebraMap liftedBaseField (Scheme.completedLocalRing X x)
        (ULift.up (RatFunc.X : counterexampleField))) =
      liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField)) := by
  dsimp only
  let S := (Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec
  let I := IsLocalRing.maximalIdeal S
  have : IsAdicComplete I S := closedPointStalk_isAdicComplete
  let a : S := (CommRingCat.Hom.hom
    ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫
      (Spec.map (CommRingCat.ofHom liftedGroundFieldMap)).appTop ≫
      (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
    (ULift.up (RatFunc.X : counterexampleField))
  change closedPointStalkEquiv
      ((AdicCompletion.ofAlgEquiv I).symm (algebraMap S (AdicCompletion I S) a)) = _
  rw [(AdicCompletion.ofAlgEquiv I).symm.commutes]
  exact stalk_groundFieldMap_parameter

/-- The residue field of the scheme at the closed point is the residue field of the
counterexample ring. -/
private noncomputable def stalkResidueEquiv :
    (Spec (.of liftedExampleRing)).residueField counterexamplePointSpec ≃+*
      IsLocalRing.ResidueField liftedExampleRing :=
  IsLocalRing.ResidueField.mapEquiv closedPointStalkEquiv

/-- In the residue field, the image of the variable does have a cube root: the residue of the
variable itself. -/
private theorem residueRoot_cube_in_ring :
    (IsLocalRing.residue liftedExampleRing
      (ULift.up (inl (RatFunc.X : counterexampleField)))) ^ 3 =
      IsLocalRing.residue liftedExampleRing
        (liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField))) := by
  apply (IsLocalRing.ResidueField.mapEquiv liftedExampleRingEquiv).injective
  simp only [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [liftedGroundFieldMap_parameter]
  simp only [liftedExampleRingEquiv]
  change (IsLocalRing.residue (DualNumber counterexampleField)
      (inl (RatFunc.X : counterexampleField))) ^ 3 =
    IsLocalRing.residue (DualNumber counterexampleField) deformedParameter
  rw [← map_pow (IsLocalRing.residue (DualNumber counterexampleField))
    (inl (RatFunc.X : counterexampleField)), dualNumber_cube]
  simp [deformedParameter, IsLocalRing.residue_eq_zero_iff,
    DualNumber.maximalIdeal_eq_span_singleton_eps]

/-- Under the identification of the residue field, the ground field acts through the residue
of the lifted ground-field map. -/
private theorem residueBaseMap_parameter :
    let X := Spec (.of liftedExampleRing)
    let f : X ⟶ Spec (.of liftedBaseField) :=
      Spec.map (CommRingCat.ofHom liftedGroundFieldMap)
    let x : X := counterexamplePointSpec
    letI : Algebra liftedBaseField (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫ f.appTop ≫
        X.Γevaluation x).hom.toAlgebra
    stalkResidueEquiv
      (algebraMap liftedBaseField (X.residueField x)
        (ULift.up (RatFunc.X : counterexampleField))) =
    IsLocalRing.residue liftedExampleRing
        (liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField))) := by
  dsimp only [stalkResidueEquiv, Scheme.residueField]
  have : IsLocalHom closedPointStalkEquiv.toRingHom :=
    ⟨fun a ha => by simpa using ha.map closedPointStalkEquiv.symm.toRingHom⟩
  change IsLocalRing.ResidueField.map closedPointStalkEquiv.toRingHom
      (IsLocalRing.residue
        ((Spec (.of liftedExampleRing)).presheaf.stalk counterexamplePointSpec)
        ((CommRingCat.Hom.hom
          ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫
            (Spec.map (CommRingCat.ofHom liftedGroundFieldMap)).appTop ≫
            (Spec (.of liftedExampleRing)).presheaf.germ ⊤ counterexamplePointSpec (by simp)))
          (ULift.up (RatFunc.X : counterexampleField)))) = _
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue liftedExampleRing) stalk_groundFieldMap_parameter

/-- The cube root, in the residue field at the closed point, of the image of the variable. -/
private noncomputable def residueRoot :
    (Spec (.of liftedExampleRing)).residueField counterexamplePointSpec :=
  stalkResidueEquiv.symm (IsLocalRing.residue liftedExampleRing
    (ULift.up (inl (RatFunc.X : counterexampleField))))

/-- The chosen residue-field element is a cube root of the image of the variable. -/
private theorem residueRoot_cube :
    let X := Spec (.of liftedExampleRing)
    let f : X ⟶ Spec (.of liftedBaseField) :=
      Spec.map (CommRingCat.ofHom liftedGroundFieldMap)
    let x : X := counterexamplePointSpec
    letI : Algebra liftedBaseField (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫ f.appTop ≫
        X.Γevaluation x).hom.toAlgebra
    residueRoot ^ 3 = algebraMap liftedBaseField (X.residueField x)
      (ULift.up (RatFunc.X : counterexampleField)) := by
  apply stalkResidueEquiv.injective
  rw [map_pow]
  simp only [residueRoot, RingEquiv.apply_symm_apply]
  rw [residueBaseMap_parameter]
  exact residueRoot_cube_in_ring

/-- A completed local ring can admit no presentation over its residue field compatible with
the ground field, even when the scheme is locally Noetherian. -/
@[stacks 0C52 "presentation_not_always_over_base_field",
  ega "IV 18.11.6" "counterexample",
  ega "0 19.6.5.2" "not k-iso to K[[T]]"]
public theorem exists_no_quotient_mvPowerSeries_algEquiv_completedLocalRing :
    ∃ (k : Type u) (_ : Field k) (X : Scheme.{u})
      (f : X ⟶ Spec (.of k)) (_ : IsLocallyNoetherian X) (x : X),
      letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      letI : Algebra k (Scheme.completedLocalRing X x) :=
        Scheme.completedLocalRingAlgebra f x
      ¬ ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.residueField x))),
          Nonempty ((MvPowerSeries (Fin n) (X.residueField x) ⧸ I) ≃ₐ[k]
            Scheme.completedLocalRing X x) := by
  refine ⟨liftedBaseField, inferInstance,
    Spec (.of liftedExampleRing),
    Spec.map (CommRingCat.ofHom liftedGroundFieldMap), inferInstance,
    counterexamplePointSpec, ?_⟩
  let X := Spec (.of liftedExampleRing)
  let f : X ⟶ Spec (.of liftedBaseField) :=
    Spec.map (CommRingCat.ofHom liftedGroundFieldMap)
  let x : X := counterexamplePointSpec
  let : Algebra liftedBaseField (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of liftedBaseField)).inv ≫ f.appTop ≫
      X.Γevaluation x).hom.toAlgebra
  let : Algebra liftedBaseField (Scheme.completedLocalRing X x) :=
    Scheme.completedLocalRingAlgebra f x
  intro h
  obtain ⟨n, I, ⟨e⟩⟩ := h
  let Q := MvPowerSeries (Fin n) (X.residueField x) ⧸ I
  let q : Q := Ideal.Quotient.mk I (MvPowerSeries.C residueRoot)
  have hq : q ^ 3 = algebraMap liftedBaseField Q
      (ULift.up (RatFunc.X : counterexampleField)) := by
    calc
      q ^ 3 = Ideal.Quotient.mk I (MvPowerSeries.C (residueRoot ^ 3)) := by
        simp [q]
      _ = Ideal.Quotient.mk I
          (MvPowerSeries.C (algebraMap liftedBaseField (X.residueField x)
            (ULift.up (RatFunc.X : counterexampleField)))) := by
        rw [residueRoot_cube]
      _ = algebraMap liftedBaseField Q
          (ULift.up (RatFunc.X : counterexampleField)) := by
        simp [Q, MvPowerSeries.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]
  have he : e q ^ 3 = algebraMap liftedBaseField
      (Scheme.completedLocalRing X x)
      (ULift.up (RatFunc.X : counterexampleField)) := by
    calc
      e q ^ 3 = e (q ^ 3) := (map_pow e.toRingHom q 3).symm
      _ = e (algebraMap liftedBaseField Q
          (ULift.up (RatFunc.X : counterexampleField))) := congrArg e hq
      _ = _ := e.commutes _
  have hring : completedStalkToRing (e q) ^ 3 =
      liftedGroundFieldMap (ULift.up (RatFunc.X : counterexampleField)) := by
    calc
      _ = completedStalkToRing (e q ^ 3) := by rw [← map_pow]
      _ = completedStalkToRing (algebraMap liftedBaseField
          (Scheme.completedLocalRing X x)
          (ULift.up (RatFunc.X : counterexampleField))) := congrArg completedStalkToRing he
      _ = _ := completedGroundFieldMap_parameter
  exact no_cube_in_liftedRing (completedStalkToRing (e q)) hring

end AlgebraicGeometry
