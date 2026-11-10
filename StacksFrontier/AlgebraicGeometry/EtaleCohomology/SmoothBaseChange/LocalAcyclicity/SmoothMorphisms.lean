module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.StrictlyHenselianBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.StrictHenselizationBaseChange

/-!
# Smooth morphisms are universally locally acyclic

Stacks, Proposition 0GJQ: a smooth morphism of schemes `f : X ⟶ S` is universally locally
acyclic.

## Implementation notes

The theorems take the inputs of the smooth base change theorem
(`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth`) as named
arguments. The form with every input supplied is
`Stacks.EtaleCohomology.SmoothBaseChange.isUniversallyLocallyAcyclic_of_smooth_unconditional`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isLocallyAcyclic_of_smooth` — a smooth morphism is
  locally acyclic.
* `Stacks.EtaleCohomology.SmoothBaseChange.isUniversallyLocallyAcyclic_of_smooth` — the
  statement of Proposition 0GJQ: a smooth morphism is
  `AlgebraicGeometry.IsUniversallyLocallyAcyclic`.

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- In a field, a positive integer prime to the characteristic is a unit. -/
theorem isUnit_natCast_of_ringChar_eq_zero_or_coprime {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (h : ringChar K = 0 ∨ n.Coprime (ringChar K)) : IsUnit (n : K) := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have hd : ringChar K ∣ n := (ringChar.spec K n).1 h0
  rcases h with h | h
  · rw [h, zero_dvd_iff] at hd
    omega
  · exact CharP.ringChar_ne_one (Nat.Coprime.eq_one_of_dvd h.symm hd)

variable (B : BigEtaleSite.{u})

/-- **An integer invertible at a geometric point is invertible on the strict henselization
there**: if `n > 0` is invertible in the residue field of the geometric point `s`, then `n` is a
unit in the global sections of the strict henselization of `S` at `s`. -/
theorem isUnit_intCast_globalSections_strictHenselization {S : Scheme.{u}} (hS : B.Contains S)
    (s : GeometricPoint S) {n : ℕ} (hn : 0 < n)
    (h : ringChar s.residueField = 0 ∨ n.Coprime (ringChar s.residueField)) :
    IsUnit (((n : ℤ) : Γ(strictHenselization B S hS s, ⊤))) := by
  have := structureSheafStalkToGeometricField_isLocalHom B S hS s
  have hR : IsUnit ((n : ℤ) : ↥(etaleLocalRing B S hS s)) := by
    refine isUnit_of_map_unit (structureSheafStalkToGeometricField B S hS s) _ ?_
    rw [map_intCast, Int.cast_natCast]
    exact isUnit_natCast_of_ringChar_eq_zero_or_coprime hn h
  simpa using hR.map (Scheme.ΓSpecIso (.of ↥(etaleLocalRing B S hS s))).inv.hom

variable {B}

/-- The geometric point of `X ×_S Spec 𝒪^{sh}_{S,f(x)}` determined by `x` lies over `x`. -/
theorem strictHenselizationBaseChangePoint_map_fst {X S : Scheme.{u}} (hS : B.Contains S)
    (f : X ⟶ S) (x : GeometricPoint X) :
    (strictHenselizationBaseChangePoint B hS f x).map (pullback.fst _ _) = x :=
  congrArg (fun m : Spec (.of x.residueField) ⟶ X => GeometricPoint.mk x.residueField m)
    (pullback.lift_fst _ _ _)

/-- The structure morphism of the strict henselization of `Spec 𝒪^{sh}_{S,f(x)}` at the image of
the geometric point of `X ×_S Spec 𝒪^{sh}_{S,f(x)}` determined by `x` is an isomorphism. -/
theorem isIso_strictHenselizationToBase_strictHenselizationBaseChangePoint {X S : Scheme.{u}}
    (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X) :
    IsIso (strictHenselizationToBase B _ (contains_strictHenselization B S hS (x.map f))
      ((strictHenselizationBaseChangePoint B hS f x).map (pullback.snd _ _))) := by
  refine isIso_strictHenselizationToBase_of_strictlyHenselian B _ _ _ ?_
  change (pullback.lift x.hom (geometricPointToStrictHenselization B S hS (x.map f)) _ ≫
    pullback.snd _ _) default = _
  rw [pullback.lift_snd]
  exact geometricPointToStrictHenselization_base_default B S hS (x.map f)

/-- **A smooth morphism is locally acyclic**, given the inputs `h0EYS`, `h0EZR`, `h0EZS`,
`h0F08`, `h03SC2`, `h03SC6` and `h0EYD` of the smooth base change theorem
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth`. -/
theorem isLocallyAcyclic_of_smooth
    (h0EYS : FlatReducedFibresBaseChange.{u}) (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) (h0F08 : FirstFailureNormalization.{u})
    (h03SC2 : AffineCurveCohomologyVanishing.{u}) (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f] :
    IsLocallyAcyclic B hX hS f := by
  intro x n hn hchar
  let π := strictHenselizationToBase B S hS (x.map f)
  let hS₁ := contains_strictHenselization B S hS (x.map f)
  let hX₁ := contains_strictHenselizationBaseChange B hX hS f x
  let x₁ := strictHenselizationBaseChangePoint B hS f x
  let A : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  have := isIso_baseChangeStrictHenselizationMap B hS f x
  have := isIso_strictHenselizationToBase_strictHenselizationBaseChangePoint hS f x
  have h₁ := isLocallyAcyclicAt_of_smooth_of_isIso_strictHenselizationToBase h0EYS h0EZR h0EZS
    h0F08 h03SC2 h03SC6 h0EYD hX₁ hS₁ (pullback.snd f π) x₁ n hn
    (isUnit_intCast_globalSections_strictHenselization B hS (x.map f) hn hchar)
  have h₂ : IsLocallyAcyclicAt B hX₁ hS₁ (pullback.snd f π)
      ((smallEtaleDerivedPullbackAb (pullback.fst f π)).obj (smallEtaleConstantZModComplex X n))
      x₁ := fun t =>
    (NatTrans.isIso_app_iff_of_iso _
      (smallEtaleDerivedPullbackAbConstantComplexIso (pullback.fst f π) A)).2 (h₁ t)
  have h₃ := isLocallyAcyclicAt_of_isPushout_of_isIso B hX hS hS₁ hX₁
    (IsPullback.of_hasPullback f π) (smallEtaleConstantZModComplex X n)
    (isPushout_strictHenselizationBaseChange B hX hS f x) h₂
  rw [← strictHenselizationBaseChangePoint_map_fst hS f x]
  exact h₃

/-- **Smooth morphisms are universally locally acyclic** (Stacks 0GJQ), from the inputs of the
smooth base change theorem (Stacks 0EYU). Let `f : X ⟶ S` be a smooth morphism of schemes. Then
`f` is universally locally acyclic (`AlgebraicGeometry.IsUniversallyLocallyAcyclic`): for every
morphism `S' ⟶ S` and every big étale site containing `X ×_S S'` and `S'`, the base change
`X ×_S S' ⟶ S'` of `f` is locally acyclic there.

The arguments `h0EYS`, `h0EZR`, `h0EZS`, `h0F08`, `h03SC2`, `h03SC6` and `h0EYD` are
those of the smooth base change theorem
`Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth`. -/
theorem isUniversallyLocallyAcyclic_of_smooth
    (h0EYS : FlatReducedFibresBaseChange.{u}) (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) (h0F08 : FirstFailureNormalization.{u})
    (h03SC2 : AffineCurveCohomologyVanishing.{u}) (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    IsUniversallyLocallyAcyclic f :=
  fun _ g _ hX' hS' =>
    isLocallyAcyclic_of_smooth h0EYS h0EZR h0EZS h0F08 h03SC2 h03SC6 h0EYD hX' hS'
      (pullback.snd f g)

end Stacks.EtaleCohomology.SmoothBaseChange

end
