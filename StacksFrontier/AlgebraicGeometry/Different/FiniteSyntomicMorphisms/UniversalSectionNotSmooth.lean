module

public import Mathlib.RingTheory.AdjoinRoot
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSectionSmooth
public import StacksFrontier.RingTheory.FormsTrace.MonogenicFrame
public import StacksFrontier.RingTheory.FormsTrace.UniversalClassification
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# The universal sectioned finite syntomic family is not smooth over its base

Let `pi_d : Y_d ⟶ X_d` be the universal finite free family of rank `d` (Tag 0FKZ), let
`U_d ⊆ X_d` be the maximal open over which it is finite syntomic (Tag 0FL0) and let
`V_d = pi_d^{-1}(U_d)`. Tag 0FL3 states that `V_d` is smooth over `Spec(ZZ)`, and that the
morphism `V_d ⟶ U_d` is not smooth when `d ≥ 2`. The first assertion is
`AlgebraicGeometry.universalSyntomicPreimage_smooth`; this file proves the second and states the
two together.

## Main results

* `AlgebraicGeometry.not_smooth_universalFamily_restrict_universalSyntomicOpen`: for `d ≥ 2` the
  restriction `V_d ⟶ U_d` of the universal family is not smooth.
* `AlgebraicGeometry.universalSyntomicPreimage_smooth_and_not_smooth_restrict`: Tag 0FL3.

## Implementation notes

The point of `U_d` used is the one classifying `R[x]/(x^d)` over `R = ZZ` on its power basis
`1, x, …, x^{d-1}`: that algebra is syntomic, so the point lies in `U_d`. The base change of
`V_d ⟶ U_d` along it is the base change of the universal family along it, whose ring is
`R[x]/(x^d)` (`Stacks.FormsTrace.universalFamily_pullback_snd_iff`). Were `V_d ⟶ U_d` smooth,
`R[x]/(x^d)` would be smooth over the reduced ring `R`, hence reduced (Tag 033B), while `x` is a
nonzero nilpotent element once `d ≥ 2`.

## References

* [Stacks Project, Tag 0FL3](https://stacks.math.columbia.edu/tag/0FL3)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.FiniteFreeAlgebra Polynomial

universe u

namespace AlgebraicGeometry

/-- For `d ≥ 2` the morphism `V_d = pi_d^{-1}(U_d) ⟶ U_d`, the restriction of the universal finite
free family of rank `d` (Tag 0FKZ) over the open `U_d` of Tag 0FL0, is not smooth. -/
theorem not_smooth_universalFamily_restrict_universalSyntomicOpen (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ¬ Smooth (universalFamily.{u} d (universalAlgebraStructure d) ∣_
      universalSyntomicOpen.{u} d) := by
  intro hsm
  -- the algebra `R[x]/(x^d)` on its power basis
  let R := ULift.{u} ℤ
  have : _root_.IsReduced R :=
    isReduced_of_injective (ULift.ringEquiv : R ≃+* ℤ) ULift.ringEquiv.injective
  let P : R[X] := Polynomial.X ^ d
  have hP : P.Monic := monic_X_pow d
  let pb := AdjoinRoot.powerBasis' hP
  have hdim : pb.dim = d := by
    simp [pb, P, AdjoinRoot.powerBasis'_dim]
  let b : Module.Basis (Fin d) R (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  have hbpow : ∀ i : Fin d, b i = AdjoinRoot.root P ^ (i : ℕ) := fun i => by
    rw [show b i = pb.basis ((finCongr hdim).symm i) from Module.Basis.reindex_apply _ _ _,
      pb.basis_eq_pow]
    simp [pb]
  have hb : b 0 = 1 := by rw [hbpow]; simp
  -- its classifying point lies in `U_d`
  have hsyn : Algebra.Syntomic R (Carrier (tableOfHom (ofBasis b hb).classify)) := by
    rw [Stacks.FormsTrace.tableOfHom_classify]
    have := Stacks.FormsTrace.syntomic_adjoinRoot R P hP
    exact Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv (algEquivCarrierOfBasis b hb)
  have hg := (Stacks.FormsTrace.syntomic_tableOfHom_iff (ofBasis b hb).classify).mp hsyn
  have hr : Set.range (Spec.map (CommRingCat.ofHom ((ofBasis b hb).classify.comp
      (ULift.ringEquiv.toRingHom : ULift.{u} (universalRing d) →+* universalRing d)))).base ⊆
      Set.range (universalSyntomicOpen.{u} d).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  set π := universalFamily.{u} d (universalAlgebraStructure d) with hπ
  set ι := (universalSyntomicOpen.{u} d).ι with hι
  set ĝ := IsOpenImmersion.lift ι _ hr with hĝ
  have hfac : ĝ ≫ ι = _ := IsOpenImmersion.lift_fac ι _ hr
  -- the base change of the universal family along that point is smooth
  have h1 : Smooth (pullback.snd π ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have h2 : Smooth (pullback.snd π (ĝ ≫ ι)) := by
    rw [show pullback.snd π (ĝ ≫ ι) = (pullbackLeftPullbackSndIso π ι ĝ).inv ≫
      pullback.snd (pullback.snd π ι) ĝ by simp]
    infer_instance
  rw [hfac] at h2
  -- so `R[x]/(x^d)` is smooth over `R`, hence reduced
  have hsmR : Algebra.Smooth R (Carrier (tableOfHom (ofBasis b hb).classify)) :=
    RingHom.smooth_algebraMap.mp
      ((Stacks.FormsTrace.universalFamily_pullback_snd_iff (P := @Smooth)
        (ofBasis b hb).classify).mp h2)
  have hred : _root_.IsReduced (Carrier (tableOfHom (ofBasis b hb).classify)) :=
    Algebra.isReduced_of_smooth R _
  rw [Stacks.FormsTrace.tableOfHom_classify] at hred
  have : _root_.IsReduced (AdjoinRoot P) :=
    isReduced_of_injective (algEquivCarrierOfBasis b hb) (algEquivCarrierOfBasis b hb).injective
  -- but `x` is a nonzero nilpotent element
  have hroot : AdjoinRoot.root P ^ d = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow]
    exact AdjoinRoot.mk_self
  have hne : AdjoinRoot.root P ≠ 0 := by
    have h := b.ne_zero ⟨1, hd⟩
    rwa [hbpow, pow_one] at h
  exact hne (eq_zero_of_pow_eq_zero hroot)

/-- **Stacks Project, Tag 0FL3.** Let `pi_d : Y_d ⟶ X_d` be the universal finite free family of
rank `d` (Tag 0FKZ) and `U_d ⊆ X_d` the maximal open over which it is finite syntomic (Tag 0FL0).
Then `V_d = pi_d^{-1}(U_d)` is smooth over `Spec(ZZ)`, while for `d ≥ 2` the morphism
`V_d ⟶ U_d` is not smooth. -/
@[stacks 0FL3 "V_d = pi_d^{-1}(U_d) is smooth over Spec(Z), for the universal finite free family \
pi_d of rank d of Tag 0FKZ and the open U_d of Tag 0FL0; and for d ≥ 2 the morphism V_d → U_d, \
the restriction of pi_d over U_d, is not smooth. The deformation problem of the remark is \
Algebra.exists_finite_syntomic_section_lift."]
theorem universalSyntomicPreimage_smooth_and_not_smooth_restrict (d : ℕ) [NeZero d] :
    Smooth (specZIsTerminal.from (universalSyntomicPreimage d).toScheme) ∧
      (2 ≤ d → ¬ Smooth (universalFamily d (universalAlgebraStructure d) ∣_
        universalSyntomicOpen d)) :=
  ⟨universalSyntomicPreimage_smooth d,
    not_smooth_universalFamily_restrict_universalSyntomicOpen d⟩

end AlgebraicGeometry

end
