module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.StrangeRegularSequence
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.Descent
public import StacksFrontier.RingTheory.Localization.ClosedPointOfSpecialFibre

/-!
# Regularity of a sequence is not preserved by passing to the closed fibre

There is a local homomorphism of local rings `A → B` and a regular sequence `x, y` in the
maximal ideal of `B` such that `B/(x, y)` is flat over `A`, and yet the induced sequence in the
closed fibre `B/m_A B` is neither a regular sequence nor Koszul-regular. So the converse of the
base change statement for regular sequences fails without a flatness hypothesis on `B` itself.

The witness is built from the strange regular sequence `x, y, z` of a local `ℚ`-algebra `R` with
a nonzero `δ ∈ R/zR` killed by `x` and `y`. Take `A` a discrete valuation ring with residue
field `ℚ` and fraction field containing it — concretely a localization of `ℚ[t]` at the origin —
mapping to `B = R` by sending the uniformizer to `z`. Then `x, y` is regular in `B`, the
quotient `B/(x, y)` is killed by the uniformizer, hence is a `ℚ`-vector space and so flat over
`A`; but the closed fibre is `R/zR`, where `δ` is annihilated by the images of both `x` and `y`,
which kills regularity, and kills Koszul regularity too since a common annihilator of a
Koszul-regular pair must vanish.

## Main results

* `Stacks.Examples.exists_regular_sequence_flat_quotient_not_koszulRegular_fiber`: the
  counterexample.

## References

* [Stacks Project, Tag 0641](https://stacks.math.columbia.edu/tag/0641)
-/

@[expose] public section

universe u v

namespace Stacks.Examples


private theorem moduleIsTorsionFree_of_uniformizer_regular
    {A M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [AddCommGroup M] [Module A M] {π : A} (hπ : Irreducible π)
    (hπM : IsSMulRegular M π) : Module.IsTorsionFree A M := by
  refine ⟨fun {a} ha => ?_⟩
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha.ne_zero hπ
  rw [hu]
  simpa [smul_eq_mul] using
    (Units.isSMulRegular M u).smul_iff (π ^ n) |>.mpr (hπM.pow n)


/-- A regular sequence in a local ring can give a flat quotient over a local
base while its closed-fiber sequence fails even Koszul regularity. -/
@[stacks 0641]
theorem exists_regular_sequence_flat_quotient_not_koszulRegular_fiber :
    ∃ (A : Type u) (B : Type v) (_ : CommRing A) (_ : CommRing B)
      (_ : IsLocalRing A) (_ : IsLocalRing B) (_ : Algebra A B)
      (_ : IsLocalHom (algebraMap A B)) (x y : B),
      let I : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
      x ∈ IsLocalRing.maximalIdeal B ∧
      y ∈ IsLocalRing.maximalIdeal B ∧
      RingTheory.Sequence.IsRegular B [x, y] ∧
      Module.Flat A (B ⧸ Ideal.ofList [x, y]) ∧
      ¬ RingTheory.Sequence.IsRegular (B ⧸ I)
        [Ideal.Quotient.mk I x, Ideal.Quotient.mk I y] ∧
      ¬ Koszul.IsKoszulRegular
        (fun i : Fin 2 =>
          if i = 0 then Ideal.Quotient.mk I x else Ideal.Quotient.mk I y) := by
  classical
  obtain ⟨R, hR, hRlocal, hRalg, x, y, z, hx, hy, hz, hreg,
      δ, hδ, hxδ, hyδ⟩ :=
    exists_regularSequence_with_common_annihilator_mod_last_withQ.{v}
  let : CommRing R := hR
  let : IsLocalRing R := hRlocal
  let : Algebra ℚ R := hRalg
  let f : Polynomial ℚ →+* R := (Polynomial.aeval z).toRingHom
  let P : Ideal (Polynomial ℚ) := (IsLocalRing.maximalIdeal R).comap f
  let : P.IsPrime := inferInstance
  let A₀ := Localization.AtPrime P
  have hP_eq : P = Ideal.span {Polynomial.X} := by
    refine ((PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change f Polynomial.X ∈ IsLocalRing.maximalIdeal R
    simpa [f] using hz
  have hPbot : P ≠ ⊥ := by
    rw [hP_eq]
    simp
  let : CommRing A₀ := inferInstance
  let : IsDomain A₀ := IsLocalization.isDomain_of_atPrime A₀ P
  let : IsDedekindDomain (Polynomial ℚ) := inferInstance
  let : IsDiscreteValuationRing A₀ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (Polynomial ℚ) hPbot A₀
  let π₀ : A₀ := algebraMap (Polynomial ℚ) A₀ Polynomial.X
  have hmaxA₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {π₀} := by
    calc
      IsLocalRing.maximalIdeal A₀ = Ideal.map (algebraMap (Polynomial ℚ) A₀) P := by
        symm
        simpa [A₀] using
          (IsLocalization.AtPrime.map_eq_maximalIdeal
            (R := Polynomial ℚ) (p := P) (Rₚ := A₀))
      _ = Ideal.map (algebraMap (Polynomial ℚ) A₀) (Ideal.span {Polynomial.X}) :=
        congrArg _ hP_eq
      _ = Ideal.span {π₀} := by
        rw [Ideal.map_span]
        simp [π₀]
  have hdenom : ∀ s : P.primeCompl, IsUnit (f s.1) := fun s => not_not.mp s.2
  let φ₀ : A₀ →+* R := IsLocalization.lift hdenom
  have hlocal₀ : IsLocalHom φ₀ := _root_.lift_isLocalHom_of_comap f P rfl hdenom
  let A := ULift.{u} A₀
  let e : A ≃+* A₀ := ULift.ringEquiv
  let : CommRing A := inferInstance
  let : IsDomain A := e.toEquiv.isDomain
  let : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  let π : A := e.symm π₀
  have hmaxA : IsLocalRing.maximalIdeal A = Ideal.span {π} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm, hmaxA₀, Ideal.map_span]
    simp [π, e]
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hmaxA
  let φ : A →+* R := φ₀.comp e.toRingHom
  have hlocal : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have ha₀ : IsUnit (φ₀ (e a)) := by simpa [φ] using ha
    exact (hlocal₀.map_nonunit (e a) ha₀).map e.symm.toMonoidHom
  let : IsLocalHom φ := hlocal
  let : Algebra A R := RingHom.toAlgebra φ
  have hφπ : φ π = z := by simp [φ, φ₀, π, e, π₀, f]
  have hI : Ideal.map φ (IsLocalRing.maximalIdeal A) = Ideal.span {z} := by
    rw [hmaxA, Ideal.map_span, Set.image_singleton, hφπ]
  have hregxy : RingTheory.Sequence.IsRegular R [x, y] := by
    refine ⟨((RingTheory.Sequence.isWeaklyRegular_append_iff (M := R) [x, y] [z]).mp
      hreg.toIsWeaklyRegular).1, fun hxy => hreg.top_ne_smul ?_⟩
    have hle : Ideal.ofList [x, y] ≤ Ideal.ofList [x, y, z] := by
      apply Ideal.span_mono
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      simp only [List.mem_cons, List.not_mem_nil] at ha ⊢
      tauto
    exact (top_le_iff.mp (hxy.le.trans (Submodule.smul_mono hle le_rfl))).symm
  let M : Type v := R ⧸ Ideal.ofList [x, y]
  have hsmulIdeal (J : Ideal R) :
      (J • (⊤ : Submodule R R) : Submodule R R) = J := by
    rw [Ideal.smul_top_eq_map J]
    simp
  have hzM : IsSMulRegular M z := by
    change IsSMulRegular (R ⧸ Ideal.ofList [x, y]) z
    rw [← hsmulIdeal (Ideal.ofList [x, y])]
    exact hreg.regular_mod_prev 2 (by simp)
  have hπM : IsSMulRegular M π :=
    IsSMulRegular.of_map (algebraMap A R)
      (fun m => IsScalarTower.algebraMap_smul (A := R) (M := M) π m)
      (by change IsSMulRegular M (φ π); rwa [hφπ])
  let : IsDedekindDomain A := inferInstance
  let : Module.IsTorsionFree A M := moduleIsTorsionFree_of_uniformizer_regular hπ hπM
  have hflat : Module.Flat A M := inferInstance
  refine ⟨A, R, inferInstance, hR, inferInstance, hRlocal, inferInstance, hlocal,
    x, y, ?_⟩
  let I : Ideal R := Ideal.map φ (IsLocalRing.maximalIdeal A)
  let e : R ⧸ Ideal.span {z} ≃+* R ⧸ I := Ideal.quotientEquivAlgOfEq R hI.symm
  let δI : R ⧸ I := e δ
  have hδI : δI ≠ 0 := fun h => hδ (e.injective h)
  have hδx : (Ideal.Quotient.mk I x) * δI = 0 := by simpa [e, δI] using congrArg e hxδ
  have hδy : (Ideal.Quotient.mk I y) * δI = 0 := by simpa [e, δI] using congrArg e hyδ
  refine ⟨hx, hy, hregxy, hflat, ?_, ?_⟩
  · intro hfiber
    exact hδI <| ((RingTheory.Sequence.isRegular_cons_iff _ _ _).mp hfiber).1
      (by change Ideal.Quotient.mk I x * δI = Ideal.Quotient.mk I x * 0; rw [mul_zero, hδx])
  · let fFiber : Fin 2 → R ⧸ I := fun i =>
      if i = 0 then Ideal.Quotient.mk I x else Ideal.Quotient.mk I y
    intro hfiber
    refine hδI <| Koszul.annihilator_eq_zero_of_isKoszulRegular fFiber hfiber δI fun i => ?_
    fin_cases i
    · rw [mul_comm]
      simpa [fFiber] using hδx
    · rw [mul_comm]
      simpa [fFiber] using hδy

end Stacks.Examples

end
