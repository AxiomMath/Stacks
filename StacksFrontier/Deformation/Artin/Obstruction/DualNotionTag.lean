module

public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClassAmbient
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClassCanonical
public import StacksFrontier.Deformation.Artin.Obstruction.DualNotionOpenness
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveObstructionAtTranslation
public import StacksFrontier.Deformation.Artin.Obstruction.PerfectDualTensor
public import StacksFrontier.Deformation.Artin.Obstruction.SquareZeroNaiveCotangent

/-!
# Stacks 07YZ

In Situation 07YX — an object `x` of a category fibred in groupoids over the big fppf site of a
locally Noetherian scheme `S`, lying over `U = Spec A` with `A` of finite type over the ring `Λ`
of an affine open `Spec Λ ⊆ S`, whose deformation theory is presented by a complex `K` of
`A`-modules — assume clause (iv) of Lemma 07YY and that `K` is a perfect object of `D(A)`. Then
if `x` is versal at a closed point `u₀ ∈ U` there is an open neighbourhood `u₀ ∈ U' ⊆ U` such
that `x` is versal at every finite type point of `U'`.

This file states and proves that.

## Main results

* `Deformation.Artin.DualNotion.exists_opennessInput_of_isPerfect` — the source's own reduction:
  perfectness of `K` together with clause (iv) produce the dual perfect complex `E = Kᵛ[-1]` of
  [Stacks, Tag 07VI] and the cotangent class `ξ` of [Stacks, Tag 07YY], satisfying assumptions
  (i) and (ii) of [Stacks, Tag 07YN].
* `Deformation.Artin.DualNotion.exists_isOpen_isVersalAt_of_isPerfect` — **Stacks 07YZ**.

## Implementation notes

The proof is the source's. Clause (iv) gives the cotangent obstruction class
`ξ₀ ∈ H¹(K ⊗ᴸ NL_{A/Λ})` of [Stacks, Tag 07YY]
(`Deformation.Artin.exists_isCotangentObstructionClass`); perfectness of `K` turns the functor
`H¹(K ⊗ᴸ −)` into `Hom_{D(A)}(E, −)` for `E = Kᵛ[-1]`, naturally
(`Deformation.Artin.exists_perfect_homologyOneEquiv`, which is [Stacks, Tag 07VI] in degree one);
and `ξ` is the morphism `E ⟶ NL_{A/Λ}` corresponding to `ξ₀`.

Assumption (i) of [Stacks, Tag 07YN] then reads: `x` lifts over a square-zero thickening
`A' → A` exactly when `ξ` is killed by the base-change map `NL_{A/Λ} ⟶ NL_{A/A'}`. The dual
situation gives liftability exactly when the obstruction element vanishes, and clause (1) of
[Stacks, Tag 07YY] identifies that element with the evaluation of `ξ₀` at the extension class
`NL_{A/Λ} ⟶ I[1]`; the extension class is the base-change map followed by the identification
`NL_{A/A'} = I[1]`, which is an isomorphism
(`Deformation.Artin.isIso_squareZeroCotangentClass`), so being killed by one is being killed by
the other. Assumption (ii) is clause (2) of [Stacks, Tag 07YY] read through the same natural
identification, with `Ext⁰_A(E, M)` spelled as a group of morphisms by
`Deformation.Artin.extZeroAddEquiv`. Assumption (iii) — finiteness of the cohomology of `E` — is
not assumed: it follows from perfectness of `E` over the Noetherian ring `A`.

The site-size condition on `A[Ω_{A/Λ}]` needed to speak of the canonical element of
`T_x(Ω_{A/Λ})` is not a hypothesis either: it is
`Deformation.Artin.differentialsSquareZero_mem_site`, since `Ω_{A/Λ}` is a finite `A`-module.

## References

* [Stacks Project, Tag 07YZ](https://stacks.math.columbia.edu/tag/07YZ)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin.DualNotion

universe u v w

attribute [local instance 10000] HasDerivedCategory.standard

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- **The source's reduction of Stacks 07YZ.** Perfectness of `K` and clause (iv) of
[Stacks, Tag 07YY] produce the dual perfect complex `E = Kᵛ[-1]` of [Stacks, Tag 07VI] together
with a morphism `ξ : E ⟶ NL_{A/Λ}` satisfying assumptions (i) and (ii) of
[Stacks, Tag 07YN]. -/
public theorem exists_opennessInput_of_isPerfect
    (hperfect : StacksDraft.Perfect.IsPerfect sit.K)
    (hboundary : ObstructionBoundaryCondition Λ A B S hS toS hA X p sit) :
    ∃ (E : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect E)
      (ξ : E ⟶ derivedNaiveCotangentComplex Λ A),
      Nonempty (OpennessInput Λ A B S hS toS hA X p sit
        (differentialsSquareZero_mem_site Λ A B hA sit.finiteType) E ξ) := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_isCotangentObstructionClass Λ A B S hS toS hA X p sit hboundary
  obtain ⟨E, hEperf, Φ, hΦ⟩ := exists_perfect_homologyOneEquiv A sit.K hperfect
  have key : ∀ (Z : DerivedCategory (ModuleCat.{u} A)) (c : derivedNaiveCotangentComplex Λ A ⟶ Z),
      (derivedTensorCohomology A sit.K 1).map c ξ₀ = 0 ↔
        Φ (derivedNaiveCotangentComplex Λ A) ξ₀ ≫ c = 0 := fun Z c => by
    rw [← hΦ (derivedNaiveCotangentComplex Λ A) Z c ξ₀]
    exact (map_eq_zero_iff (Φ Z) (Φ Z).injective).symm
  refine ⟨E, hEperf, Φ (derivedNaiveCotangentComplex Λ A) ξ₀, ⟨?_⟩⟩
  refine
    { hasLift_iff_xi_comp_eq_zero := ?_
      tangentMap := fun M a => extZeroAddEquiv E _ (Φ _ (sit.tangentMap M a))
      tangentMap_add := ?_
      tangentMap_natural := ?_
      tangentMap_bijective := ?_
      tangentMap_canonicalElement := ?_ }
  · intro A' _ D instΛ instA instTower hmap hchart
    let : Algebra Λ A' := instΛ
    let : Algebra A' A := instA
    let : IsScalarTower Λ A' A := instTower
    have hsurj : Function.Surjective (algebraMap A' A) := by
      rw [hmap]
      exact D.squareZeroSurjection.1
    have hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥ := by
      rw [hmap]
      exact D.squareZeroSurjection.2
    let := Stacks.Smooth.kerModule hsurj hsq
    rw [nonempty_underFiber_iff_obstructionEvaluation_eq_zero Λ A B S hS toS hA X p sit ξ₀ hξ₀
      A' D hmap hchart hsurj hsq,
      ← comp_cotangentExtensionClass_eq_zero_iff Λ A' A hsurj hsq
        (Φ (derivedNaiveCotangentComplex Λ A) ξ₀),
      ← key _ (cotangentExtensionClass Λ A' A hsurj hsq)]
    exact map_eq_zero_iff _ ((ModuleCat.mono_iff_injective
      (shiftedCohomologyIso A sit.K (ModuleCat.of A (RingHom.ker (algebraMap A' A)))).hom).mp
        inferInstance)
  · intro M a a'
    rw [map_add, map_add, map_add]
  · intro M N f a
    have hpush : extPushforward E f.hom 0 (extZeroAddEquiv E _ (Φ _ (sit.tangentMap M a))) =
        extZeroAddEquiv E _ (Φ _ (sit.tangentMap M a) ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom) := by
      refine (extZeroAddEquiv E _).symm.injective ?_
      rw [AddEquiv.symm_apply_apply]
      exact (extZeroAddEquiv_symm_comp_shift (extZeroAddEquiv E _ (Φ _ (sit.tangentMap M a)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)).trans
          (by rw [AddEquiv.symm_apply_apply])
    rw [hpush]
    exact congrArg (extZeroAddEquiv E _) ((congrArg (Φ _) (sit.tangentNatural f a)).trans
      (hΦ _ _ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom) (sit.tangentMap M a)))
  · exact fun M => (extZeroAddEquiv E _).bijective.comp
      ((Φ _).bijective.comp (sit.tangentBijective M))
  · have hcan : Φ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (differentialsModule Λ A))
          ((derivedTensorCohomology A sit.K 1).map (naiveCotangentToDifferentials Λ A) ξ₀) =
        Φ (derivedNaiveCotangentComplex Λ A) ξ₀ ≫ naiveCotangentToDifferentials Λ A :=
      hΦ _ _ (naiveCotangentToDifferentials Λ A) ξ₀
    change extZeroAddEquiv E _ (Φ _ (sit.tangentMap _ _)) = _
    rw [hξ₀.2, hcan]
    rfl

include sit in
/-- **Stacks 07YZ.** In Situation 07YX assume that (iv) of Lemma 07YY holds and that `K` is a
perfect object of `D(A)`. In this case, if `x` is versal at a closed point `u₀ ∈ U = Spec A`
then there exists an open neighbourhood `u₀ ∈ U' ⊆ U` such that `x` is versal at every finite
type point of `U'`. -/
@[stacks 07YZ]
public theorem exists_isOpen_isVersalAt_of_isPerfect
    (hboundary : ObstructionBoundaryCondition Λ A B S hS toS hA X p sit)
    (hperfect : StacksDraft.Perfect.IsPerfect sit.K)
    (u₀ : Spec (.of A)) (hu₀ : IsClosed ({u₀} : Set (Spec (.of A))))
    (hversal : IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ sit.x
      (versalityBase Λ A B S hS toS hA X p sit)) :
    ∃ V : Set (Spec (.of A)), IsOpen V ∧ u₀ ∈ V ∧
      ∀ u ∈ V, IsFiniteTypePoint u →
        IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u sit.x
          (versalityBase Λ A B S hS toS hA X p sit) := by
  have := isNoetherianRing_of_dualDeformationSituation Λ A B S hS toS hA X p sit
  obtain ⟨E, hEperf, ξ, ⟨input⟩⟩ :=
    exists_opennessInput_of_isPerfect Λ A B S hS toS hA X p sit hperfect hboundary
  exact exists_isOpen_isVersalAt_of_opennessInput Λ A B S hS toS hA X p sit _ E ξ
    (minus_of_isPerfect E hEperf) input
    (StacksDraft.Perfect.finite_homology_of_isPerfect A E hEperf) u₀ hu₀ hversal

end Deformation.Artin.DualNotion

end
