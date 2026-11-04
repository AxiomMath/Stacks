module

public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibreUniverse
public import StacksFrontier.RingTheory.Catenary.Universes
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayFromModule
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.FormalFibres.SerreConditionOne
public import StacksFrontier.RingTheory.LocalCohomology.PrincipalQuotientFiniteness

/-!
# A ring with a dualizing complex: universal catenarity and `(S₁)` formal fibres

A Noetherian ring `A` with a dualizing complex is universally catenary (Stacks 0A80) and the
formal fibres of its local rings are Gorenstein (Stacks 0AWY), hence Cohen–Macaulay
(Stacks 0DW8), hence `(S₁)`. This file records these two consequences in the form in which the
coherence criterion for a pushforward, Stacks 0AWB
(`AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`), asks
for them: universal catenarity of the ring, and `(S₁)` for the formal fibres
`𝒪^∧_{X,z} ⊗ κ(𝔮)` of the local rings of `X = Spec(A)`.

## Main results

* `Stacks.Algebraization.hasSerreCondition_of_isCohenMacaulayRing` — a Cohen–Macaulay ring
  satisfies `(Sₙ)` for every `n`.
* `Stacks.Algebraization.isUniversallyCatenary_and_formalFibres_of_isDualizingComplex` — a
  Noetherian ring with a dualizing complex, in any module universe, is universally catenary and
  the formal fibres of the local rings of its spectrum satisfy `(S₁)`.

## Implementation notes

The dualizing complex may live in `ModuleCat.{v} A` for an arbitrary universe `v`. As in
`Stacks.AdicCompletionFibreUniverse.depth_fibre_localization_eq_height_univ`, it is moved to
`ULift.{v} A`, a localization of `A` at its units, where it lives in the ring's own universe
(Stacks 0A7G); universal catenarity comes back along the surjection `ULift.{v} A → A`, and the
formal fibres along the ring isomorphism between the localization of `ULift.{v} A` at the prime
corresponding to `z` and the stalk of `Spec(A)` at `z`, which induces isomorphisms of the
completions and of the fibres.

## References

* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0DW8](https://stacks.math.columbia.edu/tag/0DW8)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Algebraization

/-- A Cohen–Macaulay Noetherian ring satisfies Serre's condition `(Sₙ)` for every `n`. -/
theorem hasSerreCondition_of_isCohenMacaulayRing (R : Type*) [CommRing R]
    [IsNoetherianRing R] (h : IsCohenMacaulayRing R) (n : ℕ) : HasSerreCondition R n := by
  intro p _
  have hcm := h p
  rw [IsCohenMacaulayLocalRingPropForm, Dualizing.localRingDepth_eq_depth_self] at hcm
  rw [← hcm]
  exact min_le_right _ _

/-- **A ring with a dualizing complex is universally catenary and has `(S₁)` formal fibres.** For a
Noetherian ring `A` with a dualizing complex in `ModuleCat.{v} A`, the ring is universally
catenary, and for every point `z` of `X = Spec(A)` and every prime `𝔮` of `𝒪_{X,z}` the formal
fibre `𝒪^∧_{X,z} ⊗ κ(𝔮)` satisfies `(S₁)`. These are the two hypotheses of Stacks 0AWB. -/
theorem isUniversallyCatenary_and_formalFibres_of_isDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{v} A), Dualizing.IsDualizingComplex K) :
    Ring.IsUniversallyCatenary A ∧
      ∀ (z : Spec (CommRingCat.of A))
        (q : PrimeSpectrum ((Spec (CommRingCat.of A)).presheaf.stalk z)),
        HasSerreCondition ((Spec (CommRingCat.of A)).completedLocalRing z ⊗[
          (Spec (CommRingCat.of A)).presheaf.stalk z] q.asIdeal.ResidueField) 1 := by
  obtain ⟨K, hK⟩ := hdualizing
  let e : A ≃+* ULift.{v} A := ULift.ringEquiv.symm
  let _ : Algebra A (ULift.{v} A) := e.toRingHom.toAlgebra
  let M₀ : Submonoid (ULift.{v} A) := IsUnit.submonoid (ULift.{v} A)
  let M : Submonoid A := M₀.map e.symm.toRingHom
  have hloc : IsLocalization M (ULift.{v} A) :=
    IsLocalization.isLocalization_of_base_ringEquiv M₀ (ULift.{v} A) e.symm
  have hN : IsNoetherianRing (ULift.{v} A) :=
    IsLocalization.isNoetherianRing M (ULift.{v} A) inferInstance
  have hKC := Dualizing.isDualizingComplex_localization (B := ULift.{v} A) M K hK
  obtain ⟨hcat, hfib⟩ :=
    LocalCohomology.isUniversallyCatenary_and_formalFibresAreCohenMacaulay_of_isDualizingComplex
      _ hKC
  refine ⟨Ring.IsUniversallyCatenary.of_surjective' (f := (ULift.ringEquiv : ULift.{v} A ≃+* A))
    ULift.ringEquiv.surjective hcat, fun z q => ?_⟩
  let z' : PrimeSpectrum A := z
  let P : PrimeSpectrum (ULift.{v} A) :=
    ⟨z'.asIdeal.comap e.symm.toRingHom, Ideal.comap_isPrime _ _⟩
  let S := (Spec (CommRingCat.of A)).presheaf.stalk z
  let L := Localization.AtPrime P.asIdeal
  let E : L ≃+* S :=
    (Localization.localRingEquiv P.asIdeal z'.asIdeal e.symm rfl).trans
      (IsLocalization.algEquiv z'.asIdeal.primeCompl (Localization.AtPrime z'.asIdeal)
        ((Spec.structureSheaf A).presheaf.stalk z')).toRingEquiv
  let p : Ideal L := q.asIdeal.comap E.toRingHom
  obtain ⟨hF, hCM⟩ := hfib P p
  have hS : HasSerreCondition (TensorProduct L (AdicCompletion (IsLocalRing.maximalIdeal L) L)
      p.ResidueField) 1 :=
    @hasSerreCondition_of_isCohenMacaulayRing _ _ hF hCM 1
  obtain ⟨Φ, -⟩ := Stacks.FormalFibres.exists_fiber_ringEquiv E
    (Stacks.FormalFibres.completionRingEquiv E)
    (Stacks.FormalFibres.completionRingEquiv_algebraMap E) q.asIdeal
  exact HasSerreCondition.of_ringEquiv
    (((Algebra.TensorProduct.comm L _ _).toRingEquiv.trans Φ).trans
      (Algebra.TensorProduct.comm S _ _).toRingEquiv) hS

end Stacks.Algebraization

end
