module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpPointTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing

/-!
# The blowup of a closed point, base changed to the local ring there

Let `p` be a closed point of a scheme `X` and `A` a local ring with `e : A ≃+* 𝒪_{X, p}`. The
blowup of `X` in `p`, base changed along the flat morphism `Spec A ≅ Spec 𝒪_{X, p} ⟶ X`, is the
blowup `AlgebraicGeometry.BlowUpDualizing.blowUpScheme A` of `Spec A` in its maximal ideal, the
scheme on which [Stacks, Tag 0B64] is stated ([Stacks, Tag 0805]).

The square is `AlgebraicGeometry.exists_isPullback_blowUp_maximalIdealSheaf`, stated for the
blowup in `AlgebraicGeometry.maximalIdealSheaf A`; this file identifies that ideal sheaf with the
centre `AlgebraicGeometry.BlowUpDualizing.centre A` (the kernel of the closed point
`Spec κ ⟶ Spec A`) used by [Stacks, Tag 0B64].

## Main results

* `AlgebraicGeometry.BlowUpDualizing.centre_eq_maximalIdealSheaf`: the two ideal sheaves agree.
* `AlgebraicGeometry.BlowUpDualizing.exists_isPullback_blowUpScheme`: the cartesian square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The kernel of the closed point `Spec κ ⟶ Spec A` is the ideal sheaf of the maximal ideal. -/
theorem centre_eq_maximalIdealSheaf : centre A = maximalIdealSheaf A := by
  rw [centre, Stacks.Blowup.residuePoint, Scheme.ker_SpecMap]
  congr 2
  exact IsLocalRing.ker_residue

/-- **The blowup of a closed point base changed to the local ring there** ([Stacks, Tag 0805]).
For a closed point `p` of `X` and `e : A ≃+* 𝒪_{X, p}`, the blowup of `Spec A` in its maximal
ideal is the base change of the blowup of `X` in `p` along `Spec A ⟶ X`, by a flat
preimmersion. -/
theorem exists_isPullback_blowUpScheme {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X))
    (e : A ≃+* X.presheaf.stalk p) :
    ∃ h : blowUpScheme A ⟶
        blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)),
      IsPullback (blowUpToBase (centre A)) h (specToOfRingEquivStalk A p e)
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))) ∧
      Flat h ∧ IsPreimmersion h := by
  have key : ∀ I : (Spec (.of A)).IdealSheafData, I = maximalIdealSheaf A →
      ∃ h : blowUp I ⟶
          blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)),
        IsPullback (blowUpToBase I) h (specToOfRingEquivStalk A p e)
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))) ∧
        Flat h ∧ IsPreimmersion h := by
    rintro I rfl
    exact exists_isPullback_blowUp_maximalIdealSheaf A p hp e
  exact key _ (centre_eq_maximalIdealSheaf A)

end AlgebraicGeometry.BlowUpDualizing

end
