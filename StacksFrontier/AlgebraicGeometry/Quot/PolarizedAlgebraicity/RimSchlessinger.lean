module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# `𝒫olarized` satisfies condition (RS)

Condition (RS) of Artin's Axioms (Stacks 07WP) asks that, for a pushout square of spectra of local
Artinian rings of finite type over the base along a closed immersion `X ⟶ X'`, the comparison
functor from the fibre over the fourth corner to the 2-fibre product of the fibres over the other
three be an equivalence. For `𝒫olarized` this is Stacks 0D44: a closed immersion of spectra of
local Artinian rings is a thickening (both have a single point, and the source is nonempty), and
every morphism between affine schemes is affine.

This is axiom [2] of Artin's criterion (Stacks 07Y4) for `𝒫olarized`, used in the proof of the
algebraicity of `𝒫olarized` (Stacks 0D4X), which in turn is used for Stacks 0DPU. The declarations
are helpers and carry no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedAlgebraicity

/-- The underlying space of an affine scheme whose ring of global sections is a local Artinian
ring has at most one point: every prime of a local Artinian ring is the maximal ideal. -/
theorem subsingleton_of_isAffine_of_isArtinianRing_of_isLocalRing (X : Scheme.{u}) [IsAffine X]
    [IsLocalRing Γ(X, ⊤)] [IsArtinianRing Γ(X, ⊤)] : Subsingleton X := by
  have hS : Subsingleton (Spec Γ(X, ⊤)) := by
    refine ⟨fun x y => PrimeSpectrum.ext ?_⟩
    have hx := IsArtinianRing.isMaximal_of_isPrime x.asIdeal
    have hy := IsArtinianRing.isMaximal_of_isPrime y.asIdeal
    rw [IsLocalRing.eq_maximalIdeal hx, IsLocalRing.eq_maximalIdeal hy]
  exact X.isoSpec.hom.homeomorph.injective.subsingleton

/-- An affine scheme whose ring of global sections is local is nonempty. -/
theorem nonempty_of_isAffine_of_isLocalRing (X : Scheme.{u}) [IsAffine X]
    [IsLocalRing Γ(X, ⊤)] : Nonempty X :=
  ⟨X.isoSpec.inv (IsLocalRing.closedPoint Γ(X, ⊤))⟩

/-- **A closed immersion of spectra of local Artinian rings is a thickening.** Its target has a
single point and its source is nonempty, so it is surjective. -/
theorem isThickening_of_isClosedImmersion_of_isArtinianLocal {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i] [IsAffine X] [IsLocalRing Γ(X, ⊤)] [IsAffine X']
    [IsLocalRing Γ(X', ⊤)] [IsArtinianRing Γ(X', ⊤)] : Stacks.Thickenings.IsThickening i := by
  refine ⟨inferInstance, fun x' => ?_⟩
  obtain ⟨x⟩ := nonempty_of_isAffine_of_isLocalRing X
  have := subsingleton_of_isAffine_of_isArtinianRing_of_isLocalRing X'
  exact ⟨x, Subsingleton.elim _ _⟩

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **`𝒫olarized` satisfies condition (RS)** (Stacks 07WP), by Stacks 0D44: a pushout square of
spectra of local Artinian rings along a closed immersion is a pushout along a thickening of affine
schemes. -/
theorem satisfiesRS_polarizedSliceProjection :
    Deformation.Artin.SatisfiesRS B S hS (polarizedSliceProjection B hS hT)
      ((polarizedProjection_isFiberedInGroupoids_unconditional).sliceAtTerminal hT) := by
  intro X X' Y Y' i j i' j' w hX hX' hY _ _ _ _ _ hi hpush
  obtain ⟨hXa, hXl, -⟩ := hX
  obtain ⟨hX'a, hX'l, hX'r⟩ := hX'
  obtain ⟨hYa, -, -⟩ := hY
  have : IsAffine (B.inclusion.obj X.left) := hXa
  have : IsAffine (B.inclusion.obj Y.left) := hYa
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X) := hXa
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X') := hX'a
  have : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) := hXl
  have : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) := hX'l
  have : IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) := hX'r
  have hthick := isThickening_of_isClosedImmersion_of_isArtinianLocal
    ((BigFppfOver.toScheme B S hS).map i)
  refine Functor.isEquivalence_fiberSquareComparison_sliceAtTerminal (polarizedProjection B) hT
    polarizedProjection_isFiberedInGroupoids_unconditional i j i' j' w ?_
  exact isEquivalence_polarizedPushoutRestriction B i.left j.left i'.left j'.left
    (Functor.left_comm_of_comm i j i' j' w) hpush.flip hthick

end AlgebraicGeometry.PolarizedAlgebraicity

end
