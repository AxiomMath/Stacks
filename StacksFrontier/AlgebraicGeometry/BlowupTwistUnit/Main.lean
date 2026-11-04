module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.Algebra
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.AwayFromCentre
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.CanonicalSectionAway
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformIsoOverOpen
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistNegativeOne

/-!
# `𝒪_X ⟶ b_*𝒪_{X'}(E)` for the blowing up of a scheme in a quasi-coherent sheaf of ideals

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, `b : X' ⟶ X` the blowing up of
`X` in `ℐ` and `E ⊆ X'` its exceptional divisor. Multiplication by the canonical section of
`𝒪_{X'}(E)` gives, by adjunction, a canonical map

`α : 𝒪_X ⟶ b_*𝒪_{X'}(E)`

(`Stacks.DeRham.BlowupTwist.twistUnitComparison` at the exceptional twist and its canonical
section). This file assembles what is proved about `α` out of the two halves of the point it has
to be decided at: away from the centre, and at the centre.

*Away from the centre* the map is invertible with no hypothesis beyond the invertibility of the
canonical section there: the blowup is an isomorphism over the complement of the centre
(`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`), so
`Stacks.BlowupTwistUnit.isIso_pullback_twistUnitComparison` applies.

*At a closed point* the question is the invertibility of one stalk, and the local criterion
`Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_isIso_stalk_compl` reduces the global
statement to it. The arithmetic that decides that stalk, given an abstract identification of it
with the local ring, is `Stacks.BlowupTwistUnit.bijective_of_forall_notMem_isPrime`: a map of a
two-dimensional regular — indeed any Noetherian — local ring into a module isomorphic to it is
bijective as soon as the scalar it is multiplication by lies in no prime but the maximal one.

## Main results

* `Stacks.BlowupTwistUnit.isIso_pullback_canonicalSectionHom_exceptionalIdeal`: **the canonical
  section of `𝒪_{X'}(E)` is invertible over the preimage of an open disjoint from the centre.**
* `Stacks.BlowupTwistUnit.isIso_pullback_exceptionalTwistUnitComparison`: **`α` is invertible over
  an open of the base over which the blowup is an isomorphism**, as soon as the canonical section
  of the exceptional twist is invertible over the preimage of that open.
* `Stacks.BlowupTwistUnit.isIso_twistUnitComparison_exceptionalIdeal` and
  `isIso_twistUnitComparison_exceptionalIdeal_of_isIso_stalk`: **`α` is invertible**, the second
  with the half away from the centre discharged, so that only the stalks at the centre remain.
* `Stacks.BlowupTwistUnit.bijective_of_forall_notMem_isPrime`: the arithmetic at the closed
  point, in the form a stalk computation delivers it.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The arithmetic at the closed point -/

/-- **A linear map of a local ring into a module isomorphic to it is bijective as soon as the
scalar it carries `1` to lies in no prime but the maximal one.**

The map is multiplication by `t = e (φ 1)` read through the isomorphism `e`, and
`Stacks.BlowupTwistUnit.isUnit_of_forall_isPrime_eq_maximalIdeal` makes `t` a unit.  This is
the shape in which the comparison map of a blowup at a closed point is decided: `φ` is its stalk,
`e` is an abstract identification of that stalk with the local ring, and the hypothesis is the
invertibility of the comparison away from the point. -/
theorem bijective_of_forall_notMem_isPrime {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hdim : 2 ≤ ringKrullDim A) {N : Type u} [AddCommGroup N] [Module A N]
    (e : N ≃ₗ[A] A) (φ : A →ₗ[A] N)
    (h : ∀ p : Ideal A, p.IsPrime → p ≠ IsLocalRing.maximalIdeal A → e (φ 1) ∉ p) :
    Function.Bijective φ := by
  have hunit : IsUnit (e (φ 1)) := by
    refine isUnit_of_forall_isPrime_eq_maximalIdeal hdim fun p hp hmem ↦ ?_
    by_contra hne
    exact h p hp hne hmem
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
  have hcomp : ∀ x : A, e (φ x) = x * e (φ 1) := by
    intro x
    have hx : x • (1 : A) = x := by rw [smul_eq_mul, mul_one]
    calc e (φ x) = e (φ (x • (1 : A))) := by rw [hx]
      _ = x * e (φ 1) := by rw [map_smul, map_smul, smul_eq_mul]
  refine ⟨fun x y hxy ↦ ?_, fun n ↦ ?_⟩
  · have hx : x * e (φ 1) = y * e (φ 1) := by
      rw [← hcomp, ← hcomp, hxy]
    calc x = x * e (φ 1) * v := by rw [mul_assoc, hv, mul_one]
      _ = y * e (φ 1) * v := by rw [hx]
      _ = y := by rw [mul_assoc, hv, mul_one]
  · refine ⟨e n * v, e.injective ?_⟩
    rw [hcomp]
    calc e n * v * e (φ 1) = e n * (e (φ 1) * v) := by ring
      _ = e n := by rw [hv, mul_one]

/-! ### The comparison map of the exceptional twist -/

variable {X : Scheme.{u}} (M : X.IdealSheafData)

/-- **The comparison map `𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible over an open of the base over which
the blowup is an isomorphism**, as soon as the canonical section of `𝒪_{X'}(E)` is invertible over
the preimage of that open.

The blowup is an isomorphism over the complement of the centre, part of [Stacks, Tag 02OS]
(`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`), which is the open this is applied
at; over it `Stacks.BlowupTwistUnit.isIso_pullback_twistUnitComparison` applies, the adjunction
unit restricting to an isomorphism and the direct image of the section travelling by the
naturality of the base-change morphism of the restriction square. -/
theorem isIso_pullback_exceptionalTwistUnitComparison (V : X.Opens)
    [IsIso (blowUpToBase M ∣_ V)]
    (hs : IsIso ((pullbackFunctor (blowUpToBase M ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
      (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M)))) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
        (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
        (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M)))) :=
  isIso_pullback_twistUnitComparison (blowUpToBase M) V
    (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
    (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M)) hs

/-- **The comparison map `𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible**, given the invertibility of the
canonical section of `𝒪_{X'}(E)` over the preimage of an open `V` of the base over which the
blowup is an isomorphism, together with the invertibility of its stalk at each point outside `V`.

Over `V` this is `Stacks.BlowupTwistUnit.isIso_pullback_exceptionalTwistUnitComparison`; the
passage from there to the whole scheme is
`Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_isIso_stalk_compl`. -/
theorem isIso_twistUnitComparison_exceptionalIdeal (V : X.Opens)
    [IsIso (blowUpToBase M ∣_ V)]
    (hs : IsIso ((pullbackFunctor (blowUpToBase M ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
      (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))))
    (hw : ∀ x : X, x ∉ V →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
        (show (show X.Modules from _) ⟶ (show X.Modules from _) from
          Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
            (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
            (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))).mapPresheaf)) :
    IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
      (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))) :=
  isIso_of_isIso_restrict_of_isIso_stalk_compl
    (show (show X.Modules from _) ⟶ (show X.Modules from _) from
      Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
        (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
        (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M)))
    V
    ((Stacks.AffineProjectionFormula.isIso_openRestrictHom_iff V _).mpr
      (isIso_pullback_exceptionalTwistUnitComparison M V hs))
    hw

/-- **The canonical section of `𝒪_{X'}(E)` is invertible over the preimage of an open disjoint
from the centre.** The exceptional divisor lies over the centre
(`AlgebraicGeometry.preimage_le_compl_support_exceptionalIdeal`) and it is an effective Cartier
divisor (`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`), so
`Stacks.BlowupTwistUnit.isIso_pullback_canonicalSectionHom_of_disjoint` applies. -/
theorem isIso_pullback_canonicalSectionHom_exceptionalIdeal (V : X.Opens)
    (hV : Disjoint (V : Set X) (M.support : Set X)) :
    IsIso ((pullbackFunctor (blowUpToBase M ⁻¹ᵁ V).ι.toLRSHom.toShHom).map
      (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdeal M) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M
  have hle := AlgebraicGeometry.preimage_le_compl_support_exceptionalIdeal M hV
  refine isIso_pullback_canonicalSectionHom_of_disjoint (exceptionalIdeal M)
    (blowUpToBase M ⁻¹ᵁ V) fun y ↦ ?_
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
  exact hle y.2

/-- **The comparison map `𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible**, given the invertibility of its
stalk at each point of the centre.

Away from the centre the blowup is an isomorphism and the canonical section of `𝒪_{X'}(E)` is
invertible, so the comparison map is invertible there; the rest is the local criterion. -/
theorem isIso_twistUnitComparison_exceptionalIdeal_of_isIso_stalk
    (hw : ∀ x : X, x ∈ M.support →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
        (show (show X.Modules from _) ⟶ (show X.Modules from _) from
          Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
            (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
            (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))).mapPresheaf)) :
    IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison (blowUpToBase M)
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal M))
      (Stacks.Divisors.canonicalSectionHom (exceptionalIdeal M))) := by
  have hdisj : Disjoint ((M.support.compl : X.Opens) : Set X) ((M.support : Set X)) := by
    rw [show (((M.support.compl : X.Opens)) : Set X) = ((M.support : Set X))ᶜ from rfl]
    exact disjoint_compl_left
  refine isIso_twistUnitComparison_exceptionalIdeal M (M.support.compl : X.Opens)
    (isIso_pullback_canonicalSectionHom_exceptionalIdeal M _ hdisj) fun x hx ↦ hw x ?_
  by_contra hmem
  exact hx hmem

end Stacks.BlowupTwistUnit

end
