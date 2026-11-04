module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# Regularity of schemes smooth over a field

A scheme smooth over a field is regular: each of its points has an affine open neighbourhood
whose ring of sections is a regular ring.

## Main results

* `AlgebraicGeometry.isRegular_of_smooth_over_field`: the source of a smooth morphism to the
  spectrum of a field is a regular scheme.

## Implementation notes

A scheme over `k` is represented by an explicit morphism to `Spec k`. Smoothness is Mathlib's
`AlgebraicGeometry.Smooth` and regularity is `AlgebraicGeometry.IsRegular`. The argument is
affine-local: on an affine open the sections form a smooth algebra over `Γ(Spec k, ⊤)`, which is
a field and hence a regular ring, so the ring-theoretic statement that a smooth algebra over a
regular ring is regular applies directly.

## References

* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 056S.** A scheme smooth over a field is regular. -/
@[stacks 056S, ega "IV 17.15.2" "smooth ⇒ regular"]
public theorem isRegular_of_smooth_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    IsRegular X := by
  intro x
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  refine ⟨U, hxU, ?_⟩
  let : IsRegularRing Γ(Spec (.of k), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let φ := (f.appLE ⊤ U.1 (le_top : U.1 ≤ f ⁻¹ᵁ ⊤)).hom
  let : Algebra Γ(Spec (.of k), ⊤) Γ(X, U.1) := φ.toAlgebra
  let : Algebra.Smooth Γ(Spec (.of k), ⊤) Γ(X, U.1) :=
    (f.smooth_appLE (isAffineOpen_top _) U.2 le_top).toAlgebra
  exact Algebra.isRegularRing_of_smooth Γ(Spec (.of k), ⊤) Γ(X, U.1)

end AlgebraicGeometry

end
