module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceResidual

/-!
# The residual quotient on a blown-up regular surface, and its colength bound

Let `(A, 𝔪)` be a two-dimensional regular local ring, let `b : X' ⟶ Spec A` be the blowup at the
closed point with exceptional ideal `E`, and let `J` be an ideal sheaf on `Spec A` with
`𝔪ⁿ ≤ J`. Write `b⁻¹J·𝒪_{X'} = E ^ d · Z` with `d` maximal. Then there is a *finite* set `T` of
closed points of `X'` equal to the support of `Z`, and the length over `A` of the global sections
of the subscheme `Z` cuts out is at least the sum over `T` of the colengths of the stalks of `Z`.

This is the finite-support half of clause (2) of [Stacks, Tag 0AGT] together with the second,
`≥`, inequality of its clause (3).

## Main results

* `Stacks.Blowup.Colength.exists_finset_support_residual_and_length_ge`: the two clauses
  together, for the blowup of a two-dimensional regular local ring at its closed point.

## Implementation notes

The blowup, its structure morphism and its exceptional ideal are written with their
`AlgebraicGeometry` prefixes: inside `Stacks.Blowup.Colength` the bare name `blowUp` resolves to
the different construction `Stacks.Blowup.blowUp`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.Blowup.Colength

universe u

/-- Let `A` be a two-dimensional regular local ring, `M` the ideal sheaf of its closed point and
`b : X' ⟶ Spec A` the blowup in `M`. Let `J` be an ideal sheaf with `M ^ n ≤ J`, and suppose the
inverse image `b⁻¹J·𝒪_{X'}` factors as `E ^ d · Z` with `E` the exceptional ideal and `d` maximal
among the exponents `e` with `b⁻¹J·𝒪_{X'} ≤ E ^ e`. Then the support of `Z` is a finite set of
closed points of the blowup, and the length over `A` of the global sections of the subscheme `Z`
cuts out is at least the sum over that set of the colengths of the stalks of `Z`. -/
@[stacks 0AGT "clause (2), the finite support, together with clause (3)'s second inequality, \
with the finite support no longer assumed"]
public theorem exists_finset_support_residual_and_length_ge
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (M : (Spec (CommRingCat.of A)).IdealSheafData)
    (hM : M = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (IsLocalRing.maximalIdeal A)))
    (J : (Spec (CommRingCat.of A)).IdealSheafData) (n : ℕ) (hmn : M ^ n ≤ J)
    (d : ℕ) (Z : (AlgebraicGeometry.blowUp M).IdealSheafData)
    (hfac : J.comap (AlgebraicGeometry.blowUpToBase M) =
      AlgebraicGeometry.exceptionalIdeal M ^ d * Z)
    (hmax : ∀ e : ℕ, J.comap (AlgebraicGeometry.blowUpToBase M) ≤
      AlgebraicGeometry.exceptionalIdeal M ^ e → e ≤ d) :
    letI : Algebra A Γ(Z.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Z.subschemeι ≫ AlgebraicGeometry.blowUpToBase M).appTop).hom.toAlgebra
    ∃ T : Finset (AlgebraicGeometry.blowUp M),
      (Z.support : Set (AlgebraicGeometry.blowUp M)) =
          (T : Set (AlgebraicGeometry.blowUp M)) ∧
      (∀ x ∈ T, IsClosed ({x} : Set (AlgebraicGeometry.blowUp M))) ∧
      ∑ x ∈ T, Module.length ((AlgebraicGeometry.blowUp M).presheaf.stalk x)
          (((AlgebraicGeometry.blowUp M).presheaf.stalk x) ⧸ IdealSheafData.stalk Z x) ≤
        Module.length A Γ(Z.subscheme, ⊤) := by
  classical
  let : Algebra A Γ(Z.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Z.subschemeι ≫ AlgebraicGeometry.blowUpToBase M).appTop).hom.toAlgebra
  obtain ⟨hfin, hcl⟩ :=
    AlgebraicGeometry.finite_supportSet_residual_maximalIdeal A hdim M hM J n hmn d Z hfac hmax
  have hT : (Z.support : Set (AlgebraicGeometry.blowUp M)) =
      (hfin.toFinset : Set (AlgebraicGeometry.blowUp M)) := by
    rw [hfin.coe_toFinset]
    ext x
    exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.symm
  have hT' : ∀ x ∈ hfin.toFinset, IsClosed {x} := fun x hx => hcl x (hfin.mem_toFinset.mp hx)
  exact ⟨hfin.toFinset, hT, hT', length_globalSections_ge_sum_length_stalkQuotient
    (AlgebraicGeometry.blowUpToBase M) Z hfin.toFinset hT hT'⟩

end Stacks.Blowup.Colength

end
