module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.UnionAffine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated

/-!
# Approximation by perfect complexes on a quasi-compact quasi-separated scheme

Approximation by perfect complexes holds on every quasi-compact and quasi-separated scheme.
This is [Stacks, Tag 08ES].

## Main results

* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_qcqs`:
  **[Stacks, Tag 08ES]**, in the encoding
  `AlgebraicGeometry.PerfectApproximation.ApproximationByPerfectComplexes` of the property of
  [Stacks, Tag 08EN]. The other encoding of the same tag is the imported
  `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes`.

## Implementation notes

This is the induction principle of [Stacks, Tag 08DR],
`Stacks.AlgebraicGeometry.CompactOpenInduction.top`, run on the property "approximation by
perfect complexes holds on the open subscheme". Its affine case is [Stacks, Tag 08EQ] in the
form `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_isAffine` and
its union step is [Stacks, Tag 08ER].

Both are applied inside the open subscheme `U ⊔ V`, not inside `X`: the union step produces the
property for the *scheme* `(U ⊔ V).toScheme`, whose two opens are the inverse images of `U` and
of `V`. Comparing the property on the inverse image of `U` with the property on `U` itself, and
the property on the inverse image of `⊤` with the property on `X`, is what
`AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_of_iso` is for; the two
isomorphisms are `AlgebraicGeometry.Scheme.Opens.isoOfLE` and
`AlgebraicGeometry.Scheme.topIso`.

## References

* [Stacks Project, Tag 08ES](https://stacks.math.columbia.edu/tag/08ES)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08ER](https://stacks.math.columbia.edu/tag/08ER)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.PerfectApproximation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08ES].** Approximation by perfect complexes holds on every quasi-compact and
quasi-separated scheme.

The induction principle of [Stacks, Tag 08DR] applied to the property that approximation holds
on an open subscheme: the affine case is [Stacks, Tag 08EQ] and the union step is
[Stacks, Tag 08ER]. -/
@[stacks 08ES "approximation by perfect complexes on a quasi-compact quasi-separated scheme; \
nothing is carried, and the statement is at the standard derived category of the sheaves of \
modules of the scheme, the model the whole chapter is written at"]
theorem approximationByPerfectComplexes_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : ApproximationByPerfectComplexes X := by
  have htop : ApproximationByPerfectComplexes ((⊤ : X.Opens) : Scheme.{u}) :=
    Stacks.AlgebraicGeometry.CompactOpenInduction.top
      (P := fun W : X.Opens => ApproximationByPerfectComplexes (W : Scheme.{u}))
      (fun W hW => by
        let : IsAffine (W : Scheme.{u}) := hW
        exact approximationByPerfectComplexes_of_isAffine _)
      (fun U V hUc hVaff hU _ _ => by
        have hUle : U ≤ U ⊔ V := le_sup_left
        have hUle : U ≤ U ⊔ V := le_sup_left
        have hpre : ∀ S : Set X, S ⊆ (U ⊔ V : X.Opens) → IsCompact S →
            IsCompact (⇑(U ⊔ V : X.Opens).ι.base ⁻¹' S) := fun S hS hSc =>
          ((U ⊔ V : X.Opens).ι.isOpenEmbedding.isEmbedding.isInducing.isCompact_preimage_iff
            (by rwa [Scheme.Opens.range_ι])).2 hSc
        refine approximationByPerfectComplexes_sup_affine ((U ⊔ V : X.Opens) : Scheme.{u})
          ((U ⊔ V : X.Opens).ι ⁻¹ᵁ U) ((U ⊔ V : X.Opens).ι ⁻¹ᵁ V)
          (hVaff.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact
            le_sup_right)) ?_ ?_ ?_ ?_
        · ext x
          refine ⟨fun _ => trivial, fun _ => ?_⟩
          change x.1 ∈ U ∨ x.1 ∈ V
          simpa using x.property
        · exact hpre _ hUle hUc
        · exact hpre _ (fun _ hx => hUle hx.1)
            (QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X) U.2 hUc V.2
              hVaff.isCompact)
        · exact approximationByPerfectComplexes_of_iso (Scheme.Opens.isoOfLE hUle) hU)
  exact approximationByPerfectComplexes_of_iso X.topIso.symm htop

end AlgebraicGeometry.PerfectApproximation

end
