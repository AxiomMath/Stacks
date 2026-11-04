module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Trapping a finite set of an affine open inside a basic open

On an affine scheme a finite set of points contained in an open subset is contained in a
*principal* open subset of that open subset. This file records the relative form of that
statement: the ambient scheme is arbitrary and the affine scheme is an affine open `U` of it, so
that the function produced is a section over `U` rather than a global one.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_subset_of_finite`: for an affine open `U` of a
  scheme `X`, a finite set of points of `U` contained in an open `V` lies in `X.basicOpen r` for
  some `r : Γ(X, U)` with `X.basicOpen r ≤ V`.

## Implementation notes

The prime avoidance is not redone here. It is
`AlgebraicGeometry.Scheme.exists_basicOpen_subset_of_finite_of_isQuasiAffine` of
`StacksFrontier/AlgebraicGeometry/QuasiAffineNonvanishing/Basic.lean`, which produces a
*global* section of a quasi-affine scheme; the content of this file is the transport of that
statement from the open subscheme `U`, which is affine and hence quasi-affine, to `X`. The
transport is `AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen_topIso_inv`, which identifies the
image under `U.ι` of a basic open of `↥U` with a basic open of `X`, together with
`AlgebraicGeometry.Scheme.Opens.topIso`, which is the isomorphism `Γ(↥U, ⊤) ≅ Γ(X, U)`.

The hypothesis that the finite set lies in `U` is separate from the hypothesis that it lies in
`V`; `V` is not assumed to be contained in `U`, and the conclusion `X.basicOpen r ≤ V` is
accompanied by `X.basicOpen r ≤ U` automatically, since `r` is a section over `U`.

## References

* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A finite set of an affine open lies in a basic open of any open containing it.** Let `U` be
an affine open of a scheme `X`, let `E` be a finite set of points of `U`, and let `V` be an open
of `X` containing `E`. Then there is a section `r` over `U` whose basic open contains `E` and is
contained in `V`.

This is the relative form of the slogan of Tag 00DS. It is the prime avoidance of
`AlgebraicGeometry.Scheme.exists_basicOpen_subset_of_finite_of_isQuasiAffine`, run on the affine
— hence quasi-affine — open subscheme `↥U` and transported to `X` along `U.ι`. -/
@[sga "3 V 6.1" "more general"]
theorem IsAffineOpen.exists_basicOpen_subset_of_finite {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {E : Set X} (hE : E.Finite) (hEU : E ⊆ (U : Set X))
    (V : X.Opens) (hEV : E ⊆ (V : Set X)) :
    ∃ r : Γ(X, U), E ⊆ (X.basicOpen r : Set X) ∧ X.basicOpen r ≤ V := by
  have : IsAffine U.toScheme := hU
  have hE' : (Subtype.val ⁻¹' E : Set U).Finite := hE.preimage Subtype.val_injective.injOn
  obtain ⟨g, hg1, hg2⟩ := U.toScheme.exists_basicOpen_subset_of_finite_of_isQuasiAffine
    hE' (U.ι ⁻¹ᵁ V) (fun x hx => hEV hx)
  have hb : U.ι ''ᵁ U.toScheme.basicOpen g = X.basicOpen (U.topIso.hom g) := by
    rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv (U := U), ← CommRingCat.comp_apply,
      Iso.hom_inv_id, CommRingCat.id_apply]
  refine ⟨U.topIso.hom g, fun e he => ?_, ?_⟩
  · rw [← hb]
    exact ⟨⟨e, hEU he⟩, hg1 he, rfl⟩
  · rw [← hb]
    rintro _ ⟨y, hy, rfl⟩
    exact hg2 hy

end AlgebraicGeometry

end
