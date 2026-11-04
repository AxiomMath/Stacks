module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap

/-!
# A section of the projective bundle meets the preimage of an open in that open

A section `σ` of the projection `π : 𝐏(ℰ) ⟶ X` satisfies `σ ≫ π = 𝟙 X`, so for every open `U`
of `X`

  `σ ⁻¹ᵁ (π ⁻¹ᵁ U) = U`.

**This is what lets a statement about `σ` be localised on the base.** The conormal sheaf of `σ`
is a sheaf on `X`, and the locality criterion
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict`
restricts it to an open `U` of `X`; but the tools that compute it — the conormal locality
statement `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe`, and the chart of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTransport` — are indexed by opens of
the *bundle*, and restrict along `σ ⁻¹ᵁ V` for `V` an open of `𝐏(ℰ)`. Taking `V = π ⁻¹ᵁ U` makes
the two agree, and this file is that one equality.

## Main results

* `Stacks.ProjectiveBundleConormal.preimage_toBase_preimage`: **`σ ⁻¹ᵁ (π ⁻¹ᵁ U) = U`** for a
  section `σ` of the projective bundle.
* `Stacks.ProjectiveBundleConormal.mem_toBase_preimage_iff`: the pointwise form, which is what a
  membership hypothesis is discharged by.

## Implementation notes

Nothing here is specific to the projective bundle: the statement is `Scheme.Hom.preimage_comp`
followed by the hypothesis `σ ≫ π = 𝟙 X`, so it is proved for an arbitrary retraction and the
bundle case is the instantiation. Stating it for the bundle as well means a consumer does not
have to produce the general form's arguments.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

/-! ### For an arbitrary retraction -/

/-- **A section meets the preimage of an open in that open.** If `g ≫ f = 𝟙 X` then
`g ⁻¹ᵁ (f ⁻¹ᵁ U) = U`: the two preimages compose to the preimage along the identity. -/
theorem preimage_preimage_of_comp_eq_id {X Y : Scheme.{u}} {g : X ⟶ Y} {f : Y ⟶ X}
    (h : g ≫ f = 𝟙 X) (U : X.Opens) : g ⁻¹ᵁ (f ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.id_preimage]

/-- The pointwise form of `Stacks.ProjectiveBundleConormal.preimage_preimage_of_comp_eq_id`. -/
theorem mem_preimage_preimage_iff_of_comp_eq_id {X Y : Scheme.{u}} {g : X ⟶ Y} {f : Y ⟶ X}
    (h : g ≫ f = 𝟙 X) (U : X.Opens) (x : X) : x ∈ g ⁻¹ᵁ (f ⁻¹ᵁ U) ↔ x ∈ U := by
  rw [preimage_preimage_of_comp_eq_id h]

/-! ### For a section of the projective bundle -/

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)

include hσ in
/-- **`σ ⁻¹ᵁ (π ⁻¹ᵁ U) = U` for a section of the projective bundle.** The open of `𝐏(ℰ)` over
which a chart computation is carried out is `π ⁻¹ᵁ U`; this says the section sees exactly `U`
there, so a sheaf on `X` restricted along `σ ⁻¹ᵁ (π ⁻¹ᵁ U)` is restricted along `U`. -/
theorem preimage_toBase_preimage (U : X.Opens) :
    σ ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ U) = U :=
  preimage_preimage_of_comp_eq_id hσ U

include hσ in
/-- The pointwise form of `Stacks.ProjectiveBundleConormal.preimage_toBase_preimage`. -/
theorem mem_toBase_preimage_iff (U : X.Opens) (x : X) :
    x ∈ σ ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ U) ↔ x ∈ U :=
  mem_preimage_preimage_iff_of_comp_eq_id hσ U x

end Stacks.ProjectiveBundleConormal

end
