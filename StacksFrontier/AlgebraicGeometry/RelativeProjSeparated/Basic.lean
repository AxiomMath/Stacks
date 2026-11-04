module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure morphism of a relative homogeneous spectrum is separated

Let `S` be a scheme and `A` a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra.
Tag 01NQ builds the relative homogeneous spectrum `Proj_S(A) ⟶ S`, charted over the affine opens
of `S` by the absolute projective spectra of the graded rings of sections. This file proves that
that structure morphism is **separated**, and draws the consequence that every **section** of it
is a **closed immersion**.

Both statements are about an arbitrary `RelativeProjData`, so they apply in particular to the
projective bundle `P(E) = Proj_X(Sym E)` of a module on a scheme.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toOpen`: the structure morphism
  `𝒜.projOver U ⟶ U` of the chart of a graded algebra over an affine open `U` is separated.
* `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_projInclusionToOpen`: the chart
  structure morphism `Proj Γ(U, A) ⟶ U` over an affine open of the base is separated.
* `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`: the structure morphism
  `Proj_S(A) ⟶ S` is separated.
* `Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section`: a section of a
  separated morphism of schemes is a closed immersion.
* `Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_section`: every section of
  `Proj_S(A) ⟶ S` is a closed immersion.

## References

* [Stacks Project, Tag 01MC](https://stacks.math.columbia.edu/tag/01MC)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01KT](https://stacks.math.columbia.edu/tag/01KT)

## Not done here

**No tag of 0B3V is claimed.** The "closed immersion" assertion of Tag 0B3V is registered on
`Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`, for the projective
bundle of a quasi-coherent module.

Properness and quasi-compactness of `toBase` are not addressed, nor is separatedness of
`Proj_S(A)` as a scheme (which would need `S` separated as well).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjSeparated

universe u

/-! ### Separatedness of the chart structure morphism -/

section Chart

variable {S : Scheme.{u}} (𝒜 : Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S)

/-- **The structure morphism of a chart of a relative homogeneous spectrum is separated.** -/
@[ega "II 8.14.1" "special case"]
public instance isSeparated_toOpen (U : S.AffineZariskiSite) : IsSeparated (𝒜.toOpen U) := by
  rw [Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.toOpen]
  infer_instance

end Chart

section Base

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **The structure morphism of the chart over an affine open of the base is separated.** -/
@[ega "II 8.14.1" "special case"]
public instance isSeparated_projInclusionToOpen (U : S.Opens) (hU : IsAffineOpen U) :
    IsSeparated (projInclusionToOpen A U hU) :=
  isSeparated_toOpen A.toGradedAlgebra ⟨U, hU⟩

/-- **The structure morphism of a relative homogeneous spectrum is separated.** -/
@[ega "II 3.1.3", ega "II 8.14.1"]
public theorem isSeparated_toBase (P : RelativeProjData A) : IsSeparated P.toBase := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : S.affineOpens => (V : S.Opens)) (iSup_affineOpens_eq_top S) fun V => ?_
  have h₁ := (isPullback_morphismRestrict P.toBase (V : S.Opens)).flip
  have h₂ := P.chart_isPullback (V : S.Opens) V.2
  refine (MorphismProperty.arrow_mk_iso_iff (P := @IsSeparated)
    (Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _) ?_)).mp
    (isSeparated_projInclusionToOpen A (V : S.Opens) V.2)
  exact h₂.isoIsPullback_hom_snd _ _ h₁

end Base

/-! ### Sections are closed immersions -/

/-- **A section of a separated morphism of schemes is a closed immersion.** -/
@[stacks 024T "part (2)",
  ega "I 5.4.4" "special case",
  ega "I 5.4.6",
  ega "IV 16.2.3" "special case",
  sga "3 II 4.11.4" "more general",
  sga "3 VIB 5.1" "more general",
  sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
public theorem isClosedImmersion_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : IsClosedImmersion σ :=
  have : IsClosedImmersion (σ ≫ f) := hσ ▸ inferInstance
  IsClosedImmersion.of_comp σ f

/-- **Every section of the structure morphism of a relative homogeneous spectrum is a closed
immersion.** -/
@[ega "I 5.4.6" "special case", sga "3 VIB 5.6.3" "(i) ⇒ (ii), special case"]
public theorem isClosedImmersion_section {S : Scheme.{u}} {A : SheafGradedAlgebra S}
    (P : RelativeProjData A) (σ : S ⟶ P.scheme) (hσ : σ ≫ P.toBase = 𝟙 S) :
    IsClosedImmersion σ :=
  have := isSeparated_toBase A P
  isClosedImmersion_of_section P.toBase σ hσ

end Stacks.AlgebraicGeometry.RelativeProjSeparated

end
