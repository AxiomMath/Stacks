module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat

/-!
# A flattening centre with support exactly the complement of the open, for a finite type morphism

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and
quasi-separated, and let `U ⊆ S` be a quasi-compact open such that `f⁻¹(U) ⟶ U` is flat and
locally of finite presentation. Then there is a finitely presented centre `K` on `S` whose
support is exactly `S ∖ U` such that the strict transform of `X` along the blowup of `S` in `K` is
flat over that blowup.

This is the flatness half of [Stacks, Tag 081R]. No Noetherian hypothesis is needed, and `f` is
only required to be of finite type rather than of finite presentation.

## Main results

* `AlgebraicGeometry.exists_supportSet_eq_compl_flat_strictTransformToBlowUp_of_finiteType`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A flattening centre cutting out exactly `S ∖ U`, for a finite type morphism.** Let `S` be
quasi-compact and quasi-separated, let `f : X ⟶ S` be of finite type and quasi-separated and let
`U ⊆ S` be a quasi-compact open over which `f` is flat and locally of finite presentation. There
is a finitely presented centre `K` on `S` with support `S ∖ U` such that the strict transform of
`X` along the blowup of `S` in `K` is flat over that blowup. -/
theorem exists_supportSet_eq_compl_flat_strictTransformToBlowUp_of_finiteType {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hflat : Flat (f ∣_ U)) (hfp : LocallyOfFinitePresentation (f ∣_ U)) :
    ∃ K : S.IdealSheafData, FinitePresentation K.subschemeι ∧
      K.supportSet = (U : Set S)ᶜ ∧ Flat (strictTransformToBlowUp f K) := by
  have _ : LocallyOfFinitePresentation (f ∣_ U) := hfp
  obtain ⟨K, hKfp, hKsupp, -, hKflat, -⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre f U hU
      (let ⟨I, hIfp, hIdisj, _, hIflat⟩ := exists_isAdmissibleBlowup_flat_strictTransform f U hU
        (AffineChartFlatteningCentre.of_affineCase f U hU hflat hfp)
      ⟨I, hIfp, hIdisj, hIflat⟩)
  exact ⟨K, hKfp, hKsupp, hKflat⟩

end AlgebraicGeometry

end
