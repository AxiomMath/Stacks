module

public import StacksFrontier.AlgebraicGeometry.Flatness.FittingStratification.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.FittingStratification.RankStratum
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.FinitePresentationOpenImmersion

/-!
# Finite presentation of the Fitting rank strata

Let `F` be a finitely presented sheaf of modules on a scheme `S` and let `r` be a natural
number.  The rank `r` Fitting stratum of `F` — the part of the Fitting closed subscheme of index
`r - 1` lying over the open complement of the Fitting closed subscheme of index `r` — is then of
finite presentation over `S`.

## Main results

* `AlgebraicGeometry.finitePresentation_fittingRankStratum`: the structural morphism of the
  rank `r` Fitting stratum of a finitely presented module is of finite presentation.

## Implementation notes

The structural morphism of the stratum is the inclusion of an open subscheme of the Fitting
closed subscheme `Z` of index `r - 1`, followed by the closed immersion of `Z` into `S`.  Finite
presentation of the second factor is `AlgebraicGeometry.fittingClosedSubscheme_finitePresentation`
at a nonnegative index, and is trivial at a negative index because there the subscheme is the
whole of `S`.  The first factor is an open immersion, so by
`AlgebraicGeometry.finitePresentation_iff_quasiCompact_of_isOpenImmersion` only quasi-compactness
is at stake; that open subscheme of `Z` is a base change of the Fitting generator open of index
`r`, whose quasi-compactness is part of
`AlgebraicGeometry.fittingGeneratorOpen_finitePresentation`.  Finite presentation is stable under
composition, which here is applied through the three instances it consists of.

Finite type and quasi-coherence of `F` are applied by hand rather than found by instance
synthesis: both follow from finite presentation, but the universe parameter of
`SheafOfModules.IsFinitePresentation` is not determined by the goal, so the Mathlib instances
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` and
`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation` appear as explicit arguments in the
statement, which therefore assumes finite presentation alone.

## References

* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The Fitting closed subscheme of a finitely presented module is of finite presentation over
the base at every integer index: at a nonnegative index this is
`AlgebraicGeometry.fittingClosedSubscheme_finitePresentation`, and at a negative index the
subscheme is the whole base scheme. -/
private theorem fittingClosedSubscheme_int_finitePresentation {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] [F.IsFinitePresentation] (r : ℤ) :
    FinitePresentation (fittingClosedSubscheme F r).hom := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [fittingClosedSubscheme_neg F r hr]
    change FinitePresentation (𝟙 S)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    exact fittingClosedSubscheme_finitePresentation F n

/-- Finite presentation of the rank `r` Fitting stratum, with finite type and quasi-coherence of
`F` taken as hypotheses rather than derived from finite presentation.  The structural morphism of
the stratum is the inclusion of an open subscheme of the Fitting closed subscheme of index
`r - 1`, followed by the closed immersion of that subscheme into the base; the open subscheme is
a base change of the Fitting generator open of index `r`, so it is quasi-compact, hence of finite
presentation, and finite presentation is stable under composition. -/
private theorem finitePresentation_fittingRankStratum_aux {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] [F.IsFinitePresentation] (r : ℕ) :
    FinitePresentation (fittingRankStratum F r).hom := by
  have hZ : FinitePresentation (fittingClosedSubscheme F ((r : ℤ) - 1)).hom :=
    fittingClosedSubscheme_int_finitePresentation F ((r : ℤ) - 1)
  have : QuasiCompact (fittingGeneratorOpen F r).ι :=
    (fittingGeneratorOpen_finitePresentation F r).2.1
  have hUqc : QuasiCompact
      ((fittingClosedSubscheme F ((r : ℤ) - 1)).hom ⁻¹ᵁ fittingGeneratorOpen F r).ι := by
    rw [← pullbackRestrictIsoRestrict_inv_fst (fittingClosedSubscheme F ((r : ℤ) - 1)).hom
      (fittingGeneratorOpen F r)]
    infer_instance
  have hU : FinitePresentation
      ((fittingClosedSubscheme F ((r : ℤ) - 1)).hom ⁻¹ᵁ fittingGeneratorOpen F r).ι :=
    (finitePresentation_iff_quasiCompact_of_isOpenImmersion _).2 hUqc
  have : LocallyOfFinitePresentation
      ((fittingClosedSubscheme F ((r : ℤ) - 1)).hom ⁻¹ᵁ fittingGeneratorOpen F r).ι := hU.1
  have : QuasiSeparated
      ((fittingClosedSubscheme F ((r : ℤ) - 1)).hom ⁻¹ᵁ fittingGeneratorOpen F r).ι := hU.2.2
  have : LocallyOfFinitePresentation (fittingClosedSubscheme F ((r : ℤ) - 1)).hom := hZ.1
  have : QuasiCompact (fittingClosedSubscheme F ((r : ℤ) - 1)).hom := hZ.2.1
  have : QuasiSeparated (fittingClosedSubscheme F ((r : ℤ) - 1)).hom := hZ.2.2
  dsimp [fittingRankStratum]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 05P8.** The structural morphism of the rank `r` Fitting stratum of a
finitely presented sheaf of modules `F` on `S` — the locally closed subscheme of `S` over which
`F` pulls back to a module finite locally free of rank `r` — is of finite presentation. -/
@[stacks 05P8 "finite presentation of the morphism Z_(r-1) minus Z_r to S"]
public theorem finitePresentation_fittingRankStratum {S : Scheme.{u}} (F : S.Modules)
    [F.IsFinitePresentation] (r : ℕ) :
    FinitePresentation
      (@fittingRankStratum S F (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
        (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) r).hom :=
  @finitePresentation_fittingRankStratum_aux S F
    (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
    (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)
    ‹F.IsFinitePresentation› r

end AlgebraicGeometry

end
