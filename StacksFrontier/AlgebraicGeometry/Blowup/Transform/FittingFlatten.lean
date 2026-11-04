module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransformFitting.Rank
public import StacksFrontier.AlgebraicGeometry.StrictTransformFittingRank.Basic

/-!
# Flattening a finitely presented module by blowing up a Fitting ideal

Let `ℱ` be a finitely presented module on a scheme `X` which is finite locally free of constant
rank `r` on an open `U`. Blowing up the `r`-th Fitting ideal of `ℱ` is then `U`-admissible, and
if `U` is in addition scheme-theoretically dense the strict transform of `ℱ` along that blowup
is finite locally free of rank `r`.

## Main results

* `AlgebraicGeometry.rank_eq_zero_or_fittingIdeal_pred_eq_bot`: the Fitting ideal immediately
  below the generic rank of a module vanishes.
* `AlgebraicGeometry.disjoint_support_fittingIdeal`: the centre of the Fitting blowup avoids
  the open on which the module has constant rank, which is half of admissibility.
* `AlgebraicGeometry.isAdmissibleBlowup_fittingIdeal`: the Fitting blowup is `U`-admissible.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_strictTransform_of_dense`: the strict transform
  along the Fitting blowup is finite locally free of the generic rank.

## Implementation notes

The Fitting ideal restricts to the unit ideal on `U`, by the Fitting criterion for finite local
freeness (Stacks tag 0C3G, `AlgebraicGeometry.finiteLocallyFreeOfRank_tfae_fittingIdeal`), so
its support avoids `U`.

Admissibility needs only that, together with the Fitting ideal being of finite type (Stacks tag
0C3E, `AlgebraicGeometry.fittingIdeal_isFiniteType`), which is finite presentation of its closed
subscheme by `AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType`
(Stacks tag 01TV). Scheme-theoretic density of `U` is *not* used for it.

Local freeness of the strict transform is Stacks tag 0CZQ,
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp`, whose hypothesis
is that the module is already finite locally free of rank `r` on the complement of the support
of the Fitting ideal. That is checked with the same Fitting criterion, the vanishing of the
Fitting ideal below `r` being transported from `U` by scheme-theoretic density.

The rank hypothesis is taken in the form `SheafOfModules.IsFiniteLocallyFreeOfRank` of the
pullback along `U.ι`, which is the form the repository's Fitting-rank material is stated in.

The admissibility predicate `Stacks.Blowup.IsAdmissibleBlowup` is phrased in terms of
`Stacks.Blowup.blowUpToBase`, while the strict transform and the Fitting-rank results are phrased
in terms of `AlgebraicGeometry.blowUpToBase`; these are two distinct constructions of the blowup
of an ideal sheaf. `Stacks.Blowup.isAdmissibleBlowup_iff` says that admissibility may equally be
tested against either, and it is used below so that both statements are about one and the same
morphism, `AlgebraicGeometry.blowUpToBase (fittingIdeal ℱ r)`.

## References

* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 0C3E](https://stacks.math.columbia.edu/tag/0C3E)
* [Stacks Project, Tag 0C3G](https://stacks.math.columbia.edu/tag/0C3G)
* [Stacks Project, Tag 0CZQ](https://stacks.math.columbia.edu/tag/0CZQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.StrictTransformFittingRank (ideal_eq_bot_of_comap_eq_bot)

variable {X : Scheme.{u}} (F : X.Modules)

/-- On an open `U`, the pullback of a finite type quasi-coherent module is finite locally free of
rank `r` iff its Fitting ideals have the expected shape. -/
private theorem isFiniteLocallyFreeOfRank_pullback_iff_fittingIdeal [F.IsFiniteType]
    [F.IsQuasicoherent] (U : X.Opens) (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r ↔
    (r = 0 ∨ fittingIdeal ((Scheme.Modules.pullback U.ι).obj F) ((r : ℤ) - 1) = ⊥) ∧
      fittingIdeal ((Scheme.Modules.pullback U.ι).obj F) (r : ℤ) = ⊤ := by
  have hft : ((Scheme.Modules.pullback U.ι).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType U.ι.toLRSHom.toShHom F
  have hqc : ((Scheme.Modules.pullback U.ι).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ U.ι.toLRSHom.toShHom F
      (show F.IsQuasicoherent from inferInstance)
  exact (finiteLocallyFreeOfRank_tfae_fittingIdeal
    ((Scheme.Modules.pullback U.ι).obj F) r).out 1 2

/-- For a module which is finite locally free of constant rank `r` on a scheme-theoretically
dense open, the Fitting ideal immediately below `r` vanishes. For `r = 0` this records the
convention that the Fitting ideal at index `-1` is zero. -/
theorem rank_eq_zero_or_fittingIdeal_pred_eq_bot [F.IsFiniteType] [F.IsQuasicoherent]
    (U : X.Opens) (r : ℕ) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    r = 0 ∨ fittingIdeal F ((r : ℤ) - 1) = ⊥ := by
  have hdom : IsSchemeTheoreticallyDominant U.ι :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense U hU
  have hcrit := (isFiniteLocallyFreeOfRank_pullback_iff_fittingIdeal F U r).mp hrank
  rcases hcrit.1 with hr | hfit
  · exact Or.inl hr
  · refine Or.inr (ideal_eq_bot_of_comap_eq_bot U.ι _ ?_)
    rw [fittingIdeal_comap U.ι F ((r : ℤ) - 1)]
    exact hfit

/-- The Fitting ideal of the generic rank restricts to the unit ideal on an open where the
module is finite locally free of that rank, so its support avoids that open. -/
theorem disjoint_support_fittingIdeal [F.IsFiniteType] [F.IsQuasicoherent] (U : X.Opens)
    (r : ℕ) (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    Disjoint (U : Set X) ((fittingIdeal F (r : ℤ)).support : Set X) := by
  have hcrit := (isFiniteLocallyFreeOfRank_pullback_iff_fittingIdeal F U r).mp hrank
  have hcomap : (fittingIdeal F (r : ℤ)).comap U.ι = ⊤ := by
    rw [fittingIdeal_comap U.ι F (r : ℤ)]
    exact hcrit.2
  have hsupp : ((fittingIdeal F (r : ℤ)).comap U.ι).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff (I := (fittingIdeal F (r : ℤ)).comap U.ι)).mpr
      hcomap
  rw [Set.disjoint_left]
  intro x hxU hxI
  have hx : (⟨x, hxU⟩ : U.toScheme) ∈ ((fittingIdeal F (r : ℤ)).comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hxI
  rw [hsupp] at hx
  exact hx

/-- **Stacks Project, Tag 0ESN, part (1).** The blowup of the `r`-th Fitting ideal of a finitely
presented module is `U`-admissible, for any open `U` on which the module is finite locally free
of rank `r`. Scheme-theoretic density of `U` is not needed. -/
@[stacks 0ESN "admissible"]
theorem isAdmissibleBlowup_fittingIdeal [F.IsFinitePresentation] (U : X.Opens) (r : ℕ)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase (fittingIdeal F (r : ℤ))) := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  refine (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨fittingIdeal F (r : ℤ), ?_, disjoint_support_fittingIdeal F U r hrank,
      Iso.refl _, Category.id_comp _⟩
  rw [finitePresentation_subschemeι_iff_isFiniteType]
  exact fittingIdeal_isFiniteType F r

/-- **Stacks Project, Tag 0ESN, part (2).** The strict transform of a finitely presented module
along the blowup of its `r`-th Fitting ideal is finite locally free of rank `r`, provided the
module has rank `r` on a scheme-theoretically dense open. -/
@[stacks 0ESN "strict_transform_free"]
theorem isFiniteLocallyFreeOfRank_strictTransform_of_dense [F.IsFiniteType] [F.IsQuasicoherent]
    (U : X.Opens) (r : ℕ) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F) r := by
  refine isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp F r ?_
  set V : X.Opens := (fittingIdeal F (r : ℤ)).support.compl with hV
  refine (isFiniteLocallyFreeOfRank_pullback_iff_fittingIdeal F V r).mpr ?_
  refine ⟨?_, ?_⟩
  · rcases rank_eq_zero_or_fittingIdeal_pred_eq_bot F U r hU hrank with hr | hlow
    · exact Or.inl hr
    · refine Or.inr ?_
      rw [← fittingIdeal_comap V.ι F ((r : ℤ) - 1), hlow, Scheme.IdealSheafData.comap_bot]
  · rw [← fittingIdeal_comap V.ι F (r : ℤ)]
    refine (Scheme.IdealSheafData.support_eq_bot_iff
      (I := (fittingIdeal F (r : ℤ)).comap V.ι)).mp ?_
    rw [Scheme.IdealSheafData.support_comap]
    exact TopologicalSpace.Closeds.ext
      (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ x.property hx)

end AlgebraicGeometry

end
