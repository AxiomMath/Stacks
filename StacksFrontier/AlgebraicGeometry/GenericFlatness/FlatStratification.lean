module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# The generic flatness stratification of a morphism of finite presentation

Stacks 0H3Z says that a morphism of finite presentation `f : X ⟶ S` between quasi-compact and
quasi-separated schemes admits a stratification of its base: there are closed subschemes
`S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by a finite type ideal sheaf, with `S₀ ⊆ S` a
thickening, such that `X ×_S (S_i ∖ S_{i+1})` is flat over the locally closed stratum
`S_i ∖ S_{i+1}`.

This file writes that conclusion down. The statement is *not* proved here, so no
`@[stacks 0H3Z]` attribute is attached: the proof is
`AlgebraicGeometry.HasFlatStratification.of_finitePresentation` in
`StacksFrontier.AlgebraicGeometry.GenericFlatness.MorphismFlatStratificationQcqs`, which needs the
whole quasi-compact quasi-separated case of Stacks 0ASY and therefore cannot live this low in
the import graph. `AlgebraicGeometry.FinitePresentationHasFlatStratification` is stated here as a
`Prop`-valued definition, in the style of
`AlgebraicGeometry.StandardVCoveringHasPHRefinement`, so that consumers can carry it as an
explicit hypothesis rather than import its proof.

## Main definitions

* `AlgebraicGeometry.HasFlatStratification` is the conclusion of Stacks 0H3Z for a single
  morphism.
* `AlgebraicGeometry.FinitePresentationHasFlatStratification` is the statement of Stacks 0H3Z.

## Main results

* `AlgebraicGeometry.HasFlatStratification.of_flat`: a flat morphism has a flat stratification,
  with the two-step stratification `S ⊇ S ⊇ ∅`. This is the degenerate case of the statement; it
  is here because it exercises every clause of the conclusion against a real witness, and so
  shows the conclusion is not vacuous as written.

## Implementation notes

A closed subscheme of `S` is recorded by its quasi-coherent ideal sheaf, an
`AlgebraicGeometry.Scheme.IdealSheafData`, so the descending chain of closed subschemes is an
*ascending* chain `I : Fin (t + 1) → S.IdealSheafData` of ideal sheaves, and `S_t = ∅` is
`I (Fin.last t) = ⊤`. The condition that `S_i → S` be defined by a finite type ideal sheaf is
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, and the condition that `S₀ ⊆ S` be a
thickening is `Stacks.Thickenings.IsThickening` of the closed immersion `(I 0).subschemeι`; by
`AlgebraicGeometry.Scheme.IdealSheafData.isThickening_subschemeι_iff` the latter says exactly
that `I 0` is supported on all of `S`, which is how the Stacks proof produces it (it takes
`S₀ = S_red`, whose ideal sheaf is the nilradical, see
`AlgebraicGeometry.Scheme.isThickening_reductionι`).

The locally closed stratum `S_i ∖ S_{i+1}` is the open subscheme of `S_i` obtained by removing
the support of `I (i+1)`: it is `(I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl`, an
`AlgebraicGeometry.Scheme.Opens` of `(I i.castSucc).subscheme`. Its structure morphism to `S` is
the composite of the open immersion with the closed immersion, and the flatness asserted is
flatness of `pullback.snd` along that composite, which is Mathlib's morphism property
`AlgebraicGeometry.Flat`.

## Where the statement is proved

Stacks 0H3Z is the case `ℱ = 𝒪_X` of Stacks 0ASY, `AlgebraicGeometry.exists_flat_stratification`,
which is proved in full quasi-compact quasi-separated generality. The Noetherian case of the
conclusion above is `AlgebraicGeometry.HasFlatStratification.of_isNoetherian`, and the general
case — the tag — is `AlgebraicGeometry.HasFlatStratification.of_finitePresentation`, with
`AlgebraicGeometry.finitePresentationHasFlatStratification` for the `Prop`-valued form defined
below.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The conclusion of Stacks 0H3Z for one morphism `f : X ⟶ S`.** There is a finite descending
chain of closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base, recorded by the ascending
chain `I` of their ideal sheaves, such that

* each `S_i → S` is defined by a finite type ideal sheaf,
* `S₀ ⊆ S` is a thickening, and
* the base change `X ×_S (S_i ∖ S_{i+1})` is flat over the stratum `S_i ∖ S_{i+1}`,

where `S_i ∖ S_{i+1}` is the open subscheme of `S_i` on the complement of the support of
`I (i+1)`. -/
def HasFlatStratification {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
    Stacks.Thickenings.IsThickening (I 0).subschemeι ∧
    (∀ i, (I i).IsFiniteType) ∧
    (∀ i : Fin t, I i.castSucc ≤ I i.succ) ∧
    I (Fin.last t) = ⊤ ∧
    ∀ i : Fin t,
      let Z := I i.castSucc
      let U : Z.subscheme.Opens := Z.subschemeι ⁻¹ᵁ (I i.succ).support.compl
      Flat (pullback.snd f (U.ι ≫ Z.subschemeι))

/-- **The statement of Stacks 0H3Z.** Every morphism of finite presentation between quasi-compact
and quasi-separated schemes has a flat stratification of its base.

This is proved by `AlgebraicGeometry.finitePresentationHasFlatStratification`, which lives higher
in the import graph; it is stated here as a `Prop` so that it can be carried as an explicit
hypothesis instead, as is done with `AlgebraicGeometry.StandardVCoveringHasPHRefinement` for
Stacks 0ETR. -/
def FinitePresentationHasFlatStratification : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S], FinitePresentation f → HasFlatStratification f

/-- A flat morphism has a flat stratification: take `t = 1`, so that `S₀ = S` is cut out by the
zero ideal sheaf and `S₁ = ∅` by the unit ideal sheaf. The only stratum is then `S` itself, and
flatness of the base change is flatness of `f` together with stability of flatness under base
change.

No finite presentation and no quasi-compactness is needed for this case. -/
theorem HasFlatStratification.of_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] :
    HasFlatStratification f := by
  refine ⟨1, ![⊥, ⊤],
    (Scheme.IdealSheafData.isThickening_subschemeι_iff (⊥ : S.IdealSheafData)).mpr
      Scheme.IdealSheafData.support_bot, ?_, ?_, rfl, ?_⟩
  · intro i
    fin_cases i
    · exact fun _ ↦ Submodule.fg_bot
    · exact fun _ ↦ Ideal.fg_top _
  · intro i
    fin_cases i
    simp
  · intro i
    exact MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback f _) ‹Flat f›

end AlgebraicGeometry

end
