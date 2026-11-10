module

public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionEnlargement
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing

/-!
# The first limit reduction of Tag 0E7D: the morphism may be assumed of finite presentation

The proof of [Stacks, Tag 0E7D] bounds the cohomology of a quasi-coherent module on a scheme
proper over an affine base by two reductions. This file performs the first of them.

The source writes `X = lim Xᵢ` as a cofiltered limit of schemes proper and of finite presentation
over `Y` with every transition morphism and every projection `X ⟶ Xᵢ` a closed immersion
([Stacks, Tag 09ZR]), picks an index at which the fibres are still of dimension at most `d`
([Stacks, Tag 05M5]) and transports the cohomology up the projection, which is a closed immersion
and so affine ([Stacks, Tags 01XC] and [01F6] for the higher direct images, or [Stacks, Tag 089W]
directly for the absolute cohomology over an affine base).

Here the whole system is not needed. The single-stage form of [Stacks, Tag 09ZR],
`AlgebraicGeometry.exists_isClosedImmersion_isProper_finitePresentation`, factors `g` as a closed
immersion `ι : X ⟶ W` followed by a morphism `h : W ⟶ Y` proper and of finite presentation; and
[Stacks, Tag 05M6], `AlgebraicGeometry.exists_finitePresentation_closedImmersion_of_forall_`
`topologicalKrullDim_fiber_le`, shrinks the closed subscheme `W ⊇ X` back to a closed subscheme
`Z` with `X ⊆ Z ⊆ W` whose closed immersion `j : Z ⟶ W` is of finite presentation and whose
fibres over `Y` still have dimension at most `d` — which is exactly the index [Stacks, Tag 05M5]
is invoked for, 05M6 being the statement that reduces to 05M5 inside a fixed ambient scheme. So
`j ≫ h : Z ⟶ Y` is proper, of finite presentation, with fibres of dimension at most `d`, and
`X ⟶ Z` is a closed immersion.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.cohomology_vanishing_of_forall_finitePresentation`:
  **the reduction.** If the cohomology of every quasi-coherent module vanishes above `d` for
  every morphism proper *and of finite presentation* onto an affine base with fibres of dimension
  at most `d`, then it does so for every *proper* morphism onto an affine base with fibres of
  dimension at most `d`.

## What this does and does not give

The hypothesis of `cohomology_vanishing_of_forall_finitePresentation` is strictly weaker than
its conclusion — it quantifies over a subclass of the morphisms the conclusion quantifies over —
so this is a reduction and not a restatement. It is not a registration of any tag and carries no
attribute: it is one step of the proof of [Stacks, Tag 0E7D], and the tag's statement is the
vanishing itself.

The transport along the closed immersion is
`isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom` of `BaseChangeVanishing.lean`,
which is [Stacks, Tag 089W] read on vanishing; nothing of that step is rebuilt here.

What remains of [Stacks, Tag 0E7D] after this file is the second reduction, from an arbitrary affine
base to an affine *Noetherian* one, where the Noetherian case is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_of_isLocallyNoetherian_affine_base`
of `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/ProperFibreDimensionVanishing.lean`. Its
two geometric inputs are available:
`AlgebraicGeometry.exists_isProper_finitePresentation_baseChange_of_isAffine` of
`../ProperLimitStage/SeparatedModel.lean` produces the model over an affine Noetherian scheme of
finite type over the integers ([Stacks, Tags 01ZM] part (1), [01ZQ] and [081F]), and
`AlgebraicGeometry.exists_relativeDimensionLE_baseChangeMap_of_isLimit` of
`../Limits/DescendingMorphisms/RelativeDimension.lean` descends the fibre-dimension bound to a
stage ([Stacks, Tag 05M5] again). What is missing is only their composition: the model theorem
does not carry the fibre-dimension bound, and joining the two asks for the dimension bound on the
base change to the limit to be read off the bound on `g` across the isomorphism
`X ≅ Xⱼ ×_{Tⱼ} Y`, with the slice-indexed base-change system of
`AlgebraicGeometry.baseChangeDiagram` in between.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 05M6](https://stacks.math.columbia.edu/tag/05M6)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-- **The first limit reduction in the proof of [Stacks, Tag 0E7D]: the morphism may be assumed
of finite presentation.** Suppose that for every morphism `g₀ : X₀ ⟶ Y₀` which is proper *and of
finite presentation* onto an affine scheme, all of whose fibres have dimension at most `d`, the
cohomology of every quasi-coherent module on `X₀` vanishes above degree `d`. Then the same holds
for every *proper* `g : X ⟶ Y` onto an affine scheme with fibres of dimension at most `d`.

The single-stage form of [Stacks, Tag 09ZR] factors `g` as a closed immersion `ι : X ⟶ W`
followed by `h : W ⟶ Y` proper and of finite presentation, and [Stacks, Tag 05M6] replaces `W` by
a closed subscheme `j : Z ⟶ W` of finite presentation which still contains `X` and whose fibres
over `Y` still have dimension at most `d`. Then `j ≫ h` is proper and of finite presentation with
fibres of dimension at most `d`, the hypothesis applies to it at the direct image of `ℱ` along the
closed immersion `k : X ⟶ Z`, and
`isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom` — [Stacks, Tag 089W] read on
vanishing — brings the vanishing back to `X`. -/
theorem cohomology_vanishing_of_forall_finitePresentation {d : ℕ}
    (hfp : ∀ {X₀ Y₀ : Scheme.{u}} (g₀ : X₀ ⟶ Y₀), IsProper g₀ → FinitePresentation g₀ →
      IsAffine Y₀ → (∀ s : Y₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [IsAffine Y]
    (hdim : ∀ s : Y, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : (d : ℤ) < i) (F : X.Modules) [F.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨W, h, ι, hιcl, hfac, hprop, hfpres⟩ :=
    _root_.AlgebraicGeometry.exists_isClosedImmersion_isProper_finitePresentation g
  have _ : IsClosedImmersion ι := hιcl
  have _ : IsProper h := hprop
  have hdim' : ∀ s : Y, topologicalKrullDim ((ι ≫ h).fiber s) ≤ (d : WithBot ℕ∞) := by
    rw [hfac]
    exact hdim
  obtain ⟨Z, j, k, hjcl, hkcl, -, hjfp, hZdim⟩ :=
    exists_finitePresentation_closedImmersion_of_forall_topologicalKrullDim_fiber_le
      h hfpres ι d hdim'
  have _ : IsClosedImmersion j := hjcl
  have _ : IsClosedImmersion k := hkcl
  obtain ⟨_, _, _⟩ := hjfp
  obtain ⟨_, _, _⟩ := hfpres
  have hcomp : FinitePresentation (j ≫ h) := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨n, hin⟩ : ∃ n : ℕ, i = (n : ℤ) :=
    ⟨i.toNat, by omega⟩
  exact isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom k F hin
    (hfp (j ≫ h) inferInstance hcomp inferInstance hZdim i hi _
      (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom k F inferInstance))

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
