module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology

/-!
# Top-degree cohomology vanishing from modules of finite presentation

Let `g : X₀ ⟶ Y₀` be a proper morphism onto an affine scheme all of whose fibres have dimension
at most `d`. If `Hⁱ(X₀, G)` vanishes for `i > d` and every module `G` of finite presentation,
then it vanishes for every quasi-coherent module: a quasi-coherent module is a filtered colimit of
modules of finite presentation ([Stacks, Tag 01PK]) and cohomology commutes with filtered
colimits ([Stacks, Tag 01FF]). This file deduces both parts of [Stacks, Tag 0E7D] from that
vanishing for modules of finite presentation, stated either on cohomology or, in the shape of
the conclusion of [Stacks, Tag 02V7], on the stalks of the higher direct images.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation_of_zero_le`:
  vanishing of cohomology for modules of finite presentation gives it for all quasi-coherent
  modules, in an arbitrary non-negative integer degree.
* `isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isCoherent`: the same on a locally
  Noetherian scheme, from the coherent modules.
* `cohomology_vanishing_of_forall_isFinitePresentation`: the cohomology of a proper morphism onto
  an affine base vanishes above the fibre dimension for every quasi-coherent module once it does
  for every module of finite presentation.
* `exists_isAffineOpen_vanishing_of_finitePresentation_vanishing` and
  `isZero_stalk_rightDerivedPlus_of_finitePresentation_vanishing`: parts (2) and (1) of
  [Stacks, Tag 0E7D] on that hypothesis.
* `cohomology_vanishing_of_forall_isFinitePresentation_stalk_vanishing`,
  `exists_isAffineOpen_vanishing_of_finitePresentation_stalk_vanishing` and
  `isZero_stalk_rightDerivedPlus_of_finitePresentation_stalk_vanishing`: the same three with the
  hypothesis the stalkwise vanishing of the higher direct images of modules of finite
  presentation, as in [Stacks, Tag 02V7].

## Implementation notes

A module of finite presentation is quasi-coherent by `isQuasicoherent_of_isFinitePresentation`,
used as a term: `AlgebraicGeometry.Scheme.Modules X` is a semireducible definition of
`SheafOfModules X.ringCatSheaf`, so instance search does not find it.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **Vanishing for modules of finite presentation gives vanishing for all quasi-coherent
modules, in an arbitrary non-negative degree.** On a quasi-compact quasi-separated scheme, if
`Hⁱ(X, G)` vanishes for an integer `i ≥ 0` and every `G` of finite presentation, then it vanishes
for every quasi-coherent `F`. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation_of_zero_le
    (X : Scheme.{u}) [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    (i : ℤ) (hi : 0 ≤ i) (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ G : X.Modules, G.IsFinitePresentation →
      IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj G)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  exact isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation X q F h

/-- On a locally Noetherian quasi-compact quasi-separated scheme, if `Hⁱ(X, G)` vanishes for an
integer `i ≥ 0` and every *coherent* `G` then it vanishes for every *quasi-coherent* `F`. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isCoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    (i : ℤ) (hi : 0 ≤ i) (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ G : X.Modules, G.IsCoherent →
      IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj G)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) :=
  isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation_of_zero_le X i hi F
    fun G hG => h G
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation G hG)

/-- **The cohomological hypothesis of [Stacks, Tag 0E7D] needs to be assumed only for modules of
finite presentation.** If a proper morphism onto an affine scheme all of whose fibres have
dimension at most `d` has vanishing cohomology above `d` for every module of *finite
presentation*, then it has vanishing cohomology above `d` for every *quasi-coherent* module. -/
theorem cohomology_vanishing_of_forall_isFinitePresentation (d : ℕ)
    (hfp : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G)) :
    ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) := by
  intro X₀ Y₀ g hg hY₀ hfib i hi F hF
  let _ : IsProper g := hg
  let _ : IsAffine Y₀ := hY₀
  let _ : F.IsQuasicoherent := hF
  have _ : CompactSpace (X₀ : Type u) := QuasiCompact.compactSpace_of_compactSpace g
  have _ : QuasiSeparatedSpace (X₀ : Type u) := quasiSeparatedSpace_of_quasiSeparated g
  exact isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation_of_zero_le
    X₀ i (by omega) F fun G hG => hfp g hg hY₀ hfib i hi G hG

/-- **[Stacks, Tag 0E7D] part (2), granted the vanishing of cohomology for modules of finite
presentation.** For `f` proper and `y` a point whose fibre has dimension at most `d`, there is
an affine open neighbourhood `V` of `y` over which `Rⁱ f_* F` vanishes for `i > d` and every
quasi-coherent `F`. -/
theorem exists_isAffineOpen_vanishing_of_finitePresentation_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hfp : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) :=
  exists_isAffineOpen_vanishing_of_cohomology_vanishing f y d hdim
    (cohomology_vanishing_of_forall_isFinitePresentation d hfp)

/-- **[Stacks, Tag 0E7D] part (1), granted the vanishing of cohomology for modules of finite
presentation.** For `f` proper and `y` a point whose fibre has dimension at most `d`, the stalk
of `Rⁱ f_* F` at `y` vanishes for `i > d` and every quasi-coherent `F`. -/
theorem isZero_stalk_rightDerivedPlus_of_finitePresentation_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hfp : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y d hdim
    (cohomology_vanishing_of_forall_isFinitePresentation d hfp) F i hi

/-- **The conclusion of [Stacks, Tag 02V7] for modules of finite presentation gives the
cohomological hypothesis of [Stacks, Tag 0E7D] for all quasi-coherent modules.** If, for every
proper morphism `g` onto an affine scheme with fibres of dimension at most `d`, the stalks of
`Rⁱ g_* G` vanish for `i > d` and every `G` of finite presentation, then `Hⁱ(X₀, F)` vanishes
for `i > d` and every quasi-coherent `F`. -/
theorem cohomology_vanishing_of_forall_isFinitePresentation_stalk_vanishing (d : ℕ)
    (hstalk : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation → ∀ t : Y₀,
        IsZero ((((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G).presheaf.stalk t)) :
    ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) :=
  cohomology_vanishing_of_forall_isFinitePresentation d
    fun g hg hY₀ hfib i hi G hG => by
      have := hg
      have := hY₀
      have : G.IsFinitePresentation := hG
      have : G.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation G
      exact isZero_cohomology_of_forall_isZero_stalk_rightDerivedPlus g i G
        (hstalk g hg hY₀ hfib i hi G hG)

/-- **[Stacks, Tag 0E7D] part (2), granted the conclusion of [Stacks, Tag 02V7] for modules of
finite presentation.** For `f` proper and `y` a point whose fibre has dimension at most `d`,
there is an affine open neighbourhood `V` of `y` over which `Rⁱ f_* F` vanishes for `i > d` and
every quasi-coherent `F`. -/
theorem exists_isAffineOpen_vanishing_of_finitePresentation_stalk_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hstalk : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation → ∀ t : Y₀,
        IsZero ((((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G).presheaf.stalk t)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) :=
  exists_isAffineOpen_vanishing_of_cohomology_vanishing f y d hdim
    (cohomology_vanishing_of_forall_isFinitePresentation_stalk_vanishing d hstalk)

/-- **[Stacks, Tag 0E7D] part (1), granted the conclusion of [Stacks, Tag 02V7] for modules of
finite presentation.** For `f` proper and `y` a point whose fibre has dimension at most `d`,
the stalk of `Rⁱ f_* F` at `y` vanishes for `i > d` and every quasi-coherent `F`. -/
theorem isZero_stalk_rightDerivedPlus_of_finitePresentation_stalk_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hstalk : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsFinitePresentation → ∀ t : Y₀,
        IsZero ((((Scheme.Modules.pushforward g).rightDerivedPlus i).obj G).presheaf.stalk t))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y d hdim
    (cohomology_vanishing_of_forall_isFinitePresentation_stalk_vanishing d hstalk) F i hi

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
