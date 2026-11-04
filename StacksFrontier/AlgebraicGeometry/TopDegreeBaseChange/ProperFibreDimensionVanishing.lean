module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimension
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.FibreDimensionModel
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FinitePresentationMorphismSuffices
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FinitePresentationSuffices
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OneDimensionalFibres
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology

/-!
# Tag 0E7D: higher direct images of a proper morphism vanish above the fibre dimension

[Stacks, Tag 0E7D] fixes a proper morphism `f : X ⟶ Y` and a point `y ∈ Y` with
`dim(X_y) = d`, and asserts

1. `(Rⁱ f_* ℱ)_y = 0` for every quasi-coherent `ℱ` on `X` and every `i > d`;
2. there is an affine open neighbourhood `V` of `y` such that `f⁻¹(V) ⟶ V` and `d` satisfy the
   assumptions and conclusions of [Stacks, Tag 0EX3].

This file proves the cohomological input of both parts, with no hypothesis beyond the tag's own.

The proof is the source's. By [Stacks, Tag 02FZ] and the closedness of `f`, `y` has an affine
neighbourhood over which every fibre has dimension at most `d`; this, and the passage from the
cohomology over an affine base to the higher direct images and their stalks, is
`exists_isAffineOpen_vanishing_of_cohomology_vanishing` and
`isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` of `AffineBaseCohomology.lean`. What is
left is the vanishing of `Hᵖ(X, ℱ)` for `p > d` when `X` is proper over an affine `Y` with all
fibres of dimension at most `d`, and the source obtains it by three reductions, all of which are
assembled here:

* the morphism may be assumed of finite presentation ([Stacks, Tags 09ZR, 05M5, 089W]) —
  `cohomology_vanishing_of_forall_finitePresentation` of
  `FinitePresentationMorphismSuffices.lean`;
* the affine base may then be assumed Noetherian ([Stacks, Tags 01ZM, 081F, 05M5, 089W]) —
  `cohomology_vanishing_of_forall_isLocallyNoetherian_base` below, whose geometric input is
  `AlgebraicGeometry.exists_isProper_finitePresentation_relativeDimensionLE_baseChange_of_isAffine`
  of `../ProperLimitStage/FibreDimensionModel.lean`;
* over an affine Noetherian base the module may be assumed coherent ([Stacks, Tags 01PK, 01FF]),
  where the vanishing is [Stacks, Tag 02V7] —
  `isZero_cohomology_of_isLocallyNoetherian_affine_base`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_cohomology_of_isLocallyNoetherian_affine_base`: the Noetherian case.
* `cohomology_vanishing_of_forall_isLocallyNoetherian_base`: the reduction to it.
* `isZero_cohomology_of_affine_base`: `Hⁱ(X, ℱ) = 0` for `i > d`, `X` proper over an arbitrary
  affine base with every fibre of dimension at most `d`.
* `cohomologyVanishesAboveOne`: that statement at `d = 1`, as a term of the proposition
  `CohomologyVanishesAboveOne` which the statements of `OneDimensionalFibres.lean` and
  `FibreDimensionOneVanishing.lean` take as a hypothesis.
* `isZero_rightDerivedPlus_pushforward_of_forall_fiber_dim_le`: `Rⁱ f_* ℱ = 0` for `i > d`, `f`
  proper over an arbitrary base with every fibre of dimension at most `d`.

The registered statements of [Stacks, Tag 0E7D] are
`isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le` and
`exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le`
(`FibreDimensionStalkVanishing.lean`), and the full part (2), with conclusion (c) of
[Stacks, Tag 0EX3], is
`exists_isAffineOpen_topDegreeBaseChange_full_of_topologicalKrullDim_fiber_le`.

## Implementation notes

The fibre dimension is bounded above, `dim(X_y) ≤ d`, as everywhere in this directory: the
source's `dim(X_y) = d` is the special case, and its proof uses only the bound.

`CategoryTheory.HasDerivedCategory.standard` is given a raised priority, as in
`HigherDirectImageFibreDimension/GeneralDimension.lean`, so that the `rightDerivedPlus` below
lives in the derived-category universe the rest of this directory uses.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-- **The vanishing over an affine Noetherian base.** For a proper morphism `g : X ⟶ Y` onto an
affine locally Noetherian scheme all of whose fibres have dimension at most `d`, the cohomology
`Hⁱ(X, ℱ)` of a quasi-coherent module vanishes for every `i > d`.

The source of the morphism is locally Noetherian because `g` is of finite type, so
`isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isCoherent` reduces the statement to
coherent modules — the last paragraph of the proof of [Stacks, Tag 0E7D], [Stacks, Tags 01PK]
and [01FF]. For a coherent module the vanishing is [Stacks, Tag 02V7],
`Stacks.AlgebraicGeometry.FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le`,
read over the affine base by [Stacks, Tags 01XJ] and [01XK]. -/
theorem isZero_cohomology_of_isLocallyNoetherian_affine_base {d : ℕ}
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [IsAffine Y] [IsLocallyNoetherian Y]
    (hdim : ∀ y : Y, topologicalKrullDim (g.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have _ : CompactSpace (X : Type u) := QuasiCompact.compactSpace_of_compactSpace g
  have _ : QuasiSeparatedSpace (X : Type u) := quasiSeparatedSpace_of_quasiSeparated g
  refine isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isCoherent X i (by omega) F
    fun G hG => ?_
  have _ : G.IsCoherent := hG
  have _ : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  exact isZero_cohomology_of_forall_isZero_stalk_rightDerivedPlus g i G fun y =>
    Stacks.AlgebraicGeometry.FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le
      g y d (hdim y) G i hi

/-- **The second limit reduction in the proof of [Stacks, Tag 0E7D]: the affine base may be
assumed locally Noetherian.** Suppose that for every proper morphism `g₀ : X₀ ⟶ Y₀` onto an
affine *locally Noetherian* scheme, all of whose fibres have dimension at most `d`, the
cohomology of every quasi-coherent module on `X₀` vanishes above degree `d`. Then the same holds
for every proper `g : X ⟶ Y` onto an arbitrary affine scheme with fibres of dimension at most
`d`.

`cohomology_vanishing_of_forall_finitePresentation` — the first limit reduction — lets `g` be
assumed of finite presentation as well, and
`AlgebraicGeometry.exists_isProper_finitePresentation_relativeDimensionLE_baseChange_of_isAffine`
then writes such a `g` as the base change of a proper morphism `X_T ⟶ T` of finite presentation,
with `T` affine Noetherian and with the fibres of `X_T ⟶ T` still of dimension at most `d`. The
projection `X ⟶ X_T` is the base change of `q : Y ⟶ T` along `X_T ⟶ T`, a morphism of affine
schemes, so it is affine and
`isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom` — [Stacks, Tag 089W] read on
vanishing — brings the vanishing over `T` back to `X`. -/
theorem cohomology_vanishing_of_forall_isLocallyNoetherian_base {d : ℕ}
    (hN : ∀ {X₀ Y₀ : Scheme.{u}} (g₀ : X₀ ⟶ Y₀), IsProper g₀ → IsAffine Y₀ →
      IsLocallyNoetherian Y₀ → (∀ s : Y₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X₀).rightDerivedPlus i).obj G))
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [IsAffine Y]
    (hdim : ∀ s : Y, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : (d : ℤ) < i) (F : X.Modules) [F.IsQuasicoherent] :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  refine cohomology_vanishing_of_forall_finitePresentation
    (fun {X₀ Y₀} g₀ hprop hfp haff hdim₀ n hn G hG => ?_) g hdim i hi F
  have _ : IsProper g₀ := hprop
  have _ : IsAffine Y₀ := haff
  have _ : IsProper (Over.mk g₀).hom := hprop
  obtain ⟨T, q, XT, hT, hTN, -, -, hpropT, hdimT, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_relativeDimensionLE_baseChange_of_isAffine
      Y₀ (Over.mk g₀) hfp d hdim₀
  have _ : IsAffine T := hT
  have _ : IsNoetherian T := hTN
  have _ : IsIso e.hom.left := (Over.forget Y₀).map_isIso e.hom
  have _ : IsAffineHom (pullback.fst XT.hom q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback XT.hom q).flip inferInstance
  have _ : IsAffineHom (e.hom.left ≫ pullback.fst XT.hom q) := inferInstance
  obtain ⟨m, hnm⟩ : ∃ m : ℕ, n = (m : ℤ) :=
    ⟨n.toNat, (Int.toNat_of_nonneg ((Int.natCast_nonneg d).trans hn.le)).symm⟩
  refine isZero_cohomology_of_isZero_cohomology_pushforward_of_isAffineHom
    (e.hom.left ≫ pullback.fst XT.hom q) G hnm ?_
  exact hN XT.hom hpropT ‹IsAffine T› inferInstance hdimT n hn _
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom _ G hG)

/-- **The vanishing over an arbitrary affine base.** For a proper morphism `g : X ⟶ Y` onto an
affine scheme all of whose fibres have dimension at most `d`, the cohomology `Hⁱ(X, ℱ)` of a
quasi-coherent module vanishes for every `i > d`.

This is the statement the proof of [Stacks, Tag 0E7D] reduces to after shrinking `Y`: the two
limit reductions, `cohomology_vanishing_of_forall_isLocallyNoetherian_base`, composed with the
Noetherian case `isZero_cohomology_of_isLocallyNoetherian_affine_base`. -/
theorem isZero_cohomology_of_affine_base {d : ℕ} {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    [IsAffine Y] (hdim : ∀ s : Y, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus i).obj F) :=
  cohomology_vanishing_of_forall_isLocallyNoetherian_base
    (fun g₀ hprop haff hnoe hdim₀ n hn G hG =>
      @isZero_cohomology_of_isLocallyNoetherian_affine_base d _ _ g₀ hprop haff hnoe hdim₀ G hG n
        hn)
    g hdim i hi F

/-- **`CohomologyVanishesAboveOne`, proved.** A proper morphism onto an affine scheme all of
whose fibres have dimension at most one has vanishing cohomology of quasi-coherent modules in
every degree above one: `isZero_cohomology_of_affine_base` at `d = 1`. -/
theorem cohomologyVanishesAboveOne : CohomologyVanishesAboveOne.{u} :=
  fun g hg hY hdim i hi F hF =>
    cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le 1 g hg hY hdim i hi F hF

/-- **The higher direct images of a proper morphism with fibres of dimension at most `d` vanish
above `d`.** For a proper `f : X ⟶ Y` all of whose fibres have dimension at most `d` and a
quasi-coherent `ℱ` on `X`, `Rⁱ f_* ℱ = 0` for every `i > d`.

This is part (1) of [Stacks, Tag 0E7D] at every point of `Y` at once, a sheaf of modules all of
whose stalks vanish being zero. -/
theorem isZero_rightDerivedPlus_pushforward_of_forall_fiber_dim_le {d : ℕ}
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) :=
  AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y =>
    isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y d (hdim y)
      (cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d) F i hi

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
