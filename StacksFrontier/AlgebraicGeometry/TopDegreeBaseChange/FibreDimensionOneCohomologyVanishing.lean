module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageFiniteType
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.GloballyGeneratedVanishing

/-!
# Tag 0E7H: proper morphisms with fibres of dimension at most one and `H¹(X_y, 𝒪) = 0`

[Stacks, Tag 0E7H] fixes a proper morphism `f : X ⟶ Y` with `dim(X_y) ≤ 1` and
`H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`, and a quasi-coherent `ℱ` on `X`, and asserts

1. `Rᵖ f_* ℱ = 0` for `p > 1`,
2. `R¹ f_* ℱ = 0` if there is a surjection `f^*𝒢 ⟶ ℱ` with `𝒢` quasi-coherent on `Y`,

and, when `Y` is affine,

3. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`,
4. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

The proof is the source's. Clauses (1) and (3) are [Stacks, Tag 0E7D] at `d = 1`
(`ProperFibreDimensionVanishing.lean`). Clause (4) is the last paragraph of the source's proof —
a surjection `⨁ 𝒪_X ⟶ ℱ`, the long exact sequence with `H²(X, -) = 0`, and the commutation of
`H¹(X, -)` with direct sums ([Stacks, Tag 01FF]), assembled in `OneDimensionalFibres.lean` —
together with `H¹(X, 𝒪_X) = 0`, which the source takes from [Stacks, Tag 0E7G]: `R¹ f_* 𝒪_X` is
of finite type ([Stacks, Tag 0EX4]), its pullback to `Spec κ(y)` vanishes because
`H¹(X_y, 𝒪_{X_y}) = 0` (the base change of `FirstDirectImageBaseChangeVanishing.lean`), so `y` is
outside its support ([Stacks, Tag 056J]). Clause (2) is clause (4) over the affine opens of `Y`,
where `ℱ` is globally generated, read through [Stacks, Tags 01XJ, 01XK, 01E5].

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_higherDirectImage_of_one_lt_of_isProper`: **clause (1)**.
* `isZero_cohomology_of_notMem_zero_one_of_isAffine`: **clause (3)**.
* `isZero_firstDirectImageStructureSheaf_of_isFiniteType`: `R¹ f_* 𝒪_X = 0`, granted that it is
  of finite type.
* `isZero_cohomology_one_of_generatingSections_of_isFiniteType` and
  `isZero_higherDirectImage_one_of_epi_pullback_of_isFiniteType`: clauses (4) and (2), granted
  the same.
* `isZero_cohomology_one_of_generatingSections_of_isAffine`: **clause (4)**.
* `isZero_higherDirectImage_one_of_epi_pullback_of_isProper`: **clause (2)**.
* `isZero_firstDirectImageStructureSheaf_of_isProper`: `R¹ f_* 𝒪_X = 0`.

## Implementation notes

Clauses (1) and (3) do not use the tag's hypothesis `H¹(X_y, 𝒪_{X_y}) = 0`, and it is not
imposed on them. The fibre dimension is bounded above, `dim(X_y) ≤ 1`, exactly as in the source.

## References

* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-- **`R¹ f_* 𝒪_X = 0` from the vanishing of `H¹` on every fibre**, granted that `R¹ f_* 𝒪_X` is
of finite type. This is the argument of [Stacks, Tag 0E7G] at every point: the pullback of
`R¹ f_* 𝒪_X` to `Spec κ(y)` vanishes by `isZero_pullback_firstDirectImage_iff`, so `y` misses the
support, which is where finite type enters ([Stacks, Tag 056J]). -/
theorem isZero_firstDirectImageStructureSheaf_of_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y)))
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType) :
    IsZero (firstDirectImageStructureSheaf f) := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  have _ : IsProper (f.fiberToSpecResidueField y) := isProper_fiberToSpecResidueField f y
  have hfib' : IsZero (firstDirectImageStructureSheaf
      (pullback.snd f (Y.fromSpecResidueField y))) :=
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (f.fiberToSpecResidueField y) 1
      (SheafOfModules.unit (f.fiber y).ringCatSheaf) (hfib y)
  have hpull := (isZero_pullback_firstDirectImage_iff f hdim (Y.fromSpecResidueField y)).mpr hfib'
  have hsupp : y ∉ SheafOfModules.supp (firstDirectImageStructureSheaf f) := by
    have := notMem_supp_of_isZero_pullback (firstDirectImageStructureSheaf f) hft
      (Y.fromSpecResidueField y) (default : Spec (Y.residueField y)) hpull
    rwa [Scheme.fromSpecResidueField_apply] at this
  exact (notMem_supp_iff_isZero_stalk _ y).mp hsupp

/-- **[Stacks, Tag 0E7H] clause (1).** For a proper morphism `f : X ⟶ Y` all of whose fibres
have dimension at most one and a quasi-coherent `ℱ` on `X`, `Rᵖ f_* ℱ = 0` for every `p > 1`.

This is [Stacks, Tag 0E7D] at `d = 1`. The tag's hypothesis `H¹(X_y, 𝒪_{X_y}) = 0` is not used
for this clause and is not imposed. -/
@[stacks 0E7H "clause (1)"]
theorem isZero_higherDirectImage_of_one_lt_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : 1 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  isZero_rightDerivedPlus_pushforward_of_forall_fiber_dim_le f hdim F p (by exact_mod_cast hp)

/-- **[Stacks, Tag 0E7H] clause (3).** For a proper morphism `f : X ⟶ Y` onto an affine scheme
all of whose fibres have dimension at most one and a quasi-coherent `ℱ` on `X`,
`Hᵖ(X, ℱ) = 0` for every `p ∉ {0, 1}`.

Negative degrees vanish for formal reasons, and degrees above one by [Stacks, Tag 0E7D] over an
affine base. The tag's hypothesis `H¹(X_y, 𝒪_{X_y}) = 0` is not used for this clause and is not
imposed. -/
@[stacks 0E7H "clause (3)"]
theorem isZero_cohomology_of_notMem_zero_one_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : p ∉ ({0, 1} : Set ℤ)) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus p).obj F) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
  obtain ⟨hp0, hp1⟩ := hp
  rcases lt_or_gt_of_ne hp0 with h | h
  · exact CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
      (Stacks.Cohomology.AffineBase.moduleGlobalSections X) F p h
  · exact isZero_cohomology_of_affine_base (d := 1) f hdim F p (by omega)

/-- Over an affine base, `R¹ f_* 𝒪_X = 0` and fibres of dimension at most one force `H¹(X, ℱ) = 0`
for globally generated quasi-coherent `ℱ`. -/
private theorem isZero_cohomology_one_of_isZero_firstDirectImageStructureSheaf {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsZero (firstDirectImageStructureSheaf f))
    (F : X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus 1).obj F) :=
  isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one cohomologyVanishesAboveOne
    f hdim (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward f 1
      (SheafOfModules.unit X.ringCatSheaf) h0) F σ

/-- **The last paragraph of the proof of [Stacks, Tag 0E7H]**, granted that `R¹ f_* 𝒪_X` is of
finite type: over an affine base, a globally generated quasi-coherent module has `H¹(X, ℱ) = 0`.
The vanishing `H¹(X, 𝒪_X) = 0` it needs is `isZero_firstDirectImageStructureSheaf_of_isFiniteType`
read over the affine base by [Stacks, Tag 01XK], and `H²` vanishes by [Stacks, Tag 0E7D]. -/
theorem isZero_cohomology_one_of_generatingSections_of_isFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y)))
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (F : X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus 1).obj F) :=
  isZero_cohomology_one_of_isZero_firstDirectImageStructureSheaf f hdim
    (isZero_firstDirectImageStructureSheaf_of_isFiniteType f hdim hfib hft) F σ

/-- **Clause (2) of [Stacks, Tag 0E7H]**, granted that `R¹ f_* 𝒪_X` is of finite type. -/
theorem isZero_higherDirectImage_one_of_epi_pullback_of_isFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y)))
    (hft : (firstDirectImageStructureSheaf f).IsFiniteType)
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    (p : (Scheme.Modules.pullback f).obj G ⟶ F) (hp : Epi p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus 1).obj F) := by
  have h0 := isZero_firstDirectImageStructureSheaf_of_isFiniteType f hdim hfib hft
  have hcov : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ IsAffineOpen V := fun y => by
    obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ ((⊤ : Y.Opens) : Set Y) from trivial) (⊤ : Y.Opens).isOpen
    exact ⟨V, hyV, hV⟩
  choose V hmem haff using hcov
  refine isZero_of_isZero_restrict_cover V
    (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hmem y⟩) _ fun y => ?_
  let _ : IsAffine (V y).toScheme := haff y
  have hdimV : ∀ s : (V y).toScheme,
      topologicalKrullDim ((f ∣_ V y).fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f (V y) 1 fun t _ => hdim t
  have hcohV : IsZero
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ V y).toScheme).rightDerivedPlus
        1).obj ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V y).ι).obj F)) :=
    isZero_cohomology_one_of_isZero_firstDirectImageStructureSheaf (f ∣_ V y) hdimV
      (isZero_firstDirectImage_structureSheaf_restrict f (V y) h0) _
      (generatingSectionsRestrictPreimage f (V y) G F p hp)
  have hdirV : IsZero (((Scheme.Modules.pushforward (f ∣_ V y)).rightDerivedPlus
      ((1 : ℕ) : ℤ)).obj ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V y).ι).obj F)) :=
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (f ∣_ V y) 1 _ hcohV
  exact IsZero.of_iso hdirV
    (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f (V y) 1 F).symm

/-- **[Stacks, Tag 0E7H] clause (4).** Let `f : X ⟶ Y` be a proper morphism onto an affine
scheme such that `dim(X_y) ≤ 1` and `H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`, and let `ℱ` be a
quasi-coherent `𝒪_X`-module which is globally generated. Then `H¹(X, ℱ) = 0`.

`R¹ f_* 𝒪_X` is of finite type by [Stacks, Tag 0EX4] at `d = 1`
(`firstDirectImageFiniteTypeOfFibreDimensionOne`), and the rest is
`isZero_cohomology_one_of_generatingSections_of_isFiniteType`. -/
@[stacks 0E7H "clause (4)"]
theorem isZero_cohomology_one_of_generatingSections_of_isAffine {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsAffine Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y)))
    (F : X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerivedPlus 1).obj F) :=
  isZero_cohomology_one_of_generatingSections_of_isFiniteType f hdim hfib
    (firstDirectImageFiniteTypeOfFibreDimensionOne f inferInstance hdim) F σ

/-- **[Stacks, Tag 0E7H] clause (2).** Let `f : X ⟶ Y` be a proper morphism such that
`dim(X_y) ≤ 1` and `H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`, let `ℱ` be a quasi-coherent
`𝒪_X`-module, and suppose there is a surjection `f^*𝒢 ⟶ ℱ` with `𝒢` quasi-coherent on `Y`.
Then `R¹ f_* ℱ = 0`. -/
@[stacks 0E7H "clause (2)"]
theorem isZero_higherDirectImage_one_of_epi_pullback_of_isProper {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y)))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    (p : (Scheme.Modules.pullback f).obj G ⟶ F) (hp : Epi p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus 1).obj F) :=
  isZero_higherDirectImage_one_of_epi_pullback_of_isFiniteType f hdim hfib
    (firstDirectImageFiniteTypeOfFibreDimensionOne f inferInstance hdim) F G p hp

/-- `R¹ f_* 𝒪_X = 0` for a proper morphism all of whose fibres have dimension at most one and
vanishing `H¹(X_y, 𝒪_{X_y})`. -/
theorem isZero_firstDirectImageStructureSheaf_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (f.fiber y))) :
    IsZero (firstDirectImageStructureSheaf f) :=
  isZero_firstDirectImageStructureSheaf_of_isFiniteType f hdim hfib
    (firstDirectImageFiniteTypeOfFibreDimensionOne f inferInstance hdim)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
