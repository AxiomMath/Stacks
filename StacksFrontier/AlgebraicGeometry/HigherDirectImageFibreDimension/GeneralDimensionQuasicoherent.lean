module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyFilteredColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 02V7 for quasi-coherent modules over a locally Noetherian base

`StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimension.lean` proves
[Stacks, Tag 02V7] as the source states it: for `f : X ⟶ Y` proper onto a locally Noetherian
base and `y ∈ Y` with `dim(X_y) ≤ d`, the stalk `(Rᵖ f_* ℱ)_y` vanishes for `p > d` and `ℱ`
**coherent**. The proof of [Stacks, Tag 0E7D] needs the same vanishing for `ℱ` merely
**quasi-coherent**, and that is what this file supplies, over a locally Noetherian base.

The passage from coherent to quasi-coherent is the source's own and is one filtered colimit. A
quasi-coherent module on a quasi-compact quasi-separated scheme is the colimit of a directed
system of modules of finite presentation ([Stacks, Tag 01PK]) and cohomology on such a scheme
commutes with filtered colimits ([Stacks, Tag 01FF]); over a locally Noetherian scheme a module
of finite presentation is coherent ([Stacks, Tag 01XZ], (3) ⇒ (1)). Both halves are already
available: the colimit step is
`…TopDegreeBaseChange.isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation`
and the upgrade is `…CoherenceCriteria.isCoherent_of_isFinitePresentation`.

So the argument is `GeneralDimension.lean`'s, with the coherent hypothesis on the module
relaxed one step before the affine-base vanishing is invoked: shrink `Y` to an affine open
`V ∋ y` over which *every* fibre is bounded by `d`, note that the stalk at `y` only sees
`f ∣_ V`, and over the affine base `V` turn the higher direct image into absolute cohomology —
at which point the module may be decomposed, because each piece of the decomposition is coherent
and `isZero_rightDerived_moduleGlobalSections_of_affine_base` applies to it.

## Main results

* `…FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent`:
  **[Stacks, Tag 0E7D] part (1) over a locally Noetherian base, with no further hypothesis.**

This is [Stacks, Tag 0E7D] part (1) over a locally Noetherian base, which is the only case
[Stacks, Tag 0EHU] uses: there the base is `Spec A` for a Noetherian ring `A`. Part (1) over an
arbitrary base is
`…TopDegreeBaseChange.isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le`.

## Implementation notes

The hypothesis is `IsLocallyNoetherian Y` rather than `IsAffine Y₀` quantified over all affine
bases. Over an affine base with no Noetherian hypothesis the coherent modules are the wrong
intermediary and the statement needs Noetherian approximation instead; that is a different
argument and is not what the consumers in Chapter 51 need.

`CategoryTheory.HasDerivedCategory.standard` is given the same raised priority as in
`GeneralDimension.lean`, for the same reason: otherwise the `rightDerivedPlus` of the statement
lands in a different derived-category universe from the rest of `TopDegreeBaseChange/` and the
statements no longer compose.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.FibreDimension

attribute [local instance 2000] HasDerivedCategory.standard

/-- **[Stacks, Tag 02V7] for quasi-coherent modules, over an affine locally Noetherian base.**
For `g : X₀ ⟶ Y₀` proper with `Y₀` affine and locally Noetherian and every fibre of dimension at
most `d`, the cohomology `Hᵖ(X₀, ℱ)` of a *quasi-coherent* module vanishes for `p > d`.

`isZero_rightDerived_moduleGlobalSections_of_affine_base` is this statement for a coherent
module. A quasi-coherent module on the quasi-compact quasi-separated scheme `X₀` is a filtered
colimit of modules of finite presentation, each of which is coherent because `X₀` is locally
Noetherian, and cohomology commutes with the colimit. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [IsProper g] [IsAffine Y₀] [IsLocallyNoetherian Y₀]
    [CompactSpace (X₀ : Type u)] [QuasiSeparatedSpace (X₀ : Type u)] {d : ℕ}
    (hfib : ∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞))
    (F : X₀.Modules) [F.IsQuasicoherent] {p : ℕ} (hp : d < p) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X₀).rightDerivedPlus
      (p : ℤ)).obj F) := by
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian g
  refine
    TopDegreeBaseChange.isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation
      X₀ p F fun G hG => ?_
  have : G.IsCoherent := CoherenceCriteria.isCoherent_of_isFinitePresentation G hG
  rw [Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup,
    ← Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      (R := X₀.ringCatSheaf) (U := ⊤) p G]
  exact isZero_rightDerived_moduleGlobalSections_of_affine_base g hfib G hp

/-- **[Stacks, Tag 0E7D] part (1) over a locally Noetherian base, with no further hypothesis.**
Let `f : X ⟶ Y` be proper with `Y` locally Noetherian and let `y ∈ Y` be a point whose fibre
`X_y` has dimension at most `d`. Then the stalk at `y` of `Rᵖ f_* ℱ` vanishes for every `p > d`
and every **quasi-coherent** `ℱ` on `X`.

This is [Stacks, Tag 02V7] — `isZero_stalk_rightDerivedPlus_of_fiber_dimension_le` — with the
coherence of the module relaxed to quasi-coherence, which is the form the proof of
[Stacks, Tag 0E7D] uses and the form [Stacks, Tag 0EHU] needs. The argument is the same:
`AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le` produces an affine
open `V ∋ y` over which every fibre is bounded by `d`, the stalk at `y` of the higher direct
image along `f` is the one along `f ∣_ V`
(`…SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict`), over the affine
base `V` the higher direct image vanishes as soon as the cohomology of `f ⁻¹ V` does
(`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`), and that
vanishing is `isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent`. -/
@[sga "6 X 4.4" "Stalk form of (4.4.5)"]
theorem isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : (d : ℤ) < p) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) := by
  obtain ⟨V, hyV, hVaff, hVdim⟩ :=
    _root_.AlgebraicGeometry.exists_isAffineOpen_forall_topologicalKrullDim_fiber_le f
      f.isClosedMap y d hdim
  let : IsAffine V.toScheme := hVaff
  have : CompactSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hVaff.isCompact)
  have : QuasiSeparatedSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg ((Int.natCast_nonneg d).trans hp.le)).symm⟩
  have hn : d < n := by exact_mod_cast hp
  have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ V).ι F
  refine SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict f V y hyV F
    (Int.natCast_nonneg n)
    (TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
      (f ∣_ V) (n : ℤ) _ ?_)
  exact isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent (f ∣_ V)
    (fun s => _root_.AlgebraicGeometry.topologicalKrullDim_fiber_morphismRestrict_le f V d
      (fun z hz => hVdim z hz) s) _ hn

end Stacks.AlgebraicGeometry.FibreDimension

end
