module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# Both parts of Tag 0E7D for a proper morphism with zero-dimensional fibres

[Stacks, Tag 0E7D] fixes a proper morphism `f : X ⟶ Y` and a point `y ∈ Y` with
`dim(X_y) = d`, and asserts that `(Rⁱ f_* F)_y = 0` for `i > d` and every quasi-coherent
`F` (part 1), and that `y` has an affine open neighbourhood `V` over which `f` and `d`
satisfy the hypotheses and the conclusions of [Stacks, Tag 0EX3] (part 2).

`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/AffineBaseCohomology.lean` reduces
both parts to a single hypothesis, there called `hcoh`: that a proper morphism onto an
affine scheme all of whose fibres have dimension at most `d` has vanishing cohomology of
quasi-coherent modules above `d`. That hypothesis is the whole remaining substance of the
tag, and for a general `d` the source proves it by reduction to the finiteness theorem for
the cohomology of a proper morphism over a Noetherian base.

This file discharges it **unconditionally for `d = 0`**, and so proves both parts of the tag
for a proper morphism whose fibres all have dimension at most `0`. The argument is three
steps, each already available: such a morphism is finite by Zariski's main theorem
([Stacks, Tag 02OH]), a finite morphism onto an affine scheme has affine source, and the
positive-degree cohomology of a quasi-coherent module on an affine scheme vanishes
([Stacks, Tag 01XB]).

## Main results

All three live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_rightDerivedPlus_moduleGlobalSections_of_isAffine`: [Stacks, Tag 01XB] in the
  spelling the statements of this directory use — `Hⁱ(X, F)` as
  `((moduleGlobalSections X).rightDerivedPlus i).obj F`.
* `cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero`: the hypothesis `hcoh`
  of `exists_isAffineOpen_vanishing_of_cohomology_vanishing` and of
  `isZero_stalk_rightDerivedPlus_of_cohomology_vanishing`, for `d = 0`, discharged.
* `exists_isAffineOpen_vanishing_of_fiber_dimension_le_zero` and
  `isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_zero`: parts (2) and (1) of
  [Stacks, Tag 0E7D] for `d = 0`, with no hypothesis beyond the tag's own.

## Implementation notes

The two `@[stacks 0E7D]` attributes here carry the part string *for fibre dimension at most
`0`*: the tag asserts both parts for an arbitrary `d`, and the fibre-dimension hypothesis used
here is strictly stronger for every `d ≥ 1`. The two parts for an arbitrary `d` are proved in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/FibreDimensionStalkVanishing.lean`, and carry
the tag there too.

What is specific to `d = 0` is the route. The source obtains the affine-base vanishing from
[Stacks, Tag 02V7] — hence from the theorem on formal functions ([Stacks, Tag 02OD]) — while
`AffineBaseVanishing.lean` reaches it for an arbitrary `d` by Nakayama's lemma at the maximal
ideals of the base ring, together with the source's two limit reductions. At `d = 0` neither is
needed: Zariski's main theorem makes the morphism finite, and the cohomology of a quasi-coherent
module on an affine scheme vanishes in positive degrees.

`isZero_rightDerivedPlus_moduleGlobalSections_of_isAffine` is not new mathematics: it is
`Stacks.Cohomology.AffineBase.rightAcyclic_moduleGlobalSections`, which states
[Stacks, Tag 01XB] as acyclicity of the module-valued global sections functor, read through
`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`. The second
clause of that iff needs `PreservesFiniteLimits`, supplied by the instance
`Stacks.Cohomology.AffineBase.moduleGlobalSections_preservesFiniteLimits`. It is stated
separately because the vanishing, not the acyclicity, is the form every consumer in this
directory needs; `@[stacks 01XB]` stays on
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, which states the tag for an
arbitrary affine open.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **The positive-degree cohomology of a quasi-coherent module on an affine scheme
vanishes**, [Stacks, Tag 01XB], in the `rightDerivedPlus` spelling.

This is `Stacks.Cohomology.AffineBase.rightAcyclic_moduleGlobalSections` read through
`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`, whose second
clause applies because `moduleGlobalSections` preserves finite limits. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_isAffine
    (X : Scheme.{u}) [IsAffine X] (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : 0 < i) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) :=
  (((moduleGlobalSections X).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F).2
    inferInstance).1 (rightAcyclic_moduleGlobalSections X F) i hi

/-- **The vanishing hypothesis of [Stacks, Tag 0E7D], discharged for `d = 0`.** A proper
morphism onto an affine scheme all of whose fibres have dimension at most `0` has vanishing
cohomology of quasi-coherent modules in every positive degree.

Such a morphism is finite by Zariski's main theorem ([Stacks, Tag 02OH]), as
`AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero`; a
finite morphism is affine, so the source is affine over an affine target; and the cohomology
of a quasi-coherent module on an affine scheme vanishes in positive degrees.

The statement is written at the exact shape of the hypothesis `hcoh` of
`exists_isAffineOpen_vanishing_of_cohomology_vanishing` and
`isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` specialised to `d = 0`, so that it
can be supplied to either of them directly. -/
theorem cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero :
    ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ ((0 : ℕ) : WithBot ℕ∞)) →
      ∀ i : ℤ, ((0 : ℕ) : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) := by
  intro X₀ Y₀ g _ _ hfib i hi F _
  have : IsFinite g :=
    AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero g hfib
  have : IsAffine X₀ := AlgebraicGeometry.isAffine_of_isAffineHom g
  exact isZero_rightDerivedPlus_moduleGlobalSections_of_isAffine X₀ F i (by exact_mod_cast hi)

/-- **[Stacks, Tag 0E7D] part (2) for a proper morphism with zero-dimensional fibres**, with
no hypothesis beyond the tag's own. The point `y` has an affine open neighbourhood `V` such
that `f ∣_ V` and `0` satisfy the hypotheses of [Stacks, Tag 0EX3] — the two finiteness
conditions and the vanishing of the higher direct images above the degree — whose
conclusions are then available unconditionally from
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SituationBaseChange.lean`.

This is `exists_isAffineOpen_vanishing_of_cohomology_vanishing` at `d = 0`, with its
hypothesis `hcoh` discharged by
`cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero`.

The part string records that the fibre bound is `0`, not an arbitrary `d`. -/
@[stacks 0E7D "part (2) for fibre dimension at most `0`, with no further hypothesis"]
theorem exists_isAffineOpen_vanishing_of_fiber_dimension_le_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), ((0 : ℕ) : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) :=
  exists_isAffineOpen_vanishing_of_cohomology_vanishing f y 0 hdim
    cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero

/-- **[Stacks, Tag 0E7D] part (1) for a proper morphism with zero-dimensional fibres**, with
no hypothesis beyond the tag's own: the stalk at `y` of `Rⁱ f_* F` vanishes in every
positive degree, for every quasi-coherent `F`.

This is `isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` at `d = 0`, with its
hypothesis `hcoh` discharged by
`cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero`.

The part string records that the fibre bound is `0`, not an arbitrary `d`. -/
@[stacks 0E7D "part (1) for fibre dimension at most `0`, with no further hypothesis"]
theorem isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : 0 < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y 0 hdim
    cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le_zero F i
    (by exact_mod_cast hi)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
