module

public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing

/-!
# Over an affine base, cohomology, higher direct image and stalks vanish together

`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/AffineBaseCohomology.lean` reduces both
parts of [Stacks, Tag 0E7D] to the hypothesis that a proper morphism onto an affine base with
all fibres of dimension at most `d` has vanishing *absolute cohomology* `Hⁱ(X₀, F)` for `i > d`
and `F` quasi-coherent, by proving one direction of the source's sentence

> by [Stacks, Tag 01XK] we have `Hᵖ(X₀, F) = H⁰(Y₀, Rᵖ g_* F)`; on the other hand `Rᵖ g_* F` is
> quasi-coherent on `Y₀` by [Stacks, Tag 01XJ], hence vanishing of global sections implies
> vanishing.

The source's *last* paragraph runs the same identification in the opposite direction: having
obtained `(Rᵖ f_* F)_y = 0` for every `y` from [Stacks, Tag 02V7], it concludes
`Rᵖ f_* F = 0` and *therefore* `Hᵖ(X, F) = 0`. That direction was missing. This file supplies
it, and so closes the loop: over an affine base, for a quasi-coherent module and a
quasi-compact quasi-separated morphism, the three statements

* `Hⁱ(X₀, F)` is a zero object,
* `Rⁱ g_* F` is a zero object,
* every stalk of `Rⁱ g_* F` is a zero object

are **equivalent**.

The consequence is that the hypothesis of the `AffineBaseCohomology.lean` reductions may be taken
in the shape in which [Stacks, Tag 02V7] states its conclusion — stalkwise vanishing of the
higher direct image — rather than as absolute cohomological vanishing: the two hypotheses are
interchangeable by `isZero_cohomology_iff_forall_isZero_stalk_rightDerivedPlus`. Both parts of
[Stacks, Tag 0E7D] themselves, with no such hypothesis, are
`isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le` and
`exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le` of
`FibreDimensionStalkVanishing.lean`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_stalk_of_isZero_module`: a zero sheaf of modules on a scheme has zero stalks. This is
  the converse of `AlgebraicGeometry.isZero_of_forall_isZero_stalk`.
* `isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward`: the resulting equivalence with
  `isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`.
* `isZero_cohomology_of_forall_isZero_stalk_rightDerivedPlus`: the conclusion of
  [Stacks, Tag 02V7] gives vanishing cohomology over an affine base.
* `isZero_cohomology_iff_forall_isZero_stalk_rightDerivedPlus`: the three-way equivalence.

## Implementation notes

[Stacks, Tag 01XK] is a natural isomorphism whose left-hand side carries a restriction of
scalars along `g^♯`. Restriction of scalars does not change the carrier of a module, so a zero
object on the left is detected by `ModuleCat.isZero_iff_subsingleton` on both sides; this is why
the hypothesis `h` can be transported through it without any assumption on `g^♯`.

The missing direction itself — over an affine base, a vanishing higher direct image forces
vanishing cohomology — is `isZero_cohomology_of_isZero_rightDerivedPlus_pushforward` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/BaseChangeVanishing.lean`, imported here.
The same statement was once proved a second time in this file under the same fully qualified
name; which of the two a consumer saw depended on its import order, so the copy was removed.

The stalk of a sheaf of modules is spelled as the stalk `M.presheaf.stalk y` of the underlying
presheaf of abelian groups, matching
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict` and the
conclusion of `isZero_stalk_rightDerivedPlus_of_cohomology_vanishing`.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **A zero sheaf of modules on a scheme has vanishing stalks.** The forgetful functor to
presheaves of abelian groups and the stalk functor are both additive, so each carries a zero
object to a zero object. This is the converse of
`AlgebraicGeometry.isZero_of_forall_isZero_stalk`. -/
theorem isZero_stalk_of_isZero_module {Y : Scheme.{u}} (M : Y.Modules) (y : Y)
    (h : IsZero M) : IsZero (M.presheaf.stalk y) :=
  Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} y)
    (Functor.map_isZero (Scheme.Modules.toPresheaf Y) h)

/-- **Over an affine base, vanishing cohomology and a vanishing higher direct image are the same
condition.** The two implications are
`isZero_rightDerivedPlus_pushforward_of_isZero_cohomology` and
`isZero_cohomology_of_isZero_rightDerivedPlus_pushforward`. -/
theorem isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g] [QuasiSeparated g] [IsAffine Y₀]
    (i : ℤ) (F : X₀.Modules) [F.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) ↔
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F) :=
  ⟨isZero_rightDerivedPlus_pushforward_of_isZero_cohomology g i F,
    isZero_cohomology_of_isZero_rightDerivedPlus_pushforward g i F⟩

/-- **The conclusion of [Stacks, Tag 02V7] gives vanishing cohomology over an affine base.** If
every stalk of `Rⁱ g_* F` vanishes then `Rⁱ g_* F` is a zero object
(`AlgebraicGeometry.isZero_of_forall_isZero_stalk`), hence so is `Hⁱ(X₀, F)`.

This is the step the last paragraph of the proof of [Stacks, Tag 0E7D] takes: *"Thus
`Rᵖ f_* F = 0` and therefore `Hᵖ(X, F) = 0`."* -/
theorem isZero_cohomology_of_forall_isZero_stalk_rightDerivedPlus
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g] [QuasiSeparated g] [IsAffine Y₀]
    (i : ℤ) (F : X₀.Modules) [F.IsQuasicoherent]
    (h : ∀ y : Y₀,
      IsZero ((((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F).presheaf.stalk y)) :
    IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) :=
  isZero_cohomology_of_isZero_rightDerivedPlus_pushforward g i F
    (AlgebraicGeometry.isZero_of_forall_isZero_stalk _ h)

/-- **Over an affine base, cohomological vanishing is stalkwise vanishing of the higher direct
image.** For a quasi-compact quasi-separated morphism onto an affine scheme and a quasi-coherent
module, `Hⁱ(X₀, F) = 0` holds if and only if `(Rⁱ g_* F)_y = 0` for every `y`.

So the hypothesis `hcoh` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isAffineOpen_vanishing_of_cohomology_vanishing`
and the conclusion of [Stacks, Tag 02V7] are the same statement, up to the difference between
quasi-coherent and coherent modules. -/
theorem isZero_cohomology_iff_forall_isZero_stalk_rightDerivedPlus
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g] [QuasiSeparated g] [IsAffine Y₀]
    (i : ℤ) (F : X₀.Modules) [F.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F) ↔
      ∀ y : Y₀,
        IsZero ((((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  ⟨fun h y => isZero_stalk_of_isZero_module _ y
      (isZero_rightDerivedPlus_pushforward_of_isZero_cohomology g i F h),
    isZero_cohomology_of_forall_isZero_stalk_rightDerivedPlus g i F⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
