module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal

/-!
# Over an affine base, vanishing of higher direct images is vanishing of cohomology

The proof of [Stacks, Tag 0E7D] reduces, after replacing the target by an affine open
neighbourhood of the given point, to the case of a proper morphism `g : X₀ ⟶ Y₀` with `Y₀`
affine all of whose fibres have dimension at most `d`, and then opens its second paragraph with

> It suffices to show that `Hᵖ(X₀, F) = 0` for `p > d`. Namely, by [Stacks, Tag 01XK] we have
> `Hᵖ(X₀, F) = H⁰(Y₀, Rᵖ g_* F)`. On the other hand, `Rᵖ g_* F` is quasi-coherent on `Y₀` by
> [Stacks, Tag 01XJ], hence vanishing of global sections implies vanishing.

This file proves that sentence. Both tags it invokes are already available —
`Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward` for
[Stacks, Tag 01XK] and
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage` for
[Stacks, Tag 01XJ] — and so is the step from vanishing global sections to a vanishing
quasi-coherent module on an affine scheme,
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine`; what was
missing was their composition.

Its consequence is that the hypothesis `hvan` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isAffineOpen_vanishing_of_affine_base` and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_stalk_rightDerivedPlus_of_affine_base` — the
remaining substance of [Stacks, Tag 0E7D] — may be replaced throughout by the vanishing of
absolute cohomology `Hⁱ(X₀, F)`, which is the form the rest of the source's argument works in and
the form in which the limit arguments ([Stacks, Tags 09ZR, 01ZM, 081F, 089W]) and Grothendieck
vanishing ([Stacks, Tag 02UZ], through [Stacks, Tag 02V7]) are stated.

## Main results

All four live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`: for a quasi-compact
  quasi-separated morphism onto an affine scheme, a quasi-coherent module with vanishing
  cohomology in a degree has vanishing higher direct image in that degree. This is
  unconditional.
* `isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing`: the hypothesis `hvan` of the
  two statements below, deduced from the vanishing of cohomology above `d`.
* `exists_isAffineOpen_vanishing_of_cohomology_vanishing`: part (2) of [Stacks, Tag 0E7D],
  granted the vanishing of cohomology above `d` over an affine base with all fibres bounded.
* `isZero_stalk_rightDerivedPlus_of_cohomology_vanishing`: part (1) of [Stacks, Tag 0E7D],
  granted the same.

## Implementation notes

`Hⁱ(X₀, F)` is spelled `((moduleGlobalSections X₀).rightDerivedPlus i).obj F`, with
`moduleGlobalSections` in the namespace `Stacks.Cohomology.AffineBase`, a module over
`Γ(X₀, ⊤)`. That is the spelling in which [Stacks, Tag 01XK] is stated, and it is the right
derived functor of global sections, so no comparison with another model of cohomology is
involved.

[Stacks, Tag 01XK] is a natural isomorphism of functors on the full subcategory of quasi-coherent
modules, so it is read at the object `⟨F, _⟩` of that subcategory; the restriction of scalars
along `g^♯` on its left-hand side is additive, hence kills a zero object, which is why no
hypothesis on `g^♯` appears.

The vanishing over an affine base is a hypothesis of the statements here, exactly as in
`FibreDimension.lean`; it is proved in `AffineBaseVanishing.lean`. [Stacks, Tag 0E7D] carries its
attribute on the two statements of `FibreDimensionStalkVanishing.lean`, which supply that
hypothesis in the shape of the conclusion of [Stacks, Tag 02V7], and on the two statements of
`ZeroDimensionalFibres.lean`, which take the separate route available for fibre dimension `0`.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
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

/-- **Over an affine base, vanishing cohomology is vanishing higher direct image.** If
`g : X₀ ⟶ Y₀` is quasi-compact and quasi-separated with `Y₀` affine and `F` is a quasi-coherent
module on `X₀` whose `i`-th cohomology vanishes, then the `i`-th higher direct image of `F`
vanishes.

This is the sentence [Stacks, Tag 0E7D] opens its second paragraph with:
[Stacks, Tag 01XK] identifies `Hⁱ(X₀, F)` with the global sections of `Rⁱ g_* F` over the affine
base, [Stacks, Tag 01XJ] makes `Rⁱ g_* F` quasi-coherent, and a quasi-coherent module on an
affine scheme with vanishing global sections is a zero object. -/
theorem isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
    {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g] [QuasiSeparated g] [IsAffine Y₀]
    (i : ℤ) (F : X₀.Modules) [F.IsQuasicoherent]
    (hcoh : IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F) := by
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  exact isZero_of_isZero_sections_of_isAffine _ ((R.map_isZero hcoh).of_iso
    ((cohomologyIsoGlobalSectionsRightDerivedPushforward g i).app ⟨F, inferInstance⟩).symm)

/-- **The vanishing hypothesis of [Stacks, Tag 0E7D] follows from the vanishing of cohomology.**
Granted that a proper morphism onto an affine scheme all of whose fibres have dimension at most
`d` has vanishing cohomology of quasi-coherent modules above `d`, the same morphisms have
vanishing higher direct images above `d`.

This is the hypothesis `hvan` of `exists_isAffineOpen_vanishing_of_affine_base` and of
`isZero_stalk_rightDerivedPlus_of_affine_base`, so it transports both of those statements to the
cohomological hypothesis. The fibre dimension bound is not used here — it is carried only so that
the conclusion has the shape those two statements assume. -/
theorem isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing (d : ℕ)
    (hcoh : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F)) :
    ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F) :=
  fun g hg hY₀ hfib i hi F hF =>
    isZero_rightDerivedPlus_pushforward_of_isZero_cohomology g i F (hcoh g hg hY₀ hfib i hi F hF)

/-- **[Stacks, Tag 0E7D] part (2), granted the vanishing of cohomology over an affine base.**
This is `exists_isAffineOpen_vanishing_of_affine_base` with its hypothesis `hvan` replaced, via
`isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing`, by the vanishing of absolute
cohomology above `d`. -/
theorem exists_isAffineOpen_vanishing_of_cohomology_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hcoh : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) :=
  exists_isAffineOpen_vanishing_of_affine_base f y d hdim
    (isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing d hcoh)

/-- **[Stacks, Tag 0E7D] part (1), granted the vanishing of cohomology over an affine base.**
This is `isZero_stalk_rightDerivedPlus_of_affine_base` with its hypothesis `hvan` replaced, via
`isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing`, by the vanishing of absolute
cohomology above `d`. -/
theorem isZero_stalk_rightDerivedPlus_of_cohomology_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hcoh : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((moduleGlobalSections X₀).rightDerivedPlus i).obj F))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  isZero_stalk_rightDerivedPlus_of_affine_base f y d hdim
    (isZero_rightDerivedPlus_pushforward_of_cohomology_vanishing d hcoh) F i hi

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
