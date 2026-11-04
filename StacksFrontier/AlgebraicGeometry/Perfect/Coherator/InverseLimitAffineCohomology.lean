module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.DerivedSectionsAndInverseLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology on an affine open of a derived limit of quasi-coherent sheaves

Let `X` be a scheme, let `(𝓕ₙ)` be an inverse system of quasi-coherent `𝒪_X`-modules and let
`K = R lim 𝓕ₙ` in `D(𝒪_X)`. For an affine open `U ⊆ X` one has
`H^i(U, K) = H^i(R lim Γ(U, 𝓕ₙ))`, because sections over `U` commute with derived limits and a
quasi-coherent sheaf has no higher cohomology on an affine open; so `H^i(U, K)` vanishes unless
`i ∈ [0, 1]`.

## Main results

* `AlgebraicGeometry.isZero_cohomology_of_isDerivedLimit_single_of_isAffineOpen`:
  **[Stacks, Tag 0CSB]** — the cohomology of such a `K` over an affine open vanishes outside
  degrees `0` and `1`.

## Implementation notes

The derived limit is presented by the predicate
`CategoryTheory.Pretriangulated.IsDerivedLimit`, so the statement does not depend on a chosen
construction of `R lim`. Sections over `U` are taken on the ringed site of opens of `X`, where
`Stacks.Cohomology.DerivedSectionsMilnor.isDerivedLimit_map_derivedSectionsOverObject` makes
`RΓ(U, -)` commute with derived limits; the Milnor short exact sequence
`CategoryTheory.DerivedCategory.isDerivedLimit_homology_shortExact` then turns the vanishing of
`H^j(U, 𝓕ₙ)` for `j ≠ 0` into the degree bound, both of its outer terms vanishing outside
`[0, 1]`.

That `H^j(U, 𝓕ₙ)` vanishes for `j > 0` is Serre vanishing on an affine open, transported from the
classical right derived functors of the sections functor to the cohomology of its unbounded right
derived functor; for `j < 0` it is left t-exactness of that derived functor.

## References

* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Cohomology.Localization (derivedSectionsOverObject sectionsOverObject)
open Stacks.SheafOfModules.InternalHom (spaceRingedSite)

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- The site of opens of a scheme, with its structure sheaf, read as a ringed site. -/
noncomputable abbrev schemeOpensRingedSite (X : Scheme.{u}) : RingedSite.{u, u, u} :=
  spaceRingedSite X.toRingedSpace.sheaf

/-- Over an open of a scheme, the hypercohomology of a sheaf placed in degree zero with no higher
cohomology on that open vanishes outside degree zero: above degree zero by the vanishing, below
it by left t-exactness of the derived sections functor. -/
private lemma isZero_cohomology_single (X : Scheme.{u}) (U : X.Opens)
    [(sectionsOverObject (schemeOpensRingedSite X) U).Additive]
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (schemeOpensRingedSite X).O))
    (hM : ∀ p : ℕ, 0 < p →
      IsZero (((sectionsOverObject (schemeOpensRingedSite X) U).rightDerived p).obj M))
    (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
      ((derivedSectionsOverObject (schemeOpensRingedSite X) U).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (schemeOpensRingedSite X).O)) 0).obj M))) := by
  rcases lt_trichotomy j 0 with h | h | h
  · exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (sectionsOverObject (schemeOpensRingedSite X) U) _ 0 j h
  · exact absurd h hj
  · exact Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
      (sectionsOverObject (schemeOpensRingedSite X) U)
      (Stacks.DerivedFunctor.totalRightDerived
        (sectionsOverObject (schemeOpensRingedSite X) U))
      ((Stacks.DerivedFunctor.homotopyMap
        (sectionsOverObject (schemeOpensRingedSite X) U)).totalRightDerivedUnit
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (schemeOpensRingedSite X).O))
            (ComplexShape.up ℤ)))
      Stacks.Cohomology.Localization.enoughKInjectives M hM 0 j h

/-- **[Stacks, Tag 0CSB].** Let `X` be a scheme, let `(𝓕ₙ)` be an inverse system of
quasi-coherent `𝒪_X`-modules and let `L` be a derived limit in `D(𝒪_X)` of the system `(𝓕ₙ)`
placed in degree zero. Then `H^i(U, L) = 0` for every affine open `U ⊆ X` and every `i` outside
`[0, 1]`.

Sections over `U` commute with derived limits, so `RΓ(U, L) = R lim RΓ(U, 𝓕ₙ)`, and each
`RΓ(U, 𝓕ₙ)` is concentrated in degree zero because `𝓕ₙ` is quasi-coherent and `U` is affine. In
the Milnor short exact sequence `0 → lim¹ H^{i-1}(U, 𝓕ₙ) → H^i(U, L) → lim H^i(U, 𝓕ₙ) → 0` both
outer terms then vanish as soon as `i ≠ 0` and `i ≠ 1`. -/
@[stacks 0CSB "the cohomology computation on an affine open: H^i(U, R lim 𝓕ₙ) = 0 for i outside \
[0, 1]"]
theorem isZero_cohomology_of_isDerivedLimit_single_of_isAffineOpen (X : Scheme.{u})
    (𝓕 : ℕᵒᵖ ⥤ X.Modules) (hqc : ∀ n : ℕ, (𝓕.obj ⟨n⟩).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩]
    (L : DerivedCategory.{u + 1} X.Modules)
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0) L)
    (U : X.Opens) (hU : IsAffineOpen U) (i : ℤ) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedSectionsOverObject (schemeOpensRingedSite X) U).obj L)) := by
  let Y : RingedSite.{u, u, u} := schemeOpensRingedSite X
  let K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    𝓕 ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0
  let L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := L
  let : HasProduct fun n : ℕ ↦ K.obj ⟨n⟩ :=
    ‹HasProduct fun n : ℕ ↦ (𝓕 ⋙ DerivedCategory.singleFunctor X.Modules 0).obj ⟨n⟩›
  obtain ⟨p, δ, hδ⟩ := hL
  have hDL : IsDerivedLimit K L' := ⟨p, δ, hδ⟩
  obtain ⟨hprodΓ, hRL⟩ :=
    Stacks.Cohomology.DerivedSectionsMilnor.isDerivedLimit_map_derivedSectionsOverObject
      Y U K L' hDL
  let := hprodΓ
  have := Stacks.Cohomology.Localization.additive_sectionsOverObject Y U
  -- Each `RΓ(U, 𝓕ₙ)` is concentrated in degree zero.
  have hterm : ∀ (n : ℕ) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
        ((K ⋙ derivedSectionsOverObject Y U).obj ⟨n⟩)) := by
    intro n j hj
    have := hqc n
    exact isZero_cohomology_single X U (𝓕.obj ⟨n⟩)
      (fun q hq ↦ Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X
        (𝓕.obj ⟨n⟩) U hU q hq) j hj
  obtain ⟨a, b, -, hdeg⟩ :=
    DerivedCategory.isDerivedLimit_homology_shortExact
      (K ⋙ derivedSectionsOverObject Y U) ((derivedSectionsOverObject Y U).obj L') hRL
  obtain ⟨e, ι, q, w, -, -, -, hShortExact⟩ := hdeg i
  refine isZero_X₂_of_shortExact hShortExact ?_ ?_
  · exact isZero_cokernel_of_isZero
      (isZero_limit_of_forall_isZero _ fun n ↦ hterm n.as (i - 1) (by omega)) _
  · exact isZero_limit_of_forall_isZero _ fun n ↦ hterm n.unop i hi0

end AlgebraicGeometry

end
