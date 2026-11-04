module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTriangleTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# The open-closed triangle for the derived lower shriek

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated schemes,
let `U` be a quasi-compact open of `X` with complement `Z`, and let `g : U ⟶ Y` and `h : Z ⟶ Y`
be the restrictions of `f`. Let `Λ` be a ring. [Stacks, Tag 0GKP] gives, for `K` in
`D⁺_tors(X_étale, Λ)`, or in `D(X_étale, Λ)` when `Λ` is torsion, a distinguished triangle
`Rg_!(K|_U) ⟶ Rf_! K ⟶ Rh_!(K|_Z) ⟶ Rg_!(K|_U)[1]` in `D(Y_étale, Λ)`.

## Main results

* `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriek_openClosed`: **[Stacks, Tag
  0GKP]**, both cases.
* `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriek_openClosed_plus` and
  `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriekUnbounded_openClosed`: the
  bounded below and the unbounded case separately.

## Implementation notes

The functor `Rf_!`, `Stacks.EtaleCohomology.derivedLowerShriek` on bounded below and
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on unbounded derived categories, is
`R f̄_* ∘ j_!` for a compactification `j : X ⟶ X̄` that is an explicit argument (the choice does
not matter by [Stacks, Tag 0F7I]). The statement is made for an arbitrary compactification `j`
of `f`, with `Rg_!` and `Rh_!` computed through the compactifications it induces on `U` and on
`Z`: `AlgebraicGeometry.CompactificationOf.restrictOpen` and
`AlgebraicGeometry.CompactificationOf.restrictClosed`. With these, `Rf_! ∘ j_! = Rg_!` and
`Rf_! ∘ i_* = Rh_!`.

The open `U` and the closed `Z` are given by an open immersion `j_U : U ⟶ X` and a closed
immersion `i : Z ⟶ X` with complementary images; `Z` may carry any closed subscheme structure.
`K|_U` and `K|_Z` are restriction along `j_U` and inverse image along `i`, both exact.

The formula for `Rf_!` uses no torsion hypothesis, so the bounded below case is proved for every
object of `D⁺(X_étale, Λ)`, which contains `D⁺_tors(X_étale, Λ)`, and the unbounded case for an
arbitrary ring `Λ`.

The proof applies `Rf_!` to the triangle `j_{U!} K|_U ⟶ K ⟶ i_* K|_Z ⟶` of
[Stacks, Tag 0GKL], and identifies `Rf_! ∘ j_{U!} = Rg_!` and `Rf_! ∘ i_* = Rh_!` by
`Stacks.EtaleCohomology.derivedLowerShriekRestrictOpenIso` and
`Stacks.EtaleCohomology.derivedLowerShriekRestrictClosedIso` and their unbounded versions.

## References

* [Stacks Project, Tag 0GKP](https://stacks.math.columbia.edu/tag/0GKP)
* [Stacks Project, Tag 0GKL](https://stacks.math.columbia.edu/tag/0GKL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (j : CompactificationOf (Over.mk f))
  {U Z : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] (i : Z ⟶ X) [IsClosedImmersion i]
  (hij : Set.range jU.base = (Set.range i.base)ᶜ)

include hij

/-! ### The bounded below case -/

section Plus

open Stacks.DerivedFunctor

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus

/-- **[Stacks, Tag 0GKP], bounded below case.** For `K` in `D⁺(X_étale, Λ)` there is a
distinguished triangle `Rg_!(K|_U) ⟶ Rf_! K ⟶ Rh_!(K|_Z) ⟶ Rg_!(K|_U)[1]`, where `Rf_!` is
computed through the compactification `j` of `f`, and `Rg_!` and `Rh_!` through the
compactifications `j` induces on `U` and on `Z`. -/
theorem exists_distTriang_derivedLowerShriek_openClosed_plus
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    ∃ (a : (derivedLowerShriek.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
          ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategoryPlus.obj K) ⟶
        (derivedLowerShriek.{u, r} f j Λ).obj K)
      (b : (derivedLowerShriek.{u, r} f j Λ).obj K ⟶
        (derivedLowerShriek.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K))
      (c : (derivedLowerShriek.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K) ⟶
        ((derivedLowerShriek.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
          ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategoryPlus.obj K))⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_etaleModuleExtensionByZero_directImage Λ i jU
    hij (DerivedCategory.Plus.ι.obj K)
  let KU := (etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategoryPlus.obj K
  let KZ := (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K
  obtain ⟨a₀, b₀, c₀, h₀⟩ := DerivedCategory.Plus.exists_distinguished_of_ι_objIso _ hδ
    ((etaleModuleDerivedExtensionByZero.{u, r} Λ jU).obj KU) K
    ((etaleModuleDerivedDirectImage.{u, r} Λ i).obj KZ)
    (DerivedCategory.Plus.ι.mapIso
        ((exactMapDerivedCategoryPlusIso (etaleModuleExtensionByZero.{u, r} Λ jU)).symm.app KU) ≪≫
      (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app
        (DerivedCategory.Plus.ι.obj K))
    (Iso.refl _)
    (DerivedCategory.Plus.ι.mapIso
        ((exactMapDerivedCategoryPlusIso (etaleModuleDirectImage.{u, r} Λ i)).symm.app KZ) ≪≫
      (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app
        (DerivedCategory.Plus.ι.obj K))
  exact exists_distinguished_of_objIso _
    ((derivedLowerShriek.{u, r} f j Λ).map_distinguished _ h₀) _ _ _
    ((derivedLowerShriekRestrictOpenIso.{u, r} Λ j jU).app KU) (Iso.refl _)
    ((derivedLowerShriekRestrictClosedIso.{u, r} Λ j i).app KZ)

end Plus

/-! ### The unbounded case -/

section Unbounded

/-- **[Stacks, Tag 0GKP], unbounded case.** For `K` in `D(X_étale, Λ)` there is a distinguished
triangle `Rg_!(K|_U) ⟶ Rf_! K ⟶ Rh_!(K|_Z) ⟶ Rg_!(K|_U)[1]`, where `Rf_!` is computed through
the compactification `j` of `f`, and `Rg_!` and `Rh_!` through the compactifications `j` induces
on `U` and on `Z`. -/
theorem exists_distTriang_derivedLowerShriekUnbounded_openClosed
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ∃ (a : (derivedLowerShriekUnbounded.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
          ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategory.obj K) ⟶
        (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K)
      (b : (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K ⟶
        (derivedLowerShriekUnbounded.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K))
      (c : (derivedLowerShriekUnbounded.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
          ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K) ⟶
        ((derivedLowerShriekUnbounded.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
          ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategory.obj K))⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_etaleModuleExtensionByZero_directImage Λ i jU hij K
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  have h₁ := (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).map_distinguished _
    ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.map_distinguished _ hδ)
  let KU := (etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategory.obj K
  let KZ := (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K
  let R := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  let E := etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion
  exact exists_distinguished_of_objIso _ h₁ _ _ _
    ((derivedLowerShriekUnboundedRestrictOpenIso.{u, r} Λ j jU).app KU ≪≫
      R.mapIso (E.app _ ≪≫
        (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.mapIso
        ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ jU).app KU ≪≫
          (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app K)))
    (R.mapIso (E.app K))
    ((derivedLowerShriekUnboundedRestrictClosedIso.{u, r} Λ j i).app KZ ≪≫
      R.mapIso (E.app _ ≪≫
        (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory.mapIso
        ((DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app K)))

end Unbounded

/-! ### The statement of the tag -/

/-- **[Stacks, Tag 0GKP].** Let `f : X ⟶ Y` be a morphism of schemes, quasi-compact, with a
compactification `j : X ⟶ X̄` over `Y` (for instance `f` finite type and separated with `X` and
`Y` quasi-compact and quasi-separated), let `j_U : U ⟶ X` be an open immersion and `i : Z ⟶ X` a
closed immersion with complementary images, and let `g = f ∘ j_U` and `h = f ∘ i` be the
restrictions of `f`. Let `Λ` be a ring. Then

* for every `K` in `D⁺(X_étale, Λ)`, in particular for every `K` in `D⁺_tors(X_étale, Λ)`, and
* for every `K` in `D(X_étale, Λ)`, in particular when `Λ` is torsion,

there is a distinguished triangle `Rg_!(K|_U) ⟶ Rf_! K ⟶ Rh_!(K|_Z) ⟶ Rg_!(K|_U)[1]` in
`D⁺(Y_étale, Λ)`, respectively `D(Y_étale, Λ)`. Here `Rf_! = R f̄_* ∘ j_!` is computed through
`j`, and `Rg_!` and `Rh_!` through the compactifications `j` induces on `U` and on `Z`
(`AlgebraicGeometry.CompactificationOf.restrictOpen` and
`AlgebraicGeometry.CompactificationOf.restrictClosed`). -/
@[stacks 0GKP]
theorem exists_distTriang_derivedLowerShriek_openClosed :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X),
      ∃ (a : (derivedLowerShriek.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategoryPlus.obj K) ⟶
          (derivedLowerShriek.{u, r} f j Λ).obj K)
        (b : (derivedLowerShriek.{u, r} f j Λ).obj K ⟶
          (derivedLowerShriek.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
            ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K))
        (c : (derivedLowerShriek.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
            ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus.obj K) ⟶
          ((derivedLowerShriek.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategoryPlus.obj K))⟦(1 : ℤ)⟧),
        Triangle.mk a b c ∈ distTriang _) ∧
    (∀ K : DerivedCategory (EtaleModules.{u, r} Λ X),
      ∃ (a : (derivedLowerShriekUnbounded.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategory.obj K) ⟶
          (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K)
        (b : (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K ⟶
          (derivedLowerShriekUnbounded.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
            ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K))
        (c : (derivedLowerShriekUnbounded.{u, r} (i ≫ f) (j.restrictClosed i) Λ).obj
            ((etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategory.obj K) ⟶
          ((derivedLowerShriekUnbounded.{u, r} (jU ≫ f) (j.restrictOpen jU) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ jU).mapDerivedCategory.obj K))⟦(1 : ℤ)⟧),
        Triangle.mk a b c ∈ distTriang _) :=
  ⟨exists_distTriang_derivedLowerShriek_openClosed_plus Λ j jU i hij,
    exists_distTriang_derivedLowerShriekUnbounded_openClosed Λ j jU i hij⟩

end Stacks.EtaleCohomology

end
