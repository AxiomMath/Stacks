module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.Duality.AdequateSheafOfModules

/-!
# The bounded below derived category of adequate modules over an affine base

Let `U = Spec A` be affine. Adequacy cuts out a weak Serre subcategory `Adeq(𝒪)` of the
`𝒪`-modules on the big `τ`-site over `U`, so there are two bounded below derived categories to
compare: `D⁺(Adeq(𝒪))`, the derived category of the abelian category `Adeq(𝒪)`, and
`D⁺_{Adeq}(𝒪)`, the strictly full subcategory of `D(𝒪)` of bounded below complexes whose
cohomology sheaves are adequate. The inclusion `Adeq(𝒪) ⥤ Mod(𝒪)`, being exact, induces the
canonical comparison functor from the first to the second; [Stacks, Tag 06ZV] asserts that it
is an equivalence.

The comparison is proved to be an equivalence given a right adjoint `Ψ` of the derived inclusion on
bounded below objects that preserves boundedness below (the source's `RA`, the total right derived
functor of the adequator of [Stacks, Tag 06ZS]), whose unit and counit are invertible on single
adequate modules (the source's key fact, [Stacks, Tag 06ZU]), and given the closure of adequacy
under kernels, cokernels and finite products ([Stacks, Tag 06VQ] (1)), which makes `Adeq(𝒪)`
abelian. The passage from single modules to bounded below complexes is the source's spectral
sequence argument via [Stacks, Tag 015J].

## Main results

* `Stacks.Adequate.isEquivalence_adequateBoundedBelowComparison` — **[Stacks, Tag 06ZV]**: the
  comparison functor `D⁺(Adeq(𝒪)) ⥤ D⁺_{Adeq}(𝒪)` is an equivalence.
* `Stacks.Adequate.adequateBoundedBelowEquivalence` — the same read as an equivalence of
  categories, `D⁺(Adeq(𝒪)) ≌ D⁺_{Adeq}(𝒪)`.
* `Stacks.Adequate.adequateBoundedBelowEquivalence_functor` and
  `Stacks.Adequate.adequateBoundedBelowEquivalence_functor_ι` — its functor is the canonical
  comparison functor, and that functor is the degreewise action of the inclusion
  `Adeq(𝒪) ⥤ Mod(𝒪)`.
* `Stacks.Adequate.adequateBoundedBelowEquivalence_inverse` — its quasi-inverse is the inverse of
  the comparison functor.

## References

* [Stacks Project, Tag 06ZV](https://stacks.math.columbia.edu/tag/06ZV)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m w w'

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))
  [HasSheafify B.topology AddCommGrpCat.{m}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(adequate.{u, m} B).ContainsZero] [(adequate.{u, m} B).IsClosedUnderKernels]
  [(adequate.{u, m} B).IsClosedUnderCokernels]
  [(adequate.{u, m} B).IsClosedUnderFiniteProducts]
  [PreservesFiniteLimits (adequate.{u, m} B).ι]
  [PreservesFiniteColimits (adequate.{u, m} B).ι]
  [HasDerivedCategory.{w} (SheafOfModules.{m} B.structureSheaf)]
  [HasDerivedCategory.{w'} (adequate.{u, m} B).FullSubcategory]
  (Ψ : DerivedCategory.Plus (SheafOfModules.{m} B.structureSheaf) ⥤
    DerivedCategory.Plus (adequate.{u, m} B).FullSubcategory)
  [Ψ.CommShift ℤ] [Ψ.IsTriangulated]
  (adj : (adequate.{u, m} B).ι.mapDerivedCategoryPlus ⊣ Ψ) [adj.CommShift ℤ]
  (hΨ : ∀ (L : DerivedCategory.Plus (SheafOfModules.{m} B.structureSheaf)) (n : ℤ),
    L.IsGE n → (Ψ.obj L).IsGE n)
  (hunit : ∀ F : (adequate.{u, m} B).FullSubcategory,
    IsIso (adj.unit.app
      ((DerivedCategory.Plus.singleFunctor (adequate.{u, m} B).FullSubcategory 0).obj F)))
  (hcounit : ∀ F : SheafOfModules.{m} B.structureSheaf, IsAdequate B F →
    IsIso (adj.counit.app
      ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{m} B.structureSheaf) 0).obj F)))

include Ψ adj hΨ hunit hcounit

/-- **[Stacks, Tag 06ZV].** For `U = Spec A` affine, the canonical comparison functor
`D⁺(Adeq(𝒪)) ⥤ D⁺_{Adeq}(𝒪)` — the inclusion `Adeq(𝒪) ⥤ Mod(𝒪)` applied degreewise to
complexes — is an equivalence. -/
@[stacks 06ZV "the full statement, that the canonical comparison functor
`D⁺(Adeq(𝒪)) ⥤ D⁺_Adeq(𝒪)` of the equation (46.7.5.1) of Tag 06VV is an equivalence. Assumed:
a right adjoint `Ψ` of the derived inclusion on bounded below objects together with its
preservation of boundedness below (`adj`, `hΨ`), which is the source's `RA`, available because
the adequator of Tag 06ZS is left exact and `Mod(𝒪)` has enough injectives; the source's key
fact that the adjunction maps are quasi-isomorphisms on the SINGLE modules (`hunit`,
`hcounit`), which is Tag 06ZU together with the moreover clause of Tag 06ZS; and the closure of
adequacy under kernels, cokernels and finite products, Tag 06VQ (1), which makes `Adeq(𝒪)`
abelian. The passage from the key fact on single modules to all of `D⁺`, which is the source's
spectral sequence argument via Tag 015J, is proved"]
public theorem isEquivalence_adequateBoundedBelowComparison :
    (DerivedCategoryB.boundedBelowComparison (adequate.{u, m} B)).IsEquivalence :=
  DerivedCategoryB.isEquivalence_boundedBelowComparison (adequate.{u, m} B) Ψ adj hΨ hunit
    fun F hF ↦ hcounit F hF

/-- **[Stacks, Tag 06ZV]** as an equivalence of categories:
`D⁺(Adeq(𝒪)) ≌ D⁺_{Adeq}(𝒪)` for `U = Spec A` affine. -/
@[stacks 06ZV "the equivalence as data, `D⁺(Adeq(𝒪)) ≌ D⁺_Adeq(𝒪)`, under the hypotheses of
`Stacks.Adequate.isEquivalence_adequateBoundedBelowComparison`; its functor is the canonical
comparison functor by `Stacks.Adequate.adequateBoundedBelowEquivalence_functor`"]
public def adequateBoundedBelowEquivalence :
    DerivedCategory.Plus (adequate.{u, m} B).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus (adequate.{u, m} B)).FullSubcategory :=
  DerivedCategoryB.boundedBelowEquivalence (adequate.{u, m} B) Ψ adj hΨ hunit
    fun F hF ↦ hcounit F hF

/-- The functor of the equivalence of [Stacks, Tag 06ZV] is the canonical comparison functor. -/
public theorem adequateBoundedBelowEquivalence_functor :
    (adequateBoundedBelowEquivalence B Ψ adj hΨ hunit hcounit).functor =
      DerivedCategoryB.boundedBelowComparison (adequate.{u, m} B) :=
  rfl

/-- The functor of the equivalence of [Stacks, Tag 06ZV], followed by the inclusion of
`D⁺_{Adeq}(𝒪)` into `D(𝒪)`, is the degreewise action of the inclusion `Adeq(𝒪) ⥤ Mod(𝒪)`: the
equivalence is the functor of the source's equation (46.7.5.1). -/
public theorem adequateBoundedBelowEquivalence_functor_ι :
    (adequateBoundedBelowEquivalence B Ψ adj hΨ hunit hcounit).functor ⋙
        (DerivedCategoryB.derivedCategoryBPlus (adequate.{u, m} B)).ι =
      DerivedCategory.Plus.ι ⋙ (adequate.{u, m} B).ι.mapDerivedCategory :=
  rfl

/-- The quasi-inverse of the equivalence of [Stacks, Tag 06ZV] is the inverse of the canonical
comparison functor. -/
public theorem adequateBoundedBelowEquivalence_inverse :
    letI := isEquivalence_adequateBoundedBelowComparison B Ψ adj hΨ hunit hcounit
    (adequateBoundedBelowEquivalence B Ψ adj hΨ hunit hcounit).inverse =
      (DerivedCategoryB.boundedBelowComparison (adequate.{u, m} B)).inv :=
  rfl

end Stacks.Adequate

end
