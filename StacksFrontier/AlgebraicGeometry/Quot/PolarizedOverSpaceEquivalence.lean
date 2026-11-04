module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeEssSurjIso
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedThetaEssSurj

/-!
# Polarized families over an algebraic space (Stacks 0E94)

Let `T` be an algebraic space over `Spec(ℤ)` and `𝒮_T` the algebraic stack of its points
(`AlgebraicGeometry.PolarizedOverSpace.Points T`, Stacks 04SU, 02ZV, 03YR). Stacks 0E94 says that
base change gives an equivalence from the category of pairs `(X ⟶ T, L)` of a proper, flat and
finitely presented morphism of algebraic spaces and an invertible module `L` ample on `X/T`
(`AlgebraicGeometry.PolarizedOverSpace.PolarizedSpacesOver`) to the category of functors over the
site from `𝒮_T` to the stack `Polarized` of polarized families of schemes (Stacks 0D1M), read over
`Spec(ℤ)`.

The functor is `F = Θ ∘ F^R`: `F^R`
(`AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor`) sends `(X ⟶ T, L)` to the
functor `(U, t) ↦ (U ×_T X ⟶ U, q^* L)` with the polarization on the small étale site, and `Θ`
(`AlgebraicGeometry.PolarizedOverSpace.toPolarizedBased`) restricts the polarization to the Zariski
site of the scheme `U ×_T X`, which is the module of Stacks 0D31.

`F^R` is faithful (`AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_faithful`),
full (`AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_full`: the morphism of
spaces by Stacks 0E93, the module isomorphism by descent of morphisms along the étale covering of
an atlas, Stacks 04W8) and essentially surjective
(`AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_essSurj`: the space by Stacks
0E93, the invertible module by Stacks 04W8, its relative ampleness read on the definition, as in
Stacks 0D3C); postcomposition with `Θ` is an equivalence
(`AlgebraicGeometry.PolarizedOverSpace.isEquivalence_postcompFunctor_toPolarizedBased`).

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.polarizedBaseChange`: the functor of Stacks 0E94.
* `AlgebraicGeometry.PolarizedOverSpace.polarizedBaseChange_isEquivalence`: **Stacks 0E94**.

## References

* [Stacks Project, Tag 0E94](https://stacks.math.columbia.edu/tag/0E94)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

variable (B : BigFppfSite.{u}) (T : AlgebraicSpaces B integerBase (hZ B))

/-- **The functor of Stacks 0E94.** A pair `(X ⟶ T, L)` of a proper, flat and finitely presented
morphism of algebraic spaces and an invertible module ample on `X/T` goes to the functor over the
site from the algebraic stack `𝒮_T` of `T` to `Polarized` sending a point `(U, t)` of `T` to the
base change `U ×_T X ⟶ U` with the pullback of `L` (Stacks 0D31); an isomorphism of pairs goes to
the induced morphism of functors. -/
abbrev polarizedBaseChange : PolarizedSpacesOver B T ⥤
    (Points T ⥤ᵇ BasedCategory.ofFunctor (polarizedProjection B ⋙ schemeOverIntegers B)) :=
  baseChangeRepresentedFunctor B T ⋙ BasedFunctor.postcompFunctor (Points T) (toPolarizedBased B)

/-- Let `T` be an algebraic space over `Spec(ℤ)` and `𝒮_T` its algebraic stack. Base change is an
equivalence from the category of pairs `(X ⟶ T, L)`, where `X ⟶ T` is a proper, flat and finitely
presented morphism of algebraic spaces and `L` is an invertible module ample on `X/T`, to the
category of functors over the site from `𝒮_T` to `Polarized`
(`Mor_{Cat/Sch_fppf}(𝒮_T, Polarized)`). -/
@[stacks 0E94 "base change is an equivalence of the polarized proper flat finitely presented \
spaces over T with Mor_{Cat/Sch_fppf}(S_T, Polarized)"]
theorem polarizedBaseChange_isEquivalence : (polarizedBaseChange B T).IsEquivalence := by
  have := isEquivalence_postcompFunctor_toPolarizedBased B (Points T)
  infer_instance

end AlgebraicGeometry.PolarizedOverSpace

end
