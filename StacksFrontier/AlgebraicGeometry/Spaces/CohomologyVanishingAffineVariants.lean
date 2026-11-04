module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffine
import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional

/-!
# First cohomology of a direct image along an affine morphism

Let `T` be a cohomology vanishing situation (Stacks 07UY) on an algebraic space `X`, let
`f : X' ⟶ X` be an affine morphism of algebraic spaces and let `𝓕'` be a quasi-coherent
`𝒪_{X'}`-module.  If the first cohomology of every quasi-coherent `𝒪_X`-module with sections in
the universe of the structure sheaf vanishes, the higher direct images of `𝓕'` vanish on every
chart and `f_*` sends injective modules to modules acyclic for the global sections on `X`, then
the first right derived functor of `f_*` followed by the global sections on `X` vanishes at `𝓕'`.
This is a form of clause (1) of Stacks 07V0.

## Main results

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.isZero_firstCohomology_of_isAffineHom'`:
  the vanishing above.

## References

* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace CohomologyVanishingSituation

/-- In the situation of Stacks 07UY, let `f : X' ⟶ X` be an affine morphism of algebraic spaces
and let `𝓕'` be a quasi-coherent `𝒪_{X'}`-module.  If the first cohomology of every
quasi-coherent `𝒪_X`-module with sections in the universe of the structure sheaf vanishes, the
higher direct images of `𝓕'` vanish on every chart and `f_*` sends injective modules to modules
acyclic for the global sections on `X`, then `R¹(Γ(X, -) ∘ f_*)(𝓕') = 0`. -/
theorem isZero_firstCohomology_of_isAffineHom' (T : CohomologyVanishingSituation.{u, m})
    {X' : AlgebraicSpaces T.site T.base T.containsBase} (f : X' ⟶ T.space)
    (hf : IsAffineHom T.site T.base T.containsBase f.hom)
    (F : Modules.{u, u} T.site T.base T.containsBase X'.1 X'.2)
    (hF : F.IsQuasicoherentOnSite)
    (h07UY : FirstCohomologyVanishingAtRingUniverse T.site T.base T.containsBase T.space)
    (h03DW : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage T.site T.base T.containsBase f
      (relativelyRepresentable_of_isAffineHom T.site T.base T.containsBase f hf) F n)
    (h072Z : AcyclicPushforwardOfInjective T.site T.base T.containsBase f) :
    have := hasInjectiveResolutions_modules T.site T.base T.containsBase X'.1 X'.2
    have := enoughInjectives_modules T.site T.base T.containsBase T.space.1 T.space.2
    IsZero (((modulePushforward T.site T.base T.containsBase f ⋙
      globalSectionsFunctor.{u + 1, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite T.site T.base T.containsBase
          T.space.1 T.space.2).O))).rightDerived 1).obj F) := by
  have := hasInjectiveResolutions_modules T.site T.base T.containsBase X'.1 X'.2
  have := enoughInjectives_modules T.site T.base T.containsBase T.space.1 T.space.2
  exact IsZero.of_iso
    (h07UY _ (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional T.site T.base
      T.containsBase f hf F hF))
    (cohomologyCollapseIsoOfIsAffineHom T.site T.base T.containsBase f hf F h03DW h072Z 1)

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end

end
