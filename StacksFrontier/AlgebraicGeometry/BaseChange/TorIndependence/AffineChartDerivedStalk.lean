module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedTildeStalk

/-!
# The derived stalk at a point of an affine open is the localization of the derived sections

Let `i : Spec A ⟶ X` present an affine open `U` of a scheme `X`, let `K` be an object of
`D(𝒪_X)` whose cohomology sheaves are quasi-coherent, and let `y` be a point of `Spec A`. This
module identifies the derived localization of `RΓ(U, K)` at `y` with the derived stalk of `K` at
the point `i y` of `X`:

`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, y}  ≅  K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A, y}`.

For `i` an open immersion the stalk map `𝒪_{X, i y} ⟶ 𝒪_{Spec A, y}` is an isomorphism, so the
right-hand side is the derived stalk itself read over `𝒪_{Spec A, y}`; the statement is proved
without that hypothesis, needing only that `K` restricts to the affine open with quasi-coherent
cohomology.

This is the input the affine reduction of Stacks 0DJ8 needs on the source side of the chart
cohomology map; see the module docstring of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartPrimeCriterion`.

## Main results

* `AlgebraicGeometry.tildeDerivedSectionsIso`: for `K` with quasi-coherent cohomology, the
  derived sheafification of `RΓ(U, K)` is the derived pullback of `K` to `Spec A`. This is the
  derived Spec–Γ counit of Stacks 06Z0, which is invertible on quasi-coherent cohomology.
* `AlgebraicGeometry.derivedStalkAffineSectionsIso`: the identification displayed above.

## Implementation notes

The three factors are: `AlgebraicGeometry.derivedTildeStalkIso`, which computes the derived
stalk of a derived sheafification; the counit isomorphism `tildeDerivedSectionsIso`, which
replaces that sheafification by `K|_U`; and `AlgebraicGeometry.derivedPullbackStalkIso`, the
stalk formula for a derived pullback. Only the middle one needs quasi-coherence.

Everything is at the locally small model of the derived category, which is forced:
`Stacks.Duality.derivedPullback` is not stated at a free `HasDerivedCategory` binder — see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback` for why — and
it is the functor `AlgebraicGeometry.affineDerivedSections` is built from.

No tag attribute is placed here. This is an input to Stacks 0DJ8, not a clause of it; the stalk
formula it chains together is Stacks 0098 and the counit is Stacks 06Z0, both registered
elsewhere.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X)

/-- **The derived sheafification of the derived sections is the derived pullback.** For `K` in
`D(𝒪_X)` with quasi-coherent cohomology sheaves, `RΓ(U, K)^~` is `K|_U`, where `U` is the affine
open presented by `i : Spec A ⟶ X`.

This is the counit of the derived Spec–Γ adjunction of Stacks 06Z0, which is invertible on
objects with quasi-coherent cohomology — derived pullback along `i` preserves that — read through
`AlgebraicGeometry.derivedTildeCompι`. -/
def tildeDerivedSectionsIso (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (tilde.functor A).mapDerivedCategory.obj ((affineDerivedSections i).obj K) ≅
      (Stacks.Duality.derivedPullback i).obj K :=
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj
      ((Stacks.Duality.derivedPullback i).obj K)).IsQuasicoherent := fun n =>
    Stacks.Duality.isQuasicoherent_homology_derivedPullback' i ⟨K, hK⟩ n
  haveI : IsIso ((derivedTildeGlobalSectionsAdjunction A).val.counit.app
      ((Stacks.Duality.derivedPullback i).obj K)) :=
    isIso_derivedTildeGlobalSectionsAdjunction_counit_app A
      ⟨(Stacks.Duality.derivedPullback i).obj K, hqc⟩
  ((derivedTildeCompι A).app ((affineDerivedSections i).obj K)).symm ≪≫
    asIso ((derivedTildeGlobalSectionsAdjunction A).val.counit.app
      ((Stacks.Duality.derivedPullback i).obj K))

/-- **The derived stalk at a point of an affine open is the localization of the derived
sections.** For `i : Spec A ⟶ X` presenting an affine open `U`, for `K` in `D(𝒪_X)` with
quasi-coherent cohomology sheaves and for `y` a point of `Spec A`,

`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, y} ≅ K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A, y}`.

Three factors: `derivedTildeStalkIso` computes the derived stalk of `RΓ(U,K)^~` at `y` as the
derived localization of `RΓ(U,K)`; `tildeDerivedSectionsIso` replaces `RΓ(U,K)^~` by `K|_U`; and
`derivedPullbackStalkIso` computes the derived stalk of `K|_U` at `y` as the derived base change
of the stalk of `K` at `i y` along `i^♯_y`. -/
def derivedStalkAffineSectionsIso (y : Spec A) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom A y)).functor.obj ((affineDerivedSections i).obj K) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (i.stalkMap y).hom).functor.obj ((derivedStalkFunctor (i y)).obj K) :=
  (derivedTildeStalkIso A y).app ((affineDerivedSections i).obj K) ≪≫
    (derivedStalkFunctor y).mapIso (tildeDerivedSectionsIso i K hK) ≪≫
    (derivedPullbackStalkIso i y).app K

end AlgebraicGeometry

end
