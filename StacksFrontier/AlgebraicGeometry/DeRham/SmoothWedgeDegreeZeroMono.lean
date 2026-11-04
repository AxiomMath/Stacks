module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal
public import StacksFrontier.AlgebraicGeometry.Modules.WedgeDegreeZeroMono

/-!
# The top step of the filtration of `Ω^n_{X/S}` is its source, for `f` smooth

Let `f : X ⟶ Y` be a smooth morphism of schemes over a base `S`.
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorFiltration` filters `Ω^n_{X/S}` by the
images of the wedge-product morphisms

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^{n-k}Ω_{X/S} ⟶ Ω^n_{X/S}`,

and in the **top** step `k = n` the complementary degree is `0`. **This file proves that the
wedge-product morphism of that bidegree is a monomorphism**, so that the top step *is* its source
rather than merely a quotient of it:

`⋀^n(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S} ⟶ Ω^n_{X/S}`  is a monomorphism.

Nothing is assumed beyond smoothness of `f`: no splitting of the transitivity sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is chosen and no open is fixed.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHom_of_eq_zero`: **the
  wedge-product morphism at complementary degree zero is a monomorphism**, for `f` smooth.
* `AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHomOfEq_of_eq_zero`: the same
  at the transported total degree, which is the spelling
  `SheafOfModules.exteriorImageFiltration_of_le` presents the step of the filtration in, where
  the complementary degree of the top step appears as `n - n` and not as `0`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
  PresheafOfModules TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- The short complex `f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}` splits on an open neighbourhood of every
point, for `f` smooth. -/
private theorem locally_split_relativeDifferentialsShortComplex (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth f] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (_root_.SheafOfModules.openSubspaceShortComplex
      (X := X.toRingedSpace) U (T := relativeDifferentialsShortComplex f g)).Splitting :=
  fun x => (exists_nonempty_splitting_relativeDifferentialsRestrict f g x).imp
    (fun U h => ⟨h.1, h.2.map (fun sp =>
      _root_.SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor U sp)⟩)

/-- **The wedge-product morphism `⋀^p(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S} ⟶ Ω^p_{X/S}` is a
monomorphism**, for `f : X ⟶ Y` smooth over a base `S`. Equivalently: the top step of the
filtration of `Ω^p_{X/S}` by the forms pulled back from `Y` is its source, not merely a quotient
of it. The complementary degree `q` is given with the equation `q = 0`. -/
theorem mono_relativeDifferentialsProdWedgeHom_of_eq_zero (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f]
    (p q : ℕ) (hq : q = 0) :
    Mono (_root_.SheafOfModules.prodWedgeHom
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₁)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂)
      (relativeDifferentialsShortComplex f g).f
      (𝟙 (relativeDifferentialsShortComplex f g).X₂) p q) :=
  _root_.SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split _ _ p q hq
    (locally_split_relativeDifferentialsShortComplex f g)

/-- `AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHom_of_eq_zero` at the
transported total degree, which is the spelling `SheafOfModules.exteriorImageFiltration_of_le`
presents the steps of the filtration in. -/
theorem mono_relativeDifferentialsProdWedgeHomOfEq_of_eq_zero (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f]
    (p q n : ℕ) (hq : q = 0) (h : p + q = n) :
    Mono (_root_.SheafOfModules.prodWedgeHomOfEq
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₁)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂)
      (relativeDifferentialsShortComplex f g).f
      (𝟙 (relativeDifferentialsShortComplex f g).X₂) p q n h) :=
  _root_.SheafOfModules.mono_prodWedgeHomOfEq_id_right_of_locally_split _ _ p q n hq h
    (locally_split_relativeDifferentialsShortComplex f g)

end AlgebraicGeometry.Scheme.Hom

end
