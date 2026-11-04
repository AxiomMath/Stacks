module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexComparison
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenFormsMapSections

/-!
# The relative de Rham complex on an affine open, compared with the algebraic one

Let `f : X ⟶ S` be a morphism of schemes, let `U ⊆ X` and `V ⊆ S` be affine opens with
`U ≤ f^{-1}V`, and write `A := Γ(X, U)`, `R := Γ(S, V)` and `φ := f.appLE V U e : R ⟶ A`. This file
identifies the sections over `U` of the relative differential `p`-forms of `f` with the degree-`p`
term of the algebraic de Rham complex `Ω^•_{A/R}`, in every degree:

`Γ(Ω^p_{X/S}, U) ≅ ⋀^p_A Ω[A⁄R]`.

Here `X` and `S` are arbitrary schemes and only the two opens are affine;
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamSectionsComplexIso` is the corresponding
statement when `X` and `S` are affine and `f` is `Spec φ`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.kaehlerSectionsLinearMap` and
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.kaehlerSectionsEquiv`: the degree-one comparison
  `Ω[A⁄R] ≅ Γ(Ω_{X/S}, U)`, [Stacks, Tag 01UT] over a pair of affine opens, as an `A`-linear map
  and as an `A`-linear equivalence.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`: the degreewise comparison
  `Γ(Ω^p_{X/S}, U) ≅ ⋀^p_A Ω[A⁄R]`, in every degree `p`.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.bijective_kaehlerSectionsLinearMap`: the degree-one
  comparison is bijective.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

/-- The degree-one comparison over a pair of affine opens, as a `Γ(X, U)`-linear map: the Kähler
differentials of `Γ(S, V) ⟶ Γ(X, U)` map to the sections of `Ω_{X/S}` over `U`. This is
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` read as a map of
`Γ(X, U)`-modules. -/
def kaehlerSectionsLinearMap :
    ↥(CommRingCat.KaehlerDifferential (f.appLE V U e)) →ₗ[Γ(X, U)]
      Γ(Scheme.Hom.relativeDifferentials f, U) where
  toFun := (AffineDifferentials.kaehlerToSections f V U e).hom
  map_add' _ _ := map_add _ _ _
  map_smul' r x := map_smul _ r x

include hU hV in
/-- The degree-one comparison `kaehlerSectionsLinearMap` is bijective when `U` and `V` are
affine. -/
theorem bijective_kaehlerSectionsLinearMap :
    Function.Bijective (kaehlerSectionsLinearMap f e) :=
  have := AffineDifferentialsIso.isIso_kaehlerToSections f hU e hV
  ConcreteCategory.bijective_of_isIso (AffineDifferentials.kaehlerToSections f V U e)

include hU hV in
/-- The degree-one comparison over a pair of affine opens, as a `Γ(X, U)`-linear equivalence
`Ω[Γ(X,U)⁄Γ(S,V)] ≅ Γ(Ω_{X/S}, U)`. -/
def kaehlerSectionsEquiv :
    ↥(CommRingCat.KaehlerDifferential (f.appLE V U e)) ≃ₗ[Γ(X, U)]
      Γ(Scheme.Hom.relativeDifferentials f, U) :=
  LinearEquiv.ofBijective _ (bijective_kaehlerSectionsLinearMap f hU hV e)

include hU hV in
/-- The degreewise comparison of the relative de Rham complex on an affine open with the algebraic
one: for affine opens `U ⊆ X` and `V ⊆ S` with `U ≤ f^{-1}V`, the sections over `U` of the relative
differential `p`-forms of `f` are the `p`-th exterior power of the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)`,

`Γ(Ω^p_{X/S}, U) ≅ ⋀^p_{Γ(X,U)} Ω[Γ(X,U)⁄Γ(S,V)]`,

in every degree. The right-hand side is the carrier of the degree-`p` term of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex (f.appLE V U e)`, by
`ringDeRhamComplex_X_carrier`. -/
def formsSectionsIso (p : ℕ) :
    ModuleCat.of Γ(X, U) Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U) ≅
      ModuleCat.of Γ(X, U)
        (⋀[Γ(X, U)]^p ↥(CommRingCat.KaehlerDifferential (f.appLE V U e))) :=
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentials f
  Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
      (Scheme.Hom.relativeDifferentials f) hU
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p ≪≫
    (Stacks.AffineExteriorPower.exteriorPowerCongr
      (kaehlerSectionsEquiv f hU hV e).symm p).toModuleIso



end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
