module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSectionsAffineOpen

/-!
# The stalk of a Fitting ideal sheaf of the relative differentials

Let `f : X ⟶ S` be locally of finite type, let `Spec A = U ⊆ X` and `Spec R = V ⊆ S` be affine
opens with `f(U) ⊆ V`, and let `x ∈ U`. The stalk at `x` of the `r`-th Fitting ideal sheaf of
`Ω_{X/S}` is the image in `𝒪_{X,x}` of the `r`-th Fitting ideal of the module `Ω_{A/R}`.

## Main definitions

* `AlgebraicGeometry.sectionsRelativeDifferentialsEquiv`: the sections of `Ω_{X/S}` over an
  affine open `Spec A = U` lying over `Spec R = V`, identified with `Ω_{A/R}`.

## Main results

* `AlgebraicGeometry.moduleFinite_kaehlerDifferential_appLE`: for `f` locally of finite type,
  `Ω_{A/R}` is a finite `A`-module.
* `AlgebraicGeometry.stalk_fittingIdeal_relativeDifferentials`: the stalk at `x` of the `r`-th
  Fitting ideal sheaf of `Ω_{X/S}` is the image in `𝒪_{X,x}` of the `r`-th Fitting ideal of
  `Ω_{A/R}`.

## References

* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 0C3F](https://stacks.math.columbia.edu/tag/0C3F)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The sections of the sheaf of relative differentials over an affine open `Spec A = U` lying
over an affine open `Spec R = V` are the module of differentials `Ω_{A/R}`. -/
noncomputable def sectionsRelativeDifferentialsEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    Γ(Scheme.Hom.relativeDifferentials f, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, V)] :=
  let := Stacks.Smooth.algebraAppLE f hUV
  (sectionsLinearEquivOfIso (Scheme.Hom.cotangentSheafIso f) U).trans
    (Stacks.Smooth.cotangentSectionsEquiv f hU hV hUV).symm

/-- For a morphism locally of finite type, the module of differentials of the sections over an
affine open is a finite module. -/
theorem moduleFinite_kaehlerDifferential_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    Module.Finite Γ(X, U) Ω[Γ(X, U)⁄Γ(S, V)] := by
  let := Stacks.Smooth.algebraAppLE f hUV
  have hfin : Module.Finite Γ(X, U) Γ(Scheme.Hom.relativeDifferentials f, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ hU
  exact Module.Finite.of_surjective (sectionsRelativeDifferentialsEquiv f hU hV hUV).toLinearMap
    (sectionsRelativeDifferentialsEquiv f hU hV hUV).surjective

/-- **The stalk of a Fitting ideal sheaf of the relative differentials.** For `f : X ⟶ S`
locally of finite type, affine opens `Spec A = U ⊆ X` and `Spec R = V ⊆ S` with `f(U) ⊆ V`, and
`x ∈ U`, the stalk at `x` of the `r`-th Fitting ideal sheaf of `Ω_{X/S}` is the image in
`𝒪_{X,x}` of the `r`-th Fitting ideal of `Ω_{A/R}`. -/
theorem stalk_fittingIdeal_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℤ) (x : X) (U : X.affineOpens) (hxU : x ∈ U.1)
    {V : S.Opens} (hV : IsAffineOpen V) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ V) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    letI := moduleFinite_kaehlerDifferential_appLE f U.2 hV hUV
    IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) r) x =
      (_root_.fittingIdeal (R := Γ(X, U.1)) (M := Ω[Γ(X, U.1)⁄Γ(S, V)]) r).map
        (X.presheaf.germ U.1 x hxU).hom := by
  let := Stacks.Smooth.algebraAppLE f hUV
  have := moduleFinite_kaehlerDifferential_appLE f U.2 hV hUV
  have hfin : Module.Finite Γ(X, U.1) Γ(Scheme.Hom.relativeDifferentials f, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections _ U.2
  have hmod : _root_.fittingIdeal (R := Γ(X, U.1))
      (M := Γ(Scheme.Hom.relativeDifferentials f, U.1)) r =
      _root_.fittingIdeal (R := Γ(X, U.1)) (M := Ω[Γ(X, U.1)⁄Γ(S, V)]) r :=
    fittingIdeal_eq_of_linearEquiv_int (sectionsRelativeDifferentialsEquiv f U.2 hV hUV) r
  rw [IdealSheafData.stalk_eq_map_germ _ x U hxU,
    fittingIdeal_ideal (Scheme.Hom.relativeDifferentials f) r U, hmod]

end AlgebraicGeometry

end
