module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DeRhamOrderOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderCategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative de Rham complex as a complex of differential operators

Let `a : X ⟶ S` be a morphism of schemes. The de Rham differentials of `Ω^•_{X/S}` are not
`𝒪_X`-linear, so the complex `Ω^•_{X/S}` is not a complex of `𝒪_X`-modules; it is a complex in
the category `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory a` of finite-order
differential operators on `X/S`, since each `Ω^p_{X/S}` is quasi-coherent and each differential
is an operator of order at most one.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpTerm`: the sheaf `Ω^p_{X/S}` of relative differential
  `p`-forms, as an object of the category of finite-order differential operators on `X/S`.
* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpDifferential`: the de Rham differential
  `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`, as a morphism of that category.
* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpComplex`: **the relative de Rham complex
  `Ω^•_{X/S}`, as a cochain complex in the category of finite-order differential operators on
  `X/S`.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpDifferential_coe`: the operator underlying the
  differential is the de Rham differential of
  `StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex`, so this complex is built on the same
  differentials as `AlgebraicGeometry.Scheme.Hom.deRhamComplex` and not on a second notion.
* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpDifferential_comp_self`: consecutive differentials
  compose to zero.

## Implementation notes

The terms are stated as `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms a (p : ℤ)`, which
is the degree-`p` exterior power of the sheaf of relative differentials, so its quasi-coherence is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorPower` at the quasi-coherent sheaf
`Ω_{X/S}`. The object is an `abbrev` so that the projection to the underlying module reduces: the
operator underlying the differential is literally
`AlgebraicGeometry.SheafOfModules.deRhamGlobalOp`, whose source and target are the exterior powers
of the package `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras a`, and those are the sheaves
`Ω^p_{X/S}` by definition.

The indexing is `ℕ`, matching `AlgebraicGeometry.Scheme.Hom.deRhamComplex`: the de Rham complex
of a morphism of schemes is a cochain complex concentrated in non-negative degrees.

## References

* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0G3Y](https://stacks.math.columbia.edu/tag/0G3Y)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- **The sheaf `Ω^p_{X/S}` of relative differential `p`-forms, as an object of the category of
finite-order differential operators on `X/S`.** It is quasi-coherent, being an exterior power of
the quasi-coherent sheaf `Ω_{X/S}`. -/
@[ega "IV 16.6.1"]
noncomputable abbrev deRhamDiffOpTerm (p : ℕ) : FiniteOrderDifferentialOperatorCategory a where
  module := relativeDifferentialForms a (p : ℤ)
  isQuasicoherent := Scheme.Modules.isQuasicoherent_exteriorPower (relativeDifferentials a) p

/-- **The de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`, as a morphism of the category of
finite-order differential operators on `X/S`**: by Tag 0G3Y it is a differential operator of
order at most one relative to `a⁻¹𝒪_S ⟶ 𝒪_X`. -/
noncomputable def deRhamDiffOpDifferential (p : ℕ) :
    deRhamDiffOpTerm a p ⟶ deRhamDiffOpTerm a (p + 1) :=
  ⟨SheafOfModules.deRhamGlobalOp (deRhamAlgebras a) p, 1,
    deRhamGlobalOp_isGlobalDiffOpOfOrder_one a p⟩

/-- The operator underlying the de Rham differential is the de Rham differential of the relative
de Rham complex of `a`, read on local sections. -/
theorem deRhamDiffOpDifferential_coe (p : ℕ) :
    (deRhamDiffOpDifferential a p).1 = SheafOfModules.deRhamGlobalOp (deRhamAlgebras a) p :=
  rfl

/-- **The de Rham differentials compose to zero**, because they do so as morphisms of sheaves of
`a⁻¹𝒪_S`-modules and composition in the category of finite-order differential operators is
composition of the operators on local sections. -/
theorem deRhamDiffOpDifferential_comp_self (p : ℕ) :
    deRhamDiffOpDifferential a p ≫ deRhamDiffOpDifferential a (p + 1) = 0 := by
  apply Subtype.ext
  funext U
  ext s
  exact SheafOfModules.hom_congr_app_apply
    (SheafOfModules.deRhamDifferentialHom_comp_self (deRhamAlgebras a) p) U s

/-- **The relative de Rham complex `Ω^•_{X/S}` of a morphism of schemes, as a cochain complex in
the category of finite-order differential operators on `X/S`.** Its terms are the sheaves of
relative differential forms and its arrows are the de Rham differentials; this is the form in
which `Ω^•_{X/S}` is a complex of objects rather than a complex of `a⁻¹𝒪_S`-modules, and the one
the box product of [Stacks, Tag 0G46] accepts. -/
noncomputable def deRhamDiffOpComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℕ :=
  CochainComplex.of (deRhamDiffOpTerm a) (deRhamDiffOpDifferential a)
    (deRhamDiffOpDifferential_comp_self a)

/-- The degree-`p` term of the complex is `Ω^p_{X/S}`. -/
@[simp] theorem deRhamDiffOpComplex_X (p : ℕ) :
    (deRhamDiffOpComplex a).X p = deRhamDiffOpTerm a p := rfl

/-- The arrow of the complex out of degree `p` is the de Rham differential. -/
@[simp] theorem deRhamDiffOpComplex_d (p : ℕ) :
    (deRhamDiffOpComplex a).d p (p + 1) = deRhamDiffOpDifferential a p :=
  CochainComplex.of_d (deRhamDiffOpTerm a) (deRhamDiffOpDifferential a) p

end AlgebraicGeometry.Scheme.Hom

end
