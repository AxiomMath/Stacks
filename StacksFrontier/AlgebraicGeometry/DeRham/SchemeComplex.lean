module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham complex of a morphism of schemes

For a morphism of schemes `f : X ⟶ S` the relative de Rham complex is the de Rham complex of
the structure sheaf of `X` over the inverse image of the structure sheaf of `S`,

`Ω^•_{X/S} = Ω^•_{𝒪_X / f^{-1}𝒪_S} : Ω^0_{X/S} → Ω^1_{X/S} → Ω^2_{X/S} → ⋯`,

a cochain complex of sheaves of `f^{-1}𝒪_S`-modules on `X` whose degree-`p` term is the sheaf
`Ω^p_{X/S}` of relative differential `p`-forms and whose degree-zero differential is the
universal relative derivation. It is obtained by instantiating the de Rham complex of a
morphism of sheaves of commutative rings at the structural map `f^{-1}𝒪_S ⟶ 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras`: the tensor, exterior and symmetric algebras of
  the sheaf of relative differentials `Ω_{X/S}` of a morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex`: **the relative de Rham complex** `Ω^•_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`: the degree-zero
  identification `Ω^0_{X/S} ≅ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras_exterior`: the exterior algebra of the package is
  the algebra `Ω^•_{X/S}` of relative differential forms, so the forms appearing in the de Rham
  complex are the ones of
  `StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms` and not a second notion.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_X` and
  `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d`: the degree-`p` term of the relative de Rham
  complex is `Ω^p_{X/S}`, read as a sheaf of `f^{-1}𝒪_S`-modules, and the arrow out of it is the
  relative de Rham differential.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_degreeZero`: on a degree-zero form `b · 1` the
  first differential is the universal relative derivation of `b`.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_eq`: every de Rham differential on `Ω^•_{X/S}`
  assembles into this complex, so `Ω^•_{X/S}` does not depend on a choice of differential.

## Implementation notes

The terms are sheaves of `f^{-1}𝒪_S`-modules and not of `𝒪_X`-modules: the de Rham
differential is only `f^{-1}𝒪_S`-linear, since already in degree zero the Leibniz rule gives
`d(b b') = b d b' + b' d b`. So `deRhamComplex_X` identifies the degree-`p` term with the
restriction of scalars of `Ω^p_{X/S}` along `f^{-1}𝒪_S ⟶ 𝒪_X` rather than with `Ω^p_{X/S}`
itself.

Everything is stated for `Scheme.{u}`, whose underlying ringed space is `RingedSpace.{u, u}`: a
ringed space whose underlying topological space and whose sections lie in one universe. That is
the universe the de Rham complex of a morphism of sheaves of rings is available at, for the
reason recorded in `StacksFrontier.Topology.Sheaves.Modules.DeRham` — the exterior powers of the
sheaf of relative differentials are supplied by
`SheafOfModules.TensorExteriorSymmetricAlgebras`, whose site, ring and module universes all
agree. A scheme has no slot for a larger universe of sections once its space is fixed, so no
universe is narrowed here and, unlike at the site level, no universe arguments have to be
supplied by hand: the definitions being instantiated are already stated at `RingedSpace.{u, u}`,
so there is no constraint of the form `max u ?v =?= u` left for the elaborator to solve.

The structural map is `AlgebraicGeometry.inverseImageStructureMap`, the map already used to
define the sheaf of relative differentials of a morphism of schemes, so `Ω^•_{X/S}` is built
over the same morphism of sheaves of rings as `Ω_{X/S}` rather than over a second spelling of
it. This is what makes `deRhamAlgebras_exterior` and `deRhamComplex_X` hold by definition.

## References

* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Section 50.2](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The tensor, exterior and symmetric algebras of the sheaf of relative differentials
`Ω_{X/S}` of a morphism of schemes, as the package of Stacks Section 17.21 attached to it by
`AlgebraicGeometry.SheafOfModules.differentialAlgebras`. Its exterior powers are the sheaves of
relative differential forms. -/
noncomputable abbrev deRhamAlgebras :
    _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (relativeDifferentials f) :=
  AlgebraicGeometry.SheafOfModules.differentialAlgebras (inverseImageStructureMap f)

/-- The exterior algebra of the sheaf of relative differentials of a morphism of schemes is the
algebra `Ω^•_{X/S}` of relative differential forms: the de Rham complex below is built on the
differential forms of
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms`. -/
theorem deRhamAlgebras_exterior :
    (deRhamAlgebras f).exterior = relativeDifferentialFormsAlgebra f :=
  rfl

/-- **The relative de Rham complex** `Ω^•_{X/S}` of a morphism of schemes `f : X ⟶ S`: the de
Rham complex of `𝒪_X` over `f^{-1}𝒪_S`, a cochain complex of sheaves of `f^{-1}𝒪_S`-modules
on `X`. -/
@[stacks 0FKQ "the morphism-of-schemes case"]
noncomputable def deRhamComplex :
    CochainComplex (_root_.SheafOfModules.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  AlgebraicGeometry.SheafOfModules.relativeDeRhamComplex (deRhamAlgebras f)

/-- The degree-`p` term of the relative de Rham complex is the sheaf `Ω^p_{X/S}` of relative
differential `p`-forms, read as a sheaf of `f^{-1}𝒪_S`-modules along the structural map. -/
@[simp] theorem deRhamComplex_X (p : ℕ) :
    (deRhamComplex f).X p =
      (_root_.SheafOfModules.restrictScalars
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom
            (φ := inverseImageStructureMap f))).obj (relativeDifferentialForms f (p : ℤ)) :=
  AlgebraicGeometry.SheafOfModules.deRhamComplex_X _ _ p

/-- The arrow of the relative de Rham complex out of degree `p` is the relative de Rham
differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`. -/
@[simp] theorem deRhamComplex_d (p : ℕ) :
    (deRhamComplex f).d p (p + 1) =
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential p :=
  AlgebraicGeometry.SheafOfModules.deRhamComplex_d _ _ p

/-- **Every de Rham differential on `Ω^•_{X/S}` assembles into the relative de Rham complex**,
so the complex does not depend on a choice of differential: by Tag 0FKM there is exactly one. -/
theorem deRhamComplex_eq
    (D : AlgebraicGeometry.SheafOfModules.DeRhamDifferential (deRhamAlgebras f)) :
    AlgebraicGeometry.SheafOfModules.deRhamComplex (deRhamAlgebras f) D = deRhamComplex f :=
  AlgebraicGeometry.SheafOfModules.deRhamComplex_eq_relativeDeRhamComplex _ D

/-- The degree-zero identification `Ω^0_{X/S} ≅ 𝒪_X`: the degree-zero piece of an exterior
algebra is free of rank one on the unit. -/
noncomputable def relativeDifferentialFormsZeroIso :
    relativeDifferentialForms f 0 ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  (deRhamAlgebras f).exteriorPieceZeroIsoUnit

/-- In degree zero the differential of the relative de Rham complex is the universal relative
derivation: it carries the degree-zero form `b · 1` attached to a local section `b` of `𝒪_X` to
the degree-one form `d b`. -/
theorem deRhamComplex_degreeZero (U : (X.Opens)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    HEq (((deRhamComplex f).d 0 1).val.app U
        (b • (deRhamAlgebras f).exterior.one.eval U))
      ((deRhamAlgebras f).exteriorGenerator.val.app U
        (((universalRelativeDerivation f).app U).d b)) :=
  AlgebraicGeometry.SheafOfModules.deRhamComplex_degreeZero _ _ U b

end AlgebraicGeometry.Scheme.Hom

end
