module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.HomologyZero

/-!
# The cotangent complex of a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces. Such an `f` carries its
structure-sheaf component `𝒪_S ⟶ f_* 𝒪_X`, and the morphism of sheaves of commutative rings
`f⁻¹𝒪_S ⟶ 𝒪_X` adjoint to it under `f⁻¹ ⊣ f_*` lives on the site of open subsets of `X`. The
cotangent complex `L_f = L_{X/S}` of `f` is by definition the cotangent complex of that morphism
of sheaves of rings, so it is a complex of sheaves of `𝒪_X`-modules.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex` is `L_{X/S}`, a cochain complex of
  sheaves of `𝒪_X`-modules.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplexDerived` is `L_{X/S}` regarded as an
  object of the derived category of sheaves of `𝒪_X`-modules.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_homologyZeroIso` is the canonical
  identification `H⁰(L_{X/S}) ≅ Ω_{X/S}`.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_eq` identifies `L_{X/S}` with the
  cotangent complex of the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_isZero_pos` records that `L_{X/S}`
  vanishes in positive cohomological degrees.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_homologyZeroIso_hom_postcomp` pins the
  identification `H⁰(L_{X/S}) ≅ Ω_{X/S}` down: it is the unique isomorphism carrying the
  universal derivation of `H⁰(L_{X/S})` to the universal derivation `d : 𝒪_X ⟶ Ω_{X/S}`.

## Implementation notes

`f⁻¹𝒪_S` and the morphism `f⁻¹𝒪_S ⟶ 𝒪_X` are
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf` and
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap`: the very data over which the
sheaf of relative differentials `Ω_{X/S}` of the same morphism is formed, so `L_{X/S}` and
`Ω_{X/S}` are built on one and the same morphism of sheaves of rings.

The site is `Opens X` with its topology of open covers. Its category structure lies in `Type 0`,
so the coefficient universe of `CategoryTheory.Sheaf.cotangentComplex` specializes to the
universe `u` of the sections of `𝒪_X`, and everything here is at
`AlgebraicGeometry.RingedSpace.{u, u}` with `SheafOfModules.{u}`; see the module docstring of
`StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace` for why that is forced.

A sheaf of `𝒪_X`-modules has two definitionally equal spellings of its ring sheaf, the one of
`AlgebraicGeometry.structureSheafRing` and the one used by
`CategoryTheory.Sheaf.cotangentComplex`. The statements below use the first, which is the
spelling in which instance search finds the structures of a ringed space; in particular
`cotangentComplexDerived` carries its `HasDerivedCategory` hypothesis in that spelling rather
than reusing `CategoryTheory.Sheaf.cotangentComplexDerived`.

Tag 08UV is the special case of Tag 08UR for the morphism `f⁻¹𝒪_S ⟶ 𝒪_X`, but the two sides are
spelled differently on the two levels: Tag 08UR identifies `H⁰` with the corepresenting object
`(derivationsFunctor _ _ _).coreprX` of the derivations functor, while `Ω_{X/S}` is defined as the
sheafification of the presheaf of sectionwise Kähler differentials. Both corepresent the same
functor of relative derivations, so the identification below is
`AlgebraicGeometry.SheafOfModules.corepresentableByIso` applied to the two corepresentations; it
is genuine data with both directions, not a transport of an existence statement.

## References

* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU)
* [Stacks Project, Tag 08UV](https://stacks.math.columbia.edu/tag/08UV)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex
  of a morphism of sheaves of rings.
* [Stacks Project, Tag 08UR](https://stacks.math.columbia.edu/tag/08UR), the same statement for
  a morphism of sheaves of rings on a site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  moduleOfDifferentials universalDerivation)

universe u t

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X S : RingedSpace.{u, u}}

/-- The cotangent complex `L_{X/S}` of a morphism of ringed spaces `f : X ⟶ S`: the cotangent
complex of the morphism of sheaves of commutative rings `f⁻¹𝒪_S ⟶ 𝒪_X` on the site of open
subsets of `X`. -/
@[stacks 08UU "the complex L_f"]
noncomputable def cotangentComplex (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  CategoryTheory.Sheaf.cotangentComplex (Opens.grothendieckTopology X.carrier)
    (inverseImageStructureMap f)

/-- `L_{X/S}` is the cotangent complex of the morphism of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
theorem cotangentComplex_eq (f : X ⟶ S) :
    cotangentComplex f = CategoryTheory.Sheaf.cotangentComplex
      (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f) :=
  rfl

/-- `L_{X/S}` regarded as an object of the derived category of sheaves of `𝒪_X`-modules. -/
@[stacks 08UU "the object L_f of the derived category of O_X-modules"]
noncomputable abbrev cotangentComplexDerived (f : X ⟶ S)
    [HasDerivedCategory.{t} (SheafOfModules.{u} (structureSheafRing X))] :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  DerivedCategory.Q.obj (cotangentComplex f)

/-- `L_{X/S}` vanishes in positive cohomological degrees. -/
theorem cotangentComplex_isZero_pos (f : X ⟶ S) (m : ℤ) (hm : 0 < m) :
    IsZero ((cotangentComplex f).X m) :=
  CategoryTheory.Sheaf.cotangentComplex_isZero_pos _ _ m hm

/-- `Ω_{X/S}` corepresents the relative derivations of `𝒪_X` over `f⁻¹𝒪_S`, through its
universal derivation `d`. -/
noncomputable def moduleOfDifferentials_corepresentableBy (f : X ⟶ S) :
    (SheafOfModules.derivationsFunctor.{u, u, u, u} (inverseImageSheaf f) X.sheaf
      (inverseImageStructureMap f)).CorepresentableBy (moduleOfDifferentials f) :=
  SheafOfModules.universalDerivationCorepresentableBy.{u, u, u, u} _ _ _ (universalDerivation f)
    (Stacks.Sheaves.Differentials.universalDerivation_isUniversal
      (inverseImageSheaf f) X.sheaf (inverseImageStructureMap f))

/-- **Stacks 08UV.** The zeroth cohomology of the cotangent complex of a morphism of ringed
spaces `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` is its sheaf of relative differentials:
`H⁰(L_{X/S}) ≅ Ω_{X/S}`. Both sheaves of `𝒪_X`-modules corepresent the relative derivations of
`𝒪_X` over `f⁻¹𝒪_S`, so they are canonically isomorphic. -/
@[stacks 08UV]
noncomputable def cotangentComplex_homologyZeroIso (f : X ⟶ S) :
    (cotangentComplex f).homology 0 ≅ moduleOfDifferentials f :=
  SheafOfModules.corepresentableByIso
    (CategoryTheory.Sheaf.derivationsFunctor_corepresentableBy
      (Opens.grothendieckTopology X.carrier) (inverseImageStructureMap f))
    (moduleOfDifferentials_corepresentableBy f)

/-- The identification `H⁰(L_{X/S}) ≅ Ω_{X/S}` carries the universal derivation of
`H⁰(L_{X/S})` to the universal derivation `d : 𝒪_X ⟶ Ω_{X/S}`, which determines it uniquely. -/
theorem cotangentComplex_homologyZeroIso_hom_postcomp (f : X ⟶ S) :
    (CategoryTheory.Sheaf.homologyZeroDerivation (Opens.grothendieckTopology X.carrier)
        (inverseImageStructureMap f)).postcomp
      (cotangentComplex_homologyZeroIso f).hom.val = universalDerivation f :=
  (CategoryTheory.Sheaf.derivationsFunctor_corepresentableBy
      (Opens.grothendieckTopology X.carrier)
      (inverseImageStructureMap f)).homEquiv.apply_symm_apply _

end Stacks.Sheaves.RingedSpaceCotangent

end
