module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex

/-!
# The cotangent complex of a morphism of algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the cotangent complex
`L_{X/Y}` is the cotangent complex of the canonical morphism of ringed topoi `f_small` between
the small étale sites of `X` and `Y`. Unwinding the two inputs, it is the cotangent complex of
the map of sheaves of commutative rings `f_small⁻¹𝒪_Y ⟶ 𝒪_X` on the small étale site of `X`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleStructureSheafULift` is the structure sheaf of the small
  étale ringed topos of an algebraic space with its sections presented in the universe of the
  site.
* `AlgebraicGeometry.Space.smallEtaleModulesULift` is the category of modules over it, the
  category in which `L_{X/Y}` lives.
* `AlgebraicGeometry.Space.cotangentComplex` is `L_{X/Y}`, and
  `AlgebraicGeometry.Space.cotangentComplexDerived` is its image in the derived category.

## Main results

* `AlgebraicGeometry.Space.cotangentComplex_isZero_pos`: `L_{X/Y}` vanishes in positive
  cohomological degrees.

## Implementation notes

The structure map of the morphism of ringed topoi is taken in its inverse-image form
`f_small⁻¹𝒪_Y ⟶ 𝒪_X`, which is `AlgebraicGeometry.RingedToposHom.fSharpInverseImage`: it is the
adjunct of `f♯` under the adjunction between the inverse image and the direct image of sheaves
of commutative rings, so it is derived from the morphism of ringed topoi and is not a further
choice.

The sections of the structure sheaf of a small étale ringed topos are *below* the universe of
its site: `AlgebraicGeometry.Space.smallEtaleRingedTopos` is a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, its site being the category of étale charts of a
presheaf on the big fppf site of `S` and hence a `Type (u + 1)`, while its structure sheaf has
sections in the universe `u` of the base scheme. The cotangent complex of a morphism of sheaves
of rings, `CategoryTheory.Sheaf.cotangentComplex`, is stated for sections in a universe
containing the site, because that is where the sheafifications its standard resolution
(Stacks 08SR) is built from are available without further hypotheses. The structure map is
therefore composed with `AlgebraicGeometry.SheafOfModules.sheafULift`, which lifts the sections
of a sheaf of commutative rings into the universe of the site through the ring isomorphism
`ULift R ≃+* R` and changes nothing else. This is the same device by which
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift` and
`AlgebraicGeometry.RingedSite.Hom.fsharpPullbackULift` state flatness of a structure map whose
sections are below its site. No universe is identified with another: `u` is the universe the
algebraic spaces and their morphism of ringed topoi already carry, and `u + 1` is the universe
of their small étale sites rather than a choice made here.

`cotangentComplexDerived` asks for a derived category of the coefficient modules. That is a
choice of localization and not a further condition on `f`, and it is the hypothesis
`CategoryTheory.Sheaf.cotangentComplexDerived` itself carries.

## References

* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian groups with sections in the universe of the small étale site of an algebraic space
admit sheafification on that site. -/
instance hasSheafify_smallEtaleRingedTopos (X : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleRingedTopos B S hS X).J AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat.{u + 1, u, u} _

/-- On the small étale site of an algebraic space, sheafification of abelian groups with
sections in the universe of the site inverts exactly the locally bijective maps. -/
instance wEqualsLocallyBijective_smallEtaleRingedTopos (X : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS X).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat.{u + 1, u, u} _

/-- The structure sheaf of the small étale ringed topos of an algebraic space, with its sections
presented in the universe of the site. The sections are lifted through the ring isomorphism
`ULift R ≃+* R`, so this changes nothing but their universe. -/
noncomputable abbrev smallEtaleStructureSheafULift (X : AlgebraicSpaces B S hS) :
    Sheaf (smallEtaleRingedTopos B S hS X).J CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (smallEtaleRingedTopos B S hS X).J).obj
    (smallEtaleRingedTopos B S hS X).O

/-- The category of modules over the structure sheaf of the small étale ringed topos of an
algebraic space, presented in the universe of the site. This is the category `Mod(𝒪_X)` in which
the cotangent complex of a morphism out of `X` lives; it depends on `X` alone. -/
noncomputable abbrev smallEtaleModulesULift (X : AlgebraicSpaces B S hS) :=
  CategoryTheory.Sheaf.targetModules.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
    (smallEtaleStructureSheafULift B S hS X)

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks Project, Tag 08VD.** The cotangent complex `L_{X/Y}` of a morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`: the cotangent complex of the canonical morphism of ringed
topoi `f_small` between the small étale sites of `X` and `Y`, that is, the cotangent complex of
the map of sheaves of commutative rings `f_small⁻¹𝒪_Y ⟶ 𝒪_X` on the small étale site of `X`.

It is a complex of modules over `𝒪_X`, so it depends on `X` alone. -/
@[stacks 08VD]
noncomputable abbrev cotangentComplex (f : X ⟶ Y) :
    CochainComplex (smallEtaleModulesULift B S hS X) ℤ :=
  CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
    ((SheafOfModules.sheafULift.{u, u + 1, u} (smallEtaleRingedTopos B S hS X).J).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)

/-- **Stacks Project, Tag 08VD.** The cotangent complex `L_{X/Y}` regarded as an object of the
derived category `D(𝒪_X)`. -/
@[stacks 08VD "the derived object"]
noncomputable abbrev cotangentComplexDerived (f : X ⟶ Y)
    [HasDerivedCategory.{t} (smallEtaleModulesULift B S hS X)] :
    DerivedCategory (smallEtaleModulesULift B S hS X) :=
  DerivedCategory.Q.obj (cotangentComplex B S hS f)

/-- The cotangent complex of a morphism of algebraic spaces is zero in positive cohomological
degrees. -/
theorem cotangentComplex_isZero_pos (f : X ⟶ Y) (m : ℤ) (hm : 0 < m) :
    IsZero ((cotangentComplex B S hS f).X m) :=
  CategoryTheory.Sheaf.cotangentComplex_isZero_pos.{u + 1, u, u} _ _ m hm

end AlgebraicGeometry.Space

end
