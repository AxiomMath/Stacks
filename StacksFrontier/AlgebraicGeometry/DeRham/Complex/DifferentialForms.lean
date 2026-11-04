module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.ExteriorAlgebraComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.RingedSiteAlgebras.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of relative differential forms and their functoriality

The sheaf of relative differential `n`-forms `Ω^n_{X/S}` of a morphism of schemes `p : X ⟶ S` is
the degree-`n` piece of the exterior algebra of the sheaf of relative differentials `Ω_{X/S}`.
A commutative square

```
X' → X
↓    ↓
S' → S
```

induces the canonical map `f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks Tag 01UV, and the universal
property of the exterior algebra extends it to a homomorphism of sheaves of graded algebras
`⋀(f^*Ω_{X/S}) ⟶ ⋀(Ω_{X'/S'})`. Composing its degree-`n` component with the comparison
`f^*(⋀^n Ω_{X/S}) ≅ ⋀^n(f^*Ω_{X/S})` of Stacks Tag 01CI gives the canonical map on forms

`f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}`.

It is an isomorphism as soon as the canonical map on relative differentials is — which happens
for a cartesian square (Tag 0FL5) and for a square whose horizontal edges are étale
(Tag 0FLV).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.exteriorAlgebra` and
  `AlgebraicGeometry.Scheme.Modules.exteriorGenerator`: the exterior algebra of a sheaf of
  modules on a scheme, with its degree-one generator.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms`: the algebra `Ω^•_{X/S}` of relative
  differential forms and its homogeneous pieces `Ω^n_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsComparison`: the canonical
  homomorphism of sheaves of graded algebras `⋀(f^*Ω_{X/S}) ⟶ ⋀(Ω_{X'/S'})` of a commutative
  square.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`: the canonical map
  `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isExteriorAlgebra_exteriorAlgebra`: the exterior algebra of
  a sheaf of modules on a scheme has the universal property.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsComparison_generator`: in degree one
  the comparison is the canonical map on relative differentials.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialFormsComparison_app` and
  `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialFormsMap`: both are isomorphisms in
  every degree as soon as the canonical map on relative differentials is an isomorphism.

## Implementation notes

The exterior algebra of a sheaf of modules on a scheme is `SheafOfModules.algebras` at the
topology of the scheme's open subsets and its structure sheaf; a sheaf of modules on a scheme is
a sheaf of modules over that sheaf of rings on the nose, so no transport is involved. For the
same reason `AlgebraicGeometry.Scheme.Modules.pullback f` is the pullback functor of the
underlying morphism of ringed spaces, which is the form Tag 01CI is stated in.

The comparison is a homomorphism of graded algebras rather than a family of maps because that is
what its uniqueness is about: it is the unique unital homomorphism extending the canonical map
on relative differentials, by the universal property of `⋀(f^*Ω_{X/S})`.

Invertibility separates cleanly from the construction. The construction needs no hypothesis on
the square beyond commutativity, and invertibility needs only that the canonical map on
relative differentials is invertible —
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app`, plus invertibility of the
comparison of Tag 01CI, which holds always.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace SheafOfModules.GradedAlgebra

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The exterior algebra of a sheaf of modules on a scheme, as a sheaf of graded algebras. -/
noncomputable def exteriorAlgebra {X : Scheme.{u}} (F : X.Modules) :
    SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) :=
  (SheafOfModules.algebras _ F).exterior

/-- The degree-`n` exterior power `⋀ⁿ F` of a sheaf of modules on a scheme. -/
@[ega "0 4.1.5" "special case"]
noncomputable abbrev exteriorPower {X : Scheme.{u}} (F : X.Modules) (n : ℤ) : X.Modules :=
  (exteriorAlgebra F).piece n

/-- The degree-one generator of the exterior algebra of a sheaf of modules on a scheme. -/
noncomputable def exteriorGenerator {X : Scheme.{u}} (F : X.Modules) :
    F ⟶ (exteriorAlgebra F).piece 1 :=
  (SheafOfModules.algebras _ F).exteriorGenerator

/-- The exterior algebra of a sheaf of modules on a scheme has the universal property of the
exterior algebra: its degree-one generator has square zero, and it is initial among sheaves of
graded algebras with a square-zero degree-one generator. -/
theorem isExteriorAlgebra_exteriorAlgebra {X : Scheme.{u}} (F : X.Modules) :
    (exteriorAlgebra F).IsExteriorAlgebra (exteriorGenerator F) :=
  (SheafOfModules.algebras _ F).exterior_isExteriorAlgebra

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}}

/-- The algebra `Ω^•_{X/S}` of relative differential forms of a morphism of schemes: the
exterior algebra of its sheaf of relative differentials. -/
noncomputable def relativeDifferentialFormsAlgebra (p : X ⟶ S) :
    SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) :=
  Scheme.Modules.exteriorAlgebra (relativeDifferentials p)

/-- The sheaf `Ω^n_{X/S}` of relative differential `n`-forms of a morphism of schemes. -/
noncomputable abbrev relativeDifferentialForms (p : X ⟶ S) (n : ℤ) : X.Modules :=
  (relativeDifferentialFormsAlgebra p).piece n

variable (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)

/-- **Stacks Project, Tags 0FL5 and 0FLV.** The canonical homomorphism of sheaves of graded
algebras `⋀(f^*Ω_{X/S}) ⟶ ⋀(Ω_{X'/S'})` attached to a commutative square of schemes: the unique
unital homomorphism extending the canonical map on relative differentials of Tag 01UV. -/
@[stacks 0FLV "canonical graded comparison"]
noncomputable def relativeDifferentialFormsComparison (hcomm : f ≫ p = p' ≫ g) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Scheme.Modules.exteriorAlgebra
        ((Scheme.Modules.pullback f).obj (relativeDifferentials p)))
      (relativeDifferentialFormsAlgebra p') :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).desc _
    (relativeDifferentialsMap f p p' g hcomm ≫
      Scheme.Modules.exteriorGenerator (relativeDifferentials p'))
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p')).1.comp _)

/-- **Stacks Project, Tags 0FL5 and 0FLV.** In degree one the canonical comparison of exterior
algebras is the canonical map on relative differentials of Tag 01UV. -/
@[stacks 0FLV "canonical map in degree one"]
theorem relativeDifferentialFormsComparison_generator (hcomm : f ≫ p = p' ≫ g) :
    Scheme.Modules.exteriorGenerator
          ((Scheme.Modules.pullback f).obj (relativeDifferentials p)) ≫
        (relativeDifferentialFormsComparison f p p' g hcomm).app 1 =
      relativeDifferentialsMap f p p' g hcomm ≫
        Scheme.Modules.exteriorGenerator (relativeDifferentials p') :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).desc_extends _ _ _

/-- **Stacks Project, Tags 0FL5 and 0FLV.** If the canonical map on relative differentials of a
commutative square is an isomorphism, then so is the induced comparison of exterior algebras, in
every degree. -/
theorem isIso_relativeDifferentialFormsComparison_app (hcomm : f ≫ p = p' ≫ g)
    (hc : IsIso (relativeDifferentialsMap f p p' g hcomm)) (n : ℤ) :
    IsIso ((relativeDifferentialFormsComparison f p p' g hcomm).app n) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      ((Scheme.Modules.pullback f).obj (relativeDifferentials p))).isIso_desc_app
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p'))
    (relativeDifferentialsMap f p p' g hcomm) hc _ n

/-- **Stacks Project, Tags 07HX, 0FL5 and 0FLV.** The canonical map
`f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative differential forms attached to a commutative square of
schemes: the comparison of Tag 01CI followed by the degree-`n` component of the comparison of
exterior algebras. -/
@[stacks 07HX "the linearized canonical map on differential forms"]
noncomputable def relativeDifferentialFormsMap (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (relativeDifferentialForms p n) ⟶
      relativeDifferentialForms p' n :=
  ((Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
        (relativeDifferentialFormsAlgebra p)
        (Scheme.Modules.exteriorGenerator (relativeDifferentials p))
        (Scheme.Modules.exteriorAlgebra
          ((Scheme.Modules.pullback f).obj (relativeDifferentials p)))
        (Scheme.Modules.exteriorGenerator
          ((Scheme.Modules.pullback f).obj (relativeDifferentials p)))
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)).app n).hom ≫
    (relativeDifferentialFormsComparison f p p' g hcomm).app n

/-- **Stacks Project, Tags 0FL5 and 0FLV.** If the canonical map on relative differentials of a
commutative square is an isomorphism, then the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on
relative differential forms is an isomorphism in every degree. -/
theorem isIso_relativeDifferentialFormsMap (hcomm : f ≫ p = p' ≫ g)
    (hc : IsIso (relativeDifferentialsMap f p p' g hcomm)) (n : ℤ) :
    IsIso (relativeDifferentialFormsMap f p p' g hcomm n) :=
  IsIso.comp_isIso' (Iso.isIso_hom _)
    (isIso_relativeDifferentialFormsComparison_app f p p' g hcomm hc n)

end AlgebraicGeometry.Scheme.Hom
