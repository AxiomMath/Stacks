module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogPolesRestrictionMorphism
public import
  StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryChernClass

/-!
# Boundary maps and first Chern classes along an effective Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, `i : Y ⟶ X`,
for which the de Rham complex of log poles is defined ([Stacks, Tag 0FMV]). Let
`δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` be the boundary map of the shifted short exact sequence of Tag 0FMW,
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` the map of Tag 0FU7 for `ξ = c₁^{dR}(𝒪_X(-Y))` and
`ζ' : Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]` the map of Tag 0FU7 on `Y` for `ζ = c₁^{dR}(𝒪_X(-Y)|_Y)`. Then,
as in [Stacks, Tag 0FUQ], in `D(X, f^{-1}𝒪_S)`

* `ξ' = δ ∘ res` (the upper left triangle),
* `res[2] ∘ δ = ζ'` (the lower right triangle),
* `res[2] ∘ ξ' = ζ' ∘ res` (the square),

where `res : Ω^•_{X/S} ⟶ Ω^•_{Y/S}` is the restriction of forms and `ζ'` is read on `X` through the
exact direct image along `i` over the base rings.

## Main definitions

* `Stacks.LineBundle.idealChernMorphism`: the map `ξ'`.
* `Stacks.LineBundle.divisorChernMorphism`: the map `ζ'`.

## Main results

* `Stacks.LineBundle.idealChernMorphism_eq_comp_boundary`: the upper left triangle.
* `Stacks.LineBundle.logPolesBoundary_comp_restriction_eq`: the lower right triangle.
* `Stacks.LineBundle.idealChernMorphism_comp_restriction`: the square.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.LineBundle

section Registration

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] (hlog : f.HasLogPolesDeRhamComplex I)

/-- **`ξ'`**: the map `Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of Stacks Tag 0FU7 in `D(X, f^{-1}𝒪_S)` for the
de Rham first Chern class `ξ = c₁^{dR}(𝒪_X(-Y))` of the ideal sheaf of the divisor. -/
abbrev idealChernMorphism :=
  AlgebraicGeometry.SheafOfModules.deRhamClassMorphism (Scheme.Hom.deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) 2
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass (X := X.toRingedSpace)
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
      (idealSituation f I).L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ (idealSituation f I).L
        (idealSituation f I).invertible))

/-- **`ζ'`**: the map `Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]` of Stacks Tag 0FU7 in `D(Y, f|_Y^{-1}𝒪_S)` for
the de Rham first Chern class `ζ = c₁^{dR}(𝒪_X(-Y)|_Y)` of the restriction to `Y` of the ideal
sheaf of the divisor. -/
abbrev divisorChernMorphism :=
  AlgebraicGeometry.SheafOfModules.deRhamClassMorphism
    (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential
      (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f)) 2
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass
      (X := (divisorSituation f I).X.toRingedSpace)
      (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (divisorSituation f I).f))
      (divisorSituation f I).L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ (divisorSituation f I).L
        (divisorSituation f I).invertible))

/-- The upper left triangle `ξ' = δ ∘ res`: the map `idealChernMorphism` is the restriction of
forms followed by the boundary map of the shifted log poles sequence. -/
@[stacks 0FUQ "the upper left triangle: the map of 0FU7 for c_1^dR(O_X(-Y)) is the boundary map
delta of the shifted sequence of 0FMW composed with the restriction of forms"]
theorem idealChernMorphism_eq_comp_boundary :
    idealChernMorphism f I =
      DerivedCategory.Q.map (Scheme.Hom.divisorRestrictionInt f I) ≫
        (Scheme.Hom.logPolesShiftedSequence f hI hlog).boundary :=
  (idealSituation f I).residueShiftedSequence_boundary_eq_deRhamClassMorphism.symm.trans
    (residueShiftedSequence_boundary_eq f I hlog)

/-- The lower right triangle: `res[2] ∘ δ = ζ'`, with `ζ'` read on `X` through the exact direct
image along `i : Y ⟶ X` and `Ω^•_{Y/S}` identified with its direct image by
`Stacks.LineBundle.divisorDeRhamIntHom`. -/
@[stacks 0FUQ "the lower right triangle: the boundary map delta followed by the restriction of
forms in degree two is the map of 0FU7 on Y for c_1^dR(O_X(-Y)|_Y), read on X through the exact
direct image along the closed immersion"]
theorem logPolesBoundary_comp_restriction_eq :
    (Scheme.Hom.logPolesShiftedSequence f hI hlog).boundary ≫
        (DerivedCategory.Q.map
          (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I))⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map (divisorDeRhamIntHom f I) ≫
        divisorPushforwardDerivedMap f I (divisorChernMorphism f I) := by
  refine (logPolesShiftedSequence_boundary_comp_restriction f I hlog).trans ?_
  exact congrArg (fun ζ ↦ DerivedCategory.Q.map (divisorDeRhamIntHom f I) ≫
    divisorPushforwardDerivedMap f I ζ)
    (divisorSituation f I).residueShiftedSequence_boundary_eq_deRhamClassMorphism

include hlog in
/-- The square: `res[2] ∘ ξ' = ζ' ∘ res`. -/
@[stacks 0FUQ "the square of the diagram, deduced from the two triangles: the restriction of
forms in degree two after the map of 0FU7 for c_1^dR(O_X(-Y)) equals the map of 0FU7 on Y for
c_1^dR(O_X(-Y)|_Y) after the restriction of forms, with the latter read on X through the exact
direct image along the closed immersion"]
theorem idealChernMorphism_comp_restriction :
    idealChernMorphism f I ≫
        (DerivedCategory.Q.map
          (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I))⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I) ≫
        divisorPushforwardDerivedMap f I (divisorChernMorphism f I) := by
  refine (congrArg (· ≫ _) (idealChernMorphism_eq_comp_boundary f I hlog)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (logPolesBoundary_comp_restriction_eq f I hlog)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (Functor.map_comp _ _ _).symm

end Registration

end Stacks.LineBundle
