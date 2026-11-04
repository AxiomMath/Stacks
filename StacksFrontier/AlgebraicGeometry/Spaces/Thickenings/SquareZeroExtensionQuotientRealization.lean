module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientAlgebra

/-!
# Realizations of square-zero extensions by first-order thickenings

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the small
étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT). A
*realization* of `E` is a first-order thickening `X ⊂ X'` with a morphism `h : X' ⟶ Y`
extending `f`, an isomorphism `i⁻¹𝒪_{X'} ≅ 𝒜` compatible with the maps to `𝒪_X`, under which
the algebra structure of `𝒜` is the structure map of `h`.

When the big fppf site contains the chart thickenings `U'`, `R'` of a presentation `X = U/R`
lying over a presentation of `Y`, the thickened quotient `X' = U'/R'` is a realization.

All declarations live in the namespace `AlgebraicGeometry.Space.SquareZeroExtension`.

## Main definitions

* `ToposRealization`: A realization of a square-zero extension by a first-order thickening.

## Main results

* `nonempty_realization_of_contains_chartRealizedScheme`: If `B` contains the chart
  thickenings of a presentation over a presentation of `Y`, then a realization exists.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- **A realization of a square-zero extension** `E` of `𝒪_X` relative to `f : X ⟶ Y`: a
first-order thickening `X ⊂ X'` over `Y` with `i⁻¹𝒪_{X'} ≅ 𝒜` compatibly with the maps to `𝒪_X`
and with the algebra structures over `f⁻¹𝒪_Y`. -/
structure ToposRealization (E : SquareZeroExtension B S hS f) where
  /-- The thickening `X'`. -/
  ambient : AlgebraicSpaces B S hS
  /-- The closed subspace of `X'`. -/
  closed : Subfunctor ambient.1
  /-- `X'` is a first-order thickening of the closed subspace. -/
  firstOrder : IsFirstOrderThickening B S hS ambient closed
  /-- `X` is the closed subspace. -/
  closedIso : X.1 ≅ closed.toFunctor
  /-- The inclusion `i : X ⟶ X'`. -/
  immersion : X ⟶ ambient
  immersion_eq : immersion.hom = closedIso.hom ≫ closed.ι
  /-- The morphism `h : X' ⟶ Y`. -/
  toBase : ambient ⟶ Y
  over_base : immersion ≫ toBase = f
  /-- `i⁻¹𝒪_{X'} ≅ 𝒜`. -/
  sheafIso :
    (smallEtaleRingedToposHom B S hS immersion).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS ambient).O ≅ E.A
  quotient_compatibility :
    sheafIso.hom ≫ E.π = (smallEtaleRingedToposHom B S hS immersion).fSharpInverseImage
  /-- The algebra structure of `𝒜` is the structure map of `h`, through the comparison
  `(i ≫ h)⁻¹𝒪_Y ≅ i⁻¹h⁻¹𝒪_Y` of Stacks 03G8. -/
  algebra_compatibility :
    E.toBase =
      eqToHom (congrArg (fun φ ↦ (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImageRing.obj
          (smallEtaleRingedTopos B S hS Y).O) over_base.symm) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS immersion toBase).inv.app
            (smallEtaleRingedTopos B S hS Y).O ≫
        (smallEtaleInverseImageRing B S hS immersion).map
          (smallEtaleRingedToposHom B S hS toBase).fSharpInverseImage ≫
        sheafIso.hom

variable (E : SquareZeroExtension B S hS f)

/-- **Realization when the site contains the chart thickenings.** For presentations `P₀` of `X`
and `Q` of `Y`, if the big fppf site contains the chart thickenings `U'`, `R'` of the
presentation `X = U/R` over `Q`, the thickened quotient `X' = U'/R'` realizes `E`. -/
theorem nonempty_realization_of_contains_chartRealizedScheme
    (P₀ : Presentation B S hS X.obj X.property)
    (Q : Presentation B S hS Y.obj Y.property)
    (hU : B.Contains (E.chartRealizedScheme (presentationChart (presentationOverChart f.hom P₀ Q))))
    (hR : B.Contains (E.chartRealizedScheme
      (presentationRelationChart (presentationOverChart f.hom P₀ Q)))) :
    Nonempty (ToposRealization E) := by
  let P := presentationOverChart f.hom P₀ Q
  have hgt := presentationOverChartRelHom_target f.hom P₀ Q
  have hgs := presentationOverChartRelHom_source f.hom P₀ Q
  have hgU := presentationOverChart_comm f.hom P₀ Q
  have := mono_of_isClosedImmersion B S hS _ (E.isClosedImmersion_thickeningImmersion P hU hR)
  exact ⟨{
    ambient := E.thickeningQuotient hS P hU hR
    closed := Subfunctor.range (E.thickeningImmersion P hU hR).hom
    firstOrder := E.isFirstOrderThickening_range_thickeningImmersion P hU hR
    closedIso := asIso (Subfunctor.toRange (E.thickeningImmersion P hU hR).hom)
    immersion := E.thickeningImmersion P hU hR
    immersion_eq := (Subfunctor.toRange_ι _).symm
    toBase := E.thickeningQuotientToBase P Q _ hgU _ hgt hgs hU hR
    over_base := E.thickeningImmersion_comp_thickeningQuotientToBase P Q _ hgU _ hgt hgs hU hR
    sheafIso := E.quotientSheafIso P hU hR
    quotient_compatibility := E.quotientSheafIso_hom_comp_π P hU hR
    algebra_compatibility := E.toBase_eq_thickeningQuotientToBase P Q _ hgU _ hgt hgs hU hR }⟩

end AlgebraicGeometry.Space.SquareZeroExtension

end
