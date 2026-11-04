module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorShiftedLift
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ChernClassRestrictionSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorRestrictionChain

/-!
# The first Chern class map of a divisor lifts through the canonical map to the ambient space

Let `f : X ⟶ S` be a morphism of schemes and `i : Y ⟶ X` the closed immersion of an effective
Cartier divisor for which the de Rham complex of log poles is defined. Let
`ζ' : Ω^•_{Y/S} ⟶ Ω^•_{Y/S}[2]` be the map of [Stacks, Tag 0FU7] for
`ζ = c₁^{dR}(𝒪_X(-Y)|_Y)`, and `θ = ζ'[-2] : Ω^•_{Y/S}[-2] ⟶ Ω^•_{Y/S}` its untwisted form. The
lower right triangle of [Stacks, Tag 0FUQ] says that the boundary map
`δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` of the log poles sequence, followed by the restriction of forms,
is `ζ'`. This file reads it as a lift

`Ri_*(Ω^•_{Y/S}[-2]) ⟶ Ω^•_{X/S}` of `Ri_*θ` through the canonical map `Ω^•_{X/S} ⟶ Ri_*Ω^•_{Y/S}`

in `D(X, f^{-1}𝒪_S)`, with the canonical map of Section 07HX and the derived direct image along
`Stacks.DeRhamSmooth.relativeBase`, as the proof of [Stacks, Tag 0FUW] uses it.

## Main definitions

* `Stacks.LineBundle.divisorChernUntwisted`: `θ = ζ'[-2]`.

## Main results

* `Stacks.LineBundle.exists_comp_chain_unit_eq_map_divisorChernUntwisted`: the lift.

## Implementation notes

The derived categories are the standard models, which is where the maps of Tag 0FU7 live.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.DeRhamDirectImage
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open scoped Stacks.StandardDerivedModel

universe u

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

namespace Stacks.LineBundle

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]

/-- **`θ = ζ'[-2] : Ω^•_{Y/S}[-2] ⟶ Ω^•_{Y/S}`**, the untwisted form of the map `ζ'` of
[Stacks, Tag 0FU7] for `c₁^{dR}(𝒪_X(-Y)|_Y)`. -/
abbrev divisorChernUntwisted :
    (DerivedCategory.Q.obj (deRhamCochainComplex (I.subschemeι ≫ f)))⟦(-2 : ℤ)⟧ ⟶
      DerivedCategory.Q.obj (deRhamCochainComplex (I.subschemeι ≫ f)) :=
  (divisorChernMorphism f I)⟦(-2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (2 : ℤ) (-2) (by norm_num)).hom.app _

/-- **The lift of `Ri_*θ` through the canonical map `Ω^•_{X/S} ⟶ Ri_*Ω^•_{Y/S}`**, from the lower
right triangle of [Stacks, Tag 0FUQ]: there is `δ : Ri_*(Ω^•_{Y/S}[-2]) ⟶ Ω^•_{X/S}` whose
composite with the canonical map is `Ri_*θ`, for `θ = ζ'[-2]` the untwisted map of Tag 0FU7 for
`c₁^{dR}(𝒪_X(-Y)|_Y)`. -/
theorem exists_comp_chain_unit_eq_map_divisorChernUntwisted
    (hlog : f.HasLogPolesDeRhamComplex I) :
    ∃ δ : (derivedPushforward (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)).obj
        ((DerivedCategory.Q.obj (deRhamCochainComplex (I.subschemeι ≫ f)))⟦(-2 : ℤ)⟧) ⟶
        DerivedCategory.Q.obj (deRhamCochainComplex f),
      δ ≫ DerivedCategory.Q.map (Stacks.DeRham.BlowupTriangle.chain I.subschemeι f) ≫
          Stacks.DeRham.BlowupTriangle.unit (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)
            (deRhamCochainComplex (I.subschemeι ≫ f)) =
        (derivedPushforward (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)).map
          (divisorChernUntwisted f I) := by
  have h0 := logPolesBoundary_comp_restriction_eq f I hlog
  have h1 : (inv (DerivedCategory.Q.map (divisorDeRhamIntHom f I)) ≫
      (Scheme.Hom.logPolesShiftedSequence f hI hlog).boundary) ≫
        (DerivedCategory.Q.map
          (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I))⟦(2 : ℤ)⟧' =
      divisorPushforwardDerivedMap f I (divisorChernMorphism f I) := by
    rw [Category.assoc, h0, IsIso.inv_hom_id_assoc]
  have hJ := Scheme.Hom.basePushforward_eq_modulePushforward I.subschemeι f
  have ha : (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)).Additive :=
    hJ ▸ (inferInstance : (divisorPushforward f I).Additive)
  have hl : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)) :=
    hJ ▸ (inferInstance : PreservesFiniteLimits (divisorPushforward f I))
  have hc : PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)) :=
    hJ ▸ (inferInstance : PreservesFiniteColimits (divisorPushforward f I))
  exact @StacksDraft.ExactFunctorShiftedLift.exists_comp_unitQ_eq_map_of_eq
    (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf (I.subschemeι ≫ f))) _ _
    (HasDerivedCategory.standard _) (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf f)) _ _
    (HasDerivedCategory.standard _)
    (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamSmooth.relativeBase I.subschemeι f)) ha hl hc
    (divisorPushforward f I) _ _ _ hJ _ _
    (divisorChernMorphism f I) (Stacks.DeRham.BlowupTriangle.chain I.subschemeι f)
    (Scheme.Hom.divisorRestrictionInt f I ≫ divisorDeRhamIntHom f I)
    (divisorRestriction_heq_chain f I) _ h1

end Stacks.LineBundle

end
