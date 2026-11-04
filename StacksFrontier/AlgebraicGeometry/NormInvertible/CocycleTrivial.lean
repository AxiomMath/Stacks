module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.ChartGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TwoChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A trivial glue has a coboundary cocycle

Let `D` be a unit transition cocycle on a covering family `U : ι → Opens X` of a ringed space and
suppose the glued module `D.glue` is trivial, that is, isomorphic to `𝒪_X`. Then the transition
units of `D` are a coboundary: there are units `cᵢ ∈ 𝒪_X(U i)` with
`u_{ij} · c_j = c_i` over every open inside both charts.

This is the converse reading of
`Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfCoboundaryTwist`, which glues cohomologous
cocycles to isomorphic modules, and it is what turns a *geometric* triviality statement about a
glued line bundle back into an *algebraic* statement about the transition unit. Its use is
contrapositive: a transition unit which is provably not a product of units from the two charts
glues to a nontrivial invertible module. That is the shape of the nontriviality argument of
[Stacks, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE), where the transition unit
`1 + t/(xy)` modulo `t²` is shown not to split because `1/(xy)` is not the difference of a
function on `D(x)` and a function on `D(y)`.

## Main results

* `Stacks.SheafOfModules.generatorRestrict_generatorOfIso`: the generator a trivialization
  supplies on an open is the restriction of the one it supplies on a larger open.
* `Stacks.SheafOfModules.UnitTransitionCocycle.exists_units_transition_mul_of_iso_unit`: **a
  trivial glue has a coboundary cocycle.**
* `Stacks.SheafOfModules.exists_units_overlapUnit_of_iso_unit`: the two-chart case, in the form
  the overlap unit is given in: `u` is the ratio of a unit on `U₁` and a unit on `U₀`.

## Implementation notes

The units are the comparison scalars `Stacks.SheafOfModules.generatorRatioUnit` of two generators
of `D.glue` over `U i`: the chart generator of the cocycle, and the image of `1` under the
trivialization. The coboundary identity is then the cocycle identity
`generatorRatioUnit_comp` for the three generators `(1, chart j, chart i)` over an open inside
both charts, the two ratios against `1` being the restrictions of `c j` and `c i` because the
generator supplied by the trivialization restricts to itself.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-- The generator a trivialization supplies on an open is the restriction of the generator it
supplies on a larger open: both are the image of the section `1`. -/
theorem generatorRestrict_generatorOfIso (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (e : L ≅ _root_.SheafOfModules.unit (structureSheaf X.sheaf))
    {A B : Opens X.carrier} (h : B ≤ A) :
    generatorRestrict L h (generatorOfIso L e (U := A)) = generatorOfIso L e (U := B) := by
  refine Subtype.ext ?_
  simp only [generatorRestrict_val, PresheafOfModules.restrictₛₗ_apply]
  refine (PresheafOfModules.naturality_apply e.inv.val (homOfLE h).op _).symm.trans ?_
  exact congrArg (fun z => e.inv.val.app (op B) z)
    ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom.map_one

namespace UnitTransitionCocycle

attribute [local instance] sectionsProductModule

variable {ι : Type u} {U : ι → Opens X.carrier}

/-- **A trivial glue has a coboundary cocycle.** If the module glued from a unit transition
cocycle is isomorphic to the structure sheaf, then there are units `cᵢ` on the charts with
`u_{ij} · c_j = c_i` over every open inside both charts. The units are the comparison scalars of
the chart generators against the image of `1` under the trivialization. -/
@[ega "0 5.4.7" "partial"]
theorem exists_units_transition_mul_of_iso_unit (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (e : D.glue ≅ _root_.SheafOfModules.unit (structureSheaf X.sheaf)) :
    ∃ c : (i : ι) → (X.presheaf.obj (op (U i)))ˣ, ∀ (i j : ι) (V : Opens X.carrier)
      (hi : V ≤ U i) (hj : V ≤ U j),
      D.transition i j V hi hj * Units.map (X.presheaf.map (homOfLE hj).op).hom (c j) =
        Units.map (X.presheaf.map (homOfLE hi).op).hom (c i) := by
  refine ⟨fun i => generatorRatioUnit D.glue (U i) (generatorOfIso D.glue e)
    (D.chartGenerator hU i), fun i j V hi hj => ?_⟩
  have hcomp := generatorRatioUnit_comp D.glue V (generatorOfIso D.glue e)
    (generatorRestrict D.glue hj (D.chartGenerator hU j))
    (generatorRestrict D.glue hi (D.chartGenerator hU i))
  rw [generatorRatioUnit_chartGenerator D hU i j hi hj] at hcomp
  have hres (k : ι) (hk : V ≤ U k) := generatorRestrict_generatorOfIso D.glue e hk ▸
    generatorRatioUnit_restrict D.glue hk (generatorOfIso D.glue e) (D.chartGenerator hU k)
  rwa [hres i hi, hres j hj] at hcomp

end UnitTransitionCocycle

/-- **A trivial two-chart glue has a splitting overlap unit.** If the module glued from a unit
`u` on the overlap of a two-open cover is isomorphic to the structure sheaf, then `u` is the
ratio of a unit on the first chart and a unit on the second. -/
@[ega "0 5.4.7" "special case"]
theorem exists_units_overlapUnit_of_iso_unit {U₀ U₁ : Opens X.carrier}
    (hU : (⊤ : Opens X.carrier) ≤ U₀ ⊔ U₁) (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ)
    (e : (twoChartCocycle u).glue ≅ _root_.SheafOfModules.unit (structureSheaf X.sheaf)) :
    ∃ (f : (X.presheaf.obj (op U₀))ˣ) (g : (X.presheaf.obj (op U₁))ˣ),
      u * Units.map (X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom g =
        Units.map (X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom f := by
  obtain ⟨c, hc⟩ := (twoChartCocycle u).exists_units_transition_mul_of_iso_unit
    (by rw [iSup_twoChartFamily]; exact hU) e
  have hkey := hc ⟨false⟩ ⟨true⟩ (U₀ ⊓ U₁) inf_le_left inf_le_right
  have hover : (twoChartCocycle u).transition ⟨false⟩ ⟨true⟩ (U₀ ⊓ U₁)
      (inf_le_left : U₀ ⊓ U₁ ≤ U₀) (inf_le_right : U₀ ⊓ U₁ ≤ U₁) = u := by
    refine Units.ext ?_
    change (X.presheaf.map (homOfLE (le_inf (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
      (inf_le_right : U₀ ⊓ U₁ ≤ U₁))).op).hom u.val = u.val
    rw [show (homOfLE (le_inf (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
      (inf_le_right : U₀ ⊓ U₁ ≤ U₁))).op = 𝟙 (op (U₀ ⊓ U₁)) from Subsingleton.elim _ _]
    simp
  rw [hover] at hkey
  exact ⟨c ⟨false⟩, c ⟨true⟩, hkey⟩

end Stacks.SheafOfModules

end
