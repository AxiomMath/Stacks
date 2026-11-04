module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.CocyclePushforward
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TwoChart

/-!
# Maps of two-chart glued modules, and cocycles on a family only known to be a preimage

`Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfIntertwines` builds a morphism
`D.glue ⟶ f_* D'.glue` from a morphism of schemes `f : Y' ⟶ Y` intertwining two unit transition
cocycles, the one upstairs being indexed by the preimages `f ⁻¹ᵁ U i` of the charts downstairs.
A cocycle produced by some other construction is indexed by a family which is only *equal* to
that one, so this file carries a cocycle along an equality of families and restates the
construction for such a cocycle. It then specializes everything to the two-chart gluing of
`Stacks.SheafOfModules.twoChartCocycle`, where the intertwining hypothesis collapses to a single
equation between overlap units.

The example it is written for is [Stacks, Tag 0EHE]: the two glued modules are the invertible
modules on the punctured spectra of `A/t^{n+1}A` and of `A/tⁿA`, each presented as
`twoChartCocycle` of the transition element of its level, and `f` is the closed immersion of the
one punctured spectrum in the other. There the equality of families is exactly the identification
of the preimage of a chart with the chart one level down.

## Main definitions

* `Stacks.SheafOfModules.UnitTransitionCocycle.ofFamilyEq`: a cocycle for one family of opens,
  read as a cocycle for an equal family.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfFamilyEqIntertwines`: the morphism
  `D.glue ⟶ f_* D'.glue` for a cocycle `D'` indexed by a family equal to the preimage family.
* `Stacks.SheafOfModules.glueHomOfOverlapUnit`: the morphism of two-chart glued modules attached
  to a morphism of schemes carrying one overlap unit to the other.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.glue_ofFamilyEq`: the transport does not change
  the glued module.
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_glueHomOfFamilyEqIntertwines`: in
  the chart trivializations the morphism is the map on functions, which pins it down.
* `Stacks.SheafOfModules.intertwines_twoChartCocycle`: for two-chart cocycles the intertwining
  hypothesis is the single equation `f^♯(u) = u'|`.
* `Stacks.SheafOfModules.chartLinearEquiv_glueHomOfOverlapUnit`: in the chart trivializations the
  morphism of two-chart glued modules is the map on functions.

## Implementation notes

`Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfIntertwines` is left alone: its upstairs
charts stay the preimages `f ⁻¹ᵁ U i` on the nose. Weakening it to an arbitrary family together
with a propositional equality would put that equality inside the type of every ring of sections
the construction quantifies over, starting with the membership proof
`Stacks.SheafOfModules.UnitTransitionCocycle.pullbackSections_mem`, which would then need a
per-index transport. Here the equality is absorbed once, in `ofFamilyEq`, whose fields are the
original fields read at proofs of the same `Prop` — so `ofFamilyEq D rfl` is `D` definitionally,
and every statement about the transported cocycle is proved by substituting the equality away.

The two families that actually occur, `fun i => f ⁻¹ᵁ twoChartFamily U₀ U₁ i` and
`twoChartFamily (f ⁻¹ᵁ U₀) (f ⁻¹ᵁ U₁)`, are equal by `funext` after a case split on the index:
pointwise each is the preimage of a chart, by `rfl`. They are not equal as functions, the `bif`
of `Stacks.SheafOfModules.twoChartFamily` not reducing on a variable index, which is why the
transport cannot be avoided.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

namespace UnitTransitionCocycle

section

variable {X : RingedSpace.{u, u}} {ι : Type u} {U U' : ι → Opens X.carrier}

/-- A unit transition cocycle for a family of opens is one for any family equal to it: a
transition unit over an open inside two charts of the one family is a transition unit over the
same open inside the corresponding two charts of the other. -/
def ofFamilyEq (D : UnitTransitionCocycle X U) (h : U = U') : UnitTransitionCocycle X U' where
  transition i j V hi hj :=
    D.transition i j V (hi.trans (congrFun h.symm i).le) (hj.trans (congrFun h.symm j).le)
  restrict _ _ hle := D.restrict _ _ hle
  symm i j V _ _ := D.symm i j V _ _
  cocycle i j k V _ _ _ := D.cocycle i j k V _ _ _

/-- The transition unit of `D.ofFamilyEq h` over `V` between charts `i` and `j` is the transition
unit of `D` over `V` between the same charts. -/
theorem ofFamilyEq_transition (D : UnitTransitionCocycle X U) (h : U = U') (i j : ι)
    (V : Opens X.carrier) (hi : V ≤ U' i) (hj : V ≤ U' j) (hi' : V ≤ U i) (hj' : V ≤ U j) :
    (D.ofFamilyEq h).transition i j V hi hj = D.transition i j V hi' hj' := rfl

/-- Reading a cocycle at an equal family does not change the module it glues to. -/
theorem glue_ofFamilyEq (D : UnitTransitionCocycle X U) (h : U = U') :
    (D.ofFamilyEq h).glue = D.glue := by
  cases h
  rfl

end

section

variable {Y Y' : Scheme.{u}} {f : Y' ⟶ Y} {ι : Type u} {U : ι → Y.Opens} {U' : ι → Y'.Opens}
  {D : UnitTransitionCocycle Y.toRingedSpace U}

/-- The preimage of an open inside the `i`-th chart lies in the `i`-th member of any family
equal to the preimage family. -/
theorem preimage_le_of_familyEq (hfam : U' = fun i => f ⁻¹ᵁ U i) (i : ι) {V : Y.Opens}
    (hV : V ≤ U i) : f ⁻¹ᵁ V ≤ U' i := by
  rw [hfam]
  exact f.preimage_mono hV

/-- **A map of glued modules for a cocycle indexed by a family equal to the preimage family.**
This is `Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfIntertwines` for a cocycle `D'`
whose index family is only propositionally the family of preimages. -/
noncomputable def glueHomOfFamilyEqIntertwines (D' : UnitTransitionCocycle Y'.toRingedSpace U')
    (hfam : U' = fun i => f ⁻¹ᵁ U i) (h : Intertwines f D (D'.ofFamilyEq hfam)) :
    D.glue ⟶ (Scheme.Modules.pushforward f).obj D'.glue :=
  glue_ofFamilyEq D' hfam ▸ glueHomOfIntertwines h

/-- In the chart trivializations the morphism of glued modules is the map on functions. This
pins `Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfFamilyEqIntertwines` down. -/
theorem chartLinearEquiv_glueHomOfFamilyEqIntertwines
    (D' : UnitTransitionCocycle Y'.toRingedSpace U') (hfam : U' = fun i => f ⁻¹ᵁ U i)
    (h : Intertwines f D (D'.ofFamilyEq hfam)) (i : ι) {V : Y.Opens} (hV : V ≤ U i)
    (s : D.sectionsSubmodule V) :
    D'.chartLinearEquiv i (preimage_le_of_familyEq hfam i hV)
        ((glueHomOfFamilyEqIntertwines D' hfam h).val.app (op V) s) =
      (f.app V).hom (D.chartLinearEquiv i hV s) := by
  subst hfam
  exact chartLinearEquiv_glueHomOfIntertwines h i hV s

end

end UnitTransitionCocycle

section

variable {Y Y' : Scheme.{u}} {U₀ U₁ : Y.Opens} {V₀ V₁ : Y'.Opens}

/-- The two-element family of the preimages of two charts is the family of preimages of the
two-element family: pointwise, after a case split on the index, both are the preimage of the same
chart. -/
theorem twoChartFamily_eq_preimage (f : Y' ⟶ Y) (h₀ : f ⁻¹ᵁ U₀ = V₀) (h₁ : f ⁻¹ᵁ U₁ = V₁) :
    twoChartFamily (X := Y'.toRingedSpace) V₀ V₁ =
      fun i => f ⁻¹ᵁ twoChartFamily (X := Y.toRingedSpace) U₀ U₁ i :=
  funext fun i => by rcases i with ⟨b⟩; cases b; exacts [h₀.symm, h₁.symm]

/-- The preimage of the overlap of two charts lies in the overlap of their preimages. -/
theorem preimage_inf_le_inf (f : Y' ⟶ Y) (h₀ : f ⁻¹ᵁ U₀ = V₀) (h₁ : f ⁻¹ᵁ U₁ = V₁) :
    f ⁻¹ᵁ (U₀ ⊓ U₁) ≤ V₀ ⊓ V₁ :=
  le_inf ((f.preimage_mono inf_le_left).trans h₀.le)
    ((f.preimage_mono inf_le_right).trans h₁.le)

/-- Pulling back a restriction of the overlap unit along `f` gives the corresponding restriction
of the other overlap unit, once that holds over the whole overlap. -/
theorem map_app_overlapUnit (f : Y' ⟶ Y) (u : Γ(Y, U₀ ⊓ U₁)ˣ) (u' : Γ(Y', V₀ ⊓ V₁)ˣ)
    (hle : f ⁻¹ᵁ (U₀ ⊓ U₁) ≤ V₀ ⊓ V₁)
    (hu : Units.map (f.app (U₀ ⊓ U₁)).hom u = overlapUnit u' (f ⁻¹ᵁ (U₀ ⊓ U₁)) hle)
    {V : Y.Opens} (hV : V ≤ U₀ ⊓ U₁) :
    Units.map (f.app V).hom (overlapUnit u V hV) =
      overlapUnit u' (f ⁻¹ᵁ V) ((f.preimage_mono hV).trans hle) := by
  have huv : (f.app (U₀ ⊓ U₁)).hom u.val =
      (Y'.presheaf.map (homOfLE hle).op).hom u'.val := congrArg Units.val hu
  refine Units.ext ?_
  show (f.app V).hom ((Y.presheaf.map (homOfLE hV).op).hom u.val) =
    (Y'.presheaf.map (homOfLE ((f.preimage_mono hV).trans hle)).op).hom u'.val
  rw [← UnitTransitionCocycle.app_presheafMap_apply f hV u.val, huv]
  exact congrArg Units.val (overlapUnit_restrict u' hle (f.preimage_mono hV))

/-- **The intertwining hypothesis for two-chart cocycles is a single equation.** A morphism of
schemes carrying the overlap unit `u` to the overlap unit `u'` intertwines the two-chart cocycles
they generate. -/
theorem intertwines_twoChartCocycle (f : Y' ⟶ Y) (u : Γ(Y, U₀ ⊓ U₁)ˣ) (u' : Γ(Y', V₀ ⊓ V₁)ˣ)
    (h₀ : f ⁻¹ᵁ U₀ = V₀) (h₁ : f ⁻¹ᵁ U₁ = V₁)
    (hu : Units.map (f.app (U₀ ⊓ U₁)).hom u =
      overlapUnit u' (f ⁻¹ᵁ (U₀ ⊓ U₁)) (preimage_inf_le_inf f h₀ h₁)) :
    UnitTransitionCocycle.Intertwines f (twoChartCocycle (X := Y.toRingedSpace) u)
      ((twoChartCocycle (X := Y'.toRingedSpace) u').ofFamilyEq
        (twoChartFamily_eq_preimage f h₀ h₁)) := by
  rintro ⟨i⟩ ⟨j⟩ V hi hj
  cases i <;> cases j
  · exact map_one _
  · exact map_app_overlapUnit f u u' _ hu (le_inf hi hj)
  · exact (map_inv _ _).trans
      (congrArg (·⁻¹) (map_app_overlapUnit f u u' _ hu (le_inf hj hi)))
  · exact map_one _

/-- **A map of two-chart glued modules from a map of overlap units.** A morphism of schemes
carrying the overlap unit of a two-chart cover of the target to the overlap unit of the cover of
the source by the preimages induces a morphism from the module glued downstairs to the direct
image of the module glued upstairs. -/
noncomputable def glueHomOfOverlapUnit (f : Y' ⟶ Y) (u : Γ(Y, U₀ ⊓ U₁)ˣ) (u' : Γ(Y', V₀ ⊓ V₁)ˣ)
    (h₀ : f ⁻¹ᵁ U₀ = V₀) (h₁ : f ⁻¹ᵁ U₁ = V₁)
    (hu : Units.map (f.app (U₀ ⊓ U₁)).hom u =
      overlapUnit u' (f ⁻¹ᵁ (U₀ ⊓ U₁)) (preimage_inf_le_inf f h₀ h₁)) :
    (twoChartCocycle (X := Y.toRingedSpace) u).glue ⟶
      (Scheme.Modules.pushforward f).obj (twoChartCocycle (X := Y'.toRingedSpace) u').glue :=
  UnitTransitionCocycle.glueHomOfFamilyEqIntertwines _ (twoChartFamily_eq_preimage f h₀ h₁)
    (intertwines_twoChartCocycle f u u' h₀ h₁ hu)

/-- In the chart trivializations the morphism of two-chart glued modules is the map on functions.
This pins `Stacks.SheafOfModules.glueHomOfOverlapUnit` down. -/
theorem chartLinearEquiv_glueHomOfOverlapUnit (f : Y' ⟶ Y) (u : Γ(Y, U₀ ⊓ U₁)ˣ)
    (u' : Γ(Y', V₀ ⊓ V₁)ˣ) (h₀ : f ⁻¹ᵁ U₀ = V₀) (h₁ : f ⁻¹ᵁ U₁ = V₁)
    (hu : Units.map (f.app (U₀ ⊓ U₁)).hom u =
      overlapUnit u' (f ⁻¹ᵁ (U₀ ⊓ U₁)) (preimage_inf_le_inf f h₀ h₁))
    (i : ULift.{u} Bool) {V : Y.Opens}
    (hV : V ≤ twoChartFamily (X := Y.toRingedSpace) U₀ U₁ i)
    (hV' : f ⁻¹ᵁ V ≤ twoChartFamily (X := Y'.toRingedSpace) V₀ V₁ i)
    (s : (twoChartCocycle (X := Y.toRingedSpace) u).sectionsSubmodule V) :
    (twoChartCocycle (X := Y'.toRingedSpace) u').chartLinearEquiv i hV'
        ((glueHomOfOverlapUnit f u u' h₀ h₁ hu).val.app (op V) s) =
      (f.app V).hom ((twoChartCocycle (X := Y.toRingedSpace) u).chartLinearEquiv i hV s) :=
  UnitTransitionCocycle.chartLinearEquiv_glueHomOfFamilyEqIntertwines
    (twoChartCocycle (X := Y'.toRingedSpace) u') (twoChartFamily_eq_preimage f h₀ h₁)
    (intertwines_twoChartCocycle f u u' h₀ h₁ hu) i hV s

end

end Stacks.SheafOfModules

end
