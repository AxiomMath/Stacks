module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Cardinally generated sheaves of modules

A sheaf of modules is `κ`-generated when it is generated, locally on a cover, by at most `κ`
sections.

## Main definitions

* `SheafOfModules.IsCardinalGenerated`: the predicate that a sheaf of modules has a covering by
  objects over each of which a family of at most `κ` sections generates its restriction.

## Main results

* `SheafOfModules.isCardinalGenerated_iff_exists_openCover_generatingSets`: on a topological
  space, a sheaf of modules is `κ`-generated if and only if there is an open cover with, on each
  member, a generating set of sections of cardinality at most `κ`.

## References

* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v u'

namespace SheafOfModules

/-- A sheaf of modules is `κ`-generated if it has local generating families indexed by types
of cardinality at most `κ`. -/
@[stacks 077L]
abbrev IsCardinalGenerated {C : Type u'} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (κ : Cardinal.{u}) : Prop :=
  ∃ σ : M.LocalGeneratorsData.{u'}, ∀ i, Cardinal.mk (σ.generators i).I ≤ κ

/-- On a topological space, a sheaf of modules is `κ`-generated exactly when there is an open
cover and, on each member of the cover, a generating subset of sections of cardinality at most
`κ`. -/
public theorem isCardinalGenerated_iff_exists_openCover_generatingSets
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    [∀ V : Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
    [∀ V : Opens X,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (κ : Cardinal.{u}) :
    IsCardinalGenerated M κ ↔
      ∃ (ι : Type u) (U : ι → Opens X), IsOpenCover U ∧
        ∃ S : ∀ i, Set ((M.over (U i)).sections),
          (∀ i, Cardinal.mk (S i) ≤ κ) ∧
            ∀ i, ∃ g : (M.over (U i)).GeneratingSections, Set.range g.s = S i := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.I, σ.X, (Opens.coversTop_iff (X : Type u) σ.X).mp σ.coversTop,
      fun i ↦ Set.range (σ.generators i).s, fun i ↦ Cardinal.mk_range_le.trans (hσ i),
      fun i ↦ ⟨σ.generators i, rfl⟩⟩
  · rintro ⟨ι, U, hU, S, hS, hgen⟩
    let gens (i : ι) : (M.over (U i)).GeneratingSections := by
      let g := (hgen i).choose
      have hg : Set.range g.s = S i := (hgen i).choose_spec
      let f : g.I → S i := fun j ↦ ⟨g.s j, hg ▸ Set.mem_range_self j⟩
      exact
        { I := S i
          s := Subtype.val
          epi := by
            apply epi_of_epi_fac
              (f := SheafOfModules.freeMap (R := R.over (U i)) f) (h := g.π)
            apply (M.over (U i)).freeHomEquiv.injective
            funext j
            rw [SheafOfModules.freeHomEquiv_comp_apply,
              SheafOfModules.freeHomEquiv_freeMap]
            simpa [f] using
              SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
                (R := R.over (U i)) (fun x : S i ↦ x.1) (f j) }
    exact ⟨
      { I := ι
        X := U
        coversTop := (Opens.coversTop_iff (X : Type u) U).mpr hU
        generators := gens }, hS⟩

end SheafOfModules

end
