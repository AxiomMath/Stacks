module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Splitting the counit of an adjunction is a property of the objects, not of the map

Let `L ⊣ R` be an adjunction and `Y` an object of the target category.  Every morphism
`L.obj (R.obj Y) ⟶ Y` factors through the counit on the right, so a splitting of any one of them
splits the counit itself: if `v : L.obj (R.obj Y) ⟶ Y` has a section `s`, then
`s ≫ L.map (adj.homEquiv _ _ v)` is a section of `adj.counit.app Y`.  In particular the counit at
`Y` is a split epimorphism as soon as `Y` is a retract of an object isomorphic to
`L.obj (R.obj Y)`, through arbitrary morphisms.

## Main results

* `Stacks.Adjunction.map_homEquiv_comp_counit`: a morphism `L.obj (R.obj Y) ⟶ Y` is the transpose
  of its own image under the hom-set bijection, hence factors through the counit.
* `Stacks.Adjunction.splitEpiCounitOfSplitEpi`: a splitting of any morphism
  `L.obj (R.obj Y) ⟶ Y` splits the counit at `Y`.
* `Stacks.Adjunction.splitEpiCounitOfRetract`,
  `Stacks.Adjunction.splitEpiCounitOfRetractIso` and
  `Stacks.Adjunction.splitEpiCounitOfIsoRetract`: the same, phrased as `Y` being a retract of
  `L.obj (R.obj Y)`, respectively of an object isomorphic to it, respectively isomorphic to a
  retract of such an object.
* `Stacks.Adjunction.isSplitEpi_counit_of_isSplitEpi`: the propositional form.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- **Every morphism `L.obj (R.obj Y) ⟶ Y` factors through the counit.**  It is `L` applied to its
image under the hom-set bijection of the adjunction, followed by the counit. -/
theorem map_homEquiv_comp_counit (adj : L ⊣ R) {Y : D} (v : L.obj (R.obj Y) ⟶ Y) :
    L.map (adj.homEquiv (R.obj Y) Y v) ≫ adj.counit.app Y = v :=
  (adj.homEquiv (R.obj Y) Y).symm_apply_apply v

/-- **A splitting of any morphism `v : L.obj (R.obj Y) ⟶ Y` splits the counit at `Y`.**  The
section is the section of `v` followed by `L.map (adj.homEquiv _ _ v)`. -/
noncomputable def splitEpiCounitOfSplitEpi (adj : L ⊣ R) {Y : D}
    {v : L.obj (R.obj Y) ⟶ Y} (hv : SplitEpi v) : SplitEpi (adj.counit.app Y) where
  section_ := hv.section_ ≫ L.map (adj.homEquiv (R.obj Y) Y v)
  id := by
    rw [Category.assoc, map_homEquiv_comp_counit]
    exact hv.id

/-- **If `Y` is a retract of `L.obj (R.obj Y)` then the counit at `Y` is a split epimorphism.**
The two morphisms witnessing the retract are arbitrary. -/
noncomputable def splitEpiCounitOfRetract (adj : L ⊣ R) {Y : D} (s : Y ⟶ L.obj (R.obj Y))
    (v : L.obj (R.obj Y) ⟶ Y) (h : s ≫ v = 𝟙 Y) : SplitEpi (adj.counit.app Y) :=
  splitEpiCounitOfSplitEpi adj (v := v) ⟨s, h⟩

/-- **If `Y` is a retract of an object isomorphic to `L.obj (R.obj Y)` then the counit at `Y` is a
split epimorphism.**  The isomorphism is arbitrary: it is not asked to be compatible with the unit
or the counit. -/
noncomputable def splitEpiCounitOfRetractIso (adj : L ⊣ R) {Y W : D}
    (θ : L.obj (R.obj Y) ≅ W) (s : Y ⟶ W) (v : W ⟶ Y) (h : s ≫ v = 𝟙 Y) :
    SplitEpi (adj.counit.app Y) :=
  splitEpiCounitOfRetract adj (s ≫ θ.inv) (θ.hom ≫ v) (by
    rw [Category.assoc, ← Category.assoc θ.inv, θ.inv_hom_id, Category.id_comp, h])

/-- **If `Y` is isomorphic to a retract of an object isomorphic to `L.obj (R.obj Y)` then the
counit at `Y` is a split epimorphism.** -/
noncomputable def splitEpiCounitOfIsoRetract (adj : L ⊣ R) {Y W M : D}
    (θ : L.obj (R.obj Y) ≅ W) (ψ : M ≅ Y) (σ : M ⟶ W) (η : W ⟶ M) (h : σ ≫ η = 𝟙 M) :
    SplitEpi (adj.counit.app Y) :=
  splitEpiCounitOfRetractIso adj θ (ψ.inv ≫ σ) (η ≫ ψ.hom) (by
    rw [Category.assoc, ← Category.assoc σ, h, Category.id_comp, ψ.inv_hom_id])

/-- The propositional form of `Stacks.Adjunction.splitEpiCounitOfSplitEpi`. -/
theorem isSplitEpi_counit_of_isSplitEpi (adj : L ⊣ R) {Y : D} (v : L.obj (R.obj Y) ⟶ Y)
    [IsSplitEpi v] : IsSplitEpi (adj.counit.app Y) :=
  ⟨⟨splitEpiCounitOfSplitEpi adj (IsSplitEpi.exists_splitEpi (f := v)).some⟩⟩

end Stacks.Adjunction

end
