module

public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverAWellOrderedCover

/-!
# The glued object of a system of complexes along an increasing cover

This file carries the *assembly* step of the proof of [Stacks, Tag 0D6B]: the passage from a
system of complexes of sheaves of modules supported on the members of an increasing open cover,
with strictly transitive transition maps, to a single object of the derived category on `⊤`
whose restrictions are the prescribed objects.

The source's recursion produces maps of complexes `τ_{β,α} : (j_β)_! I^•_β ⟶ (j_α)_! I^•_α`
which compose *strictly*, and takes the glued object to be represented by the termwise colimit
`colim_α (j_α)_! I^•_α`.  Strict transitivity is exactly functoriality, so the system is
packaged here as a **functor `F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ`** out of the index order.  That
reformulation is what removes the recursion from this half of the tag: nothing in this file is
transfinite, and no uniqueness statement is used.

## Main definitions

* `Stacks.DerivedGlueing.transitionToward`, `coconeToward`, `colimitToward`: the retraction of a
  colimit over a linear order onto a stage above which the diagram is constant.
* `Stacks.DerivedGlueing.glueingComplex`, `glueingObject`: the colimit of the system, read on the
  open subspace `⊤`, and its class in the derived category.
* `Stacks.DerivedGlueing.glueingRestrictionIso`: the identification `σ_α` of the restriction of
  the glued object to `W α` with the prescribed object there.
* `Stacks.DerivedGlueing.glueingTransitionIso`: the transition `ρ^α_β` that the system of
  complexes determines, for `β ≤ α`.
* `Stacks.DerivedGlueing.colimitWitness`: a non-degenerate witness for the colimit lemma.

## Main results

* `Stacks.DerivedGlueing.isIso_colimit_ι_of_isIso_map_above`: **a colimit over a linear order is
  attained at any stage above which the diagram is constant.** This replaces the appeal to
  cofinality of `{β | α ≤ β}` that the route for this tag recorded: the inverse is the descent of
  a cocone whose leg at `β` goes up to `max β α` and comes back down, so no filteredness of the
  index category, no connectedness of the subdiagram above `α` and no `Functor.Final` is needed.
* `Stacks.DerivedGlueing.quasiIso_jStar_map_colimit_ι`: **the restriction to `W α` of the colimit
  inclusion at `α` is a quasi-isomorphism**, given that the restriction to `W β` of a transition
  `F β ⟶ F α` is one whenever `β ≤ α`.  Nothing is assumed of `W`.
* `Stacks.DerivedGlueing.not_isIso_colimit_ι_colimitWitness_zero`: the negative control, proved
  as a negation — the conclusion of the colimit lemma really does fail at a stage below which the
  diagram grows.
* `Stacks.DerivedGlueing.glueing_compatibility`: **the identifications `σ_α` of the restrictions
  of the glued object are compatible with the transitions `ρ^α_β` the system determines**,
  unconditionally.
* `Stacks.DerivedGlueing.exists_glueing_of_complexSystem`: **the glueing problem of
  [Stacks, Tag 0D6B] is solved by a system of complexes**, unconditionally.

## What is proved and what is not

Writing `σ_α` for `Stacks.DerivedGlueing.glueingRestrictionIso` and `ρ^α_β` for
`Stacks.DerivedGlueing.glueingTransitionIso`, this file produces the glued object, both families
of isomorphisms, and their compatibility, unconditionally.  The assembly half of
[Stacks, Tag 0D6B] is therefore complete, and it is
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem`.

The mathematical content of the compatibility is the cocone law
`F.map h ≫ colimit.ι F α = colimit.ι F β`, read against the counit of extension by zero on the
middle open: degreewise both sides of the equation are that counit at `F α` followed by the
colimit inclusion, on one side by the triangle identity of `j_! ⊣ j^*` and on the other by its
naturality.  That is `Stacks.DerivedGlueing.jStar_jShriek_counit_key`, and it is the only place
where anything is computed.  What makes the rest long is bookkeeping, since
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp` is pinned down only on the image of
`DerivedCategory.Q`, by
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'`, which identifies it with the
prolongation of `Stacks.DerivedGlueing.openModuleRestrictionComparison` — the counit of
extension by zero on the middle open.  Both `σ_α` and `ρ^α_β` contain the inverse of a `Q.map`,
so the equation is first cleared of those inverses
(`Stacks.DerivedGlueing.Q_map_colimit_ι_comp_glueingComplexRestrictionIso`,
`Stacks.DerivedGlueing.Q_map_comp_glueingComplexTransitionIso`), and the action of the displayed
restriction functor is carried across the comparison with its complex-level model by
`Stacks.DerivedGlueing.transportHom`, whose multiplicativity is what makes a cleared equation
transportable at all.

The system of complexes is produced from prescribed objects `K α` and prescribed transitions
by the transfinite recursion of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion`, whose limit
stages consume the uniqueness clause of [Stacks, Tag 0D68] and the assembly of this file
relativized to an open, `Stacks.DerivedGlueing.exists_glueing_of_complexSystem_over_of_le`.

A non-degenerate inhabitant of the datum `(F, I, hsupp, hqi)` over an index order with no
greatest element is the filtration of a fixed complex `A` on `X` by its extensions by zero off
the members of the cover,

```
F.obj α = (j_α)_! (j_α)^* A,     I α = (j_α)^* A,     hsupp α = Iso.refl _
```

`Stacks.DerivedGlueing.globalFiltrationSystem` and
`Stacks.DerivedGlueing.exists_glueing_of_globalFiltration` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemFromGlobalComplex`, on the
carrier `Stacks.DerivedGlueing.natLine` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.NonDegenerateIncreasingCover`.

Nothing in this file is tagged: all of it is a step of the source's *proof* of
[Stacks, Tag 0D6B], not a clause of its statement.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.DerivedGlueing

universe w v u

/-! ### A colimit over a linear order attained at a stage -/

section ColimitAttained

variable {A : Type u} [Category.{w} A] {E : Type v} [LinearOrder E] (D : E ⥤ A) {α : E}
  (hiso : ∀ (β : E) (h : α ≤ β), IsIso (D.map h.hom))

/-- The comparison `D β ⟶ D α` available once every transition out of `α` is invertible: go up
to `max β α` and come back down. -/
def transitionToward (β : E) : D.obj β ⟶ D.obj α :=
  letI := hiso (max β α) (le_max_right β α)
  D.map (le_max_left β α).hom ≫ inv (D.map (le_max_right β α).hom)

/-- The comparison unfolds to the composite through `max β α`, for any instance. -/
private theorem transitionToward_eq (β : E) [IsIso (D.map (le_max_right β α).hom)] :
    transitionToward D hiso β =
      D.map (le_max_left β α).hom ≫ inv (D.map (le_max_right β α).hom) := rfl

/-- The comparison at `α` itself is the identity. -/
theorem transitionToward_self : transitionToward D hiso α = 𝟙 (D.obj α) := by
  have := hiso (max α α) (le_max_right α α)
  rw [transitionToward_eq, IsIso.hom_inv_id]

/-- The comparison is a retraction of every cocone: composing it with the leg at `α` gives the
leg at `β`. -/
theorem transitionToward_comp (c : Cocone D) (β : E) :
    transitionToward D hiso β ≫ c.ι.app α = c.ι.app β := by
  have := hiso (max β α) (le_max_right β α)
  have h1 : inv (D.map (le_max_right β α).hom) ≫ c.ι.app α = c.ι.app (max β α) := by
    rw [IsIso.inv_comp_eq]
    exact (c.w (le_max_right β α).hom).symm
  rw [transitionToward_eq, Category.assoc, h1]
  exact c.w (le_max_left β α).hom

/-- The comparisons assemble into a cocone with vertex `D α`. -/
def coconeToward : Cocone D where
  pt := D.obj α
  ι :=
    { app := transitionToward D hiso
      naturality := by
        intro β β' f
        let := hiso (max β α) (le_max_right β α)
        let := hiso (max β' α) (le_max_right β' α)
        have hmm' : max β α ≤ max β' α :=
          max_le (f.le.trans (le_max_left β' α)) (le_max_right β' α)
        have hb : transitionToward D hiso β =
            D.map (le_max_left β α).hom ≫ inv (D.map (le_max_right β α).hom) := rfl
        have hb' : transitionToward D hiso β' =
            D.map (le_max_left β' α).hom ≫ inv (D.map (le_max_right β' α).hom) := rfl
        have key : D.map hmm'.hom ≫ inv (D.map (le_max_right β' α).hom) =
            inv (D.map (le_max_right β α).hom) := by
          rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp, ← Functor.map_comp]
          exact congrArg D.map (Subsingleton.elim _ _)
        have step : D.map f ≫ D.map (le_max_left β' α).hom =
            D.map (le_max_left β α).hom ≫ D.map hmm'.hom := by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg D.map (Subsingleton.elim _ _)
        have goal : D.map f ≫ transitionToward D hiso β' = transitionToward D hiso β := by
          rw [hb, hb', ← Category.assoc, step, Category.assoc, key]
        simpa using goal }

/-- The leg of `Stacks.DerivedGlueing.coconeToward` at `β` is
`Stacks.DerivedGlueing.transitionToward` at `β`. -/
@[simp]
theorem coconeToward_ι_app (β : E) : (coconeToward D hiso).ι.app β = transitionToward D hiso β :=
  rfl

/-- The retraction of the colimit onto the stage `α`, descended from
`Stacks.DerivedGlueing.coconeToward`. -/
def colimitToward [HasColimit D] : colimit D ⟶ D.obj α :=
  colimit.desc D (coconeToward D hiso)

/-- The colimit inclusion at `β` followed by `Stacks.DerivedGlueing.colimitToward` is
`Stacks.DerivedGlueing.transitionToward` at `β`. -/
@[simp]
theorem ι_colimitToward [HasColimit D] (β : E) :
    colimit.ι D β ≫ colimitToward D hiso = transitionToward D hiso β :=
  colimit.ι_desc (coconeToward D hiso) β

include hiso in
/-- **A colimit over a linear order is attained at any stage above which the diagram is
constant.** If every transition `D α ⟶ D β` with `α ≤ β` is invertible, then the colimit
inclusion at `α` is invertible.

This is the elementary replacement for an appeal to cofinality of `{β | α ≤ β}`: the inverse is
`Stacks.DerivedGlueing.colimitToward`, the descent of the cocone whose leg at `β` goes up to
`max β α` and back down, and which needs no filteredness of the index category and no
connectedness of the subdiagram above `α`. -/
theorem isIso_colimit_ι_of_isIso_map_above [HasColimit D] : IsIso (colimit.ι D α) := by
  refine ⟨colimitToward D hiso, ?_, ?_⟩
  · rw [ι_colimitToward]
    exact transitionToward_self D hiso
  · refine colimit.hom_ext fun β => ?_
    have h : colimit.ι D β ≫ colimitToward D hiso ≫ colimit.ι D α = colimit.ι D β := by
      rw [← Category.assoc, ι_colimitToward]
      exact transitionToward_comp D hiso (colimit.cocone D) β
    simpa using h

end ColimitAttained

/-! ### A non-degenerate witness, and the failure of the conclusion below the stage -/

section ColimitWitness

/-- The stages of the witness diagram: `∅` at `0`, and `{0}` at every later stage. -/
def colimitWitnessFamily (n : ℕ) : Set ℕ := Set.Iio (min n 1)

/-- The family `Stacks.DerivedGlueing.colimitWitnessFamily` is monotone. -/
theorem colimitWitnessFamily_monotone : Monotone colimitWitnessFamily :=
  fun _ _ h => Set.Iio_subset_Iio (min_le_min h le_rfl)

/-- **A diagram over `ℕ` which is not constant below the stage `1` and is constant above it:**
its value is `∅` at `0` and `{0}` at every later stage, read in the complete lattice `Set ℕ`
viewed as a category, where colimits are suprema
(`CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup`).

This is the non-degeneracy certificate for
`Stacks.DerivedGlueing.isIso_colimit_ι_of_isIso_map_above`: the hypothesis is satisfied at the
stage `1` (`Stacks.DerivedGlueing.isIso_colimit_ι_colimitWitness`) while the diagram is *not*
constant — its value at `0` is `∅` and at `1` is `{0}` — and the conclusion genuinely fails at
the stage `0` (`Stacks.DerivedGlueing.not_isIso_colimit_ι_colimitWitness_zero`). -/
def colimitWitness : ℕ ⥤ Set ℕ := colimitWitnessFamily_monotone.functor

/-- The value of `Stacks.DerivedGlueing.colimitWitness` at `n` is `Set.Iio (min n 1)`. -/
theorem colimitWitness_obj (n : ℕ) : colimitWitness.obj n = Set.Iio (min n 1) := rfl

/-- Every transition of `Stacks.DerivedGlueing.colimitWitness` out of a positive stage is
invertible, its source and target being the same subset. -/
theorem isIso_colimitWitness_map {β γ : ℕ} (hβ : 1 ≤ β) (h : β ≤ γ) :
    IsIso (colimitWitness.map h.hom) := by
  have he : colimitWitness.obj β = colimitWitness.obj γ := by
    rw [colimitWitness_obj, colimitWitness_obj, min_eq_right hβ, min_eq_right (hβ.trans h)]
  rw [Subsingleton.elim (colimitWitness.map h.hom) (homOfLE (le_of_eq he))]
  exact homOfLE_isIso_of_eq (le_of_eq he) he

/-- **The hypothesis of `Stacks.DerivedGlueing.isIso_colimit_ι_of_isIso_map_above` is satisfied
at the stage `1` by `Stacks.DerivedGlueing.colimitWitness`,** so its conclusion holds there. -/
theorem isIso_colimit_ι_colimitWitness : IsIso (colimit.ι colimitWitness 1) :=
  isIso_colimit_ι_of_isIso_map_above colimitWitness fun _ h => isIso_colimitWitness_map le_rfl h

/-- **The conclusion fails at the stage `0`.** Were the colimit inclusion at `0` invertible, the
colimit would be `∅`, while it contains the stage at `1`, which is `{0}`.  So the hypothesis of
`Stacks.DerivedGlueing.isIso_colimit_ι_of_isIso_map_above` is neither vacuous nor removable, and
the diagram above is a genuine instance of it rather than a constant diagram in disguise.

This is the negation itself, proved, not the observation that a proof was not found. -/
theorem not_isIso_colimit_ι_colimitWitness_zero : ¬ IsIso (colimit.ι colimitWitness 0) := by
  intro hiso
  have h3 : colimitWitness.obj 1 ≤ colimitWitness.obj 0 :=
    (leOfHom (colimit.ι colimitWitness 1)).trans
      (leOfHom (inv (colimit.ι colimitWitness 0)))
  rw [colimitWitness_obj, colimitWitness_obj] at h3
  have h4 : (0 : ℕ) ∈ Set.Iio (min (0 : ℕ) 1) := h3 (by simp)
  simp at h4

end ColimitWitness

/-! ### The restriction of the colimit inclusion is a quasi-isomorphism -/

section QuasiIsoColimit

open ExtensionByZeroModules

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]

/-- **Restriction of modules to an open subspace preserves all colimits**, being a left adjoint
(`ExtensionByZeroModules.jStarAdjunction`). -/
instance jStar_preservesColimitsOfSize (U : Opens X.carrier) :
    PreservesColimitsOfSize.{u, u} (jStar U (underlyingRingSheaf X)) :=
  (jStarAdjunction U (underlyingRingSheaf X)).leftAdjoint_preservesColimits

/-- The degree-`n` homology of the restriction to `U` of a complex of `𝒪_X`-modules, as a
functor.  It is the composite through which
`Stacks.DerivedGlueing.quasiIso_jStar_map_colimit_ι` reads a quasi-isomorphism degreewise. -/
abbrev restrictHomologyFunctor (X : RingedSpace.{u, u}) (U : Opens X.carrier) (n : ℤ) :
    CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ ⥤
      SheafOfModules.{u} (restrictedRingSheaf X U) :=
  (jStar U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (restrictedRingSheaf X U)) (ComplexShape.up ℤ) n

/-- **The restriction to `W α` of the colimit inclusion at `α` is a quasi-isomorphism.** Let
`F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ` be a system of complexes indexed by a nonempty linear
order, and suppose that restricting a transition `F β ⟶ F α` to `W β` is a quasi-isomorphism
whenever `β ≤ α`. Then restricting the colimit inclusion `F α ⟶ colim F` to `W α` is a
quasi-isomorphism.

Nothing is assumed of `W` beyond its being a family of opens: neither monotonicity nor that the
`W α` cover.  The proof is the degreewise one: homology commutes with the colimit (the index
category is filtered, being a nonempty linear order, and the category of sheaves of modules is
Grothendieck abelian), and in each degree the resulting diagram is constant above `α`, so
`Stacks.DerivedGlueing.isIso_colimit_ι_of_isIso_map_above` applies. -/
theorem quasiIso_jStar_map_colimit_ι (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (α : E) :
    QuasiIso (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (colimit.ι F α)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : PreservesColimitsOfShape E
      (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X (W α))) (ComplexShape.up ℤ) n) :=
    Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor _ _
  have hiso : ∀ (β : E) (h : α ≤ β),
      IsIso ((F ⋙ restrictHomologyFunctor X (W α) n).map h.hom) := by
    intro β h
    have h2 := (hqi α β h).quasiIsoAt n
    rw [quasiIsoAt_iff_isIso_homologyMap] at h2
    exact h2
  have key : IsIso ((restrictHomologyFunctor X (W α) n).map (colimit.ι F α)) := by
    rw [← ι_preservesColimitIso_inv]
    have := isIso_colimit_ι_of_isIso_map_above (F ⋙ restrictHomologyFunctor X (W α) n) hiso
    infer_instance
  exact key

end QuasiIsoColimit

/-! ### The glued complex, the glued object, and the identification of its restrictions -/

section Glueing

open ExtensionByZeroModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]

/-- **Extension by zero along `⊤` undoes restriction to `⊤`, on complexes.** The complex-level
form of `Stacks.DerivedGlueing.jStarTopCompJShriekTopIso`. -/
def topRoundTripIso (X : RingedSpace.{u, u}) :
    (jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (jStarTopCompJShriekTopIso (underlyingRingSheaf X)) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)

/-- **Restriction to an open undoes extension by zero from it, on complexes.** The complex-level
form of the invertibility of the unit of `ExtensionByZeroModules.jShriekAdjunction`, which holds
for an arbitrary open. -/
def jShriekJStarIso (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    𝟭 (CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) ≅
      (jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (jStar U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex
      (@asIso _ _ _ _ (jShriekAdjunction U (underlyingRingSheaf X)).unit
        (isIso_jShriekAdjunction_unit U (underlyingRingSheaf X))) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := jShriek U (underlyingRingSheaf X)) (G := jStar U (underlyingRingSheaf X))
      (H := jShriek U (underlyingRingSheaf X) ⋙ jStar U (underlyingRingSheaf X))
      (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- **Restriction from `U` to `V` is extension by zero along `U` followed by restriction to
`V`, on complexes.** -/
def openModuleRestrictionMapIso (X : RingedSpace.{u, u}) (V U : Opens X.carrier) (hVU : V ≤ U) :
    (openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (jShriek U (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (F := jShriek U (underlyingRingSheaf X)) (G := jStar V (underlyingRingSheaf X))
    (H := openModuleRestriction X V U hVU) (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- **The glued complex of a system of complexes**: the colimit of the system, read on the open
subspace `⊤`.

This is the complex the source's proof of [Stacks, Tag 0D6B] takes for the glued object:
`colim_α (W_α → X)_! I^•_α`, which is `colimit F` since the `F α` are already the extensions by
zero of the `I α`, pushed to the open-subspace model of `⊤`. -/
def glueingComplex (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) ℤ :=
  ((jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (colimit F)

/-- **The glued object of the derived category** of a system of complexes. -/
def glueingObject (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    OpenDerivedCategory X ⊤ :=
  DerivedCategory.Q.obj (glueingComplex F)

/-- **The restriction of the glued object to `W α` is the prescribed object there.** Let
`F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ` be a system of complexes over a nonempty linear order,
let `I α` be a complex of modules on `W α` with `F α ≅ (j_α)_! I α`, and assume that the
restriction to `W β` of a transition `F β ⟶ F α` is a quasi-isomorphism whenever `β ≤ α`.  Then
the restriction of `Stacks.DerivedGlueing.glueingObject F` to `W α`, in the system `S`, is
`Q (I α)`.

This is the identification the source's proof of [Stacks, Tag 0D6B] produces at each stage, and
it is assembled from: the comparison of the displayed restriction with the functor induced by
restriction of complexes (`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`); the
factorization of that functor through the localization
(`CategoryTheory.Functor.mapDerivedCategoryFactors`); the two round trips
`Stacks.DerivedGlueing.topRoundTripIso` and `Stacks.DerivedGlueing.jShriekJStarIso`; and the
quasi-isomorphism `Stacks.DerivedGlueing.quasiIso_jStar_map_colimit_ι`, which is where the
transfinite content sits and which becomes invertible in the derived category. -/
def glueingComplexRestrictionIso (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (α : E) :
    DerivedCategory.Q.obj
        (((openModuleRestriction X (W α) ⊤ le_top).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (glueingComplex F)) ≅
      DerivedCategory.Q.obj (I α) :=
  letI : IsIso (DerivedCategory.Q.map
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_jStar_map_colimit_ι W F hqi α)
  DerivedCategory.Q.mapIso
      ((openModuleRestrictionMapIso X (W α) ⊤ le_top).app (glueingComplex F)) ≪≫
    DerivedCategory.Q.mapIso
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso ((topRoundTripIso X).app (colimit F))) ≪≫
    (asIso (DerivedCategory.Q.map
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α)))).symm ≪≫
    DerivedCategory.Q.mapIso
      (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (hsupp α)) ≪≫
    DerivedCategory.Q.mapIso ((jShriekJStarIso X (W α)).symm.app (I α))

/-- **The restriction of the glued object to `W α`, in the system `S`, is the prescribed object
there.**  The displayed restriction is compared with restriction of complexes by the field
`restrictionFactors` of the system, and the rest is
`Stacks.DerivedGlueing.glueingComplexRestrictionIso`. -/
def glueingRestrictionIso (S : LocallyGiven X) (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (α : E) :
    (S.restriction (W α) ⊤ le_top).obj (glueingObject F) ≅ DerivedCategory.Q.obj (I α) :=
  (S.restrictionFactors (W α) ⊤ le_top).app (glueingComplex F) ≪≫
    glueingComplexRestrictionIso W F I hsupp hqi α

/-- **The transition isomorphism carried by the system of complexes**, on complexes: for
`β ≤ α` the restriction to `W β` of the prescribed complex on `W α` is the prescribed complex on
`W β`, in the derived category.

This is the datum `ρ^α_β` of [Stacks, Tag 0D6B] as the system of complexes determines it: the
hypothesis `hqi` says precisely that the transition `F β ⟶ F α`, restricted to `W β`, is a
quasi-isomorphism, hence invertible after `DerivedCategory.Q`. -/
def glueingComplexTransitionIso (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    DerivedCategory.Q.obj
        (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I α)) ≅
      DerivedCategory.Q.obj (I β) :=
  letI : IsIso (DerivedCategory.Q.map
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hqi β α h)
  DerivedCategory.Q.mapIso ((openModuleRestrictionMapIso X (W β) (W α) hβα).app (I α)) ≪≫
    DerivedCategory.Q.mapIso
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (hsupp α).symm) ≪≫
    (asIso (DerivedCategory.Q.map
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))).symm ≪≫
    DerivedCategory.Q.mapIso
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (hsupp β)) ≪≫
    DerivedCategory.Q.mapIso ((jShriekJStarIso X (W β)).symm.app (I β))

/-- **The transition isomorphism carried by the system of complexes**, read in the system `S`:
the datum `ρ^α_β` of [Stacks, Tag 0D6B]. -/
def glueingTransitionIso (S : LocallyGiven X) (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (S.restriction (W β) (W α) hβα).obj (DerivedCategory.Q.obj (I α)) ≅
      DerivedCategory.Q.obj (I β) :=
  (S.restrictionFactors (W β) (W α) hβα).app (I α) ≪≫
    glueingComplexTransitionIso W F I hsupp hqi hβα h

end Glueing

/-! ### Transporting a morphism along a comparison of a functor with its model -/

section Transport

variable {CB CA DB DA : Type*} [Category CB] [Category CA] [Category DB] [Category DA]
  (QB : CB ⥤ DB) (QA : CA ⥤ DA) {R : DB ⥤ DA} {rr : CB ⥤ CA} (φ : QB ⋙ R ≅ rr ⋙ QA)

/-- **The transport of an endomorphism-shaped morphism along a comparison.** Given a comparison
`φ : QB ⋙ R ≅ rr ⋙ QA` of a functor `R` between the targets of `QB` and `QA` with a model `rr`
between their sources, a morphism `QB C₁ ⟶ QB C₂` is carried to a morphism
`QA (rr C₁) ⟶ QA (rr C₂)` by conjugating its image under `R`. -/
def transportHom {C₁ C₂ : CB} (u : QB.obj C₁ ⟶ QB.obj C₂) :
    QA.obj (rr.obj C₁) ⟶ QA.obj (rr.obj C₂) :=
  φ.inv.app C₁ ≫ R.map u ≫ φ.hom.app C₂

/-- The defining property of the transport: it is what `R.map` becomes after the comparison. -/
theorem map_comp_hom_app {C₁ C₂ : CB} (u : QB.obj C₁ ⟶ QB.obj C₂) :
    R.map u ≫ φ.hom.app C₂ = φ.hom.app C₁ ≫ transportHom QB QA φ u := by
  simp [transportHom]

/-- The transport of an identity is an identity. -/
@[simp]
theorem transportHom_id (C₁ : CB) : transportHom QB QA φ (𝟙 (QB.obj C₁)) = 𝟙 _ := by
  simp [transportHom]

/-- The transport is multiplicative. -/
theorem transportHom_comp {C₁ C₂ C₃ : CB} (u : QB.obj C₁ ⟶ QB.obj C₂)
    (v : QB.obj C₂ ⟶ QB.obj C₃) :
    transportHom QB QA φ (u ≫ v) = transportHom QB QA φ u ≫ transportHom QB QA φ v := by
  simp [transportHom]

/-- The transport of the image of a morphism of the sources is the image of its image. -/
@[simp]
theorem transportHom_map {C₁ C₂ : CB} (f : C₁ ⟶ C₂) :
    transportHom QB QA φ (QB.map f) = QA.map (rr.map f) := by
  have h := φ.hom.naturality f
  simp only [Functor.comp_map] at h
  rw [transportHom, h]
  simp

/-- The transport of an isomorphism is an isomorphism. -/
instance transportHom_isIso {C₁ C₂ : CB} (u : QB.obj C₁ ⟶ QB.obj C₂) [IsIso u] :
    IsIso (transportHom QB QA φ u) := by
  rw [transportHom]
  infer_instance

/-- The transport of an inverse is the inverse of the transport. -/
theorem transportHom_inv {C₁ C₂ : CB} (u : QB.obj C₁ ⟶ QB.obj C₂) [IsIso u] :
    transportHom QB QA φ (inv u) = inv (transportHom QB QA φ u) := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  rw [← transportHom_comp, IsIso.hom_inv_id, transportHom_id]

/-- The image under two successive functors of an inverse cancels the image of the
isomorphism.  Stated with every category, functor and object a variable, so that applying it
costs one unification instead of a chain of rewrites inside a large composite. -/
theorem map_map_inv_comp_map_map_hom_assoc {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] (G : 𝒜 ⥤ ℬ) (H : ℬ ⥤ 𝒞) {A B : 𝒜} (e : A ≅ B) {Z : 𝒞}
    (f : H.obj (G.obj B) ⟶ Z) :
    H.map (G.map e.inv) ≫ H.map (G.map e.hom) ≫ f = f := by
  rw [← Category.assoc, ← H.map_comp, ← G.map_comp, e.inv_hom_id, G.map_id, H.map_id,
    Category.id_comp]

/-- The image of an isomorphism cancels the image of its inverse.  Stated with every category,
functor and object a variable, for the same reason as
`Stacks.DerivedGlueing.map_map_inv_comp_map_map_hom_assoc`. -/
theorem map_map_hom_inv_comp_assoc {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (H : 𝒜 ⥤ ℬ)
    {A B : 𝒜} (e : A ≅ B) {Z : ℬ} (f : H.obj A ⟶ Z) :
    H.map e.hom ≫ H.map e.inv ≫ f = f := by
  rw [← Category.assoc, ← H.map_comp, e.hom_inv_id, H.map_id, Category.id_comp]

end Transport

/-! ### The counit identity behind the compatibility of the glued identifications -/

section CounitKey

open ExtensionByZeroModules

variable (X : RingedSpace.{u, u})

/-- **The identity on sheaves of modules behind the compatibility of the glued object with the
transitions.** Let `A ⊆ B` be opens, let `M` be a sheaf of modules on `B`, let `N`, `D`, `P` be
sheaves of modules on `X`, and suppose given `u : N ⟶ (j_B)_! M` with a retraction `v`, a map
`i : N ⟶ D`, and `s : D ⟶ P` with a retraction `t`.  Then the two ways of comparing `N` with `D`
over `A` — through the identification of `N` with the extension by zero of `M` and through `P` —
agree.

Both sides are the restriction to `A` of the counit of extension by zero along `B` at `N`,
followed by `i`: on the left because the counit at `(j_B)_! M` is the inverse of the extension
by zero of the unit (the triangle identity), and on the right by its naturality at `i ≫ s`.
This is the whole mathematical content of
`Stacks.DerivedGlueing.glueing_compatibility`; everything else in that proof is bookkeeping. -/
theorem jStar_jShriek_counit_key (A B : Opens X.carrier)
    {M : SheafOfModules.{u} (restrictedRingSheaf X B)}
    {N D P : SheafOfModules.{u} (underlyingRingSheaf X)}
    (u : N ⟶ (jShriek B (underlyingRingSheaf X)).obj M)
    (v : (jShriek B (underlyingRingSheaf X)).obj M ⟶ N)
    (e : (jStar B (underlyingRingSheaf X)).obj ((jShriek B (underlyingRingSheaf X)).obj M) ⟶ M)
    (i : N ⟶ D) (s : D ⟶ P) (t : P ⟶ D)
    (huv : u ≫ v = 𝟙 N) (hst : s ≫ t = 𝟙 D)
    (he : e ≫ (jShriekAdjunction B (underlyingRingSheaf X)).unit.app M = 𝟙 _) :
    (jStar A (underlyingRingSheaf X)).map
          ((jShriek B (underlyingRingSheaf X)).map
            ((jStar B (underlyingRingSheaf X)).map u)) ≫
        (jStar A (underlyingRingSheaf X)).map
          ((jShriek B (underlyingRingSheaf X)).map e) ≫
        (jStar A (underlyingRingSheaf X)).map v ≫
        (jStar A (underlyingRingSheaf X)).map i =
      (jStar A (underlyingRingSheaf X)).map
          ((jShriek B (underlyingRingSheaf X)).map
            ((jStar B (underlyingRingSheaf X)).map i)) ≫
        (jStar A (underlyingRingSheaf X)).map
          ((jShriek B (underlyingRingSheaf X)).map
            ((jStar B (underlyingRingSheaf X)).map s)) ≫
        (jStar A (underlyingRingSheaf X)).map
          ((jShriekAdjunction B (underlyingRingSheaf X)).counit.app P) ≫
        (jStar A (underlyingRingSheaf X)).map t := by
  have hεe : (jShriek B (underlyingRingSheaf X)).map e =
      (jShriekAdjunction B (underlyingRingSheaf X)).counit.app
        ((jShriek B (underlyingRingSheaf X)).obj M) := by
    calc (jShriek B (underlyingRingSheaf X)).map e
        = (jShriek B (underlyingRingSheaf X)).map e ≫
            ((jShriek B (underlyingRingSheaf X)).map
                ((jShriekAdjunction B (underlyingRingSheaf X)).unit.app M) ≫
              (jShriekAdjunction B (underlyingRingSheaf X)).counit.app _) := by
          rw [(jShriekAdjunction B (underlyingRingSheaf X)).left_triangle_components M,
            Category.comp_id]
      _ = (jShriek B (underlyingRingSheaf X)).map
            (e ≫ (jShriekAdjunction B (underlyingRingSheaf X)).unit.app M) ≫
              (jShriekAdjunction B (underlyingRingSheaf X)).counit.app _ := by
          rw [Functor.map_comp, Category.assoc]
      _ = (jShriekAdjunction B (underlyingRingSheaf X)).counit.app _ := by
          rw [he, CategoryTheory.Functor.map_id, Category.id_comp]
  have hu := (jShriekAdjunction B (underlyingRingSheaf X)).counit.naturality u
  have hi := (jShriekAdjunction B (underlyingRingSheaf X)).counit.naturality (i ≫ s)
  simp only [Functor.comp_map, Functor.id_map] at hu hi
  simp only [← Functor.map_comp]
  refine congrArg (jStar A (underlyingRingSheaf X)).map ?_
  rw [hεe, reassoc_of% hu, ← Category.assoc u v i, huv, Category.id_comp,
    ← Category.assoc ((jShriek B (underlyingRingSheaf X)).map
      ((jStar B (underlyingRingSheaf X)).map i)), ← Functor.map_comp, ← Functor.map_comp,
    reassoc_of% hi, hst, Category.comp_id]

/-- `Stacks.DerivedGlueing.jStar_jShriek_counit_key` read through
`Stacks.DerivedGlueing.openModuleRestriction`, which is extension by zero followed by
restriction by definition.  This is the shape in which the degreewise identity is applied. -/
theorem openModuleRestriction_counit_key (A B : Opens X.carrier) (hAB : A ≤ B)
    {M : SheafOfModules.{u} (restrictedRingSheaf X B)}
    {N D P : SheafOfModules.{u} (underlyingRingSheaf X)}
    (u : N ⟶ (jShriek B (underlyingRingSheaf X)).obj M)
    (v : (jShriek B (underlyingRingSheaf X)).obj M ⟶ N)
    (e : (jStar B (underlyingRingSheaf X)).obj ((jShriek B (underlyingRingSheaf X)).obj M) ⟶ M)
    (i : N ⟶ D) (s : D ⟶ P) (t : P ⟶ D)
    (huv : u ≫ v = 𝟙 N) (hst : s ≫ t = 𝟙 D)
    (he : e ≫ (jShriekAdjunction B (underlyingRingSheaf X)).unit.app M = 𝟙 _) :
    (openModuleRestriction X A B hAB).map ((jStar B (underlyingRingSheaf X)).map u) ≫
        (openModuleRestriction X A B hAB).map e ≫
        (jStar A (underlyingRingSheaf X)).map v ≫
        (jStar A (underlyingRingSheaf X)).map i =
      (openModuleRestriction X A B hAB).map ((jStar B (underlyingRingSheaf X)).map i) ≫
        (openModuleRestriction X A B hAB).map ((jStar B (underlyingRingSheaf X)).map s) ≫
        (jStar A (underlyingRingSheaf X)).map
          ((jShriekAdjunction B (underlyingRingSheaf X)).counit.app P) ≫
        (jStar A (underlyingRingSheaf X)).map t :=
  jStar_jShriek_counit_key X A B u v e i s t huv hst he

end CounitKey

/-! ### The components of the three comparisons of complexes -/

section Components

open ExtensionByZeroModules

variable (X : RingedSpace.{u, u})

/-- The comparison of restriction with extension by zero followed by restriction is degreewise
the identity: the two functors agree, and the comparison is the identification of the two
readings of a composite prolongation. -/
@[simp]
theorem openModuleRestrictionMapIso_hom_app_f (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) (n : ℤ) :
    ((openModuleRestrictionMapIso X V U hVU).hom.app C).f n = 𝟙 _ := by
  rfl

/-- The inverse of `Stacks.DerivedGlueing.openModuleRestrictionMapIso` is degreewise the
identity. -/
@[simp]
theorem openModuleRestrictionMapIso_inv_app_f (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) (n : ℤ) :
    ((openModuleRestrictionMapIso X V U hVU).inv.app C).f n = 𝟙 _ := by
  rfl

/-- Degreewise, the round trip along `⊤` is the counit of extension by zero along `⊤`. -/
@[simp]
theorem topRoundTripIso_hom_app_f
    (C : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) (n : ℤ) :
    ((topRoundTripIso X).hom.app C).f n =
      (jShriekAdjunction (⊤ : Opens X.carrier) (underlyingRingSheaf X)).counit.app (C.X n) := by
  rfl

/-- Degreewise, the identification of a complex on `U` with the restriction of its extension by
zero is the unit of extension by zero along `U`. -/
@[simp]
theorem jShriekJStarIso_hom_app_f (U : Opens X.carrier)
    (M : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) (n : ℤ) :
    ((jShriekJStarIso X U).hom.app M).f n =
      (jShriekAdjunction U (underlyingRingSheaf X)).unit.app (M.X n) := by
  simp [jShriekJStarIso, Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

end Components

/-! ### The compatibility of the glued identifications with the transitions -/

section Compatibility

open ExtensionByZeroModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {E : Type u} [LinearOrder E] [Nonempty E]

/-- **The restriction to `V` of the glued complex is the restriction to `V` of the colimit of the
system.** These are the first two legs of
`Stacks.DerivedGlueing.glueingComplexRestrictionIso`, and unlike the third they are isomorphisms
already on complexes. -/
def glueingComplexRestrictIso (V : Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ) :
    ((openModuleRestriction X V ⊤ le_top).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (glueingComplex F) ≅
      ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (colimit F) :=
  (openModuleRestrictionMapIso X V ⊤ le_top).app (glueingComplex F) ≪≫
    ((jStar V (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((topRoundTripIso X).app (colimit F))

/-- **The restriction to `W α` of the stage `F α` is the prescribed complex there.** These are
the last two legs of `Stacks.DerivedGlueing.glueingComplexRestrictionIso`. -/
def glueingComplexLocalIso (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    (α : E) :
    ((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (F.obj α) ≅ I α :=
  ((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (hsupp α) ≪≫
    (jShriekJStarIso X (W α)).symm.app (I α)

/-- **The restriction to `W β` of the prescribed complex on `W α` is the restriction to `W β` of
the stage `F α`.** These are the first two legs of
`Stacks.DerivedGlueing.glueingComplexTransitionIso`. -/
def glueingComplexTransitionSourceIso (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))
    {β α : E} (hβα : W β ≤ W α) :
    ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I α) ≅
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F.obj α) :=
  (openModuleRestrictionMapIso X (W β) (W α) hβα).app (I α) ≪≫
    ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (hsupp α).symm

variable (W : E → Opens X.carrier)
    (F : E ⥤ CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ)
    (I : ∀ α : E, CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X (W α))) ℤ)
    (hsupp : ∀ α : E, F.obj α ≅
      ((jShriek (W α) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (I α))

/-- **The identification of the restriction of the glued object with the prescribed object, with
the inverse of the colimit inclusion cleared.** This is
`Stacks.DerivedGlueing.glueingComplexRestrictionIso` written through forward maps only, and it is
the form in which the compatibility of the glued identifications can be checked. -/
theorem Q_map_colimit_ι_comp_glueingComplexRestrictionIso
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (α : E) :
    DerivedCategory.Q.map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        DerivedCategory.Q.map (glueingComplexRestrictIso (W α) F).inv ≫
        (glueingComplexRestrictionIso W F I hsupp hqi α).hom =
      DerivedCategory.Q.map (glueingComplexLocalIso W F I hsupp α).hom := by
  simp [glueingComplexRestrictionIso, glueingComplexRestrictIso, glueingComplexLocalIso,
    CategoryTheory.Functor.map_comp]

omit [Nonempty E] in
/-- **The transition the system of complexes determines, with the inverse of its transition map
cleared.** This is `Stacks.DerivedGlueing.glueingComplexTransitionIso` written through forward
maps only. -/
theorem Q_map_comp_glueingComplexTransitionIso
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    DerivedCategory.Q.map
          (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (F.map h.hom)) ≫
        DerivedCategory.Q.map
          (glueingComplexTransitionSourceIso W F I hsupp hβα).inv ≫
        (glueingComplexTransitionIso W F I hsupp hqi hβα h).hom =
      DerivedCategory.Q.map (glueingComplexLocalIso W F I hsupp β).hom := by
  simp [glueingComplexTransitionIso, glueingComplexLocalIso, glueingComplexTransitionSourceIso,
    CategoryTheory.Functor.map_comp]

/-! #### The components of the comparisons, in the form the degreewise identity needs -/

/-- The prolongation of restriction acts degreewise. -/
theorem openModuleRestriction_mapHomologicalComplex_map_f (V U : Opens X.carrier) (hVU : V ≤ U)
    {C D : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ} (f : C ⟶ D) (n : ℤ) :
    (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).map f).f n =
      (openModuleRestriction X V U hVU).map (f.f n) :=
  rfl

omit [Nonempty E] in
/-- The degreewise components of
`Stacks.DerivedGlueing.glueingComplexLocalIso`. -/
theorem glueingComplexLocalIso_hom_f (α : E) (n : ℤ) :
    (glueingComplexLocalIso W F I hsupp α).hom.f n =
      (jStar (W α) (underlyingRingSheaf X)).map ((hsupp α).hom.f n) ≫
        ((jShriekJStarIso X (W α)).inv.app (I α)).f n :=
  rfl

omit [Nonempty E] in
/-- The degreewise components of
`Stacks.DerivedGlueing.glueingComplexTransitionSourceIso`: the comparison of the two readings of
restriction is the identity, so only the support isomorphism survives. -/
theorem glueingComplexTransitionSourceIso_hom_f {β α : E} (hβα : W β ≤ W α) (n : ℤ) :
    (glueingComplexTransitionSourceIso W F I hsupp hβα).hom.f n =
      (jStar (W β) (underlyingRingSheaf X)).map ((hsupp α).inv.f n) :=
  rfl

omit [Nonempty E] in
/-- The degreewise components of `Stacks.DerivedGlueing.glueingComplexRestrictIso`. -/
theorem glueingComplexRestrictIso_hom_f (V : Opens X.carrier) (n : ℤ) :
    (glueingComplexRestrictIso V F).hom.f n =
      (jStar V (underlyingRingSheaf X)).map
        (((topRoundTripIso X).app (colimit F)).hom.f n) :=
  rfl

omit [Nonempty E] in
/-- The degreewise components of the inverse of
`Stacks.DerivedGlueing.glueingComplexRestrictIso`. -/
theorem glueingComplexRestrictIso_inv_f (V : Opens X.carrier) (n : ℤ) :
    (glueingComplexRestrictIso V F).inv.f n =
      (jStar V (underlyingRingSheaf X)).map
        (((topRoundTripIso X).app (colimit F)).inv.f n) :=
  rfl

/-- The degreewise components of the prolongation of the comparison of restriction in one and in
two steps. -/
theorem mapHomologicalComplex_openModuleRestrictionComparison_app_f (V T U : Opens X.carrier)
    (hVT : V ≤ T) (hTU : T ≤ U)
    (C : CochainComplex (SheafOfModules.{u} (restrictedRingSheaf X U)) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X V T U hVT hTU)
          (ComplexShape.up ℤ)).app C).f n =
      (jStar V (underlyingRingSheaf X)).map
        ((jShriekAdjunction T (underlyingRingSheaf X)).counit.app
          ((jShriek U (underlyingRingSheaf X)).obj (C.X n))) :=
  rfl

omit [Nonempty E] in
/-- **The compatibility of the glued complex with the transitions, on complexes.** Identifying
the restriction to `W β` of the prescribed complex on `W α` with the restriction to `W β` of the
stage `F α` and then composing with the colimit inclusion at `α` is the same as restricting the
colimit inclusion at `α` to `W β` through the glued complex.

Degreewise this is `Stacks.DerivedGlueing.jStar_jShriek_counit_key`: both sides are the
restriction to `W β` of the counit of extension by zero along `W α`, followed by the colimit
inclusion. -/
theorem glueingComplexCompatibility {β α : E} (hβα : W β ≤ W α) :
    ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (glueingComplexLocalIso W F I hsupp α).hom ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).hom ≫
        ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α) =
      ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexRestrictIso (W α) F).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) ⊤ hβα le_top)
            (ComplexShape.up ℤ)).app (glueingComplex F) ≫
        (glueingComplexRestrictIso (W β) F).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have hf : ∀ {C D : CochainComplex (SheafOfModules.{u} (underlyingRingSheaf X)) ℤ}
      (e : C ≅ D), e.hom.f n ≫ e.inv.f n = 𝟙 _ := fun e =>
    HomologicalComplex.congr_hom e.hom_inv_id n
  have huv := hf (hsupp α)
  have hst := hf ((topRoundTripIso X).app (colimit F)).symm
  have he : ((jShriekJStarIso X (W α)).inv.app (I α)).f n ≫
      (jShriekAdjunction (W α) (underlyingRingSheaf X)).unit.app ((I α).X n) = 𝟙 _ := by
    rw [← jShriekJStarIso_hom_app_f]
    exact HomologicalComplex.congr_hom ((jShriekJStarIso X (W α)).inv_hom_id_app (I α)) n
  have key := openModuleRestriction_counit_key X (W β) (W α) hβα
    ((hsupp α).hom.f n) ((hsupp α).inv.f n) (((jShriekJStarIso X (W α)).inv.app (I α)).f n)
    ((colimit.ι F α).f n) (((topRoundTripIso X).app (colimit F)).inv.f n)
    (((topRoundTripIso X).app (colimit F)).hom.f n) huv hst he
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    glueingComplexLocalIso_hom_f,
    glueingComplexTransitionSourceIso_hom_f, glueingComplexRestrictIso_hom_f,
    glueingComplexRestrictIso_inv_f, mapHomologicalComplex_openModuleRestrictionComparison_app_f,
    CategoryTheory.Functor.map_comp, Category.assoc]
  exact key

omit [Nonempty E] in
/-- **The compatibility of the glued complex with the transitions, rearranged through forward
maps.** The form of `Stacks.DerivedGlueing.glueingComplexCompatibility` the derived-category
assembly consumes: the two identifications cancel and the cocone law
`F.map h ≫ colimit.ι F α = colimit.ι F β` is what is left. -/
theorem glueingComplexCompatibility' {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (F.map h.hom) ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexRestrictIso (W α) F).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) ⊤ hβα le_top)
            (ComplexShape.up ℤ)).app (glueingComplex F) ≫
        (glueingComplexRestrictIso (W β) F).hom =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (colimit.ι F β) := by
  have hw : ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom) ≫
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F α) =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (colimit.ι F β) := by
    rw [← CategoryTheory.Functor.map_comp, colimit.w]
  rw [← glueingComplexCompatibility W F I hsupp hβα,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_assoc]
  exact hw

omit [Nonempty E] in
/-- `Stacks.DerivedGlueing.glueingComplexCompatibility'` with the comparison of the restriction
of the glued complex moved to the right-hand side. -/
theorem glueingComplexCompatibility'' {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (F.map h.hom) ≫
        (glueingComplexTransitionSourceIso W F I hsupp hβα).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (colimit.ι F α)) ≫
        ((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (glueingComplexRestrictIso (W α) F).inv ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) ⊤ hβα le_top)
            (ComplexShape.up ℤ)).app (glueingComplex F) =
      ((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (colimit.ι F β) ≫
        (glueingComplexRestrictIso (W β) F).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  exact glueingComplexCompatibility' W F I hsupp hβα h

/-- **The transported identification of the glued object composed with the transition is the
comparison followed by the identification one stage down.** This is the compatibility of `σ` with
`ρ` after the comparison `restrictionComp` has been replaced, by
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'`, by the prolongation of the counit
of extension by zero on the middle open; the remaining content is
`Stacks.DerivedGlueing.glueingComplexCompatibility''`. -/
theorem transportHom_glueingComplexRestrictionIso_comp (S : LocallyGiven X)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    transportHom DerivedCategory.Q DerivedCategory.Q (S.restrictionFactors (W β) (W α) hβα)
          (glueingComplexRestrictionIso W F I hsupp hqi α).hom ≫
        (glueingComplexTransitionIso W F I hsupp hqi hβα h).hom =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X (W β) (W α) ⊤ hβα le_top)
            (ComplexShape.up ℤ)).app (glueingComplex F)) ≫
        (glueingComplexRestrictionIso W F I hsupp hqi β).hom := by
  have hQν := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_jStar_map_colimit_ι W F hqi α)
  have hQμ := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hqi β α h)
  have hQrν : IsIso (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α)))) := by
    rw [← transportHom_map DerivedCategory.Q DerivedCategory.Q
      (S.restrictionFactors (W β) (W α) hβα)]
    infer_instance
  have hCA' := congrArg (transportHom DerivedCategory.Q DerivedCategory.Q
    (S.restrictionFactors (W β) (W α) hβα))
    (Q_map_colimit_ι_comp_glueingComplexRestrictionIso W F I hsupp hqi α)
  simp only [transportHom_comp, transportHom_map] at hCA'
  refine (cancel_epi (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((jStar (W α) (underlyingRingSheaf X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (colimit.ι F α))) ≫
    DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (glueingComplexRestrictIso (W α) F).inv))).mp ?_
  simp only [Category.assoc]
  rw [reassoc_of% hCA']
  refine (cancel_epi (DerivedCategory.Q.map
      (((openModuleRestriction X (W β) (W α) hβα).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (glueingComplexLocalIso W F I hsupp α).inv))).mp ?_
  rw [map_map_inv_comp_map_map_hom_assoc]
  refine (cancel_epi (DerivedCategory.Q.map
      (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)) ≫
    DerivedCategory.Q.map
      (glueingComplexTransitionSourceIso W F I hsupp hβα).inv)).mp ?_
  simp only [Category.assoc]
  refine (Q_map_comp_glueingComplexTransitionIso W F I hsupp hqi hβα h).trans (Eq.symm ?_)
  have hcc := glueingComplexCompatibility'' W F I hsupp hβα h
  simp only [← CategoryTheory.Functor.map_comp_assoc] at hcc ⊢
  rw [hcc]
  simp only [CategoryTheory.Functor.map_comp_assoc]
  exact Q_map_colimit_ι_comp_glueingComplexRestrictionIso W F I hsupp hqi β

/-- **The identifications of the restrictions of the glued object are compatible with the
transitions the system of complexes determines.** This is the last step of this half of
[Stacks, Tag 0D6B], and with it the assembly is complete: the glued object
`Stacks.DerivedGlueing.glueingObject F`, the identifications
`Stacks.DerivedGlueing.glueingRestrictionIso` and the transitions
`Stacks.DerivedGlueing.glueingTransitionIso` form a solution of the glueing problem.

Its mathematical content is the cocone law `F.map h ≫ colimit.ι F α = colimit.ι F β`, read
against the counit of extension by zero on `W α`
(`Stacks.DerivedGlueing.jStar_jShriek_counit_key`).  The bookkeeping is the passage from the
comparison `Stacks.DerivedGlueing.LocallyGiven.restrictionComp`, which the system pins down only
on the image of `DerivedCategory.Q`, to that counit, by
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'`; since both families of
isomorphisms contain the inverse of a `Q.map`, the equation is first cleared of those inverses
(`Stacks.DerivedGlueing.Q_map_colimit_ι_comp_glueingComplexRestrictionIso` and
`Stacks.DerivedGlueing.Q_map_comp_glueingComplexTransitionIso`) and the restriction functor's
action is carried across the comparison by
`Stacks.DerivedGlueing.transportHom`. -/
theorem glueing_compatibility (S : LocallyGiven X)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (S.restrictionComp (W β) (W α) ⊤ hβα le_top).hom.app (glueingObject F) ≫
        (S.restriction (W β) (W α) hβα).map
          (glueingRestrictionIso S W F I hsupp hqi α).hom ≫
        (glueingTransitionIso S W F I hsupp hqi hβα h).hom =
      (glueingRestrictionIso S W F I hsupp hqi β).hom := by
  simp only [glueingObject, glueingRestrictionIso, glueingTransitionIso, Iso.trans_hom,
    CategoryTheory.Iso.app_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_comp_hom_app DerivedCategory.Q DerivedCategory.Q
      (S.restrictionFactors (W β) (W α) hβα)
      (glueingComplexRestrictionIso W F I hsupp hqi α).hom),
    transportHom_glueingComplexRestrictionIso_comp W F I hsupp S hqi hβα h,
    reassoc_of% (S.restrictionCompFactors' (W β) (W α) ⊤ hβα le_top (glueingComplex F))]

/-- `Stacks.DerivedGlueing.glueing_compatibility` transported along a choice of prescribed
objects `K α` for the classes of the complexes `I α`. -/
theorem glueing_compatibility_of_iso (S : LocallyGiven X)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)
    {β α : E} (hβα : W β ≤ W α) (h : β ≤ α) :
    (S.restrictionComp (W β) (W α) ⊤ hβα le_top).hom.app (glueingObject F) ≫
        (S.restriction (W β) (W α) hβα).map
          (glueingRestrictionIso S W F I hsupp hqi α ≪≫ hK α).hom ≫
        ((S.restriction (W β) (W α) hβα).mapIso (hK α).symm ≪≫
          glueingTransitionIso S W F I hsupp hqi hβα h ≪≫ hK β).hom =
      (glueingRestrictionIso S W F I hsupp hqi β ≪≫ hK β).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [map_map_hom_inv_comp_assoc, reassoc_of% (glueing_compatibility W F I hsupp S hqi hβα h)]

include hsupp in
/-- **The glueing problem of [Stacks, Tag 0D6B] is solved by a system of complexes.** Let `W` be
an increasing family of opens, let `F : E ⥤ CochainComplex (Mod 𝒪_X) ℤ` be a system of complexes
over a nonempty linear order with `F α` supported on `W α` — that is, the extension by zero of a
complex `I α` on `W α` — and such that restricting a transition `F β ⟶ F α` to `W β` is a
quasi-isomorphism whenever `β ≤ α`.  Let `K α` be the class of `I α` in the derived category on
`W α`.  Then there is an object `G` of the derived category on `⊤` together with
identifications of its restrictions with the `K α` and transitions between the `K α`, compatible
with each other.

This is the assembly half of [Stacks, Tag 0D6B]: `G` is the class of the termwise colimit
`colim_α (j_α)_! I^•_α`, which is `Stacks.DerivedGlueing.glueingObject`.  The system of
complexes is produced from prescribed objects and transitions by
`Stacks.DerivedGlueing.producesComplexSystem`.

It is untagged: the datum here is a system of *complexes*, not the system of objects of the
derived category and prescribed transitions that [Stacks, Tag 0D6B] starts from. -/
theorem exists_glueing_of_complexSystem (S : LocallyGiven X)
    (hqi : ∀ (β α : E) (h : β ≤ α),
      QuasiIso (((jStar (W β) (underlyingRingSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (F.map h.hom)))
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hK : ∀ α : E, DerivedCategory.Q.obj (I α) ≅ K α)
    (hmono : ∀ β α : E, β ≤ α → W β ≤ W α) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α)
      (rho : ∀ (β α : E) (h : β ≤ α),
        (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β),
      ∀ (β α : E) (h : β ≤ α),
        (S.restrictionComp (W β) (W α) ⊤ (hmono β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α) (hmono β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom :=
  ⟨glueingObject F, fun α => glueingRestrictionIso S W F I hsupp hqi α ≪≫ hK α,
    fun β α h => (S.restriction (W β) (W α) (hmono β α h)).mapIso (hK α).symm ≪≫
      glueingTransitionIso S W F I hsupp hqi (hmono β α h) h ≪≫ hK β,
    fun β α h => glueing_compatibility_of_iso W F I hsupp S hqi K hK (hmono β α h) h⟩

end Compatibility

end Stacks.DerivedGlueing

end
