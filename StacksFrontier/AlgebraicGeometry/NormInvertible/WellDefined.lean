module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Coboundary
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Reindex
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The norm of an invertible module is well defined on isomorphism classes

Let `f : X ⟶ Y` carry a norm `N` of degree `d` on functions, and let `L ≅ M` be isomorphic
`𝒪_X`-modules. Then `Stacks.Divisors.normInvertible f N L ≅ normInvertible f N M`: the norm
construction does not depend on which representative of an isomorphism class it is applied to,
nor on the trivializations that `Stacks.Divisors.normTransitionCocycle` picks with
`Classical.choice`.

This is **the first of the three verifications that
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) omits.** The source ends its proof
with "We omit the verification that: this is well defined, additive on Picard groups, and
satisfies the property `Norm_π(π^*𝒩) ≅ 𝒩^{⊗d}`"; well-definedness is what this file supplies, and
`Stacks.Divisors.picardClass_normInvertible_congr` states it in the form the Picard-group
homomorphism of that tag needs.

## The two halves, and why both are needed

`normTransitionCocycle f N L` is indexed by `Stacks.Divisors.NormChart f L`, so the index *type*
depends on `L`, and the chart trivializations are chosen independently for `L` and for `M`.
Comparing the two glued modules therefore needs both of the general facts about
`Stacks.SheafOfModules.UnitTransitionCocycle`:

* reindexing invariance (`UnitTransitionCocycle.glueReindexIso`) moves `M`'s cocycle onto `L`'s
  index type. The equivalence is `Stacks.Divisors.normChartEquiv`, which is the identity on the
  underlying open — a chart for `L` is a chart for `M`, the trivialization being transported
  along `e` by `AlgebraicGeometry.Scheme.Modules.restrictFunctor` — so the two families of opens
  are definitionally equal and no transport of sections is incurred;
* the coboundary twist (`UnitTransitionCocycle.glueIsoOfCoboundaryTwist`) then absorbs the
  difference between `M`'s own chart generator and the transported one. The twisting units are
  `Stacks.Divisors.chartComparisonUnit`, the normed ratio of those two generators over the chart.

## Main definitions

* `Stacks.Divisors.normChartEquiv`: a chart for `L` is a chart for any isomorphic module.
* `Stacks.Divisors.transportedChartGenerator`: `L`'s chart generator, carried to `M` along the
  isomorphism.
* `Stacks.Divisors.chartComparisonUnit`: the normed ratio of `M`'s chart generator to the
  transported one, which is the coboundary that relates the two cocycles.
* `Stacks.Divisors.normInvertibleIsoOfIso`: **the norm of `L` is isomorphic to the norm of any
  module isomorphic to `L`.**

## Main results

* `Stacks.Divisors.normGeneratorRatio_symm`: reversing a normed ratio inverts it.
* `Stacks.Divisors.chartComparisonUnit_restrict`: the comparison unit commutes with restriction.
* `Stacks.Divisors.isCoboundaryTwist_normTransitionCocycle`: the two transition cocycles differ
  by the coboundary of the comparison units.
* `Stacks.Divisors.picardClass_normInvertible_congr`: **the norm construction is well defined on
  Picard classes.**
* `Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible`: Tag 0BUT with
  invertibility as a named hypothesis, which is how an element of the Picard group carries it.
* `Stacks.Divisors.exists_normPicardMap`: **the norm descends to a map of Picard groups**,
  characterized by its value on the class of an invertible module. This is the data of the
  `picardMap` field of `Stacks.Divisors.NormPicardData` together with its `picardMap_picardClass`
  law; additivity is not proved here, so the map is produced as a function rather than as an
  `AddMonoidHom` (`Stacks.Divisors.exists_normPicardAddMonoidHom` upgrades it).

## Implementation notes

No `@[stacks]` attribute is placed. Tag 0BCY asserts the whole norm construction including the
Picard-group homomorphism, and only its well-definedness clause is settled here; the additivity
clause and the pullback--power formula are not.

`normInvertibleIsoOfIso` carries **no** hypothesis — in particular not
`Stacks.Divisors.HasTrivializingTargetCover`. The cocycle comparison is chartwise, and the cover
is needed only to know that the glued module is invertible, which this statement does not
mention. `picardClass_normInvertible_congr` needs the cover on both sides, because a Picard class
is only defined for an invertible module.

**Why the final step is an abstract group lemma.** After the three ratio compositions the goal is
`a⁻¹ * (t * b) = b * a⁻¹ * t` in the units of `Γ(Y, V)`. Normalizing it in place with
`simp only [mul_assoc, mul_comm, mul_left_comm]` dies with `(deterministic) timeout at
Lean.Meta.acLt` — the terms are large and the associativity-commutativity ordering is what the
budget is spent on, not the mathematics. Stated for an abstract `CommGroup`
(`UnitTransitionCocycle.unitsCoboundaryRearrange`) the same `simp only` is free, and is applied.
`UnitTransitionCocycle.unitsCoboundaryCancel` plays the same role for `IsCoboundaryTwist.symm`;
the two lemmas are kept in one namespace.

**Rewriting against `normChartGeneratorOver`.** Two of the restriction steps cannot be closed by
`rw`: the pattern `generatorRestrict ?L _ (normChartGeneratorOver ?f ?L ?i ?V ?hi)` is not found,
Lean reporting that the target "is not type-correct under the `implicit` transparency level".
They are closed by `congrArg₂` with every argument supplied, which is the idiom
`normTransitionCocycle`'s own `restrict` field already uses. No transparency option is set.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.SheafOfModules.UnitTransitionCocycle

/-- The rearrangement that turns a three-term ratio composition into the shape of
`UnitTransitionCocycle.IsCoboundaryTwist`. Stated for an abstract commutative group, because on
the units of a ring of sections the same normalization exhausts the default heartbeat budget
inside `Lean.Meta.acLt`. Companion to `UnitTransitionCocycle.unitsCoboundaryCancel`. -/
theorem unitsCoboundaryRearrange {G : Type*} [CommGroup G] (a b t : G) :
    a⁻¹ * (t * b) = b * a⁻¹ * t := by
  simp only [mul_assoc, mul_comm, mul_left_comm]

end Stacks.SheafOfModules.UnitTransitionCocycle

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

variable {X Y : Scheme.{u}}

/-! ### Charts and generators carried along an isomorphism -/

/-- **A chart for `L` is a chart for any isomorphic module.** The underlying open is unchanged;
only the trivialization is transported, along the restriction functor. -/
def normChartEquiv (f : X ⟶ Y) {L M : X.Modules} (e : L ≅ M) : NormChart f L ≃ NormChart f M :=
  Equiv.subtypeEquivRight fun U =>
    ⟨fun ⟨φ⟩ => ⟨((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e).symm ≪≫ φ⟩,
     fun ⟨φ⟩ => ⟨(Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e ≪≫ φ⟩⟩

/-- The chart `normChartEquiv f e i` has the same underlying open as `i`. -/
@[simp]
theorem normChartEquiv_val (f : X ⟶ Y) {L M : X.Modules} (e : L ≅ M) (i : NormChart f L) :
    (normChartEquiv f e i).val = i.val :=
  rfl

/-- `L`'s chart generator over a target open, carried to `M` along the isomorphism. -/
noncomputable abbrev transportedChartGenerator (f : X ⟶ Y) {L M : X.Modules} (e : L ≅ M)
    (i : NormChart f L) (V : Y.Opens) (h : V ≤ i.val) :
    GeneratorSections X.toRingedSpace M (f ⁻¹ᵁ V) :=
  generatorMapIso (X := X.toRingedSpace) e (f ⁻¹ᵁ V) (normChartGeneratorOver f L i V h)

/-- The transported chart generator commutes with restriction to a smaller target open. -/
theorem transportedChartGenerator_restrict (f : X ⟶ Y) {L M : X.Modules} (e : L ≅ M)
    (i : NormChart f L) {V W : Y.Opens} (hi : V ≤ i.val) (h : W ≤ V) :
    generatorRestrict (X := X.toRingedSpace) M ((Opens.map f.base).map (homOfLE h)).le
        (transportedChartGenerator f e i V hi) =
      transportedChartGenerator f e i W (h.trans hi) := by
  rw [transportedChartGenerator, ← generatorMapIso_restrict (X := X.toRingedSpace) e
    ((Opens.map f.base).map (homOfLE h)).le, normChartGeneratorOver_restrict]
  exact h

/-! ### The comparison units -/

/-- Reversing a normed ratio inverts it. -/
theorem normGeneratorRatio_symm (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d) (L : X.Modules)
    (V : Y.Opens) (s t : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)) :
    normGeneratorRatio f N.toMorphismNormMap L V t s =
      (normGeneratorRatio f N.toMorphismNormMap L V s t)⁻¹ :=
  (congrArg (normUnitsMap f N.toMorphismNormMap V)
    (generatorRatioUnit_symm (X := X.toRingedSpace) L (f ⁻¹ᵁ V) s t)).trans (map_inv _ _)

/-- The normed ratio of `M`'s own chart generator to the one transported from `L`. This is the
coboundary relating the two transition cocycles. -/
noncomputable def chartComparisonUnit (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (e : L ≅ M) (i : NormChart f L) : (Γ(Y, i.val))ˣ :=
  normGeneratorRatio f N.toMorphismNormMap M i.val
    (normChartGeneratorOver f M (normChartEquiv f e i) i.val le_rfl)
    (transportedChartGenerator f e i i.val le_rfl)

/-- The restriction of the comparison unit to a smaller target open is the normed ratio of the two
chart generators over that open. -/
theorem chartComparisonUnit_restrict (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (e : L ≅ M) (i : NormChart f L) {V : Y.Opens} (hi : V ≤ i.val) :
    UnitTransitionCocycle.resUnits (X := Y.toRingedSpace) hi (chartComparisonUnit f N e i) =
      normGeneratorRatio f N.toMorphismNormMap M V
        (normChartGeneratorOver f M (normChartEquiv f e i) V hi)
        (transportedChartGenerator f e i V hi) := by
  have hres : UnitTransitionCocycle.resUnits (X := Y.toRingedSpace) hi
        (chartComparisonUnit f N e i) =
      Units.map (Y.presheaf.map (homOfLE hi).op).hom (chartComparisonUnit f N e i) := rfl
  rw [hres, chartComparisonUnit, ← normGeneratorRatio_restrict f N.toMorphismNormMap M hi]
  exact congrArg₂ (normGeneratorRatio f N.toMorphismNormMap M V)
    (normChartGeneratorOver_restrict f M (normChartEquiv f e i) le_rfl hi)
    (transportedChartGenerator_restrict f e i le_rfl hi)

/-! ### Well-definedness -/

/-- **The transition cocycles of two isomorphic modules differ by a coboundary**, once `M`'s is
reindexed onto `L`'s charts. -/
theorem isCoboundaryTwist_normTransitionCocycle (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (e : L ≅ M) :
    UnitTransitionCocycle.IsCoboundaryTwist (normTransitionCocycle f N.toMorphismNormMap L)
      ((normTransitionCocycle f N.toMorphismNormMap M).reindex (normChartEquiv f e))
      (chartComparisonUnit f N e) := by
  intro i j V hi hj
  have key : normGeneratorRatio f N.toMorphismNormMap M V
        (normChartGeneratorOver f M (normChartEquiv f e j) V hj)
        (normChartGeneratorOver f M (normChartEquiv f e i) V hi) =
      UnitTransitionCocycle.resUnits (X := Y.toRingedSpace) hj (chartComparisonUnit f N e j) *
        (UnitTransitionCocycle.resUnits (X := Y.toRingedSpace) hi
          (chartComparisonUnit f N e i))⁻¹ *
        normGeneratorRatio f N.toMorphismNormMap L V (normChartGeneratorOver f L j V hj)
          (normChartGeneratorOver f L i V hi) := by
    rw [chartComparisonUnit_restrict f N e i hi, chartComparisonUnit_restrict f N e j hj,
      ← normUnitsMap_generatorRatio_comp f N.toMorphismNormMap V M
        (normChartGeneratorOver f M (normChartEquiv f e j) V hj)
        (transportedChartGenerator f e i V hi)
        (normChartGeneratorOver f M (normChartEquiv f e i) V hi),
      ← normUnitsMap_generatorRatio_comp f N.toMorphismNormMap V M
        (normChartGeneratorOver f M (normChartEquiv f e j) V hj)
        (transportedChartGenerator f e j V hj)
        (transportedChartGenerator f e i V hi),
      normGeneratorRatio_mapIso f N.toMorphismNormMap e V (normChartGeneratorOver f L j V hj)
        (normChartGeneratorOver f L i V hi),
      normGeneratorRatio_symm f N M V
        (normChartGeneratorOver f M (normChartEquiv f e i) V hi)
        (transportedChartGenerator f e i V hi)]
    exact UnitTransitionCocycle.unitsCoboundaryRearrange _ _ _
  exact key

/-- **The norm of an invertible module depends only on its isomorphism class.** This is the
well-definedness clause that Stacks Tag 0BCY omits. -/
noncomputable def normInvertibleIsoOfIso (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (e : L ≅ M) :
    normInvertible f N.toMorphismNormMap L ≅ normInvertible f N.toMorphismNormMap M :=
  UnitTransitionCocycle.glueIsoOfCoboundaryTwist
      (isCoboundaryTwist_normTransitionCocycle f N e) ≪≫
    (UnitTransitionCocycle.glueReindexIso (normTransitionCocycle f N.toMorphismNormMap M)
      (normChartEquiv f e)).symm

/-- **The norm construction is well defined on Picard classes.** -/
theorem picardClass_normInvertible_congr (f : X ⟶ Y) {d : ℕ} (N : MorphismNorm f d)
    {L M : X.Modules} (e : L ≅ M)
    (hL : HasTrivializingTargetCover f L) (hM : HasTrivializingTargetCover f M) :
    picardClass Y.presheaf (structureSheaf Y.sheaf).property
        (normInvertible f N.toMorphismNormMap L)
        (isInvertible_normInvertible f N.toMorphismNormMap L hL) =
      picardClass Y.presheaf (structureSheaf Y.sheaf).property
        (normInvertible f N.toMorphismNormMap M)
        (isInvertible_normInvertible f N.toMorphismNormMap M hM) :=
  (picardClass_eq_iff Y.presheaf (structureSheaf Y.sheaf).property _ _ _ _).mpr
    ⟨normInvertibleIsoOfIso f N e⟩

/-! ### The induced map on Picard groups -/

/-- **Tag 0BUT with invertibility as a named hypothesis**, in the spelling
`Stacks.SheafOfModules.PicardGroup` uses. `hasTrivializingTargetCover_of_isFinite` takes
invertibility as an *instance* argument and spells the sheaf of rings
`structureSheafRing X.toRingedSpace`; an element of the Picard group carries invertibility as the
structure field `ObjectProperty.FullSubcategory.property`, which instance search cannot see. The
two spellings of the sheaf of rings are equal by `rfl`, so this is a restatement and not a second
proof. -/
theorem hasTrivializingTargetCover_of_isFinite_of_isInvertible (f : X ⟶ Y) [IsFinite f]
    (L : X.Modules) (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L) :
    HasTrivializingTargetCover f L :=
  have : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L := hL
  hasTrivializingTargetCover_of_isFinite f L

/-- **The norm descends to a map of Picard groups, characterized on classes.** This is the data
of the `picardMap` field of `Stacks.Divisors.NormPicardData` together with its
`picardMap_picardClass` law; what is *not* here is additivity, so the map is produced as a
function and not as an `AddMonoidHom` (`Stacks.Divisors.exists_normPicardAddMonoidHom` upgrades
it).

The map is well defined precisely by `picardClass_normInvertible_congr`: a class is the class of
some invertible module (`Stacks.SheafOfModules.exists_picardClass_eq`), any two representatives
are isomorphic (`Stacks.SheafOfModules.picardClass_eq_iff`), and the norms of isomorphic modules
have the same class. -/
@[ega "IV 21.5.3" "partial"]
theorem exists_normPicardMap (f : X ⟶ Y) [IsFinite f] {d : ℕ} (N : MorphismNorm f d) :
    ∃ F : PicardGroup X.presheaf (structureSheaf X.sheaf).property →
        PicardGroup Y.presheaf (structureSheaf Y.sheaf).property,
      ∀ (L : X.Modules) (hL : IsInvertible X.presheaf (structureSheaf X.sheaf).property L),
        F (picardClass X.presheaf (structureSheaf X.sheaf).property L hL) =
          picardClass Y.presheaf (structureSheaf Y.sheaf).property
            (normInvertible f N.toMorphismNormMap L)
            (isInvertible_normInvertible f N.toMorphismNormMap L
              (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)) := by
  choose M hM hx using exists_picardClass_eq X.presheaf (structureSheaf X.sheaf).property
  refine ⟨fun x =>
    picardClass Y.presheaf (structureSheaf Y.sheaf).property
      (normInvertible f N.toMorphismNormMap (M x))
      (isInvertible_normInvertible f N.toMorphismNormMap _
        (hasTrivializingTargetCover_of_isFinite_of_isInvertible f _ (hM x))), ?_⟩
  intro L hL
  obtain ⟨e⟩ := (picardClass_eq_iff X.presheaf (structureSheaf X.sheaf).property _ _ _ _).mp
    (hx (picardClass X.presheaf (structureSheaf X.sheaf).property L hL))
  exact picardClass_normInvertible_congr f N e
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f _ (hM _))
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)

end Stacks.Divisors

end
