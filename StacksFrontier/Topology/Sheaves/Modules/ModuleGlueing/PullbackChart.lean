module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent

/-!
# Pulling a glued sheaf of modules back along a morphism into a chart

A sheaf of modules glued from a family of sheaves on the members of a cover by open immersions
restricts on each chart to the sheaf it was glued from. This file reads that comparison as a
statement about *pullbacks*: if a morphism `h : T ⟶ S` of schemes factors as `h = g ≫ f i`
through the `i`-th chart, then `h^*` of the glued sheaf is `g^*` of the `i`-th member. More
generally, for an open immersion `f : Y ⟶ S`, a comparison `N|_Y ≅ M` and `h = g ≫ f`, the
pullback `h^*N` is `g^*M`.

A morphism into a scheme covered by open immersions factors through one of them on a
neighbourhood of each point of its source.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso`: **the pullback of a sheaf of
  modules along a morphism factoring through an open immersion**, in terms of a comparison of its
  restriction along that immersion.
* `Stacks.SheafOfModules.ModulesGlueData.pullbackChartIso` and
  `Stacks.SheafOfModules.ModulesDirectedGlueData.pullbackChartIso`: **`h^*` of the glued sheaf is
  `g^*` of the `i`-th member**, for a factorization `h = g ≫ f i` through the `i`-th chart.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_factorization_of_iSup_opensRange_eq_top`: **a morphism
  into the base factors through a chart on a neighbourhood of each point**, given that the charts
  cover the base.

## Implementation notes

No `@[stacks]` attribute is placed: the comparison is the chart-local description of a pullback of
a glued sheaf, and is not a statement of the source.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S T Y : Scheme.{u}}

/-- **The pullback of a sheaf of modules along a morphism factoring through an open immersion.**
If `h : T ⟶ S` factors as `g ≫ f` with `f : Y ⟶ S` an open immersion, and if the restriction of
`N` along `f` is identified with `M` by `e`, then `h^*N` is `g^*M`. -/
def pullbackIsoOfRestrictIso (f : Y ⟶ S) [IsOpenImmersion f] {N : S.Modules} {M : Y.Modules}
    (e : N.restrict f ≅ M) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f) :
    (pullback h).obj N ≅ (pullback g).obj M :=
  (pullbackCongr hfac).app N ≪≫ ((pullbackComp g f).app N).symm ≪≫
    (pullback g).mapIso (((restrictFunctorIsoPullback f).app N).symm ≪≫ e)

/-- **A morphism into the base of a cover by open immersions factors through a chart on a
neighbourhood of each point of its source.** -/
theorem exists_factorization_of_iSup_opensRange_eq_top {ι : Type u} {W : ι → Scheme.{u}}
    (f : ∀ i, W i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcover : ⨆ i, (f i).opensRange = ⊤) (h : T ⟶ S) (t : T) :
    ∃ (i : ι) (V : T.Opens) (g : (V : Scheme.{u}) ⟶ W i), t ∈ V ∧ V.ι ≫ h = g ≫ f i := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (show h.base t ∈ (⊤ : S.Opens) from trivial))
  exact ⟨i, h ⁻¹ᵁ (f i).opensRange, IsOpenImmersion.lift (f i)
    ((h ⁻¹ᵁ (f i).opensRange).ι ≫ h) (by rintro _ ⟨v, rfl⟩; exact v.2), hi,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.SheafOfModules

open AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)] {T : Scheme.{u}}

/-- **The pullback of a glued sheaf of modules along a morphism factoring through a chart.** If
`h : T ⟶ S` factors as `g ≫ f i` through the `i`-th chart, then `h^*` of the glued sheaf is `g^*`
of the sheaf the datum carries on that chart. -/
def ModulesGlueData.pullbackChartIso (D : ModulesGlueData S f) (i : ι) (g : T ⟶ Y i)
    {h : T ⟶ S} (hfac : h = g ≫ f i) :
    (Scheme.Modules.pullback h).obj D.glued ≅ (Scheme.Modules.pullback g).obj (D.mod i) :=
  Scheme.Modules.pullbackIsoOfRestrictIso (f i) (D.chartIso i) g hfac

/-- **The pullback of a sheaf of modules glued from a locally directed datum along a morphism
factoring through a chart.** -/
def ModulesDirectedGlueData.pullbackChartIso [Preorder ι] (D : ModulesDirectedGlueData S f)
    (i : ι) (g : T ⟶ Y i) {h : T ⟶ S} (hfac : h = g ≫ f i) :
    (Scheme.Modules.pullback h).obj D.glued ≅ (Scheme.Modules.pullback g).obj (D.mod i) :=
  Scheme.Modules.pullbackIsoOfRestrictIso (f i) (D.chartIso i) g hfac

end Stacks.SheafOfModules

end
