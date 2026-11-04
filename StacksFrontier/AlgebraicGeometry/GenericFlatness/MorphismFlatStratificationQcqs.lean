module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratification
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationQcqs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport

/-!
# The generic flatness stratification of a morphism over a quasi-compact quasi-separated base

Let `f : X ⟶ S` be a morphism of finite presentation between quasi-compact and quasi-separated
schemes. Then there are closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by a finite
type ideal sheaf, with `S₀ ⊆ S` a thickening, such that `X ×_S (S_i ∖ S_{i+1})` is flat over the
locally closed stratum `S_i ∖ S_{i+1}`. This is [Stacks, Tag 0H3Z].

## Main results

* `AlgebraicGeometry.flat_pullback_snd_of_isFlatOver_pullback_unitModule`: flatness of a base
  change as a morphism, from flatness of the pulled back structure sheaf as a module.
* `AlgebraicGeometry.HasFlatStratification.of_finitePresentation`: **[Stacks, Tag 0H3Z]**.
* `AlgebraicGeometry.finitePresentationHasFlatStratification`: the same statement in the
  `Prop`-valued form `AlgebraicGeometry.FinitePresentationHasFlatStratification`.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness of a base change as a morphism, from flatness of the pulled back structure sheaf as
a module over the base change. -/
public theorem flat_pullback_snd_of_isFlatOver_pullback_unitModule
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (h : IsFlatOver (pullback.snd f g).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f g)).obj X.unitModule)) :
    Flat (pullback.snd f g) :=
  (Flat.iff_flat_stalkMap _).mpr fun x ↦
    (MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit (pullback.snd f g) x).mpr
      ((isFlatOver_iff_of_moduleIso (pullback.snd f g).toLRSHom.toShHom
        (Scheme.Modules.pullbackUnitIso (pullback.fst f g))).mp h x)

/-- A morphism of finite presentation between quasi-compact quasi-separated
schemes has a flat stratification of its base: a finite descending chain of closed subschemes,
each cut out by an ideal sheaf of finite type, beginning with a thickening of the base and ending
with the empty scheme, over each of whose locally closed strata the base change of the morphism
is flat. -/
@[stacks 0H3Z,
  ega "IV 6.9.3" "Case F = O_X",
  ega "IV 8.9.5" "Case F = O_X",
  sga "6 XIII 1.13" "special case"]
public theorem HasFlatStratification.of_finitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : FinitePresentation f) : HasFlatStratification f := by
  obtain ⟨t, I, hthick, hft, hmono, hlast, hflat⟩ :=
    exists_flat_stratification f hf X.unitModule
  exact ⟨t, I, hthick, hft, hmono, hlast,
    fun i ↦ flat_pullback_snd_of_isFlatOver_pullback_unitModule f _ (hflat i)⟩

/-- `AlgebraicGeometry.FinitePresentationHasFlatStratification` holds: every morphism of finite
presentation between quasi-compact quasi-separated schemes has a flat stratification of its
base. -/
public theorem finitePresentationHasFlatStratification :
    FinitePresentationHasFlatStratification.{u} :=
  fun f _ _ _ _ hf ↦ .of_finitePresentation f hf

end AlgebraicGeometry

end
