module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula

/-!
# Pure relative dimension on a preconnected source

A flat morphism locally of finite presentation with Cohen–Macaulay fibres decomposes its source
into clopen pieces of pure relative dimension (Stacks 02NM,
`AlgebraicGeometry.exists_clopen_relativeDimension`). When the source is preconnected there is
only one piece, so the morphism itself has pure relative dimension in the sense of Stacks 02NJ.
The fibres of a smooth morphism are Cohen–Macaulay, so this applies in particular to a smooth
morphism with preconnected source.

## Main results

* `AlgebraicGeometry.exists_relativeDimension_of_preconnectedSpace` — a flat morphism locally of
  finite presentation with Cohen–Macaulay fibres and preconnected source has pure relative
  dimension.
* `AlgebraicGeometry.exists_relativeDimension_of_smooth_of_preconnectedSpace` — the same for a
  smooth morphism.

## References

* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Relative dimension transports along an equality of morphisms. -/
private theorem relativeDimension_of_eq {X S : Scheme.{u}} {f g : X ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) {d : ℕ}
    (hf : RelativeDimension f d) : RelativeDimension g d := by
  subst h
  exact hf

/-- A flat morphism locally of finite presentation with Cohen–Macaulay fibres and preconnected
source has pure relative dimension: of the clopen pieces of pure relative dimension of
Stacks 02NM, the one containing a given point is the whole source. -/
theorem exists_relativeDimension_of_preconnectedSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [PreconnectedSpace X] (hCM : ∀ s : S, IsCohenMacaulay (f.fiber s)) :
    ∃ d : ℕ, RelativeDimension f d := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, fun s ⟨w⟩ ↦ (hX.false (f.fiberι s w)).elim⟩
  obtain ⟨U, hclopen, hcover, -, hrel⟩ := exists_clopen_relativeDimension f hCM
  have hx₀ : x₀ ∈ iSup U := hcover ▸ trivial
  obtain ⟨d, hd⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
  have htop : U d = ⊤ := TopologicalSpace.Opens.coe_inj.1 ((hclopen d).eq_univ ⟨x₀, hd⟩)
  have hrel := hrel d
  rw [htop] at hrel
  exact ⟨d, relativeDimension_of_eq
    (by rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
    (RelativeDimension.comp_isOpenImmersion X.topIso.inv _ hrel)⟩

/-- A smooth morphism with preconnected source has pure relative dimension. Its fibres are
Cohen–Macaulay by `AlgebraicGeometry.isCohenMacaulay_fiber_of_smooth`. -/
theorem exists_relativeDimension_of_smooth_of_preconnectedSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [PreconnectedSpace X] :
    ∃ d : ℕ, RelativeDimension f d :=
  exists_relativeDimension_of_preconnectedSpace f (isCohenMacaulay_fiber_of_smooth f)

end AlgebraicGeometry

end
