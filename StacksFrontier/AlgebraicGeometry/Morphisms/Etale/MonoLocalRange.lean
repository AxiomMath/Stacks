module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OpenImmersionCriterion

/-!
# A monomorphism étale at a point is an open immersion near that point

Let `i : Z ⟶ W` be a monomorphism of schemes which is étale at a point `z` of `Z`. Étaleness at a
point is étaleness on an affine open neighbourhood `V` of it, and `V ⟶ W` is then a
monomorphism — hence universally injective — which is étale, so it is an open immersion by Tag
025G. The image of `i` therefore contains an open neighbourhood of `i z`.

When the image of `i` is moreover closed — `i` a closed immersion, say — this forces every
irreducible closed subset of `W` through `i z` to lie inside that image: such a subset meets the
open neighbourhood, hence meets it densely, and the image is closed.

Both statements are the shape in which the last step of the proof of Stacks 0B0E is used. There
`Z ⊆ Z''` is a closed subvariety of the closed subscheme `Z'' = π^{-1}(π(Z))` of `X`, and `Z ⟶ Z''`
is étale at a chosen closed point `x` of `Z` by the cancellation law of Tag 02GW, both `Z` and
`Z''` being étale over `Z' = π(Z)` there; the source concludes "`Z = Z''` in a Zariski
neighbourhood of `x`", and uses it to see that no other component of `Z''` passes through `x`.

## Main results

* `AlgebraicGeometry.exists_isOpen_mem_subset_range_of_etaleAt_of_mono`: the image of a
  monomorphism étale at a point contains an open neighbourhood of the image of that point.
* `AlgebraicGeometry.subset_range_of_etaleAt_of_mono`: with closed image, every irreducible
  closed subset through that point lies in the image.

## Implementation notes

The hypothesis is `Mono` rather than `IsClosedImmersion` because that is all the argument uses;
closedness of the image is a separate hypothesis of the second statement, so that it applies to
an immersion as well as to a closed immersion.

The density step is run by hand through `mem_closure_iff` and the preirreducibility of the
subset: an open neighbourhood of a point of an irreducible set meets every other open set that
the set meets.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A monomorphism of schemes which is étale at a point has open image near that point.** On an
affine open neighbourhood of the point the morphism becomes a universally injective étale
morphism, hence an open immersion by Tag 025G, so its range is an open subset of the target
contained in the range of the original morphism. -/
public theorem exists_isOpen_mem_subset_range_of_etaleAt_of_mono {Z W : Scheme.{u}} (i : Z ⟶ W)
    [Mono i] {z : Z} (hi : EtaleAt i z) :
    ∃ U : Set W, IsOpen U ∧ i.base z ∈ U ∧ U ⊆ Set.range i.base := by
  obtain ⟨V, -, hzV, het⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt i z hi
  have hmono : Mono (V.ι ≫ i) := inferInstance
  have hui : UniversallyInjective (V.ι ≫ i) := inferInstance
  have htfae := (tfae_isOpenImmersion (V.ι ≫ i)).out 2 1
  have hoi : IsOpenImmersion (V.ι ≫ i) := htfae.mp ⟨hui, het⟩
  refine ⟨Set.range (V.ι ≫ i).base, hoi.base_open.isOpen_range, ⟨⟨z, hzV⟩, ?_⟩, ?_⟩
  · rfl
  · rintro _ ⟨v, rfl⟩
    exact ⟨V.ι.base v, rfl⟩

/-- **An irreducible closed subset through a point of étaleness lies in the image.** Let
`i : Z ⟶ W` be a monomorphism with closed image which is étale at `z`. Then every irreducible
closed subset of `W` containing `i z` is contained in the image of `i`: it meets the open
neighbourhood of `i z` inside that image, so it meets it densely, and the image is closed. -/
public theorem subset_range_of_etaleAt_of_mono {Z W : Scheme.{u}} (i : Z ⟶ W) [Mono i] {z : Z}
    (hi : EtaleAt i z) (hcl : IsClosed (Set.range i.base)) {T : Set W} (hT : IsIrreducible T)
    (hz : i.base z ∈ T) :
    T ⊆ Set.range i.base := by
  obtain ⟨U, hU, hzU, hUr⟩ := exists_isOpen_mem_subset_range_of_etaleAt_of_mono i hi
  have hdense := subset_closure_inter_of_isPreirreducible_of_isOpen hT.2 hU
    ⟨i.base z, hz, hzU⟩
  exact hdense.trans (closure_minimal (fun x hx => hUr hx.2) hcl)

end AlgebraicGeometry

end
