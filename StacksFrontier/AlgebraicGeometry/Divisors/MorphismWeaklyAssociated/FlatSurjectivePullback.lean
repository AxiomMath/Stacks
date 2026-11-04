module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.FlatPullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints

/-!
# Weakly associated points under a flat surjective pullback

Let `f : X ⟶ S` be a flat surjective morphism of schemes and let `G` be an `𝒪_S`-module. Every
weakly associated point of `G` has a preimage in `X` which is weakly associated to `f^*G`:
surjectivity makes the fibre over the point nonempty, and a generic point of an irreducible
component of that fibre is weakly associated to the pullback by Stacks 05F0.

## Main results

* `AlgebraicGeometry.exists_isWeaklyAssociatedPoint_pullback_of_flat_of_surjective`: the
  existence of such a preimage.

## Implementation notes

The point produced is the image in `X` of a generic point of an irreducible component of the
scheme-theoretic fibre `f.fiber s`, which exists because the fibre is a nonempty scheme and
therefore a nonempty quasi-sober space. Stacks 05F0 is stated at the canonical point
`f.asFiber x` of the fibre over the image of `x`, so it is applied after identifying that point
with the chosen generic point; that identification is where the fibre over `s` and the fibre
over `f x` are matched.

Neither quasi-coherence of `G` nor any finiteness hypothesis on `f` enters: Stacks 05F0 needs
none, the flatness being used on the stalks and the generic point only through the nilpotence of
the maximal ideal of the local ring of the fibre there.

## References

* [Stacks Project, Tag 05F0](https://stacks.math.columbia.edu/tag/05F0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of a fibre which is generic in that fibre is, read as the canonical point of the
fibre over its own image, generic there. -/
private theorem mem_genericPoints_asFiber_of_fiberι_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (y : Y) (h : f x = y) (ξ : f.fiber y) (hξ : f.fiberι y ξ = x)
    (hgen : ξ ∈ genericPoints (f.fiber y)) :
    f.asFiber x ∈ genericPoints (f.fiber (f x)) := by
  subst h
  have heq : ξ = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by rw [hξ, f.fiberι_asFiber])
  exact heq ▸ hgen

/-- Every nonempty fibre of a morphism of schemes carries a point which is generic in it: a
scheme is a quasi-sober space, so the irreducible component through any of its points has a
generic point. -/
private theorem exists_mem_genericPoints_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (ξ₀ : f.fiber y) : ∃ ξ : f.fiber y, ξ ∈ genericPoints (f.fiber y) :=
  ⟨_, (genericPoints.ofComponent
    ⟨irreducibleComponent ξ₀, irreducibleComponent_mem_irreducibleComponents ξ₀⟩).2⟩

/-- **A weakly associated point of a module has a weakly associated preimage under a flat
surjective morphism.** Let `f : X ⟶ S` be flat and surjective and let `G` be an `𝒪_S`-module. If
`s` is weakly associated to `G`, then some point of `X` above `s` is weakly associated to
`f^*G`.

Surjectivity makes the fibre of `f` over `s` nonempty, so that fibre has a generic point of an
irreducible component; the image of such a point in `X` lies above `s` and is weakly associated
to `f^*G` by Stacks 05F0. -/
theorem exists_isWeaklyAssociatedPoint_pullback_of_flat_of_surjective {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [Surjective f] (G : S.Modules) {s : S}
    (hs : Stacks.Divisors.IsWeaklyAssociatedPoint G s) :
    ∃ x : X, f x = s ∧
      Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback f).obj G) x := by
  obtain ⟨x₀, hx₀⟩ := Surjective.surj (f := f) s
  obtain ⟨ξ, hξ⟩ := exists_mem_genericPoints_fiber f s (Scheme.Hom.asFiberAt f x₀ s hx₀)
  have hfι : f (f.fiberι s ξ) = s := f.apply_fiberι s ξ
  refine ⟨f.fiberι s ξ, hfι, ?_⟩
  refine isWeaklyAssociatedPoint_pullback_of_isGenericPoint_fiber f G (f.fiberι s ξ)
    ((Flat.iff_flat_stalkMap f).mp inferInstance _)
    (mem_genericPoints_asFiber_of_fiberι_eq f _ s hfι ξ rfl hξ) ?_
  rw [hfι]
  exact hs

end AlgebraicGeometry

end
