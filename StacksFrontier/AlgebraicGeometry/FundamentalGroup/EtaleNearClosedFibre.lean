module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# A finite locally free morphism étale over a closed subscheme is étale near it

Let `f : U ⟶ S` be finite locally free, and let `z : Z ⟶ S` be a morphism over which the base
change of `f` is étale. Then `f` is étale over an open neighbourhood of the image of `z`. This is
the last step of the proof of [Stacks, Tag 0EK1]: the relative spectrum of the algebraized
algebra is finite locally free over a neighbourhood of the closed subscheme, and its restriction
to the closed subscheme is the given finite étale cover, so it is étale near the closed subscheme
by More on Morphisms, Lemma 37.12.3.

## Main results

* `AlgebraicGeometry.exists_etale_morphismRestrict_of_isPullback` — the statement above: there is
  an open `W` of `S` containing the image of `z` such that `f ∣_ W` is étale.

## Implementation notes

The source argues through the fibres. Here the étale locus does the work directly: a finite
locally free morphism is flat and locally of finite presentation, so the étale locus of `f` is
compatible with the base change along `z` (`AlgebraicGeometry.etaleAt_iff_of_isPullback`, Tag
0476), and every point of `U` over the image of `z` comes from a point of the base change, at
which the base change is étale. The non-étale locus of `f` is closed
(`AlgebraicGeometry.isOpen_setOf_etaleAt`) and `f` is finite, hence a closed map, so its image is
a closed subset of `S` missing the image of `z`; `W` is its complement. Over `W` every point of
the source is a point of étaleness, and the restriction `f ∣_ W` is a base change of `f` along the
open immersion of `W`, so it is étale at every point.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A finite locally free morphism whose base change along `z` is étale is étale over an open
neighbourhood of the image of `z`.** -/
public theorem exists_etale_morphismRestrict_of_isPullback {U S C Z : Scheme.{u}} (f : U ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree f] {g : C ⟶ U} {c : C ⟶ Z} {z : Z ⟶ S}
    (h : IsPullback g c f z) [Etale c] :
    ∃ W : S.Opens, Set.range z.base ⊆ (W : Set S) ∧ Etale (f ∣_ W) := by
  obtain ⟨_, hflat, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  let W : S.Opens := ⟨(f.base '' {x : U | ¬ EtaleAt f x})ᶜ,
    (f.isClosedMap _ (isOpen_setOf_etaleAt f).isClosed_compl).isOpen_compl⟩
  refine ⟨W, ?_, ?_⟩
  · rintro _ ⟨ζ, rfl⟩ ⟨x, hx, hxζ⟩
    obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x ζ hxζ
    have hg : g.base (h.isoPullback.inv.base p) = x := by
      rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hp₁]
    rw [← hg] at hx
    exact hx ((etaleAt_iff_of_isPullback h (Or.inl hflat) _).mpr
      ((etale_iff_forall_etaleAt c).mp inferInstance _))
  · refine (etale_iff_forall_etaleAt (f ∣_ W)).mpr fun x => ?_
    refine (etaleAt_iff_of_isPullback (isPullback_morphismRestrict f W).flip (Or.inl hflat) x).mp ?_
    by_contra hx
    have hxW : (f ⁻¹ᵁ W).ι.base x ∈ (f ⁻¹ᵁ W : Set U) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact hxW ⟨_, hx, rfl⟩

end AlgebraicGeometry

end
