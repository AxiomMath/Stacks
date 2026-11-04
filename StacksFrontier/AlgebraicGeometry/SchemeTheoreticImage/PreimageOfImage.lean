module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.CancellationAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.MonoLocalRange
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.LocalIsomorphism

/-!
# A closed subscheme is its own preimage near a point of étaleness

Let `h : Y ⟶ P` be a morphism of schemes, let `i : Z ⟶ Y` be a closed immersion with `Z`
reduced, and let `z` be a point of `Z` over a point `y` of `Y`. Suppose

* `h` is étale at `y`, and
* `h|_Z : Z ⟶ P` is a closed immersion over an open neighbourhood `R` of `h y`.

Then `Z` contains the whole of `h^{-1}(h(Z))` on a Zariski neighbourhood of `y`.

This is the last step of the proof of Stacks 0B0E. There `h = π` is the final projection of the
chain, `Z` is the subvariety being moved, and the conclusion is that no component of
`π^{-1}(π(Z))` other than `Z` passes through the chosen point `y`, which is what turns the
source's non-strict dimension inequality into a strict one.

## The shape of the argument

Topologically the statement is false: a Zariski neighbourhood of `y` meets every other component
of `h^{-1}(h(Z))` that is not cut out by a closed set avoiding `y`, and avoiding `y` is what has
to be proved. The argument is scheme-theoretic, and runs through the *scheme-theoretic* preimage
`Z'' = h^{-1}(Z')` of the scheme-theoretic image `Z' = (i ≫ h).image`:

* `Z ⟶ Z'` is étale at `z`, by
  `AlgebraicGeometry.Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict` — this is
  where the closed immersion over `R` is used;
* `Z'' ⟶ Z'` is étale at the point over `y`, being the base change of `h` along the closed
  immersion of `Z'`, by `AlgebraicGeometry.etaleAt_of_isPullback` — which needs no flatness;
* hence `Z ⟶ Z''` is étale at `z` by the pointwise cancellation law
  `AlgebraicGeometry.etaleAt_of_comp_right`, and it is a monomorphism because it composes with
  the closed immersion of `Z''` in `Y` to the closed immersion `i`;
* so its image contains an open neighbourhood of the point over `y`, by
  `AlgebraicGeometry.exists_isOpen_mem_subset_range_of_etaleAt_of_mono`.

The open subset of `Y` is then the complement of the image, under the closed immersion
`Z'' ⟶ Y`, of the complement of that neighbourhood.

## Main results

* `AlgebraicGeometry.exists_isOpen_inter_preimage_closure_range_subset`: the statement above.

## Implementation notes

The image is taken with a closure — the conclusion is about `h^{-1}(closure (h(Z)))` rather than
`h^{-1}(h(Z))` — because that is what the range of the embedding of the scheme-theoretic image
is, and it makes the statement stronger. When `h` is finite, as it is in Stacks 0B0E, the two
agree.

Only quasi-compactness of `h` is assumed, which is what makes the scheme-theoretic image of
`i ≫ h` have `closure (range (i ≫ h))` as its underlying set.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed subscheme is the whole preimage of its image on a neighbourhood of a point of
étaleness.** Let `h : Y ⟶ P` be quasi-compact, let `i : Z ⟶ Y` be a closed immersion with `Z`
reduced, and let `z` be a point of `Z` with `i z = y`. If `h` is étale at `y` and the composite
`i ≫ h` is a closed immersion over an open neighbourhood `R` of `h y`, then there is an open
neighbourhood `V` of `y` in `Y` with

`V ∩ h^{-1}(closure (h (Z))) ⊆ Z`.

In the proof of Stacks 0B0E this says that no component of `π^{-1}(π(Z))` other than `Z` passes
through the chosen closed point of `Z`. -/
public theorem exists_isOpen_inter_preimage_closure_range_subset {Y P Z : Scheme.{u}}
    (h : Y ⟶ P) [QuasiCompact h] (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]
    {y : Y} {z : Z} (hz : i.base z = y) (hh : EtaleAt h y)
    (R : P.Opens) (hR : h.base y ∈ R) (hci : IsClosedImmersion ((i ≫ h) ∣_ R)) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      V ∩ h.base ⁻¹' closure (Set.range (i ≫ h).base) ⊆ Set.range i.base := by
  have : QuasiCompact (i ≫ h) := inferInstance
  -- the scheme-theoretic image of `Z` in `P`, and `Z ⟶ Z'` étale at `z`
  set ι : (i ≫ h).image ⟶ P := (i ≫ h).imageι with hιdef
  have hetZ : EtaleAt (i ≫ h).toImage z :=
    Scheme.Hom.etaleAt_toImage_of_isClosedImmersion_morphismRestrict (i ≫ h) R hci
      (show (i ≫ h).base z ∈ R from by
        rw [show (i ≫ h).base z = h.base y from by rw [← hz]; rfl]
        exact hR)
  -- the scheme-theoretic preimage `Z'' = h^{-1}(Z')`
  set sq : IsPullback (pullback.fst h ι) (pullback.snd h ι) h ι := IsPullback.of_hasPullback h ι
  have hfstci : IsClosedImmersion (pullback.fst h ι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  set w : Z ⟶ (pullback h ι : Scheme.{u}) :=
    pullback.lift i (i ≫ h).toImage (Scheme.Hom.toImage_imageι (i ≫ h)).symm with hwdef
  have hwfst : w ≫ pullback.fst h ι = i := pullback.lift_fst _ _ _
  have hwsnd : w ≫ pullback.snd h ι = (i ≫ h).toImage := pullback.lift_snd _ _ _
  have : Mono w := mono_of_mono_fac hwfst
  -- the base change of `h` is étale at the point over `y`
  have hfst (x : Z) : (pullback.fst h ι).base (w.base x) = i.base x :=
    congrArg (fun f => f.base x) hwfst
  have hbase : (pullback.fst h ι).base (w.base z) = y := (hfst z).trans hz
  have hsndet : EtaleAt (pullback.snd h ι) (w.base z) :=
    etaleAt_of_isPullback sq (w.base z) (by rw [hbase]; exact hh)
  -- hence `Z ⟶ Z''` is étale at `z`, and is a monomorphism
  have hwet : EtaleAt w z :=
    etaleAt_of_comp_right w (pullback.snd h ι) (by rw [hwsnd]; exact hetZ) hsndet
  obtain ⟨O, hOopen, hOmem, hOsub⟩ :=
    exists_isOpen_mem_subset_range_of_etaleAt_of_mono w hwet
  -- the open of `Y` is the complement of the image of the complement of `O`
  have himgcl : IsClosed ((pullback.fst h ι).base '' Oᶜ) :=
    (pullback.fst h ι).isClosedEmbedding.isClosedMap _ hOopen.isClosed_compl
  refine ⟨((pullback.fst h ι).base '' Oᶜ)ᶜ, himgcl.isOpen_compl, ?_, ?_⟩
  · rintro ⟨u, huO, hu⟩
    exact huO ((pullback.fst h ι).isClosedEmbedding.injective (hu.trans hbase.symm) ▸ hOmem)
  · rintro y' ⟨hy'V, hy'pre⟩
    have hy'range : y' ∈ Set.range (pullback.fst h ι).base := by
      rw [Scheme.Pullback.range_fst, hιdef, Scheme.IdealSheafData.range_subschemeι,
        Scheme.Hom.support_ker]
      exact hy'pre
    obtain ⟨u, hu⟩ := hy'range
    have huO : u ∈ O := by
      by_contra hnot
      exact hy'V ⟨u, hnot, hu⟩
    obtain ⟨z', hz'⟩ := hOsub huO
    refine ⟨z', ?_⟩
    rw [← hu, ← hz', hfst]

end AlgebraicGeometry

end
