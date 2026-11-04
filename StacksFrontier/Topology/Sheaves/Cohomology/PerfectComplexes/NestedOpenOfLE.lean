module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect

/-!
# An open inside a larger open, and the closed support that makes [Stacks, Tag 08DP] apply

Let `X` be a ringed space and `U ≤ W` two opens. Reading `U` as an open `Z` of the subspace `W`
presents `X|_U` as a nested open subspace of `X|_W`, and
`Stacks.Cohomology.ClosedSupportPerfect.nestedOpenToAmbientIso` identifies
`(X|_W)|_Z` with `X|_U` as ringed spaces.

That identification is what lets [Stacks, Tag 08DP] — the derived pushforward of a perfect object
with closed support is perfect — be applied along `Z ⟶ W` to an object given on `U`. Its
hypothesis is that the image of the support in the ambient space is closed, and over `X` that
fails for `T ∩ U` with `T` merely closed in `X`; over `W` it holds as soon as `T ∩ W ⊆ U`, because
the image is then `T ∩ W`, closed in `W`.

## Main definitions and results

* `Stacks.Cohomology.ClosedSupportPerfect.nestedOpenOfLE`: `U` read as an open of the subspace
  `W`, for `U ≤ W`.
* `Stacks.Cohomology.ClosedSupportPerfect.image_nestedOpenOfLE`: its image in `X` is `U`.
* `Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict`: the resulting isomorphism
  of ringed spaces `(X|_W)|_Z ≅ X|_U`.
* `Stacks.Cohomology.ClosedSupportPerfect.isClosed_image_nestedPreimage`: **the hypothesis of
  [Stacks, Tag 08DP] along `Z ⟶ W`.** If `T` is closed in `X` and `T ∩ W ⊆ U`, the image in `W`
  of the preimage of `T` in `(X|_W)|_Z` is closed.

## Where `T ∩ W ⊆ U` comes from

In [Stacks, Tag 08EK] the open `W` is `U ∪ (X ∖ T)`: a point of `W` lying in `T` cannot lie in
`X ∖ T`, so it lies in `U`. That is the whole reason for enlarging `U` to `W`, and it is what
replaces the source's iteration of cones on multiplication by the equations of `T`.

## References

* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ClosedSupportPerfect

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U W : Opens X)

/-- `U` read as an open of the subspace `W`, for `U ≤ W`: the preimage of `U` under the
inclusion of `W`. -/
def nestedOpenOfLE : Opens (X.restrict W.isOpenEmbedding) :=
  ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩

/-- The image in `X` of `U` read as an open of `W` is `U` again. -/
theorem image_nestedOpenOfLE (hUW : U ≤ W) :
    W.isOpenEmbedding.functor.obj (nestedOpenOfLE U W) = U := by
  apply Opens.ext
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hUW hx⟩, hx, rfl⟩⟩

/-- **`(X|_W)|_Z ≅ X|_U`** for `U ≤ W` and `Z` the copy of `U` inside `W`: the nested open
subspace of `Stacks.Cohomology.ClosedSupportPerfect.nestedOpenToAmbientIso`, with its image
identified with `U`. -/
def restrictNestedIsoRestrict (hUW : U ≤ W) :
    (X.restrict W.isOpenEmbedding).restrict (nestedOpenOfLE U W).isOpenEmbedding ≅
      X.restrict U.isOpenEmbedding :=
  nestedOpenToAmbientIso W (nestedOpenOfLE U W) ≪≫
    eqToIso (congrArg (fun O : Opens X => X.restrict O.isOpenEmbedding)
      ((opensFunctor_nestedOpenInclusion_obj_top W (nestedOpenOfLE U W)).trans
        (image_nestedOpenOfLE U W hUW)))

/-- **The hypothesis of [Stacks, Tag 08DP] along `Z ⟶ W`.** If `T` is closed in `X` and
`T ∩ W ⊆ U`, then the image in the subspace `W` of the preimage of `T` in `(X|_W)|_Z` is closed:
that image is the preimage of `T` in `W`, which is closed because `T` is.

Over `X` the corresponding statement is false — `T ∩ U` need not be closed in `X` — and that is
exactly why [Stacks, Tag 08EK] pushes forward over `W` rather than over `X`. -/
theorem isClosed_image_nestedPreimage (T : Set X) (hT : IsClosed T)
    (hTWU : T ∩ (W : Set X) ⊆ (U : Set X)) :
    IsClosed (((X.restrict W.isOpenEmbedding).ofRestrict
      (nestedOpenOfLE U W).isOpenEmbedding).hom.base ''
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' T))) := by
  have himage : ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding).hom.base ''
          (Subtype.val ⁻¹' (Subtype.val ⁻¹' T)) =
      Subtype.val ⁻¹' T := by
    ext y
    exact ⟨by rintro ⟨z, hz, rfl⟩; exact hz, fun hy => ⟨⟨y, hTWU ⟨hy, y.2⟩⟩, hy, rfl⟩⟩
  rw [himage]
  exact hT.preimage continuous_subtype_val

end Stacks.Cohomology.ClosedSupportPerfect

end
