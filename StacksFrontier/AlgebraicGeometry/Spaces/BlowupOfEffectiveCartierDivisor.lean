module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup

/-!
# Blowing up an algebraic space in an effective Cartier divisor

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace which is an effective Cartier divisor.  Then the blowup of `X` in `Z` is the identity
morphism of `X`.

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_id_of_isEffectiveCartierDivisor` is **Stacks 085V**:
  the identity morphism of `X` is the blowup of `X` in an effective Cartier divisor `Z ⊆ X`.
* `AlgebraicGeometry.Space.IsBlowupAlong.isIso_of_isEffectiveCartierDivisor` is the same
  statement read off a given blowup: any morphism which is the blowup of `X` in an effective
  Cartier divisor is an isomorphism.

## Implementation notes

The blowup of `X` in `Z` is characterised by the universal property of Tag 085U:
`AlgebraicGeometry.Space.IsBlowupAlong Z f` says that `f : X' ⟶ X`, viewed as an object of the
category `𝒞` of algebraic spaces over `X` on which the inverse image of `Z` is an effective
Cartier divisor, is a terminal object of `𝒞`. The statement "the blowup of `X` in `Z` is the
identity morphism of `X`" is therefore `IsBlowupAlong Z (𝟙 X)`: terminal objects are unique up
to unique isomorphism over `X`, so this says both that the blowup of `X` in `Z` exists and that
every morphism which is that blowup is uniquely isomorphic, over `X`, to the identity of `X`.
The second reading is `AlgebraicGeometry.Space.IsBlowupAlong.isIso_of_isEffectiveCartierDivisor`,
the algebraic-space analogue of the scheme-level Tag 0807
(`Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor`); it is the weaker of the two,
since the `IsIso` form is vacuous for a space with no blowup.

The whole content is that the identity of `X` lies in `𝒞`, which is exactly the hypothesis that
`Z` is an effective Cartier divisor: the inverse image of `Z` along `𝟙 X` is `Z` itself.  That
last identification is definitional here — `CategoryTheory.Subfunctor.preimage` of a subfunctor
along an identity natural transformation has the same sections, and
`AlgebraicGeometry.Space.ClosedSubspaces` is a subtype — so
`AlgebraicGeometry.Space.isPullbackDefined_id` is literally the hypothesis.

Terminality is then inherited from `CategoryTheory.Over.mkIdTerminal`, the terminality of
`𝟙 X` in the whole of `Spaces/X`, because `𝒞` is a *full* subcategory of `Spaces/X`: a
morphism into `⟨Over.mk (𝟙 X), _⟩` in `𝒞` is nothing more than a morphism into
`Over.mk (𝟙 X)` in `Spaces/X`, so existence is `CategoryTheory.ObjectProperty.homMk` of the
morphism downstairs and uniqueness is faithfulness of
`CategoryTheory.ObjectProperty.ι` together with the uniqueness half of terminality
downstairs.

## References

* [Stacks Project, Tag 085V](https://stacks.math.columbia.edu/tag/085V)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An effective Cartier divisor `Z ⊆ X` pulls back along the identity of `X` to itself, so the
pullback of `Z` along `𝟙 X` is defined in the sense of Tag 083Y.  Equivalently: the identity
morphism of `X` is an object of the category `𝒞` of Tag 085U with centre `Z`.

The inverse image of `Z` along `𝟙 X` has the same sections as `Z` over every object of the big
site, so the two closed subspaces are the same term and this is the hypothesis itself. -/
theorem isPullbackDefined_id (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsEffectiveCartierDivisor B S hS X Z) :
    IsPullbackDefined B S hS (𝟙 X) Z :=
  hZ

/-- **Stacks 085V.** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z ⊆ X` be an effective Cartier divisor.  **The blowup of `X` in `Z` is the identity morphism
of `X`.**

Being the blowup of `X` in `Z` is the universal property of Tag 085U, which
`AlgebraicGeometry.Space.IsBlowupAlong` records: terminality in the category `𝒞` of algebraic
spaces over `X` on which the inverse image of `Z` is an effective Cartier divisor.  The
identity of `X` is an object of `𝒞` precisely because `Z` is an effective Cartier divisor, and
it is terminal in `𝒞` because it is already terminal in all of `Spaces/X` and `𝒞` is a full
subcategory.  Since terminal objects are unique up to unique isomorphism over `X`, this says
that the blowup of `X` in `Z` exists and is the identity of `X`; see
`AlgebraicGeometry.Space.IsBlowupAlong.isIso_of_isEffectiveCartierDivisor`. -/
@[stacks 085V]
theorem isBlowupAlong_id_of_isEffectiveCartierDivisor (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsEffectiveCartierDivisor B S hS X Z) :
    IsBlowupAlong B S hS Z (𝟙 X) := by
  refine ⟨isPullbackDefined_id B S hS X Z hZ, ⟨IsTerminal.ofUniqueHom
    (fun Y => ObjectProperty.homMk
      ((Over.mkIdTerminal (X := X)).from Y.obj)) fun Y m => ?_⟩⟩
  exact (ObjectProperty.ι (IsCartierOver B S hS Z)).map_injective
    ((Over.mkIdTerminal (X := X)).hom_ext _ _)

variable {B S hS}

/-- **Stacks 085V**, read off a given blowup: if `Z ⊆ X` is an effective Cartier divisor and
`f : X' ⟶ X` is the blowup of `X` in `Z`, then `f` is an isomorphism.

This is the algebraic-space analogue of the scheme-level Tag 0807,
`Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor`.  It follows from
`AlgebraicGeometry.Space.isBlowupAlong_id_of_isEffectiveCartierDivisor` and the uniqueness of
blowups over `X`: `f` is isomorphic over `X` to the identity of `X`, hence equal to the
isomorphism witnessing that. -/
theorem IsBlowupAlong.isIso_of_isEffectiveCartierDivisor {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X} (hf : IsBlowupAlong B S hS Z f)
    (hZ : IsEffectiveCartierDivisor B S hS X Z) : IsIso f := by
  obtain ⟨e, he⟩ :=
    IsBlowupAlong.exists_iso hf (isBlowupAlong_id_of_isEffectiveCartierDivisor B S hS X Z hZ)
  have hfe : f = e.hom := by simpa using he.symm
  rw [hfe]
  infer_instance

end AlgebraicGeometry.Space

end
