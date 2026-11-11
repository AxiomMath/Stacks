module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined

/-!
# Representability by algebraic spaces is local on the source and the target: Stacks 0AN4

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AN4** asserts that the following are equivalent:

1. `f` is representable by algebraic spaces;
2. there is a commutative square with `U`, `V` formal algebraic spaces, vertical arrows
   representable by algebraic spaces, `U ⟶ X` surjective étale, and `U ⟶ V` representable by
   algebraic spaces (`AlgebraicGeometry.FormalSpace.IsRepresentableOnSomeSquare`);
3. for every commutative square with `U`, `V` formal algebraic spaces and vertical arrows
   representable by algebraic spaces, `U ⟶ V` is representable by algebraic spaces
   (`AlgebraicGeometry.FormalSpace.IsRepresentableOnEverySquare`);
4. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with each `Xⱼᵢ ⟶ Yⱼ` representable by algebraic
   spaces (`AlgebraicGeometry.FormalSpace.IsRepresentableAfterTargetCover`);
5. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` of `Xᵢ ⟶ X ⟶ Y` with `Yᵢ` an affine formal algebraic space and both
   `Yᵢ ⟶ Y` and `Xᵢ ⟶ Yᵢ` representable by algebraic spaces
   (`AlgebraicGeometry.FormalSpace.IsRepresentableOnFactoredAtlas`).

The source lists a sixth item, *add more here*, which is a placeholder and not a condition.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentable_tfae`: **Stacks 0AN4**, the equivalence of
  conditions (1) to (5).

## Implementation notes

Every input of the source's proof is a theorem of this library; nothing is assumed.

* (1) ⟹ (2) and (3) ⟹ (1) take the square formed by the identities of `X` and `Y`.
* (2) ⟹ (1): the composite `U ⟶ X ⟶ Y` equals `U ⟶ V ⟶ Y`, which is representable by
  algebraic spaces by Stacks 0APY, and representability by algebraic spaces descends along the
  surjective representable étale map `U ⟶ X`
  (`FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective`,
  which runs on Stacks 0BGR). This is the étale case of the source's appeal to Stacks 0AMP.
* (1) ⟹ (3): `U ⟶ X ⟶ Y` is representable by algebraic spaces by Stacks 0APY and equals
  `U ⟶ V ⟶ Y`, so Stacks 0AQ0 for the formal algebraic space `V`
  (`FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`) applies.
* (3) ⟹ (4): the fibre product `Yⱼ ×_Y X` of a chart of `Y` with `f` is a formal algebraic
  space by Stacks 0AJ3
  (`FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`),
  so it has an atlas, and the squares it forms are squares as in (3).
* (4) ⟹ (5) composes the coverings, and (5) ⟹ (1) is locality of representability on the
  source along a jointly surjective representable étale family; both are proved in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFamily`.

Surjectivity of a covering, and of `U ⟶ X` in (2), is surjectivity of the morphism of sheaves,
`CategoryTheory.Sheaf.IsLocallySurjective`, which is how Definition 0AIM is recorded in this
library (`AlgebraicGeometry.FormalSpace.IsAffineEtaleCover`).

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0APY](https://stacks.math.columbia.edu/tag/0APY)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AN4.** For a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` the
following are equivalent:
1. `f` is representable by algebraic spaces;
2. there is a commutative square `U ⟶ V` over `f` with `U`, `V` formal algebraic spaces,
   vertical arrows representable by algebraic spaces, `U ⟶ X` surjective étale and `U ⟶ V`
   representable by algebraic spaces;
3. every commutative square `U ⟶ V` over `f` with `U`, `V` formal algebraic spaces and
   vertical arrows representable by algebraic spaces has `U ⟶ V` representable by algebraic
   spaces;
4. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM with every `Xⱼᵢ ⟶ Yⱼ` representable by algebraic
   spaces;
5. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` and `Xᵢ ⟶ Yᵢ`
   representable by algebraic spaces.

The source's sixth item, *add more here*, is a placeholder and not a condition. -/
@[stacks 0AN4 "the equivalence of conditions (1) to (5); the sixth item of the source, \
add more here, is a placeholder"]
theorem isRepresentable_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    List.TFAE [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
      IsRepresentableOnSomeSquare B S hS f,
      IsRepresentableOnEverySquare B S hS f,
      IsRepresentableAfterTargetCover B S hS f,
      IsRepresentableOnFactoredAtlas B S hS f] := by
  tfae_have 1 → 2 := isRepresentableOnSomeSquare_of_isRepresentable B S hS f hX hY
  tfae_have 2 → 1 := by
    rintro ⟨U, V, p, q, t, -, -, hp, hpsurj, hq, ht, hcomm⟩
    have hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom := by
      rw [congrArg (fun k : U ⟶ Y ↦ k.hom) hcomm]
      exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS t.hom q.hom ht hq
    exact isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective B S hS f p hp
      hpsurj hpf
  tfae_have 1 → 3 := by
    intro hf U V p q t _ hV hp _ hcomm
    have h : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom :=
      Space.isRepresentableByAlgebraicSpacesULift_comp B S hS p.hom f.hom hp hf
    rw [hcomm] at h
    exact isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace B S hS t q hV h
  tfae_have 3 → 1 := isRepresentable_of_isRepresentableOnEverySquare B S hS f hX hY
  tfae_have 3 → 4 := isRepresentableAfterTargetCover_of_everySquare B S hS f hY
    (fun _ v hV _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS v f
      hY hV hX)
  tfae_have 4 → 5 := isRepresentableOnFactoredAtlas_of_afterTargetCover B S hS f
  tfae_have 5 → 1 := isRepresentable_of_onFactoredAtlas B S hS f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
