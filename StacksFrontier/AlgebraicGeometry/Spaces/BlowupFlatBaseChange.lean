module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria

/-!
# Blowing up commutes with flat base change

Let `S` be a scheme, let `g : X₁ ⟶ X₂` be a flat morphism of algebraic spaces over `S`, let
`Z₂ ⊆ X₂` be a closed subspace and let `Z₁ ⊆ X₁` be its inverse image.  Stacks 085S says that
the blowup of `X₁` in `Z₁` is the base change along `g` of the blowup of `X₂` in `Z₂`: there is
a cartesian square

```
X₁' ⟶ X₂'
 ↓      ↓
X₁ ⟶  X₂
```

This file proves that, in the form "any base change of the blowup along a flat morphism *is*
the blowup of the base in the inverse image of the centre", from which the cartesian square
follows for any blowup of `X₁` in `Z₁`.

## Main definitions

* `AlgebraicGeometry.Space.preimageClosedSubspace` is the inverse image of a closed subspace
  along a morphism of algebraic spaces, as a closed subspace of the source; it is the `Z₁` of
  the source.

## Main results

* `AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat` is **Stacks 085S**:
  for a flat `g : X₁ ⟶ X₂` and a cartesian square over `g` and the blowup `b₂ : X₂' ⟶ X₂` of
  `X₂` in `Z₂`, the projection `X₁ ×_{X₂} X₂' ⟶ X₁` is the blowup of `X₁` in the inverse image
  of `Z₂`.
* `AlgebraicGeometry.Space.isBlowupAlong_pullbackFst_of_isFlat` is the same statement for the
  chosen fibre product of the category of algebraic spaces.
* `AlgebraicGeometry.Space.exists_isPullback_blowup_of_isFlat` is Stacks 085S in the source's
  own words: a cartesian square relating the blowup of `X₁` in `Z₁` to the blowup of `X₂` in
  `Z₂`.

## Implementation notes

The blowup is named by its universal property, `AlgebraicGeometry.Space.IsBlowupAlong` of
Stacks 085U, rather than by the explicit construction of Stacks 085Q,
`AlgebraicGeometry.Space.blowUpAlong'`.  The latter IS available for algebraic spaces
(`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelationClosed.lean`), but only once a
presentation of the ambient space and the containment side-conditions on its charts have been
fixed, which this lemma's hypotheses do not supply.  That
is also why the conclusion is phrased as "the projection is the blowup" rather than as an
isomorphism with a constructed object: the two are equivalent, since any two blowups of `X₁` in
`Z₁` are isomorphic over `X₁`, and the passage is
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, used in
`AlgebraicGeometry.Space.exists_isPullback_blowup_of_isFlat`.

The proof is the universal-property proof, not the source's computation with the Rees algebra.
Flatness is used exactly once, for the one step of the source's argument that the universal
property cannot supply: the inverse image of `Z₁` in `X₁ ×_{X₂} X₂'` is the inverse image of the
exceptional divisor `E ⊆ X₂'` along the projection to `X₂'`, which is flat because `g` is, so it
is an effective Cartier divisor by Stacks 083Z (2),
`AlgebraicGeometry.Space.isPullbackDefined_of_isFlat`.  The remaining half — that every
`Y ⟶ X₁` on which `Z₁` pulls back to an effective Cartier divisor factors uniquely through the
projection — uses no hypothesis on `g` at all: the inverse image of `Z₂` in `Y` *is* the inverse
image of `Z₁` in `Y`, so finality of `b₂` applies to `Y ⟶ X₁ ⟶ X₂`.

## References

* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083Z](https://stacks.math.columbia.edu/tag/083Z)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 083Q for closed subspaces.** The inverse image of a closed subspace `Z ⊆ X` along a
morphism `f : Y ⟶ X` of algebraic spaces, as a closed subspace of `Y`.  This is the fibre
product `Z ×_X Y`. -/
def preimageClosedSubspace {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) : ClosedSubspaces B S hS Y.1 :=
  ⟨Z.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom Z.1 X.2 Y.2 Z.2⟩

/-- Effective Cartier-ness of a closed subspace depends only on its underlying subfunctor. -/
theorem isEffectiveCartierDivisor_of_subfunctor_eq {W : AlgebraicSpaces B S hS}
    {D D' : ClosedSubspaces B S hS W.1} (h : D.1 = D'.1)
    (hD : IsEffectiveCartierDivisor B S hS W D') :
    IsEffectiveCartierDivisor B S hS W D := by
  have he : D = D' := Subtype.ext h
  rw [he]
  exact hD

/-- The inverse image of a closed subspace along a composite is the iterated inverse image. -/
private theorem preimageClosedSubspace_comp {X Y W : AlgebraicSpaces B S hS}
    (a : W ⟶ Y) (u : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1) :
    (preimageClosedSubspace (a ≫ u) Z).1 =
      (preimageClosedSubspace a (preimageClosedSubspace u Z)).1 :=
  Subfunctor.preimage_comp Z.1 a.hom u.hom

/-- Taking inverse images of a closed subspace along the two legs of a commuting square gives
the same closed subspace of the corner. -/
private theorem preimage_eq_preimage_of_comp_eq {X W : AlgebraicSpaces B S hS}
    {Y Y' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    {a : W ⟶ Y} {u : Y ⟶ X} {a' : W ⟶ Y'} {u' : Y' ⟶ X} (h : a ≫ u = a' ≫ u') :
    (preimageClosedSubspace a (preimageClosedSubspace u Z)).1 =
      (preimageClosedSubspace a' (preimageClosedSubspace u' Z)).1 := by
  rw [← preimageClosedSubspace_comp, ← preimageClosedSubspace_comp, h]

/-- **Stacks 085S.** Let `g : X₁ ⟶ X₂` be a flat morphism of algebraic spaces over `S`, let
`Z₂ ⊆ X₂` be a closed subspace and let `b₂ : X₂' ⟶ X₂` be the blowup of `X₂` in `Z₂`.  Then for
any cartesian square with legs `q : W ⟶ X₁` and `r : W ⟶ X₂'` over `g` and `b₂`, the projection
`q` is the blowup of `X₁` in the inverse image of `Z₂`.

So the square expressing `W = X₁ ×_{X₂} X₂'` is the cartesian square of the source, with
`W = X₁'`.

Flatness enters only to see that the inverse image of the centre in `W` — which is the inverse
image along `r` of the exceptional divisor of `b₂` — is an effective Cartier divisor; the
universal property of `q` holds for an arbitrary `g`. -/
@[stacks 085S]
theorem isBlowupAlong_preimage_of_isPullback_of_isFlat
    {X₁ X₂ X₂' W : AlgebraicSpaces B S hS} {g : X₁ ⟶ X₂} (hg : IsFlat B S hS g.hom)
    {Z₂ : ClosedSubspaces B S hS X₂.1} {b₂ : X₂' ⟶ X₂}
    (hb₂ : IsBlowupAlong B S hS Z₂ b₂) {q : W ⟶ X₁} {r : W ⟶ X₂'}
    (sq : IsPullback q r g b₂) :
    IsBlowupAlong B S hS (preimageClosedSubspace g Z₂) q := by
  have hr : IsFlat B S hS r.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hg
  refine isBlowupAlong_of_existsUnique_lift ?_ ?_
  · refine isEffectiveCartierDivisor_of_subfunctor_eq
      (preimage_eq_preimage_of_comp_eq Z₂ sq.w) ?_
    exact isPullbackDefined_of_isFlat B S hS r (preimageClosedSubspace b₂ Z₂)
      hb₂.isPullbackDefined hr
  · intro Y y hy
    have hy₂ : IsPullbackDefined B S hS (y ≫ g) Z₂ :=
      isEffectiveCartierDivisor_of_subfunctor_eq (preimageClosedSubspace_comp y g Z₂) hy
    obtain ⟨l, hl, hlu⟩ := hb₂.existsUnique_lift (y ≫ g) hy₂
    refine ⟨sq.lift y l hl.symm, sq.lift_fst y l hl.symm, fun m hm => ?_⟩
    refine sq.hom_ext ?_ ?_
    · rw [sq.lift_fst, hm]
    · rw [sq.lift_snd]
      refine hlu (m ≫ r) ?_
      show (m ≫ r) ≫ b₂ = y ≫ g
      rw [Category.assoc, ← sq.w, ← Category.assoc, hm]

/-- **Stacks 085S for the chosen fibre product.** The first projection of the fibre product
`X₁ ×_{X₂} X₂'` of a flat morphism `g : X₁ ⟶ X₂` with the blowup `b₂ : X₂' ⟶ X₂` of `X₂` in a
closed subspace `Z₂` is the blowup of `X₁` in the inverse image of `Z₂`. -/
@[stacks 085S]
theorem isBlowupAlong_pullbackFst_of_isFlat
    {X₁ X₂ X₂' : AlgebraicSpaces B S hS} {g : X₁ ⟶ X₂} (hg : IsFlat B S hS g.hom)
    {Z₂ : ClosedSubspaces B S hS X₂.1} {b₂ : X₂' ⟶ X₂}
    (hb₂ : IsBlowupAlong B S hS Z₂ b₂) :
    IsBlowupAlong B S hS (preimageClosedSubspace g Z₂) (pullback.fst g b₂) :=
  isBlowupAlong_preimage_of_isPullback_of_isFlat hg hb₂ (IsPullback.of_hasPullback g b₂)

/-- **Stacks 085S in the source's phrasing.** For a flat morphism `g : X₁ ⟶ X₂` of algebraic
spaces over `S`, a closed subspace `Z₂ ⊆ X₂` with inverse image `Z₁ ⊆ X₁`, the blowup
`b₁ : X₁' ⟶ X₁` of `X₁` in `Z₁` and the blowup `b₂ : X₂' ⟶ X₂` of `X₂` in `Z₂`, there is a
morphism `X₁' ⟶ X₂'` making the square

```
X₁' ⟶ X₂'
 ↓      ↓
X₁ ⟶  X₂
```

cartesian.

The fibre product `X₁ ×_{X₂} X₂'` is a blowup of `X₁` in `Z₁` by
`AlgebraicGeometry.Space.isBlowupAlong_pullbackFst_of_isFlat`, and any two blowups of `X₁` in
`Z₁` are isomorphic over `X₁`, so `X₁'` is itself a fibre product. -/
@[stacks 085S]
theorem exists_isPullback_blowup_of_isFlat
    {X₁ X₂ X₁' X₂' : AlgebraicSpaces B S hS} {g : X₁ ⟶ X₂} (hg : IsFlat B S hS g.hom)
    {Z₂ : ClosedSubspaces B S hS X₂.1} {b₂ : X₂' ⟶ X₂}
    (hb₂ : IsBlowupAlong B S hS Z₂ b₂) {b₁ : X₁' ⟶ X₁}
    (hb₁ : IsBlowupAlong B S hS (preimageClosedSubspace g Z₂) b₁) :
    ∃ m : X₁' ⟶ X₂', IsPullback b₁ m g b₂ := by
  obtain ⟨e, he⟩ := hb₁.exists_iso (isBlowupAlong_pullbackFst_of_isFlat hg hb₂)
  refine ⟨e.hom ≫ pullback.snd g b₂, IsPullback.of_iso_pullback ⟨?_⟩ e he rfl⟩
  rw [← he, Category.assoc, Category.assoc, pullback.condition]

end AlgebraicGeometry.Space

end
