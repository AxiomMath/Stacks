module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback

/-!
# The cycle of a closed subscheme that decomposes into open and closed pieces

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project and let `ι : A ⟶ X` be a closed subscheme which decomposes as `A = A₁ ⊔ A₂` into two
open and closed pieces, each of which is therefore itself a closed subscheme of `X`. Then

  `[A]_k = [A₁]_k + [A₂]_k`.

The pieces are presented, as everywhere else in
`StacksDraft.AlgebraicGeometry.Chow.ClopenDecomposition`, by *open immersions* `g_j : A_j ⟶ A`
rather than as open subschemes of `A`: in the application the pieces arrive already equipped
with their own closed immersions into `X`, and asking them to be literal open subschemes of `A`
would force a transport along the isomorphism onto the image at every use.

Step 5 of the proof of Stacks 0FH5 cuts a smooth projective `X` by `d` divisors so that
`H_1 ∩ … ∩ H_d = x ⊔ Z`, the chosen closed point together with a residual closed subscheme, and
Steps 7 and 8 then compare the class of the whole intersection — computed by
`Stacks.Chow.CompleteIntersection.mk_eq_mk_of_isIteratedDivisorCut` — with the sum of the classes
of the two pieces. This file is the identity that passage needs. It is used without comment in
the source, and is not the statement of any tag, so nothing here carries a `@[stacks]`
attribute, following
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces`.

Note what is *not* needed: no delta-dimension bound on `A`, and no local finiteness. The whole
argument is coefficientwise, and at a single point of `X` only the generic points of the
irreducible components of `A` lying over that point matter. Each of those lies in exactly one
piece, because the pieces are disjoint and cover; it is the generic point of a component of that
piece, because the generic points of an open subspace are the generic points of the ambient
space lying in it (`Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding`, which needs only
openness); and it has the same multiplicity there, because multiplicity is the length of the
stalk of the subscheme at the point over itself and an open immersion induces an isomorphism on
stalks (`Stacks.Chow.componentMultiplicity_eq_of_isOpenImmersion_ambient`).

## Relation to the cycle of a scheme-theoretic union

`Stacks.Chow.cycleAssociatedToClosedSubscheme_inf` in
`StacksFrontier.AlgebraicGeometry.Chow.UnionFundamentalCycle` is the same additivity for two closed
subschemes of `X` presented by *ideal sheaves on `X`*: `[I ⊓ J]_k = [I]_k + [J]_k` whenever no
point of the scheme-theoretic intersection `I ⊔ J` has delta-dimension `k`. A disjoint union of
two closed subschemes satisfies that side condition vacuously, so in the ideal-sheaf presentation
that result covers this one. What it does not cover is the presentation the complete-intersection
machinery produces: there the subscheme arrives as an arbitrary closed immersion `ι : A ⟶ X`,
isomorphic to the subscheme of an ideal sheaf but not equal to it, and the decomposition is given
inside `A`, by open immersions, with no ideal sheaf on `X` cutting out either piece. Identifying
the ideal sheaf of `A` with the meet of the ideal sheaves of the two pieces would be a longer
detour than the coefficient computation below, which uses no ideal sheaves at all.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_of_mem_range_of_isOpenImmersion` — at the
  image of a generic point of `A` lying in a piece, the cycle of that piece has the same
  coefficient as the cycle of `A`.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range_of_isOpenImmersion`
  — the cycle of a piece has coefficient zero at the image of a point of `A` outside the piece.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion` — the cycle of
  a piece has coefficient zero at a point which is not the image of a generic point of `A` of
  delta-dimension `k`.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces` —
  **`[A]_k = [A₁]_k + [A₂]_k` for a decomposition of the closed subscheme `A` into two open and
  closed pieces.**
* `Stacks.Chow.mk_cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces` — the same
  identity in the Chow group `A_k(X)`, which is the form Steps 7 and 8 of Stacks 0FH5 use.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X A A' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (ι : A ⟶ X) [IsClosedImmersion ι] (ι' : A' ⟶ X) [IsClosedImmersion ι']
  (g : A' ⟶ A) [IsOpenImmersion g]

/-! ### One piece of the decomposition -/

/-- **At the image of a generic point of `A` lying in a piece, the cycle of that piece has the
same coefficient as the cycle of `A`.** The point is the generic point of a component of the
piece by `Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding`, and the two components have the
same multiplicity by `Stacks.Chow.componentMultiplicity_eq_of_isOpenImmersion_ambient`. -/
theorem cycleAssociatedToClosedSubscheme_apply_of_mem_range_of_isOpenImmersion
    (h : g ≫ ι = ι') (k : ℤ) (ξ : genericPoints A)
    (hd : relativeDimension C.dimensionFunction p (ι ξ.1) = k) (a : A') (ha : g a = ξ.1) :
    (cycleAssociatedToClosedSubscheme C p ι' k).1 (ι ξ.1) =
      (cycleAssociatedToClosedSubscheme C p ι k).1 (ι ξ.1) := by
  have hgen : a ∈ genericPoints A' :=
    (mem_genericPoints_iff_of_isOpenEmbedding g.isOpenEmbedding a).mpr (ha ▸ ξ.2)
  have hι' : ι' a = ι ξ.1 := by
    rw [← h, Scheme.Hom.comp_apply, ha]
  rw [← hι', cycleAssociatedToClosedSubscheme_apply C p ι' k ⟨a, hgen⟩ (hι' ▸ hd), hι',
    cycleAssociatedToClosedSubscheme_apply C p ι k ξ hd,
    componentMultiplicity_eq_of_isOpenImmersion_ambient ι ι' g ⟨a, hgen⟩ (ha ▸ ξ.2),
    show (⟨g a, ha ▸ ξ.2⟩ : genericPoints A) = ξ from Subtype.ext ha]

omit [IsOpenImmersion g] in
/-- **The cycle of a piece has coefficient zero at the image of a point of `A` lying outside that
piece.** A generic point of the piece has the same image in `X` as its image in `A`, and `ι` is
injective. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range_of_isOpenImmersion
    (h : g ≫ ι = ι') (k : ℤ) {a : A} (ha : a ∉ Set.range g.base) :
    (cycleAssociatedToClosedSubscheme C p ι' k).1 (ι a) = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C p ι' k (ι a) ?_
  rintro ⟨η, hη, -⟩
  refine ha ⟨η.1, ι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, h, hη]

omit [IsClosedImmersion ι] in
/-- **The cycle of a piece has coefficient zero at a point of `X` which is not the image of a
generic point of `A` of delta-dimension `k`.** A generic point of the piece is a generic point of
`A`, again by `Stacks.Chow.mem_genericPoints_iff_of_isOpenEmbedding`, and it has the same image
in `X`. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion (h : g ≫ ι = ι')
    (k : ℤ) (x : X)
    (hx : ¬ ∃ ξ : genericPoints A,
      ι ξ.1 = x ∧ relativeDimension C.dimensionFunction p x = k) :
    (cycleAssociatedToClosedSubscheme C p ι' k).1 x = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C p ι' k x ?_
  rintro ⟨η, hη, hdim⟩
  refine hx ⟨⟨g η.1, (mem_genericPoints_iff_of_isOpenEmbedding g.isOpenEmbedding η.1).mp η.2⟩,
    ?_, hdim⟩
  rw [← Scheme.Hom.comp_apply, h, hη]

/-! ### Additivity over a decomposition of the closed subscheme -/

/-- **The cycle of a closed subscheme is additive over a decomposition of that subscheme into
open and closed pieces:** if the open immersions `g₁ : A₁ ⟶ A` and `g₂ : A₂ ⟶ A` have disjoint
ranges covering `A`, and sit over closed immersions `ι₁ : A₁ ⟶ X` and `ι₂ : A₂ ⟶ X` through the
closed immersion `ι : A ⟶ X`, then

  `[A]_k = [A₁]_k + [A₂]_k`   in   `Z_k(X)`.

This is the identity Step 5 of the proof of Stacks 0FH5 uses on the complete intersection
`H_1 ∩ … ∩ H_d = x ⊔ Z`, whose class is computed by
`Stacks.Chow.CompleteIntersection.mk_eq_mk_of_isIteratedDivisorCut`.

The proof is coefficientwise. At the image of a generic point `ξ` of `A` of delta-dimension `k`
the left side is the multiplicity of the component of `ξ`; the piece containing `ξ` contributes
exactly that multiplicity, by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_of_mem_range_of_isOpenImmersion`, and the
other piece contributes nothing, because the ranges are disjoint. At every other point all three
coefficients vanish, by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion`. -/
theorem cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces
    {A₁ A₂ : Scheme.{u}} (ι₁ : A₁ ⟶ X) [IsClosedImmersion ι₁] (ι₂ : A₂ ⟶ X)
    [IsClosedImmersion ι₂] (g₁ : A₁ ⟶ A) [IsOpenImmersion g₁] (g₂ : A₂ ⟶ A)
    [IsOpenImmersion g₂] (h₁ : g₁ ≫ ι = ι₁) (h₂ : g₂ ≫ ι = ι₂)
    (hdisjoint : Disjoint (Set.range g₁.base) (Set.range g₂.base))
    (hcover : Set.range g₁.base ∪ Set.range g₂.base = Set.univ) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C p ι k =
      cycleAssociatedToClosedSubscheme C p ι₁ k + cycleAssociatedToClosedSubscheme C p ι₂ k := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (cycleAssociatedToClosedSubscheme C p ι k).1 x =
    (cycleAssociatedToClosedSubscheme C p ι₁ k).1 x +
      (cycleAssociatedToClosedSubscheme C p ι₂ k).1 x
  by_cases hA : ∃ ξ : genericPoints A,
      ι ξ.1 = x ∧ relativeDimension C.dimensionFunction p x = k
  · obtain ⟨ξ, hξ, hd⟩ := hA
    subst hξ
    wlog hmem : ξ.1 ∈ Set.range g₁.base generalizing A₁ A₂ ι₁ ι₂ g₁ g₂ h₁ h₂
    · rw [add_comm]
      exact this ι₂ ι₁ g₂ g₁ h₂ h₁ hdisjoint.symm (by rwa [Set.union_comm])
        ((hcover ▸ Set.mem_univ ξ.1).resolve_left hmem)
    rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range_of_isOpenImmersion
        C p ι ι₂ g₂ h₂ k (fun hc ↦ hdisjoint.le_bot ⟨hmem, hc⟩), add_zero]
    obtain ⟨a, ha⟩ := hmem
    exact (cycleAssociatedToClosedSubscheme_apply_of_mem_range_of_isOpenImmersion C p ι ι₁ g₁
      h₁ k ξ hd a ha).symm
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C p ι k x hA,
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion C p ι ι₁ g₁ h₁ k x hA,
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_isOpenImmersion C p ι ι₂ g₂ h₂ k x hA,
      add_zero]

/-- **The class of the cycle of a closed subscheme is additive over a decomposition of that
subscheme into open and closed pieces**, in the Chow group `A_k(X)`.

This is the form in which Steps 7 and 8 of the proof of Stacks 0FH5 use the identity: the class
of the complete intersection `H_1 ∩ … ∩ H_d`, which
`Stacks.Chow.CompleteIntersection.mk_eq_mk_of_isIteratedDivisorCut` compares with that of another
complete intersection, splits as the sum of the classes of the chosen closed point and of the
residual closed subscheme. It is the image of
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces` under the
quotient map, which is additive. -/
theorem mk_cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces
    {A₁ A₂ : Scheme.{u}} (ι₁ : A₁ ⟶ X) [IsClosedImmersion ι₁] (ι₂ : A₂ ⟶ X)
    [IsClosedImmersion ι₂] (g₁ : A₁ ⟶ A) [IsOpenImmersion g₁] (g₂ : A₂ ⟶ A)
    [IsOpenImmersion g₂] (h₁ : g₁ ≫ ι = ι₁) (h₂ : g₂ ≫ ι = ι₂)
    (hdisjoint : Disjoint (Set.range g₁.base) (Set.range g₂.base))
    (hcover : Set.range g₁.base ∪ Set.range g₂.base = Set.univ) (k : ℤ) :
    QuotientAddGroup.mk' (rationalEquivalences C p k)
        (cycleAssociatedToClosedSubscheme C p ι k) =
      QuotientAddGroup.mk' (rationalEquivalences C p k)
          (cycleAssociatedToClosedSubscheme C p ι₁ k) +
        QuotientAddGroup.mk' (rationalEquivalences C p k)
          (cycleAssociatedToClosedSubscheme C p ι₂ k) := by
  rw [cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces C p ι ι₁ ι₂ g₁ g₂ h₁ h₂
    hdisjoint hcover k, map_add]

end Stacks.Chow

end
