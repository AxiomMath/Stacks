module

public import StacksFrontier.AlgebraicGeometry.Gluing.Punctured
public import StacksFrontier.AlgebraicGeometry.Assembly.Iterate

/-!
# The cover the proof of Tag 0E8Q glues along, and that it satisfies the iteration's hypotheses

Let `s : I → S` be a finite family of closed points, `V` the open complement of the family, and
let `W i` be an open neighbourhood of `s i` **avoiding every other member of the family** — the
neighbourhood produced by
`AlgebraicGeometry.exists_affineOpenNhds_model_avoiding`.  Then

* `V` together with the `W i` covers `S`: a point outside `V` is one of the `s i`, and `s i ∈ W i`;
* any two distinct members of the family of neighbourhoods meet inside `V`: a point of
  `W i ⊓ W j` which were some `s k` would have to be avoided by `W i` (if `k ≠ i`) or by `W j`
  (as `k = i` and `i ≠ j`).

Those are exactly the two hypotheses of
`AlgebraicGeometry.exists_finitePresentation_isPullback_glueFamily`, so the whole gluing side of
Tag 0E8Q's `equivalence` label is discharged by the avoidance that
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)'s residue item (3) supplies, with no
further geometry.

Note that the second condition is where framing the gluing as a *one-shot*
cover `{V, W₁, …, Wₙ}` of `S` goes wrong: `V ⊔ W i = ⊤` is false as soon as the family has more
than one member, because `s j` with `j ≠ i` lies in neither side.  It is the pairwise condition,
not a one-shot cover identity, that makes the iteration run — and
`AlgebraicGeometry.sup_complementOfClosedPoints_iSup_eq_top` is the identity that *is* true, with
the join taken over the whole family.

## Main results

* `AlgebraicGeometry.sup_complementOfClosedPoints_iSup_eq_top`
* `AlgebraicGeometry.inf_le_complementOfClosedPoints_of_avoiding`
* `AlgebraicGeometry.exists_finitePresentation_isPullback_glueAvoiding`: the gluing of a family of
  charts over neighbourhoods of the closed points onto a chart over the open complement, which is
  the form the essential-surjectivity argument consumes.

## Implementation notes

No `@[stacks]` attribute is attached: Tag 0E8Q's `equivalence` label has the single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set, so no lemma here can earn
part of it, and Tag 0BPA is not carded in this repository.

## References

* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {I : Type u} [Finite I] {s : I → S} {hs : ∀ i, s i ∈ closedPoints S}
  (W : I → S.Opens)

/-- **The open complement of the family, together with one neighbourhood of each member, covers
the scheme.**  A point outside the complement is one of the points of the family, and that one's
neighbourhood contains it. -/
theorem sup_complementOfClosedPoints_iSup_eq_top (hW : ∀ i, s i ∈ W i) :
    complementOfClosedPoints s hs ⊔ ⨆ i, W i = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  by_cases hxV : x ∈ complementOfClosedPoints s hs
  · exact Or.inl hxV
  · refine Or.inr ?_
    obtain ⟨i, hi⟩ :=
      not_forall.mp (show ¬ ∀ i, x ∈ ({s i}ᶜ : Set S) from fun h ↦ hxV (Set.mem_iInter.mpr h))
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [show x = s i from not_not.mp hi]
    exact hW i

/-- **Two neighbourhoods from the family meet inside the open complement.**  This is the pairwise
condition the iteration of
`AlgebraicGeometry.exists_finitePresentation_isPullback_glueFamily` runs on, and it is exactly
the avoidance clause of Tag 0BPA's residue item (3). -/
theorem inf_le_complementOfClosedPoints_of_avoiding
    (havoid : ∀ i j, j ≠ i → s j ∉ W i) {i j : I} (hij : i ≠ j) :
    W i ⊓ W j ≤ complementOfClosedPoints s hs := by
  refine fun x hx ↦ Set.mem_iInter.mpr fun k ↦ fun (hk : x ∈ ({s k} : Set S)) ↦ ?_
  by_cases hki : k = i
  · exact havoid j i hij (hki ▸ hk ▸ hx.2)
  · exact havoid i k hki (hk ▸ hx.1)

/-- **The gluing step of Tag 0E8Q's essential surjectivity, as a statement about charts.**  A
chart of finite presentation over the open complement of the family, one over each of the
avoiding neighbourhoods, and an isomorphism of their base changes to each overlap, glue to a
scheme of finite presentation over `S` restricting to all of them.

This is `AlgebraicGeometry.exists_finitePresentation_isPullback_glueFamily` with the two lattice
hypotheses discharged by the avoidance.  What it does *not* supply is the overlap isomorphisms:
those are the content of Tag 0BPA's items (1), (2) and the descent along the punctured inverse
limit. -/
theorem exists_finitePresentation_isPullback_glueAvoiding (hW : ∀ i, s i ∈ W i)
    (havoid : ∀ i j, j ≠ i → s j ∉ W i) {A : Scheme.{u}}
    {a : A ⟶ ((complementOfClosedPoints s hs : S.Opens) : Scheme.{u})}
    (ha : FinitePresentation a) {Z : I → Scheme.{u}}
    {z : ∀ i, Z i ⟶ ((W i : S.Opens) : Scheme.{u})} (hz : ∀ i, FinitePresentation (z i))
    (φ : ∀ i, (Over.pullback (S.homOfLE
          (inf_le_left : complementOfClosedPoints s hs ⊓ W i ≤
            complementOfClosedPoints s hs))).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE
        (inf_le_right : complementOfClosedPoints s hs ⊓ W i ≤ W i))).obj (Over.mk (z i))) :
    ∃ (X : Scheme.{u}) (q : X ⟶ S) (jA : A ⟶ X), FinitePresentation q ∧
      IsPullback a jA (complementOfClosedPoints s hs).ι q ∧
        ∀ i, ∃ jZ : Z i ⟶ X, IsPullback (z i) jZ (W i).ι q ∧
          pullback.fst a (S.homOfLE
              (inf_le_left : complementOfClosedPoints s hs ⊓ W i ≤
                complementOfClosedPoints s hs)) ≫ jA =
            (φ i).hom.left ≫
              pullback.fst (z i) (S.homOfLE
                (inf_le_right : complementOfClosedPoints s hs ⊓ W i ≤ W i)) ≫ jZ :=
  exists_finitePresentation_isPullback_glueFamily
    (sup_complementOfClosedPoints_iSup_eq_top W hW)
    (fun _ _ hij ↦ inf_le_complementOfClosedPoints_of_avoiding W havoid hij) ha hz φ

end AlgebraicGeometry

end
