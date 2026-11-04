module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartIndependence

/-!
# The invariant of Stacks 0DSA does not depend on the presented self-intersection (Stacks 0DS9)

Condition (2) of **Stacks 0DS9** —
`AlgebraicGeometry.Stack.HasLocalRingDimensionAtEveryChart` — quantifies over a 2-fibre product
square `T` for the cospan `(g, g)` of a smooth chart, over an algebraic space `Q` presenting its
apex, over the comparison equivalence of that apex and over the mediating morphism giving the
diagonal. Condition (1) supplies only *some* of each. The file
`StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionChartIndependence.lean` removes the
dependence on the comparison equivalences and on the mediating morphism at a *fixed* square `T`;
this file removes the dependence on the square and on the presenting algebraic space, so that the
whole of the presentation data of the self-intersection drops out of condition (2) and only the
chart `g : V ⟶ 𝒳` and the point `ν` of `V` remain. (The comparison equivalence of the *chart* is
not quantified over by either condition and must not be — see
`StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionChartEquivalenceOrbit.lean`.)

That is what makes the pullback squares of
`StacksFrontier/AlgebraicGeometry/Stacks/RefinedChartSelfIntersectionPullback.lean` usable: they are
stated at the canonical 2-fibre product, and without the transport below an argument run there
would prove something strictly weaker than the `∀` of condition (2).

## Main results

* `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_comp_selfIntersectionSourceMap`: the
  diagonal `e : V ⟶ R` is a section of the source morphism `s : R ⟶ V`.
* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_diagonal_iff`: consequently the
  invariant of Stacks 0DSA read at the diagonal image of `ν` is
  `2 dim(𝒪_{V,ν}) - dim(𝒪_{R, e(ν)})` with the *chart* dimension taken at `ν` itself — the
  source morphism has disappeared from it.
* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`: the
  invariant at the diagonal image of a point is unchanged when the 2-fibre product square, the
  presenting algebraic space, its comparison equivalence and the mediating morphism are all
  replaced by others — at the *same* point of the chart, with no transport needed.
* `AlgebraicGeometry.Stack.forall_hasRelationLocalRingDimension_transport_presentation`: the
  previous result combined with
  `AlgebraicGeometry.Stack.forall_hasRelationLocalRingDimension_transport_equivalence`, so that
  the comparison equivalence of the chart moves too — at the price of the `∀` over the point,
  which is what absorbs the transport a change of that equivalence forces. A consumer that has
  to move the chart's equivalence at ONE point needs
  `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence` and the
  transported point.

## Implementation notes

**Why the point does not move here, although it does for a change of the chart's comparison
equivalence.** The predicate depends on the presentation data through the source morphism
`AlgebraicGeometry.Stack.selfIntersectionSourceMap` and through the diagonal
`AlgebraicGeometry.Stack.selfIntersectionDiagonalMap`. Since the diagonal is a section of the
source morphism, the chart dimension entering the invariant at the diagonal image of `ν` is the
dimension at `ν` itself and the source morphism drops out; what is left is the dimension of the
relation at the diagonal image. Replacing `T` by `T'` conjugates the diagonal by the comparison
morphism of the two representing presheaves, which is an *isomorphism* `Q ≅ Q'` — it changes the
point of the relation but not the point of the chart, so no transport of `ν` appears. A change of
the chart's comparison equivalence `eV`, by contrast, moves the points of `yoneda.obj V`
themselves, which is why
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence` has to carry `ν`
along and why the combined statement is given only in the `∀`-quantified form.

The comparison morphism `Q ⟶ Q'` is the morphism of representing presheaves of **Stacks 04SW**
attached to the mediating 1-morphism `T.pt ⟶ T'.pt` supplied by terminality of `T'`, and it is an
isomorphism because the mediating 1-morphism the other way is a quasi-inverse: both composites
are 2-isomorphic to the identity by terminality
(`CategoryTheory.Bicategory.twoFibreProductPreHom_rel`), and Stacks 04SW is functorial
(`AlgebraicGeometry.Stack.representingMap_comp`) and constant on 2-isomorphism classes
(`AlgebraicGeometry.Stack.representingMap_congr_twoIso`).

Terminality of *both* squares is needed and is used symmetrically: `hT'` to compare the diagonals
and to produce one of the two mediating 1-morphisms, `hT` for the other.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
  (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (T T' : Bicategory.TwoCommSq g g)
  (Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eV eV' : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS V).val.val.p
    (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
  (eQ' : StacksRepresentableCFG.EquivalenceOver
    T'.pt.val.val.p (presheafOfCategories (Q' ⋙ typeToCat)).p)

/-! ### The diagonal is a section of the source morphism -/

/-- If `a ≫ c` is 2-isomorphic to the identity, the induced morphisms of representing presheaves
compose to the identity. -/
private theorem representingMap_comp_eq_id_of_iso
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ ℬ) (c : ℬ ⟶ 𝒜) (η : a ≫ c ≅ 𝟙 𝒜) :
    representingMap B S hS 𝒜 ℬ F G eF eG a ≫ representingMap B S hS ℬ 𝒜 G F eG eF c = 𝟙 F := by
  rw [← representingMap_comp, representingMap_congr_twoIso B S hS F F eF eF η, representingMap_id]

/-- **The diagonal `e : V ⟶ R` of a presented self-intersection is a section of the source
morphism `s : R ⟶ V`.** The second leg of the tautological square
`AlgebraicGeometry.Stack.selfIntersectionDiagonalSquare` is the identity, so the comparison
2-cell `δ.isoSnd` of a morphism `δ` of 2-commutative squares into `T` identifies
`δ.hom ≫ T.snd` with the identity; functoriality of **Stacks 04SW** and its being constant on
2-isomorphism classes then give the identity on representing presheaves.

Nothing about `T` being a 2-fibre product is used: only the comparison 2-cell carried by `δ`. -/
theorem selfIntersectionDiagonalMap_comp_selfIntersectionSourceMap
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T) :
    selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ≫
        selfIntersectionSourceMap B S hS V g T Q eV eQ = 𝟙 (yoneda.obj V) :=
  representingMap_comp_eq_id_of_iso B S hS (yoneda.obj V) Q eV eQ δ.hom.hom T.snd.hom
    (Bicategory.InducedBicategory.isoHom
      (f := δ.hom ≫ T.snd) (g := 𝟙 (schemeStack.{u, w} B S hS V)) δ.isoSnd.symm)

/-- The image of the diagonal image of a point of the chart under the source morphism is the
point itself: `s(e(ν)) = ν`, by
`AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_comp_selfIntersectionSourceMap`. -/
theorem pointsMap_selfIntersectionSourceMap_diagonal
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (ν : Space.points B S hS (yoneda.obj V)) :
    Space.pointsMap B S hS Q (selfIntersectionSourceMap B S hS V g T Q eV eQ)
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) = ν := by
  simpa only [Space.pointsMap_comp_apply, Space.pointsMap_id_apply] using
    congrArg (fun k => Space.pointsMap B S hS (yoneda.obj V) k ν)
      (selfIntersectionDiagonalMap_comp_selfIntersectionSourceMap B S hS V g T Q eV eQ δ)

/-- **The invariant of Stacks 0DSA at the diagonal image of a point of the chart is
`2 dim(𝒪_{V,ν}) - dim(𝒪_{R, e(ν)})`**, with the chart dimension read at `ν` itself rather than
at the image of `e(ν)` under the source morphism.

`AlgebraicGeometry.Stack.HasRelationLocalRingDimension` is stated at an arbitrary point of the
relation and so has to name the source morphism; at a point of the diagonal the source morphism
drops out, because the diagonal is a section of it. This is the shape in which the dependence of
the invariant on the presentation data can be seen: all of it is in the single term
`dim(𝒪_{R, e(ν)})`. -/
theorem hasRelationLocalRingDimension_diagonal_iff
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    HasRelationLocalRingDimension B S hS V g T Q eV eQ
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d ↔
      ∃ m n : ℕ, Space.localRingDimension B S hS ν = (m : ℕ∞) ∧
        Space.localRingDimension B S hS
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) = (n : ℕ∞) ∧
          2 * (m : ℤ) - (n : ℤ) = d := by
  rw [HasRelationLocalRingDimension,
    pointsMap_selfIntersectionSourceMap_diagonal B S hS V g T Q eV eQ δ ν]

/-! ### Independence of the 2-fibre product square and of the presenting algebraic space -/

section TransportSquare

variable (hT : Bicategory.IsTwoFibreProduct T) (hT' : Bicategory.IsTwoFibreProduct T')

include hT in
/-- **The comparison morphism of the representing presheaves of two 2-fibre products of one
cospan is an isomorphism.** Terminality of each square supplies a mediating morphism of
2-commutative squares into the other, and the two composites are 2-isomorphic to the identity;
Stacks 04SW is functorial and constant on 2-isomorphism classes, so the two induced morphisms of
representing presheaves are mutually inverse. -/
theorem isIso_representingMap_twoFibreProductPreHom :
    IsIso (representingMap B S hS T.pt.val T'.pt.val Q Q' eQ eQ'
      (Bicategory.twoFibreProductPreHom hT' T).hom.hom) := by
  classical
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hT
    ((Bicategory.twoFibreProductPreHom hT' T).comp (Bicategory.twoFibreProductPreHom hT T'))
    (Bicategory.TwoCommSq.PreHom.id T)
  obtain ⟨θ', -, -⟩ := Bicategory.twoFibreProductPreHom_rel hT'
    ((Bicategory.twoFibreProductPreHom hT T').comp (Bicategory.twoFibreProductPreHom hT' T))
    (Bicategory.TwoCommSq.PreHom.id T')
  refine ⟨representingMap B S hS T'.pt.val T.pt.val Q' Q eQ' eQ
    (Bicategory.twoFibreProductPreHom hT T').hom.hom, ?_, ?_⟩
  · exact representingMap_comp_eq_id_of_iso B S hS Q Q' eQ eQ' _ _
      (Bicategory.InducedBicategory.isoHom
        (f := (Bicategory.twoFibreProductPreHom hT' T).hom ≫
          (Bicategory.twoFibreProductPreHom hT T').hom)
        (g := 𝟙 T.pt) θ)
  · exact representingMap_comp_eq_id_of_iso B S hS Q' Q eQ' eQ _ _
      (Bicategory.InducedBicategory.isoHom
        (f := (Bicategory.twoFibreProductPreHom hT T').hom ≫
          (Bicategory.twoFibreProductPreHom hT' T).hom)
        (g := 𝟙 T'.pt) θ')

/-- **The diagonal of a second presented self-intersection is the first one followed by the
comparison morphism.** The mediating morphism `δ'` into `T'` may be replaced by the composite of
`δ` with the comparison morphism `T.pt ⟶ T'.pt`, by
`AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_congr_preHom` — which is where terminality
of `T'` is used — and Stacks 04SW is functorial. -/
theorem selfIntersectionDiagonalMap_congr_twoFibreProduct
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T') :
    selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ' δ' =
      selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ≫
        representingMap B S hS T.pt.val T'.pt.val Q Q' eQ eQ'
          (Bicategory.twoFibreProductPreHom hT' T).hom.hom :=
  calc selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ' δ'
      = selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ'
          (δ.comp (Bicategory.twoFibreProductPreHom hT' T)) :=
        selfIntersectionDiagonalMap_congr_preHom B S hS V g T' Q' eV eQ' hT' δ'
          (δ.comp (Bicategory.twoFibreProductPreHom hT' T))
    _ = selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ≫
          representingMap B S hS T.pt.val T'.pt.val Q Q' eQ eQ'
            (Bicategory.twoFibreProductPreHom hT' T).hom.hom :=
        representingMap_comp B S hS (yoneda.obj V) Q Q' eV eQ eQ' δ.hom.hom _

include hT hT' in
/-- **The invariant of Stacks 0DSA does not depend on the presented self-intersection.** Let a
smooth chart `g : V ⟶ 𝒳` be given, and let its self-intersection be presented twice over — by a
2-fibre product square `T` for the cospan `(g, g)`, an algebraic space `Q` presenting its apex
through `eQ` and a mediating morphism `δ`, and by `T'`, `Q'`, `eQ'`, `δ'`. Then at one and the
same point `ν` of the chart the two presentations measure the invariant to be the same integer.

The point of the chart does *not* move: the comparison of the two presentations is an
isomorphism `Q ≅ Q'` of the two representing presheaves of the relation, which carries the
diagonal image of `ν` for the first presentation to the diagonal image of `ν` for the second and
leaves `ν` alone. The chart dimension entering the invariant is read at `ν` itself
(`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_diagonal_iff`), so it is untouched, and
the dimension of the relation is unchanged under an isomorphism of presheaves
(`AlgebraicGeometry.Space.localRingDimension_pointsMap_of_isIso`).

This is one half of the presentation quantifier of condition (2) of **Stacks 0DS9**; the other
half, the comparison equivalence of the chart, is
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence`, and the two are
combined in
`AlgebraicGeometry.Stack.forall_hasRelationLocalRingDimension_transport_presentation`. -/
@[stacks 0DS9
  "the invariant of the two conditions does not depend on the presented self-intersection"]
theorem hasRelationLocalRingDimension_transport_twoFibreProduct
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T')
    (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    HasRelationLocalRingDimension B S hS V g T Q eV eQ
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d ↔
      HasRelationLocalRingDimension B S hS V g T' Q' eV eQ'
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ' δ') ν) d := by
  have hiso := isIso_representingMap_twoFibreProductPreHom B S hS V g T T' Q Q' eQ eQ' hT hT'
  have hpt : Space.pointsMap B S hS (yoneda.obj V)
        (selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ' δ') ν =
      Space.pointsMap B S hS Q
        (representingMap B S hS T.pt.val T'.pt.val Q Q' eQ eQ'
          (Bicategory.twoFibreProductPreHom hT' T).hom.hom)
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) := by
    simpa only [Space.pointsMap_comp_apply] using
      congrArg (fun k => Space.pointsMap B S hS (yoneda.obj V) k ν)
        (selfIntersectionDiagonalMap_congr_twoFibreProduct B S hS V g T T' Q Q' eV eQ eQ'
          hT' δ δ')
  have hdim : Space.localRingDimension B S hS
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T' Q' eV eQ' δ') ν) =
      Space.localRingDimension B S hS
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) := by
    rw [hpt]
    exact Space.localRingDimension_pointsMap_of_isIso B S hS _ _
  rw [hasRelationLocalRingDimension_diagonal_iff B S hS V g T Q eV eQ δ ν d,
    hasRelationLocalRingDimension_diagonal_iff B S hS V g T' Q' eV eQ' δ' ν d, hdim]

include hT hT' in
/-- **The invariant read at every point of the chart does not depend on any of the comparison
data.** All of the 2-fibre product square `T`, the presenting algebraic space `Q` with its
comparison equivalence `eQ`, the comparison equivalence `eV` of the chart, and the mediating
morphism `δ` may be replaced at once.

It is `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`, which
moves `T`, `Q`, `eQ` and `δ` at a fixed point of the chart, composed with
`AlgebraicGeometry.Stack.forall_hasRelationLocalRingDimension_transport_equivalence`, which moves
`eV` and absorbs the transport of the point that a change of `eV` forces. The `∀` over `ν` is
therefore not a convenience: at a fixed point of the chart the statement with `eV` moved is
false, the comparison automorphism of `yoneda.obj V` being nontrivial in general — which is why
the conditions of Stacks 0DS9 fix that equivalence to the canonical one instead of quantifying
over it, and why only the quantifiers over `T`, `Q`, `eQ` and `δ` that they do carry are
discharged by the previous theorem. -/
theorem forall_hasRelationLocalRingDimension_transport_presentation
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T')
    (d : ℤ) :
    (∀ ν : Space.points B S hS (yoneda.obj V),
        HasRelationLocalRingDimension B S hS V g T Q eV eQ
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d) ↔
      ∀ ν : Space.points B S hS (yoneda.obj V),
        HasRelationLocalRingDimension B S hS V g T' Q' eV' eQ'
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T' Q' eV' eQ' δ') ν) d :=
  (forall_hasRelationLocalRingDimension_transport_equivalence B S hS V g T Q eV eV' eQ eQ
    hT δ δ d).trans
    (forall_congr' fun ν =>
      hasRelationLocalRingDimension_transport_twoFibreProduct B S hS V g T T' Q Q' eV' eQ eQ'
        hT hT' δ δ' ν d)

end TransportSquare

end AlgebraicGeometry.Stack

end
