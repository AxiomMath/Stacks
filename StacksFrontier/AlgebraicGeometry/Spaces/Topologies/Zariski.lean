module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback

/-!
# The Zariski topology on algebraic spaces

A *Zariski covering* of an algebraic space over a scheme `S` is a family of open immersions
whose images together contain every point of the target. Such families are the coverings of
the Zariski topology on the category of algebraic spaces over `S`: an isomorphism is a
covering, a covering of each member of a covering composes to a covering, the base change of
a covering along any morphism into its target is a covering, and every Zariski covering is in
particular an étale covering.

## Main definitions

* `AlgebraicGeometry.Space.IsZariskiCovering` says that a family of morphisms of algebraic
  spaces is a Zariski covering of its common target.

## Main results

* `AlgebraicGeometry.Space.isZariskiCovering_of_isIso`: an isomorphism is a Zariski
  covering, viewed as a one-member family.
* `AlgebraicGeometry.Space.isZariskiCovering_comp`: composing a Zariski covering with a
  Zariski covering of each of its members gives a Zariski covering.
* `AlgebraicGeometry.Space.isZariskiCovering_pullback`: the first projections of the fibre
  products of a Zariski covering with a morphism into its target form a Zariski covering of
  the source of that morphism.
* `AlgebraicGeometry.Space.isEtaleCovering_of_isZariskiCovering`: a Zariski covering of
  algebraic spaces is an étale covering.

## Implementation notes

The two clauses of the definition say that every member of the family is an open immersion
in the sense of `AlgebraicGeometry.Space.IsOpenImmersion`, and that the induced maps on
`AlgebraicGeometry.Space.points` are jointly surjective. Joint surjectivity is written in
pointwise form rather than as an equality of sets, which lets a client use a covering by
naming a member and a preimage of a given point.

The definition is stated for families of presheaves on the big fppf site of `S`, so that it
is available before the algebraic-space axioms have been checked; on algebraic spaces it is
the source definition. Only `AlgebraicGeometry.Space.isEtaleCovering_of_isZariskiCovering`
needs those axioms, because they are fields of
`AlgebraicGeometry.Space.IsEtaleCovering`, which it supplies from its hypotheses.

The indexing type of a covering, and of the family of coverings used for the composition,
are arbitrary types in their own universes; the composite family is indexed by the dependent
sum.

The base-change clause is stated for the fibre products of presheaves,
`CategoryTheory.Limits.pullback`, and their first projections, keeping the same index type.
Its open-immersion clause is base-change stability of a relative morphism property, and its
joint-surjectivity clause is Stacks 03H4 in the presheaf form
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`: a point of the new base and a
point of a member of the family with the same image amalgamate to a point of the fibre
product. Neither step uses the algebraic-space axioms, so the clause holds at the same
generality as the definition.

## References

* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
* [Stacks Project, Tag 041H](https://stacks.math.columbia.edu/tag/041H)
* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Space

/-- **Stacks 041G.** A family of open immersions whose images cover every point of the
target. -/
@[stacks 041G]
abbrev IsZariskiCovering (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : Type v) (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Xᵢ i ⟶ X) : Prop :=
  (∀ i, IsOpenImmersion B S hS (f i)) ∧
    (∀ x : points B S hS X,
      ∃ i : I, ∃ y : points B S hS (Xᵢ i),
        pointsMap B S hS (Xᵢ i) (f i) y = x)

/-- **Stacks 041H.** An isomorphism gives a singleton Zariski covering. -/
@[stacks 041H "isomorphism_cover"]
theorem isZariskiCovering_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : X' ⟶ X) [IsIso f] :
    IsZariskiCovering B S hS PUnit (fun _ => X') (fun _ => f) :=
  ⟨fun _ => (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).of_isIso f, fun x =>
    ⟨PUnit.unit, pointsMap B S hS X (inv f) x,
      Quot.inductionOn x (fun p => by
        simp [pointsMap_class, FieldValuedPoint.map, FieldValuedPoint.siteObject])⟩⟩

/-- **Stacks 041H.** Composing a Zariski covering with a covering of each member gives a
Zariski covering. -/
@[stacks 041H "composition_cover"]
theorem isZariskiCovering_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : Type v) (J : I → Type w)
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (Xᵢⱼ : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Xᵢ i ⟶ X)
    (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hf : IsZariskiCovering B S hS I Xᵢ f)
    (hg : ∀ i, IsZariskiCovering B S hS (J i) (Xᵢⱼ i) (g i)) :
    IsZariskiCovering B S hS (Σ i, J i)
      (fun p => Xᵢⱼ p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) := by
  refine ⟨fun ⟨i, j⟩ => ?_, fun x => ?_⟩
  · have _ : ((@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}).inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _ ((hg i).1 j) (hf.1 i)
  · obtain ⟨i, y, hy⟩ := hf.2 x
    obtain ⟨j, z, hz⟩ := (hg i).2 y
    rcases Quot.exists_rep z with ⟨p, rfl⟩
    refine ⟨⟨i, j⟩, p.class B S hS (Xᵢⱼ i j), ?_⟩
    convert (congrArg (pointsMap B S hS (Xᵢ i) (f i)) hz).trans hy using 1
    simp only [pointsMap_class]
    rfl

/-- **Stacks 041H.** Zariski coverings are stable under base change: the first projections of
the fibre products of a Zariski covering `{Xᵢ ⟶ X}` with a morphism `g : X' ⟶ X` form a
Zariski covering of `X'`. -/
@[stacks 041H "base_change_cover"]
theorem isZariskiCovering_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : Type v) (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Xᵢ i ⟶ X) (g : X' ⟶ X)
    (h : IsZariskiCovering B S hS I Xᵢ f) :
    IsZariskiCovering B S hS I (fun i => Limits.pullback g (f i))
      (fun i => Limits.pullback.fst g (f i)) := by
  refine ⟨fun i => ?_, fun x => ?_⟩
  · exact (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (IsPullback.of_hasPullback g (f i)).flip (h.1 i)
  · obtain ⟨i, y, hy⟩ := h.2 (pointsMap B S hS X' g x)
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS
      (IsPullback.of_hasPullback g (f i)) x y hy.symm
    exact ⟨i, w, hw⟩

/-- **Stacks 0DF1.** Every Zariski covering of algebraic spaces is an étale covering. -/
@[stacks 0DF1]
lemma isEtaleCovering_of_isZariskiCovering
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {I : Type v} {Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, Xᵢ i ⟶ X}
    (hX : IsAlgebraicSpace B S hS X)
    (hXᵢ : ∀ i, IsAlgebraicSpace B S hS (Xᵢ i))
    (h : IsZariskiCovering B S hS I Xᵢ f) :
    IsEtaleCovering B S hS Xᵢ f := by
  refine ⟨hX, hXᵢ, ?_, ?_⟩
  · let Q := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    have _ : Q.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have _ : Q.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition Q
    intro i U φ hφ
    exact MorphismProperty.comp_mem Q.presheaf _ _ hφ
      (MorphismProperty.relative_monotone (F := yoneda)
        (fun _ _ _ hg => @AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ _ hg) _ (h.1 i))
  · simpa only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range] using h.2

end AlgebraicGeometry.Space

end
