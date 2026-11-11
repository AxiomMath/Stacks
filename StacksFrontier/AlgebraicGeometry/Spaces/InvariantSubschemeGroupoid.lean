module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Defs

/-!
# Invariance under a groupoid scheme and invariance under an atlas relation

A subscheme of the object scheme of a groupoid scheme is invariant when its two pullbacks
along the source and the target map agree as subobjects of the arrow scheme; this is
`Stacks.Groupoids.IsInvariantMonomorphism`, the condition imposed on a monomorphism by
Stacks 03BC, part (4). A subscheme of a surjective
étale chart of an algebraic space is invariant when its two pullbacks along the two legs of
the kernel pair of that chart agree. The two conditions are the same condition: the groupoid
canonically extending the relation of a presentation has that relation's two legs as its
source and target maps, and the relation of a presentation is isomorphic, compatibly with
both legs, to the kernel pair of its atlas.

This file proves that agreement and transports the bijection of Stacks 07TW across it, so
that the correspondence between invariant locally closed subschemes of the presenting scheme
and locally closed subspaces of the presented algebraic space can be read with invariance
taken in the groupoid sense.

## Main results

* `AlgebraicGeometry.ExtendsRelation.pullback_obj_eq_iff`: invariance under a groupoid scheme
  extending a pre-relation is invariance under the two maps of that pre-relation.
* `AlgebraicGeometry.Space.Presentation.exists_iso_atlasRelation`: the presenting relation of
  a presentation is isomorphic, compatibly with both legs, to the kernel pair of its atlas.
* `AlgebraicGeometry.Space.Presentation.isInvariantSubscheme_iff`: invariance under the kernel
  pair of the atlas is invariance under the two legs of the presenting relation.
* `AlgebraicGeometry.Space.Presentation.isInvariantSubscheme_iff_of_extendsRelation`: the
  comparison itself, identifying
  `AlgebraicGeometry.Space.IsInvariantSubscheme` with
  `Stacks.Groupoids.IsInvariantMonomorphism`, the invariance condition of Stacks 03BC
  part (4), for any groupoid scheme extending the relation of the presentation.
* `AlgebraicGeometry.Space.Presentation.invariantLocallyClosedSubschemeEquivOfExtendsRelation`,
  `AlgebraicGeometry.Space.Presentation.closed_iff_of_extendsRelation` and
  `AlgebraicGeometry.Space.Presentation.open_iff_of_extendsRelation`: the three statements of
  Stacks 07TW with invariance in the groupoid sense.

## Implementation notes

The schemes of objects and arrows of a groupoid scheme extending a pre-relation are only
propositionally the schemes of that relation, so the identification of the object schemes is
carried explicitly: the comparison results take an argument `hobj` for it, whose only proof is
`congrArg CategoryTheory.Over.left hG.objects_eq`. Taking it as an argument rather than
building it from `hG` lets the statement be read at the object scheme of the presenting
chart, which is the form in which the subobject to be tested is given.

The two legs of a presentation are not the two projections of the kernel pair of its atlas on
the nose, only up to the canonical isomorphism between two pullbacks of one cospan. Pulling a
subobject back along an isomorphism is injective on subobjects, so invariance is insensitive
to that isomorphism; this is why no compatibility beyond `isPullback` is needed.

The last three results are stated for an arbitrary groupoid scheme extending the relation
rather than for the canonical one, and so apply in particular to
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`. The effective-descent input of
`AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv` — Stacks 02W8 for immersions, in
the form Stacks 03I2 consumes — is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`, so the three
results below need no input beyond the presentation and the extending groupoid scheme. They are
the three assertions of Stacks 07TW in the shape of the source: an étale equivalence relation
`R` on `U`, its quotient `X = U/R`, and invariance in the sense of Stacks 03BC part (4). The
general chart form of the same three statements is tagged in
`StacksFrontier/AlgebraicGeometry/Descent/ImmersionEtaleDescent.lean`.

## References

* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Pulling a subobject back along an isomorphism is injective. -/
private theorem pullback_obj_injective_of_isIso {C : Type*} [Category C] [HasPullbacks C]
    {A A' : C} (m : A ⟶ A') [IsIso m] {x y : Subobject A'}
    (h : (Subobject.pullback m).obj x = (Subobject.pullback m).obj y) : x = y := by
  have hx : (Subobject.pullback (inv m ≫ m)).obj x =
      (Subobject.pullback (inv m)).obj ((Subobject.pullback m).obj x) :=
    Subobject.pullback_comp _ _ _
  have hy : (Subobject.pullback (inv m ≫ m)).obj y =
      (Subobject.pullback (inv m)).obj ((Subobject.pullback m).obj y) :=
    Subobject.pullback_comp _ _ _
  rw [IsIso.inv_hom_id, Subobject.pullback_id] at hx hy
  rw [hx, hy, h]

namespace ExtendsRelation

variable {S : Scheme.{u}} {R U : Over S}

/-- A subscheme of the object scheme of a groupoid scheme extending a pre-relation is
invariant under the groupoid, in the sense of Stacks 03BC part (4), exactly when its two
pullbacks along the target and the source map of that pre-relation agree.

The hypothesis `hobj` is the identification of object schemes supplied by `hG`; its only
proof is `congrArg CategoryTheory.Over.left hG.objects_eq`. -/
theorem pullback_obj_eq_iff {j : PreRelation R U} {G : GroupoidScheme S}
    (hG : ExtendsRelation j G) (hobj : G.objects.left = U.left) (Z : Subobject U.left) :
    IsInvariantMonomorphism G (Z.arrow ≫ eqToHom hobj.symm) ↔
      ((Subobject.pullback j.target.left).obj Z =
        (Subobject.pullback j.source.left).obj Z) := by
  change ((Subobject.pullback G.target.left).obj
        (Subobject.mk (Z.arrow ≫ eqToHom hobj.symm)) =
      (Subobject.pullback G.source.left).obj
        (Subobject.mk (Z.arrow ≫ eqToHom hobj.symm))) ↔ _
  obtain ⟨ho, ha, hsrc, htgt⟩ := hG
  cases ha
  cases ho
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Subobject.mk_arrow]
    at hsrc htgt ⊢
  rw [hsrc, htgt]

end ExtendsRelation

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The presenting relation of a presentation is isomorphic to the kernel pair of its atlas,
compatibly with both legs. -/
theorem Presentation.exists_iso_atlasRelation (P : Presentation B S hS X hX) :
    ∃ m : P.R ≅ atlasRelation B S hS P.surjective,
      m.hom ≫ atlasRelationTarget B S hS P.surjective = P.target ∧
        m.hom ≫ atlasRelationSource B S hS P.surjective = P.source := by
  have hmap : yoneda.map (atlasRelationTarget B S hS P.surjective) =
      P.surjective.rep.fst P.toSpace := Functor.map_preimage _ _
  have hker : IsPullback (yoneda.map (atlasRelationTarget B S hS P.surjective))
      (yoneda.map (atlasRelationSource B S hS P.surjective)) P.toSpace P.toSpace := by
    rw [hmap]
    exact P.surjective.rep.isPullback P.toSpace
  refine ⟨yoneda.preimageIso (P.isPullback.isoIsPullback _ _ hker), ?_, ?_⟩ <;>
    apply yoneda.map_injective <;>
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
  exacts [P.isPullback.isoIsPullback_hom_fst _ _ hker, P.isPullback.isoIsPullback_hom_snd _ _ hker]

/-- A subscheme of the presenting scheme of a presentation is invariant under the kernel pair
of its atlas exactly when its two pullbacks along the two legs of the presenting relation
agree. -/
theorem Presentation.isInvariantSubscheme_iff (P : Presentation B S hS X hX)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U)) :
    IsInvariantSubscheme B S hS P.surjective Z ↔
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map P.target)).obj Z =
        (Subobject.pullback ((BigFppfOver.toScheme B S hS).map P.source)).obj Z := by
  obtain ⟨m, ht, hsrc⟩ := P.exists_iso_atlasRelation B S hS
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map m.hom) :=
    ((BigFppfOver.toScheme B S hS).mapIso m).isIso_hom
  rw [← ht, ← hsrc, Functor.map_comp, Functor.map_comp, Subobject.pullback_comp,
    Subobject.pullback_comp]
  exact ⟨congrArg _, pullback_obj_injective_of_isIso _⟩

/-- Invariance of a subscheme of the presenting scheme under the kernel pair of the atlas,
which is `AlgebraicGeometry.Space.IsInvariantSubscheme`, is invariance under any groupoid
scheme extending the presenting relation, which is the condition of Stacks 03BC part (4).

The hypothesis `hobj` is the identification of object schemes supplied by `hG`; its only
proof is `congrArg CategoryTheory.Over.left hG.objects_eq`. -/
theorem Presentation.isInvariantSubscheme_iff_of_extendsRelation
    (P : Presentation B S hS X hX) {G : GroupoidScheme S}
    (hG : ExtendsRelation (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) G)
    (hobj : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U)) :
    IsInvariantMonomorphism G (Z.arrow ≫ eqToHom hobj.symm) ↔
      IsInvariantSubscheme B S hS P.surjective Z := by
  refine Iff.trans (hG.pullback_obj_eq_iff hobj Z) ?_
  rw [P.isInvariantSubscheme_iff B S hS Z, PreRelation.target, PreRelation.source,
    prod.lift_fst, prod.lift_snd]
  rfl

/-- **Stacks 07TW**, the canonical bijection, with invariance of the subschemes of the
presenting scheme taken in the groupoid sense of Stacks 03BC part (4) against any groupoid
scheme extending the presenting relation.

Effective descent of immersions along the surjective étale morphisms of the site, which is
Stacks 02W8 in the form Stacks 03I2 consumes, is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`. -/
@[stacks 07TW "the canonical bijection, with invariance taken in the groupoid sense"]
noncomputable def Presentation.invariantLocallyClosedSubschemeEquivOfExtendsRelation
    (P : Presentation B S hS X hX) {G : GroupoidScheme S}
    (hG : ExtendsRelation (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) G)
    (hobj : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U) :
    {e : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
            AlgebraicGeometry.IsImmersion Z.arrow ∧
              IsInvariantMonomorphism G (Z.arrow ≫ eqToHom hobj.symm)} ≃
          LocallyClosedQuotientSubspace B S hS (X := X) //
      ∀ Z, ((e Z).1.preimage P.toSpace) = subschemePoints B S hS Z.1} := by
  refine ⟨(Equiv.subtypeEquivRight (fun Z =>
      and_congr_right' (P.isInvariantSubscheme_iff_of_extendsRelation B S hS hG hobj Z))).trans
    (invariantLocallyClosedSubschemeEquiv B S hS P.surjective P.etale
      (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX).1, fun Z => ?_⟩
  exact (invariantLocallyClosedSubschemeEquiv B S hS P.surjective P.etale
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX).2 _

/-- **Stacks 07TW**, closedness, with invariance taken in the groupoid sense: the subspace of
the presented algebraic space corresponding to an invariant subscheme of the presenting scheme
is closed exactly when that subscheme is closed. -/
@[stacks 07TW "closedness, with invariance taken in the groupoid sense"]
theorem Presentation.closed_iff_of_extendsRelation
    (P : Presentation B S hS X hX) {G : GroupoidScheme S}
    (hG : ExtendsRelation (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) G)
    (hobj : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U)
    (Z : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
      AlgebraicGeometry.IsImmersion Z.arrow ∧
        IsInvariantMonomorphism G (Z.arrow ≫ eqToHom hobj.symm)}) :
    IsClosedSubspace B S hS
        ((P.invariantLocallyClosedSubschemeEquivOfExtendsRelation B S hS hG hobj).1 Z).1 ↔
      AlgebraicGeometry.IsClosedImmersion Z.1.arrow :=
  closed_iff B S hS P.surjective P.etale
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX _

/-- **Stacks 07TW**, openness, with invariance taken in the groupoid sense: the subspace of
the presented algebraic space corresponding to an invariant subscheme of the presenting scheme
is open exactly when that subscheme is open. -/
@[stacks 07TW "openness, with invariance taken in the groupoid sense"]
theorem Presentation.open_iff_of_extendsRelation
    (P : Presentation B S hS X hX) {G : GroupoidScheme S}
    (hG : ExtendsRelation (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) G)
    (hobj : G.objects.left = (BigFppfOver.toScheme B S hS).obj P.U)
    (Z : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
      AlgebraicGeometry.IsImmersion Z.arrow ∧
        IsInvariantMonomorphism G (Z.arrow ≫ eqToHom hobj.symm)}) :
    IsOpenSubspace B S hS
        ((P.invariantLocallyClosedSubschemeEquivOfExtendsRelation B S hS hG hobj).1 Z).1 ↔
      AlgebraicGeometry.IsOpenImmersion Z.1.arrow :=
  open_iff B S hS P.surjective P.etale
    (isEffectiveDescentAlongSurjectiveEtale_isImmersion B S hS) hX _

end Space

end AlgebraicGeometry

end
