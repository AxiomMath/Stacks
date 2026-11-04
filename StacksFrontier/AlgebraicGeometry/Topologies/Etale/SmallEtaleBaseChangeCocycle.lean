module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The cocycle for small étale base change (Stacks 021J)

`AlgebraicGeometry.smallEtaleBaseChange_compIso` compares base-changing an étale scheme along
`g : Y ⟶ Z` and then along `f : X ⟶ Y` with base-changing it along the composite, and
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` is the same comparison for a chosen
factorization.  This file proves that those comparisons satisfy the **cocycle condition** over a
triple of morphisms: contracting the last two base changes and then the result agrees with
contracting the first two and then the result.

Nothing here is a limit construction.  A morphism of the small étale category of `W` into a base
change along `g : W ⟶ Z` is determined by its composite with the projection to the object
upstairs: the small étale category is a full subcategory of `Over (B.obj W)`, so such a morphism
is a morphism of slices, its composite with the *other* projection is its own structure morphism
by `CategoryTheory.Over.w`, and `CategoryTheory.Limits.pullback.hom_ext` then leaves only the
first projection.  That is
`AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange`.  Both routes round the
cocycle compose to the same string of three projections, by
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst` applied twice on each side,
so the cocycle holds for the only available reason.

## Implementation notes

`B.Scheme` is itself a full subcategory of `Scheme`, and its composition reaches the goal by an
instance path that is definitionally but not syntactically the one
`CategoryTheory.Category.assoc` and `CategoryTheory.Limits.pullback.fst` carry in the statements
being rewritten with.  So neither `rw` nor `simp` re-associates the goal here.  Two measures
answer that, and both are needed: the projection lemmas are restated **with a trailing factor**,
in the right-associated shape the goal actually has, so that no re-association is asked for at
the point of use; and each such restatement, and the final step of the cocycle, is proved in
*term* mode, where `CategoryTheory.Category.assoc` is applied as a term and has only to
typecheck rather than to match syntactically.

## Main results

* `AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange`: a morphism into a
  small étale base change is determined by its composite with the projection upstairs.
* `AlgebraicGeometry.smallEtaleBaseChange_map_hom_left_comp_fst` and
  `AlgebraicGeometry.smallEtaleBaseChange_map_hom_left_comp_fst_comp`: base change on morphisms
  commutes with the projection upstairs, without and with a trailing factor.
* `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst_comp`: the projection
  identity for the comparison of Stacks 021J, with a trailing factor.
* `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_assoc`: **the cocycle condition for
  the comparisons of Stacks 021J**, at a component and for chosen factorizations.

## What this unblocks

The functoriality in `f` of the rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)` — the presheaf that
**Stacks 070S part (3)** compares `(id_{τ,étale})^*𝓖` with, and the one clauses (1), (2), (3),
(6) and (7) of **Stacks 0DEW** also speak of.  Its `map_comp` needs the cocycle for
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` on sheaves of modules; what is proved
here is that cocycle's indexing half, the part about the base-change functors themselves.  The
module-level cocycle is
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtalePullbackCompCocycleProof.lean`,
and the presheaf it feeds is
`AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheafOfModules` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsSheafTauPresheaf.lean`;
neither is proved here.  Part (3)'s comparison, and the clause itself, are
`AlgebraicGeometry.BigFppfOver.smallEtaleSectionsGamma` and
`AlgebraicGeometry.BigFppfOver.baseSmallEtalePullbackIsoSectionsSheafification` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsSheafTauBigSite.lean`,
which is where the tag sits; no `@[stacks 070S]` attribute is claimed here.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

/-- **A morphism into a small étale base change is determined by the projection upstairs.**  For
`g : T ⟶ S` of the big étale site, the base change along `g` of an étale `U / S` is the fibre
product `T ×_S U`, whose structure morphism to `T` is the second projection.  A morphism of the
small étale category of `T` into it is a morphism of slices over `T`, so its composite with that
second projection is its own structure morphism and carries no information; by
`CategoryTheory.Limits.pullback.hom_ext` only the composite with the first projection remains. -/
public theorem SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange {S T : B.Scheme} (g : T ⟶ S)
    {U : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (u v : V ⟶ (smallEtaleBaseChange B g).obj U)
    (h : u.hom.left ≫ pullback.fst U.obj.hom g = v.hom.left ≫ pullback.fst U.obj.hom g) :
    u = v := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext h ?_))
  exact (Over.w u.hom).trans (Over.w v.hom).symm

/-- **Small étale base change on morphisms commutes with the projection upstairs.**  Base change
is the slice pullback restricted to the étale objects, by
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`, and the slice pullback of a morphism is
the lift whose first component is the first projection followed by that morphism. -/
@[reassoc]
public theorem smallEtaleBaseChange_map_hom_left_comp_fst {S T : B.Scheme} (g : T ⟶ S)
    {U V : SmallEtale B S.obj S.property} (k : U ⟶ V) :
    ((smallEtaleBaseChange B g).map k).hom.left ≫ pullback.fst V.obj.hom g =
      pullback.fst U.obj.hom g ≫ k.hom.left :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.smallEtaleBaseChange_map_hom_left_comp_fst` with a trailing factor.  The
goal of the cocycle is right-associated, so this is the shape that applies to it; stating it
separately also keeps the re-association inside a statement elaborated here, where the category
instance of `B.Scheme` is the one `CategoryTheory.Category.assoc` matches. -/
public theorem smallEtaleBaseChange_map_hom_left_comp_fst_comp {S T : B.Scheme} (g : T ⟶ S)
    {U V : SmallEtale B S.obj S.property} (k : U ⟶ V) {R : B.Scheme}
    (m : Over.left V.obj ⟶ R) :
    ((smallEtaleBaseChange B g).map k).hom.left ≫ pullback.fst V.obj.hom g ≫ m =
      pullback.fst U.obj.hom g ≫ k.hom.left ≫ m :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ m) (smallEtaleBaseChange_map_hom_left_comp_fst B g k)).trans
      (Category.assoc _ _ _))

/-- `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst` with a trailing factor,
for the same reason as `AlgebraicGeometry.smallEtaleBaseChange_map_hom_left_comp_fst_comp`. -/
public theorem smallEtaleBaseChange_factoredCompIso_hom_app_fst_comp
    (X' Y' Z' : B.Scheme) (f : X' ⟶ Y') (g : Y' ⟶ Z') (fg : X' ⟶ Z') (hfg : f ≫ g = fg)
    (W' : SmallEtale B Z'.obj Z'.property) {R : B.Scheme} (m : Over.left W'.obj ⟶ R) :
    ((smallEtaleBaseChange_factoredCompIso B X' Y' Z' f g fg hfg).hom.app W').hom.left ≫
        pullback.fst W'.obj.hom fg ≫ m =
      pullback.fst ((smallEtaleBaseChange B g).obj W').obj.hom f ≫
        pullback.fst W'.obj.hom g ≫ m :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ m)
        (smallEtaleBaseChange_factoredCompIso_hom_app_fst B X' Y' Z' f g fg hfg W')).trans
      (Category.assoc _ _ _))

variable (W X Y Z : B.Scheme) (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)

/-- **The cocycle condition for the comparisons of Stacks 021J.**  Let `a : W ⟶ X`, `b : X ⟶ Y`
and `c : Y ⟶ Z` be morphisms of a big étale site, with chosen factorizations `b ≫ c = bc`,
`a ≫ b = ab` and `a ≫ bc = abc = ab ≫ c`.  The two routes from the threefold base change
`U ↦ W ×_X (X ×_Y (Y ×_Z U))` to the base change `W ×_Z U` along the composite agree:
contracting `(b, c)` first and then `(a, bc)` is contracting `(a, b)` first and then `(ab, c)`.

Both sides are morphisms into a base change along `abc`, so by
`AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange` it suffices to compose
with the projection to `U`; and
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`, applied once on each side
to each comparison, carries both to the same composite of the three projections
`W ×_X (X ×_Y (Y ×_Z U)) ⟶ X ×_Y (Y ×_Z U) ⟶ Y ×_Z U ⟶ U`.

The whole proof after that reduction is a term, for the reason the implementation notes give:
`B.Scheme` is a full subcategory of `Scheme`, so the composite in the goal and the composites in
the statements of the two projection lemmas are produced by instance paths that are
definitionally but not syntactically equal.  Neither `rw` nor `simp` matches them -- a rewriting
tactic rechecks the goal at a restricted transparency, where it is not even type-correct -- so
the two re-associations are supplied as `CategoryTheory.Category.assoc` applied to named
arguments, which only has to typecheck. -/
public theorem smallEtaleBaseChange_factoredCompIso_assoc
    (bc : X ⟶ Z) (hbc : b ≫ c = bc) (ab : W ⟶ Y) (hab : a ≫ b = ab)
    (abc : W ⟶ Z) (habc : a ≫ bc = abc) (habc' : ab ≫ c = abc)
    (U : SmallEtale B Z.obj Z.property) :
    (smallEtaleBaseChange B a).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).hom.app U) ≫
        (smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).hom.app U =
      (smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).hom.app
          ((smallEtaleBaseChange B c).obj U) ≫
        (smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').hom.app U := by
  refine SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange B abc _ _ ?_
  have hL := smallEtaleBaseChange_factoredCompIso_hom_app_fst B W X Z a bc abc habc U
  have hL' := smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z b c bc hbc U
  have hR := smallEtaleBaseChange_factoredCompIso_hom_app_fst B W Y Z ab c abc habc' U
  exact Eq.trans
    (Category.assoc
      ((smallEtaleBaseChange B a).map
        ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).hom.app U)).hom.left
      ((smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).hom.app U).hom.left
      (pullback.fst U.obj.hom abc))
    (Eq.trans
      ((congrArg (fun t => ((smallEtaleBaseChange B a).map
            ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).hom.app U)).hom.left ≫ t)
          hL).trans
        ((((smallEtaleBaseChange_map_hom_left_comp_fst_comp B a
                  ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).hom.app U)
                  (pullback.fst U.obj.hom bc)).trans
                (congrArg (fun t => pullback.fst ((smallEtaleBaseChange B b).obj
                  ((smallEtaleBaseChange B c).obj U)).obj.hom a ≫ t) hL')).trans
              (smallEtaleBaseChange_factoredCompIso_hom_app_fst_comp B W X Y a b ab hab
                ((smallEtaleBaseChange B c).obj U) (pullback.fst U.obj.hom c)).symm).trans
          (congrArg (fun t => ((smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).hom.app
            ((smallEtaleBaseChange B c).obj U)).hom.left ≫ t) hR).symm))
      (Category.assoc
        ((smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).hom.app
          ((smallEtaleBaseChange B c).obj U)).hom.left
        ((smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').hom.app U).hom.left
        (pullback.fst U.obj.hom abc)).symm)

end AlgebraicGeometry

end
