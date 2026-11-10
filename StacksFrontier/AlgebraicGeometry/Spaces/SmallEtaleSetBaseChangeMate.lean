module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardParallelArrowCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesSetBaseChangeMate
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

/-!
# Stacks 03LR, part (1) for the canonical map on the small étale sites, at `Type u`

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  `StacksFrontier/AlgebraicGeometry/Spaces/SpacesSetBaseChangeMate.lean` proves that
on the *spaces*-étale sites, with coefficients in `Type u`, the base-change isomorphism of
Stacks 03LR, part (1) is the adjunction mate of the comparison of the two composite direct
images, and in particular that that mate is invertible.  This file carries that invertibility to
the **small** étale sites, where the direct image of modules reads it.

The transport is `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, the cube
along which invertibility of a mate moves under a change of the four categories of its square.
The four corners are related by the comparison equivalences of Stacks 03G1 at `Type u`, whose
inverses are fully faithful and so reflect isomorphisms; what the cube asks for besides is the
comparison of the two left adjoints, the comparison of the two vertical functors, the agreement
of the two units, and the agreement of the two comparisons of composite direct images.  All four
are supplied below, and none of them is new mathematics: each of the four functors of the small
étale square is *by definition* the conjugate of the corresponding spaces-étale one.

## Main results

* `AlgebraicGeometry.Space.isIso_mateEquiv_symm_smallSetPushforwardCompSquare`: **Stacks 03LR,
  part (1) for the canonical map, on the small étale sites at the universe of the structure
  rings.**
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_spacesIso`: the units of the
  small étale and of the spaces-étale adjunction of Stacks 03LP agree under the comparison
  equivalences, and `AlgebraicGeometry.Space.mateEquiv_smallEtaleSetRestrictionSpacesIso` reads
  that as a mate relation.
* `AlgebraicGeometry.Space.smallSetPushforwardCompSquare_spacesIso`: the small étale comparison
  of the two composite direct images around the square is the spaces-étale one.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso` and
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionSpacesIso`: the comparisons of the small
  étale direct image and of small étale restriction with their spaces-étale counterparts.
* `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_spacesIso`: the comparison of
  composite small étale direct images, Stacks 03G2 part (3) at `Type u`, read through the
  comparison equivalence of Stacks 03G1.  The comparison itself is
  `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean`, which already
  states Stacks 03G2 part (3) with its type written out in the
  `AlgebraicGeometry.Space.smallEtaleDirectImage` spelling.

## Implementation notes

**Two kernel-budget constraints, both of the shape recorded elsewhere in this development.**
First, `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` retyped, and the `rfl` rule
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso_def` identifying the two is stated here at
the level of the *isomorphism*: at the level of its components the kernel has to reconcile
`(smallToposMorphismTypeU f).pushforward.obj P` with `(smallEtaleDirectImage f).obj P` through a
transport, which unfolds the quasi-inverse of the comparison equivalence — a `Classical.choose` —
and does not finish.  Every proof below that needs the identification goes through that rule, so
none of them reintroduces the unfolding.

Second, the comparison of the two composite direct images around the square is written out as
its three factors in
`AlgebraicGeometry.Space.smallSetPushforwardCompSquare_spacesIso` and in
`AlgebraicGeometry.Space.isIso_mateEquiv_symm_smallSetPushforwardCompSquare` rather than hidden
behind a definition.  That is not stylistic: with the composite behind a definition the kernel
check of the component equation — one delta step away — exceeds its budget, for the same reason.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- The unit of an adjunction conjugated by two equivalences, compared with the original unit
through the two comparison isomorphisms the conjugation is built from. -/
theorem unit_conjugate_ofNatIsoLeft {C D C' D' : Type*} [Category C] [Category D] [Category C']
    [Category D'] (e₁ : C ≌ C') (e₂ : D ≌ D') {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    {L₀ : D' ⥤ C'} (iso : L₀ ≅ e₂.inverse ⋙ L ⋙ e₁.functor) (P : D') :
    adj.unit.app (e₂.inverse.obj P) ≫
        R.map (e₁.unitIso.hom.app (L.obj (e₂.inverse.obj P)) ≫
          e₁.inverse.map (iso.inv.app P)) =
      e₂.inverse.map ((((e₂.symm.toAdjunction.comp adj).comp
            e₁.toAdjunction).ofNatIsoLeft iso.symm).unit.app P) ≫
        e₂.unitIso.inv.app (R.obj (e₁.inverse.obj (L₀.obj P))) := by
  simp [Adjunction.comp_unit_app]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of sheaves of sets on the small étale sites, read on the spaces-étale sites
through the comparison equivalences of Stacks 03G1, is restriction along spaces-étale base
change.

`AlgebraicGeometry.Space.smallEtaleDirectImage` is by definition the conjugate of that
restriction functor, so the comparison is the unit isomorphism of the comparison equivalence at
the target. -/
noncomputable def smallEtaleDirectImageSpacesIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    smallEtaleDirectImage B S hS h ⋙
        (smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse ≅
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse ⋙
        spacesSetBaseChange B S hS h :=
  Functor.isoWhiskerLeft
    ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse ⋙
      spacesSetBaseChange B S hS h)
    (smallEtaleComparisonRestriction B S hS V).asEquivalence.unitIso.symm

/-- Restriction of sheaves of sets along small étale postcomposition with an étale morphism,
read on the spaces-étale sites through the comparison equivalences of Stacks 03G1, is restriction
along spaces-étale postcomposition.

This is `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso` with the comparison
equivalence at the source cancelled off. -/
noncomputable def smallEtaleSetRestrictionSpacesIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse ⋙
        spacesEtaleSetRestriction B S hS h hh ≅
      smallEtaleSetRestriction B S hS h hh ⋙
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse :=
  Functor.isoWhiskerLeft
      ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse ⋙
        spacesEtaleSetRestriction B S hS h hh)
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight
      (smallEtaleSetRestrictionConjIso B S hS h hh).symm
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse

/-- The components of `AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso`. -/
theorem smallEtaleDirectImageSpacesIso_hom_app {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (Q : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallEtaleDirectImageSpacesIso B S hS h).hom.app Q =
      (smallEtaleComparisonRestriction B S hS V).asEquivalence.unitIso.inv.app
        ((spacesSetBaseChange B S hS h).obj
          ((smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.obj Q)) := by
  rfl

/-- The components of `AlgebraicGeometry.Space.smallEtaleSetRestrictionSpacesIso`. -/
theorem smallEtaleSetRestrictionSpacesIso_hom_app {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallEtaleSetRestrictionSpacesIso B S hS h hh).hom.app P =
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.hom.app
          ((spacesEtaleSetRestriction B S hS h hh).obj
            ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P)) ≫
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse.map
          ((smallEtaleSetRestrictionConjIso B S hS h hh).inv.app P) := by
  rfl

/-- The units of the small étale and of the spaces-étale adjunction of Stacks 03LP agree under
the comparison equivalences of Stacks 03G1.  Both
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and its left adjoint are obtained
from the spaces-étale adjunction by conjugating with those equivalences, so this is
`CategoryTheory.unit_conjugate_ofNatIsoLeft`. -/
theorem smallEtaleSetRestrictionAdjunction_unit_spacesIso {U V : AlgebraicSpaces B S hS}
    (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh).unit.app
          ((smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.obj P) ≫
        (spacesSetBaseChange B S hS h).map
          ((smallEtaleSetRestrictionSpacesIso B S hS h hh).hom.app P) =
      (smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse.map
          ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app P) ≫
        (smallEtaleDirectImageSpacesIso B S hS h).hom.app
          ((smallEtaleSetRestriction B S hS h hh).obj P) := by
  rw [smallEtaleSetRestrictionSpacesIso_hom_app, smallEtaleDirectImageSpacesIso_hom_app]
  exact unit_conjugate_ofNatIsoLeft
    (smallEtaleComparisonRestriction B S hS U).asEquivalence
    (smallEtaleComparisonRestriction B S hS V).asEquivalence
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh)
    (smallEtaleSetRestrictionConjIso B S hS h hh) P

/-- `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, retyped.  The rewrite rule is stated at
the level of the *isomorphism* and not of its components: at the components the kernel has to
identify `(smallToposMorphismTypeU f).pushforward.obj P` with
`(smallEtaleDirectImage f).obj P` under a transport and runs out of its budget, whereas at the
isomorphism it is one unfolding. -/
theorem smallEtaleDirectImageCompIso_def {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    (b : Y ⟶ Z) :
    smallEtaleDirectImageCompIso B S hS a b = smallToposMorphismTypeU_comp B S hS a b :=
  rfl

/-- **The comparison of composite direct images on the small étale sites is the spaces-étale
one.**  This is the naturality of the unit isomorphism of the comparison equivalence of
Stacks 03G1 at the target. -/
theorem smallEtaleDirectImageCompIso_spacesIso {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    (b : Y ⟶ Z) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS Z).asEquivalence.inverse.map
          ((smallEtaleDirectImageCompIso B S hS a b).hom.app P) ≫
        (smallEtaleDirectImageSpacesIso B S hS (a ≫ b)).hom.app P =
      (smallEtaleDirectImageSpacesIso B S hS b).hom.app
          ((smallEtaleDirectImage B S hS a).obj P) ≫
        (spacesSetBaseChange B S hS b).map
          ((smallEtaleDirectImageSpacesIso B S hS a).hom.app P) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS a b).hom.app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P) := by
  rw [smallEtaleDirectImageCompIso_hom_app, smallEtaleDirectImageSpacesIso_hom_app,
    smallEtaleDirectImageSpacesIso_hom_app]
  exact (smallEtaleComparisonRestriction B S hS Z).asEquivalence.unitIso.inv.naturality _

/-- The comparison of `AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso` along an equality
of morphisms. -/
theorem smallEtaleDirectImageSpacesIso_eqToHom {X Z : AlgebraicSpaces B S hS} {k k' : X ⟶ Z}
    (w : k = k') (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImageSpacesIso B S hS k).hom.app P ≫
        (eqToHom (congrArg (fun m : X ⟶ Z =>
          (spacesBaseChange B S hS m).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X)) w)).app
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P) =
      (smallEtaleComparisonRestriction B S hS Z).asEquivalence.inverse.map
          ((eqToHom (congrArg (fun m : X ⟶ Z => smallEtaleDirectImage B S hS m) w)).app P) ≫
        (smallEtaleDirectImageSpacesIso B S hS k').hom.app P := by
  subst w
  simp

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **The comparison of composite direct images around the square is the spaces-étale one.**
The small étale comparison of the two composite direct images, read on the spaces-étale sites
through `AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso` at the four corners, is
`AlgebraicGeometry.Space.spacesSetPushforwardCompSquare`.

This is the cube hypothesis along which
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` carries the invertibility
of the spaces-étale mate to the small étale sites. -/
theorem smallSetPushforwardCompSquare_spacesIso (w : i ≫ f = f' ≫ g)
    (N : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)) :
    (smallEtaleDirectImageSpacesIso B S hS f).hom.app
          ((smallEtaleDirectImage B S hS i).obj N) ≫
        (spacesSetBaseChange B S hS f).map
          ((smallEtaleDirectImageSpacesIso B S hS i).hom.app N) ≫
        ((spacesBaseChange_pushforward_compTypeU B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y =>
              (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
                (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS f' g).inv).app
          ((smallEtaleComparisonRestriction B S hS X').asEquivalence.inverse.obj N) ≫
        (spacesSetBaseChange B S hS g).map
          ((smallEtaleDirectImageSpacesIso B S hS f').inv.app N) =
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
          (((smallEtaleDirectImageCompIso B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y => smallEtaleDirectImage B S hS k) w) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv).app N) ≫
        (smallEtaleDirectImageSpacesIso B S hS g).hom.app
          ((smallEtaleDirectImage B S hS f').obj N) := by
  have hA1 := smallEtaleDirectImageCompIso_spacesIso B S hS i f N
  have hA2 := smallEtaleDirectImageCompIso_spacesIso B S hS f' g N
  have heq := smallEtaleDirectImageSpacesIso_eqToHom B S hS w N
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  slice_lhs 1 3 => rw [← hA1]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [heq]
  simp only [Category.assoc]
  rw [cancel_epi, cancel_epi,
    ← cancel_epi ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
      ((smallEtaleDirectImageCompIso B S hS f' g).hom.app N))]
  slice_lhs 1 2 => rw [hA2]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.id_comp, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [← Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  refine (Category.id_comp _).symm.trans (congrArg (fun m ↦ m ≫
    (smallEtaleDirectImageSpacesIso B S hS g).hom.app
      ((smallEtaleDirectImage B S hS f').obj N)) ?_)
  exact ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map_id _).symm

end Square

/-- The mate of `AlgebraicGeometry.Space.smallEtaleSetRestrictionSpacesIso` across the small
étale and the spaces-étale adjunction of Stacks 03LP is
`AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso`: the two comparisons of the left and of
the right adjoints correspond. -/
theorem mateEquiv_smallEtaleSetRestrictionSpacesIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    mateEquiv (smallEtaleSetRestrictionAdjunction B S hS h hh)
        (spacesEtalePostcompSheafAdjunction B S hS (Type u) h hh)
        (TwoSquare.mk _ _ _ _ (smallEtaleSetRestrictionSpacesIso B S hS h hh).hom) =
      TwoSquare.mk _ _ _ _ (smallEtaleDirectImageSpacesIso B S hS h).hom :=
  mateEquiv_eq_of_unit _ _ _ _ (smallEtaleSetRestrictionAdjunction_unit_spacesIso B S hS h hh)

section Cube

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Stacks 03LR, part (1) for the canonical map, on the small étale sites at the universe of
the structure rings.**  For a cartesian square of algebraic spaces whose bottom arrow `g` is
étale, the mate of the comparison of the two composite direct images of sheaves of sets, across
the two adjunctions `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` of Stacks 03LP,
is an isomorphism.

This is the spaces-étale statement
`AlgebraicGeometry.Space.isIso_mateEquiv_symm_spacesSetPushforwardCompSquare` transported along
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`: the four corners of the
square are related by the comparison equivalences of Stacks 03G1, whose inverses are fully
faithful and so reflect isomorphisms, the two left adjoints by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionSpacesIso`, the two vertical functors by
`AlgebraicGeometry.Space.smallEtaleDirectImageSpacesIso`, and the two comparisons of composite
direct images by
`AlgebraicGeometry.Space.smallSetPushforwardCompSquare_spacesIso`. -/
theorem isIso_mateEquiv_symm_smallSetPushforwardCompSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso ((mateEquiv (smallEtaleSetRestrictionAdjunction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (smallEtaleSetRestrictionAdjunction B S hS g hg)).symm
      (TwoSquare.mk _ _ _ _ ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y => smallEtaleDirectImage B S hS k) sq.w) ≫
          (smallEtaleDirectImageCompIso B S hS f' g).inv))) := by
  have hi := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have : Functor.ReflectsIsomorphisms
      (smallEtaleComparisonRestriction B S hS Y').asEquivalence.inverse := inferInstance
  have (U V : AlgebraicSpaces B S hS) (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
      IsIso (TwoSquare.mk _ _ _ _ (smallEtaleSetRestrictionSpacesIso B S hS h hh).hom) :=
    inferInstanceAs (IsIso (smallEtaleSetRestrictionSpacesIso B S hS h hh).hom)
  have := isIso_mateEquiv_symm_spacesSetPushforwardCompSquare B S hS i f' f g sq hg
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (smallEtaleSetRestrictionAdjunction B S hS i hi)
    (smallEtaleSetRestrictionAdjunction B S hS g hg)
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) i hi)
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)
    (TwoSquare.mk _ _ _ _ (smallEtaleSetRestrictionSpacesIso B S hS i hi).hom)
    (TwoSquare.mk _ _ _ _ (smallEtaleSetRestrictionSpacesIso B S hS g hg).hom)
    (smallEtaleDirectImageSpacesIso B S hS f).hom
    (smallEtaleDirectImageSpacesIso B S hS f').inv
    (TwoSquare.mk _ _ _ _ ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y => smallEtaleDirectImage B S hS k) sq.w) ≫
          (smallEtaleDirectImageCompIso B S hS f' g).inv))
    (TwoSquare.mk _ _ _ _ (spacesSetPushforwardCompSquare B S hS i f' f g sq.w)) ?_
  rw [mateEquiv_smallEtaleSetRestrictionSpacesIso, mateEquiv_smallEtaleSetRestrictionSpacesIso]
  refine NatTrans.ext (funext fun N => ?_)
  simp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  exact smallSetPushforwardCompSquare_spacesIso B S hS i f' f g sq.w N

end Cube

end AlgebraicGeometry.Space

end
