module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison

/-!
# Inverse image for base change in the direction of restriction, and its mate

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category. The two
presentations of the small étale site of a scheme — the size-bounded site
`AlgebraicGeometry.SmallEtale` of Stacks 021B and Mathlib's site
`AlgebraicGeometry.Scheme.Etale` of all schemes étale over the base — have the same sheaves, by
`AlgebraicGeometry.SmallEtale.sheafEquiv`, and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison` compares base
change across that equivalence. It does so in two different directions: the direct images are
compared along the **restriction** functor `ρ_S` of
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`, which carries a sheaf on
Mathlib's site to a sheaf on the bounded site, while the inverse images are compared along the
quasi-inverse `ρ_S⁻¹` of `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`, which
goes the other way.

A transport of a mate along a change of the four categories of its square,
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, needs all four comparisons
along **one** family of functors. This file supplies the missing direction: the comparison

```
ρ_S ⋙ f⁻¹  ≅  f⁻¹ ⋙ ρ_T
```

of inverse images along the restriction functors, and the identification of its mate under the
two inverse-image/direct-image adjunctions with the comparison of direct images.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSiteRestrictionAdjunction` — the equivalence of sheaf
  categories as an adjunction whose right adjoint is spelled as restriction along the embedding.
* `AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange` — the comparison of inverse images
  along the restriction functors, as a 2-square.
* `AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso` — the same comparison as a
  natural isomorphism.

## Main results

* `AlgebraicGeometry.SmallEtale.mateEquiv_restrictionPullbackBaseChange` — **the mate of the
  comparison of inverse images along the restriction functors is the comparison of direct
  images.** This is the single-edge identification that a transport of a mate along a change of
  categories consumes; the identification available before was
  `AlgebraicGeometry.SmallEtale.conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom`, which pins
  the comparison of inverse images only through the two *composite* adjunctions.

## Implementation notes

**Why the comparison is built as a mate and not by cancelling the equivalences.** The comparison
`ρ_S ⋙ f⁻¹ ≅ f⁻¹ ⋙ ρ_T` can be obtained from
`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso` by inserting the unit and counit
of the two equivalences, and that is in effect what the mate construction does; but a comparison
built that way would then have to be matched with a mate anyway. Taking the mate of the inverse
of `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso` along the two *horizontal*
adjunctions makes `AlgebraicGeometry.SmallEtale.mateEquiv_restrictionPullbackBaseChange` an
instance of `CategoryTheory.iterated_mateEquiv_conjugateEquiv`: iterating the mate operation of a
square of four adjunctions in the two directions returns the conjugate of the 2-cell one started
from, and that conjugate is pinned by
`AlgebraicGeometry.SmallEtale.conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom`.

**That the comparison is invertible is not automatic**, a mate of an invertible 2-cell being
invertible in general only in the degenerate cases: this is the Beck–Chevalley phenomenon. Here
it holds because the two horizontal adjunctions are those of *equivalences*, so that their units
and counits are invertible; `Stacks.CategoryTheory.isIso_mateEquiv_natTrans` is that observation,
read off the three-factor formula for a component of a mate.

**The spelling of the restriction functor.** `AlgebraicGeometry.SmallEtale.sheafEquiv` is an
equivalence whose inverse is restriction along the embedding, and
`CategoryTheory.Equivalence.toAdjunction` presents it with that inverse spelled as
`CategoryTheory.Equivalence.inverse`. The comparisons of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison` spell it instead
as `CategoryTheory.Functor.sheafPushforwardContinuous`. The two are definitionally equal, but a
2-cell whose type uses one spelling cannot be rewritten in a goal that uses the other, so the
adjunction is named once, in the second spelling, in
`AlgebraicGeometry.SmallEtale.toEtaleSiteRestrictionAdjunction`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ v' u' u

namespace Stacks.CategoryTheory

/-- **A mate of an invertible 2-cell is invertible when the two adjunctions are those of
equivalences**, or more precisely when the counit of the upper one and the unit of the lower one
are invertible.

This is not a general fact — the invertibility of a 2-cell and of its mate are different
conditions, which is the Beck–Chevalley phenomenon — but it is immediate from the formula for a
component of a mate: that component is the unit of the lower adjunction, followed by the right
adjoint applied to the component of the 2-cell, followed by the right adjoint applied to the
counit of the upper one. -/
public theorem isIso_mateEquiv_natTrans {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    [IsIso α] [IsIso adj₁.counit] [IsIso adj₂.unit] :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  have h : (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
    simp [mateEquiv]
  rw [h]
  infer_instance

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A]

/-- **The equivalence of the two presentations of the small étale site, as an adjunction whose
right adjoint is restriction along the embedding.**

This is `AlgebraicGeometry.SmallEtale.sheafEquiv` read through
`CategoryTheory.Equivalence.toAdjunction`, with the inverse of the equivalence spelled as
restriction of sheaves along `AlgebraicGeometry.SmallEtale.toEtaleSite`, which is the spelling
the base change comparisons use. -/
public noncomputable def toEtaleSiteRestrictionAdjunction (S : B.Scheme) :
    (sheafEquiv B S.obj S.property A).functor ⊣
      (toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
        (topology B S.obj S.property) S.obj.smallEtaleTopology :=
  (sheafEquiv B S.obj S.property A).toAdjunction

/-- The unit of the adjunction of an equivalence is invertible. -/
public instance isIso_toEtaleSiteRestrictionAdjunction_unit (S : B.Scheme) :
    IsIso (toEtaleSiteRestrictionAdjunction B A S).unit :=
  inferInstanceAs (IsIso (sheafEquiv B S.obj S.property A).toAdjunction.unit)

/-- The counit of the adjunction of an equivalence is invertible. -/
public instance isIso_toEtaleSiteRestrictionAdjunction_counit (S : B.Scheme) :
    IsIso (toEtaleSiteRestrictionAdjunction B A S).counit :=
  inferInstanceAs (IsIso (sheafEquiv B S.obj S.property A).toAdjunction.counit)

variable {S T : B.Scheme} (f : T ⟶ S)
  {LU : Sheaf S.obj.smallEtaleTopology A ⥤ Sheaf T.obj.smallEtaleTopology A}
  {LB : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (topology B T.obj T.property) A}
  (adjU : LU ⊣ (Stacks.EtaleCohomology.smallEtaleBaseChange
      (B.inclusion.map f)).sheafPushforwardContinuous A
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
  (adjB : LB ⊣ (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (topology B S.obj S.property) (topology B T.obj T.property))

/-- **The comparison of the two inverse images along base change, in the direction of
restriction.** Restriction along the embedding of the bounded site of `S`, followed by inverse
image along base change for the bounded presentation, is inverse image along base change for
Mathlib's presentation followed by restriction along the embedding of the bounded site of `T`.

`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso` is the same square read along the
quasi-inverses of the two restriction functors; this is its mate along the two horizontal
adjunctions, which is what puts it in the direction in which the comparison of direct images,
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`, is stated. -/
public noncomputable def restrictionPullbackBaseChange :
    TwoSquare ((toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
        (topology B S.obj S.property) S.obj.smallEtaleTopology) LU LB
      ((toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
        (topology B T.obj T.property) T.obj.smallEtaleTopology) :=
  mateEquiv (toEtaleSiteRestrictionAdjunction B A S) (toEtaleSiteRestrictionAdjunction B A T)
    (TwoSquare.mk _ _ _ _ (sheafEquivPullbackBaseChangeIso B f A adjU adjB).inv)

/-- **The comparison of inverse images along the restriction functors is invertible.** The two
adjunctions along which the mate is taken are those of equivalences, so their units and counits
are invertible and `Stacks.CategoryTheory.isIso_mateEquiv_natTrans` applies. -/
public instance isIso_restrictionPullbackBaseChange :
    IsIso (restrictionPullbackBaseChange B A f adjU adjB) :=
  Stacks.CategoryTheory.isIso_mateEquiv_natTrans _ _ _

/-- **The two presentations of the small étale site have the same inverse image along base
change, compared along the restriction functors.** The isomorphism
`ρ_S ⋙ f⁻¹ ≅ f⁻¹ ⋙ ρ_T` underlying
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange`. -/
public noncomputable def restrictionPullbackBaseChangeIso :
    (toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
          (topology B S.obj S.property) S.obj.smallEtaleTopology ⋙ LB ≅
      LU ⋙ (toEtaleSite B T.obj T.property).sheafPushforwardContinuous A
        (topology B T.obj T.property) T.obj.smallEtaleTopology :=
  asIso (restrictionPullbackBaseChange B A f adjU adjB)

/-- **The mate of the comparison of inverse images along the restriction functors is the
comparison of direct images.** Under the two inverse-image/direct-image adjunctions for base
change along `f`, the 2-cell `ρ_S ⋙ f⁻¹ ⟶ f⁻¹ ⋙ ρ_T` of
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange` goes to the 2-cell
`f_* ⋙ ρ_S ⟶ ρ_T ⋙ f_*` of
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`.

This is the single-edge form of
`AlgebraicGeometry.SmallEtale.conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom`, which pins
the comparison of inverse images only through the two composite adjunctions. The passage from
the one to the other is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`, that iterating the
mate operation of a square of four adjunctions in the two directions gives the conjugate of the
2-cell one started from, read backwards. -/
public theorem mateEquiv_restrictionPullbackBaseChange :
    (mateEquiv adjU adjB (restrictionPullbackBaseChange B A f adjU adjB)) =
      (toEtaleSitePushforwardBaseChangeIso B f A).hom := by
  rw [restrictionPullbackBaseChange, iterated_mateEquiv_conjugateEquiv
    (toEtaleSiteRestrictionAdjunction B A S) (toEtaleSiteRestrictionAdjunction B A T) adjB adjU]
  have hi : conjugateIsoEquiv (adjB.comp (toEtaleSiteRestrictionAdjunction B A T))
        ((toEtaleSiteRestrictionAdjunction B A S).comp adjU)
        (toEtaleSitePullbackBaseChangeIso B f A adjU adjB
          (toEtaleSiteRestrictionAdjunction B A S) (toEtaleSiteRestrictionAdjunction B A T)) =
      (toEtaleSitePushforwardBaseChangeIso B f A).symm :=
    Iso.ext (conjugateEquiv_toEtaleSitePullbackBaseChangeIso_hom B f A adjU adjB
      (toEtaleSiteRestrictionAdjunction B A S) (toEtaleSiteRestrictionAdjunction B A T))
  exact congrArg Iso.inv hi

end AlgebraicGeometry.SmallEtale

end
