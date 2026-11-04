module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtaleEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Abelian
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianBaseChange
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleToOverBaseChange
public import StacksFrontier.CategoryTheory.Equivalence.ConjugateSquare
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of the finite locally constant sheaf represented by a finite étale cover

Let `B` be a big étale site, let `X` and `Y` be objects of `B` and let `f : Y ⟶ X`. Base change
along `f` carries a finite object of the small étale site of `X` to a finite object of the small
étale site of `Y`, and inverse image carries a finite locally constant sheaf of sets on
`X_étale` to one on `Y_étale`. This file proves that the resulting square

```
  finite objects of X_étale  ──h_•^#──→  finite locally constant sheaves on X_étale
            │                                          │
       base change                                   f^{-1}
            ↓                                          ↓
  finite objects of Y_étale  ──h_•^#──→  finite locally constant sheaves on Y_étale
```

commutes: the inverse image of the sheaf represented by `U ⟶ X` is the sheaf represented by
`U ×_X Y ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.finiteSmallEtaleBaseChange` — base change on the finite objects of the
  small étale site.
* `AlgebraicGeometry.finiteLocallyConstantSheafPullback` — inverse image on the finite locally
  constant sheaves of sets.

## Main results

* `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstantBaseChangeIso` — the square above
  commutes.
* `AlgebraicGeometry.finiteEtaleFromSmallEtaleBaseChangeIso` — base change on the finite objects
  of the small étale site is base change of finite étale covers.
* `AlgebraicGeometry.finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso` — the dictionary
  of Stacks 03RV commutes with pullback.
* `AlgebraicGeometry.nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso` — **Stacks
  0DV6 for sheaves of sets**: the equivalence of Stacks 0DV5 (1) between the finite locally
  constant sheaves of sets on `X_étale` and the finite continuous `π₁(X, x)`-sets commutes with
  pullback along a morphism of connected schemes, the action being reindexed along the induced
  homomorphism of fundamental groups.
* `AlgebraicGeometry.nonempty_finiteLocallyConstantAbelianSheafEquivalence_pullbackIso` —
  **Stacks 0DV6 for sheaves of abelian groups**: the same for the equivalence of Stacks
  0DV5 (2) with the finite discrete `π₁(X, x)`-modules.
* `AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalence_pullbackIso` —
  **Stacks 0DV6 for sheaves of modules** over a finite ring: the same for the equivalence of
  Stacks 0DV5 (3) with the finite `π₁(X, x)`-modules carrying a commuting module structure.

## Implementation notes

Both vertical functors are lifts along a full subcategory inclusion of functors already in the
library, so each composed with its inclusion is the original functor on the nose. The square is
therefore checked after composing with the inclusion of the finite locally constant sheaves,
where it becomes the general statement
`CategoryTheory.Sheaf.sheafPullbackCompSheafifiedYonedaIso` — the inverse image of a sheafified
representable is the sheafified representable of the image — restricted along the inclusion of
the finite objects. Full faithfulness of the inclusion then transports the isomorphism back,
by `CategoryTheory.Functor.fullyFaithfulCancelRight`.

That base change preserves finiteness of the structure morphism is stability of finite
morphisms under base change, applied to the pullback square which `B.inclusion` preserves; that
inverse image preserves finite local constancy is
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback`, Stacks Tag 093R.

The abelian case is the sets case transported along the two dictionaries presenting a finite
locally constant abelian sheaf and a finite discrete module as commutative group objects, which
is `Stacks.ConstantSheaf.finiteLocallyConstantAbelianPullbackSquare`. Its two vertical arrows are
again lifts of ambient functors: the inverse image of abelian sheaves and
`CategoryTheory.ContAction.res` on actions on abelian groups, both identified by
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafPullback_comp_ι` and
`CategoryTheory.ContinuousGAddCommGrp.resIsFinite_comp_ι` together with
`CategoryTheory.ContinuousGAddCommGrp.res_comp_ι`.

The module case is the abelian case read on additive functors out of the one-object category of
the coefficient ring, which is `CategoryTheory.scalarActionTransportSquare`. Its sheaf-side input
is the identification of the inverse image of sheaves of modules with the inverse image of the
underlying abelian sheaves together with the induced scalar operations,
`Stacks.Sites.AbelianPullback.moduleSheafPullbackScalarSquare`, which again needs no new
mathematics: the direct images agree on the nose, and postcomposition with an additive functor
carries an adjunction to an adjunction, so uniqueness of left adjoints does the rest. Its
action-side input is
`Stacks.GroupCohomology.finiteTypeContinuousModuleToScalarAction_res`, which holds by `rfl`.

Tag 0DV6 for sheaves of sets is the square above joined to the one of Stacks 0BND (3). The
join is the identification of base change on the finite objects of the small étale site with
base change of finite étale covers, which is
`AlgebraicGeometry.smallEtaleToOverBaseChangeIso` read on the finite objects: both composites
land in `FÉt_Y`, whose forgetful functor to schemes over `Y` is fully faithful because the
morphism property on the arrows is `⊤`. Composing the three squares needs the first of them
with its two horizontal equivalences reversed, which is
`CategoryTheory.Equivalence.conjugateSquare`, and the change of universe of a finite discrete
continuous action commutes with restriction of the action on the nose.

## References

* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology
open scoped FintypeCatDiscrete

universe u uG r

attribute [local instance] discreteForget₂Type discreteForget₂AddCommGrpCat
  cartesianMonoidalContinuousGSet braidedContinuousGSet
  Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)

/-- Base change along `f` preserves finiteness of the structure morphism of an object of the
small étale site: finite morphisms are stable under base change, and `B.inclusion` preserves the
pullback square. -/
public theorem isFinite_smallEtaleBaseChange_obj (U : SmallEtale B X.1 X.2)
    (hU : finiteSmallEtaleObjects B X U) :
    finiteSmallEtaleObjects B Y ((smallEtaleBaseChange B f).obj U) := by
  show IsFinite (B.inclusion.map (pullback.snd U.obj.hom f))
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback U.obj.hom f).map B.inclusion) hU

/-- Base change along `f` on the finite objects of the small étale site. -/
public def finiteSmallEtaleBaseChange :
    (finiteSmallEtaleObjects B X).FullSubcategory ⥤
      (finiteSmallEtaleObjects B Y).FullSubcategory :=
  (finiteSmallEtaleObjects B Y).lift
    ((finiteSmallEtaleObjects B X).ι ⋙ smallEtaleBaseChange B f)
    fun U ↦ isFinite_smallEtaleBaseChange_obj B f U.1 U.2

/-- Inverse image along `f` on sheaves of sets for the small étale topologies. -/
public abbrev smallEtaleSheafPullbackType :
    Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B Y.1 Y.2) (Type (u + 1)) :=
  (smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)

/-- Inverse image along `f` on the finite locally constant sheaves of sets, which is defined
because inverse image preserves finite local constancy (Stacks Tag 093R). -/
public def finiteLocallyConstantSheafPullback :
    FiniteLocallyConstantSheaf B X ⥤ FiniteLocallyConstantSheaf B Y :=
  ObjectProperty.lift _
    (ObjectProperty.ι
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
          IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) ⋙
      smallEtaleSheafPullbackType B f)
    fun F ↦ isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) F.1 F.2

/-- Composing `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstant` with the inclusion of
the finite locally constant sheaves gives the sheafified Yoneda embedding restricted to the
finite objects of the small étale site. -/
public def finiteSmallEtaleToFiniteLocallyConstantCompιIso :
    finiteSmallEtaleToFiniteLocallyConstant B X ⋙
        ObjectProperty.ι
          (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ↦
            IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) ≅
      (finiteSmallEtaleObjects B X).ι ⋙ Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro U V g
    simp [finiteSmallEtaleToFiniteLocallyConstant])

/-- **Stacks Project, Tag 0DV6, the first leg of the sets case.** The inverse image of the
finite locally constant sheaf represented by a finite étale cover is the one represented by its
base change: the square of `AlgebraicGeometry.finiteSmallEtaleToFiniteLocallyConstant` against
base change on the site and inverse image on sheaves commutes.

The equivalence of Tag 0DV5 (1) between the finite locally constant sheaves of sets on
`X_étale` and the finite continuous `π₁(X, x)`-sets is the composite of two legs, the dictionary
of Tag 03RV with finite étale covers and the equivalence of Tag 0BND (1). This is the
compatibility of the first leg with pullbacks. -/
@[stacks 0DV6 "the sets case, first leg: the dictionary of Stacks 03RV between the finite \
objects of the small etale site and the finite locally constant sheaves of sets commutes with \
pullback. The second leg, Stacks 0BND (3), is proved separately as \
AlgebraicGeometry.exists_finiteEtaleEquivalence_mapIso; the two legs are not composed here, \
which would need the comparison of AlgebraicGeometry.finiteSmallEtaleBaseChange with \
AlgebraicGeometry.finiteEtaleBaseChange across AlgebraicGeometry.finiteEtaleSiteEquivalence"]
public def finiteSmallEtaleToFiniteLocallyConstantBaseChangeIso :
    finiteSmallEtaleToFiniteLocallyConstant B X ⋙ finiteLocallyConstantSheafPullback B f ≅
      finiteSmallEtaleBaseChange B f ⋙ finiteSmallEtaleToFiniteLocallyConstant B Y :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι
      (fun F : Sheaf (SmallEtale.topology B Y.1 Y.2) (Type (u + 1)) ↦
        IsFiniteLocallyConstant (SmallEtale.topology B Y.1 Y.2) F))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (finiteSmallEtaleToFiniteLocallyConstant B X)
        (ObjectProperty.liftCompιIso _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (finiteSmallEtaleToFiniteLocallyConstantCompιIso B)
        (smallEtaleSheafPullbackType B f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (finiteSmallEtaleObjects B X).ι
        (Sheaf.sheafifiedYonedaCompSheafPullbackIso (smallEtaleBaseChange B f)
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _).symm
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B Y.1 Y.2)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (finiteSmallEtaleBaseChange B f)
        (finiteSmallEtaleToFiniteLocallyConstantCompιIso B).symm ≪≫
      (Functor.associator _ _ _).symm)

/-! ### The join with the dictionary of finite étale covers -/

/-- **Base change on the finite objects of the small étale site is base change of finite étale
covers.** The comparison functor to `FÉt_•` takes the one to the other: both composites become,
after the fully faithful forgetful functor to schemes over `Y`, the comparison
`AlgebraicGeometry.smallEtaleToOverBaseChangeIso` restricted along the inclusion of the finite
objects. -/
public def finiteEtaleFromSmallEtaleBaseChangeIso :
    finiteSmallEtaleBaseChange B f ⋙ finiteEtaleFromSmallEtale B Y ≅
      finiteEtaleFromSmallEtale B X ⋙ finiteEtaleBaseChange f.hom :=
  Functor.fullyFaithfulCancelRight
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ Y.1)
    (Functor.isoWhiskerLeft (finiteSmallEtaleObjects B X).ι
      (smallEtaleToOverBaseChangeIso B f))

/-- **The dictionary of Stacks Tag 03RV commutes with pullback.** The equivalence identifying
the finite locally constant sheaves of sets on `X_étale` with the finite étale covers of `X`
carries inverse image of sheaves to base change of covers. -/
public def finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso :
    (finiteLocallyConstantFiniteEtaleEquivalence B X).functor ⋙ finiteEtaleBaseChange f.hom ≅
      finiteLocallyConstantSheafPullback B f ⋙
        (finiteLocallyConstantFiniteEtaleEquivalence B Y).functor :=
  Functor.isoWhiskerLeft (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.inverse
      (finiteEtaleFromSmallEtaleBaseChangeIso B f).symm ≪≫
    Functor.isoWhiskerRight
      (Equivalence.conjugateSquare
        (finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence
        (finiteSmallEtaleToFiniteLocallyConstant B Y).asEquivalence
        (finiteSmallEtaleToFiniteLocallyConstantBaseChangeIso B f))
      (finiteEtaleFromSmallEtale B Y)

/-! ### Tag 0DV6 for sheaves of sets -/

/-- **Stacks Project, Tag 0DV6 for sheaves of sets.** Let `f : Y ⟶ X` be a morphism of connected
schemes and let `y` be a geometric point of `Y`, with image `x = f(y)`. Then the square

```
  finite locally constant sheaves of sets on X_étale  ──→  finite π₁(X, x)-sets
                        │                                          │
                     f^{-1}                                   restriction
                        ↓                                          ↓
  finite locally constant sheaves of sets on Y_étale  ──→  finite π₁(Y, y)-sets
```

commutes, where the horizontal arrows are the equivalence of Stacks Tag 0DV5 (1) and the right
vertical arrow reindexes the action along the homomorphism `π₁(Y, y) ⟶ π₁(X, x)` induced by
`f`.

The equivalence of Tag 0DV5 (1) is the composite of the dictionary of Tag 03RV with the finite
étale covers, the equivalence of Tag 0BND (1) and a change of universe. The first factor
commutes with pullback by
`AlgebraicGeometry.finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso`, the second by
Tag 0BND (3), that is `AlgebraicGeometry.exists_finiteEtaleEquivalence_mapIso`, and the third
on the nose. Only the existence of the comparison is asserted, because Tag 0BND (3) is
available in that form. -/
@[stacks 0DV6 "for sheaves of sets: the equivalence of Stacks 0DV5 (1) commutes with pullback, \
the action being reindexed along the induced homomorphism of fundamental groups"]
public theorem nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (y : GeometricPoint Y.1) :
    Nonempty ((finiteLocallyConstantSetsEquivalence B X (y.map f.hom)).functor ⋙
        ContAction.res FintypeCat.{u + 1} (etaleFundamentalGroupMap f.hom y) ≅
      finiteLocallyConstantSheafPullback B f ⋙
        (finiteLocallyConstantSetsEquivalence B Y y).functor) := by
  obtain ⟨η, -⟩ := exists_finiteEtaleEquivalence_mapIso f.hom y
  exact ⟨Functor.isoWhiskerLeft (finiteLocallyConstantFiniteEtaleEquivalence B X).functor
      (Functor.isoWhiskerRight η
        (contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup Y.1 y)).functor) ≪≫
    Functor.isoWhiskerRight (finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso B f)
      ((finiteEtaleEquivalenceOfIsGaloisCategory Y.1 y).functor ⋙
        (contActionUniverseEquivalence.{u, u + 1} (EtaleFundamentalGroup Y.1 y)).functor)⟩

/-! ### Tag 0DV6 for sheaves of abelian groups -/

section Abelian

variable {G H : Type uG} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- **Reading a finite continuous action of `H` on a finite set as a continuous `H`-set commutes
with restriction along `φ : G →ₜ* H`.** Restriction changes neither the underlying finite set nor
the topology, so the two composites agree on the nose. -/
public theorem finiteActionToFiniteGSet_comp_resIsFinite :
    finiteActionToFiniteGSet (G := H) ⋙ ContinuousGSet.resIsFinite φ =
      ContAction.res FintypeCat.{uG} φ ⋙ finiteActionToFiniteGSet (G := G) := rfl

end Abelian

/-- Inverse image along `f` on the finite locally constant sheaves of abelian groups, which is
defined because inverse image preserves finite local constancy (Stacks Tag 093R). -/
public def finiteLocallyConstantAbelianSheafPullback :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B Y.1 Y.2)).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    fun F ↦ isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) F.1 F.2

/-- **Inverse image on the finite locally constant abelian sheaves is the inverse image of
abelian sheaves.** The left vertical arrow of the abelian square is the chosen left adjoint of
the direct image of abelian sheaves, read on the finite locally constant ones. -/
public theorem finiteLocallyConstantAbelianSheafPullback_comp_ι :
    finiteLocallyConstantAbelianSheafPullback B f ⋙
        (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B Y.1 Y.2)).ι =
      (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B X.1 X.2)).ι ⋙
        (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) := rfl

/-- **Inverse image on the finite locally constant sheaves of sets is the inverse image of
sheaves of sets.** -/
public theorem finiteLocallyConstantSheafPullback_comp_ι :
    finiteLocallyConstantSheafPullback B f ⋙
        (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B Y.1 Y.2)).ι =
      (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B X.1 X.2)).ι ⋙ smallEtaleSheafPullbackType B f := rfl

/-- **Stacks Project, Tag 0DV6 for sheaves of sets, in the shape Tag 0DV5 (2) consumes.** The
equivalence of Tag 0DV5 (1) read with the finite continuous `π₁(X, x)`-sets presented as a full
subcategory of all continuous `π₁(X, x)`-sets again commutes with pullback. This is
`AlgebraicGeometry.nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso` composed with
`AlgebraicGeometry.finiteActionToFiniteGSet_comp_resIsFinite`. -/
public theorem nonempty_finiteLocallyConstantSetsEquivalence'_pullbackIso
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (y : GeometricPoint Y.1) :
    Nonempty ((finiteLocallyConstantSetsEquivalence' B X (y.map f.hom)).functor ⋙
        ContinuousGSet.resIsFinite (etaleFundamentalGroupMap f.hom y) ≅
      finiteLocallyConstantSheafPullback B f ⋙
        (finiteLocallyConstantSetsEquivalence' B Y y).functor) := by
  obtain ⟨h₀⟩ := nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso B f y
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (finiteLocallyConstantSetsEquivalence B X (y.map f.hom)).functor
      (eqToIso (finiteActionToFiniteGSet_comp_resIsFinite
        (etaleFundamentalGroupMap f.hom y))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight h₀ finiteActionToFiniteGSet ≪≫
    Functor.associator _ _ _⟩

/-- **Stacks Project, Tag 0DV6 for sheaves of abelian groups.** Let `f : Y ⟶ X` be a morphism of
connected schemes and let `y` be a geometric point of `Y`, with image `x = f(y)`. Then the square

```
  finite locally constant abelian sheaves on X_étale  ──→  finite π₁(X, x)-modules
                        │                                          │
                     f^{-1}                                   restriction
                        ↓                                          ↓
  finite locally constant abelian sheaves on Y_étale  ──→  finite π₁(Y, y)-modules
```

commutes, where the horizontal arrows are the equivalence of Stacks Tag 0DV5 (2), the left
vertical arrow is the inverse image of abelian sheaves
(`AlgebraicGeometry.finiteLocallyConstantAbelianSheafPullback_comp_ι`) and the right vertical
arrow reindexes the action along the homomorphism `π₁(Y, y) ⟶ π₁(X, x)` induced by `f`
(`CategoryTheory.ContinuousGAddCommGrp.resIsFinite_comp_ι`).

The equivalence of Tag 0DV5 (2) is the transport of commutative group objects along the
equivalence of Tag 0DV5 (1), and the only factor of that transport which depends on the latter is
`CategoryTheory.Functor.mapCommGrp` applied to it, so the sets case of Tag 0DV6 transports:
`Stacks.ConstantSheaf.finiteLocallyConstantAbelianPullbackSquare`. Its two remaining inputs are
the compatibility of each dictionary with the two vertical arrows, and for the sheaf side that is
the identification of the inverse image of abelian sheaves with the inverse image of the
underlying sheaves of sets together with the induced group operations,
`Stacks.Sites.AbelianPullback.internalSheafPullbackSquare`. Only the existence of the comparison
is asserted, because the sets case is available in that form. -/
@[stacks 0DV6 "for sheaves of abelian groups: the equivalence of Stacks 0DV5 (2) commutes with \
pullback, the action being reindexed along the induced homomorphism of fundamental groups"]
public theorem nonempty_finiteLocallyConstantAbelianSheafEquivalence_pullbackIso
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (y : GeometricPoint Y.1) :
    Nonempty ((finiteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).functor ⋙
        ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y) ≅
      finiteLocallyConstantAbelianSheafPullback B f ⋙
        (finiteLocallyConstantAbelianSheafEquivalence B Y y).functor) := by
  obtain ⟨α⟩ := nonempty_finiteLocallyConstantSetsEquivalence'_pullbackIso B f y
  have hpp : PreservesFiniteProducts (smallEtaleSheafPullbackType B f) := inferInstance
  have hpt : ∀ A : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)),
      isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2) A →
      isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1} (SmallEtale.topology B Y.1 Y.2)
        ((smallEtaleSheafPullbackType B f).obj A) :=
    fun A hA ↦ isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) A hA
  have hint := Stacks.Sites.AbelianPullback.internalSheafPullbackSquare.{u + 1}
    (smallEtaleBaseChange B f) (SmallEtale.topology B X.1 X.2)
    (SmallEtale.topology B Y.1 Y.2)
  exact ⟨@finiteLocallyConstantAbelianPullbackSquare.{u, u + 1, u + 1}
    _ _ _ _ (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) _ _
    _ _ _ _ _ _
    (etaleFundamentalGroupMap f.hom y)
    (smallEtaleSheafPullbackType B f) hpp
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    hpt
    (finiteLocallyConstantSetsEquivalence' B X (y.map f.hom))
    (finiteLocallyConstantSetsEquivalence' B Y y)
    (finiteLocallyConstantSheafPullback B f) (Iso.refl _)
    (finiteLocallyConstantAbelianSheafPullback B f) (Iso.refl _)
    hint α⟩

/-! ### Tag 0DV6 for sheaves of modules -/

section Modules

variable (Λ : Type r) [Ring Λ] [Finite Λ] [ConnectedSpace X.1] [ConnectedSpace Y.1]

/-- Inverse image on the finite locally constant abelian sheaves is additive: after the fully
faithful inclusion it is the inverse image of abelian sheaves, which is a left adjoint. -/
public instance additive_finiteLocallyConstantAbelianSheafPullback :
    (finiteLocallyConstantAbelianSheafPullback B f).Additive := by
  have : (finiteLocallyConstantAbelianSheafPullback B f ⋙
      (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B Y.1 Y.2)).ι).Additive := by
    rw [finiteLocallyConstantAbelianSheafPullback_comp_ι]
    infer_instance
  exact Functor.additive_of_comp_faithful _
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B Y.1 Y.2)).ι

/-- Inverse image along `f` on the finite locally constant sheaves of `Λ`-modules. -/
public def finiteLocallyConstantModuleSheafPullback :
    ObjectProperty.FullSubcategory (fun F : Sheaf (SmallEtale.topology B X.1 X.2)
        (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) ⥤
      ObjectProperty.FullSubcategory (fun F : Sheaf (SmallEtale.topology B Y.1 Y.2)
        (ModuleCat.{u + 1} Λ) ↦ IsFiniteLocallyConstant (SmallEtale.topology B Y.1 Y.2) F) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    fun F ↦ isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) F.1 F.2

/-- Inverse image along `f` on the finite type locally constant sheaves of `Λ`-modules, which is
the left-hand vertical arrow of the module square. Over a finite ring the finite type condition
is finiteness of the local values, which is
`AlgebraicGeometry.isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant`, so inverse image
preserves it by Stacks Tag 093R. -/
public def finiteTypeLocallyConstantModuleSheafPullback :
    ObjectProperty.FullSubcategory (fun F : Sheaf (SmallEtale.topology B X.1 X.2)
        (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) ⥤
      ObjectProperty.FullSubcategory (fun F : Sheaf (SmallEtale.topology B Y.1 Y.2)
        (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B Y.1 Y.2) F) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    fun F ↦ by
      rw [congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B Y Λ)]
      refine isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) F.1 ?_
      rw [← congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B X Λ)]
      exact F.2

omit [ConnectedSpace X.1] [ConnectedSpace Y.1] in
/-- **Inverse image on the finite type locally constant module sheaves is the inverse image of
sheaves of `Λ`-modules.** The left vertical arrow of the module square is the chosen left adjoint
of the direct image of sheaves of `Λ`-modules, read on the finite type locally constant ones. -/
public theorem finiteTypeLocallyConstantModuleSheafPullback_comp_ι :
    finiteTypeLocallyConstantModuleSheafPullback B f Λ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) := rfl

/-- The square of `CategoryTheory.moduleSheafScalarActionEquivalence` against the two inverse
images, at the small étale sites. -/
public def etaleModuleSheafPullbackScalarSquare :
    (moduleSheafToScalarAction.{u, u + 1, u + 1, r} (SmallEtale.topology B X.1 X.2) Λ :
          Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ⥤
            (SingleObj Λ ⥤+
              Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1})) ⋙
        additiveWhiskerRight Λ ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)) ≅
      (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) ⋙
        (moduleSheafToScalarAction.{u, u + 1, u + 1, r} (SmallEtale.topology B Y.1 Y.2) Λ :
          Sheaf (SmallEtale.topology B Y.1 Y.2) (ModuleCat.{u + 1} Λ) ⥤
            (SingleObj Λ ⥤+
              Sheaf (SmallEtale.topology B Y.1 Y.2) AddCommGrpCat.{u + 1})) := by
  haveI : HasSheafify (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} := inferInstance
  haveI : HasSheafify (SmallEtale.topology B Y.1 Y.2) AddCommGrpCat.{u + 1} := inferInstance
  haveI : ReflectsLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := inferInstance
  exact (@Stacks.Sites.AbelianPullback.moduleSheafPullbackScalarSquare.{r, u, u + 1, u, u + 1,
      u + 1} _ _ _ _ (smallEtaleBaseChange B f) (SmallEtale.topology B X.1 X.2)
      (SmallEtale.topology B Y.1 Y.2) _ Λ _ _ _ _ _ _ _ _ _).symm

/-- The same square on the finite locally constant sheaves. -/
public def etaleFiniteModuleSheafPullbackScalarSquare :
    (finiteLocallyConstantModuleSheafScalarActionEquivalence
          (SmallEtale.topology B X.1 X.2) Λ).functor ⋙
        additiveWhiskerRight Λ (finiteLocallyConstantAbelianSheafPullback B f) ≅
      finiteLocallyConstantModuleSheafPullback B f Λ ⋙
        (finiteLocallyConstantModuleSheafScalarActionEquivalence
          (SmallEtale.topology B Y.1 Y.2) Λ).functor :=
  finiteModuleSheafPullbackScalarSquare.{r, u, u + 1}
    (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) Λ
    ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))
    (finiteLocallyConstantAbelianSheafPullback B f)
    (finiteLocallyConstantAbelianSheafPullback_comp_ι B f)
    (finiteLocallyConstantModuleSheafPullback B f Λ) rfl
    (etaleModuleSheafPullbackScalarSquare B f Λ)

/-- **Stacks Project, Tag 0DV6 for sheaves of modules.** Let `Λ` be a finite ring, let
`f : Y ⟶ X` be a morphism of connected schemes and let `y` be a geometric point of `Y`, with
image `x = f(y)`. Then the square

```
  finite type locally constant Λ-module sheaves on X_étale  ──→  finite Λ-π₁(X, x)-modules
                        │                                                 │
                     f^{-1}                                          restriction
                        ↓                                                 ↓
  finite type locally constant Λ-module sheaves on Y_étale  ──→  finite Λ-π₁(Y, y)-modules
```

commutes, where the horizontal arrows are the equivalence of Stacks Tag 0DV5 (3), the left
vertical arrow is the inverse image of sheaves of `Λ`-modules
(`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafPullback_comp_ι`) and the right vertical
arrow reindexes the action along the homomorphism `π₁(Y, y) ⟶ π₁(X, x)` induced by `f`
(`Stacks.GroupCohomology.finiteTypeContinuousModuleRes_comp_ι` together with
`Stacks.GroupCohomology.continuousModuleRes_comp_ι`).

The equivalence of Tag 0DV5 (3) is the equivalence of Tag 0DV5 (2) read on additive functors out
of the one-object category of `Λ`, and the only factor of that reading which depends on the
latter is postcomposition with it, so the abelian case of Tag 0DV6 transports:
`CategoryTheory.scalarActionTransportSquare`. Only the existence of the comparison is asserted,
because the abelian case is available in that form. -/
@[stacks 0DV6 "for sheaves of modules over a finite ring: the equivalence of Stacks 0DV5 (3) \
commutes with pullback, the action being reindexed along the induced homomorphism of fundamental \
groups"]
public theorem nonempty_finiteTypeLocallyConstantModuleSheafEquivalence_pullbackIso
    (y : GeometricPoint Y.1) :
    Nonempty ((finiteTypeLocallyConstantModuleSheafEquivalence B X (y.map f.hom) Λ).functor ⋙
        finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y) ≅
      finiteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
        (finiteTypeLocallyConstantModuleSheafEquivalence B Y y Λ).functor) := by
  obtain ⟨α⟩ := nonempty_finiteLocallyConstantAbelianSheafEquivalence_pullbackIso B f y
  have h₁ := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (finiteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
      (finiteTypeLocallyConstantModuleSheafBridge B Y Λ).inverse) ≪≫
      Iso.refl ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse ⋙
        finiteLocallyConstantModuleSheafPullback B f Λ))
      (finiteLocallyConstantModuleSheafScalarActionEquivalence
        (SmallEtale.topology B Y.1 Y.2) Λ).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleFiniteModuleSheafPullbackScalarSquare B f Λ).symm ≪≫
    (Functor.associator _ _ _).symm
  have h₂ := (Equivalence.conjugateSquare
    (finiteTypeContinuousModuleScalarActionEquivalence Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom)))
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup Y.1 y))
    (eqToIso (finiteTypeContinuousModuleToScalarAction_res Λ
      (etaleFundamentalGroupMap f.hom y)))).symm
  exact ⟨scalarActionTransportSquare Λ
    ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).symm.trans
      (finiteLocallyConstantModuleSheafScalarActionEquivalence
        (SmallEtale.topology B X.1 X.2) Λ))
    ((finiteTypeLocallyConstantModuleSheafBridge B Y Λ).symm.trans
      (finiteLocallyConstantModuleSheafScalarActionEquivalence
        (SmallEtale.topology B Y.1 Y.2) Λ))
    (finiteTypeContinuousModuleScalarActionEquivalence Λ
      (EtaleFundamentalGroup X.1 (y.map f.hom))).symm
    (finiteTypeContinuousModuleScalarActionEquivalence Λ (EtaleFundamentalGroup Y.1 y)).symm
    h₁ h₂ α⟩

end Modules

end AlgebraicGeometry

end
