module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcisionPushforward

/-!
# The underived base change of a square of ringed spaces is a mate

For a commutative square of ringed spaces

```
U --i--> X
|        |
g        f
v        v
V --j--> Y
```

`Stacks.Cohomology.pushforwardRestrictMap` is the canonical base-change map
`f_* ⋙ j^* ⟶ i^* ⋙ g_*`, built as the adjoint transpose under `j^* ⊣ j_*` of `f_*` applied to
the unit of `i^* ⊣ i_*`, followed by the identification `i_* f_* ≅ g_* j_*` of the two composite
direct images.  The *derived* base change of [Stacks, Tag 08HY],
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, is built differently: it is the
**mate**, under the two derived adjunctions `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*`, of the comparison of
the two iterated derived pullbacks around the square.

This file shows that the underived map is the mate, under `f^* ⊣ f_*` and `g^* ⊣ g_*`, of the
comparison of the two iterated *underived* pullbacks — that is, that the two base-change maps are
built by the same recipe, one level down.

## Main definitions

* `Stacks.Cohomology.pullbackCompSquare`: the comparison `j^* ⋙ g^* ⟶ f^* ⋙ i^*` of the two
  iterated pullbacks around the square, as a `CategoryTheory.TwoSquare`.  This is the underived
  counterpart of `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare`.
* `Stacks.Cohomology.pushforwardCompSquare`: the comparison `i_* ⋙ f_* ⟶ g_* ⋙ j_*` of the two
  iterated direct images, as a `CategoryTheory.TwoSquare`.  Its components are identities, the
  direct image of sheaves of modules being multiplicative in the morphism on the nose.

## Main results

* `Stacks.Cohomology.conjugateEquiv_pullbackCompSquare`: **the two comparisons are conjugate.**
  Under `CategoryTheory.conjugateEquiv` for the two composite adjunctions
  `f^* ⋙ i^* ⊣ i_* ⋙ f_*` and `j^* ⋙ g^* ⊣ g_* ⋙ j_*`, the pullback comparison corresponds to
  the pushforward comparison.
* `Stacks.Cohomology.pushforwardRestrictMap_app`: the canonical base-change map at an object,
  written out.
* `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv`: **the canonical base-change map is the
  mate of the pullback comparison** under `f^* ⊣ f_*` and `g^* ⊣ g_*`.
* `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv`:
  that statement at the Cartesian square of the restriction of an open immersion to a closed
  subset, which is the square excision for `ℋ ⁿ_Z ⋙ i_*` runs on.

## Implementation notes

**Why the mate description and not the transpose description.**  `pushforwardRestrictMap` is
defined as a transpose along *one* adjunction, `j^* ⊣ j_*`, of a transformation assembled from the
unit of `i^* ⊣ i_*`; that is the "horizontal" mate of the pushforward comparison.  The derived
base change of [Stacks, Tag 08HY] is the "vertical" mate, along `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*`,
of the pullback comparison.  Mathlib's
`CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm` says that iterating the mate operation on
a square of four adjunctions gives the conjugate, which is exactly what turns the first
description into the second; `conjugateEquiv_pullbackCompSquare` supplies the conjugacy of the two
comparisons that it is applied to, and that in turn is
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom` — the characterisation of the
pullback composition isomorphism of [Stacks, Tag 0096] — once at `(i, f)` and once at `(g, j)`,
with a transport along the commutativity of the square in between.  No description of either map
on sections is used anywhere.

**The transport along the commutativity of the square.**  The two iterated pullbacks are
identified with `(i ≫ f)^*` and `(g ≫ j)^*`, and these are compared by `eqToHom` along
`w : i ≫ f = g ≫ j`.  `conjugateEquiv_eqToHom_modulePullback` computes the conjugate of that
`eqToHom`: after `subst` the two adjunctions are the same and the transformation is the identity,
whose conjugate is the identity.  This is the only place the commutativity of the square enters,
and it enters as an equality of morphisms of ringed spaces rather than as a Cartesian-square
hypothesis: nothing here needs the square to be Cartesian, and nothing needs either arrow to be
an open immersion.

## References

* [Stacks Project, Lemma 20.28.6 (Tag 08FE)](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Section 17.6 (Tag 0096)](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology

variable {X Y U V : RingedSpace.{u, u}} (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)

/-! ### The two comparisons of iterated functors around a commutative square -/

/-- **The comparison of the two iterated pullbacks around a commutative square of ringed
spaces**, `j^* ⋙ g^* ⟶ f^* ⋙ i^*`, as a two-square.  Both composites are pullback along the
common composite `i ≫ f = g ≫ j`, by the composition isomorphism
`RingedSpaceModuleAdjunction.modulePullbackComp` of [Stacks, Tag 0096], and the comparison is the
resulting isomorphism.

This is the underived counterpart of
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare`, of which the derived base change of
[Stacks, Tag 08HY] is the mate. -/
def pullbackCompSquare (w : i ≫ f = g ≫ j) :
    TwoSquare (modulePullback j) (modulePullback f) (modulePullback g) (modulePullback i) :=
  TwoSquare.mk _ _ _ _ ((modulePullbackComp g j).inv ≫
    eqToHom (congrArg modulePullback w.symm) ≫ (modulePullbackComp i f).hom)

/-- **The comparison of the two iterated direct images around a commutative square of ringed
spaces**, `i_* ⋙ f_* ⟶ g_* ⋙ j_*`, as a two-square.  The direct image of sheaves of modules is
multiplicative in the morphism on the nose, so both composites are the direct image along the
common composite and the comparison has identity components.

This is the transformation that `Stacks.Cohomology.pushforwardRestrictMap` is assembled from. -/
def pushforwardCompSquare (w : i ≫ f = g ≫ j) :
    TwoSquare (modulePushforward i) (modulePushforward g) (modulePushforward f)
      (modulePushforward j) :=
  TwoSquare.mk _ _ _ _ ((modulePushforwardComp i f).hom ≫
    eqToHom (congrArg modulePushforward w) ≫ (modulePushforwardComp g j).inv)

/-! ### The two comparisons are conjugate -/

/-- The conjugate of the comparison of the pullbacks along two equal morphisms of ringed spaces is
the comparison of the direct images along them.  Both transformations are identities once the two
morphisms are identified. -/
theorem conjugateEquiv_eqToHom_modulePullback {a b : U ⟶ Y} (h : a = b) :
    conjugateEquiv (modulePullbackPushforwardAdjunction a)
        (modulePullbackPushforwardAdjunction b)
        (eqToHom (congrArg modulePullback h.symm)) =
      eqToHom (congrArg modulePushforward h) := by
  subst h
  simp

/-- The conjugate of the inverse of the pullback composition isomorphism of [Stacks, Tag 0096] is
the inverse of the pushforward composition isomorphism: conjugation takes a pair of mutually
inverse transformations to a pair of mutually inverse transformations, so this follows from
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom`. -/
theorem conjugateEquiv_modulePullbackComp_inv :
    conjugateEquiv (modulePullbackPushforwardAdjunction (g ≫ j))
        ((modulePullbackPushforwardAdjunction j).comp
          (modulePullbackPushforwardAdjunction g))
        (modulePullbackComp g j).inv =
      (modulePushforwardComp g j).inv := by
  have h := conjugateEquiv_comm
    ((modulePullbackPushforwardAdjunction j).comp (modulePullbackPushforwardAdjunction g))
    (modulePullbackPushforwardAdjunction (g ≫ j))
    (α := (modulePullbackComp g j).hom) (β := (modulePullbackComp g j).inv)
    (modulePullbackComp g j).inv_hom_id
  rw [conjugateEquiv_modulePullbackComp_hom] at h
  exact (cancel_epi (modulePushforwardComp g j).hom).mp
    (h.trans ((modulePushforwardComp g j).hom_inv_id).symm)

/-- **The pullback comparison of a commutative square of ringed spaces is conjugate to the
pushforward comparison.**  Under the conjugation bijection for the two composite adjunctions
`f^* ⋙ i^* ⊣ i_* ⋙ f_*` and `j^* ⋙ g^* ⊣ g_* ⋙ j_*`, the comparison `pullbackCompSquare` of the
two iterated pullbacks corresponds to the comparison `pushforwardCompSquare` of the two iterated
direct images.

This is `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom` at `(i, f)` and at
`(g, j)`, with `conjugateEquiv_eqToHom_modulePullback` mediating. -/
theorem conjugateEquiv_pullbackCompSquare (w : i ≫ f = g ≫ j) :
    conjugateEquiv ((modulePullbackPushforwardAdjunction f).comp
          (modulePullbackPushforwardAdjunction i))
        ((modulePullbackPushforwardAdjunction j).comp
          (modulePullbackPushforwardAdjunction g))
        (pullbackCompSquare f i j g w) =
      (pushforwardCompSquare f i j g w) := by
  dsimp only [pullbackCompSquare, pushforwardCompSquare, TwoSquare.mk]
  rw [← conjugateEquiv_modulePullbackComp_hom i f, ← conjugateEquiv_eqToHom_modulePullback w,
    ← conjugateEquiv_modulePullbackComp_inv j g, ← Category.assoc, conjugateEquiv_comp,
    conjugateEquiv_comp]

/-! ### The canonical base-change map is the mate of the pullback comparison -/

/-- **The canonical base-change map of a commutative square of ringed spaces, at an object.**  It
is `j^*` applied to the composite of `f_*` of the unit of `i^* ⊣ i_*` with the comparison of the
two iterated direct images, followed by the counit of `j^* ⊣ j_*`. -/
theorem pushforwardRestrictMap_app (w : i ≫ f = g ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (pushforwardRestrictMap f i j g w).app M =
      (modulePullback j).map ((modulePushforward f).map
          ((modulePullbackPushforwardAdjunction i).unit.app M)) ≫
        (modulePullback j).map
            ((pushforwardCompSquare f i j g w).app ((modulePullback i).obj M)) ≫
          (modulePullbackPushforwardAdjunction j).counit.app
            ((modulePushforward g).obj ((modulePullback i).obj M)) := by
  dsimp only [pushforwardRestrictMap, pushforwardCompSquare, TwoSquare.mk]
  rw [Adjunction.homEquiv_symm_apply]
  change (modulePullback j).map
    (𝟙 _ ≫ (modulePushforward f).map ((modulePullbackPushforwardAdjunction i).unit.app M) ≫ 𝟙 _ ≫
      _ ≫ 𝟙 _) ≫
    (𝟙 _ ≫ (modulePullbackPushforwardAdjunction j).counit.app
      ((modulePushforward g).obj ((modulePullback i).obj M)) ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  congr 2

/-- The canonical base-change map is the mate, under `i^* ⊣ i_*` and `j^* ⊣ j_*`, of the
comparison of the two iterated direct images.  This is `pushforwardRestrictMap_app` read back as
an equality of natural transformations. -/
theorem pushforwardRestrictMap_eq_mateEquiv_symm (w : i ≫ f = g ≫ j) :
    pushforwardRestrictMap f i j g w =
      (mateEquiv (modulePullbackPushforwardAdjunction i)
        (modulePullbackPushforwardAdjunction j)).symm (pushforwardCompSquare f i j g w) := by
  refine NatTrans.ext (funext fun M => ?_)
  rw [pushforwardRestrictMap_app]
  simp [mateEquiv]

/-- **The canonical base-change map of a commutative square of ringed spaces is the mate of the
comparison of the two iterated pullbacks**, under the adjunctions `f^* ⊣ f_*` and `g^* ⊣ g_*`.

This is the recipe by which the derived base change of [Stacks, Tag 08HY],
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, is defined — the mate of
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` under the derived adjunctions of
[Stacks, Tag 079W] — so this identifies the two constructions one level down.

No hypothesis on the square beyond its commutativity: it need not be Cartesian and neither arrow
need be an open immersion. -/
theorem pushforwardRestrictMap_eq_mateEquiv (w : i ≫ f = g ≫ j) :
    pushforwardRestrictMap f i j g w =
      mateEquiv (modulePullbackPushforwardAdjunction f)
        (modulePullbackPushforwardAdjunction g) (pullbackCompSquare f i j g w) := by
  have key := iterated_mateEquiv_conjugateEquiv_symm
    (modulePullbackPushforwardAdjunction f) (modulePullbackPushforwardAdjunction g)
    (modulePullbackPushforwardAdjunction j) (modulePullbackPushforwardAdjunction i)
    (pushforwardCompSquare f i j g w)
  rw [← pushforwardRestrictMap_eq_mateEquiv_symm] at key
  refine (Equiv.symm_apply_eq _).mp (key.trans ?_)
  change TwoSquare.mk _ _ _ _
      ((conjugateEquiv ((modulePullbackPushforwardAdjunction f).comp
          (modulePullbackPushforwardAdjunction i))
        ((modulePullbackPushforwardAdjunction j).comp
          (modulePullbackPushforwardAdjunction g))).symm
        (pushforwardCompSquare f i j g w)) = pullbackCompSquare f i j g w
  rw [← conjugateEquiv_pullbackCompSquare f i j g w, Equiv.symm_apply_apply]

namespace SupportedComplexes

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-- **The underived base change `i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*` of the Cartesian square of the
restriction is the mate of the comparison of the two iterated pullbacks around that square**,
under the adjunctions `i^* ⊣ i_*` on `X` and `i'^* ⊣ i'_*` on `X'`.

This is `Stacks.Cohomology.pushforwardRestrictMap_eq_mateEquiv` read at the square of
`isPullback_closedSubsetRestriction`, whose base-change map
`closedSubsetPushforwardPullbackNatIso` is by
`closedSubsetPushforwardPullbackNatIso_hom`.  It is the form in which this isomorphism is to be
compared with the derived base change of [Stacks, Tag 08HY] attached to the same square, which is
the mate of the derived comparison of the two iterated derived pullbacks. -/
theorem closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv :
    (closedSubsetPushforwardPullbackNatIso f Z).hom =
      mateEquiv (modulePullbackPushforwardAdjunction (closedSubsetInclusion X Z))
        (modulePullbackPushforwardAdjunction
          (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (pullbackCompSquare (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))
          (isPullback_closedSubsetRestriction f Z).w) :=
  (closedSubsetPushforwardPullbackNatIso_hom f Z).trans
    (pushforwardRestrictMap_eq_mateEquiv (closedSubsetInclusion X Z)
      (closedSubsetRestriction f Z) f (closedSubsetInclusion X' (closedSubsetPreimage f Z))
      (isPullback_closedSubsetRestriction f Z).w)

end SupportedComplexes

end Stacks.Cohomology

end
