module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationForkTransports
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardSectionsEtaleRestriction

/-!
# The sequence of Stacks 03M8 as a fork of sheaves

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `U` be a surjective étale scheme chart of `X`, let `R = U ×_X U` with its two
projections `t, s : R ⟶ U`, and let `G` be a sheaf of sets on the small étale site of `X` at the
universe of the structure rings.  Writing `τ` and `ρ` for the structure morphisms of `U` and `R`
read as étale morphisms of algebraic spaces and putting `a = τ ≫ f`, `b = ρ ≫ f`, Stacks 03M8
asserts the exactness of

`0 → f_*G → a_*(G|_U) → b_*(G|_R)`.

`AlgebraicGeometry.Space.isLimitForkDirectImage` proves the fork form of that assertion for
**presheaves** on the small étale site of `Y`: its first term is the presheaf underlying `f_*G`,
but its middle and right terms are the presheaves `V ↦ G^{ext}(U ⨯ (V ×_Y X))` and
`V ↦ G^{ext}(R ⨯ (V ×_Y X))` of sections over the products of the spaces-étale site of `X`,
which is the form the source's proof displays, and the functor those terms are restrictions
along is not shown to be continuous.  The canonical sequence, on the other hand, lives in the
category of **sheaves**.  This file transfers the one to the other.

The transfer is in two steps, and this is what has to be transferred:

* the three terms of the fork have to be identified with the presheaves underlying the three
  sheaves `f_*G`, `a_*(G|_U)` and `b_*(G|_R)`, compatibly with the three arrows.  On the left
  the identification is `Eq.refl`, by
  `AlgebraicGeometry.Space.chartBaseChangeFunctor_op_comp_eq`; in the middle and on the right it
  is `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso`, and its compatibility
  with the two parallel arrows is
  `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso`.  The first arrow is
  then *defined* by transport, as
  `AlgebraicGeometry.Space.chartDirectImageGeometricUnit`; and
* the resulting limiting fork of presheaves, all of whose terms are now the presheaves
  underlying sheaves and all of whose arrows are morphisms of those sheaves, has to be
  recognised as a limiting fork in the category of sheaves.  This is purely formal: sheaves form
  a full subcategory of presheaves, so the inclusion reflects limits of every shape.

## Main definitions

* `AlgebraicGeometry.Space.chartDirectImageSectionsIso`,
  `AlgebraicGeometry.Space.chartForkIota` and `AlgebraicGeometry.Space.chartForkParallel` name
  the sections identification and the three arrows of the fork of
  `AlgebraicGeometry.Space.isLimitForkDirectImage` at an étale scheme chart, in the spelling
  that fork carries.
* `AlgebraicGeometry.Space.chartDirectImageGeometricUnit` and
  `AlgebraicGeometry.Space.chartDirectImageGeometricParallel` are the three arrows of the
  sequence in the `a_*`/`b_*` spelling, as morphisms of the presheaves underlying the three
  sheaves.
* `AlgebraicGeometry.Space.sheafChartDirectImageUnit` and
  `AlgebraicGeometry.Space.sheafChartDirectImageParallel` are those arrows read as morphisms of
  sheaves.

## Main results

* `CategoryTheory.Sheaf.isLimitForkOfIsLimitForkHom`: **a fork of sheaves is a limit as soon as
  the fork of underlying presheaves is.**  This is the presheaf-to-sheaf step.
* `AlgebraicGeometry.Space.chartDirectImageSectionsIso_parallel` and
  `AlgebraicGeometry.Space.chartDirectImageSectionsIso_inv_parallel` are the compatibility of
  the sections identification with the parallel arrows, in the chart spelling.
* `AlgebraicGeometry.Space.isLimitForkChartDirectImageGeometric` is the limiting fork of
  presheaves with the three terms read as the presheaves underlying `f_*G`, `a_*(G|_U)` and
  `b_*(G|_R)`.
* `AlgebraicGeometry.Space.isLimitForkSheafDirectImage`: **the sequence of Stacks 03M8 is a
  limiting fork of sheaves on the small étale site of `Y`.**

## Implementation notes

The identifications and arrows of this file are stated at an étale scheme *chart* `U` of `X`,
read as an étale morphism of algebraic spaces by the comparison functor of Stacks 03G1, because
that is the datum `AlgebraicGeometry.Space.isLimitForkDirectImage` takes, while
`AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` is stated for an arbitrary
étale morphism of algebraic spaces.  The two spellings of the product factor agree by `Eq.refl`
(`AlgebraicGeometry.Space.etaleOverObj_comparisonFunctor_obj` and
`AlgebraicGeometry.Space.etaleOverMap_comparisonFunctor_map`), but a goal mentioning both is not
type-correct at `implicit` transparency, so each identification and each arrow is given a
declaration whose *declared* type is the fork's spelling and whose body is the general one; the
conversion then happens once, at elaboration, and no later step has to see through it.

The transport of the limiting fork along the two isomorphisms is
`CategoryTheory.Limits.isLimitForkOfMap` at the identity functor: the statement of that lemma
pins the first arrow by an equation, which here is `Eq.refl`, and asks for the compatibility of
the two parallel arrows with the isomorphisms, which is
`AlgebraicGeometry.Space.chartDirectImageSectionsIso_inv_parallel`.

Nothing here raises a compiler limit or disables a linter.

## What is not done

The three arrows of `AlgebraicGeometry.Space.isLimitForkSheafDirectImage` are the *geometric*
ones — the first is restriction along the counit of the product comonad of the chart and the
parallel ones are restriction along `prod.map t (𝟙)` and `prod.map s (𝟙)`, each read in the
`a_*`/`b_*` spelling.  They are not identified with the *canonical* arrows
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` and
`AlgebraicGeometry.Space.chartDirectImageParallelArrow`, which are built from the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the composition comparison of
Stacks 03G2, part (3); for the first arrow, what that identification still needs is recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardUnitArrowSections.lean`.  Nor is the whole
diagram lifted from sheaves of sets to `Mod(𝒪_Y)`; the registration of the tag therefore stays
on `AlgebraicGeometry.Space.isLimitForkDirectImage`.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₂ u₂ v u

/-! ### A limiting fork of underlying presheaves is a limiting fork of sheaves -/

namespace CategoryTheory.Sheaf

/-- **A fork of sheaves whose fork of underlying presheaves is a limit is a limit.**  The
inclusion of sheaves into presheaves is fully faithful, so it reflects limits of every shape;
in particular a fork of sheaves is a limit as soon as the fork of underlying presheaves is. -/
noncomputable def isLimitForkOfIsLimitForkHom {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] {E F H : Sheaf J A}
    {ι : E ⟶ F} {φ ψ : F ⟶ H} (w : ι ≫ φ = ι ≫ ψ)
    (h : IsLimit (Fork.ofι ι.hom
      (show ι.hom ≫ φ.hom = ι.hom ≫ ψ.hom from congrArg (fun k : E ⟶ H ↦ k.hom) w))) :
    IsLimit (Fork.ofι ι w) :=
  isLimitOfReflects (sheafToPresheaf J A) ((isLimitMapConeForkEquiv _ w).symm h)

end CategoryTheory.Sheaf

/-! ### The three terms in the chart spelling -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))

/-- The sections identification of
`AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso`, at an étale scheme *chart* `W`
of `X` read as an étale morphism of algebraic spaces by the comparison functor of Stacks 03G1.

The declaration exists so that its *declared* type carries the fork's spelling
`(comparisonFunctor X).obj W` of the product factor, which by
`AlgebraicGeometry.Space.etaleOverObj_comparisonFunctor_obj` is `Eq.refl` to the
`AlgebraicGeometry.Space.etaleOverObj` spelling that
`AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` produces. -/
noncomputable def chartDirectImageSectionsIso (W : SmallEtale B S hS X.1) :
    ((smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj W).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj W).1.hom
          ((comparisonFunctor B S hS X).obj W).2).obj G)).obj ≅
      (chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj ((comparisonFunctor B S hS X).obj W)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :=
  directImageEtaleRestrictionSectionsIso B S hS ((comparisonFunctor B S hS X).obj W).1.hom
    ((comparisonFunctor B S hS X).obj W).2 f G

variable {U R : SmallEtale B S hS X.1}

/-- The first arrow of the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`, named:
restriction along the counit of the product comonad of the chart `U`. -/
noncomputable abbrev chartForkIota (U : SmallEtale B S hS X.1) :
    ((smallEtaleDirectImage B S hS f).obj G).obj ⟶
      (chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :=
  Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
    (Functor.whiskerRight
      (NatTrans.op ((prodComonad ((comparisonFunctor B S hS X).obj U)).ε))
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj :
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj ⟶
        (prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj)

/-- A parallel arrow of the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`, named:
restriction along `prod.map t (𝟙)` for a morphism `t` of étale scheme charts of `X`. -/
noncomputable abbrev chartForkParallel (t : R ⟶ U) :
    (chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj ((comparisonFunctor B S hS X).obj U)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) ⟶
      (chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj ((comparisonFunctor B S hS X).obj R)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :=
  Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
    (Functor.whiskerRight
      (NatTrans.op (prod.functor.map ((comparisonFunctor B S hS X).map t)))
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj)

/-- The parallel arrow `a_*(G|_U) ⟶ b_*(G|_R)` of
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` attached to a morphism `t` of
étale scheme charts of `X`. -/
noncomputable def chartDirectImageGeometricParallel (t : R ⟶ U) :
    ((smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj U).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj U).1.hom
          ((comparisonFunctor B S hS X).obj U).2).obj G)).obj ⟶
      ((smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj R).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj R).1.hom
          ((comparisonFunctor B S hS X).obj R).2).obj G)).obj :=
  directImageEtaleRestrictionParallel B S hS ((comparisonFunctor B S hS X).obj U).1.hom
    ((comparisonFunctor B S hS X).obj U).2 ((comparisonFunctor B S hS X).obj R).2
    ((comparisonFunctor B S hS X).map t).hom.left
    (Over.w ((comparisonFunctor B S hS X).map t).hom) f G

/-- **The parallel arrow in the `a_*`/`b_*` spelling is the parallel arrow of the fork of
Stacks 03M8**, in the chart spelling of
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso`. -/
theorem chartDirectImageSectionsIso_parallel (t : R ⟶ U) :
    chartDirectImageGeometricParallel B S hS f G t ≫
        (chartDirectImageSectionsIso B S hS f G R).hom =
      (chartDirectImageSectionsIso B S hS f G U).hom ≫ chartForkParallel B S hS f G t :=
  directImageEtaleRestrictionParallel_sectionsIso B S hS
    ((comparisonFunctor B S hS X).obj U).1.hom ((comparisonFunctor B S hS X).obj U).2
    ((comparisonFunctor B S hS X).obj R).2 ((comparisonFunctor B S hS X).map t).hom.left
    (Over.w ((comparisonFunctor B S hS X).map t).hom) f G

/-- The previous statement with the identification moved to the other side: restriction along
`prod.map t (𝟙)` corresponds to the parallel arrow of the `a_*`/`b_*` spelling. -/
theorem chartDirectImageSectionsIso_inv_parallel (t : R ⟶ U) :
    (chartDirectImageSectionsIso B S hS f G U).inv ≫
        chartDirectImageGeometricParallel B S hS f G t =
      chartForkParallel B S hS f G t ≫ (chartDirectImageSectionsIso B S hS f G R).inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (chartDirectImageSectionsIso_parallel B S hS f G t)).trans
      (Category.assoc _ _ _).symm)

/-- The first arrow `f_*G ⟶ a_*(G|_U)` of the sequence of Stacks 03M8 in the `a_*(G|_U)`
spelling, read off the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`: restriction
along the counit of the product comonad, followed by the inverse of the sections
identification. -/
noncomputable def chartDirectImageGeometricUnit (U : SmallEtale B S hS X.1) :
    ((smallEtaleDirectImage B S hS f).obj G).obj ⟶
      ((smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj U).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj U).1.hom
          ((comparisonFunctor B S hS X).obj U).2).obj G)).obj :=
  chartForkIota B S hS f G U ≫ (chartDirectImageSectionsIso B S hS f G U).inv

/-- The fork condition in the `a_*`/`b_*` spelling: the first arrow followed by the two
parallel arrows of two morphisms `t, s` of étale scheme charts agree.

It is the fork condition `AlgebraicGeometry.Space.fork_condition_chartBaseChange` of the fork
of `AlgebraicGeometry.Space.isLimitForkDirectImage`, carried across the sections
identification by `AlgebraicGeometry.Space.chartDirectImageSectionsIso_inv_parallel`. -/
theorem fork_condition_chartDirectImageGeometric (t s : R ⟶ U) :
    chartDirectImageGeometricUnit B S hS f G U ≫
        chartDirectImageGeometricParallel B S hS f G t =
      chartDirectImageGeometricUnit B S hS f G U ≫
        chartDirectImageGeometricParallel B S hS f G s := by
  have hu : chartDirectImageGeometricUnit B S hS f G U =
      chartForkIota B S hS f G U ≫ (chartDirectImageSectionsIso B S hS f G U).inv := rfl
  rw [hu, Category.assoc, Category.assoc, chartDirectImageSectionsIso_inv_parallel,
    chartDirectImageSectionsIso_inv_parallel, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ (chartDirectImageSectionsIso B S hS f G R).inv)
    (fork_condition_chartBaseChange B S hS f
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj t s)

/-- **The sequence of Stacks 03M8 in the `a_*`/`b_*` spelling is exact, as a fork of
presheaves.**  The fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`, transported along
`AlgebraicGeometry.Space.chartDirectImageSectionsIso`, is the fork of presheaves

`(f_*G).obj → (a_*(G|_U)).obj ⇉ (b_*(G|_R)).obj`

whose first arrow is `AlgebraicGeometry.Space.chartDirectImageGeometricUnit` and whose two
parallel arrows are `AlgebraicGeometry.Space.chartDirectImageGeometricParallel` at `t` and at
`s`, and it is a limit. -/
noncomputable def isLimitForkChartDirectImageGeometric (hU : IsSurjective B S hS U.1.hom)
    {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι (chartDirectImageGeometricUnit B S hS f G U)
      (fork_condition_chartDirectImageGeometric B S hS f G t s)) :=
  isLimitForkOfMap (𝟭 _) _ (isLimitForkDirectImage B S hS f G hU hR)
    (chartDirectImageSectionsIso B S hS f G U).symm
    (chartDirectImageSectionsIso B S hS f G R).symm rfl
    (chartDirectImageSectionsIso_inv_parallel B S hS f G t)
    (chartDirectImageSectionsIso_inv_parallel B S hS f G s)
    (fork_condition_chartDirectImageGeometric B S hS f G t s)

/-! ### The fork of sheaves -/

/-- The first arrow `f_*G ⟶ a_*(G|_U)` of the sequence of Stacks 03M8 as a morphism of
*sheaves* on the small étale site of `Y`: the morphism of presheaves
`AlgebraicGeometry.Space.chartDirectImageGeometricUnit` between the presheaves underlying two
sheaves, read as a morphism of those sheaves.  Sheaves form a full subcategory of presheaves,
so this is not a construction but a reading. -/
noncomputable def sheafChartDirectImageUnit (U : SmallEtale B S hS X.1) :
    (smallEtaleDirectImage B S hS f).obj G ⟶
      (smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj U).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj U).1.hom
          ((comparisonFunctor B S hS X).obj U).2).obj G) :=
  ObjectProperty.homMk (chartDirectImageGeometricUnit B S hS f G U)

/-- The parallel arrow `a_*(G|_U) ⟶ b_*(G|_R)` of the sequence of Stacks 03M8 attached to a
morphism `t` of étale scheme charts of `X`, as a morphism of sheaves on the small étale site
of `Y`. -/
noncomputable def sheafChartDirectImageParallel (t : R ⟶ U) :
    (smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj U).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj U).1.hom
          ((comparisonFunctor B S hS X).obj U).2).obj G) ⟶
      (smallEtaleDirectImage B S hS (((comparisonFunctor B S hS X).obj R).1.hom ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ((comparisonFunctor B S hS X).obj R).1.hom
          ((comparisonFunctor B S hS X).obj R).2).obj G) :=
  ObjectProperty.homMk (chartDirectImageGeometricParallel B S hS f G t)

/-- The fork condition of the sequence of Stacks 03M8 at the level of sheaves: it is the
condition `AlgebraicGeometry.Space.fork_condition_chartDirectImageGeometric` on the underlying
presheaves, sheaves being a full subcategory of presheaves. -/
theorem fork_condition_sheafChartDirectImage (t s : R ⟶ U) :
    sheafChartDirectImageUnit B S hS f G U ≫ sheafChartDirectImageParallel B S hS f G t =
      sheafChartDirectImageUnit B S hS f G U ≫ sheafChartDirectImageParallel B S hS f G s :=
  ObjectProperty.hom_ext _ (fork_condition_chartDirectImageGeometric B S hS f G t s)

/-- **Stacks 03M8 as a fork of sheaves on the small étale site of the target.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `U` be a surjective étale scheme
chart of `X`, let `R = U ×_X U` with its two projections `t, s : R ⟶ U`, and let `G` be a sheaf
of sets on the small étale site of `X` at the universe of the structure rings.  Put `a = τ ≫ f`
and `b = ρ ≫ f` for the structure morphisms `τ` of `U` and `ρ` of `R`.  Then

`f_*G → a_*(G|_U) ⇉ b_*(G|_R)`

is a limiting fork **in the category of sheaves** on the small étale site of `Y`.

`AlgebraicGeometry.Space.isLimitForkDirectImage` is the corresponding statement for
*presheaves*, with its middle and right terms written as the sections of the extension of `G`
over `U ⨯ (V ×_Y X)` and `R ⨯ (V ×_Y X)`; this transfers it in two steps.  First the three
terms are identified with the presheaves underlying the three sheaves `f_*G`, `a_*(G|_U)` and
`b_*(G|_R)`: on the left this is `Eq.refl`
(`AlgebraicGeometry.Space.chartBaseChangeFunctor_op_comp_eq`) and in the middle and on the
right it is `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso`, whose
compatibility with the parallel arrows is
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso`.  Then the fork of
underlying presheaves is reflected into sheaves by
`CategoryTheory.Sheaf.isLimitForkOfIsLimitForkHom`, the inclusion of sheaves into presheaves
being fully faithful.

The three arrows are the geometric ones: the first is restriction along the counit of the
product comonad of the chart, read in the `a_*(G|_U)` spelling, and the parallel ones are
restriction along `prod.map t (𝟙)` and `prod.map s (𝟙)`.  Identifying them with the *canonical*
arrows of `AlgebraicGeometry.Space.chartDirectImageUnitArrow` and
`AlgebraicGeometry.Space.chartDirectImageParallelArrow` — built from the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the composition comparison of
direct images of Stacks 03G2, part (3) — is a separate matter and is not done here. -/
noncomputable def isLimitForkSheafDirectImage (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι (sheafChartDirectImageUnit B S hS f G U)
      (fork_condition_sheafChartDirectImage B S hS f G t s)) :=
  Sheaf.isLimitForkOfIsLimitForkHom _
    (isLimitForkChartDirectImageGeometric B S hS f G hU hR)

end AlgebraicGeometry.Space

end
