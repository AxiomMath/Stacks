module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit

/-!
# The chart projection of the composition comparison of direct images

Let `h : D ⟶ A` and `g : A ⟶ C` be representable morphisms of algebraic spaces over a scheme
`S` contained in a big fppf site `B`.  For a sheaf of sets `F` on the small étale site of `D`
and an étale scheme chart `V` of `C`, the direct image along a representable morphism has a
*chart projection* `AlgebraicGeometry.Space.chartSetProj`: sections of `f_*F` over `V` restrict
to sections of `F` over the base-changed chart `V ×_C D`.  This file computes the chart
projection of the composition comparison of Stacks 03G2, part (3).

The answer is the only one it could be.  The iterated chart projection of a section of
`g_*(h_*F)` lands in the sections of `F` over `(V ×_C A) ×_A D`, the chart projection of the
comparison lands in the sections over `V ×_C D`, and the two charts are canonically isomorphic;
the comparison of them is `AlgebraicGeometry.Space.chartBaseChangeCompComparison`, and the two
projections agree after restriction along it.

## Main definitions

* `AlgebraicGeometry.Space.compChartIndex`: the étale scheme chart `(V ×_C A) ×_A D` of `D`,
  read as a chart above the algebraic space `D ×_C V` through
  `AlgebraicGeometry.Space.chartBaseChangeComp`.
* `AlgebraicGeometry.Space.chartBaseChangeCompComparison`: **the canonical comparison of charts**
  `V ×_C D ⟶ (V ×_C A) ×_A D`.  It is the unique morphism of indices out of the initial index
  `AlgebraicGeometry.Space.smallBaseChangeIndex` of `h ≫ g`, read on underlying charts; no
  universal property of a fibre product has to be invoked by hand, because the index category
  already records the compatibility.

* `AlgebraicGeometry.Space.isInitial_of_isIso_hom`: an index whose structure morphism is an
  isomorphism is initial.  This is the content of
  `AlgebraicGeometry.Space.smallBaseChangeIndex_isInitial` with the comparison isomorphism of
  base changes replaced by an arbitrary isomorphism, and it is what makes
  `AlgebraicGeometry.Space.compChartIndex` an initial index too.

## Main results

* `AlgebraicGeometry.Space.chartSetProj_smallToposMorphismTypeU_comp`: **the chart projection of
  the composition comparison of direct images of Stacks 03G2, part (3), is the iterated chart
  projection**, read along `AlgebraicGeometry.Space.chartBaseChangeCompComparison`.
* `AlgebraicGeometry.Space.chartBaseChangeCompComparison_counit`: **the comparison of charts is
  compatible with the counits** of the base-change adjunctions of Stacks 03LP: following it with
  the two cartesian projections is the cartesian projection of the composite.  This is the form
  in which a consumer that reads the chart projection of a unit — where the chart projection is
  restriction along the counit — can chain the previous result.

## Implementation notes

Everything here is at the level of sheaves of **sets**; no module enters, and that is what keeps
the statements elaborable.  The module-level analogue forces the elaborator to reconcile the
sections of a direct image of modules with those of the direct image of the underlying sheaf of
sets, which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnit.lean` record as costing a
large fraction of the heartbeat budget each time it is done.

Three spellings that one might expect to need a lemma are definitional equalities (each holds by
`rfl`), and the proofs lean on them:

* `((smallEtaleDirectImageRanIso f).hom.app F).hom.app (op V)` is
  `((smallEtaleComparisonRanIso X).hom.app F).hom.app (op (chartBaseChange f V))` — the direct
  image is restriction along the comparison functor of a cartesian direct image, and sections
  over `V` of the outer are sections over `X ×_Y V` of the inner;
* `((spacesBaseChange_pushforward_compTypeU f g).hom.app G).hom.app (op W)` is restriction along
  `((spacesBaseChange_comp f g).inv.app W).op` — this is what
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` unfolds to;
* `(smallBaseChangeIndex f hf V).hom.unop` is `(smallBaseChangeComparisonIso f hf V).hom`.

The comparison of charts is produced from initiality rather than from `hrep.lift`: an index of
the Kan-extension limit *is* a chart together with the compatibility datum, so the unique
morphism of indices carries the compatibility for free, and
`AlgebraicGeometry.Space.chartBaseChangeMap_comp` then reads off the identity with the cartesian
projections that `AlgebraicGeometry.Space.chartBaseChangeCompComparison_counit` needs.  Going the
other way — defining the comparison by the universal property and *then* proving it is a
morphism of indices — would duplicate that compatibility.

Two further elaboration facts.

* Instance search does **not** close
  `IsIso ((smallBaseChangeIndex h hreph _).hom.unop ≫ chartBaseChangeComp h g V _)` even though
  it closes each factor on its own; the composite is therefore assembled explicitly with
  `CategoryTheory.IsIso.comp_isIso'`.
* `AlgebraicGeometry.Space.chartBaseChangeMap_smallBaseChangeIndex` must not be rewritten
  *inside a hypothesis*: the type of a chart morphism names the chart, so replacing the chart
  morphism by the cartesian projection leaves the hypothesis's type referring to the old chart
  and the rewrite is rejected as not type-correct.  The identities are chained with
  `Eq.trans` and `congrArg` instead, where the two spellings of the chart are only ever compared
  up to definitional equality.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Initial indices -/

/-- **An index whose structure morphism is an isomorphism is initial.**  An object of the index
category of the Kan-extension limit over an étale algebraic space `W` of `X` is an étale scheme
chart of `X` together with a morphism from its image to `W`; the comparison functor of
Stacks 03G1 is fully faithful, so if that morphism is invertible, every other index factors
through it by a unique morphism of charts.

This is `AlgebraicGeometry.Space.smallBaseChangeIndex_isInitial` with the comparison isomorphism
of the two base changes replaced by an arbitrary isomorphism. -/
noncomputable def isInitial_of_isIso_hom (X : AlgebraicSpaces B S hS)
    {W : SpacesEtale B S hS X} (m : StructuredArrow (op W) (comparisonFunctor B S hS X).op)
    (hm : IsIso m.hom.unop) : IsInitial m := by
  haveI := hm
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  refine IsInitial.ofUniqueHom (fun j => StructuredArrow.homMk
    ((comparisonFunctor B S hS X).preimage (j.hom.unop ≫ inv m.hom.unop)).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change (comparisonFunctor B S hS X).map
        ((comparisonFunctor B S hS X).preimage (j.hom.unop ≫ inv m.hom.unop)) ≫ m.hom.unop =
      j.hom.unop
    rw [Functor.map_preimage, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro j n
    have hcomm : (comparisonFunctor B S hS X).map n.right.unop ≫ m.hom.unop = j.hom.unop :=
      congrArg Quiver.Hom.unop (StructuredArrow.w n)
    have hfac : (comparisonFunctor B S hS X).map n.right.unop =
        j.hom.unop ≫ inv m.hom.unop := by
      rw [← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    refine StructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj
      ((comparisonFunctor B S hS X).map_injective ?_))
    exact hfac.trans (Functor.map_preimage (comparisonFunctor B S hS X)
      (j.hom.unop ≫ inv m.hom.unop)).symm

variable {X Y : AlgebraicSpaces B S hS}

/-- **The base-changed index has an invertible structure morphism**: that morphism is, by
definition, the comparison isomorphism `AlgebraicGeometry.Space.smallBaseChangeComparisonIso` of
the two base changes.  The two spellings are definitionally equal, so the instance is
`inferInstanceAs`. -/
instance isIso_smallBaseChangeIndex_hom_unop (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsIso (smallBaseChangeIndex B S hS f hf V).hom.unop :=
  inferInstanceAs (IsIso (smallBaseChangeComparisonIso B S hS f hf V).hom)

/-! ### The composite index and the comparison of charts -/

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-- **The iterated base-changed chart, as an index for the composite.**  The chart
`(V ×_C A) ×_A D` of `D`, read as an étale scheme chart above the algebraic space `D ×_C V`
through `AlgebraicGeometry.Space.chartBaseChangeComp`.

It is *not* the chosen initial index `AlgebraicGeometry.Space.smallBaseChangeIndex` of `h ≫ g`,
whose chart is `V ×_C D`; it is initial all the same, by
`AlgebraicGeometry.Space.isInitial_compChartIndex`. -/
noncomputable abbrev compChartIndex (V : SmallEtale B S hS C.1) :
    StructuredArrow (op (chartBaseChange B S hS (h ≫ g) V)) (comparisonFunctor B S hS D).op :=
  StructuredArrow.mk
    ((chartBaseChangeComp B S hS h g V (smallBaseChangeIndex B S hS g hrepg V)).op ≫
      (smallBaseChangeIndex B S hS h hreph
        ((smallBaseChange B S hS g hrepg).obj V)).hom)

/-- **The chart morphism out of the base-changed chart of `g` is invertible**: it is the base
change along `h` of the comparison isomorphism of the base changes along `g`, followed by the
composition comparison `AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2,
part (2). -/
instance isIso_chartBaseChangeComp_smallBaseChangeIndex (V : SmallEtale B S hS C.1) :
    IsIso (chartBaseChangeComp B S hS h g V (smallBaseChangeIndex B S hS g hrepg V)) := by
  rw [chartBaseChangeComp]
  infer_instance

/-- **The structure morphism of the iterated base-changed index is invertible**: it is a
composite of the two isomorphisms above.  See the implementation notes for why the composite is
assembled with `CategoryTheory.IsIso.comp_isIso'` rather than left to instance search. -/
instance isIso_compChartIndex_hom_unop (V : SmallEtale B S hS C.1) :
    IsIso (compChartIndex B S hS h g hreph hrepg V).hom.unop :=
  IsIso.comp_isIso'
    (isIso_smallBaseChangeIndex_hom_unop B S hS h hreph
      ((smallBaseChange B S hS g hrepg).obj V))
    (isIso_chartBaseChangeComp_smallBaseChangeIndex B S hS h g hrepg V)

/-- **The iterated base-changed chart is an initial index too.**  Its structure morphism is a
composite of two isomorphisms: the comparison isomorphism of the base changes along `h`, and the
base change along `h` of the one along `g` followed by the composition comparison
`AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2, part (2). -/
noncomputable def isInitial_compChartIndex (V : SmallEtale B S hS C.1) :
    IsInitial (compChartIndex B S hS h g hreph hrepg V) :=
  isInitial_of_isIso_hom B S hS D (compChartIndex B S hS h g hreph hrepg V)
    (isIso_compChartIndex_hom_unop B S hS h g hreph hrepg V)

/-- **The canonical comparison of charts** `V ×_C D ⟶ (V ×_C A) ×_A D`: the unique morphism of
indices from the iterated base-changed chart to the base-changed chart of the composite, read on
underlying charts.  Both are initial, so it is an isomorphism; what is used below is only that it
is a morphism of indices. -/
noncomputable def chartBaseChangeCompComparison (V : SmallEtale B S hS C.1) :
    (smallBaseChange B S hS (h ≫ g) hrephg).obj V ⟶
      (smallBaseChange B S hS h hreph).obj ((smallBaseChange B S hS g hrepg).obj V) :=
  ((isInitial_compChartIndex B S hS h g hreph hrepg V).to
    (smallBaseChangeIndex B S hS (h ≫ g) hrephg V)).right.unop

/-- The chart projection at the base-changed chart of the composite is the chart projection at
the iterated base-changed chart, restricted along the comparison of charts.  This is the cone
condition of the Kan-extension limit at the unique morphism of indices. -/
theorem ranChartCone_π_smallBaseChangeIndex_comp
    (F : (SmallEtale B S hS D.1)ᵒᵖ ⥤ Type u) (V : SmallEtale B S hS C.1)
    (a : ((comparisonFunctor B S hS D).op.ran.obj F).obj
      (op (chartBaseChange B S hS (h ≫ g) V))) :
    (ranChartCone B S hS D F (chartBaseChange B S hS (h ≫ g) V)).π.app
        (smallBaseChangeIndex B S hS (h ≫ g) hrephg V) a =
      F.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        ((ranChartCone B S hS D F (chartBaseChange B S hS (h ≫ g) V)).π.app
          (compChartIndex B S hS h g hreph hrepg V) a) :=
  (ranChartCone_π_comp B S hS D F (chartBaseChange B S hS (h ≫ g) V)
    ((isInitial_compChartIndex B S hS h g hreph hrepg V).to
      (smallBaseChangeIndex B S hS (h ≫ g) hrephg V)) a).symm

/-! ### The composition comparison, read in the Kan-extension picture -/

/-- `AlgebraicGeometry.Space.ranSpacesHom_comp_formula` at the identity homomorphism: the
composition comparison of Stacks 03G2, part (3), read between the Kan-extension forms of the
direct images, is the transported identity followed by the cartesian comparison. -/
theorem ranSpacesHom_comp_formula_id
    (F : Sheaf (SmallEtale.topology B S hS D.1) (Type u)) :
    (smallEtaleDirectImageRanIso B S hS g).inv.app
          ((smallEtaleDirectImage B S hS h).obj F) ≫
        (smallToposMorphismTypeU_comp B S hS h g).hom.app F ≫
        (smallEtaleDirectImageRanIso B S hS (h ≫ g)).hom.app F =
      (smallEtaleComparisonRestriction B S hS C).map
        ((spacesDirectImage B S hS g).map
            (ranSpacesHom B S hS h F ((smallEtaleDirectImage B S hS h).obj F) (𝟙 _)) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS h g).hom.app
            ((smallEtaleComparisonRan B S hS D).obj F)) := by
  refine Eq.trans ?_ (ranSpacesHom_comp_formula B S hS h g F
    ((smallEtaleDirectImage B S hS h).obj F) (𝟙 _))
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The comparison of Stacks 03G2, part (3), on a section over an étale scheme chart `V` of `C`,
read in the Kan-extension form of the direct image along `h ≫ g`: it is the transported identity
homomorphism, followed by restriction along the composition comparison of base changes. -/
theorem comparisonRanIso_smallToposMorphismTypeU_comp_app
    (F : Sheaf (SmallEtale.topology B S hS D.1) (Type u)) (V : SmallEtale B S hS C.1)
    (w : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS h).obj F)).obj.obj (op V)) :
    ((smallEtaleComparisonRanIso B S hS D).hom.app F).hom.app
        (op (chartBaseChange B S hS (h ≫ g) V))
        (((smallToposMorphismTypeU_comp B S hS h g).hom.app F).hom.app (op V) w) =
      ((comparisonFunctor B S hS D).op.ran.obj F.obj).map
        ((spacesBaseChange_comp B S hS h g).inv.app
          ((comparisonFunctor B S hS C).obj V)).op
        ((ranSpacesHom B S hS h F ((smallEtaleDirectImage B S hS h).obj F) (𝟙 _)).hom.app
          (op (chartBaseChange B S hS g V))
          (((smallEtaleComparisonRanIso B S hS A).hom.app
            ((smallEtaleDirectImage B S hS h).obj F)).hom.app
            (op (chartBaseChange B S hS g V)) w)) := by
  have hinv : ((smallEtaleDirectImageRanIso B S hS g).inv.app
        ((smallEtaleDirectImage B S hS h).obj F)).hom.app (op V)
        (((smallEtaleDirectImageRanIso B S hS g).hom.app
          ((smallEtaleDirectImage B S hS h).obj F)).hom.app (op V) w) = w :=
    congrArg (fun m : (smallEtaleDirectImage B S hS g).obj
          ((smallEtaleDirectImage B S hS h).obj F) ⟶
        (smallEtaleDirectImage B S hS g).obj ((smallEtaleDirectImage B S hS h).obj F) ↦
      m.hom.app (op V) w)
      ((smallEtaleDirectImageRanIso B S hS g).hom_inv_id_app
        ((smallEtaleDirectImage B S hS h).obj F))
  refine Eq.trans ?_ (congrArg (fun m ↦ m.hom.app (op V)
    (((smallEtaleDirectImageRanIso B S hS g).hom.app
      ((smallEtaleDirectImage B S hS h).obj F)).hom.app (op V) w))
    (ranSpacesHom_comp_formula_id B S hS h g F))
  exact congrArg (fun y ↦ ((smallEtaleComparisonRanIso B S hS D).hom.app F).hom.app
      (op (chartBaseChange B S hS (h ≫ g) V))
      (((smallToposMorphismTypeU_comp B S hS h g).hom.app F).hom.app (op V) y)) hinv.symm

/-! ### The chart projection of the composition comparison -/

/-- The chart projection at the iterated base-changed chart of the comparison of Stacks 03G2,
part (3), is the iterated chart projection.  This is
`AlgebraicGeometry.Space.ranProj_ranSpacesHom_comp` at the identity homomorphism and at the two
initial indices. -/
theorem ranChartCone_π_compChartIndex_comparison
    (F : Sheaf (SmallEtale.topology B S hS D.1) (Type u)) (V : SmallEtale B S hS C.1)
    (w : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS h).obj F)).obj.obj (op V)) :
    (ranChartCone B S hS D F.obj (chartBaseChange B S hS (h ≫ g) V)).π.app
        (compChartIndex B S hS h g hreph hrepg V)
        (((smallEtaleComparisonRanIso B S hS D).hom.app F).hom.app
          (op (chartBaseChange B S hS (h ≫ g) V))
          (((smallToposMorphismTypeU_comp B S hS h g).hom.app F).hom.app (op V) w)) =
      chartSetProj B S hS h hreph F ((smallBaseChange B S hS g hrepg).obj V)
        (chartSetProj B S hS g hrepg ((smallEtaleDirectImage B S hS h).obj F) V w) := by
  have hstep := ranProj_ranSpacesHom_comp B S hS h g F
    ((smallEtaleDirectImage B S hS h).obj F) (𝟙 _) V
    (smallBaseChangeIndex B S hS g hrepg V)
    (smallBaseChangeIndex B S hS h hreph ((smallBaseChange B S hS g hrepg).obj V))
    (((smallEtaleComparisonRanIso B S hS A).hom.app
      ((smallEtaleDirectImage B S hS h).obj F)).hom.app
      (op (chartBaseChange B S hS g V)) w)
  rw [Category.id_comp] at hstep
  refine Eq.trans ?_ (Eq.trans ((ranProj_app_apply B S hS D
    (chartBaseChange B S hS (h ≫ g) V) F (compChartIndex B S hS h g hreph hrepg V) _).symm.trans
      hstep) ?_)
  · exact congrArg
      ((ranChartCone B S hS D F.obj (chartBaseChange B S hS (h ≫ g) V)).π.app
        (compChartIndex B S hS h g hreph hrepg V))
      (comparisonRanIso_smallToposMorphismTypeU_comp_app B S hS h g F V w)
  · exact ranProj_app_apply B S hS D
      (chartBaseChange B S hS h ((smallBaseChange B S hS g hrepg).obj V)) F
      (smallBaseChangeIndex B S hS h hreph ((smallBaseChange B S hS g hrepg).obj V)) _

/-- **The chart projection of the composition comparison of direct images of Stacks 03G2,
part (3), is the iterated chart projection**, read along the canonical comparison of charts
`AlgebraicGeometry.Space.chartBaseChangeCompComparison`.

Both sides are sections of `F` over `V ×_C D`: the left-hand side projects a section of
`(h ≫ g)_*F` over `V` there directly, the right-hand side projects a section of `g_*(h_*F)`
over `V` first to `V ×_C A` and then to `(V ×_C A) ×_A D`, and restricts along the comparison of
the two charts. -/
theorem chartSetProj_smallToposMorphismTypeU_comp
    (F : Sheaf (SmallEtale.topology B S hS D.1) (Type u)) (V : SmallEtale B S hS C.1)
    (w : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS h).obj F)).obj.obj (op V)) :
    chartSetProj B S hS (h ≫ g) hrephg F V
        (((smallToposMorphismTypeU_comp B S hS h g).hom.app F).hom.app (op V) w) =
      F.obj.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartSetProj B S hS h hreph F ((smallBaseChange B S hS g hrepg).obj V)
          (chartSetProj B S hS g hrepg ((smallEtaleDirectImage B S hS h).obj F) V w)) :=
  (ranChartCone_π_smallBaseChangeIndex_comp B S hS h g hreph hrepg hrephg F.obj V _).trans
    (congrArg (F.obj.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op)
      (ranChartCone_π_compChartIndex_comparison B S hS h g hreph hrepg F V w))

/-! ### The comparison of charts against the cartesian projections -/

/-- **The chart morphism of the iterated base-changed index is the composite of the two
cartesian projections.**  This is
`AlgebraicGeometry.Space.chartBaseChangeMap_comp_chart`, which factors the chart morphism of a
composite through the middle chart, followed by the computation
`AlgebraicGeometry.Space.chartBaseChangeMap_smallBaseChangeIndex` of the chart morphism at an
initial index. -/
theorem chartBaseChangeMap_compChartIndex (V : SmallEtale B S hS C.1) :
    chartBaseChangeMap B S hS (h ≫ g) V (compChartIndex B S hS h g hreph hrepg V) =
      hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom ≫ hrepg.snd V.1.hom := by
  refine Eq.trans (chartBaseChangeMap_comp_chart B S hS h g V
    (smallBaseChangeIndex B S hS g hrepg V)
    (smallBaseChangeIndex B S hS h hreph ((smallBaseChange B S hS g hrepg).obj V))) ?_
  rw [chartBaseChangeMap_smallBaseChangeIndex B S hS g hrepg V]
  exact congrArg (fun q ↦ q ≫ hrepg.snd V.1.hom)
    (chartBaseChangeMap_smallBaseChangeIndex B S hS h hreph
      ((smallBaseChange B S hS g hrepg).obj V))

/-- **The comparison of charts followed by the two cartesian projections is the cartesian
projection of the composite**, as morphisms of the big fppf site.  This is
`AlgebraicGeometry.Space.chartBaseChangeMap_comp` at the unique morphism of indices, together
with `AlgebraicGeometry.Space.chartBaseChangeMap_compChartIndex` and the computation
`AlgebraicGeometry.Space.chartBaseChangeMap_smallBaseChangeIndex` of the chart morphism at the
initial index of the composite. -/
theorem toOver_map_chartBaseChangeCompComparison_comp_snd (V : SmallEtale B S hS C.1) :
    (SmallEtale.toOver B S hS D.1).map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
        hreph.snd ((smallBaseChange B S hS g hrepg).obj V).1.hom ≫ hrepg.snd V.1.hom =
      hrephg.snd V.1.hom := by
  refine Eq.trans ?_ (chartBaseChangeMap_smallBaseChangeIndex B S hS (h ≫ g) hrephg V)
  refine Eq.trans ?_ (chartBaseChangeMap_comp B S hS (h ≫ g) V
    ((isInitial_compChartIndex B S hS h g hreph hrepg V).to
      (smallBaseChangeIndex B S hS (h ≫ g) hrephg V))).symm
  exact congrArg (fun q ↦ (SmallEtale.toOver B S hS D.1).map
      (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫ q)
    (chartBaseChangeMap_compChartIndex B S hS h g hreph hrepg V).symm

variable (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)

/-- **The comparison of charts is compatible with the counits of the base-change adjunctions of
Stacks 03LP.**  Following it with the counit at `h` — postcomposed along `g`, which is possible
because postcomposition of charts composes strictly — and then with the counit at `g` is the
counit at `h ≫ g`.

A morphism of charts out of a postcomposed chart is determined by its underlying morphism of the
big fppf site (`AlgebraicGeometry.Space.postcompLeft_injective`), and each counit has the
cartesian projection as that morphism
(`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction_counit_left`), so this is
`AlgebraicGeometry.Space.toOver_map_chartBaseChangeCompComparison_comp_snd`. -/
theorem chartBaseChangeCompComparison_counit (V : SmallEtale B S hS C.1) :
    (smallEtalePostcomp B S hS (h ≫ g) hhg).map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
        (smallEtalePostcomp B S hS g hg).map
          ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V)) ≫
        (smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V =
      (smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V := by
  refine postcompLeft_injective B S hS (h ≫ g) hhg
    ((smallBaseChange B S hS (h ≫ g) hrephg).obj V) V ?_
  change (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).hom.left ≫
      ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
        ((smallBaseChange B S hS g hrepg).obj V)).hom.left ≫
      ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).hom.left =
    ((smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V).hom.left
  rw [smallEtalePostcompBaseChangeAdjunction_counit_left B S hS h hh hreph,
    smallEtalePostcompBaseChangeAdjunction_counit_left B S hS g hg hrepg,
    smallEtalePostcompBaseChangeAdjunction_counit_left B S hS (h ≫ g) hhg hrephg]
  exact toOver_map_chartBaseChangeCompComparison_comp_snd B S hS h g hreph hrepg hrephg V

end Comp

end AlgebraicGeometry.Space

end
