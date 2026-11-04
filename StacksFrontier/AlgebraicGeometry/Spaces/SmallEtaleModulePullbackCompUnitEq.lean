module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitChart

/-!
# The chart projection of the unit of the composite adjunction

Let `h : D ⟶ A` and `g : A ⟶ C` be étale *representable* morphisms of algebraic spaces over a
scheme `S` in a big fppf site `B`.  There are two adjunctions between restriction of
`𝒪`-modules along `h ≫ g` and the direct image along `h ≫ g`: the one of Stacks 03LU at the
composite, read through Stacks 03LW, and the one assembled from the two factors through the
comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of the direct images and the
strict composition `AlgebraicGeometry.Space.etaleModulePullbackComp` of the étale restrictions.

Their units agree, and that is **not** proved here: it is
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`, in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean`, which needs no relative
representability.  This file proves the **chart projection of the composite unit**, which is the
representable route to the same equality and was for a time a second declaration of it; of two
declarations of one conclusion the hypothesis-free one survives, so what is kept here is the chart
projection itself, which has consumers of its own.

The chart projection is this.  Both units are morphisms of `𝒪_C`-modules into the direct image
along `h ≫ g`, so each is determined by its chart projections
(`AlgebraicGeometry.Space.chartModProj_injective`), and both chart projections are restriction of
sections along the cartesian projection `V ×_C D ⟶ V` of `h ≫ g`.  For the unit of Stacks 03LU
that is `AlgebraicGeometry.Space.chartModProj_etaleModulePullbackAdjunction_unit`.  For the
composite unit it is the content of this file: the unit is the fourfold composite written out by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_val_app`, the chart projection of
each factor is known, and the four answers compose to the cartesian projection of `h ≫ g` by the
reindexing identity `AlgebraicGeometry.Space.postcomp_counit_val_map`.

## Main results

* `AlgebraicGeometry.Space.chartModProj_etaleModulePullbackCompAdjunction_unit`: **the chart
  projection of the unit of `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` is
  restriction of sections along the cartesian projection of `h ≫ g`** — the same answer as for
  the unit of Stacks 03LU.

## Implementation notes

Two elaboration facts govern how the chain below is cut into declarations.

*Peel one factor at a time, and never write a peeled composite.*  The composite unit is a
fourfold `≫`, and a statement that writes all four factors applied to a section one after the
other does not elaborate, in any spelling of the intermediate objects — with the factors given
explicitly, with them left to unification, and with the peel stated at variable objects and
instantiated.  What does elaborate is a statement carrying the *composite*, which is what
`AlgebraicGeometry.Space.chartModProj_comp_apply` peels one factor off of; each peeled head is
consumed immediately by the lemma computing its chart projection, so the composite shrinks by
one factor per declaration and no peeled form is ever named.

*At most one crossing per declaration.*  The iterated étale restriction has two spellings — the
value of the composite functor, which the unit's `≫` records, and the restrictions applied one
after the other, which every lemma proved through
`AlgebraicGeometry.Space.chartModProj_map` at a variable morphism carries — and a section has
two readings wherever a direct image or an étale restriction is unfolded.  Reconciling two of
these in one declaration exhausts the heartbeat budget; reconciling one is affordable.  So the
peels of the two comparisons are taken in the composite-functor spelling, the crossing to the
applied spelling is paid once in
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackCompAdjunction_unit_peel_three`, and
the three restrictions the chart projections leave behind are composed in two steps rather than
one: `AlgebraicGeometry.Space.chartModProj_etaleModulePullbackCompAdjunction_unit_val_map` stops
at the restriction inside the étale restriction along `g`, and
`AlgebraicGeometry.Space.etaleRestriction_chartBaseChangeCompComparison_counit_val_map` reads it
on `M` and finishes.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.ChartUnitEq

universe w m v₁ u₁

variable {CC : Type u₁} [Category.{v₁} CC] {J : GrothendieckTopology CC}
    {R : CategoryTheory.Sheaf J RingCat.{w}}

/-- **A morphism of sheaves of modules is determined by its action on sections**, with the object
of the site unopped and the action written through the coercion that applies a component to a
section.  Stated generically: at a chart the ring a component is linear over is reached only by
unfolding the chart data, and `CategoryTheory.ModuleCat.hom_ext` asked to infer it from a
chart-level goal exhausts the heartbeat budget. -/
theorem hom_ext_val_app_unop {M N : _root_.SheafOfModules.{m} R} {f g : M ⟶ N}
    (hfg : ∀ (Y : CC) (x : M.val.obj (op Y)),
      f.val.app (op Y) x = g.val.app (op Y) x) : f = g :=
  _root_.SheafOfModules.hom_ext
    (_root_.PresheafOfModules.hom_ext fun Z ↦
      ModuleCat.hom_ext (LinearMap.ext fun x ↦ hfg Z.unop x))

end Stacks.ChartUnitEq

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-! ### The chart projection of the composite unit, factor by factor -/

/-- **The composite unit with its last factor peeled off.**  The unit is written out by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_val_app`, the strict composition
of the étale restrictions is split off the composite by
`AlgebraicGeometry.Space.chartModProj_comp_apply`, and its chart projection is
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackComp_comp`.  What is left under the
projection is a threefold composite, in the spelling the unit carries. -/
theorem chartModProj_etaleModulePullbackCompAdjunction_unit_peel_four
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M).val.app
          (op V) x) =
      chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS g hg ⋙
          etaleModulePullback.{u, u} B S hS h hh).obj M) V
        ((((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
                (modulePushforward B S hS g).map
                  ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                    ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
              (modulePushforwardCompIso B S hS h g).hom.app
                ((etaleModulePullback.{u, u} B S hS g hg ⋙
                  etaleModulePullback.{u, u} B S hS h hh).obj M)).val.app (op V) x) :=
  (Stacks.CategoryTheory.proj_congr
        (etaleModulePullbackCompAdjunction_unit_val_app B S hS h g hh hg hhg M V x)
        (fun s ↦ chartModProj B S hS (h ≫ g) hrephg
          ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V s)).trans
    ((chartModProj_comp_apply B S hS (h ≫ g) hrephg
          (((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
                (modulePushforward B S hS g).map
                  ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                    ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
              (modulePushforwardCompIso B S hS h g).hom.app
                ((etaleModulePullback.{u, u} B S hS g hg ⋙
                  etaleModulePullback.{u, u} B S hS h hh).obj M))
          ((modulePushforward B S hS (h ≫ g)).map
            ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M)) V x).trans
      (chartModProj_etaleModulePullbackComp_comp B S hS h g hh hg hhg hrephg M V _))

/-- **The composite unit with the composition comparison of the direct images peeled off too.**
Its chart projection is the iterated chart projection, read along the comparison
`AlgebraicGeometry.Space.chartBaseChangeCompComparison` of the base-changed charts — this is
`AlgebraicGeometry.Space.chartModProj_modulePushforwardCompIso`.  What is left is the twofold
composite of the two units.

The statement writes the iterated étale restriction with the restrictions applied one after the
other, which is the spelling the chart projections of the two units carry, while the proof reads
the comparison at the composite-functor spelling the unit records; this is the one place where
the two are reconciled. -/
theorem chartModProj_etaleModulePullbackCompAdjunction_unit_peel_three
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M).val.app
          (op V) x) =
      ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph
            ((etaleModulePullback.{u, u} B S hS h hh).obj
              ((etaleModulePullback.{u, u} B S hS g hg).obj M))
            ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg
              ((modulePushforward B S hS h).obj
                ((etaleModulePullback.{u, u} B S hS h hh).obj
                  ((etaleModulePullback.{u, u} B S hS g hg).obj M))) V
            (((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
                (modulePushforward B S hS g).map
                  ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                    ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.app (op V) x))) :=
  (chartModProj_etaleModulePullbackCompAdjunction_unit_peel_four B S hS h g hh hg hhg hrephg
      M V x).trans
    ((chartModProj_comp_apply B S hS (h ≫ g) hrephg
          ((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
            (modulePushforward B S hS g).map
              ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                ((etaleModulePullback.{u, u} B S hS g hg).obj M)))
          ((modulePushforwardCompIso B S hS h g).hom.app
            ((etaleModulePullback.{u, u} B S hS g hg ⋙
              etaleModulePullback.{u, u} B S hS h hh).obj M)) V x).trans
      (chartModProj_modulePushforwardCompIso B S hS h g hreph hrepg hrephg
        ((etaleModulePullback.{u, u} B S hS g hg ⋙
          etaleModulePullback.{u, u} B S hS h hh).obj M) V _))

/-- The chart projection along `g` of the two units: the unit at `h` moves out of the projection
(`AlgebraicGeometry.Space.chartModProj_modulePushforward_etaleModulePullbackAdjunction_unit`) and
the unit at `g` becomes restriction along the cartesian projection of `g`. -/
theorem chartModProj_unit_comp_unit
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS g hrepg
        ((modulePushforward B S hS h).obj
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) V
        (((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
            (modulePushforward B S hS g).map
              ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.app (op V) x) =
      ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.app
          (op ((smallBaseChange B S hS g hrepg).obj V))
        (M.val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).op x) :=
  (chartModProj_comp_apply B S hS g hrepg
        ((etaleModulePullbackAdjunction B S hS g hg).unit.app M)
        ((modulePushforward B S hS g).map
          ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) V x).trans
    ((chartModProj_modulePushforward_etaleModulePullbackAdjunction_unit B S hS h g hh hg hrepg
          M V _).trans
      (Stacks.CategoryTheory.proj_congr
        (chartModProj_etaleModulePullbackAdjunction_unit B S hS g hg hrepg M V x)
        (fun m ↦ ((etaleModulePullbackAdjunction B S hS h hh).unit.app
              ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.app
            (op ((smallBaseChange B S hS g hrepg).obj V)) m)))

/-- The iterated chart projection of the two units: the chart projection along `h` of the unit at
`h` is restriction along the cartesian projection of `h`, so the two units become the two
cartesian restrictions, one after the other. -/
theorem chartModProj_chartModProj_unit_comp_unit
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS h hreph
        ((etaleModulePullback.{u, u} B S hS h hh).obj
          ((etaleModulePullback.{u, u} B S hS g hg).obj M))
        ((smallBaseChange B S hS g hrepg).obj V)
        (chartModProj B S hS g hrepg
            ((modulePushforward B S hS h).obj
              ((etaleModulePullback.{u, u} B S hS h hh).obj
                ((etaleModulePullback.{u, u} B S hS g hg).obj M))) V
          (((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
              (modulePushforward B S hS g).map
                ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                  ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.app (op V) x)) =
      ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V)).op
        (M.val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).op x) :=
  (Stacks.CategoryTheory.proj_congr
        (chartModProj_unit_comp_unit B S hS h g hh hg hrepg M V x)
        (fun m ↦ chartModProj B S hS h hreph
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))
          ((smallBaseChange B S hS g hrepg).obj V) m)).trans
    (chartModProj_etaleModulePullbackAdjunction_unit B S hS h hh hreph
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)
      ((smallBaseChange B S hS g hrepg).obj V) _)

/-! ### The chart projection of the composite unit -/

/-- The chart projection of the composite unit, with the comparison of charts and the cartesian
projection of `h` composed into a single restriction, still read inside the étale restriction
along `g`.  This is
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackCompAdjunction_unit_peel_three` with the
iterated chart projection computed and
`AlgebraicGeometry.Space.etaleRestriction_counit_val_map_comp` applied. -/
theorem chartModProj_etaleModulePullbackCompAdjunction_unit_val_map
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M).val.app
          (op V) x) =
      ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map
          ((smallEtalePostcomp B S hS h hh).map
              (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
            (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
              ((smallBaseChange B S hS g hrepg).obj V)).op
        (M.val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).op x) :=
  (chartModProj_etaleModulePullbackCompAdjunction_unit_peel_three B S hS h g hh hg hhg hreph
        hrepg hrephg M V x).trans
    ((Stacks.CategoryTheory.proj_congr
          (chartModProj_chartModProj_unit_comp_unit B S hS h g hh hg hreph hrepg M V x)
          (fun r ↦ ((etaleModulePullback.{u, u} B S hS h hh).obj
                ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.map
              (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op r)).trans
      (etaleRestriction_counit_val_map_comp B S hS h g hh hg hreph hrepg hrephg M V _))

/-- **The three restrictions the chart projections leave behind compose to the cartesian
projection of `h ≫ g`**, read on `M` itself: the outer two are moved onto `M` by
`AlgebraicGeometry.Space.etaleRestriction_val_map_apply`, and what is left is the reindexing
identity `AlgebraicGeometry.Space.postcomp_counit_val_map`. -/
theorem etaleRestriction_chartBaseChangeCompComparison_counit_val_map
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map
          ((smallEtalePostcomp B S hS h hh).map
              (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
            (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
              ((smallBaseChange B S hS g hrepg).obj V)).op
        (M.val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).op x) =
      M.val.map
        ((smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V).op x :=
  (etaleRestriction_val_map_apply B S hS g hg M
        ((smallEtalePostcomp B S hS h hh).map
            (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
          (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V)) _).trans
    (postcomp_counit_val_map B S hS h g hh hg hhg hreph hrepg hrephg M V x)

include hreph hrepg in
/-- **The chart projection of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` is restriction of sections along the
cartesian projection of `h ≫ g`** — the same answer
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackAdjunction_unit` gives for the unit of
Stacks 03LU at the composite. -/
theorem chartModProj_etaleModulePullbackCompAdjunction_unit
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M).val.app
          (op V) x) =
      M.val.map
        ((smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V).op x :=
  (chartModProj_etaleModulePullbackCompAdjunction_unit_val_map B S hS h g hh hg hhg hreph hrepg
      hrephg M V x).trans
    (etaleRestriction_chartBaseChangeCompComparison_counit_val_map B S hS h g hh hg hhg hreph
      hrepg hrephg M V x)

/-! ### The two units

The equality of the two units is **not** stated here.  It was, with the three relative
representability hypotheses of this file carried, and the same statement is proved without any of
them in `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleUnitCompJoin.lean` as
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit`, by comparing the two units at
their written-out spellings instead of through the chart projections.  Two declarations of one
statement is exactly the duplication the library is being cleaned of, and of the two it is the
hypothesis-free one that survives; the chart-projection route reached it only for a composable
pair of *relatively representable* étale morphisms, so keeping this copy would have been keeping
the weaker of two identical conclusions.

What this file still supplies is that route's ingredients -- in particular
`.chartModProj_etaleModulePullbackCompAdjunction_unit`, the chart projection of the composite
unit, which is used elsewhere. -/

end AlgebraicGeometry.Space

end
