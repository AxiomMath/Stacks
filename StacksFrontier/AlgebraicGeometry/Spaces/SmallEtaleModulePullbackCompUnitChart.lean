module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompCoherence

/-!
# The chart projection of the unit of étale restriction along a composite

Let `h : D ⟶ A` and `g : A ⟶ C` be étale *representable* morphisms of algebraic spaces over a
scheme `S` in a big fppf site `B`.  The unit of
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` is written out in four factors by
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app`, and this file computes the
chart projection of each of them.  Three of the four are already available —
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackAdjunction_unit` for a unit of
Stacks 03LU, `AlgebraicGeometry.Space.chartModProj_modulePushforwardCompIso` for the composition
comparison of the direct images and
`AlgebraicGeometry.Space.chartModProj_etaleModulePullbackComp` for the strict composition of the
étale restrictions — and what is added here is the direct image along `g` of the unit at `h`
together with the reindexing identity that assembles the four.

## Main results

* `AlgebraicGeometry.Space.modules_comp4_val_app_apply`,
  `AlgebraicGeometry.Space.chartModProj_comp_apply` and
  `AlgebraicGeometry.Space.modules_comp_val_app_apply`: the peels of a composite under a chart
  projection, all stated at variable objects so that an application compares objects and never
  their sections.
* `AlgebraicGeometry.Space.chartModProj_modulePushforward_etaleModulePullbackAdjunction_unit`:
  the chart projection of the direct image along `g` of the unit at `h` is that unit read on the
  sections over the base-changed chart.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_val_app` and
  `AlgebraicGeometry.Space.chartModProj_etaleModulePullbackComp_comp`: the composite unit on a
  section, and the chart projection of its last factor.
* `AlgebraicGeometry.Space.postcomp_chartBaseChangeCompComparison_counit`: the comparison of
  charts followed by the two cartesian projections is the cartesian projection of the composite,
  in the shape the reindexing identity consumes.
* `AlgebraicGeometry.Space.etaleRestriction_counit_val_map_comp` and
  `AlgebraicGeometry.Space.postcomp_counit_val_map`: **the reindexing identity** — restricting a
  section of an `𝒪_C`-module along the cartesian projection of `g`, then along the cartesian
  projection of `h`, then along the comparison of charts, is restricting it along the cartesian
  projection of `h ≫ g`.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite of morphisms of `𝒪`-modules on the small étale site acts on sections by
composition.  Stated for `AlgebraicGeometry.Space.Modules` so that peeling a composite off a
section needs no reconciliation of that abbreviation with `SheafOfModules`. -/
theorem modules_comp_val_app_apply {W : AlgebraicSpaces B S hS}
    {M N P : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N) (ψ : N ⟶ P)
    (U : (SmallEtale B S hS W.1)ᵒᵖ) (x : M.val.obj U) :
    (φ ≫ ψ).val.app U x = ψ.val.app U (φ.val.app U x) := rfl

/-- A fourfold composite of morphisms of `𝒪`-modules acts on sections by composition.  The
middle morphism is the *first* argument, so that an application with the four morphisms given
explicitly fixes the two intermediate objects by the spellings the middle one carries; every
check an application then performs is between objects, never between their sections. -/
theorem modules_comp4_val_app_apply {W : AlgebraicSpaces B S hS}
    {Q R₁ R₂ R₃ P : Modules.{u, u} B S hS W.1 W.2} (c : R₂ ⟶ R₃) (b : R₁ ⟶ R₂) (a : Q ⟶ R₁)
    (d : R₃ ⟶ P) (U : (SmallEtale B S hS W.1)ᵒᵖ) (x : Q.val.obj U) :
    (((a ≫ b) ≫ c) ≫ d).val.app U x =
      d.val.app U (c.val.app U (b.val.app U (a.val.app U x))) := rfl

/-- Peeling the last factor off a composite under a chart projection.  Every object is a
variable, so an application is a first-order match on `≫` and the composite is never reduced. -/
theorem chartModProj_comp_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    {Q R : Modules.{u, u} B S hS Y.1 Y.2} {N : Modules.{u, u} B S hS X.1 X.2}
    (p : Q ⟶ R) (q : R ⟶ (modulePushforward B S hS f).obj N)
    (V : SmallEtale B S hS Y.1) (x : Q.val.obj (op V)) :
    chartModProj B S hS f hrep N V ((p ≫ q).val.app (op V) x) =
      chartModProj B S hS f hrep N V (q.val.app (op V) (p.val.app (op V) x)) := rfl

/-- **The chart projection of a section of the direct image of modules is injective**, being the
set-level chart projection of the underlying sheaf of sets. -/
theorem chartModProj_injective {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) :
    Function.Injective (chartModProj B S hS f hrep N V) :=
  chartSetProj_injective B S hS f hrep (moduleSetSheaf B S hS X N) V

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-! ### The direct image along `g` of the unit at `h` -/

/-- The chart projection along `g` of the direct image along `g` of the unit of Stacks 03LU at
`h`: the unit moves out of the projection, read on the sections over the base-changed chart.
This is `AlgebraicGeometry.Space.chartModProj_map`. -/
theorem chartModProj_modulePushforward_etaleModulePullbackAdjunction_unit
    (M : Modules.{u, u} B S hS C.1 C.2) (V : SmallEtale B S hS C.1)
    (z : ((modulePushforward B S hS g).obj
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.obj (op V)) :
    chartModProj B S hS g hrepg
        ((modulePushforward B S hS h).obj
          ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))) V
        (((modulePushforward B S hS g).map
          ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.app (op V) z) =
      ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.app
          (op ((smallBaseChange B S hS g hrepg).obj V))
        (chartModProj B S hS g hrepg
          ((etaleModulePullback.{u, u} B S hS g hg).obj M) V z) :=
  chartModProj_map B S hS g hrepg
    ((etaleModulePullbackAdjunction B S hS h hh).unit.app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)) V z

/-! ### The reindexing identity -/

/-- **The comparison of charts against the cartesian projections**, in the shape the reindexing
identity consumes: the comparison of charts followed by the counit at `h` and then the counit at
`g`, with the first two postcomposed along `g` as one morphism.  This is
`AlgebraicGeometry.Space.chartBaseChangeCompComparison_counit` with the functor applied to a
composite split, and with the strictness of postcomposition
(`AlgebraicGeometry.Space.smallEtalePostcomp_map_comp`) absorbed. -/
theorem postcomp_chartBaseChangeCompComparison_counit (V : SmallEtale B S hS C.1) :
    (smallEtalePostcomp B S hS g hg).map
          ((smallEtalePostcomp B S hS h hh).map
              (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
            (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
              ((smallBaseChange B S hS g hrepg).obj V)) ≫
        (smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V =
      (smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V := by
  refine Eq.trans (congrArg
    (fun q ↦ q ≫ (smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V)
    (CategoryTheory.Functor.map_comp (smallEtalePostcomp B S hS g hg)
      ((smallEtalePostcomp B S hS h hh).map
        (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V))
      ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
        ((smallBaseChange B S hS g hrepg).obj V)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact chartBaseChangeCompComparison_counit B S hS h g hreph hrepg hrephg hh hg hhg V

/-- The first half of the reindexing: restricting a section of the étale restriction along `g`
first along the counit at `h` and then along the comparison of charts is restricting it along the
composite of the two, inside that étale restriction. -/
theorem etaleRestriction_counit_val_map_comp (M : Modules.{u, u} B S hS C.1 C.2)
    (V : SmallEtale B S hS C.1)
    (m : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj
      (op ((smallBaseChange B S hS g hrepg).obj V))) :
    ((etaleModulePullback.{u, u} B S hS h hh).obj
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)).val.map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V)).op m) =
      ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map
        ((smallEtalePostcomp B S hS h hh).map
            (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
          (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V)).op m :=
  (etaleRestriction_val_map_apply B S hS h hh
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)
      (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) _).trans
    (compCoherence_val_map_comp_apply B S hS
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)
      ((smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
        ((smallBaseChange B S hS g hrepg).obj V))
      ((smallEtalePostcomp B S hS h hh).map
        (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V)) m)

/-- **The reindexing identity.**  Restricting a section of an `𝒪_C`-module along the cartesian
projection of `g` and then along the composite of the comparison of charts with the cartesian
projection of `h`, postcomposed along `g`, is restricting it along the cartesian projection of
`h ≫ g`.  The two restrictions compose
(`AlgebraicGeometry.Space.compCoherence_val_map_comp_apply`) and what is left is
`AlgebraicGeometry.Space.postcomp_chartBaseChangeCompComparison_counit`. -/
theorem postcomp_counit_val_map (M : Modules.{u, u} B S hS C.1 C.2)
    (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    M.val.map
          ((smallEtalePostcomp B S hS g hg).map
            ((smallEtalePostcomp B S hS h hh).map
                (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
              (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
                ((smallBaseChange B S hS g hrepg).obj V))).op
        (M.val.map
          ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V).op x) =
      M.val.map
        ((smallEtalePostcompBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg).counit.app V).op x :=
  (compCoherence_val_map_comp_apply B S hS M
      ((smallEtalePostcompBaseChangeAdjunction B S hS g hg hrepg).counit.app V)
      ((smallEtalePostcomp B S hS g hg).map
        ((smallEtalePostcomp B S hS h hh).map
            (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V) ≫
          (smallEtalePostcompBaseChangeAdjunction B S hS h hh hreph).counit.app
            ((smallBaseChange B S hS g hrepg).obj V))) x).trans
    (Stacks.CategoryTheory.proj_congr
      (postcomp_chartBaseChangeCompComparison_counit B S hS h g hh hg hhg hreph hrepg hrephg V)
      (fun q ↦ M.val.map q.op x))


/-! ### The chart projection of the composite unit

Every spelling below is the one
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app` produces — in particular the
iterated étale restriction appears as the value of the *composite* functor — so that no two
spellings of it ever have to be reconciled underneath
`AlgebraicGeometry.Space.modulePushforward`, which is what exceeds the heartbeat budget. -/

/-- The chart projection of the strict composition comparison of étale restrictions, with the
iterated restriction spelled as the value of the composite functor. -/
theorem chartModProj_etaleModulePullbackComp_comp (M : Modules.{u, u} B S hS C.1 C.2)
    (V : SmallEtale B S hS C.1)
    (z : ((modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS g hg ⋙
        etaleModulePullback.{u, u} B S hS h hh).obj M)).val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((modulePushforward B S hS (h ≫ g)).map
          ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M)).val.app (op V) z) =
      chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS g hg ⋙
          etaleModulePullback.{u, u} B S hS h hh).obj M) V z :=
  (chartModProj_map B S hS (h ≫ g) hrephg
      ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M) V z).trans
    (etaleModulePullbackComp_hom_app_val_app B S hS h g hh hg hhg M
      ((smallBaseChange B S hS (h ≫ g) hrephg).obj V) _)

/-- The unit of `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` read on a section,
as the fourfold composite of
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app`. -/
theorem etaleModulePullbackCompAdjunction_unit_val_app (M : Modules.{u, u} B S hS C.1 C.2)
    (V : SmallEtale B S hS C.1) (x : M.val.obj (op V)) :
    ((etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M).val.app (op V) x =
      ((((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
              (modulePushforward B S hS g).map
                ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                  ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
            (modulePushforwardCompIso B S hS h g).hom.app
              ((etaleModulePullback.{u, u} B S hS g hg ⋙
                etaleModulePullback.{u, u} B S hS h hh).obj M)) ≫
          (modulePushforward B S hS (h ≫ g)).map
            ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M)).val.app (op V) x :=
  Stacks.CategoryTheory.proj_congr
    (etaleModulePullbackCompAdjunction_unit_app B S hS h g hh hg hhg M)
    (fun m ↦ m.val.app (op V) x)

end Comp

end AlgebraicGeometry.Space

end
