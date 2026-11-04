module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnit

/-!
# The coherence of Stacks 03LU against Stacks 03LW, at a representable pair

Let `h : D ⟶ A` and `g : A ⟶ C` be étale *representable* morphisms of algebraic spaces.  This
file discharges the hypothesis of
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`: the two adjunctions
between étale restriction of modules along `h ≫ g` and the direct image along `h ≫ g` — the one
assembled from the two factors through the comparison of direct images of Stacks 03LU and the
transport of the adjunction of Stacks 03LU along the identification of Stacks 03LW — have the
same unit.

## Implementation notes

Every chart projection here is `AlgebraicGeometry.Space.chartModProj`, the projection whose
domain is the sections of the direct image **of modules**, and never the set-level
`AlgebraicGeometry.Space.chartSetProj` applied to the underlying sheaf of sets of a concrete
module.  The two are the same function, and the bridge
`AlgebraicGeometry.Space.chartModProj_eq_chartSetProj` is proved at a *variable* module; applied
at the concrete two-layer étale restrictions occurring below, the same reconciliation exhausts
the heartbeat budget.  Each step is its own declaration for the same reason.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading restrictions of sections -/

/-- Restricting sections along `ψ` and then along `φ` is restricting along `ψ ≫ φ`; this is
functoriality of the underlying presheaf of abelian groups. -/
theorem compCoherence_val_map_comp_apply {W : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS W.1 W.2) {V₁ V₂ V₃ : SmallEtale B S hS W.1} (φ : V₂ ⟶ V₃)
    (ψ : V₁ ⟶ V₂) (x : M.val.obj (op V₃)) :
    M.val.map ψ.op (M.val.map φ.op x) = M.val.map (ψ ≫ φ).op x :=
  (CategoryTheory.congr_fun (M.val.presheaf.map_comp φ.op ψ.op) x).symm

/-- The underlying sheaf of sets of a module restricts sections the way the module does. -/
theorem moduleSetSheaf_obj_map_apply {W : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS W.1 W.2) {V V' : SmallEtale B S hS W.1} (k : V' ⟶ V)
    (x : M.val.obj (op V)) :
    (moduleSetSheaf B S hS W M).obj.map k.op x = M.val.map k.op x := rfl

/-- Restricting a section of an étale restriction is restricting along the postcomposed chart
morphism. -/
theorem etaleRestriction_val_map_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    {U U' : SmallEtale B S hS X.1} (k : U' ⟶ U)
    (m : ((etaleModulePullback.{u, u} B S hS f hf).obj M).val.obj (op U)) :
    ((etaleModulePullback.{u, u} B S hS f hf).obj M).val.map k.op m =
      M.val.map ((smallEtalePostcomp B S hS f hf).map k).op m := rfl

/-! ### The chart projection of modules against the chart projection of sets -/

/-- **The chart projection of the direct image of modules is the set-level chart projection** of
the underlying sheaf of sets.  Stated at a variable module: the two sides reconcile the sections
of a direct image of modules with those of the direct image of the underlying sheaf of sets, and
that reconciliation is affordable here and not at the concrete iterated restrictions below. -/
theorem chartModProj_eq_chartSetProj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hrep N V z =
      chartSetProj B S hS f hrep (moduleSetSheaf B S hS X N) V z := rfl

/-- **The chart projection of a section of the direct image of modules, computed through the
set-level chart projection after rewriting the section.**  The section `z` is moved to `z'` by
`hz`, and the set-level chart projection of `z'` is read off by `hr`.

Stated at a variable morphism, module and chart, with the two steps as hypotheses in exactly the
shape their producers have — an equality of sections of the direct image of modules, and a
computation of the set-level chart projection of the underlying sheaf of sets.  The
reconciliation of the two kinds of sections which
`AlgebraicGeometry.Space.chartModProj_eq_chartSetProj` performs is therefore done here, once, at
a variable module; a consumer instantiating this lemma performs none.  Carried out instead at
the concrete composite of
`AlgebraicGeometry.Space.chartModProj_modulePushforwardCompIso`, where the two hypotheses are
about the comparison of Stacks 03LU and about the comparison of Stacks 03G2, part (3), the same
reconciliation exhausts the heartbeat budget. -/
theorem chartModProj_eq_of_chartSetProj_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    {z z' : ((modulePushforward B S hS f).obj N).val.obj (op V)}
    {r : N.val.obj (op ((smallBaseChange B S hS f hrep).obj V))} (hz : z = z')
    (hr : chartSetProj B S hS f hrep (moduleSetSheaf B S hS X N) V z' = r) :
    chartModProj B S hS f hrep N V z = r :=
  ((chartModProj_eq_chartSetProj B S hS f hrep N V z).trans
    (congrArg (chartSetProj B S hS f hrep (moduleSetSheaf B S hS X N) V) hz)).trans hr

/-- **The chart projection of the unit of Stacks 03LU is restriction along the cartesian
projection**, with the projection read on module sections. -/
theorem chartModProj_etaleModulePullbackAdjunction_unit {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hrep : yoneda.relativelyRepresentable f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    chartModProj B S hS f hrep ((etaleModulePullback.{u, u} B S hS f hf).obj M) V
        (((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x) =
      M.val.map
        ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).op x :=
  chartSetProj_etaleModulePullbackAdjunction_unit B S hS f hf hrep M V x

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-- Postcomposition of charts composes strictly, read on a morphism of charts. -/
theorem smallEtalePostcomp_map_comp {U U' : SmallEtale B S hS D.1} (k : U' ⟶ U) :
    (smallEtalePostcomp B S hS g hg).map ((smallEtalePostcomp B S hS h hh).map k) =
      (smallEtalePostcomp B S hS (h ≫ g) hhg).map k := rfl

/-- The direct image of modules along `h` of a variable module, read as the direct image of
sheaves of sets of its underlying sheaf.  Stated at a variable module. -/
theorem moduleSetSheaf_modulePushforward_eq (N : Modules.{u, u} B S hS D.1 D.2) :
    moduleSetSheaf B S hS A ((modulePushforward B S hS h).obj N) =
      (smallEtaleDirectImage B S hS h).obj (moduleSetSheaf B S hS D N) := rfl

/-! ### The chart projection of the composition comparison of the direct images

Every section below is taken in the spelling the composite unit produces, the sections of the
iterated direct image **of modules**.  Each declaration then performs at most one of the two
reconciliations — the module-to-set one at `h ≫ g`, which `AlgebraicGeometry.Space.chartModProj`
and `AlgebraicGeometry.Space.chartSetProj` differ by, and the one at the iterated direct image,
which the comparison of Stacks 03G2, part (3), is stated with.  Performing both in one
declaration exceeds the heartbeat budget. -/

/-- The set-level computation `AlgebraicGeometry.Space.chartSetProj_smallToposMorphismTypeU_comp`
at the underlying sheaf of sets of a variable module. -/
theorem chartSetProj_smallToposMorphismTypeU_comp_moduleSetSheaf
    (N : Modules.{u, u} B S hS D.1 D.2) (V : SmallEtale B S hS C.1)
    (w : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    chartSetProj B S hS (h ≫ g) hrephg (moduleSetSheaf B S hS D N) V
        (((smallToposMorphismTypeU_comp B S hS h g).hom.app
          (moduleSetSheaf B S hS D N)).hom.app (op V) w) =
      (moduleSetSheaf B S hS D N).obj.map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartSetProj B S hS h hreph (moduleSetSheaf B S hS D N)
            ((smallBaseChange B S hS g hrepg).obj V)
          (chartSetProj B S hS g hrepg
            ((smallEtaleDirectImage B S hS h).obj (moduleSetSheaf B S hS D N)) V w)) :=
  chartSetProj_smallToposMorphismTypeU_comp B S hS h g hreph hrepg hrephg
    (moduleSetSheaf B S hS D N) V w

/-- The iterated set-level chart projection of the underlying sheaf of sets of a variable module
is the iterated chart projection of the module. -/
theorem chartSetProj_iterated_eq_chartModProj (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (w : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    (moduleSetSheaf B S hS D N).obj.map
          (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartSetProj B S hS h hreph (moduleSetSheaf B S hS D N)
            ((smallBaseChange B S hS g hrepg).obj V)
          (chartSetProj B S hS g hrepg
            ((smallEtaleDirectImage B S hS h).obj (moduleSetSheaf B S hS D N)) V w)) =
      N.val.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V w)) := rfl

/-- The two previous steps composed: the set-level chart projection of the comparison of
Stacks 03G2, part (3), is the iterated chart projection of modules. -/
theorem chartSetProj_smallToposMorphismTypeU_comp_chartModProj
    (N : Modules.{u, u} B S hS D.1 D.2) (V : SmallEtale B S hS C.1)
    (w : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    chartSetProj B S hS (h ≫ g) hrephg (moduleSetSheaf B S hS D N) V
        (((smallToposMorphismTypeU_comp B S hS h g).hom.app
          (moduleSetSheaf B S hS D N)).hom.app (op V) w) =
      N.val.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V w)) :=
  (chartSetProj_smallToposMorphismTypeU_comp_moduleSetSheaf B S hS h g hreph hrepg hrephg
      N V w).trans
    (chartSetProj_iterated_eq_chartModProj B S hS h g hreph hrepg hrephg N V w)

/-- The bridge of the two chart projections, at the section the comparison of Stacks 03LU
produces. -/
theorem chartModProj_eq_chartSetProj_modulePushforwardCompIso
    (N : Modules.{u, u} B S hS D.1 D.2) (V : SmallEtale B S hS C.1)
    (w : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg N V
        (((modulePushforwardCompIso B S hS h g).hom.app N).val.app (op V) w) =
      chartSetProj B S hS (h ≫ g) hrephg (moduleSetSheaf B S hS D N) V
        (((modulePushforwardCompIso B S hS h g).hom.app N).val.app (op V) w) :=
  chartModProj_eq_chartSetProj B S hS (h ≫ g) hrephg N V _

/-- **The chart projection of the composition comparison of the direct images of modules is the
iterated chart projection**, read along the comparison
`AlgebraicGeometry.Space.chartBaseChangeCompComparison` of the base-changed charts.  This is the
module-level form of Stacks 03G2, part (3), on sections: the only step of the route to
Stacks 03LY which the three preceding declarations were split up to make affordable, assembled
by `AlgebraicGeometry.Space.chartModProj_eq_of_chartSetProj_eq`, whose two hypotheses are the
comparison of Stacks 03LU on sections and the set-level computation.

The chart at which
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` is read is left to
unification rather than written as `op V`: that lemma takes it as a variable of type
`(SmallEtale B S hS C.1)ᵒᵖ`, so writing the argument out elaborates `Opposite.op` at
`AlgebraicGeometry.Space.SmallEtale`, whereas the sections in this statement elaborate it at the
site of the sheaf of modules, which is that definition unfolded.  Both spellings sit inside the
implicit arguments of every section occurring here, and identifying them exhausts the heartbeat
budget; inferred from the type of `w`, the lemma arrives in the spelling this statement
uses. -/
theorem chartModProj_modulePushforwardCompIso (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (w : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg N V
        (((modulePushforwardCompIso B S hS h g).hom.app N).val.app (op V) w) =
      N.val.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V w)) :=
  chartModProj_eq_of_chartSetProj_eq B S hS (h ≫ g) hrephg N V
    (modulePushforwardCompIso_hom_app_val_app B S hS h g N _ w)
    (chartSetProj_smallToposMorphismTypeU_comp_chartModProj B S hS h g hreph hrepg hrephg N V w)

/-! ### The chart projection of the factors of the composite unit -/

/-- The chart projection of the strict composition comparison of étale restrictions: it is the
identity on sections, so the projection only retypes the chart module. -/
theorem chartModProj_etaleModulePullbackComp (M : Modules.{u, u} B S hS C.1 C.2)
    (V : SmallEtale B S hS C.1)
    (z : ((modulePushforward B S hS (h ≫ g)).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M))).val.obj (op V)) :
    chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) V
        (((modulePushforward B S hS (h ≫ g)).map
          ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M)).val.app (op V) z) =
      chartModProj B S hS (h ≫ g) hrephg
        ((etaleModulePullback.{u, u} B S hS h hh).obj
          ((etaleModulePullback.{u, u} B S hS g hg).obj M)) V z :=
  (chartModProj_map B S hS (h ≫ g) hrephg
      ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M) V z).trans
    (etaleModulePullbackComp_hom_app_val_app B S hS h g hh hg hhg M
      ((smallBaseChange B S hS (h ≫ g) hrephg).obj V) _)

end Comp

end AlgebraicGeometry.Space

end
