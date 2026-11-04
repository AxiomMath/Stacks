module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPresentationComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitChart

/-!
# The composition comparison of inverse images on chart sections

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B`.  `AlgebraicGeometry.Space.modulePullbackCompIso` is the comparison
`g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU, and
`AlgebraicGeometry.Space.modulePullbackUnitSection` is the chart component of the unit of the
Stacks 03D7 adjunction: the canonical section of `f^*M` over the upper chart of a commutative
diagram of étale scheme charts over `f`, attached to a section of `M` over the lower chart.

This file proves that **the comparison carries a chart section of a chart section to the chart
section of the composite**, on a composed chart diagram, with no hypothesis on either morphism.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection`:
  **the chart-section formula for the comparison of inverse images of Stacks 03LU.**

## Implementation notes

The two inputs are both proved, and the proof is their composite.

The chart formula `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFMapCompChartFormula.lean`, taken with both linear
maps of sections the units of Stacks 03D7, computes the composite of the two chart sections.
Its one hypothesis is the Stacks 03LU clause
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`, which is
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`; the
implementation notes of several other files record that clause as missing and name a refactor of
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` as the route to it, and those
notes are stale — it is proved there by reading the comparison on a local section, where the
identification is between two elements of one type rather than between two sheaves.

The passage from the comparison of *direct* images, which that chart formula is about, to the
comparison of *inverse* images is the unit composition law
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app`, which is
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` — the equation
characterizing the latter as the mate of the former — with the composite unit split.  It is read
on a chart section by naturality of the counit of the chartwise universal property,
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`.  So
`CategoryTheory.Adjunction.leftAdjointUniq`, which the comparison of inverse images is defined
by, is never unfolded.

No étaleness is assumed anywhere.  The chart formula applies because the chart diagram is
`AlgebraicGeometry.Space.ChartDiagram.comp` of the two given ones and therefore factors through
the middle chart by construction, which is the only thing
`AlgebraicGeometry.Space.FMap.comp_app` asks of it.  In particular the formula covers the *mixed*
case — one of the two morphisms étale and the other arbitrary, or neither — which the
both-factors-étale identification
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction` does not.

Each step is a `have` of its own at the spelling the preceding one produces, and three
elaboration facts decide the shape.

*Do not restate the unit of the composite adjunction.*  Matching
`AlgebraicGeometry.Space.moduleCompAdjunction` against
`CategoryTheory.Adjunction.ofNatIsoRight` so as to split its unit is a `whnf` deterministic
timeout.  It does not have to be done: `AlgebraicGeometry.Space.moduleCompAdjunction_unit_app`
and `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app` are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationComplex.lean`, and the second is
used here as it stands.

*The `congrArg` that carries the unit equation under a section needs its binder type ascribed.*
Written as `congrArg (fun m ↦ … (m.val.app (op W) s)) h` the elaborator must infer the binder's
type through `m.val.app (op W)`, whose coercion to a function carries the module structure of the
direct image in its instance arguments, and that is a `whnf` deterministic timeout; written as
`congrArg (fun m : M ⟶ (modulePushforward B S hS (f ≫ g)).obj _ ↦ …) h` with the `Hom` type
given, it is free.  This is the discipline the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean` record.

*Peel the composite by `rfl` between two written-out sides, not by applying a peeling lemma.*
`AlgebraicGeometry.Space.modules_comp_val_app_apply` is stated at variable modules for exactly
this, but applying it here is an `isDefEq` deterministic timeout: its three module arguments have
to be solved while the two spellings of the composite inverse image —
`(modulePullback B S hS g ⋙ modulePullback B S hS f).obj M`, which the comparison of inverse
images carries, and the nested `(modulePullback B S hS f).obj ((modulePullback B S hS g).obj M)`,
which `AlgebraicGeometry.Space.moduleFMapCompHom` carries — are reconciled underneath
`AlgebraicGeometry.Space.modulePushforward`.  With both sides of the peel written out the
reconciliation happens once inside each side's own elaboration, which is affordable, and the peel
itself is then `rfl`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

section Factor

variable (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- **The comparison of Stacks 03LU carries a chart section of a chart section to the chart
section of the composite.**  For étale scheme charts `U` of `X`, `V` of `Y` and `W` of `Z` joined
by vertical morphisms `a : U ⟶ V` over `f` and `b : V ⟶ W` over `g`, the comparison
`g^*(f^*M) ⟶ (f ≫ g)^*M` of inverse images carries the chart section along `a` of the chart
section along `b` of a section `s` of `M` over `W` to the chart section of `s` along `a ≫ b`.

No hypothesis is placed on `f` or `g`: the chart diagram is the composite of the two given ones,
so it factors through `V` by construction, which is all the chart formula of
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` asks. -/
theorem modulePullbackCompIso_hom_val_app_modulePullbackUnitSection
    (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        (modulePullbackUnitSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
          (modulePullbackUnitSection B S hS g M ⟨V, W, b, hb⟩ s)) =
      modulePullbackUnitSection B S hS (f ≫ g) M (ChartDiagram.comp B S hS f g a b ha hb) s := by
  -- the composite morphism of modules, followed by the comparison of inverse images, is the unit
  have hassoc : (moduleFMapCompHom B S hS f g
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS g).obj M) M
        (modulePushforwardHomFMap B S hS g ((modulePullback B S hS g).obj M) M
          ((modulePullbackAdjunction B S hS g).unit.app M))
        (modulePushforwardHomFMap B S hS f
          ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
          ((modulePullback B S hS g).obj M)
          ((modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj M)))
        (modulePushforwardCompIso B S hS f g)) ≫
          ((modulePushforward B S hS (f ≫ g)).map ((modulePullbackCompIso B S hS f g).hom.app M)) =
          ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M) := by
    rw [moduleFMapCompHom_modulePushforwardHomFMap]
    simp only [Category.assoc]
    exact modulePullbackAdjunction_unit_comp_app B S hS f g M
  -- abbreviations for the two units as linear maps of sections, and the composed chart diagram
  set ug := modulePushforwardHomFMap B S hS g ((modulePullback B S hS g).obj M) M
    ((modulePullbackAdjunction B S hS g).unit.app M)
  set uf := modulePushforwardHomFMap B S hS f
    ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
    ((modulePullback B S hS g).obj M)
    ((modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj M))
  set c := ChartDiagram.comp B S hS f g a b ha hb
  -- the composite of the two linear maps of sections, at the composed chart diagram
  have hchart := ModuleFMap.compOfIso_app B S hS f g a b ha hb _ _ M ug uf
    (modulePushforwardCompIso B S hS f g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g _) s
  have hcomp := ModuleFMap.compOfIso_app_comp f g a b ha hb _ _ M ug uf
    (modulePushforwardCompIso B S hS f g) s
  -- the unit section at `f ≫ g`, as the counit of the chartwise universal property on the unit
  have r1 : modulePullbackUnitSection B S hS (f ≫ g) M c s =
      modulePushforwardCounitApp B S hS (f ≫ g) ((modulePullback B S hS (f ≫ g)).obj M) c
        (((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app (op W) s) :=
    (modulePushforwardHomFMap_unit_app (f ≫ g) M c s).symm.trans
      (modulePushforwardHomFMap_app (f ≫ g) ((modulePullback B S hS (f ≫ g)).obj M) M
        ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M) c s)
  have r2 :=
    congrArg
      (fun m : M ⟶ (modulePushforward B S hS (f ≫ g)).obj
          ((modulePullback B S hS (f ≫ g)).obj M) ↦
        modulePushforwardCounitApp B S hS (f ≫ g) ((modulePullback B S hS (f ≫ g)).obj M)
          c (m.val.app (op W) s))
      hassoc.symm
  have r4 := modulePushforwardCounitApp_map B S hS (f ≫ g)
    ((modulePullbackCompIso B S hS f g).hom.app M) c
    ((moduleFMapCompHom B S hS f g _ _ M ug uf
      (modulePushforwardCompIso B S hS f g)).val.app (op W) s)
  have r5 : ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        (modulePushforwardCounitApp B S hS (f ≫ g) _ c
          ((moduleFMapCompHom B S hS f g _ _ M ug uf
            (modulePushforwardCompIso B S hS f g)).val.app (op W) s)) =
      ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        (modulePullbackUnitSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
          (modulePullbackUnitSection B S hS g M ⟨V, W, b, hb⟩ s)) :=
    congrArg (fun y ↦ ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U) y)
      ((hcomp.symm.trans hchart).trans
        ((congrArg (fun z ↦ uf.app ⟨U, V, a, ha⟩ z)
            (modulePushforwardHomFMap_unit_app g M ⟨V, W, b, hb⟩ s)).trans
          (modulePushforwardHomFMap_unit_app f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
            (modulePullbackUnitSection B S hS g M ⟨V, W, b, hb⟩ s))))
  exact (r1.trans (r2.trans (r4.trans r5))).symm

end Factor

end AlgebraicGeometry.Space

end
