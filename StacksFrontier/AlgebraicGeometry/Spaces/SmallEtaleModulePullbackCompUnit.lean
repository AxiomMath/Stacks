module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The unit of étale restriction of modules against the unit of étale restriction of sheaves of sets

Let `f : X ⟶ Y` be an étale *representable* morphism of algebraic spaces over a scheme `S` in a
big fppf site `B`.  Restriction of `𝒪`-modules along `f` and restriction of sheaves of sets along
`f` are the same operation on underlying sheaves — both are restriction of sections along
postcomposition of charts — and their direct images likewise agree on underlying sheaves.  The two
adjunctions `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` (Stacks 03LU read through
Stacks 03LW) and `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` therefore have units
living in the same place, and this file proves that they are **equal**.

That is not formal: the unit of Stacks 03LU is the unit of the inverse image of Stacks 03D6, which
carries an extension of scalars, read through the identification of Stacks 03LW.  What makes the
comparison available is **(†)** of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnitTransport.lean`: its
ingredient `AlgebraicGeometry.Space.chartSetProj_etaleModulePullbackAdjunction_unit` says that the
chart projection of the module unit is restriction of sections along the cartesian projection
`V ×_Y X ⟶ V`, and `AlgebraicGeometry.Space.chartSetProj_setRestrictionAdjunction_unit` says the
same of the set-level unit.  The chart projection is an isomorphism, hence injective, so the two
units agree.

## Main results

* `AlgebraicGeometry.Space.chartSetProj_injective`: the chart projection of a section of the
  direct image of sheaves of sets is injective — it is the projection of a limit over a category
  with an initial object, read through an isomorphism.
* `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq`: **the unit of
  Stacks 03LU and the unit of étale restriction of sheaves of sets agree on sections.**
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit`: the same,
  as an equality of morphisms of sheaves of sets.  This is the form in which the set-level
  composition law `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app` can
  be fed module-level data.
The identification of the composition comparison of the direct images of modules with the
geometric comparison of Stacks 03G2, part (3), on sections, is *not* here: it is
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, where
Stacks 03M8 states it.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_unit_app`: the unit of the
  adjunction of étale restriction along a composite assembled from the two factors, written out.

## What is not done

The next step of the route to Stacks 03LY — the chart projection of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction`, and with it the square
`AlgebraicGeometry.Space.SmallBaseChangeModulePushforwardCompSquare` — is **not** taken here.
What it needs is
`AlgebraicGeometry.Space.modulePushforward_map_eq_directImage_map` instantiated at the unit of
Stacks 03LU at `h`, so that
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app` — the set-level
composition law, which the tree already proves — applies to the composite unit.  That
instantiation does not elaborate: writing the resulting statement forces the elaborator to
reconcile `(Sheaf.moduleSheafFunctor _).obj ((modulePushforward h).obj N)` with
`(smallEtaleDirectImage h).obj (moduleSetSheaf N)` *and*
`moduleSetSheaf ((etaleModulePullback h hh).obj M)` with
`(smallEtaleSetRestriction h hh).obj (moduleSetSheaf M)` inside one declaration, each of which
costs a large fraction of the heartbeat budget on its own.  Splitting the statement moves the
cost but does not remove it: every spelling of the step mentions both reconciliations, because
the direct image along `g` is applied to a morphism whose source and target are the two sides of
the second one.  The obstruction is elaboration, not mathematics.

## Implementation notes

The reconciliations that do not fit the heartbeat budget are performed at *variables*, in the
auxiliary namespace `Stacks.ChartUnitComp`: `Stacks.ChartUnitComp.moduleSheafFunctor_map_eq`
takes the sectionwise identity and the two morphisms as hypotheses, so that the passage from an
equality of sections to an equality of morphisms of sheaves of sets never has to be decided at the
concrete units.  Written directly at the concrete units — with `CategoryTheory.Sheaf.hom_ext` and
`funext`, or with `CategoryTheory.Sheaf.hom_ext_sections` — it does not elaborate.

For the same reason the unit of the composite adjunction is written out in three steps, each the
transport lemma of one of the three adjunction constructions it is built from.  Taking the whole
decomposition by `rfl`, or by `simp only` with the three lemmas, exceeds the budget: the composite
adjunction is `CategoryTheory.Adjunction.mk'`, whose unit does not reduce cheaply.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

namespace Stacks.ChartUnitComp

universe w v uu

variable {CC : Type uu} [Category.{v} CC] {J : GrothendieckTopology CC}
    {R : Sheaf J RingCat.{w}}

/-- The underlying sheaf of sets of a morphism of sheaves of modules acts on sections as the
morphism itself. -/
theorem moduleSheafFunctor_map_hom_app_apply {M N : SheafOfModules.{w} R} (psi : M ⟶ N)
    (W : CCᵒᵖ) (s : M.val.obj W) :
    ((Sheaf.moduleSheafFunctor R).map psi).hom.app W s = psi.val.app W s := rfl

/-- **A morphism of sheaves of modules has a prescribed underlying morphism of sheaves of sets as
soon as the two agree on sections.**  The two morphisms are hypotheses rather than terms built in
the statement, so that the reconciliation of the sections of a sheaf of modules with the sections
of its underlying sheaf of sets is decided here, at variables; see the implementation notes. -/
theorem moduleSheafFunctor_map_eq {M N : SheafOfModules.{w} R} (psi : M ⟶ N)
    (chi : (Sheaf.moduleSheafFunctor R).obj M ⟶ (Sheaf.moduleSheafFunctor R).obj N)
    (hps : ∀ (W : CCᵒᵖ) (s : ((Sheaf.moduleSheafFunctor R).obj M).obj.obj W),
      ((Sheaf.moduleSheafFunctor R).map psi).hom.app W s = chi.hom.app W s) :
    (Sheaf.moduleSheafFunctor R).map psi = chi := by
  apply Sheaf.hom_ext
  ext W s
  exact hps W s

end Stacks.ChartUnitComp

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two units of étale restriction -/

section Single

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)

/-- **The chart projection of a section of the direct image is injective.**  It is the projection
of the limit of the sections over the charts above the base-changed chart to its initial index,
read through the comparison of the direct image with its right Kan extension form; both are
isomorphisms. -/
theorem chartSetProj_injective
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1) :
    Function.Injective (chartSetProj B S hS f hrep F V) :=
  Function.Injective.comp
    ((CategoryTheory.isIso_iff_bijective (chartRanApp B S hS f hrep F.obj V)).mp
      inferInstance).1
    ((CategoryTheory.isIso_iff_bijective
      (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app
        (op (chartBaseChange B S hS f V)))).mp inferInstance).1

include hrep in
/-- The unit of `etaleModulePullbackAdjunction` and the unit of
`smallEtaleSetRestrictionAdjunction` agree on sections: for an `𝒪_Y`-module `M` and an object `V`
of the small étale site of `Y`, both send a section of `M` over `V` to the same section of the
pullback over `V`. -/
theorem etaleModulePullbackAdjunction_unit_val_app_eq
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    (x : M.val.obj (op V)) :
    (((etaleModulePullbackAdjunction B S hS f hf).unit.app M).val.app (op V) x : _) =
      ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (moduleSetSheaf B S hS Y M)).hom.app (op V) x :=
  chartSetProj_injective B S hS f hrep
    (moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) V
    ((chartSetProj_etaleModulePullbackAdjunction_unit B S hS f hf hrep M V x).trans
      (chartSetProj_setRestrictionAdjunction_unit B S hS f hf hrep
        (moduleSetSheaf B S hS Y M) V x).symm)

include hrep in
/-- `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq` with the left-hand
side read on the underlying sheaf of sets, which is the spelling
`Stacks.ChartUnitComp.moduleSheafFunctor_map_eq` consumes. -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_hom_app
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : M.val.obj V) :
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
          ((etaleModulePullbackAdjunction B S hS f hf).unit.app M)).hom.app V x =
      ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (moduleSetSheaf B S hS Y M)).hom.app V x :=
  (Stacks.ChartUnitComp.moduleSheafFunctor_map_hom_app_apply
      ((etaleModulePullbackAdjunction B S hS f hf).unit.app M) V x).trans
    (etaleModulePullbackAdjunction_unit_val_app_eq B S hS f hf hrep M V.unop x)

include hrep in
/-- **The underlying morphism of sheaves of sets of the unit of Stacks 03LU is the unit of étale
restriction of sheaves of sets.** -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (show moduleSetSheaf B S hS Y M ⟶
        (smallEtaleDirectImage B S hS f).obj
          (moduleSetSheaf B S hS X ((etaleModulePullback.{u, u} B S hS f hf).obj M)) from
      (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
        ((etaleModulePullbackAdjunction B S hS f hf).unit.app M)) =
      (smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (moduleSetSheaf B S hS Y M) :=
  Stacks.ChartUnitComp.moduleSheafFunctor_map_eq
    ((etaleModulePullbackAdjunction B S hS f hf).unit.app M)
    ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app (moduleSetSheaf B S hS Y M))
    (fun V x ↦ moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_hom_app
      B S hS f hf hrep M V x)

end Single

/-! ### The unit of étale restriction along a composite -/

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-- The unit of `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction` is the unit of its
composite adjunction followed by the strict composition of étale restrictions: the first of the
three transports the definition performs. -/
theorem etaleModulePullbackCompAdjunction_unit_eq :
    (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (((etaleModulePullbackAdjunction B S hS g hg).comp
          (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
            (modulePushforwardCompIso B S hS h g)).unit ≫
        Functor.whiskerRight (etaleModulePullbackComp B S hS h g hh hg hhg).hom
          (modulePushforward B S hS (h ≫ g)) :=
  Adjunction.ofNatIsoLeft_unit _ _

/-- The second transport: reading the right adjoint of the composite adjunction through the
composition comparison of the direct images composes that comparison onto the unit. -/
theorem ofNatIsoRight_comp_unit_eq :
    (((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
          (modulePushforwardCompIso B S hS h g)).unit =
      ((etaleModulePullbackAdjunction B S hS g hg).comp
          (etaleModulePullbackAdjunction B S hS h hh)).unit ≫
        Functor.whiskerLeft
          (etaleModulePullback.{u, u} B S hS g hg ⋙
            etaleModulePullback.{u, u} B S hS h hh)
          (modulePushforwardCompIso B S hS h g).hom :=
  Adjunction.ofNatIsoRight_unit _ _

/-- The third: the unit of a composite of adjunctions is the unit of the outer one followed by
the direct image of the unit of the inner one. -/
theorem comp_unit_app_eq (M : Modules.{u, u} B S hS C.1 C.2) :
    ((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).unit.app M =
      (etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
        (modulePushforward B S hS g).map
          ((etaleModulePullbackAdjunction B S hS h hh).unit.app
            ((etaleModulePullback.{u, u} B S hS g hg).obj M)) :=
  Adjunction.comp_unit_app _ _ M

/-- The unit of the composite adjunction read through the composition comparison, written
out. -/
theorem ofNatIsoRight_comp_unit_app_eq (M : Modules.{u, u} B S hS C.1 C.2) :
    (((etaleModulePullbackAdjunction B S hS g hg).comp
        (etaleModulePullbackAdjunction B S hS h hh)).ofNatIsoRight
          (modulePushforwardCompIso B S hS h g)).unit.app M =
      ((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
          (modulePushforward B S hS g).map
            ((etaleModulePullbackAdjunction B S hS h hh).unit.app
              ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
        (modulePushforwardCompIso B S hS h g).hom.app
          ((etaleModulePullback.{u, u} B S hS g hg ⋙
            etaleModulePullback.{u, u} B S hS h hh).obj M) :=
  (CategoryTheory.NatTrans.congr_app
      (ofNatIsoRight_comp_unit_eq B S hS h g hh hg) M).trans
    (Stacks.CategoryTheory.proj_congr (comp_unit_app_eq B S hS h g hh hg M)
      (fun m ↦ m ≫ (modulePushforwardCompIso B S hS h g).hom.app
        ((etaleModulePullback.{u, u} B S hS g hg ⋙
          etaleModulePullback.{u, u} B S hS h hh).obj M)))

/-- **The unit of étale restriction along a composite, written out**: the unit at `g`, the direct
image along `g` of the unit at `h`, the composition comparison of the direct images, and the
strict composition of the étale restrictions. -/
theorem etaleModulePullbackCompAdjunction_unit_app (M : Modules.{u, u} B S hS C.1 C.2) :
    (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit.app M =
      (((etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
            (modulePushforward B S hS g).map
              ((etaleModulePullbackAdjunction B S hS h hh).unit.app
                ((etaleModulePullback.{u, u} B S hS g hg).obj M))) ≫
          (modulePushforwardCompIso B S hS h g).hom.app
            ((etaleModulePullback.{u, u} B S hS g hg ⋙
              etaleModulePullback.{u, u} B S hS h hh).obj M)) ≫
        (modulePushforward B S hS (h ≫ g)).map
          ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M) :=
  (CategoryTheory.NatTrans.congr_app
      (etaleModulePullbackCompAdjunction_unit_eq B S hS h g hh hg hhg) M).trans
    (Stacks.CategoryTheory.proj_congr
      (ofNatIsoRight_comp_unit_app_eq B S hS h g hh hg M)
      (fun m ↦ m ≫ (modulePushforward B S hS (h ≫ g)).map
        ((etaleModulePullbackComp B S hS h g hh hg hhg).hom.app M)))

/-- The direct image of modules acts on sections as the direct image of the underlying sheaves
of sets.  Stated at a variable morphism, where the two spellings reduce to one another. -/
theorem modulePushforward_map_val_app_setSheaf {N N' : Modules.{u, u} B S hS A.1 A.2}
    (al : N ⟶ N') (W : (SmallEtale B S hS C.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj N).val.obj W) :
    ((((modulePushforward B S hS g).map al).val.app W z : _) : _) =
      ((smallEtaleDirectImage B S hS g).map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS A)).map
          al)).hom.app W z := rfl

/-- **The direct image along `g` of a morphism of modules, on sections, is the direct image of
any morphism of sheaves of sets that the morphism underlies.**  Everything is a variable, so the
reconciliation of the sections of a direct image of modules with those of the direct image of
the underlying sheaf of sets is decided here and never again. -/
theorem modulePushforward_map_eq_directImage_map {N N' : Modules.{u, u} B S hS A.1 A.2}
    (al : N ⟶ N')
    {chi : (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS A)).obj N ⟶
      (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS A)).obj N'}
    (e : (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS A)).map al = chi)
    (W : (SmallEtale B S hS C.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj N).val.obj W) :
    ((((modulePushforward B S hS g).map al).val.app W z : _) : _) =
      ((smallEtaleDirectImage B S hS g).map chi).hom.app W z := by
  rw [← e]
  exact modulePushforward_map_val_app_setSheaf B S hS g al W z

end Comp

end AlgebraicGeometry.Space

end
