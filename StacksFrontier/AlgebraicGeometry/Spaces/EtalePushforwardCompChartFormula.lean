module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackCompCorrespondence

/-!
# The chart formula for composition with the counit of a direct image along an étale morphism

Let `p_U : X' ⟶ X` be an **étale** morphism of algebraic spaces over a scheme `S` of a big fppf
site `B` and let `f : X ⟶ Y` be arbitrary.  The two chart projections of the direct images
compose: a section of `f_*(p_{U*}N)` over a chart `e.V` of `Y` is carried by the chart component
of the counit at `f` to a section of `p_{U*}N` over the postcomposed chart of `X`, and that by
the chart component of the counit at `p_U` — at the identity-vertical diagram, which is
available because `p_U` is étale — to a section of `N` over the chart `e.U` of `X'`.

This file shows that this composite *is* a linear map of sections along `p_U ≫ f`
(`AlgebraicGeometry.Space.moduleCompCounitFMap`), that the morphism of modules

`f_*(p_{U*}N) ⟶ (p_U ≫ f)_*N`

the module chart correspondence attaches to it is an **isomorphism**, and hence that composition
with the counit of the direct image along `p_U` is a bijection with the stated values on chart
diagrams — which is `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence`, the single
hypothesis of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackCompCorrespondence.lean`.

Discharging it closes the affine-chart step of Stacks 073K part (2): the canonical base-change
comparison `AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d` is bijective for
every quasi-coherent `M` over every diagram of affine étale charts, with no presentation of `M`
assumed.

## Main definitions

* `AlgebraicGeometry.Space.moduleCompCounitFMap`: the composite of the two chart projections, as
  a linear map of sections along `p_U ≫ f`.
* `AlgebraicGeometry.Space.modulePushforwardEtaleCompHom`: the morphism of `𝒪_Y`-modules
  `f_*(p_{U*}N) ⟶ (p_U ≫ f)_*N` the module chart correspondence attaches to it.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCounitApp_modulePushforwardEtaleCompHom`: the
  defining property — the chart projection at `p_U ≫ f` of its value is the composite of the two
  chart projections.
* `AlgebraicGeometry.Space.toFMap_moduleCompCounitFMap`: the `f`-map of sheaves of sets
  underlying the composite chart projection is `AlgebraicGeometry.Space.FMap.comp` of the two
  underlying `f`-maps of the counits.  Every chart diagram over `p_U ≫ f` factors through an
  étale chart of `X` — the postcomposition of its own chart of `X'` — so the chart formula
  `AlgebraicGeometry.Space.FMap.comp_app` applies at every diagram, which is what makes this an
  equality of `f`-maps and not merely an agreement on the factoring ones.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardEtaleCompHom`: on underlying
  sheaves of sets the comparison is the geometric comparison
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3).
* `AlgebraicGeometry.Space.isIso_modulePushforwardEtaleCompHom`: **the comparison is an
  isomorphism**, the geometric comparison being one.
* `AlgebraicGeometry.Space.bijective_modulePullbackEtaleSourceComparison_val_app'` and
  `AlgebraicGeometry.Space.bijective_modulePullbackEtaleSquareComparison_val_app_idChart`: the
  mixed comparison of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackComparison.lean` and the
  comparison of a chart-space square are bijective on sections, unconditionally.

The chart formula for composition with the counit —
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence` — and the chart bijectivity of
Stacks 083K that follows from it —
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite` — are
not proved here: they are
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean`, which obtains the
chart formula from `AlgebraicGeometry.Space.exists_bijective_moduleFMapCompCounit` at the
comparison of Stacks 03LU.  The comparison built in this file is what the two results below
consume.

## Implementation notes

**Why the comparison of direct images is built here rather than taken from Stacks 03LU.**  The
library's comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` is assembled from two
`CategoryTheory.eqToIso`s of equalities of *functors*, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackCompCorrespondence.lean` record,
with measurements, that identifying it with the geometric comparison on underlying sheaves of
sets does not get past the kernel: deciding those equalities of functors unfolds
`AlgebraicGeometry.Space.modulePushforward` at these types and does not terminate.

The comparison of this file is not that one.  It is built from the module chart correspondence
of Stacks 03G4 at `p_U ≫ f` applied to the composite chart projection, so no `eqToIso` enters
it, and its underlying homomorphism of sheaves of sets is identified with the geometric
comparison through the *set-level* composition of Stacks 03G4
(`AlgebraicGeometry.Space.fmapDirectImageEquiv_comp`), where the only comparison that appears is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` itself.  The two counits contribute
nothing to that identification: the homomorphism of sheaves of sets attached to a counit is the
identity, which is
`AlgebraicGeometry.Space.fmapDirectImageEquiv_toFMap_modulePushforwardCounit` below.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Two generalities -/

/-- A morphism of `𝒪_X`-modules on the small étale site of an algebraic space which is bijective
on the sections over every étale chart is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_of_bijective_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean`, which is not in this
file's import closure. -/
private theorem isIso_of_bijective_val_app {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (c : M ⟶ N)
    (hbij : ∀ V : (SmallEtale B S hS Z.1)ᵒᵖ, Function.Bijective (c.val.app V).hom) :
    IsIso c := by
  rw [← isIso_iff_of_reflects_iso c
      (SheafOfModules.toSheaf (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)),
    ← isIso_iff_of_reflects_iso _
      (sheafToPresheaf (smallEtaleRingedSite B S hS Z.1 Z.2).J AddCommGrpCat.{u}),
    NatTrans.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hbij V

/-- Composing with an isomorphism on the target is a bijection of hom-sets. -/
private theorem bijective_comp_isIso {C : Type*} [Category C] {A A' : C} (c : A ⟶ A')
    [IsIso c] (T : C) : Function.Bijective (fun a : T ⟶ A ↦ a ≫ c) := by
  refine ⟨fun a b hab ↦ ?_, fun y ↦ ⟨y ≫ inv c, ?_⟩⟩
  · have h := congrArg (fun m : T ⟶ A' ↦ m ≫ inv c) hab
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h
  · simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-! ### The composite of the two chart projections -/

section Comp

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom) (N : Modules.{u, u} B S hS X'.1 X'.2)

/-- **The composite of the two chart projections, as a linear map of sections along
`p_U ≫ f`.**  At a chart diagram `e` over `p_U ≫ f` it is the chart projection of the direct
image along `f` at the source-postcomposed diagram, followed by the chart projection of the
direct image along `p_U` at the identity-vertical diagram of `e.U`.

Both factors are available at every chart diagram over `p_U ≫ f` because `p_U` is étale: the
postcomposition of the chart of `X'` is a chart of `X`, and the two diagrams meet there. -/
noncomputable def moduleCompCounitFMap :
    ModuleFMap B S hS (pU ≫ f) N
      ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N)) where
  app e y := (modulePushforwardCounit B S hS pU N).app
    (ChartDiagram.etaleUnit B S hS pU hU e.U)
    ((modulePushforwardCounit B S hS f ((modulePushforward B S hS pU).obj N)).app
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) y)
  naturality e e' i j hcond y := by
    refine Eq.trans (congrArg
      ((modulePushforwardCounit B S hS pU N).app
        (ChartDiagram.etaleUnit B S hS pU hU e'.U))
      ((modulePushforwardCounit B S hS f ((modulePushforward B S hS pU).obj N)).naturality
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e)
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e')
        ((smallEtalePostcomp B S hS pU hU).map i) j hcond y)) ?_
    refine (modulePushforwardCounit B S hS pU N).naturality
      (ChartDiagram.etaleUnit B S hS pU hU e.U) (ChartDiagram.etaleUnit B S hS pU hU e'.U)
      i ((smallEtalePostcomp B S hS pU hU).map i) ?_ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  map_add e s t :=
    (congrArg
      ((modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U))
      ((modulePushforwardCounit B S hS f ((modulePushforward B S hS pU).obj N)).map_add
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s t)).trans
      ((modulePushforwardCounit B S hS pU N).map_add
        (ChartDiagram.etaleUnit B S hS pU hU e.U) _ _)
  map_smul e r s := by
    refine Eq.trans (congrArg
      ((modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U))
      ((modulePushforwardCounit B S hS f ((modulePushforward B S hS pU).obj N)).map_smul
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) r s)) ?_
    refine Eq.trans ((modulePushforwardCounit B S hS pU N).map_smul
      (ChartDiagram.etaleUnit B S hS pU hU e.U) _ _) ?_
    exact congrArg (fun c ↦ c • (modulePushforwardCounit B S hS pU N).app
        (ChartDiagram.etaleUnit B S hS pU hU e.U)
        ((modulePushforwardCounit B S hS f ((modulePushforward B S hS pU).obj N)).app
          (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))
      (chartDiagramPullback_etaleUnit_apply B S hS pU hU e.U _)

/-- **The comparison of the iterated direct image with the direct image along the composite**:
the morphism

`f_*(p_{U*}N) ⟶ (p_U ≫ f)_*N`

of `𝒪_Y`-modules which the module chart correspondence of Stacks 03G4 attaches to the composite
of the two chart projections.

No comparison of Stacks 03LU enters its construction; that it agrees with that comparison is not
asserted and is not needed. -/
noncomputable def modulePushforwardEtaleCompHom :
    (modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N) ⟶
      (modulePushforward B S hS (pU ≫ f)).obj N :=
  moduleFMapHom B S hS (pU ≫ f) N
    ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
    (moduleCompCounitFMap B S hS pU f hU N)

/-- **The defining property of the comparison**: its chart projection at `p_U ≫ f` is the
composite of the two chart projections. -/
theorem modulePushforwardCounitApp_modulePushforwardEtaleCompHom
    (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom)
    (y : ((modulePushforward B S hS f).obj
      ((modulePushforward B S hS pU).obj N)).val.obj (op e.V)) :
    modulePushforwardCounitApp B S hS (pU ≫ f) N e
        ((modulePushforwardEtaleCompHom B S hS pU f hU N).val.app (op e.V) y) =
      (moduleCompCounitFMap B S hS pU f hU N).app e y :=
  congrArg
    (fun ζ : ModuleFMap B S hS (pU ≫ f) N ((modulePushforward B S hS f).obj
        ((modulePushforward B S hS pU).obj N)) ↦ ζ.app e y)
    (modulePushforwardHomFMap_moduleFMapHom B S hS (pU ≫ f) N
      ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
      (moduleCompCounitFMap B S hS pU f hU N))

/-! ### The underlying homomorphism of sheaves of sets -/

/-- The homomorphism of sheaves of sets attached to a linear map of sections is the one the
set-level chart correspondence of Stacks 03G4 attaches to the underlying `f`-map.  This is the
definition of `AlgebraicGeometry.Space.moduleFMapSetHom`, isolated so that it is unfolded once
rather than inside a unification. -/
private theorem moduleFMapSetHom_eq {Z W : AlgebraicSpaces B S hS} (g : Z ⟶ W)
    (F : Modules.{u, u} B S hS Z.1 Z.2) (G : Modules.{u, u} B S hS W.1 W.2)
    (ξ : ModuleFMap B S hS g F G) :
    moduleFMapSetHom B S hS g F G ξ =
      fmapDirectImageEquiv B S hS g (moduleSetSheaf B S hS Z F) (moduleSetSheaf B S hS W G)
        (ModuleFMap.toFMap B S hS ξ) := rfl

/-- The homomorphism of sheaves of sets which the chart correspondence of Stacks 03G4 attaches
to the `f`-map underlying a counit of a direct image of modules is the identity: the counit is
the chartwise transpose of the identity. -/
theorem fmapDirectImageEquiv_toFMap_modulePushforwardCounit {Z W : AlgebraicSpaces B S hS}
    (g : Z ⟶ W) (F : Modules.{u, u} B S hS Z.1 Z.2) :
    fmapDirectImageEquiv B S hS g (moduleSetSheaf B S hS Z F)
        (moduleSetSheaf B S hS W ((modulePushforward B S hS g).obj F))
        (ModuleFMap.toFMap B S hS (modulePushforwardCounit B S hS g F)) =
      𝟙 ((smallEtaleDirectImage B S hS g).obj (moduleSetSheaf B S hS Z F)) := by
  refine Eq.trans (congrArg
    (fun ζ : ModuleFMap B S hS g F ((modulePushforward B S hS g).obj F) ↦
      fmapDirectImageEquiv B S hS g (moduleSetSheaf B S hS Z F)
        (moduleSetSheaf B S hS W ((modulePushforward B S hS g).obj F))
        (ModuleFMap.toFMap B S hS ζ))
    (modulePushforwardHomFMap_id B S hS g F).symm) ?_
  refine Eq.trans (moduleFMapSetHom_eq B S hS g F ((modulePushforward B S hS g).obj F)
    (modulePushforwardHomFMap B S hS g F ((modulePushforward B S hS g).obj F) (𝟙 _))).symm ?_
  refine Eq.trans (moduleFMapSetHom_modulePushforwardHomFMap B S hS g F
    ((modulePushforward B S hS g).obj F) (𝟙 _)) ?_
  exact CategoryTheory.Functor.map_id _ _

/-- **The `f`-map underlying the composite chart projection is the set-level composite of the
two `f`-maps underlying the counits.**

Every chart diagram `e` over `p_U ≫ f` factors through an étale chart of `X` — the
postcomposition of `e.U` along `p_U`, with the identity as the first vertical morphism — so the
chart formula `AlgebraicGeometry.Space.FMap.comp_app` applies at `e` itself, and the two
diagrams it reads the components at are the identity-vertical diagram of `e.U` and the
source-postcomposed diagram of `e`. -/
theorem toFMap_moduleCompCounitFMap :
    ModuleFMap.toFMap B S hS (moduleCompCounitFMap B S hS pU f hU N) =
      FMap.comp B S hS pU f (moduleSetSheaf B S hS X' N)
        (moduleSetSheaf B S hS X ((modulePushforward B S hS pU).obj N))
        (moduleSetSheaf B S hS Y ((modulePushforward B S hS f).obj
          ((modulePushforward B S hS pU).obj N)))
        (ModuleFMap.toFMap B S hS (modulePushforwardCounit B S hS f
          ((modulePushforward B S hS pU).obj N)))
        (ModuleFMap.toFMap B S hS (modulePushforwardCounit B S hS pU N)) := by
  refine FMap.ext B S hS (funext fun e ↦ funext fun y ↦ ?_)
  have hdiag : ChartDiagram.comp B S hS pU f
      (ChartDiagram.etaleUnit B S hS pU hU e.U).g
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).g
      (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm = e :=
    ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (Category.id_comp e.g))
  refine Eq.trans (FMap.comp_app B S hS pU f
    (ChartDiagram.etaleUnit B S hS pU hU e.U).g
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).g
    (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm
    (moduleSetSheaf B S hS X' N)
    (moduleSetSheaf B S hS X ((modulePushforward B S hS pU).obj N))
    (moduleSetSheaf B S hS Y ((modulePushforward B S hS f).obj
      ((modulePushforward B S hS pU).obj N)))
    (ModuleFMap.toFMap B S hS (modulePushforwardCounit B S hS f
      ((modulePushforward B S hS pU).obj N)))
    (ModuleFMap.toFMap B S hS (modulePushforwardCounit B S hS pU N)) y).symm ?_
  exact eq_of_heq (FMap.app_heq B S hS _ hdiag HEq.rfl)

/-- **On underlying sheaves of sets the comparison is the geometric comparison of Stacks 03G2,
part (3).**

The homomorphism of sheaves of sets attached to the comparison is the one the chart
correspondence of Stacks 03G4 attaches to the composite chart projection, which by
`AlgebraicGeometry.Space.toFMap_moduleCompCounitFMap` is the set-level composite of the two
counits; the compatibility `AlgebraicGeometry.Space.fmapDirectImageEquiv_comp` of Stacks 03G4
with composition writes that as the two homomorphisms of the counits — both identities —
followed by the geometric comparison. -/
theorem moduleSheafFunctor_map_modulePushforwardEtaleCompHom :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        (modulePushforwardEtaleCompHom B S hS pU f hU N) =
      (smallToposMorphismTypeU_comp B S hS pU f).hom.app (moduleSetSheaf B S hS X' N) := by
  have h1 := moduleFMapSetHom_modulePushforwardHomFMap B S hS (pU ≫ f) N
    ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
    (modulePushforwardEtaleCompHom B S hS pU f hU N)
  have h2 : modulePushforwardHomFMap B S hS (pU ≫ f) N
      ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
      (modulePushforwardEtaleCompHom B S hS pU f hU N) =
      moduleCompCounitFMap B S hS pU f hU N :=
    modulePushforwardHomFMap_moduleFMapHom B S hS (pU ≫ f) N
      ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
      (moduleCompCounitFMap B S hS pU f hU N)
  rw [h2] at h1
  refine Eq.trans h1.symm ?_
  refine Eq.trans (moduleFMapSetHom_eq B S hS (pU ≫ f) N
    ((modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
    (moduleCompCounitFMap B S hS pU f hU N)) ?_
  rw [toFMap_moduleCompCounitFMap B S hS pU f hU N,
    fmapDirectImageEquiv_comp B S hS pU f,
    fmapDirectImageEquiv_toFMap_modulePushforwardCounit B S hS f
      ((modulePushforward B S hS pU).obj N),
    fmapDirectImageEquiv_toFMap_modulePushforwardCounit B S hS pU N]
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (smallToposMorphismTypeU_comp B S hS pU f).hom.app
      (moduleSetSheaf B S hS X' N))
    (CategoryTheory.Functor.map_id (smallEtaleDirectImage B S hS f)
      ((smallEtaleDirectImage B S hS pU).obj (moduleSetSheaf B S hS X' N)))) ?_
  exact Category.id_comp _

/-- **The comparison is an isomorphism**: on underlying sheaves of sets it is the geometric
comparison of Stacks 03G2, part (3), which is one, so it is bijective on the sections over every
chart. -/
theorem isIso_modulePushforwardEtaleCompHom :
    IsIso (modulePushforwardEtaleCompHom B S hS pU f hU N) := by
  have hcomp := moduleSheafFunctor_map_modulePushforwardEtaleCompHom B S hS pU f hU N
  refine isIso_of_bijective_val_app B S hS _ fun V ↦ ?_
  have : IsIso ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      (modulePushforwardEtaleCompHom B S hS pU f hU N)) := by
    rw [hcomp]
    exact ((smallToposMorphismTypeU_comp B S hS pU f).app _).isIso_hom
  exact (isIso_iff_bijective _).1 (inferInstance : IsIso (((Sheaf.moduleSheafFunctor
    (structureRingSheaf B S hS Y)).map (modulePushforwardEtaleCompHom B S hS pU f hU N)).hom.app V))

/-- **The chartwise transpose of a morphism into the iterated direct image, composed with the
comparison**: at a chart diagram `e` over `p_U ≫ f` it is the chart projection of the direct
image along `p_U` at the identity-vertical diagram of `e.U`, applied to the value at the
source-postcomposed diagram of the chartwise transpose at `f`.

This is the defining property of the comparison, read through the two chart correspondences; it
is the chart formula the hypothesis of
`AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` asks for. -/
theorem modulePushforwardHomFMap_comp_modulePushforwardEtaleCompHom
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (a : M ⟶ (modulePushforward B S hS f).obj ((modulePushforward B S hS pU).obj N))
    (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)) :
    (modulePushforwardHomFMap B S hS (pU ≫ f) N M
        (a ≫ modulePushforwardEtaleCompHom B S hS pU f hU N)).app e s =
      (modulePushforwardCounit B S hS pU N).app (ChartDiagram.etaleUnit B S hS pU hU e.U)
        ((modulePushforwardHomFMap B S hS f ((modulePushforward B S hS pU).obj N) M a).app
          (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) :=
  modulePushforwardCounitApp_modulePushforwardEtaleCompHom B S hS pU f hU N e
    (a.val.app (op e.V) s)

end Comp

/-! ### The consequences, unconditionally -/

/-- **The mixed comparison of a composite with an étale first factor is bijective on the
sections over every chart.** -/
theorem bijective_modulePullbackEtaleSourceComparison_val_app'
    {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y) (hU : IsEtale B S hS pU.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (k : X' ⟶ Y) (hk : pU ≫ f = k)
    (W : SmallEtale B S hS X'.1) :
    Function.Bijective
      ((modulePullbackEtaleSourceComparison B S hS pU f hU k hk M).val.app (op W)) :=
  bijective_modulePullbackEtaleSourceComparison_val_app B S hS pU f hU M
    (moduleFMapEtaleSourceCompCorrespondence B S hS pU f hU) k hk W

/-- **The comparison of the chart-space square of a diagram of étale charts is bijective on the
sections over the identity chart.**

This is the hypothesis of
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison`, with
no hypothesis of its own: neither quasi-coherence of `M` nor affineness of the two charts is
needed for it. -/
theorem bijective_modulePullbackEtaleSquareComparison_val_app_idChart (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Function.Bijective
      ((modulePullbackEtaleSquareComparison B S hS f (chartSpaceMapOver B S hS d.g)
        (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
        (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M).val.app
        (op (chartSpaceIdChartDiagram B S hS f d).U)) :=
  (bijective_modulePullbackEtaleSquareComparison_val_app_iff B S hS f
    (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
    (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M
    (Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable
      (chartToSpace B S hS Y d.V).hom)
    (chartSpaceIdChartDiagram B S hS f d).U).2
    (bijective_modulePullbackEtaleSourceComparison_val_app' B S hS
      (chartToSpace B S hS X d.U) f (isEtale_chartToSpace B S hS X d.U) M
      (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V)
      (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm).symm
      (chartSpaceIdChartDiagram B S hS f d).U)

end AlgebraicGeometry.Space

end
