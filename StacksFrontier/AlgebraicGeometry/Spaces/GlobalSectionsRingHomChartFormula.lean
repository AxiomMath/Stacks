module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsRingHomOnSections

/-!
# The ring map on global sections of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.  The morphism of small étale ringed
topoi of Stacks 03G8 induces, abstractly, a ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`,
`Stacks.Cohomology.SiteModules.globalSectionsRingHom`: it is the ring map through which global
sections of a direct image `f_* N` are identified with global sections of `N`
(`Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv`).  This file shows that it is
the pullback of global regular functions, `AlgebraicGeometry.Space.globalFunctionsMap`.

## Main results

* `AlgebraicGeometry.Space.globalSectionsRingHom_val_chartDiagram`: on a commutative diagram of
  étale scheme charts over `f`, the ring map is pullback of regular functions along the vertical
  morphism of schemes.
* `AlgebraicGeometry.Space.globalFunctionsMap_val_chartDiagram`: the same for the pullback of
  global functions.
* `AlgebraicGeometry.Space.exists_chartDiagram_isSurjective`: there is such a diagram whose
  chart of the source is surjective (Stacks 02X1).
* `AlgebraicGeometry.Space.globalSectionsRingHom_eq_globalFunctionsMap`: the two ring maps
  agree.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- The structure map of the four-field morphism of small étale ringed topoi of a morphism of
algebraic spaces, read on underlying sheaves of sets, is the structure map of Stacks 03G8. -/
theorem sheafCompose_forget_map_smallEtaleRingedToposModulesHom_fSharp (f : X ⟶ Y) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp =
      structureSharpSet B S hS f := by
  have h3 : (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
      (structureSharp B S hS f) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp := by
    rw [← forgetCommRingSheaf_map_fSharp B S hS f]
    exact Sheaf.hom_ext_sections fun _ _ ↦ rfl
  have hfi : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (smallEtaleRingedToposHom B S hS f).ringFsharpInverseImage =
      (smallEtaleRingedTopos B S hS X).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage :=
    Sheaf.hom_ext_sections fun _ _ ↦ rfl
  change _ = (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    (structureSharp B S hS f)
  rw [h3]
  change (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    (smallEtaleRingedToposHom B S hS f).ringFsharp = _
  exact (smallEtaleRingedToposHom B S hS f).ringSheafMap_ringFsharp.trans
    ((congrArg (fun m ↦ ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _) m)
      (hfi.trans (smallEtaleRingedToposHom B S hS f).fSharpInverseImage_forget_homEquiv)).trans
      (Equiv.apply_symm_apply _ _))

/-- **The ring map on global sections of a morphism of algebraic spaces, on a diagram of
charts.**  For a commutative diagram of étale scheme charts `U ⟶ V` over `f : X ⟶ Y`, the value
on `U` of the image of a global section `b` of `𝒪_Y` is the pullback of `b|_V` along `U ⟶ V`.
This is `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq` with the chart projection
of the direct image attached to the diagram, which carries the structure map to pullback along
the vertical morphism. -/
theorem globalSectionsRingHom_val_chartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O).obj) :
    (Stacks.Cohomology.SiteModules.globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)
        b).1 (op d.U) =
      (chartDiagramPullback B S hS f d).hom (b.1 (op d.V)) := by
  refine (Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq
    (smallEtaleRingedToposModulesHom B S hS f) (W := op d.V) (Z := op d.U)
    (directImageChartProjection B S hS f d.V
      (StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS f d).op)) b).trans ?_
  rw [sheafCompose_forget_map_smallEtaleRingedToposModulesHom_fSharp]
  exact directImageChartProjection_structureSharpSet_chartDiagram B S hS f d (b.1 (op d.V))

/-- **Pullback of global functions on a diagram of charts.**  For a commutative diagram of
étale scheme charts `U ⟶ V` over `f : X ⟶ Y`, the value on `U` of the pullback of a global
function `b` of `Y` is the pullback of `b|_V` along `U ⟶ V`. -/
theorem globalFunctionsMap_val_chartDiagram (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : globalFunctions B S hS Y.1) :
    (globalFunctionsMap B S hS f b).val (op d.U) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom (b.val (op d.V)) := by
  rw [← globalFunctionsChartEquiv_val_etale B S hS X, globalFunctionsMap_chart,
    ← globalFunctionsChartEquiv_val_etale B S hS Y b d.V]
  exact (((globalFunctionsChartEquiv B S hS Y).val b).property
    (CostructuredArrow.homMk d.g d.comm.symm :
      CostructuredArrow.mk (d.U.1.hom ≫ f.hom) ⟶ CostructuredArrow.mk d.V.1.hom).op).symm

/-- **A morphism of algebraic spaces has a diagram of étale scheme charts with surjective
source chart.**  A surjective étale chart of the target lifts to a surjective étale chart of the
source with a morphism to it, by Stacks 02X1. -/
theorem exists_chartDiagram_isSurjective (f : X ⟶ Y) :
    ∃ d : ChartDiagram B S hS X.1 Y.1 f.hom, IsSurjective B S hS d.U.obj.hom := by
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  obtain ⟨U, p, α, hcomm, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.property Y.property f.hom V q hqS hqE
  exact ⟨⟨⟨CostructuredArrow.mk p, hpE⟩, ⟨CostructuredArrow.mk q, hqE⟩, α, hcomm⟩,
    (surjective_iff_surjective_pointsMap B S hS X.obj X.property U p).1 hpS⟩

/-- **The ring map on global sections of a morphism of algebraic spaces is the pullback of
global regular functions.**  Both are pullback along the vertical morphism on every diagram of
étale scheme charts over `f`, and one such diagram has a surjective source chart, on which a
global function is determined by its restriction. -/
theorem globalSectionsRingHom_eq_globalFunctionsMap (f : X ⟶ Y)
    (b : globalFunctions B S hS Y.1) :
    (Stacks.Cohomology.SiteModules.globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)
        ⟨b.1, b.2⟩).1 = (globalFunctionsMap B S hS f b).1 := by
  obtain ⟨d, hd⟩ := exists_chartDiagram_isSurjective B S hS f
  have h := injective_globalFunctions_val_of_isSurjective B S hS X.obj X.property d.U hd
    (a₁ := ⟨(Stacks.Cohomology.SiteModules.globalSectionsRingHom
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposModulesHom B S hS f) ⟨b.1, b.2⟩).1,
      (Stacks.Cohomology.SiteModules.globalSectionsRingHom
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposModulesHom B S hS f) ⟨b.1, b.2⟩).2⟩)
    (a₂ := globalFunctionsMap B S hS f b)
    ((globalSectionsRingHom_val_chartDiagram B S hS f d ⟨b.1, b.2⟩).trans
      (globalFunctionsMap_val_chartDiagram B S hS f d b).symm)
  exact congrArg Subtype.val h

end AlgebraicGeometry.Space

end
