module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The functors of formal glueing of modules, and their adjunction

In a formal glueing situation, with `j : U → X` the open immersion, `f : Y → X` the ambient
morphism and `j' : V → Y` the open immersion over it, this file constructs the functor
`QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)`, `F ↦ (F|_U, f^*F, can)`, the functor
`(H, G, φ) ↦ Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))` in the other direction, and the adjunction
between them, with no further hypotheses.

The underlying functors into the ambient comma category and into all `𝒪_X`-modules are
`quasicoherentGlueingDiagram` and `glueingKernelDiagram`; their values are quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` and the
theorems of `FormalGlueingModulesQuasicoherence.lean`. The adjunction is
`CategoryTheory.Adjunction.toCommaPullbackAdjunctionRestrict` instantiated at them.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModulesFunctor`: the functor
  `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)`, `F ↦ (F|_U, f^*F, can)`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelFunctor`: the functor
  `(H, G, φ) ↦ Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingAdjunction`: the first functor is left
  adjoint to the second.

## References

* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 0AEY](https://stacks.math.columbia.edu/tag/0AEY)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- The functor `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of formal glueing: a quasi-coherent `𝒪_X`-module
`F` goes to `(F|_U, f^*F, can)`. -/
@[stacks 0AEW "the functor, with no hypothesis"]
def glueingModulesFunctor :
    QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 ⥤ D.moduleGlueingData :=
  ObjectProperty.lift _ D.quasicoherentGlueingDiagram fun M ↦
    ⟨D.isIso_quasicoherentGlueingDiagram_obj_hom M,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.openImmersion
        M.obj M.property,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.ambientMorphism
        M.obj M.property⟩

/-- The underlying triple of `glueingModulesFunctor` at `M` is `quasicoherentGlueingDiagram` at
`M`. -/
@[simp]
theorem glueingModulesFunctor_obj_obj
    (M : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    (D.glueingModulesFunctor.obj M).obj = D.quasicoherentGlueingDiagram.obj M := rfl

/-- The underlying morphism of `glueingModulesFunctor` at `a` is `quasicoherentGlueingDiagram`
at `a`. -/
@[simp]
theorem glueingModulesFunctor_map_hom
    {M N : QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2} (a : M ⟶ N) :
    InducedCategory.Hom.hom (D.glueingModulesFunctor.map a) =
      D.quasicoherentGlueingDiagram.map a := rfl

/-- The module `glueingKernelDiagram.obj t` attached to a glueing triple `t` with
quasi-coherent components is quasi-coherent. -/
theorem isQuasicoherentOnSite_glueingKernelDiagram_obj_of_quasicoherent
    (t : D.moduleGlueingComma) (hleft : t.left.IsQuasicoherentOnSite)
    (hright : t.right.IsQuasicoherentOnSite) :
    (D.glueingKernelDiagram.obj t).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (D.glueingKernelDiagramObjIso t).symm
    (D.hasQuasicoherentKernels_spaceX (D.glueingKernelMap.app t)
      (D.isQuasicoherentOnSite_directImageSum_obj
        D.modulePushforwardPreservesQuasicoherence_openImmersion
        D.modulePushforwardPreservesQuasicoherence_ambientMorphism t hleft hright)
      (D.modulePushforwardPreservesQuasicoherence_overlapImmersion _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          D.openImmersionOver t.right hright)))

/-- The functor `QCoh(Y → X, Z) ⥤ QCoh(𝒪_X)`,
`(H, G, φ) ↦ Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`. -/
@[stacks 0AEX "the functor, with no hypothesis"]
def glueingKernelFunctor :
    D.moduleGlueingData ⥤ QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ D.glueingKernelDiagram) fun t ↦
    D.isQuasicoherentOnSite_glueingKernelDiagram_obj_of_quasicoherent t.obj
      t.property.2.1 t.property.2.2

/-- The underlying module of `glueingKernelFunctor` at `t` is `glueingKernelDiagram` at `t`. -/
@[simp]
theorem glueingKernelFunctor_obj_obj (t : D.moduleGlueingData) :
    (D.glueingKernelFunctor.obj t).obj = D.glueingKernelDiagram.obj t.obj := rfl

/-- The underlying morphism of `glueingKernelFunctor` at `a` is `glueingKernelDiagram` at the
underlying morphism of `a`. -/
@[simp]
theorem glueingKernelFunctor_map_hom {t s : D.moduleGlueingData} (a : t ⟶ s) :
    InducedCategory.Hom.hom (D.glueingKernelFunctor.map a) =
      D.glueingKernelDiagram.map (InducedCategory.Hom.hom a) := rfl

/-- The functor `glueingModulesFunctor` is left adjoint to the functor
`glueingKernelFunctor`. -/
@[stacks 0AEY "with no hypothesis"]
def glueingAdjunction : D.glueingModulesFunctor ⊣ D.glueingKernelFunctor :=
  Adjunction.toCommaPullbackAdjunctionRestrict
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel
    (show D.ambientInclusion.FullyFaithful from ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    D.quasicoherentOverlapComparison D.quasicoherentOverlapComparison_eq rfl rfl

end AlgebraicGeometry.Space.FormalGlueingSituation

end
