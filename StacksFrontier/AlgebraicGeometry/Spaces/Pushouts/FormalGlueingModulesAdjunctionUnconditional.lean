module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFunctorUnconditional

/-!
# The adjunction of formal glueing, with no inverse-image hypothesis

Stacks 0AEY is formalized, with no hypothesis, as
`AlgebraicGeometry.Space.FormalGlueingSituation.glueingAdjunction` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional`.  This file
states the adjunction for the functor of Stacks 0AEW without the inverse-image factor of
Stacks 03DO for the open immersion `j` and for the ambient morphism `f` — the quasi-coherence of
the two outer components of its triples is Stacks 03GA at an arbitrary morphism — and for the
right adjoint taking the five hypotheses of Stacks 0AEX.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingModulesAdjunctionUnconditional`: the
  adjunction of Stacks 0AEY, taking only the five hypotheses of the right adjoint of
  Stacks 0AEX.

## References

* [Stacks Project, Tag 0AEY](https://stacks.math.columbia.edu/tag/0AEY)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FormalGlueingSituation

variable (D : FormalGlueingSituation B S hS)

/-- **Stacks 0AEY.**  In the formal glueing situation of Stacks 0AEV, the functor
`QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of Stacks 0AEW is left adjoint to the functor
`QCoh(Y → X, Z) ⥤ QCoh(𝒪_X)` of Stacks 0AEX.

The adjunction is a term: its hom-set bijection sends a morphism of glueing triples to the pair
of the transposes of its two components, which the commutative square of the morphism makes a
section of the kernel of Stacks 0AEX.

The five hypotheses are exactly those of the two functors: Stacks 0AEW needs none, and
Stacks 0AEX needs Stacks 03M9 for `j`, for `f` and for `f ∘ j'`, Stacks 03GA for `j'` and the
kernel clause of Stacks 03M1 for `X`.  No hypothesis of the formal glueing situation beyond the
openness of `U` and of `V` is used; the finite presentation of `Z` and the flatness of `f` along
`f⁻¹(Z)` are needed only for Stacks 0AF0, that this adjunction is an equivalence. -/
def glueingModulesAdjunctionUnconditional
    (quasicoherentPushforward_openImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion)
    (quasicoherentPushforward_ambientMorphism :
      ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism)
    (quasicoherentPushforward_overlapImmersion :
      ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion)
    (quasicoherentPullback_openImmersionOver :
      HasLocalInverseImagePresentations B S hS D.openImmersionOver)
    (quasicoherentKernels : HasQuasicoherentKernels B S hS D.spaceX.1 D.spaceX.2) :
    D.glueingModulesUnconditional ⊣
      D.glueingKernelModules quasicoherentPushforward_openImmersion
        quasicoherentPushforward_ambientMorphism quasicoherentPushforward_overlapImmersion
        quasicoherentPullback_openImmersionOver quasicoherentKernels :=
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

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
