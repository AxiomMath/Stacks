module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionTensorPushforwardIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorArbitrary
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorRowComplex
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp

/-!
# Tensoring a complex with a direct image along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`, `P` a complex of
`𝒪_X`-modules on the small étale site and `G` an `𝒪_Z`-module. The underived projection formula
of Stacks 04G0, `F ⊗_{𝒪_X} i_*G ≅ i_*(i^*F ⊗_{𝒪_Z} G)`, holds for every `F` and every `G`
(`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion`). Applied degreewise it
identifies the termwise complex `p ↦ Pᵖ ⊗ i_*G` with `i_*` of the termwise complex
`p ↦ i^*Pᵖ ⊗ G`. When `P` is K-flat with flat terms, this is the complex-level form of the
projection formula `K ⊗^L Ri_*G ≅ Ri_*(Li^*K ⊗^L G)` of Stacks 0DK5 for a closed immersion and a
module `G`.

If moreover `i^*P` is K-flat with quasi-coherent cohomology and `G` is quasi-coherent, then
`p ↦ Pᵖ ⊗ i_*G` has quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.Space.rowComplexModulePushforwardIso`: `(p ↦ Pᵖ ⊗ i_*G) ≅ i_*(p ↦ i^*Pᵖ ⊗ G)`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_rowComplex_modulePushforward`: the
  quasi-coherence of the cohomology of `p ↦ Pᵖ ⊗ i_*G`.

The degreewise pullback in the statements is that of
`(AlgebraicGeometry.Space.smallEtaleRingedToposHom B S hS i).toModulesHom`.

## References

* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Z X : AlgebraicSpaces B S hS}

/-- For a closed immersion `i`, the canonical map `F ⊗ i_*G ⟶ i_*(i^*F ⊗ G)` formed with
`(smallEtaleRingedToposHom B S hS i).toModulesHom` is invertible (Stacks 04G0). -/
theorem isIso_pushforwardTensorMap_toModulesHom_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
    (G : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)) :
    IsIso (Stacks.SheafOfModules.pushforwardTensorMap
      (smallEtaleRingedToposHom B S hS i).toModulesHom F G) := by
  rw [← (smallEtaleRingedToposHom B S hS i).toRingedToposModulesHom_eq_toModulesHom]
  exact isIso_tensorPushforwardMap_of_isClosedImmersion B S hS i hi
    (structureSharpCommRing B S hS i) F G

/-- The direct image of modules along `(smallEtaleRingedToposHom B S hS i).toModulesHom` is
isomorphic to `AlgebraicGeometry.Space.modulePushforward`. -/
def smallEtaleToModulesHomPushforwardIso (i : Z ⟶ X) :
    Stacks.Sheaves.RingedToposModules.pushforwardModules
        (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS i).toModulesHom ≅ modulePushforward B S hS i :=
  (smallEtaleRingedToposHom B S hS i).toModulesPushforwardIso ≪≫
    pushforwardModulesIsoModulePushforward B S hS i

/-- **The projection formula of Stacks 04G0, degreewise.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces, a complex `P` of `𝒪_X`-modules and an `𝒪_Z`-module `G`, the termwise complex
`p ↦ Pᵖ ⊗ i_*G` is `i_*` of the termwise complex `p ↦ i^*Pᵖ ⊗ G`. -/
def rowComplexModulePushforwardIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (G : Modules.{u, u} B S hS Z.1 Z.2) :
    CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O) P ((modulePushforward B S hS i).obj G) ≅
      ((modulePushforward B S hS i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (@CochainComplex.KFlatBifunctor.rowComplex _ _ _ _ _ _ _ _
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (smallEtaleRingedTopos B S hS Z).O)
          (Stacks.SheafOfModules.Tensor.sheafTensor_additive _)
          (((smallEtaleRingedToposHom B S hS i).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) G) :=
  haveI : (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS i).toModulesHom).Additive :=
    Stacks.Sheaves.RingedToposModules.additive_pushforwardModules
      (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X) _
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules
          (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS i).toModulesHom).obj G)).PreservesZeroMorphisms :=
    HomologicalComplex.preservesZeroMorphisms_flip_obj _ _
  (NatIso.mapHomologicalComplex
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O).flip.mapIso
          ((smallEtaleToModulesHomPushforwardIso B S hS i).app G).symm)
      (ComplexShape.up ℤ)).app P ≪≫
    Stacks.SheafOfModules.rowComplexPushforwardIso
      (smallEtaleRingedToposHom B S hS i).toModulesHom G
      (fun F => isIso_pushforwardTensorMap_toModulesHom_of_isClosedImmersion B S hS i hi F G) P ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun _ => (smallEtaleToModulesHomPushforwardIso B S hS i).app _)
      (fun _ _ _ => ((smallEtaleToModulesHomPushforwardIso B S hS i).hom.naturality _).symm)

/-- **Quasi-coherence of `P ⊗ i_*G`.** Let `i : Z ⟶ X` be a closed immersion of algebraic spaces,
`P` a complex of `𝒪_X`-modules whose degreewise pullback `i^*P` is K-flat and has quasi-coherent
cohomology sheaves, and `G` a quasi-coherent `𝒪_Z`-module. Then the termwise complex
`p ↦ Pᵖ ⊗ i_*G` has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherentOnSite_homology_rowComplex_modulePushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hP : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS Z.1 Z.2).O
      (((smallEtaleRingedToposHom B S hS i).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))
    (hq : ∀ n : ℤ,
      ((((smallEtaleRingedToposHom B S hS i).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology n).IsQuasicoherentOnSite)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite) (n : ℤ) :
    ((CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS X.1 X.2).O) P
        ((modulePushforward B S hS i).obj G)).homology n).IsQuasicoherentOnSite := by
  have hL : ∀ m : ℤ, (((HomologicalComplex.single (Modules.{u, u} B S hS Z.1 Z.2)
      (ComplexShape.up ℤ) 0).obj G).homology m).IsQuasicoherentOnSite := by
    intro m
    by_cases hm : m = 0
    · subst hm
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hG
    · exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hm)
  have hC := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Z.1 Z.2).O) _ G))
    (isQuasicoherentOnSite_homology_tensorComplex B S hS Z _ _ hP hq hL n)
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1
    (exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity B S hS i hi)
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso ?_
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS i
      (isAffineHom_of_isClosedImmersion B S hS i.hom hi) _ hC)
  exact ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
      (modulePushforward B S hS i) n).app _).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (rowComplexModulePushforwardIso B S hS i hi P G).symm

end AlgebraicGeometry.Space
