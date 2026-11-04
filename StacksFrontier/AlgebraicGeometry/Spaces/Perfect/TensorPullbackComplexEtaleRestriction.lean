module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Homology.TotalComplexTransport
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# Restricting the complex `𝒢^• ⊗ f^*M` to an étale neighbourhood

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `𝒢^•` a complex of `𝒪_X`-modules and
`j : X' ⟶ X` an étale morphism.  For a complex `M` of `𝒪_Y`-modules write
`𝒢^• ⊗ f^*M = Tot(𝒢^• ⊗_{𝒪_X} f^*M)` for the total complex of the tensor double complex of `𝒢^•`
and the termwise pullback of `M`.  Then, naturally in `M`,

`(𝒢^• ⊗ f^*M)|_{X'} ≅ 𝒢^•|_{X'} ⊗ (j ≫ f)^*M`.

This is the restriction of the coefficient complexes `𝒢^• ⊗ f^*ℱ` of Stacks 0A1M, 08JN and 08JR to
the quasi-compact neighbourhood of the support of `𝒢^•` in the proof of Stacks 08JR.  The
comparison is restriction along `j` (which is the pullback of modules along the morphism of small
étale ringed topoi of `j`, Stacks 03LW), the commutation of pullback with total tensor complexes
(Stacks 03EL in each bidegree, `Stacks.Sheaves.DerivedPullback.pullbackTensorBicomplexIso`), and
the composition of pullbacks (Stacks 03D6).

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictTensorPullbackComplexIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] etaleModulePullback_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : AlgebraicSpaces B S hS}

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtale

/-- Restriction of modules along an étale morphism is the pullback of modules along the morphism
of small étale ringed topoi (Stacks 03LW). -/
def etaleModulePullbackIsoPullbackModules (j : X' ⟶ X) (hj : IsEtale B S hS j.hom) :
    etaleModulePullback.{u, u} B S hS j hj ≅
      RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS j).toModulesHom :=
  (modulePullbackIsoEtaleModulePullback B S hS j hj).symm ≪≫
    (pullbackModulesIsoModulePullback B S hS j).symm

/-- The isomorphism of total complexes induced by isomorphisms of the two factors. -/
def mapBifunctorMapIsoOfIso {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ C ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X : C, (F.obj X).PreservesZeroMorphisms] {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor L₁ L₂ F (ComplexShape.up ℤ)]
    (e₁ : K₁ ≅ L₁) (e₂ : K₂ ≅ L₂) :
    HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor L₁ L₂ F (ComplexShape.up ℤ) where
  hom := HomologicalComplex.mapBifunctorMap e₁.hom e₂.hom F (ComplexShape.up ℤ)
  inv := HomologicalComplex.mapBifunctorMap e₁.inv e₂.inv F (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [HomologicalComplex.mapBifunctorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id,
      HomologicalComplex.mapBifunctorMap_id]
  inv_hom_id := by
    rw [HomologicalComplex.mapBifunctorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id,
      HomologicalComplex.mapBifunctorMap_id]

/-- **Stacks 03EL in each bidegree, for the restriction along an étale `j : X' ⟶ X`**: the
pullback of the total tensor complex of `K` and `L` is the total tensor complex of the pullbacks,
naturally in both complexes; here in the spelling of the small étale ringed site. -/
def pullbackTensorTotalIsoSmallEtale (j : X' ⟶ X)
    (K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    ((RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS j).toModulesHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS X.1 X.2).O).obj
          K).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          (((RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS X)
              (smallEtaleRingedToposHom B S hS j).toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)).obj
        (((RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS X)
              (smallEtaleRingedToposHom B S hS j).toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L) :=
  Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso
    (smallEtaleRingedToposHom B S hS j).toModulesHom K L

/-- **The restriction of `𝒢^• ⊗ f^*M` to an étale `j : X' ⟶ X` is `𝒢^•|_{X'} ⊗ (j ≫ f)^*M`.** -/
def etaleRestrictTensorPullbackComplexIso (j : X' ⟶ X) (hj : IsEtale B S hS j.hom) (f : X ⟶ Y)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (M : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS X.1 X.2).O).obj
          G).obj ((RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS Y)
              (smallEtaleRingedToposHom B S hS f).toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj M)) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          (((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G)).obj
        ((RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS Y)
              (smallEtaleRingedToposHom B S hS (j ≫ f)).toModulesHom).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj M) := by
  haveI := pullbackModules_smallEtaleRingedToposHom_additive B S hS j
  haveI := pullbackModules_smallEtaleRingedToposHom_additive B S hS f
  haveI := pullbackModules_smallEtaleRingedToposHom_additive B S hS (j ≫ f)
  haveI := Functor.preservesZeroMorphisms_of_iso (etaleModulePullbackIsoPullbackModules B S hS j hj)
  exact
  (NatIso.mapHomologicalComplex (etaleModulePullbackIsoPullbackModules B S hS j hj)
      (ComplexShape.up ℤ)).app _ ≪≫
    pullbackTensorTotalIsoSmallEtale B S hS j G _ ≪≫
    mapBifunctorMapIsoOfIso (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X'.1 X'.2).O)
      ((NatIso.mapHomologicalComplex (etaleModulePullbackIsoPullbackModules B S hS j hj)
        (ComplexShape.up ℤ)).app G).symm
      ((Functor.mapHomologicalComplexCompIso
        ((AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (smallEtaleRingedToposHom B S hS j) (smallEtaleRingedToposHom B S hS f)).symm ≪≫
            pullbackModulesCompTransport B S hS j f) (ComplexShape.up ℤ)).app M)

end AlgebraicGeometry.Space

end
