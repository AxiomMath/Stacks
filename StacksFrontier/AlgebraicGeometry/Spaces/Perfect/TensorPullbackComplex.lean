module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverTensorPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplexNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso

/-!
# The complex `𝒢^• ⊗_{𝒪_X} f^*M` and its restriction to an étale neighbourhood

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢^•` a complex of `𝒪_X`-modules.  For a
complex `M` of `𝒪_Y`-modules, `𝒢^• ⊗ f^*M = Tot(𝒢^• ⊗_{𝒪_X} f^*M)` is the total complex of the
tensor double complex of `𝒢^•` and the termwise pullback of `M`; at `M = ℱ[0]` it is the complex
`𝒢^• ⊗ f^*ℱ` of Stacks 0A1M, 08JN and 08JR.  The tensor product and the pullback are those of the
small étale ringed topos (`Stacks.SheafOfModules.Tensor.sheafTensor` and the pullback of modules
along `AlgebraicGeometry.Space.smallEtaleRingedToposHom`), the spelling at which `Lf^*` and `⊗^L`
of an algebraic space are stated.

For an étale `j : X' ⟶ X` the restriction of `𝒢^• ⊗ f^*M` to `X'` is `𝒢^•|_{X'} ⊗ (j ≫ f)^*M`,
naturally in `M`: Stacks 03EL in each bidegree
(`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso`) and the composition of pullbacks
(Stacks 03D6).

## Main definitions

* `AlgebraicGeometry.Space.tensorPullbackComplex`: `M ↦ 𝒢^• ⊗ f^*M`.
* `AlgebraicGeometry.Space.tensorPullbackComplexPullbackIso`: its restriction along `j`, as an
  isomorphism of functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Y : AlgebraicSpaces B S hS}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over
  hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

/-- Termwise pullback of complexes of modules along a morphism of algebraic spaces, in the
spelling of the morphism of small étale ringed topoi. -/
abbrev pullbackComplexSmallEtale (f : X ⟶ Y) :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom

/-- **The complex `𝒢^• ⊗_{𝒪_X} f^*M`**, the total complex of the tensor double complex of `𝒢^•`
and the termwise pullback of `M`, as a functor of the complex `M` of `𝒪_Y`-modules. -/
def tensorPullbackComplex (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  pullbackComplexSmallEtale f ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G

/-- The functor `M ↦ 𝒢^• ⊗ f^*M` sends `q : M ⟶ M'` to the map of total complexes induced by
the identity of `𝒢^•` and the termwise pullback of `q`. -/
theorem tensorPullbackComplex_map (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    {M M' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (q : M ⟶ M') :
    (tensorPullbackComplex f G).map q = HomologicalComplex.mapBifunctorMap (𝟙 G)
      ((pullbackComplexSmallEtale f).map q)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O) (ComplexShape.up ℤ) := rfl

/-- The functor `M ↦ 𝒢^• ⊗ f^*M` preserves zero morphisms. -/
instance tensorPullbackComplex_preservesZeroMorphisms (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (tensorPullbackComplex f G).PreservesZeroMorphisms where
  map_zero M M' := by
    rw [tensorPullbackComplex_map, Functor.map_zero]
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, Functor.map_zero, zero_comp,
      comp_zero, CategoryTheory.Functor.map_id, NatTrans.id_app]
    exact (comp_zero).symm

/-- The composite of pullbacks `f^* ⋙ j^* ≅ (j ≫ f)^*` (Stacks 03D6). -/
def pullbackModulesCompSmallEtaleIso (j : X' ⟶ X) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS j).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS (j ≫ f)).toModulesHom.pullbackModules :=
  (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
      (smallEtaleRingedToposHom B S hS j) (smallEtaleRingedToposHom B S hS f)).symm ≪≫
    pullbackModulesCompTransport B S hS j f

/-- **The restriction of `𝒢^• ⊗ f^*M` along `j : X' ⟶ X` is `j^*𝒢^• ⊗ (j ≫ f)^*M`, naturally in
`M`.** -/
def tensorPullbackComplexPullbackIso (j : X' ⟶ X) (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    tensorPullbackComplex f G ⋙ pullbackComplexSmallEtale j ≅
      tensorPullbackComplex (j ≫ f) ((pullbackComplexSmallEtale j).obj G) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pullbackComplexSmallEtale f)
      (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalNatIso
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS j).toModulesHom G) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (pullbackModulesCompSmallEtaleIso j f) (ComplexShape.up ℤ))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X').O).map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj ((pullbackComplexSmallEtale j).obj G))

end AlgebraicGeometry.Space

end
