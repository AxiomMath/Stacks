module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback

/-!
# Computing derived pullbacks of modules on algebraic spaces

We compute the derived pullback `Lf^*` of `𝒪`-modules along a morphism of algebraic spaces
(Stacks 06YY, along the morphism of small étale ringed topoi of Stacks 03G8) in two cases, on a
representing complex.

## Main results

* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback`:
  along an étale morphism `f`, `Lf^*` of the class of a complex `K` is the class of its étale
  restriction `f^*K` (Stacks 03LW).
* `nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso`: along the morphism
  `h_{T'} ⟶ h_T` represented by a morphism `g : T' ⟶ T` of the big fppf site, `Lh^*` commutes
  with the associated-module functor `ε^*` of Stacks 03DU (4) on K-flat complexes with flat terms.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For an étale `f : Y ⟶ X` and a complex `K` of `𝒪_X`-modules, `Lf^*` of the class of `K` is the
class of the étale restriction `f^*K`. -/
theorem nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((etaleModulePullback B S hS f hf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨P', hP', t, ht⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P'
  have : IsIso (DerivedCategory.Qh.map t) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) t ht
  let eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
    ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫ asIso (DerivedCategory.Qh.map t) ≪≫
      (DerivedCategory.quotientCompQhIso _).app K
  let F := etaleModulePullback B S hS f hf
  let e₁ := (smallEtaleDerivedModulePullback B S hS f).mapIso eP.symm ≪≫
    derivedPullbackObjIsoOfIsKFlat B S hS f P hP'
  let e₃ : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
      F.mapDerivedCategoryFactors.app K
  have e₂ : Nonempty (DerivedCategory.Q.obj
      (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    ⟨DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => (modulePullbackIsoEtaleModulePullback B S hS f hf).app (P.X i))
      (fun i j _ => ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.naturality
        (P.d i j)).symm))⟩
  have := modulePullback_additive (B := B) (S := S) (hS := hS) f
  have := pullbackModules_smallEtaleRingedToposHom_additive B S hS f
  replace e₂ := (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
    (Functor.preservesZeroMorphisms_of_additive _)
    (Functor.preservesZeroMorphisms_of_additive (modulePullback B S hS f))
    (pullbackModules_eq_modulePullback B S hS f) P
    (fun L => Nonempty (DerivedCategory.Q.obj L ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))).2 e₂
  obtain ⟨e₂⟩ := e₂
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- Let `g : T' ⟶ T` be a morphism of the big fppf site, `h` the morphism of represented algebraic
spaces and `r` the underlying morphism of schemes, and let `K` be a K-flat complex with flat
terms of `𝒪_T`-modules. Then `Lh^*` of the class of `ε^*K` is the class of `ε^*(r^*K)`. -/
theorem nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (K : CochainComplex (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace K)
    (hKf : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace.sheaf) (K.X i)) :
    haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS g)
    Nonempty ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (DerivedCategory.Q.obj (((representedAssociatedModule B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((representedAssociatedModule B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS g)
  have := modulePullback_representedSpaceMap_preservesZeroMorphisms B S hS g
  have := pullbackModules_representedSpaceMap_preservesZeroMorphisms B S hS g
  let εT := representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  let εT' := representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')
  let M := (εT.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hM := isKFlat_representedAssociatedModule B S hS T K ⟨hK, hKf⟩
  let e₁ := derivedPullbackObjIsoOfIsKFlat B S hS (representedSpaceMap B S hS g) M hM
  let e₃ : ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ≅ (((RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).app (K.X i))
      (fun i j _ => ((Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).hom.naturality (K.d i j)).symm)
  have e₂ : Nonempty (DerivedCategory.Q.obj
      (((modulePullback B S hS (representedSpaceMap B S hS g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≅
        DerivedCategory.Q.obj ((εT'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((RingedSpaceModuleAdjunction.modulePullback
            ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) :=
    ⟨DerivedCategory.Q.mapIso (representedAssociatedModulePullbackComplexIso B S hS g K ≪≫
      (εT'.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e₃)⟩
  replace e₂ := (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
    (pullbackModules_representedSpaceMap_preservesZeroMorphisms B S hS g)
    (modulePullback_representedSpaceMap_preservesZeroMorphisms B S hS g)
    (pullbackModules_eq_modulePullback B S hS (representedSpaceMap B S hS g)) M
    (fun L => Nonempty (DerivedCategory.Q.obj L ≅
      DerivedCategory.Q.obj ((εT'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((RingedSpaceModuleAdjunction.modulePullback
            ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))))).2 e₂
  obtain ⟨e₂⟩ := e₂
  exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.Space
