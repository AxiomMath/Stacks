module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction

/-!
# The comparison of restricted algebras is an isomorphism

In Situation 0849, for a morphism `τ : T' ⟶ T` of test objects and scheme points `f` of `X` at `T`
and `f' = f ∘ τ` at `T'`, the comparison `τ^*(f^*𝒜) ⟶ f'^*𝒜` of
`AlgebraicGeometry.Space.pointComparison` is an isomorphism in every degree as soon as the pieces
of `𝒜` are quasi-coherent.

The comparison is the transpose along `τ^* ⊣ τ_*` of the restriction map, which is the Zariski
reading of the étale restriction map followed by the identification of the Zariski reading of a
direct image.  By `CategoryTheory.Adjunction.isIso_homEquiv_symm_map_comp` such a transpose is an
isomorphism once the transpose of the étale restriction map is — it is the comparison of inverse
images, `AlgebraicGeometry.Space.isIso_homEquiv_symm_gradedPullRestrictionApp` — and the unit and
counit of the adjunction between the Zariski reading and the associated-module functor of
Stacks 03DU are invertible at the quasi-coherent modules involved.

## Main results

* `AlgebraicGeometry.Space.isIso_pointComparison_app`: the comparison is an isomorphism.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

/-- The identification of sections of a direct image over Zariski opens, as a natural
transformation of functors of sheaves of modules. -/
def zariskiDirectImageNatTrans {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    (testToposHom τ).pushforwardModules ⋙
        SheafOfModules.pushforward (selfOpensStructureMap B S hS T) ⟶
      SheafOfModules.pushforward (selfOpensStructureMap B S hS T') ⋙
        Stacks.RingedSpace.pushforwardFunctor
            (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)) where
  app M := zariskiDirectImageModuleHom τ M
  naturality _ _ g := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      directImageSelfOpensSection_map τ O.unop ((Sheaf.moduleSheafFunctor (testRing T')).map g) x))

/-- The identification of sections is a natural isomorphism. -/
instance isIso_zariskiDirectImageNatTrans {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    IsIso (zariskiDirectImageNatTrans τ) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => isIso_zariskiDirectImageModuleHom τ M

/-- The pieces of a pulled-back quasi-coherent algebra are quasi-coherent. -/
theorem isQuasicoherentOnSite_etalePointAlgebra_piece
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite) {T : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    ((etalePointAlgebra A T f).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom f) _ (hA n)

/-- The transpose along `τ^* ⊣ τ_*` of the restriction map is invertible in every degree. -/
theorem isIso_pointRestriction_transpose
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    IsIso (((Stacks.RingedSpace.pullbackAdjunction
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
        ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
      ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n) ≫
        (zariskiDirectImageNatTrans τ).app ((etalePointAlgebra A T' f').piece n))) := by
  have hN := isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n
  have hZ := isQuasicoherent_zariskiReading_piece T _ hN
  have hc := isIso_zariskiReadingAdjunction_counit_app T _ hN
  have hu := isIso_zariskiReadingAdjunction_unit_app T'
    ((Stacks.RingedSpace.pullbackFunctor
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
        ((BigFppfOver.toScheme B S hS).map τ))).obj
      ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
        ((etalePointAlgebra A T f).piece n)))
    (Stacks.Modules.isQuasicoherent_pullback ((BigFppfOver.toScheme B S hS).map τ) _ hZ)
  have hθ := isIso_homEquiv_symm_gradedPullRestrictionApp
    (representedSpaceMap B S hS τ) (pointHom f) (pointHom f') (pointHom_comp τ hf) A n
  exact @CategoryTheory.Adjunction.isIso_homEquiv_symm_map_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (Stacks.RingedSpace.pullbackAdjunction
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
        ((BigFppfOver.toScheme B S hS).map τ)))
    (zariskiReadingAdjunction T) (zariskiReadingAdjunction T')
    (zariskiDirectImageNatTrans τ) (isIso_zariskiDirectImageNatTrans τ) _ _
    (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
        (pointHom_comp τ hf) A n) hc hu hθ

/-- **The comparison of restricted algebras is an isomorphism in every degree.** -/
theorem isIso_pointComparison_app
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
    (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    IsIso ((pointComparison A τ f f' hf).app n) := by
  have h6 : (pointComparison A τ f f' hf).app n = ((Stacks.RingedSpace.pullbackAdjunction
            (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ringedSpaceHom
              ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n) ≫
        (zariskiDirectImageNatTrans τ).app ((etalePointAlgebra A T' f').piece n)) := rfl
  exact (congrArg IsIso h6).mpr (isIso_pointRestriction_transpose A hA τ f f' hf n)


end AlgebraicGeometry.Space
