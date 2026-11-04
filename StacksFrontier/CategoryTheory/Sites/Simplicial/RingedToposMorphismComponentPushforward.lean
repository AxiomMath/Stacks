module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.UnboundedBaseChangeForACocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismDerivedPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to a component computes the degreewise derived direct image

Let `h` be a morphism between simplicial sites in the cocontinuous case and `n` a simplicial
degree. This file supplies the abelian half of the source's proof of Stacks 0DH1: for a
K-injective complex `I` of modules on the total site, the restriction to the component of degree
`n` of the underlying abelian complex of `I` computes the degreewise derived direct image of
abelian sheaves `Rh_{n,*}`. It also records how the pullback of modules to a component and the
degreewise direct image of modules look on underlying abelian sheaves.

## Main definitions

* `CategoryTheory.Functor.sheafPushforwardCocontinuousForgetIso`: the direct image of abelian
  sheaves along a cocontinuous functor of sites lies over the direct image of sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackModulesToSheafIso`: the underlying
  abelian sheaf of `g_n^*M` is the restriction of the underlying abelian sheaf of `M`.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentPushforwardModulesToSheafIso`:
  the underlying abelian sheaf of `h_{n,*}M` is the direct image of the underlying abelian sheaf.

## Main results

* `CocontinuousSimplicialSite.Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent`:
  the restriction to a component of the underlying abelian complex of a K-injective complex of
  modules computes the degreewise derived direct image of abelian sheaves.

## Implementation notes

The last statement is the argument of Stacks 0D97, run on a complex that computes the derived
direct image along the total morphism without being K-injective: Stacks 0D6J for the cocontinuous
total functor
(`Stacks.Cohomology.CocontinuousForgetModule.quasiIso_cocontinuousPushforward_map_of_isKInjective`)
says that the direct image of a K-injective resolution `I_ab ⟶ J` is a quasi-isomorphism;
restriction to the component is exact, so carries it to a quasi-isomorphism, which is the
degreewise direct image of the restricted resolution by Stacks 0D96 on abelian sheaves; and the
restriction of `J` is K-injective by Stacks 09WH.

The two comparisons of underlying abelian sheaves are obtained from comparisons of underlying
sheaves of sets by `Stacks.Cohomology.abelianSheafNatIsoOfUnderlying`, additivity of the
components being automatic for additive functors.

## References

* [Stacks Project, Tag 0DH1](https://stacks.math.columbia.edu/tag/0DH1)
* [Stacks Project, Tag 0D97](https://stacks.math.columbia.edu/tag/0D97)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory

section Forget

variable {X Y : Type u} [SmallCategory X] [SmallCategory Y] (J : GrothendieckTopology X)
  (K : GrothendieckTopology Y) (w : X ⥤ Y) [w.IsCocontinuous J K]

/-- The direct image of abelian sheaves along a cocontinuous functor of sites, followed by
forgetting the group structure, is the direct image of the underlying sheaves of sets: forgetting
the group structure preserves the limits computing the right Kan extension. -/
def Functor.sheafPushforwardCocontinuousForgetIso :
    w.sheafPushforwardCocontinuous Ab.{u} J K ⋙ sheafCompose K (forget Ab.{u}) ≅
      sheafCompose J (forget Ab.{u}) ⋙ w.sheafPushforwardCocontinuous (Type u) J K :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K (Type u))
    (F := w.sheafPushforwardCocontinuous Ab.{u} J K ⋙ sheafCompose K (forget Ab.{u}))
    (G := sheafCompose J (forget Ab.{u}) ⋙ w.sheafPushforwardCocontinuous (Type u) J K)
    (Functor.isoWhiskerLeft (sheafToPresheaf J Ab.{u})
      ((forget Ab.{u}).ranCompIsoOfPreserves w.op))

end Forget

namespace SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **The underlying abelian sheaf of the pullback of a sheaf of modules to a simplicial
component is the restriction of the underlying abelian sheaf**, naturally in the module. On
underlying sheaves of sets this is `componentPullbackUnderlyingIso` followed by the identification
of the inverse image to a component with restriction (Stacks 00XR); additivity is automatic. -/
def componentPullbackModulesToSheafIso :
    (componentRingedToposHom S O n).toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (componentRingedTopos S O n).J)) (componentRingedTopos S O n).O) ≅
      SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (totalRingedTopos S O).J)) (totalRingedTopos S O).O) ⋙ abelianComponent S n :=
  haveI : HasBinaryBiproducts (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (totalRingedTopos S O).J))
        (totalRingedTopos S O).O)) := HasBinaryBiproducts.of_hasBinaryProducts
  @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ (S.componentTopology n)
    ((componentRingedToposHom S O n).toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (componentRingedTopos S O n).J)) (componentRingedTopos S O n).O))
    (SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (totalRingedTopos S O).J)) (totalRingedTopos S O).O) ⋙ abelianComponent S n)
    (inferInstanceAs ((componentRingedToposHom S O n).toModulesHom.pullbackModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (componentRingedTopos S O n).J)) (componentRingedTopos S O n).O)).Additive)
    ⟨fun {_ _ f g} => ((abelianComponent S n).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((abelianComponent S n).map_add)⟩
    (componentPullbackUnderlyingIso S O n ≪≫
      Functor.isoWhiskerLeft (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (totalRingedTopos S O).J))
            (totalRingedTopos S O).O))
        (componentRingedTopos_setRestrictionIso S n))

end SimplicialSiteSituation

namespace CocontinuousSimplicialSite.RingedMorphism

variable {C C' : CocontinuousSimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}
  (h : RingedMorphism C C'
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology)) O)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
  (n : SimplexCategory)

attribute [local instance] Morphism.additive_abelianComponentPushforward

/-- **The underlying abelian sheaf of the degreewise direct image of a sheaf of modules is the
direct image of the underlying abelian sheaf**, naturally in the module. On underlying sheaves
of sets both are the direct image of the underlying sheaf of sets, the right Kan extension
commuting with forgetting the group structure; additivity is automatic. -/
@[sga "4 IV 13.2.3" "special case"]
def componentPushforwardModulesToSheafIso :
    (h.componentRingedToposHom n).pushforwardModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C'.situation.componentRingedTopos O' n).J))
          (C'.situation.componentRingedTopos O' n).O) ≅
      SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O) ⋙ h.hom.abelianComponentPushforward n :=
  haveI : HasBinaryBiproducts (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
        (C.situation.componentRingedTopos O n).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  letI : (h.hom.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
    h.hom.isCocontinuous (Opposite.op n)
  haveI := h.hom.additive_abelianComponentPushforward n
  @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _
    ((h.componentRingedToposHom n).pushforwardModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C'.situation.componentRingedTopos O' n).J))
          (C'.situation.componentRingedTopos O' n).O))
    (SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O) ⋙ h.hom.abelianComponentPushforward n)
    inferInstance
    ⟨fun {_ _ f g} => ((h.hom.abelianComponentPushforward n).congr_map
      ((SheafOfModules.toSheaf _).map_add (f := f) (g := g))).trans
        ((h.hom.abelianComponentPushforward n).map_add)⟩
    ((h.componentRingedToposHom n).pushforwardModulesUnderlyingIso ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
            (C.situation.componentRingedTopos O n).O))
        ((h.hom.hom.app (Opposite.op n)).toFunctor.sheafPushforwardCocontinuousForgetIso
          (topologyOfCoverings (C.coverage (Opposite.op n)))
          (topologyOfCoverings (C'.coverage (Opposite.op n)))).symm)

end CocontinuousSimplicialSite.RingedMorphism

namespace CocontinuousSimplicialSite.Morphism

open SimplicialSiteSituation Stacks.Cohomology.CocontinuousForgetModule

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforward
  additive_abelianComponentPushforward

variable {C C' : CocontinuousSimplicialSite.{u}} (h : Morphism C C') (n : SimplexCategory)
  (R : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u})

/-- **The restriction to a component of the underlying abelian complex of a K-injective complex
of modules computes the degreewise derived direct image of abelian sheaves.** This is the
argument of Stacks 0D97 run on a complex that is not K-injective but computes the derived direct
image along the total morphism, by Stacks 0D6J: if `I_ab ⟶ J` is a K-injective resolution, its
restriction to the component is one as well (Stacks 09WH), and the degreewise direct image of
that restriction is the restriction of the direct image along the total morphism (Stacks 0D96),
which is a quasi-isomorphism by Stacks 0D6J for the cocontinuous total functor. -/
theorem isIso_derivedAbelianPushforwardUnit_app_abelianComponent
    (I : CochainComplex (SheafOfModules.{u} R) ℤ) [I.IsKInjective] :
    letI : (h.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
      h.isCocontinuous (Opposite.op n)
    IsIso ((derivedAbelianPushforwardUnit (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C'.coverage (Opposite.op n)))
        (h.hom.app (Opposite.op n)).toFunctor).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  let : (h.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
    h.isCocontinuous (Opposite.op n)
  let : h.totalFunctor.IsCocontinuous (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology := h.totalFunctor_isCocontinuous
  set Iab := ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  set qI := (Stacks.Injectives.kInjectiveResolutionInclusion
    (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})).app Iab
  have := Functor.preservesHomologyOfExact
    (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)
  have := Functor.preservesHomologyOfExact
    (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n)
  have hNK : CochainComplex.IsKInjective
      (((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((Stacks.Injectives.kInjectiveResolutionFunctor
          (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})).obj Iab)) :=
    isKInjective_componentRestriction C n _
  have hTq : QuasiIso ((h.abelianTotalPushforward.mapHomologicalComplex
      (ComplexShape.up ℤ)).map qI) :=
    @quasiIso_cocontinuousPushforward_map_of_isKInjective _ _ _ _
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology h.totalFunctor
      h.totalFunctor_isCocontinuous _ _ _ R I _ _ _ qI _
  have hrTq : QuasiIso (((abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((h.abelianTotalPushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map qI)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hvq : QuasiIso (((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
      h.abelianComponentPushforward n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) := by
    rw [← NatIso.naturality_1 (Functor.mapHomologicalComplexCompIso
      (h.abelianTotalPushforwardRestrictIso n) (ComplexShape.up ℤ)) qI]
    have : QuasiIso ((h.abelianTotalPushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u})
          n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) := hrTq
    infer_instance
  have hrq : QuasiIso (((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology qI _
  exact @Stacks.Cohomology.ForgetModule.rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise
    _ _ _ _ _ _ _ _ _
    ((h.hom.app (Opposite.op n)).toFunctor.sheafPushforwardCocontinuous Ab.{u}
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n)))) _ _ _ _ _ _
    (((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) hrq hNK hvq

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end
