module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphismContinuous
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphismDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphismDerivedPushforward

/-!
# The derived direct image of sheaves of modules along a morphism of ringed simplicial sites,
case (A)

With the notation and hypotheses of Stacks 0DH0 in case (A) of Stacks 09WE — two simplicial
sites whose transitions are morphisms of sites, sheaves of rings `𝒪` and `𝒪'` on their total
sites, a morphism `(h, h♯)` of ringed simplicial sites built from morphisms of sites, the induced
morphisms of ringed topoi `h_{total}` and `h_n`, and the canonical morphisms `g_n` and `g'_n`
from the ringed topoi of the simplicial components of degree `n` — Stacks 0DH1 asserts that for
`K` in the unbounded derived category of `𝒪`-modules,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

Case (B) is treated in parallel in
`StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphismDerivedPushforward`.

## Main definitions

* `CategoryTheory.SimplicialSite.RingedMorphism.componentPushforwardModulesToSheafIso`: the
  underlying abelian sheaf of `h_{n,*}M` is the direct image of the underlying abelian sheaf.
* `CategoryTheory.SimplicialSite.RingedMorphism.derivedTotalPushforwardModules` and
  `.derivedComponentPushforwardModules`: `Rh_{total,*}` and `Rh_{n,*}` on sheaves of modules, with
  the canonical comparisons from the degreewise direct images.

## Main results

* `SimplicialSite.Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent`:
  the restriction to a component of the underlying abelian complex of a K-injective complex of
  modules computes the degreewise derived direct image of abelian sheaves.
* `RingedMorphism.isIso_derivedComponentPushforwardModulesUnit_app_componentPullback`:
  the pullback to a component of a K-injective complex of `𝒪`-modules computes `Rh_{n,*}`.
* `CategoryTheory.SimplicialSite.RingedMorphism.derivedComponentPushforwardModulesIso`:
  **Stacks 0DH1**, case (A), with `.derivedComponentPushforwardModulesIso_fac` pinning the
  isomorphism down.

## Implementation notes

The argument is the source's, as in case (B). The two sides of the identity are exhibited as
right derived functors of one and the same functor on the unbounded homotopy category of
`𝒪`-modules, identified through the canonical comparison of Stacks 0DH0 in case (A),
`CategoryTheory.SimplicialSite.RingedMorphism.componentPushforwardModulesIso`, and the
isomorphism is the induced comparison of right derived functors. That `Rh_{total,*}` followed by
`Lg'^*_n` is a right derived functor is formal, the pullback to a component being exact. For the
other side, `g_n^* I` computes `Rh_{n,*}` for a K-injective complex `I` of `𝒪`-modules: forgetting
the module structure (Stacks 0D6J for the morphism of sites of degree `n`) reduces this to the
underlying abelian complex, which is the restriction `I_ab|_{𝒞_n}`; and that restriction computes
the abelian `Rh_{n,*}` by the argument of Stacks 0D97: a K-injective resolution `I_ab ⟶ J`
restricts to one (Stacks 09WH), and `h_{n,*}` of the restriction is the restriction of
`h_{total,*}(I_ab ⟶ J)` (Stacks 0D96 on abelian sheaves), which is a quasi-isomorphism by
Stacks 0D6J for the morphism of sites between the total sites
(`Stacks.Cohomology.ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective`).

## References

* [Stacks Project, Tag 0DH1](https://stacks.math.columbia.edu/tag/0DH1)
* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
* [Stacks Project, Tag 0D97](https://stacks.math.columbia.edu/tag/0D97)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Pseudofunctor
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.DerivedPushforward.hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy
  SimplicialSiteSituation.componentPullbackModules_preservesFiniteLimits
  SimplicialSiteSituation.componentPullbackModules_preservesFiniteColimits
  SimplicialSiteSituation.hasWeakSheafifyComponent

namespace SimplicialSite.Morphism

open SimplicialSiteSituation Stacks.Cohomology.ForgetModule

attribute [local instance] additive_abelianTotalPushforward additive_abelianComponentPushforward

variable {C C' : SimplicialSite.{u}} (h : Morphism C C') (n : SimplexCategory)
  (R : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology RingCat.{u})

/-- **The restriction to a component of the underlying abelian complex of a K-injective complex
of modules computes the degreewise derived direct image of abelian sheaves**, in case (A). This
is the argument of Stacks 0D97 run on a complex that is not K-injective but computes the derived
direct image along the total morphism, by Stacks 0D6J: if `I_ab ⟶ J` is a K-injective
resolution, its restriction to the component is one as well (Stacks 09WH), and the degreewise
direct image of that restriction is the restriction of the direct image along the total morphism
(Stacks 0D96), which is a quasi-isomorphism by Stacks 0D6J for the morphism of sites between the
total sites. -/
theorem isIso_derivedAbelianPushforwardUnit_app_abelianComponent
    (I : CochainComplex (SheafOfModules.{u} R) ℤ) [I.IsKInjective] :
    letI := (h.isMorphismOfSites n).isContinuous
    IsIso ((derivedAbelianPushforwardUnit (C.coverage n).toGrothendieck
        (C'.coverage n).toGrothendieck (h.hom.app n).toFunctor).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  let := (h.isMorphismOfSites n).isContinuous
  let := h.totalFunctor_isContinuous
  set Iab := ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  set qI := (Stacks.Injectives.kInjectiveResolutionInclusion
    (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})).app Iab
  have := Functor.preservesHomologyOfExact
    (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
  have := Functor.preservesHomologyOfExact
    (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n)
  have hNK : CochainComplex.IsKInjective
      (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((Stacks.Injectives.kInjectiveResolutionFunctor
          (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})).obj Iab)) :=
    SimplicialSiteSituation.isKInjective_componentRestriction
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n _
  have hTq : QuasiIso ((h.abelianTotalPushforward.mapHomologicalComplex
      (ComplexShape.up ℤ)).map qI) :=
    @quasiIso_abelianPushforward_map_of_isKInjective _ _ _ _ C.totalTopology C'.totalTopology
      h.totalFunctor _ R I ‹I.IsKInjective› _
      (inferInstanceAs (((Stacks.Injectives.kInjectiveResolutionFunctor
        (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})).obj
          Iab).IsKInjective)) qI (inferInstanceAs (QuasiIso qI))
  have hrTq : QuasiIso (((abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((h.abelianTotalPushforward.mapHomologicalComplex (ComplexShape.up ℤ)).map qI)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hvq : QuasiIso (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ⋙
      h.abelianComponentPushforward n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) := by
    rw [← NatIso.naturality_1 (Functor.mapHomologicalComplexCompIso
      (h.abelianTotalPushforwardRestrictIso n) (ComplexShape.up ℤ)) qI]
    have : QuasiIso ((h.abelianTotalPushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u})
          n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) := hrTq
    infer_instance
  have hrq : QuasiIso (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology qI _
  exact @rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise
    _ _ _ _ _ _ _ _ _
    (abelianPushforward (C.coverage n).toGrothendieck (C'.coverage n).toGrothendieck
      (h.hom.app n).toFunctor) _ _ _ _ _ _
    (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
      n).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) hrq hNK hvq

end SimplicialSite.Morphism

namespace SimplicialSite.RingedMorphism

open SimplicialSiteSituation Stacks.Cohomology.ForgetModule

variable {C C' : SimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}

attribute [local instance] Morphism.additive_abelianComponentPushforward

/-- **The underlying abelian sheaf of the degreewise direct image of a sheaf of modules is the
direct image of the underlying abelian sheaf**, naturally in the module, in case (A). On
underlying sheaves of sets both are restriction along the functor representing the morphism of
sites of degree `n`; additivity is automatic. -/
def componentPushforwardModulesToSheafIso
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    (h.componentRingedToposHom n).pushforwardModules ⋙
        SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C'.situation.componentRingedTopos O' n).J))
          (C'.situation.componentRingedTopos O' n).O) ≅
      SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O) ⋙ h.hom.abelianComponentPushforward n :=
  haveI : HasBinaryBiproducts (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (C.situation.componentRingedTopos O n).J)) (C.situation.componentRingedTopos O n).O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
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
    ((h.componentRingedToposHom n).pushforwardModulesUnderlyingIso ≪≫ Iso.refl _)

/-! ### The two derived direct images -/

/-- `Rh_{total,*}`: the unbounded derived direct image of sheaves of modules along the morphism
of total ringed topoi of Stacks 0DH0, case (A). -/
abbrev derivedTotalPushforwardModules
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C'.situation.totalRingedTopos O').J))
        (C'.situation.totalRingedTopos O').O)) :=
  derivedPushforward.{u, u, u, u, u, u} h.totalRingedToposHom

/-- The canonical comparison from the degreewise direct image along the total morphism into
`Rh_{total,*}`. -/
abbrev derivedTotalPushforwardModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O')) :
    pushforwardOnHomotopy.{u, u, u, u, u, u} h.totalRingedToposHom ⟶
      DerivedCategory.Qh ⋙ derivedTotalPushforwardModules h :=
  derivedPushforwardUnit _ _ h.totalRingedToposHom

/-- `Rh_{n,*}`: the unbounded derived direct image of sheaves of modules along the morphism of
component ringed topoi of simplicial degree `n` of Stacks 0DH0, case (A). -/
abbrev derivedComponentPushforwardModules
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.componentRingedTopos O n).J))
        (C.situation.componentRingedTopos O n).O)) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C'.situation.componentRingedTopos O' n).J))
        (C'.situation.componentRingedTopos O' n).O)) :=
  derivedPushforward.{u, u, u, u, u, u} (h.componentRingedToposHom n)

/-- The canonical comparison from the degreewise direct image in simplicial degree `n` into
`Rh_{n,*}`. -/
abbrev derivedComponentPushforwardModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (h.componentRingedToposHom n) ⟶
      DerivedCategory.Qh ⋙ derivedComponentPushforwardModules h n :=
  derivedPushforwardUnit _ _ (h.componentRingedToposHom n)

/-! ### The two sides of the source's identity as right derived functors -/

/-- The comparison from the degreewise direct image along the total morphism followed by the
degreewise pullback to the component of degree `n`, into `Rh_{total,*}` followed by `Lg'_n^*`. -/
def derivedTotalPushforwardRestrictModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n) :=
  Functor.whiskerLeft
      (h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ))
      (C'.situation.componentRingedToposHom O' n
        ).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedTotalPushforwardModulesUnit h)
      (C'.situation.derivedComponentPullbackModules O' n)

/-- The comparison from the degreewise pullback to the component of degree `n` followed by the
degreewise direct image of that degree, into `Lg_n^*` followed by `Rh_{n,*}`. -/
def derivedRestrictTotalPushforwardModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.componentRingedToposHom n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n) :=
  Functor.whiskerLeft
      ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedComponentPushforwardModulesUnit h n) ≫
    Functor.whiskerRight
      (C.situation.componentRingedToposHom O n
        ).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.inv
      (derivedComponentPushforwardModules h n)

/-- **Pullback to a component of a K-injective complex of modules computes `Rh_{n,*}`**, in case
(A). This is the source's reduction to abelian sheaves through Stacks 0D6J: forgetting the module
structure is exact and reflects isomorphisms and carries `h_{n,*}` to the degreewise direct image
of abelian sheaves (`componentPushforwardModulesToSheafIso`); the abelian comparison is invertible
at the underlying complex of every K-injective complex of `𝒪_n`-modules, by Stacks 0D6J for the
morphism of sites of degree `n`, and at the underlying complex of `g_n^* I`, which is the
restriction of the underlying complex of `I` (`componentPullbackModulesToSheafIso`) and so
computes the abelian `Rh_{n,*}` by the argument of Stacks 0D97
(`Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent`). -/
theorem isIso_derivedComponentPushforwardModulesUnit_app_componentPullback
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory)
    (I : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.totalRingedTopos O).J))
      (C.situation.totalRingedTopos O).O)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedComponentPushforwardModulesUnit h n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((C.situation.componentRingedToposHom O n
          ).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))) := by
  let := (h.hom.isMorphismOfSites n).isContinuous
  have := hI
  have := Morphism.additive_abelianComponentPushforward h.hom n
  let ι : ((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((C.situation.componentRingedToposHom O n
          ).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((C.situation.abelianComponent n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (SimplicialSiteSituation.componentPullbackModulesToSheafIso C.situation O n).app
        (I.X i))
      (fun i j _ => ((SimplicialSiteSituation.componentPullbackModulesToSheafIso C.situation O
        n).hom.naturality (I.d i j)).symm)
  have h3 := @Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent _ _ h.hom n
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.totalRingedTopos O).J)) (C.situation.totalRingedTopos O).O) I hI
  have hab : IsIso ((derivedAbelianPushforwardUnit (C.coverage n).toGrothendieck
      (C'.coverage n).toGrothendieck (h.hom.hom.app n).toFunctor).app
        (((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((C.situation.componentRingedToposHom O n
              ).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)))) :=
    (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ι)).mpr h3
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (h.componentRingedToposHom n).pushforwardModules
    (abelianPushforward (C.coverage n).toGrothendieck (C'.coverage n).toGrothendieck
      (h.hom.hom.app n).toFunctor)
    (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.componentRingedTopos O n).J))
      (C.situation.componentRingedTopos O n).O))
    (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C'.situation.componentRingedTopos O' n).J))
      (C'.situation.componentRingedTopos O' n).O))
    _ _ ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.componentRingedTopos O n).J)) (C.situation.componentRingedTopos O n).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C'.situation.componentRingedTopos O' n).J))
        (C'.situation.componentRingedTopos O' n).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C'.situation.componentRingedTopos O' n).J))
      (C'.situation.componentRingedTopos O' n).O)).ReflectsIsomorphisms)
    (componentPushforwardModulesToSheafIso h n) (derivedComponentPushforwardModules h n)
    (derivedAbelianPushforward (C.coverage n).toGrothendieck (C'.coverage n).toGrothendieck
      (h.hom.hom.app n).toFunctor)
    (derivedComponentPushforwardModulesUnit h n)
    (derivedAbelianPushforwardUnit (C.coverage n).toGrothendieck (C'.coverage n).toGrothendieck
      (h.hom.hom.app n).toFunctor) _
    (fun I' hI' =>
      @abelianPushforwardUnit_isIso_at_underlying_kInjective _ _ _ _
        (C.coverage n).toGrothendieck (C'.coverage n).toGrothendieck
        (h.hom.hom.app n).toFunctor _
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O) I' hI')
    _ hab

/-- `Rh_{total,*}` followed by `Lg'_n^*` is a right derived functor of the degreewise direct
image along the total morphism followed by the degreewise pullback to the component of degree
`n`: the comparison for the direct image is invertible on a K-injective complex, and the one for
the pullback is invertible everywhere because the pullback is exact. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    (derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n).IsRightDerivedFunctor
      (derivedTotalPushforwardRestrictModulesUnit h n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have := isIso_derivedPushforwardUnit_app_of_isKInjective _ _ h.totalRingedToposHom I hI
  rw [derivedTotalPushforwardRestrictModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- `Lg_n^*` followed by `Rh_{n,*}` is a right derived functor of the degreewise pullback to the
component of degree `n` followed by the degreewise direct image of that degree: the pullback is
exact, and the pullback of a K-injective complex computes `Rh_{n,*}` by
`isIso_derivedComponentPushforwardModulesUnit_app_componentPullback`. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n).IsRightDerivedFunctor
      (derivedRestrictTotalPushforwardModulesUnit h n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ : IsIso ((derivedComponentPushforwardModulesUnit h n).app
      (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C.situation.totalRingedTopos O).J))
            (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ)).obj I))) :=
    isIso_derivedComponentPushforwardModulesUnit_app_componentPullback h n I hI
  rw [derivedRestrictTotalPushforwardModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-! ### Stacks 0DH1, case (A) -/

/-- The module-level identity of Stacks 0DH0, case (A), read on unbounded homotopy categories:
the canonical comparison `componentPushforwardModulesIso` applied degreewise to complexes. -/
def homotopyComponentPushforwardModulesIso
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.componentRingedToposHom n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (componentPushforwardModulesIso h n) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules)) (ComplexShape.up ℤ)).symm

/-- **Stacks 0DH1**, case (A). With notation and hypotheses as in Stacks 0DH0, for simplicial
sites whose transitions are morphisms of sites and a morphism of ringed simplicial sites built
from morphisms of sites: for `K` in the unbounded derived category of sheaves of `𝒪`-modules on
the total site,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

The source's equality is read as a natural isomorphism of functors on the derived category.
Both sides are right derived functors of one and the same functor on the unbounded homotopy
category of `𝒪`-modules, by
`isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit` and
`isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit` of this namespace, the two
being identified by the canonical comparison of Stacks 0DH0, `componentPushforwardModulesIso`.
The isomorphism is the induced comparison of the two right derived functors, pinned down by
`derivedComponentPushforwardModulesIso_fac`. -/
@[stacks 0DH1 "case (A)"]
def derivedComponentPushforwardModulesIso
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n ≅
      C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h n
  Functor.rightDerivedNatIso _ _ (derivedTotalPushforwardRestrictModulesUnit h n)
    (derivedRestrictTotalPushforwardModulesUnit h n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n) DerivedCategory.Qh)

/-- **Stacks 0DH1**, case (A), the isomorphism is the canonical one. Composing the canonical
comparison into the first right derived functor with the isomorphism gives the canonical
underived comparison of Stacks 0DH0, applied degreewise to complexes, followed by the canonical
comparison into the second. -/
theorem derivedComponentPushforwardModulesIso_fac
    (h : SimplicialSite.RingedMorphism C C' (C.totalRingSheaf O) (C'.totalRingSheaf O'))
    (n : SimplexCategory) :
    derivedTotalPushforwardRestrictModulesUnit h n ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedComponentPushforwardModulesIso h n).hom =
      (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n)
            DerivedCategory.Qh).hom ≫
        derivedRestrictTotalPushforwardModulesUnit h n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h n
  Functor.rightDerivedNatTrans_fac _ _ (derivedTotalPushforwardRestrictModulesUnit h n)
    (derivedRestrictTotalPushforwardModulesUnit h n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n)
      DerivedCategory.Qh).hom

end SimplicialSite.RingedMorphism

end CategoryTheory

end
