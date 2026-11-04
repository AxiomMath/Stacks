module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetNormalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.LocalizedStructureSheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleInverseImagePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleLowerShriekForget
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek of modules commutes with forgetting the module structure in Situation 08PA

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `g : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)` be the induced
morphism of ringed topoi. **Stacks 08PC part (2)** is that the square

```
Mod(O_{C'}) --g_!--> Mod(O_C)
    |                   |
 forget              forget
    v                   v
 Ab(C')  --g_!^{Ab}--> Ab(C)
```

commutes. This file proves it.

By Stacks 0798
(`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison`)
it suffices that for every object `U'` of `C'`, with `U = u(U')` and `g' : Sh(C'/U') ⟶ Sh(C/U)`
the localized morphism, the canonical map

`κ_{U'} : (g')^{Ab}_! O_{U'} ⟶ O_U`

is an isomorphism; this is the form of the criterion for the structure sheaf `u⁻¹O_C`. The source
proves it by a chain of identifications of `Hom(-, E)`, using Stacks 08PB. Here the same chain
is organised as a Yoneda argument. `κ_{U'}` is the Stacks 0798 comparison of `g'` at `O_{U'}`
followed by `g'_! O_{U'} ⟶ O_U`, and its adjoint transpose is the identification
`O_{U'} ≅ g'^{-1} O_U`; so by
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_comp_of_bijective` it is an
isomorphism as soon as `g'^{-1}` is bijective on morphisms of abelian sheaves out of `O_U`. That
is where Stacks 08PB enters: `O_U` is the inverse image `π_U^{-1} O_V` from the base slice
`D/V`, `V = p(U)`, and
`MorphismSituation.homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit` says
that `g'^{-1}` acts on morphisms out of `π_U^{-1} Z` as the adjunction bijection of
`g'_! ⊣ g'^{-1}`, up to the isomorphism `g'_! (π'_{U'})^{-1} Z ≅ π_U^{-1} Z` of Stacks 08PB.

The criterion is for the structure map `𝟙 : u⁻¹O_C ⟶ u⁻¹O_C`, whereas in Situation 08PA the
structure sheaf of `C'` is `(π')^{-1} O_D` and `g^*` is a pushforward along the isomorphism
`MorphismSituation.moduleStructureMap : O_{C'} ⟶ u⁻¹O_C` built from `g♯`. The two lower shrieks
differ by restriction of scalars along that isomorphism, which does not change underlying
abelian sheaves (`Stacks.SheafOfModules.lowerShriekForgetIsoOfRestrictScalars`).

## Main results

* `MorphismSituation.moduleDiagramInverseImage_isRightAdjointUnconditional` and
  `MorphismSituation.abelianInverseImage_isRightAdjointUnconditional`, in the namespace
  `Stacks.Sites.FibredCategory`: **Stacks 08PC part (1)**, the left adjoints `g_!` and
  `g_!^{Ab}`, with the sheafification hypotheses of the earlier statements discharged.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_localizedStructureSheafComparison`: the
  canonical map `(g')^{Ab}_! O_{U'} ⟶ O_{u(U')}` is an isomorphism for every object `U'`.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_lowerShriekForgetComparison_structureMap`:
  the Stacks 0798 comparison is an isomorphism for the structure sheaf `u⁻¹O_C`.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_moduleLowerShriekForgetComparison`:
  **Stacks 08PC part (2)**, the canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` is an
  isomorphism.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekForgetIso`: the same as
  an isomorphism of functors, `forget ∘ g_! ≅ g_!^{Ab} ∘ forget`.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- Abelian presheaves on a slice of the target fibred category can be sheafified: at the
situation's universe of sections the slice site is essentially small. -/
theorem hasWeakSheafify_totalTopology_over (U : S.total) :
    HasWeakSheafify (S.totalTopology.over U) AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  have := Stacks.SheafOfModules.siteHasSheafify.{max u₁ v₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂}
    (S.totalTopology.over U)
  inferInstance

attribute [local instance] hasWeakSheafify_totalTopology_over isContinuous_overPost_u
  Stacks.SheafOfModules.siteHasSheafify Stacks.SheafOfModules.siteWEqualsLocallyBijective

/-- Abelian presheaves on the source fibred category can be sheafified: at the situation's
universe of sections the inherited site is essentially small. -/
theorem hasWeakSheafify_sourceTopology :
    HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  have := Stacks.SheafOfModules.siteHasSheafify.{u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.sourceTopology
  inferInstance

/-- Abelian presheaves on the target fibred category can be sheafified. -/
theorem hasWeakSheafify_totalTopology :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  have := Stacks.SheafOfModules.siteHasSheafify.{u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.totalTopology
  inferInstance

/-- On the source fibred category, sheafification of abelian presheaves inverts exactly the
locally bijective morphisms. -/
theorem wEqualsLocallyBijective_sourceTopology :
    S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  Stacks.SheafOfModules.siteWEqualsLocallyBijective.{u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} _

/-- On the target fibred category, sheafification of abelian presheaves inverts exactly the
locally bijective morphisms. -/
theorem wEqualsLocallyBijective_totalTopology :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  Stacks.SheafOfModules.siteWEqualsLocallyBijective.{u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} _

attribute [local instance] hasWeakSheafify_sourceTopology hasWeakSheafify_totalTopology
  wEqualsLocallyBijective_sourceTopology wEqualsLocallyBijective_totalTopology

/-- **Stacks 08PC, part (1), for sheaves of modules, with no sheafification hypothesis.** The
inverse image `g^*` of sheaves of modules along the `g` of any commutative triangle of ringed
topoi over Situation 08PA has a left adjoint `g_!`. This is
`MorphismSituation.moduleDiagramInverseImage_isRightAdjoint` with its sheafification hypotheses
discharged: at the situation's universe of sections both inherited sites are essentially
small. -/
@[stacks 08PC "part (1), modules: `g^*` has a left adjoint `g_!`"]
theorem moduleDiagramInverseImage_isRightAdjointUnconditional (D : S.RingedToposDiagram) :
    (D.gRinged.toModulesHom.pullbackModules).IsRightAdjoint :=
  S.moduleDiagramInverseImage_isRightAdjoint D

/-- **Stacks 08PC, part (1), for abelian sheaves, with no sheafification hypothesis.** The
inverse image `g^{-1}` of abelian sheaves has a left adjoint `g_!^{Ab}`. This is
`MorphismSituation.abelianInverseImage_isRightAdjoint` with its sheafification hypothesis
discharged. -/
@[stacks 08PC "part (1), abelian sheaves: `g^{-1}` has a left adjoint `g_!^{Ab}`"]
theorem abelianInverseImage_isRightAdjointUnconditional :
    S.abelianInverseImage.IsRightAdjoint :=
  S.abelianInverseImage_isRightAdjoint

/-- **Stacks 08PB, read on morphisms.** Restriction along the localized 1-morphism
`Over.post u : C'/U' ⥤ C/u(U')` is bijective on morphisms of abelian sheaves out of an inverse
image `π_{u(U')}^{-1} Z` from the base slice. Up to the isomorphism
`g'_! (π'_{U'})^{-1} Z ≅ π_{u(U')}^{-1} Z` of `localizedLowerShriekSourceProjectionIso` and the
factorisation of the localized source projection, it is the adjunction bijection of
`g'_! ⊣ g'^{-1}`; that is
`homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit`. -/
theorem bijective_overPost_map_of_projection (U' : S.source)
    (Z : Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (Y : Sheaf (S.totalTopology.over (S.u.obj U')) AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    Function.Bijective (fun g : ((Over.post S.p :
        Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.totalTopology.over (S.u.obj U'))
          (S.base.J.over (S.p.obj (S.u.obj U')))).obj Z ⟶ Y =>
      ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).map g) :=
  Adjunction.map_bijective_of_homEquiv_comp
    ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafAdjunctionContinuous
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')))
    ((localizedLowerShriekSourceProjectionIso S U'
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}).hom.app Z)
    ((Functor.sheafPushforwardContinuousComp' (sourceSliceProjectionComp S U').symm
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
      (S.base.J.over (S.p.obj (S.u.obj U')))).inv.app Z)
    (fun g => homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit S U'
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} Z g) Y

/-- The abelian sheaf underlying the structure sheaf of the slice `C/u(U')` is the inverse image
along the localized target projection of the abelian sheaf underlying the structure sheaf of the
base slice `D/p(u(U'))`: the structure sheaf of the target is the restriction of `O_D` along `p`
(`MorphismSituation.targetStructureRingSheafRestrictionIso`), and restricting along `p` and then
to the slice is restricting to the base slice and then along `Over.post p`, on the nose. -/
def toSheafUnitOverIso (U' : S.source) :
    (SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
            Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}).over (S.u.obj U'))).obj
        (SheafOfModules.unit _) ≅
      ((Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous
          AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.totalTopology.over (S.u.obj U'))
          (S.base.J.over (S.p.obj (S.u.obj U')))).obj
        ((sheafCompose (S.base.J.over (S.p.obj (S.u.obj U')))
            (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj
          ((S.base.J.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              (S.p.obj (S.u.obj U'))).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf S.baseTopos.O))) :=
  (sheafCompose (S.totalTopology.over (S.u.obj U'))
      (forget₂ RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).mapIso
    ((S.totalTopology.overPullback RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        (S.u.obj U')).mapIso S.targetStructureRingSheafRestrictionIso)

/-- Restriction along the localized 1-morphism is bijective on morphisms of abelian sheaves out of
the structure sheaf of `C/u(U')`: by `toSheafUnitOverIso` that sheaf is an inverse image from the
base slice, where `bijective_overPost_map_of_projection` applies. -/
theorem bijective_overPost_map_unit (U' : S.source)
    (Y : Sheaf (S.totalTopology.over (S.u.obj U')) AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    Function.Bijective (fun g : (SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
            Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}).over (S.u.obj U'))).obj
          (SheafOfModules.unit _) ⟶ Y =>
      ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).map g) :=
  Functor.map_bijective_of_iso _ (S.toSheafUnitOverIso U')
    (S.bijective_overPost_map_of_projection U' _) Y

/-- **The canonical map `(g')^{Ab}_! O_{U'} ⟶ O_{u(U')}` of Stacks 0798 is an isomorphism** for
every object `U'` of `C'`, for the structure sheaf `u⁻¹O_C` of `C'`.

It is the comparison of the localized morphism `g'` at `O_{U'}` followed by `forget` of
`g'_! O_{U'} ⟶ O_{u(U')}`, whose transpose `O_{U'} ⟶ g'^{-1} O_{u(U')}` is invertible, the
structure map of `g'` being an identity; and `g'^{-1}` is bijective on morphisms out of
`O_{u(U')}` by `bijective_overPost_map_unit`, which is Stacks 08PB. So
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_comp_of_bijective` applies. -/
theorem isIso_localizedStructureSheafComparison (U' : S.source) :
    IsIso (Stacks.SheafOfModules.localizedStructureSheafComparison.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology S.totalTopology S.u
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
        Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) U') := by
  let phi := Stacks.SheafOfModules.structureMap (S.sourceTopology.over U')
    (S.totalTopology.over (S.u.obj U')) (Over.post S.u : Over U' ⥤ Over (S.u.obj U'))
    ((Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
        Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}).over (S.u.obj U'))
  have : IsIso ((SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂} _).map
      ((SheafOfModules.pullbackPushforwardAdjunction.{max w u₀ u₁ u₂ v₀ v₁ v₂} phi).homEquiv
        _ _ (SheafOfModules.pullbackObjUnitToUnit phi))) := by
    rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
    infer_instance
  exact Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_comp_of_bijective
    (Over.post S.u : Over U' ⥤ Over (S.u.obj U')) phi _ _
    (SheafOfModules.pullbackObjUnitToUnit phi) (S.bijective_overPost_map_unit U')

/-- **Stacks 0798 for the structure sheaf `u⁻¹O_C`.** The canonical comparison
`g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` is an isomorphism when the source fibred category is ringed by
the restriction of the target's structure sheaf along `u`: by the criterion
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison`
it suffices that every `(g')^{Ab}_! O_{U'} ⟶ O_{u(U')}` is an isomorphism, which is
`isIso_localizedStructureSheafComparison`. -/
theorem isIso_lowerShriekForgetComparison_structureMap :
    IsIso (Stacks.SheafOfModules.lowerShriekForgetComparison.{max w u₀ u₁ u₂ v₀ v₁ v₂,
        max w u₀ u₁ u₂ v₀ v₁ v₂} S.u
      (Stacks.SheafOfModules.structureMap S.sourceTopology S.totalTopology S.u
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
          Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}))) :=
  Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison.{
      max w u₀ v₀, u₂, u₁, v₂, v₁}
    S.sourceTopology S.totalTopology S.u _ S.isIso_localizedStructureSheafComparison

/-- `g_!` is the lower shriek of `SheafOfModules.pullback` along the structure map
`MorphismSituation.moduleStructureMap`: both are left adjoint to `g^*`, which is the pushforward
along that structure map by `MorphismSituation.moduleInverseImageIsoPushforward`. -/
def moduleLowerShriekIsoPullback :
    S.moduleLowerShriek ≅ SheafOfModules.pullback.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.moduleStructureMap :=
  S.moduleLowerShriekAdjunction.leftAdjointUniq
    ((SheafOfModules.pullbackPushforwardAdjunction.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.moduleStructureMap).ofNatIsoRight S.moduleInverseImageIsoPushforward.symm)

/-- **Stacks 08PC, part (2).** In Situation 08PA the canonical comparison of Stacks 0798

`g_!^{Ab} ∘ forget ⟶ forget ∘ g_!`

(`MorphismSituation.moduleLowerShriekForgetComparison`, the transformation adjoint to the
forgotten unit of `g_! ⊣ g^*`, for the structure sheaf `O_{C'} = (π')^{-1} O_D` of the
situation) is an isomorphism: lower shriek on sheaves of modules commutes with forgetting the
module structure.

The comparison is an isomorphism for the structure sheaf `u⁻¹O_C` of `C'`
(`isIso_lowerShriekForgetComparison_structureMap`, which is where Stacks 08PB enters), and the
structure sheaf of Situation 08PA is isomorphic to it through the structure map
`MorphismSituation.moduleStructureMap`, built from the invertible `g♯`; the comparison along an
isomorphic structure map is the same comparison up to restriction of scalars
(`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_restrictScalars`). -/
@[stacks 08PC "part (2): the canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` is an \
isomorphism"]
theorem isIso_moduleLowerShriekForgetComparison :
    IsIso S.moduleLowerShriekForgetComparison := by
  have h0 := S.isIso_lowerShriekForgetComparison_structureMap
  have hiso : IsIso S.moduleStructureMap :=
    inferInstanceAs (IsIso ((asIso S.gRinged.fSharpInverseImageRing).symm ≪≫
      S.restrictionRingIsoU).hom)
  have h1 : (SheafOfModules.pushforward.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (Stacks.SheafOfModules.structureMap S.sourceTopology S.totalTopology S.u
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O :
          Sheaf S.totalTopology RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}))).IsRightAdjoint :=
    inferInstance
  exact @Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_restrictScalars _ _ _ _ _ _
    S.u _ _ _ _ _ S.moduleStructureMap (@asIso _ _ _ _ S.moduleStructureMap hiso)
    (Category.comp_id _) h1 S.modulePushforward_isRightAdjoint
    (abelianInverseImageTopos_isRightAdjoint.{u₀, u₁, u₂, v₀, v₁, v₂, w} S) h0

/-- The canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798 with `g_!` read as
the chosen left adjoint `MorphismSituation.moduleLowerShriek` of `g^*`: the comparison
`MorphismSituation.moduleLowerShriekForgetComparison`, which is phrased with the lower shriek of
`SheafOfModules.pullback`, followed by `forget` of the identification
`moduleLowerShriekIsoPullback` of the two left adjoints. -/
def moduleLowerShriekForgetTransformation :
    SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O) ⋙
        S.abelianLowerShriek ⟶
      S.moduleLowerShriek ⋙
        SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O) :=
  S.moduleLowerShriekForgetComparison ≫
    Functor.whiskerRight S.moduleLowerShriekIsoPullback.inv _

/-- The canonical comparison for the chosen `g_!` is an isomorphism, by
`isIso_moduleLowerShriekForgetComparison`. -/
instance isIso_moduleLowerShriekForgetTransformation :
    IsIso S.moduleLowerShriekForgetTransformation := by
  have h := S.isIso_moduleLowerShriekForgetComparison
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h
    (Functor.isoWhiskerRight S.moduleLowerShriekIsoPullback.symm _).isIso_hom

/-- `forget ∘ g_! ≅ g_!^{Ab} ∘ forget`, the inverse of the canonical comparison
`moduleLowerShriekForgetTransformation`; Stacks 08PC part (2) as an isomorphism of functors. -/
def moduleLowerShriekForgetIso :
    S.moduleLowerShriek ⋙
        SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O) ≅
      SheafOfModules.toSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O) ⋙
        S.abelianLowerShriek :=
  (asIso S.moduleLowerShriekForgetTransformation).symm

end Stacks.Sites.FibredCategory.MorphismSituation

end
