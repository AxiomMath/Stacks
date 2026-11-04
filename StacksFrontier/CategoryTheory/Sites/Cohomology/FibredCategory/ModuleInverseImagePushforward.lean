module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The module inverse image of Situation 08PA as a pushforward

In Situation 08PA (Stacks 08PA) the structure map `g♯` of the morphism of ringed topoi `g` is
invertible, so the second factor of `g^* = O_C ⊗_{g^{-1}O_D} g^{-1}(-)` — extension of scalars
along `g♯` — is restriction of scalars along its inverse, and the first factor is restriction
along `u` up to restriction of scalars along `restrictionRingIso`. The two restrictions of
scalars collapse into one, and restriction along `u` followed by one restriction of scalars is
`SheafOfModules.pushforward`. So `g^*` is a pushforward of sheaves of modules along `u`, and the
inverse image of a sheaf of modules has the inverse image of its underlying abelian sheaf as
underlying abelian sheaf.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.moduleInverseImageIsoPushforward`: `g^*` is a
  pushforward of sheaves of modules along `u`.
* `Stacks.Sites.FibredCategory.MorphismSituation.inverseImageForgetIso`: `g^*` commutes with
  forgetting the module structure.

## References

* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

section LowerShriek

variable [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-! ### `g^*` as a pushforward of sheaves of modules along `u` -/

/-- `u` is continuous for the topologies of the source and target ringed topoi, with the
`Category` instances of the ringed topoi. -/
instance uContinuousTopos :
    @Functor.IsContinuous (S.sourceTopos S.pi').C
      (AlgebraicGeometry.RingedTopos.category (S.sourceTopos S.pi'))
      (S.totalTopos S.pi).C (AlgebraicGeometry.RingedTopos.category (S.totalTopos S.pi))
      S.u (S.sourceTopos S.pi').J (S.totalTopos S.pi).J :=
  S.uContinuous

/-- `u` is continuous for the topologies of the source and target ringed topoi, with the
`Category` instances of the situation on `S.source` and `S.total`. -/
instance uContinuousToposTopologies :
    S.u.IsContinuous (S.sourceTopos S.pi').J (S.totalTopos S.pi).J :=
  S.uContinuous

/-- Abelian sheaves can be sheafified on the target ringed topos. -/
instance hasWeakSheafifyTotalTopos
    (π : _root_.MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    HasWeakSheafify (S.totalTopos π).J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs
    (HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- On the target ringed topos the weak equivalences of abelian sheaves are the locally bijective
morphisms. -/
instance wEqualsLocallyBijectiveTotalTopos
    (π : _root_.MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.totalTopos π).J.WEqualsLocallyBijective
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  inferInstanceAs (S.totalTopology.WEqualsLocallyBijective
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- **`g_!^{Ab}` exists, read at the topologies of the two ringed topoi.** `g^{-1}` on abelian
sheaves, with the source and target sites and their `Category` instances taken from `sourceTopos`
and `totalTopos`, admits a left adjoint. -/
instance abelianInverseImageTopos_isRightAdjoint :
    (@Functor.sheafPushforwardContinuous
      (S.sourceTopos S.pi').C (AlgebraicGeometry.RingedTopos.category (S.sourceTopos S.pi'))
      (S.totalTopos S.pi).C (AlgebraicGeometry.RingedTopos.category (S.totalTopos S.pi))
      S.u AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} _
      (S.sourceTopos S.pi').J (S.totalTopos S.pi).J S.uContinuousTopos).IsRightAdjoint :=
  inferInstanceAs S.abelianInverseImage.IsRightAdjoint

/-- The comparison of `g⁻¹O_C` with the restriction of `O_C` along `u`, at the level of sheaves of
rings: `Stacks.Sheaves.ToposPullback.restrictionRingIso` at the situation's data. -/
abbrev restrictionRingIsoU :=
  Stacks.Sheaves.ToposPullback.restrictionRingIso (S.sourceTopos S.pi').J (S.totalTopos S.pi).J
    S.u (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)

/-- The morphism of sheaves of rings `O_{C'} ⟶ u_* O_C` along which `g^*` is a pushforward of
sheaves of modules: the inverse of the structure map `g♯ : g⁻¹O_C ⟶ O_{C'}` — invertible by
Stacks 08PA — followed by the comparison of `g⁻¹O_C` with the restriction of `O_C` along `u`. -/
abbrev moduleStructureMap :=
  (asIso S.gRinged.fSharpInverseImageRing).inv ≫ S.restrictionRingIsoU.hom

omit [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}] in
/-- Restriction of scalars along the comparison `restrictionRingIso`, followed by restriction of
scalars along the inverse of `g♯`, is restriction of scalars along `moduleStructureMap`. -/
theorem restrictScalars_comp_moduleStructureMap :
    SheafOfModules.restrictScalars.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.restrictionRingIsoU.hom ⋙
        SheafOfModules.restrictScalars.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          (asIso S.gRinged.fSharpInverseImageRing).inv =
      SheafOfModules.restrictScalars.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.moduleStructureMap :=
  Stacks.Sheaves.RingedToposModules.restrictScalars_comp _ _

/-- Restriction of scalars along the comparison `restrictionRingIso` followed by extension of
scalars along the invertible `g♯` is isomorphic to restriction of scalars along
`moduleStructureMap`. -/
def moduleRestrictScalarsCompExtendScalarsIso :
    SheafOfModules.restrictScalars S.restrictionRingIsoU.hom ⋙
        Stacks.Sheaves.RingedToposModules.extendScalarsFSharp S.gRinged.toModulesHom ≅
      SheafOfModules.restrictScalars S.moduleStructureMap :=
  Functor.isoWhiskerLeft _
      S.gRinged.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫
    eqToIso S.restrictScalars_comp_moduleStructureMap

/-- **`g^*` is the pushforward of sheaves of modules along `u` and `moduleStructureMap`.** The
inverse image of Stacks 03D2 is restriction along the continuous functor `u` up to restriction of
scalars along `restrictionRingIso`, and extension of scalars along the invertible `g♯` of
Stacks 08PA is restriction of scalars along its inverse; the two restrictions of scalars collapse,
and restriction along `u` followed by one restriction of scalars is
`SheafOfModules.pushforward`. -/
def moduleInverseImageIsoPushforward :
    S.moduleInverseImage ≅ SheafOfModules.pushforward S.moduleStructureMap :=
  Functor.isoWhiskerRight
      (Stacks.Sheaves.ToposPullback.restrictionModuleIso (S.sourceTopos S.pi').J
        (S.totalTopos S.pi).J S.u
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O))
      (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp S.gRinged.toModulesHom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ S.moduleRestrictScalarsCompExtendScalarsIso ≪≫
    eqToIso (Stacks.Sheaves.ToposPullback.restrictionModules_comp_restrictScalars
      (S.sourceTopos S.pi').J (S.totalTopos S.pi).J S.u
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)
      S.moduleStructureMap)

/-- **The module pushforward along `u` and `moduleStructureMap` admits a left adjoint.** -/
instance modulePushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.moduleStructureMap).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso S.moduleInverseImageIsoPushforward

/-- **`forget ∘ g^* = g^{-1} ∘ forget`.** The underlying abelian sheaf of the inverse image of a
sheaf of modules along `g` is the inverse image `g^{-1}` of its underlying abelian sheaf, i.e. its
restriction along `u`. -/
def inverseImageForgetIso :
    S.moduleInverseImage ⋙
        SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O) ≅
      SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O) ⋙
        S.abelianInverseImage :=
  Functor.isoWhiskerRight S.moduleInverseImageIsoPushforward _ ≪≫
    eqToIso (Stacks.SheafOfModules.pushforward_comp_toSheaf S.u S.moduleStructureMap)

end LowerShriek

end Stacks.Sites.FibredCategory.MorphismSituation

end
