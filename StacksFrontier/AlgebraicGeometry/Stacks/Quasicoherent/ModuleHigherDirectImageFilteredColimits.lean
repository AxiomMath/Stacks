module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRanNatIso
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHigherDirectImagesQcqs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CocontinuousPushforwardAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.TensorSheafExtComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives

/-!
# Higher direct images of modules along a qcqs morphism commute with filtered colimits

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks.
**Stacks 0GQW** says that the higher direct images `Rᵖf_*` of *abelian* sheaves commute with
filtered colimits; it is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_abelianDirectImage_fppf_of_qcqs`.
The proof of **Stacks 0GQX** applies it to sheaves of modules: "the functors `f_*` and `Rⁱf_*`
commute with direct sums and filtered colimits on all modules by Lemma 0GQW". This file carries
that out, on the fppf sites, at the module universe `u + 1` of the objects of the site and at the
module universe `u` of the schemes.

## Main results

* `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_stackModuleDirectImageSucc_fppf`:
  at module universe `u + 1`, `Rⁿf_*` commutes with filtered colimits of `u + 1`-small shape.
* `AlgebraicGeometry.Stack.preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered`
  and `AlgebraicGeometry.Stack.preservesColimitsOfShape_fppfModulesPushforward_of_isFiltered`: at
  module universe `u`, `Rⁿf_*` and `f_*` commute with filtered colimits of `u`-small shape.
* `AlgebraicGeometry.Stack.preservesColimitsOfShape_discrete_fppfModulesHigherDirectImage` and
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_discrete_fppfModulesPushforward`: they
  commute with direct sums indexed by any `ι : Type u`.

## Proof

At module universe `u + 1` the direct image of modules is the sheafification of the derived
presheaf direct image (`AlgebraicGeometry.Stack.stackModuleDirectImageSuccRightDerivedIso`), as
for abelian sheaves. At an object `y` of `𝒴`, the sections of the direct image of a module `ℳ`
are the sections of the direct image of its underlying abelian sheaf `ℳ_ab`
(`SheafOfModules.directImageOfEqCompToPresheafIso`), and those are `Hom(ℤ_{K_y}^♯, ℳ_ab)` for
the presheaf of sets `K_y = h_y ∘ fᵒᵖ`
(`Stacks.Cohomology.CocontinuousPushforward.pushforwardSectionsCorepresentation`), that is
`Hom(𝒪_{K_y}, ℳ)` for the sheafified extension of scalars `𝒪_{K_y}`
(`Stacks.SheafOfModules.tensorSheafHomIso`). Deriving, the `n`-th derived functor of sections
over `y` on modules is `Extⁿ(𝒪_{K_y}, -) = Extⁿ(ℤ_{K_y}^♯, (-)_ab)`
(`Stacks.Cohomology.TensorSheafComparison.extTensorSheafIso`, the argument of **Stacks 03FD**,
`ℤ_{K_y}` being torsion-free), which is the `n`-th derived functor of sections over `y` of the
abelian direct image, applied to `(-)_ab`. For `y` affine that commutes with filtered colimits
by the local step of **Stacks 0GQW**
(`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_fibreSections_fppf`), and
forgetting the module structure commutes with colimits. Every object of `𝒴` is covered by
objects over affine schemes, so the comparison map of derived presheaf direct images, bijective
over those, becomes an isomorphism after sheafification (**Stacks 0H6Y**).

At module universe `u` the universe lift carries `Rⁿf_*` to `Rⁿf_*` at `u + 1`
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImageULiftIso`), it commutes with colimits and
it is fully faithful. Direct sums are filtered colimits of finite direct sums, which the additive
functors `Rⁿf_*` preserve.

## References

* [Stacks Project, Tag 0GQW](https://stacks.math.columbia.edu/tag/0GQW)
* [Stacks Project, Tag 0GQX](https://stacks.math.columbia.edu/tag/0GQX)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (k : 𝒳 ⟶ 𝒴)

section Succ

variable (τ : SiteKind)

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ

/-- **The underlying presheaf of abelian groups of the direct image of a module, at module
universe `u + 1`, is the right Kan extension of the underlying presheaf of the module** along
the functor underlying the 1-morphism, naturally in the module. -/
def stackModuleDirectImageSuccCompToPresheafIso :
    stackModuleDirectImageSucc B S hS k τ ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.toPresheaf _ ≅
      SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
        (CatFiberedInGroupoids.homFunctor k.hom).op.ran :=
  have hF := (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p k.hom))
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).1
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).2
  SheafOfModules.directImageOfEqCompToPresheafIso.{u, u + 1, u, u, u + 1, u + 1}
    (CatFiberedInGroupoids.homFunctor k.hom) _ _ _
    (Stacks.RelativeCech.ringStructureSheafCore_eq_pushforward B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ)

/-- The sections over an object `y` of `𝒴` of the direct image of a module at module universe
`u + 1`, as an additive functor to abelian groups. -/
abbrev directImageSectionsSucc (y : 𝒴.val.val.obj) :
    SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ) ⥤ AddCommGrpCat.{u + 1} :=
  directImageSectionsFunctor k τ y

/-- **The sections over `y` of the direct image of a module are the sections over `y` of the
direct image of its underlying abelian sheaf.** -/
def directImageSectionsSuccIso (y : 𝒴.val.val.obj) :
    directImageSectionsSucc k τ y ≅
      SheafOfModules.toSheaf _ ⋙ fibreSections.{u, 0} B S hS 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor k.hom) τ y :=
  Functor.isoWhiskerRight (stackModuleDirectImageSuccCompToPresheafIso k τ)
    ((evaluation _ AddCommGrpCat.{u + 1}).obj (op y))

local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "RX" => Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p
  𝒳.val.isFiberedInGroupoids τ
local notation "Fn" => CatFiberedInGroupoids.homFunctor k.hom

/-- The free abelian presheaf `ℤ_{K_y}` on `K_y = h_y ∘ fᵒᵖ`, the presheaf of sets on `𝒳` whose
free abelian sheaf corepresents sections over `y` of the direct image. -/
abbrev directImageSectionsPresheaf (y : 𝒴.val.val.obj) : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Presheaf.freeAbelian.obj
    (Stacks.Cohomology.CocontinuousPushforward.restrictedYoneda.{u + 1, u + 1, u, u, 0} Fn y)

/-- Sections over `y` of the direct image of abelian sheaves are corepresented by `ℤ_{K_y}^♯`:
`Stacks.Cohomology.CocontinuousPushforward.pushforwardSectionsCorepresentation`, read for
`AlgebraicGeometry.Stack.fibreSections`. -/
def fibreSectionsCorepresentation (y : 𝒴.val.val.obj) :
    fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y ≅ preadditiveCoyoneda.obj
      (op ((presheafToSheaf JX AddCommGrpCat.{u + 1}).obj (directImageSectionsPresheaf k y))) :=
  Stacks.Cohomology.CocontinuousPushforward.pushforwardSectionsCorepresentation.{u + 1, u + 1,
    u, u, 0} Fn JX y

/-- **Sections over `y` of the direct image of modules are corepresented by the sheafified
extension of scalars `𝒪_{K_y}` of `ℤ_{K_y}`**: they are the sections of the direct image of the
underlying abelian sheaf, which are `Hom(ℤ_{K_y}^♯, -)`
(`Stacks.Cohomology.CocontinuousPushforward.pushforwardSectionsCorepresentation`), and
`Hom(ℤ_{K_y}^♯, (-)_ab) = Hom(𝒪_{K_y}, -)` (`Stacks.SheafOfModules.tensorSheafHomIso`). -/
def directImageSectionsSuccCorepresentation (y : 𝒴.val.val.obj) :
    directImageSectionsSucc k τ y ≅ preadditiveCoyoneda.obj
      (op (Stacks.Cohomology.TensorSheafComparison.tensorSheaf JX RX
        (directImageSectionsPresheaf k y))) :=
  directImageSectionsSuccIso k τ y ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) (fibreSectionsCorepresentation k τ y) ≪≫
    (Stacks.SheafOfModules.tensorSheafHomIso.{u + 1, u, u, u + 1} JX RX
      (directImageSectionsPresheaf k y)).symm

attribute [local instance] Stacks.Cohomology.ModuleAbelianComparison.hasExt
  Stacks.Cohomology.ULiftUnitComparison.hasExtModules
  enoughInjectives_stackModules_succ additive_stackModuleDirectImageSucc

/-- **The derived functors of sections over `y` of the direct image of modules are those of the
abelian direct image, applied to the underlying abelian sheaf**:
`Rⁿ(ℳ ↦ (f_*ℳ)(y)) ≅ Rⁿ(𝒢 ↦ (f_*𝒢)(y)) ∘ (-)_ab`. Both are `Extⁿ(ℤ_{K_y}^♯, (-)_ab)`: on modules
by `Stacks.Cohomology.TensorSheafComparison.extTensorSheafIso` (`ℤ_{K_y}` is torsion-free), on
abelian sheaves by the corepresentation. -/
def rightDerivedDirectImageSectionsSuccIso (y : 𝒴.val.val.obj) (n : ℕ) :
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
    letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
    (directImageSectionsSucc k τ y).rightDerived n ≅
      SheafOfModules.toSheaf _ ⋙
        (fibreSections.{u, 0} B S hS 𝒳.val.val.p Fn τ y).rightDerived n :=
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} JX AddCommGrpCat.{u + 1}
  letI := IsGrothendieckAbelian.enoughInjectives (C := Sheaf JX AddCommGrpCat.{u + 1})
  Functor.rightDerivedIsoOfNatIso (directImageSectionsSuccCorepresentation k τ y) n ≪≫
    (Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda _ n).symm ≪≫
    Stacks.Cohomology.TensorSheafComparison.extTensorSheafIso JX RX
      (directImageSectionsPresheaf k y)
      (Stacks.Cohomology.TensorSheafComparison.isTorsionFree_freeAbelian _) n ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf _)
      (Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda _ n) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf _)
      (Functor.rightDerivedIsoOfNatIso (fibreSectionsCorepresentation k τ y).symm n)

end Succ

section Fppf

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ
  Stacks.Cohomology.ModuleAbelianComparison.hasExt
  Stacks.Cohomology.ULiftUnitComparison.hasExtModules
  enoughInjectives_stackModules_succ additive_stackModuleDirectImageSucc
  additive_stackModuleSheafificationSucc preservesHomology_stackModuleSheafificationSucc

variable (hfqc : IsQuasiCompactMorphism.{u, w} B S hS k)
  (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS k)

include hfqc hfqs in
/-- **The local step of Stacks 0GQW for modules**: for `f` quasi-compact and quasi-separated and
`y` an object of `𝒴` lying over an affine scheme, the derived functors of sections over `y` of
the direct image of modules, at module universe `u + 1`, commute with filtered colimits. They are
those of the abelian direct image applied to the underlying abelian sheaf
(`AlgebraicGeometry.Stack.rightDerivedDirectImageSectionsSuccIso`), which commute with filtered
colimits by `AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_fibreSections_fppf`;
and forgetting the module structure commutes with colimits. -/
theorem preservesColimitsOfShape_rightDerived_directImageSectionsSucc_fppf
    {y : 𝒴.val.val.obj} (hy : IsAffineObject B S hS 𝒴.val.val.p y) (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((directImageSectionsSucc k .fppf y).rightDerived n) := by
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1}
  let := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u + 1})
  have := preservesColimitsOfShape_rightDerived_fibreSections_fppf B S hS k y hfqc hfqs hy n I
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)) :=
    Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf.{u + 1, u + 1,
      u + 1, u, u, u + 1} _ I
  exact preservesColimitsOfShape_of_natIso (rightDerivedDirectImageSectionsSuccIso k .fppf y n).symm

include hfqc hfqs in
/-- **Stacks 0GQW for modules, at module universe `u + 1`, in the fppf topology.** For `f`
quasi-compact and quasi-separated, the higher direct images `Rⁿf_*` of sheaves of modules commute
with filtered colimits of `u + 1`-small shape.

`Rⁿf_*` is the sheafification of the derived presheaf direct image
(`AlgebraicGeometry.Stack.stackModuleDirectImageSuccRightDerivedIso`) and sheafification commutes
with colimits. The comparison map of derived presheaf direct images is bijective on sections over
every object lying over an affine scheme, by
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_directImageSectionsSucc_fppf` and
because colimits of presheaves of modules are computed on sections; every object of the fppf site
of `𝒴` is covered by such objects, so the comparison map becomes an isomorphism after
sheafification (**Stacks 0H6Y**). -/
theorem preservesColimitsOfShape_rightDerived_stackModuleDirectImageSucc_fppf (n : ℕ)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((stackModuleDirectImageSucc B S hS k .fppf).rightDerived n) := by
  let P0 := stackModuleDirectImageSucc B S hS k .fppf ⋙ SheafOfModules.forget
    (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf)
  let a := stackModuleSheafificationSucc .fppf 𝒴
  have hpre : PreservesColimitsOfShape I a :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        .fppf).obj)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  suffices h : PreservesColimitsOfShape I (P0.rightDerived n ⋙ a) from
    preservesColimitsOfShape_of_natIso (stackModuleDirectImageSuccRightDerivedIso k .fppf n).symm
  refine ⟨fun {K} => ?_⟩
  let φ := colimit.post K (P0.rightDerived n)
  have hφ : ∀ ⦃y : 𝒴.val.val.obj⦄, IsAffineObject B S hS 𝒴.val.val.p y →
      IsIso (((PresheafOfModules.toPresheaf _).map φ).app (op y)) := fun y hy => by
    let G := PresheafOfModules.toPresheaf (Stacks.RelativeCech.moduleRingSheaf B S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf).obj ⋙
        (evaluation _ AddCommGrpCat.{u + 1}).obj (op y)
    have : G.PreservesHomology := Functor.preservesHomologyOfExact _
    have : PreservesColimitsOfShape I ((P0 ⋙ G).rightDerived n) :=
      preservesColimitsOfShape_rightDerived_directImageSectionsSucc_fppf k hfqc hfqs hy n I
    have : PreservesColimitsOfShape I (P0.rightDerived n ⋙ G) :=
      preservesColimitsOfShape_of_natIso (Functor.rightDerivedCompIso P0 G n)
    have : IsIso (colimit.post (K ⋙ P0.rightDerived n) G ≫ G.map φ) :=
      colimit.post_post K (P0.rightDerived n) G ▸ inferInstance
    exact IsIso.of_isIso_comp_left (colimit.post (K ⋙ P0.rightDerived n) G) (G.map φ)
  have ha : IsIso (a.map φ) := by
    have : IsIso ((SheafOfModules.toSheaf _).map (a.map φ)) :=
      Presheaf.isIso_presheafToSheaf_map_of_isIso_app_of_covers.{u, u + 1, u + 1, u + 1}
        (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf) _
        (IsAffineObject B S hS 𝒴.val.val.p)
        (FibredSite.exists_affine_ofArrows B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids)
        hφ
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have : IsIso (colimit.post K (P0.rightDerived n ⋙ a)) :=
    colimit.post_post K (P0.rightDerived n) a ▸ inferInstance
  exact preservesColimit_of_isIso_post _ _

end Fppf

section Univ

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ
  enoughInjectives_stackModules_succ additive_stackModuleDirectImageSucc

/-- The universe lift of modules on the `τ`-site of an algebraic stack is
`SheafOfModules.uliftForPresentationFunctor`: both apply `ULift` to every module of sections. -/
def stackModuleULiftIsoUliftForPresentationFunctor (τ : SiteKind)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    stackModuleULift B S hS τ 𝒵 ≅
      SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u + 1} :=
  NatIso.ofComponents (fun _ => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))) (fun _ => rfl)

/-- **The universe lift of modules on the `τ`-site of an algebraic stack commutes with colimits**
indexed in the universe `u` of the schemes. -/
theorem preservesColimitsOfShape_stackModuleULift (τ : SiteKind)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (stackModuleULift B S hS τ 𝒵) :=
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒵.val.val.p τ
  have := SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor.{u + 1, u, u, u,
    u + 1} (J := BigFppfOver.associatedTopology B S hS 𝒵.val.val.p τ)
    (R := Stacks.RelativeCech.moduleRingSheaf B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids τ)
  preservesColimitsOfShape_of_natIso (stackModuleULiftIsoUliftForPresentationFunctor τ 𝒵).symm

/-- The direct image of modules on the fppf sites preserves limits, being a right adjoint. -/
private theorem preservesLimitsOfSize_fppfModulesPushforward :
    PreservesLimitsOfSize.{0, 0} (fppfModulesPushforward B S hS k) :=
  (fppfModulesPullbackPushforwardAdjunction B S hS k).rightAdjoint_preservesLimits

/-- The direct image of modules commutes with colimits of a shape if its zeroth right derived
functor does, as it is its own zeroth right derived functor. -/
private theorem preservesColimitsOfShape_fppfModulesPushforward_of_rightDerived_zero
    (J : Type u) [Category.{u} J] :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    PreservesColimitsOfShape J ((fppfModulesPushforward B S hS k).rightDerived 0) →
      PreservesColimitsOfShape J (fppfModulesPushforward B S hS k) := by
  intro h
  let := enoughInjectives_fppfModules B S hS 𝒳
  have := preservesLimitsOfSize_fppfModulesPushforward k
  exact preservesColimitsOfShape_of_natIso (fppfModulesPushforward B S hS k).rightDerivedZeroIsoSelf

variable (hfqc : IsQuasiCompactMorphism.{u, w} B S hS k)
  (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS k)

include hfqc hfqs in
/-- **Stacks 0GQW for modules on the fppf sites, at the module universe `u` of the schemes**: for
`f` quasi-compact and quasi-separated, the higher direct images
`AlgebraicGeometry.Stack.fppfModulesHigherDirectImage` commute with filtered colimits of
`u`-small shape. The universe lift carries `Rⁿf_*` at `u` to `Rⁿf_*` at `u + 1`
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImageULiftIso`), where this is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_rightDerived_stackModuleDirectImageSucc_fppf`;
the lift commutes with colimits and is fully faithful. -/
theorem preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered (n : ℕ)
    (J : Type u) [Category.{u} J] [IsFiltered J] :
    PreservesColimitsOfShape J (fppfModulesHigherDirectImage B S hS k n) := by
  have : IsFiltered (AsSmall.{u + 1} J) := IsFiltered.of_equivalence AsSmall.equiv
  have := preservesColimitsOfShape_rightDerived_stackModuleDirectImageSucc_fppf k hfqc hfqs n
    (AsSmall.{u + 1} J)
  have h2 : PreservesColimitsOfShape J
      ((stackModuleDirectImageSucc B S hS k .fppf).rightDerived n) :=
    preservesColimitsOfShape_of_equiv AsSmall.equiv.symm _
  have := Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u + 1} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) .fppf
  have : PreservesColimitsOfShape J
      ((Stacks.RelativeCech.moduleDirectImage.{u, u + 1, u + 1, u, u, u + 1} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
        .fppf).rightDerived n) := h2
  have : PreservesColimitsOfShape J
      (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) n) :=
    preservesColimitsOfShape_of_natIso
      (AlgebraicStacks.moduleDirectImageRightDerivedIso B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
        .fppf n)
  have := preservesColimitsOfShape_stackModuleULift .fppf 𝒳 J
  have : PreservesColimitsOfShape J (stackModuleHigherDirectImage B S hS k .fppf n ⋙
      stackModuleULift B S hS .fppf 𝒴) :=
    preservesColimitsOfShape_of_natIso (stackModuleHigherDirectImageULiftIso .fppf k n).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (stackModuleULift B S hS .fppf 𝒴)

include hfqc hfqs in
/-- **Stacks 0GQW for modules on the fppf sites in degree `0`**: for `f` quasi-compact and
quasi-separated, the direct image `AlgebraicGeometry.Stack.fppfModulesPushforward` commutes with
filtered colimits of `u`-small shape; it is its own zeroth right derived functor. -/
theorem preservesColimitsOfShape_fppfModulesPushforward_of_isFiltered
    (J : Type u) [Category.{u} J] [IsFiltered J] :
    PreservesColimitsOfShape J (fppfModulesPushforward B S hS k) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  have := preservesLimitsOfSize_fppfModulesPushforward k
  exact preservesColimitsOfShape_fppfModulesPushforward_of_rightDerived_zero k J
    (preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered k hfqc hfqs 0 J)

end Univ

section DirectSums

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ
  enoughInjectives_stackModules_succ additive_stackModuleDirectImageSucc

variable (hfqc : IsQuasiCompactMorphism.{u, w} B S hS k)
  (hfqs : AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS k)

include hfqc hfqs in
/-- **Higher direct images of modules along a qcqs morphism commute with direct sums**, on the
fppf sites at the module universe `u`: a direct sum is the filtered colimit of its finite
subsums, which the additive functor `Rⁿf_*` preserves. -/
theorem preservesColimitsOfShape_discrete_fppfModulesHigherDirectImage (n : ℕ) (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (fppfModulesHigherDirectImage B S hS k n) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  have := preservesLimitsOfSize_fppfModulesPushforward k
  have hC : HasColimitsOfSize.{u, u} (fppfModules B S hS 𝒳) :=
    @IsGrothendieckAbelian.hasColimits _ _ _ (isGrothendieckAbelian_fppfModules B S hS 𝒳)
  have hF : PreservesColimitsOfShape (Finset (Discrete α))
      ((fppfModulesPushforward B S hS k).rightDerived n) :=
    preservesColimitsOfShape_fppfModulesHigherDirectImage_of_isFiltered k hfqc hfqs n
      (Finset (Discrete α))
  have hCo : HasCoproducts.{u} (fppfModules B S hS 𝒳) := fun _ => hC.has_colimits_of_shape _
  exact @Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete _ _ _ _
    ((fppfModulesPushforward B S hS k).rightDerived n) α
    (@hasFiniteCoproducts_of_hasCoproducts.{u} _ _ hCo) hCo (hC.has_colimits_of_shape _)
    (Functor.preservesFiniteCoproductsOfAdditive _) hF

include hfqc hfqs in
/-- **The direct image of modules along a qcqs morphism commutes with direct sums**, on the
fppf sites at the module universe `u`. -/
theorem preservesColimitsOfShape_discrete_fppfModulesPushforward (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (fppfModulesPushforward B S hS k) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  have := preservesLimitsOfSize_fppfModulesPushforward k
  exact preservesColimitsOfShape_fppfModulesPushforward_of_rightDerived_zero k (Discrete α)
    (preservesColimitsOfShape_discrete_fppfModulesHigherDirectImage k hfqc hfqs 0 α)

end DirectSums

end AlgebraicGeometry.Stack

end
