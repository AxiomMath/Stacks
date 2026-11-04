module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComparison
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedPullbackTensorMate

/-!
# The identity of comparisons of direct images round the square of a represented morphism

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` and `φ` the morphism of
representable algebraic spaces it represents.
`AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`
is the one identity of comparisons of direct images round the square of ringed topoi of `g` on
which `AlgebraicGeometry.Space.representedSquareModulePullbackIso_hom_app_of_rightAdjointCompat`
rests.  This file proves it, by reading every factor on sections.

The reindexing of Stacks 04M0 is written here as a morphism of ringed sites
(`AlgebraicGeometry.Space.representedReindexSiteHom`) whose source is the small étale ringed site
of `yoneda.obj U` itself, so that the equivalence of Stacks 04M0 is the native equivalence of
direct images `SheafOfModules.pushforwardPushforwardEquivalence`
(`AlgebraicGeometry.Space.representedReindexSitePushforwardEquivalence`).  On sections the two
sides of the identity are computed separately: the right-hand side by
`Stacks.ReindexSquare.sections_rhs`, the left-hand side factor by factor
(`Stacks.ReindexSquare.lhsSections_of`).

## Main results

* `AlgebraicGeometry.Space.representedSquareRightAdjointCompat`: the identity
  `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat`.
* `AlgebraicGeometry.Space.representedSquareModulePullbackIso_hom_eq`: the comparison of the two
  factorizations of the square of `g` is the inverse mate of
  `AlgebraicGeometry.Space.representedModulePullbackIso`.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.SheafOfModules

universe wX vX uX wZ vZ uZ wA vA uA wB vB uB

variable {X : AlgebraicGeometry.RingedTopos.{vX, uX, wX}}
    {Z : AlgebraicGeometry.RingedTopos.{vZ, uZ, wZ}}
    {Y₁ : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    {Y₂ : AlgebraicGeometry.RingedTopos.{vB, uB, wB}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wX} RingCat.{wX})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{wZ} RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [X.J.HasSheafCompose (forget RingCat.{wX})] [Z.J.HasSheafCompose (forget RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget RingCat.{wA})] [Y₂.J.HasSheafCompose (forget RingCat.{wB})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wX})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [HasWeakSheafify X.J AddCommGrpCat.{wX}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wX}]
  [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}]
  [HasWeakSheafify Y₁.J AddCommGrpCat.{wA}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{wB}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  (φ₁ : RingedToposHom X Y₁) (ψ₁ : RingedToposHom Y₁ Z)
  (φ₂ : RingedToposHom X Y₂) (ψ₂ : RingedToposHom Y₂ Z) (χ : RingedToposHom X Z)
  (τ₁ : φ₁.toToposHom.pushforward ⋙ ψ₁.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₁ : fSharpSetComp φ₁ ψ₁ ≫
    τ₁.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (τ₂ : φ₂.toToposHom.pushforward ⋙ ψ₂.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₂ : fSharpSetComp φ₂ ψ₂ ≫
    τ₂.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ₁ : _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₁ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O)}
  {Lψ₂ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O)}
  (αφ₁ : φ₁.pullbackModules ≅ Lφ₁) (αψ₁ : ψ₁.pullbackModules ≅ Lψ₁) (αψ₂ : ψ₂.pullbackModules ≅ Lψ₂)

/-- `Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso` with the
comparison of the factorizations replaced by a natural transformation `θ` it is equal to.  Stated
for the whole natural transformation, so that a description of the comparison is matched once,
against `θ`, and not componentwise. -/
theorem pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq
    (θ : Lψ₁ ⋙ Lφ₁ ⟶ Lψ₂ ⋙ φ₂.pullbackModules)
    (hθ : (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom = θ)
    (F G : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O)) :
    Lφ₁.map (pullbackTensorIsoTransport ψ₁ αψ₁ F G).hom ≫
        (pullbackTensorIsoTransport φ₁ αφ₁ (Lψ₁.obj F) (Lψ₁.obj G)).hom ≫
          ((Tensor.sheafTensor X.O).map (θ.app F)).app (Lφ₁.obj (Lψ₁.obj G)) ≫
            ((Tensor.sheafTensor X.O).obj (φ₂.pullbackModules.obj (Lψ₂.obj F))).map (θ.app G) =
      θ.app (((Tensor.sheafTensor Z.O).obj F).obj G) ≫
        φ₂.pullbackModules.map (pullbackTensorIsoTransport ψ₂ αψ₂ F G).hom ≫
          (pullbackTensorIsoTransport φ₂ (Iso.refl _) (Lψ₂.obj F) (Lψ₂.obj G)).hom := by
  subst hθ
  exact pullbackTensorIsoTransport_square_factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂
    αφ₁ αψ₁ αψ₂ F G

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reindexing of the small étale ringed site of the scheme underlying `U` to the small étale
ringed site of the representable algebraic space `yoneda.obj U`, along the comparison of Stacks
04M0, as a morphism of ringed sites: the functor is the inverse of the comparison of sites and the
structure map is that of `Stacks.SheafOfModules.reindexRingedSiteHom`.

It is `Stacks.SheafOfModules.reindexRingedSiteHom` with its source written as the small étale
ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` of `yoneda.obj U` rather than as the
reindexed ringed site: the two structure sheaves agree
(`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`), and at this spelling the
sheaves of modules of its source are those of the small étale ringed topos of `yoneda.obj U` with
no comparison of structure sheaves. -/
noncomputable def representedReindexSiteHom (U : BigFppfOver B S hS) :
    AlgebraicGeometry.RingedSite.HomGeneral
      (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property) where
  u := (representedSmallEtaleEquivalence B S hS U).inverse
  isMorphismOfSites := (Stacks.SheafOfModules.reindexRingedSiteHom
    (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeCommRingStructureSheaf B S hS U)).isMorphismOfSites
  fsharp := (Stacks.SheafOfModules.reindexRingedSiteHom
    (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeCommRingStructureSheaf B S hS U)).fsharp

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- Base change of schemes along `g` is continuous, with both topologies spelled as the
projections of the small étale ringed sites. -/
instance isContinuous_representedSchemeBaseChange_smallEtaleRingedSite :
    (representedSchemeBaseChange B S hS g).IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).J :=
  isContinuous_representedSchemeBaseChange B S hS g

/-- Base change of schemes along `g` followed by the inverse of the comparison of Stacks 04M0 for
`T'` is continuous, with the topology of `T` spelled as the projection of its small étale ringed
site. -/
instance isContinuous_representedSchemeBaseChange_comp_inverse_smallEtaleRingedSite :
    (representedSchemeBaseChange B S hS g ⋙
        (representedSmallEtaleEquivalence B S hS T').inverse).IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).J
      (SmallEtale.topology B S hS (yoneda.obj T')) :=
  isContinuous_representedSchemeBaseChange_comp_inverse B S hS g

end AlgebraicGeometry.Space

open Opposite

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : AlgebraicGeometry.RingedTopos}
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat)]
  [X.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat)]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The comparison between the two spellings of the direct image of sheaves of modules is the
identity on sections. -/
theorem pushforwardModulesIso_hom_app_val_app
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : Y.Cᵒᵖ)
    (y : (f.pushforwardModules.obj N).val.obj U) :
    (f.pushforwardModulesIso.hom.app N).val.app U y = y :=
  congrArg (fun m => m.hom.app U y) (moduleSheafFunctor_map_pushforwardModulesIso f N)

/-- The inverse comparison between the two spellings of the direct image of sheaves of modules is
the identity on sections. -/
theorem pushforwardModulesIso_inv_app_val_app
    (N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : Y.Cᵒᵖ)
    (y : ((Stacks.Sheaves.RingedToposModules.pushforwardModules
      f.toRingedToposModulesHom).obj N).val.obj U) :
    (f.pushforwardModulesIso.inv.app N).val.app U y = y :=
  (pushforwardModulesIso_hom_app_val_app f N U _).symm.trans
    (congrArg (fun m => m.val.app U y) (f.pushforwardModulesIso.inv_hom_id_app N))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : HomGeneral X Y)

/-- The comparison of the two pushforwards of sheaves of modules along a morphism of ringed
sites is the identity on sections, at independent universes. -/
theorem HomGeneral.val_app_pushforwardModulesToposIsoGeneral_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (U : Y.Cᵒᵖ)
    (y : ((Stacks.Sheaves.RingedToposModules.pushforwardModules
      f.toRingedToposHom.toRingedToposModulesHom).obj N).val.obj U) :
    (f.pushforwardModulesToposIsoGeneral.hom.app N).val.app U y = y :=
  AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_hom_app_val_app f.toRingedToposHom N U y

/-- The inverse comparison of the two pushforwards of sheaves of modules along a morphism of
ringed sites is the identity on sections, at independent universes. -/
theorem HomGeneral.val_app_pushforwardModulesToposIsoGeneral_inv_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (U : Y.Cᵒᵖ) (y : (f.toRingedToposSiteHom.pushforwardTopos.obj N).val.obj U) :
    (f.pushforwardModulesToposIsoGeneral.inv.app N).val.app U y = y :=
  AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_inv_app_val_app f.toRingedToposHom N U y

/-- The comparison of the two pushforwards is the identity on sections of the underlying
sheaves of sets. -/
theorem HomGeneral.sections_pushforwardModulesToposIsoGeneral_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (U : Y.Cᵒᵖ)
    (y : (Sheaf.sectionsFunctor (toRingedTopos Y).J U).obj
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules
          f.toRingedToposHom.toRingedToposModulesHom).obj N))) :
    (Sheaf.sectionsFunctor (toRingedTopos Y).J U).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (f.pushforwardModulesToposIsoGeneral.hom.app N)) y = y :=
  HomGeneral.val_app_pushforwardModulesToposIsoGeneral_hom_app f N U y

end AlgebraicGeometry.RingedSite

namespace Stacks.Sheaves.RingedToposModules

open CategoryTheory

universe wc vc₁ uc₁ vc₂ uc₂ vc₃ uc₃

variable {X : AlgebraicGeometry.RingedTopos.{vc₁, uc₁, wc}}
  {Y : AlgebraicGeometry.RingedTopos.{vc₂, uc₂, wc}} {Z :
      AlgebraicGeometry.RingedTopos.{vc₃, uc₃, wc}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wc} RingCat.{wc})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wc} RingCat.{wc})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{wc} RingCat.{wc})]
  [X.J.HasSheafCompose (forget RingCat.{wc})] [Y.J.HasSheafCompose (forget RingCat.{wc})]
  [Z.J.HasSheafCompose (forget RingCat.{wc})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wc})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wc})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{wc})]

/-- The comparison of direct images of modules attached to the identity of the composite of
two morphisms of ringed topoi is, inversely, the identity on sections. -/
theorem sections_pushforwardModulesCompIso_comp_inv_app (ψ : RingedToposHom Y Z)
    (φ : RingedToposHom X Y)
    (hτ : fSharpSetComp φ ψ ≫ (Iso.refl (φ.toToposHom.pushforward ⋙
        ψ.toToposHom.pushforward)).hom.app
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
            fSharpSet (RingedToposHom.comp ψ φ))
    (M : SheafOfModules.{wc} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : Z.Cᵒᵖ)
    (y : (Sheaf.sectionsFunctor Z.J W).obj
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
      ((pushforwardModules (RingedToposHom.comp ψ φ)).obj M))) :
    (Sheaf.sectionsFunctor Z.J W).map ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pushforwardModulesCompIso φ ψ (RingedToposHom.comp ψ φ)
          (Iso.refl _) hτ).inv.app M)) y = y :=
  rfl

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Mates

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {χr : 𝒳 ⥤ 𝒵} {ψ₁r : 𝒴₁ ⥤ 𝒵} {φ₁r : 𝒳 ⥤ 𝒴₁} {ψ₂r : 𝒴₂ ⥤ 𝒵} {φ₂r φr : 𝒳 ⥤ 𝒴₂}
  {pbr : 𝒴₁ ⥤ 𝒵}

/-- `Stacks.Mates.RightAdjointSquareCompat` only depends on the two equivalences and the
comparisons with their inverses through their values. -/
theorem rightAdjointSquareCompat_of_eq {E₁ E₂ : 𝒵 ≌ 𝒴₂} {E₁' E₂' : 𝒴₁ ≌ 𝒳} (μ : φ₂r ≅ φr)
    (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (τ₂ : φ₂r ⋙ ψ₂r ≅ χr) (Pψ₁ : ψ₁r ≅ pbr)
    {Pφ₁ : φ₁r ≅ E₁'.inverse} {Pφ₁' : φ₁r ≅ E₂'.inverse} {Pψ₂ : ψ₂r ≅ E₁.inverse}
    {Pψ₂' : ψ₂r ≅ E₂.inverse} {Sg : pbr ⋙ E₁.functor ≅ E₁'.functor ⋙ φr}
    {Sg' : pbr ⋙ E₂.functor ≅ E₂'.functor ⋙ φr} (hE : E₁ = E₂) (hE' : E₁' = E₂')
    (hφ : HEq Pφ₁ Pφ₁') (hψ : HEq Pψ₂ Pψ₂') (hS : HEq Sg Sg')
    (H : RightAdjointSquareCompat E₂ E₂' μ τ₁ τ₂ Pψ₁ Pφ₁' Pψ₂' Sg') :
    RightAdjointSquareCompat E₁ E₁' μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂ Sg := by
  subst hE hE'
  cases hφ
  cases hψ
  cases hS
  exact H

/-- `Stacks.Mates.RightAdjointSquareCompat` only depends on the two equivalences, the target of
the comparison `Pψ₁` and the comparisons with the inverses through their values. -/
theorem rightAdjointSquareCompat_of_heq {E₁ E₂ : 𝒵 ≌ 𝒴₂} {E₁' E₂' : 𝒴₁ ≌ 𝒳} {μ : φ₂r ≅ φr}
    {τ₁ : φ₁r ⋙ ψ₁r ≅ χr} {τ₂ : φ₂r ⋙ ψ₂r ≅ χr} {pbr' : 𝒴₁ ⥤ 𝒵} {Pψ₁ : ψ₁r ≅ pbr}
    {Pψ₁' : ψ₁r ≅ pbr'} {Pφ₁ : φ₁r ≅ E₁'.inverse} {Pφ₁' : φ₁r ≅ E₂'.inverse}
    {Pψ₂ : ψ₂r ≅ E₁.inverse} {Pψ₂' : ψ₂r ≅ E₂.inverse} {Sg : pbr ⋙ E₁.functor ≅ E₁'.functor ⋙ φr}
    {Sg' : pbr' ⋙ E₂.functor ≅ E₂'.functor ⋙ φr}
    (H : RightAdjointSquareCompat E₂ E₂' μ τ₁ τ₂ Pψ₁' Pφ₁' Pψ₂' Sg')
        (hE : E₁ = E₂) (hE' : E₁' = E₂')
    (hp : pbr = pbr') (hP : HEq Pψ₁ Pψ₁') (hφ : HEq Pφ₁ Pφ₁')
        (hψ : HEq Pψ₂ Pψ₂') (hS : HEq Sg Sg') :
    RightAdjointSquareCompat E₁ E₁' μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂ Sg := by
  subst hE hE' hp
  cases hP
  cases hφ
  cases hψ
  cases hS
  exact H

end Stacks.Mates

namespace AlgebraicGeometry.Space

/-- The triangle identity of an equivalence `e`, read in the opposite categories at an object
`A`: the counit at `e.functor A` followed by the image of the unit at `A`. -/
private theorem counit_op_comp_functor_op_map_unit_op {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) (A : Cᵒᵖ) :
    (e.counit.app (e.functor.obj A.unop)).op ≫ e.functor.op.map ((NatTrans.op e.unit).app A) =
      𝟙 _ := by
  rw [NatTrans.op_app, Functor.op_map, Quiver.Hom.unop_op, ← op_comp]
  exact congrArg Quiver.Hom.op (e.functor_unit_comp A.unop)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The comparison functor of Stacks 04M0 is continuous, at the ringed-topos spellings. -/
instance isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos
    (U : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS U).functor.IsContinuous
      (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.J :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS U).functor.IsContinuous
    (SmallEtale.topology B S hS (yoneda.obj U)) (representedSchemeSmallEtaleTopology B S hS U))

/-- The inverse comparison functor of Stacks 04M0 is continuous, at the ringed-topos spellings. -/
instance isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos
    (U : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS U).inverse.IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.J
      (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).J :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS U).inverse.IsContinuous
    (representedSchemeSmallEtaleTopology B S hS U) (SmallEtale.topology B S hS (yoneda.obj U)))

/-- The structure map of the functor of the native comparison of Stacks 04M0: the identity of
the structure sheaf of `yoneda.obj U`, typed at the two ringed-site spellings. -/
noncomputable def representedReindexRingHom (U : BigFppfOver B S hS) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O) ⟶
      ((representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous RingCat.{u}
        (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).J
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O) :=
  𝟙 _

/-- The structure sheaf of `yoneda.obj U` is the structure sheaf of the scheme underlying `U`
read through the comparison functor. -/
theorem representedStructureRing_map (U : BigFppfOver B S hS)
    {A A' : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ} (f : A ⟶ A') :
    (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O).obj.map f =
      (Stacks.SheafOfModules.Tensor.ringSheaf
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O).obj.map
        ((representedSmallEtaleEquivalence B S hS U).functor.op.map f) :=
  rfl

/-- The structure map of `AlgebraicGeometry.Space.representedReindexSiteHom` is restriction
along the counit of the comparison of Stacks 04M0. -/
theorem representedReindexSiteHom_fSharpRing_app (U : BigFppfOver B S hS)
    (X : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ) :
    (representedReindexSiteHom B S hS U).toRingedToposSiteHom.fSharpRing.hom.app X =
      (Stacks.SheafOfModules.Tensor.ringSheaf
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O).obj.map
        ((representedSmallEtaleEquivalence B S hS U).counit.app X.unop).op :=
  rfl

/-- The counit condition of `SheafOfModules.pushforwardPushforwardEquivalence` for the
comparison of Stacks 04M0. -/
theorem representedReindexRing_counit (U : BigFppfOver B S hS) :
    Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O).obj =
      (representedReindexSiteHom B S hS U).toRingedToposSiteHom.fSharpRing.hom ≫
        (representedSmallEtaleEquivalence B S hS U).inverse.op.whiskerLeft
          (representedReindexRingHom B S hS U).hom :=
  NatTrans.ext (funext fun X =>
    (representedReindexSiteHom_fSharpRing_app B S hS U X).symm.trans (Category.comp_id _).symm)

/-- The unit condition of `SheafOfModules.pushforwardPushforwardEquivalence` for the
comparison of Stacks 04M0, at an object. -/
theorem representedReindexRing_unit_app (U : BigFppfOver B S hS)
    (A : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ) :
    (representedReindexSiteHom B S hS U).toRingedToposSiteHom.fSharpRing.hom.app
        ((representedSmallEtaleEquivalence B S hS U).functor.op.obj A) ≫
      (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O).obj.map
        ((NatTrans.op (representedSmallEtaleEquivalence B S hS U).unit).app A) = 𝟙 _ := by
  ext x
  refine (ConcreteCategory.congr_hom (representedStructureRing_map B S hS U
      ((NatTrans.op (representedSmallEtaleEquivalence B S hS U).unit).app A)) _).trans ?_
  refine (congrArg (fun y => ConcreteCategory.hom ((Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O).obj.map
        ((representedSmallEtaleEquivalence B S hS U).functor.op.map
          ((NatTrans.op (representedSmallEtaleEquivalence B S hS U).unit).app A))) y)
    (ConcreteCategory.congr_hom (representedReindexSiteHom_fSharpRing_app B S hS U _) x)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ x).symm.trans ?_
  rw [← CategoryTheory.Functor.map_comp]
  exact (congrArg (fun k => ConcreteCategory.hom ((Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O).obj.map k) x)
    (counit_op_comp_functor_op_map_unit_op (representedSmallEtaleEquivalence B S hS U) A)).trans
    (ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) x)

/-- The unit condition of `SheafOfModules.pushforwardPushforwardEquivalence` for the
comparison of Stacks 04M0. -/
theorem representedReindexRing_unit (U : BigFppfOver B S hS) :
    (representedReindexRingHom B S hS U).hom ≫
        (representedSmallEtaleEquivalence B S hS U).functor.op.whiskerLeft
          (representedReindexSiteHom B S hS U).toRingedToposSiteHom.fSharpRing.hom ≫
        Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O).obj =
      𝟙 _ :=
  NatTrans.ext (funext fun A =>
    (Category.id_comp _).trans (representedReindexRing_unit_app B S hS U A))

/-- The equivalence of Stacks 04M0 of direct images along the comparison of sites. -/
noncomputable abbrev representedReindexSitePushforwardEquivalence (U : BigFppfOver B S hS) :=
  SheafOfModules.pushforwardPushforwardEquivalence (representedSmallEtaleEquivalence B S hS U)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
          (SmallEtale.topology B S hS (yoneda.obj U))
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O)
    (representedReindexRingHom B S hS U)
    (representedReindexSiteHom B S hS U).toRingedToposSiteHom.fSharpRing
    (representedReindexRing_counit B S hS U) (representedReindexRing_unit B S hS U)

/-- `AlgebraicGeometry.Space.representedReindexEquivalence` is the native equivalence
`AlgebraicGeometry.Space.representedReindexSitePushforwardEquivalence`. -/
theorem representedReindexEquivalence_eq_pushforward (U : BigFppfOver B S hS) :
    representedReindexEquivalence B S hS U =
        representedReindexSitePushforwardEquivalence B S hS U :=
  rfl

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` with the functors of the
native comparisons of Stacks 04M0. -/
noncomputable abbrev representedSitePushforwardSquareIso :
    @Iso ((_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).toRingedTopos.O)) ⥤
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (schemeSpace T)).O))) _
    ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pushforwardTopos ⋙
      (representedReindexSitePushforwardEquivalence B S hS T).functor)
    ((representedReindexSitePushforwardEquivalence B S hS T').functor ⋙
      modulePushforward B S hS (schemeSpaceMap g)) :=
  representedModulePushforwardSquareIso B S hS g hg

/-- H at the native spelling. -/
abbrev RepresentedSquarePushforwardRightAdjointCompat : Prop :=
  Stacks.Mates.RightAdjointSquareCompat (representedReindexSitePushforwardEquivalence B S hS T)
      (representedReindexSitePushforwardEquivalence B S hS T')
      (modulePushforwardIso B S hS (representedSpaceMap B S hS g))
      (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g))
      (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg))
      (representedSchemeBaseChangePushforwardIso B S hS g)
      (representedReindexSiteHom B S hS T').pushforwardModulesToposIsoGeneral
      (representedReindexSiteHom B S hS T).pushforwardModulesToposIsoGeneral
      (representedSitePushforwardSquareIso B S hS g hg)

/-- `AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat` from its native form. -/
theorem representedSquareRightAdjointCompat_of_pushforward
    (H : RepresentedSquarePushforwardRightAdjointCompat B S hS g hg) :
    RepresentedSquareRightAdjointCompat B S hS g hg :=
  Stacks.Mates.rightAdjointSquareCompat_of_eq
    (modulePushforwardIso B S hS (representedSpaceMap B S hS g))
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g))
    (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg))
    (representedSchemeBaseChangePushforwardIso B S hS g)
    (representedReindexEquivalence_eq_pushforward B S hS T)
    (representedReindexEquivalence_eq_pushforward B S hS T')
    HEq.rfl HEq.rfl HEq.rfl H

end AlgebraicGeometry.Space

namespace Stacks.ReindexSquare

open CategoryTheory Opposite

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Conj

variable {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
  (e : D ≌ A) (e' : D' ≌ A') (bc : A ⥤ A') (sbc : D ⥤ D') (s : sbc ⋙ e'.functor ≅ e.functor ⋙ bc)

/-- The components of the inverse of the square `s` conjugated by `e` and `e'`. -/
theorem conj_inv_app (W : A) :
    ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (e.inverse ⋙ sbc) e'.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft e.inverse s ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso bc ≪≫
        Functor.leftUnitor _) e'.inverse).inv.app W =
      e'.inverse.map (bc.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
        e'.unitIso.inv.app (sbc.obj (e.inverse.obj W)) := by
  simp

end Conj

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
  {A' : Type u₃} [Category.{v₃} A'] {D' : Type u₄} [Category.{v₄} D']
  {JA : GrothendieckTopology A} {JD : GrothendieckTopology D}
  {JA' : GrothendieckTopology A'} {JD' : GrothendieckTopology D'}
  [JA.HasSheafCompose (forget AddCommGrpCat.{w})] [JD.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JA'.HasSheafCompose (forget AddCommGrpCat.{w})] [JD'.HasSheafCompose (forget AddCommGrpCat.{w})]

section Pushforward

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  [J₁.HasSheafCompose (forget AddCommGrpCat.{w})] [J₂.HasSheafCompose (forget AddCommGrpCat.{w})]
  {F : C₁ ⥤ C₂} [F.IsContinuous J₁ J₂] {R₁ : Sheaf J₁ RingCat.{w}} {R₂ : Sheaf J₂ RingCat.{w}}
  (φ : R₁ ⟶ (F.sheafPushforwardContinuous RingCat.{w} J₁ J₂).obj R₂)

/-- The direct image of a morphism of modules on sections. -/
theorem sections_pushforward_map {M N : SheafOfModules.{w} R₂} (f : M ⟶ N) (W : C₁)
    (x : (Sheaf.sectionsFunctor J₁ (op W)).obj ((Sheaf.moduleSheafFunctor R₁).obj
      ((SheafOfModules.pushforward.{w} φ).obj M))) :
    (Sheaf.sectionsFunctor J₁ (op W)).map ((Sheaf.moduleSheafFunctor R₁).map
      ((SheafOfModules.pushforward.{w} φ).map f)) x =
      (Sheaf.sectionsFunctor J₂ (op (F.obj W))).map ((Sheaf.moduleSheafFunctor R₂).map f) x :=
  rfl

/-- The restriction maps of a direct image of modules. -/
theorem moduleSheaf_pushforward_map (M : SheafOfModules.{w} R₂) {W W' : C₁} (k : W ⟶ W')
    (x : ((Sheaf.moduleSheafFunctor R₁).obj ((SheafOfModules.pushforward.{w} φ).obj M)).obj.obj
      (op W')) :
    ((Sheaf.moduleSheafFunctor R₁).obj ((SheafOfModules.pushforward.{w} φ).obj M)).obj.map k.op x =
      ((Sheaf.moduleSheafFunctor R₂).obj M).obj.map (F.map k).op x :=
  rfl

end Pushforward

variable {e : D ≌ A} {e' : D' ≌ A'}
  [e.functor.IsContinuous JD JA] [e.inverse.IsContinuous JA JD]
  [e'.functor.IsContinuous JD' JA'] [e'.inverse.IsContinuous JA' JD']
  {RA : Sheaf JA RingCat.{w}} {RD : Sheaf JD RingCat.{w}}
  {RA' : Sheaf JA' RingCat.{w}} {RD' : Sheaf JD' RingCat.{w}}
  {φe : RD ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} JD JA).obj RA}
  {ψe : RA ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} JA JD).obj RD}
  {H₁ : Functor.whiskerRight (NatTrans.op e.counit) RA.obj =
    ψe.hom ≫ e.inverse.op.whiskerLeft φe.hom}
  {H₂ : φe.hom ≫ e.functor.op.whiskerLeft ψe.hom ≫
    Functor.whiskerRight (NatTrans.op e.unit) RD.obj = 𝟙 RD.obj}
  {φe' : RD' ⟶ (e'.functor.sheafPushforwardContinuous RingCat.{w} JD' JA').obj RA'}
  {ψe' : RA' ⟶ (e'.inverse.sheafPushforwardContinuous RingCat.{w} JA' JD').obj RD'}
  {H₁' : Functor.whiskerRight (NatTrans.op e'.counit) RA'.obj =
    ψe'.hom ≫ e'.inverse.op.whiskerLeft φe'.hom}
  {H₂' : φe'.hom ≫ e'.functor.op.whiskerLeft ψe'.hom ≫
    Functor.whiskerRight (NatTrans.op e'.unit) RD'.obj = 𝟙 RD'.obj}

/-- The inverse of the equivalence of pushforwards on sections of morphisms. -/
theorem sections_inverse_map {M N : SheafOfModules.{w} RD} (f : M ⟶ N) (W : A)
    (x : (Sheaf.sectionsFunctor JA (op W)).obj ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj M))) :
    (Sheaf.sectionsFunctor JA (op W)).map ((Sheaf.moduleSheafFunctor RA).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.map f)) x =
      (Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor RD).map f) x :=
  rfl

/-- The restriction maps of the inverse of the equivalence of pushforwards. -/
theorem moduleSheaf_inverse_obj_map (N : SheafOfModules.{w} RD) {W W' : A} (k : W ⟶ W')
    (y : ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj N)).obj.obj
      (op W')) :
    ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj N)).obj.map
        k.op y =
      ((Sheaf.moduleSheafFunctor RD).obj N).obj.map (e.inverse.map k).op y :=
  rfl

omit [JD.HasSheafCompose (forget AddCommGrpCat)] in
/-- The inverse unit of the equivalence of pushforwards is restriction along the counit. -/
theorem sections_unitIso_inv_app (X : SheafOfModules.{w} RA) (W : A)
    (x : (Sheaf.sectionsFunctor JA (op W)).obj ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj
        ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).functor.obj X)))) :
    (Sheaf.sectionsFunctor JA (op W)).map ((Sheaf.moduleSheafFunctor RA).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).unitIso.inv.app X)) x =
      ((Sheaf.moduleSheafFunctor RA).obj X).obj.map (e.counitIso.inv.app W).op x :=
  rfl

omit [JA'.HasSheafCompose (forget AddCommGrpCat)] in
/-- The inverse counit of the equivalence of pushforwards is restriction along the unit. -/
theorem sections_counitIso_inv_app (N : SheafOfModules.{w} RD') (U : D')
    (x : (Sheaf.sectionsFunctor JD' (op U)).obj ((Sheaf.moduleSheafFunctor RD').obj N)) :
    (Sheaf.sectionsFunctor JD' (op U)).map ((Sheaf.moduleSheafFunctor RD').map
      ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').counitIso.inv.app N))
        x =
      ((Sheaf.moduleSheafFunctor RD').obj N).obj.map (e'.unitIso.inv.app U).op x :=
  rfl

variable {bc : A ⥤ A'} {sbc : D ⥤ D'} [bc.IsContinuous JA JA'] [sbc.IsContinuous JD JD']
  {ρ : RA ⟶ (bc.sheafPushforwardContinuous RingCat.{w} JA JA').obj RA'}
  {σ : RD ⟶ (sbc.sheafPushforwardContinuous RingCat.{w} JD JD').obj RD'}
  (s : sbc ⋙ e'.functor ≅ e.functor ⋙ bc)
  {Φm : SheafOfModules.{w} RD' ⥤ SheafOfModules.{w} RD} (χ : Φm ≅ SheafOfModules.pushforward.{w} σ)
  (Sg : SheafOfModules.pushforward.{w} ρ ⋙ SheafOfModules.pushforward.{w} φe ≅
    SheafOfModules.pushforward.{w} φe' ⋙ Φm)

/-- The components of the square `Sg` of right adjoints on sections, through `s` and `χ`. -/
def SectionsSquareInv (Sg : SheafOfModules.pushforward.{w} ρ ⋙ SheafOfModules.pushforward.{w} φe ≅
    SheafOfModules.pushforward.{w} φe' ⋙ Φm) : Prop :=
  ∀ (M : SheafOfModules.{w} RA') (V : D)
    (y : (Sheaf.sectionsFunctor JD (op V)).obj ((Sheaf.moduleSheafFunctor RD).obj
      (Φm.obj ((SheafOfModules.pushforward.{w} φe').obj M)))),
    (Sheaf.sectionsFunctor JD (op V)).map ((Sheaf.moduleSheafFunctor RD).map (Sg.inv.app M)) y =
      ((Sheaf.moduleSheafFunctor RA').obj M).obj.map (s.inv.app V).op
        ((Sheaf.sectionsFunctor JD (op V)).map ((Sheaf.moduleSheafFunctor RD).map
          (χ.hom.app ((SheafOfModules.pushforward.{w} φe').obj M))) y)

omit [JA.HasSheafCompose (forget AddCommGrpCat)] [JD'.HasSheafCompose (forget AddCommGrpCat)]
  [e.inverse.IsContinuous JA JD] [e'.inverse.IsContinuous JA' JD'] in
/-- The structural square of `s` followed by `χ` satisfies `SectionsSquareInv`. -/
theorem sectionsSquareInv_of_squareIso [(e.functor ⋙ bc).IsContinuous JD JA']
    [(sbc ⋙ e'.functor).IsContinuous JD JA']
    (he : SheafOfModules.comparisonComp φe ρ ≫
      (Functor.sheafPushforwardContinuousNatTrans s.hom RingCat.{w} JD JA').app RA' =
        SheafOfModules.comparisonComp σ φe') :
    SectionsSquareInv s χ (SheafOfModules.pushforwardComp.{w} φe ρ ≪≫
      SheafOfModules.pushforwardCongr₂.{w} _ s he ≪≫
      (SheafOfModules.pushforwardComp.{w} σ φe').symm ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.pushforward.{w} φe') χ.symm) :=
  fun _ _ _ => rfl

/-- The right-hand side of `Stacks.Mates.RightAdjointSquareCompat` on sections, for an
equivalence of pushforwards and a square satisfying
`Stacks.ReindexSquare.SectionsSquareInv`. -/
theorem sections_rhs
    (hSg : SectionsSquareInv s χ Sg)
    (N : SheafOfModules.{w} RD') (W : A)
    (x : (Sheaf.sectionsFunctor JA (op W)).obj ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj
        (Φm.obj N)))) :
    (Sheaf.sectionsFunctor JA (op W)).map ((Sheaf.moduleSheafFunctor RA).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.map
          (Φm.map ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
            H₂').counitIso.inv.app N)) ≫
        (SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.map
          (Sg.inv.app ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
            H₂').inverse.obj N)) ≫
        (SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).unitIso.inv.app
          ((SheafOfModules.pushforward.{w} ρ).obj
            ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
              H₂').inverse.obj N)))) x =
      ((Sheaf.moduleSheafFunctor RD').obj N).obj.map
        (e'.inverse.map (bc.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op
        ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor RD).map (χ.hom.app N)) x) := by
  have hχ : ∀ y : (Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).obj
      ((Sheaf.moduleSheafFunctor RD).obj (Φm.obj N)),
      (Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
        ((Sheaf.moduleSheafFunctor RD).map (χ.hom.app
          ((SheafOfModules.pushforward.{w} φe').obj
            ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').inverse.obj N))))
        ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor RD).map (Φm.map
            ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
              H₂').counitIso.inv.app N))) y) =
      (Sheaf.sectionsFunctor JD' (op (sbc.obj (e.inverse.obj W)))).map
        ((Sheaf.moduleSheafFunctor RD').map
          ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').counitIso.inv.app
            N))
        ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor RD).map (χ.hom.app N)) y) := fun y => by
    have h := congrArg (fun f => (Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
      ((Sheaf.moduleSheafFunctor RD).map f) y)
      (χ.hom.naturality ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
        H₂').counitIso.inv.app N))
    simp only [Functor.map_comp, ConcreteCategory.comp_apply, Functor.comp_obj,
      Functor.id_obj] at h
    exact h
  have hk : ∀ z : ((Sheaf.moduleSheafFunctor RD').obj N).obj.obj
      (op (sbc.obj (e.inverse.obj W))),
      ((Sheaf.moduleSheafFunctor RD').obj N).obj.map
        (e'.inverse.map (bc.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op z =
      ((Sheaf.moduleSheafFunctor RD').obj N).obj.map
        (e'.inverse.map (bc.map (e.counitIso.inv.app W))).op
        (((Sheaf.moduleSheafFunctor RD').obj N).obj.map
          (e'.inverse.map (s.inv.app (e.inverse.obj W))).op
          (((Sheaf.moduleSheafFunctor RD').obj N).obj.map
            (e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op z)) := fun z => by
    simp only [op_comp, Functor.map_comp_apply]
  change ((Sheaf.moduleSheafFunctor RA).obj ((SheafOfModules.pushforward.{w} ρ).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
          H₂').inverse.obj N))).obj.map
      (e.counitIso.inv.app W).op
      ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map ((Sheaf.moduleSheafFunctor RD).map
        (Sg.inv.app ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
          H₂').inverse.obj N)))
        ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map ((Sheaf.moduleSheafFunctor RD).map
          (Φm.map ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁'
            H₂').counitIso.inv.app N))) x)) = _
  rw [hSg ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').inverse.obj N)
    (e.inverse.obj W) ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
      ((Sheaf.moduleSheafFunctor RD).map (Φm.map
        ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').counitIso.inv.app
          N))) x), hχ x]
  exact (hk _).symm

section Compat

variable {φ₂r : SheafOfModules.{w} RD' ⥤ SheafOfModules.{w} RD} (μ : φ₂r ≅ Φm)
  {χr : SheafOfModules.{w} RD' ⥤ SheafOfModules.{w} RA}
  {ψ₁r : SheafOfModules.{w} RA' ⥤ SheafOfModules.{w} RA}
  {φ₁r : SheafOfModules.{w} RD' ⥤ SheafOfModules.{w} RA'}
  {ψ₂r : SheafOfModules.{w} RD ⥤ SheafOfModules.{w} RA}
  (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (τ₂ : φ₂r ⋙ ψ₂r ≅ χr) (Pψ₁ : ψ₁r ≅ SheafOfModules.pushforward.{w} ρ)
  (Pφ₁ : φ₁r ≅ (SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂').inverse)
  (Pψ₂ : ψ₂r ≅ (SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse)

/-- The left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on sections: restriction of
the chart comparison `χ` along the components of the conjugate of `s`. -/
def LHSSections : Prop :=
  ∀ (N : SheafOfModules.{w} RD') (W : A)
    (x : (Sheaf.sectionsFunctor JA (op W)).obj ((Sheaf.moduleSheafFunctor RA).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.obj
        (Φm.obj N)))),
    (Sheaf.sectionsFunctor JA (op W)).map ((Sheaf.moduleSheafFunctor RA).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂).inverse.map
          (μ.inv.app N) ≫ Pψ₂.inv.app (φ₂r.obj N) ≫ τ₂.hom.app N ≫ τ₁.inv.app N ≫
        Pψ₁.hom.app (φ₁r.obj N) ≫ (SheafOfModules.pushforward.{w} ρ).map (Pφ₁.hom.app N))) x =
      ((Sheaf.moduleSheafFunctor RD').obj N).obj.map
        (e'.inverse.map (bc.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op
        ((Sheaf.sectionsFunctor JD (op (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor RD).map (χ.hom.app N)) x)

/-- `Stacks.Mates.RightAdjointSquareCompat` from its two sides on sections. -/
theorem rightAdjointSquareCompat_of_sections (hSg : SectionsSquareInv s χ Sg)
    (hL : LHSSections s χ μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂) :
    Stacks.Mates.RightAdjointSquareCompat
      (SheafOfModules.pushforwardPushforwardEquivalence e φe ψe H₁ H₂)
      (SheafOfModules.pushforwardPushforwardEquivalence e' φe' ψe' H₁' H₂') μ τ₁ τ₂ Pψ₁ Pφ₁ Pψ₂
      Sg := fun N =>
  Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (Sheaf.hom_ext_sections fun W x => (hL N W.unop x).trans
      (sections_rhs s χ Sg hSg N W.unop x).symm)

end Compat

section Chain

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] {R : Sheaf J RingCat.{w}}

/-- A composite of six morphisms of sheaves of modules on a section, from the values of the
first two factors, of the third, and of the last three. -/
theorem sections_comp₆_eq {M₁ M₂ M₃ M₄ M₅ M₆ M₇ : SheafOfModules.{w} R} (f₁ : M₁ ⟶ M₂)
    (f₂ : M₂ ⟶ M₃) (f₃ : M₃ ⟶ M₄) (f₄ : M₄ ⟶ M₅) (f₅ : M₅ ⟶ M₆) (f₆ : M₆ ⟶ M₇) {X : Cᵒᵖ}
    (x₁ : (Sheaf.sectionsFunctor J X).obj ((Sheaf.moduleSheafFunctor R).obj M₁))
    (x₃ : (Sheaf.sectionsFunctor J X).obj ((Sheaf.moduleSheafFunctor R).obj M₃))
    (x₄ : (Sheaf.sectionsFunctor J X).obj ((Sheaf.moduleSheafFunctor R).obj M₄))
    (x₇ : (Sheaf.sectionsFunctor J X).obj ((Sheaf.moduleSheafFunctor R).obj M₇))
    (h₁₂ : (Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₂)
      ((Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₁) x₁) = x₃)
    (h₃ : (Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₃) x₃ = x₄)
    (h₄₅₆ : (Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₆)
      ((Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₅)
        ((Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map f₄) x₄)) = x₇) :
    (Sheaf.sectionsFunctor J X).map ((Sheaf.moduleSheafFunctor R).map
      (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆)) x₁ = x₇ := by
  subst h₁₂ h₃ h₄₅₆
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]

end Chain

section HomGeneralSquare

/-! The left-hand side on sections when the three comparisons of pushforwards are those of
morphisms of ringed sites.  Every category of the four sites is written as the category of its
ringed topos, `(AlgebraicGeometry.RingedSite.toRingedTopos X).C` with its own instance; the kernel
checks of the statements below are syntactic only at that uniform spelling. -/

open AlgebraicGeometry.RingedSite (HomGeneral)

local notation "𝒯" => AlgebraicGeometry.RingedSite.toRingedTopos

local notation "𝒪" => Stacks.SheafOfModules.Tensor.ringSheaf

variable {XD : AlgebraicGeometry.RingedSite.{u₂, v₂, w}} {YA : AlgebraicGeometry.RingedSite.{u₁,
    v₁, w}}
  {XD' : AlgebraicGeometry.RingedSite.{u₄, v₄, w}} {YA' : AlgebraicGeometry.RingedSite.{u₃, v₃, w}}
  [XD.J.HasSheafCompose (forget RingCat.{w})] [XD.J.HasSheafCompose (forget₂ CommRingCat.{w}
      RingCat.{w})]
  [XD.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [YA.J.HasSheafCompose (forget RingCat.{w})] [YA.J.HasSheafCompose (forget₂ CommRingCat.{w}
      RingCat.{w})]
  [YA.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [XD'.J.HasSheafCompose (forget RingCat.{w})] [XD'.J.HasSheafCompose (forget₂ CommRingCat.{w}
      RingCat.{w})]
  [XD'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [YA'.J.HasSheafCompose (forget RingCat.{w})] [YA'.J.HasSheafCompose (forget₂ CommRingCat.{w}
      RingCat.{w})]
  [YA'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (e : @CategoryTheory.Equivalence (𝒯 XD).C (𝒯 YA).C (𝒯 XD).category (𝒯 YA).category) [hc₁ :
      e.functor.IsContinuous (𝒯 XD).J (𝒯 YA).J]
  [hc₂ : e.inverse.IsContinuous (𝒯 YA).J (𝒯 XD).J] (hm : IsMorphismOfSites.{w} e.inverse YA.J XD.J)
  (fs : YA.O ⟶ (e.inverse.sheafPushforwardContinuous CommRingCat.{w} YA.J XD.J).obj XD.O)
  (φe : (𝒪 (𝒯 XD).O) ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} (𝒯 XD).J (𝒯 YA).J).obj (𝒪
      (𝒯 YA).O))
  {H₁ : Functor.whiskerRight (NatTrans.op e.counit) (𝒪 (𝒯 YA).O).obj =
      (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing.hom ≫
        e.inverse.op.whiskerLeft φe.hom}
  {H₂ : φe.hom ≫ e.functor.op.whiskerLeft (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm
      fs).toRingedToposSiteHom.fSharpRing.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) (𝒪 (𝒯 XD).O).obj = 𝟙 (𝒪 (𝒯 XD).O).obj}
  (e' : @CategoryTheory.Equivalence (𝒯 XD').C (𝒯 YA').C (𝒯 XD').category (𝒯 YA').category) [hc₃ :
      e'.functor.IsContinuous (𝒯 XD').J (𝒯 YA').J]
  [hc₄ : e'.inverse.IsContinuous (𝒯 YA').J (𝒯 XD').J] (hm' : IsMorphismOfSites.{w} e'.inverse YA'.J
      XD'.J)
  (fs' : YA'.O ⟶ (e'.inverse.sheafPushforwardContinuous CommRingCat.{w} YA'.J XD'.J).obj XD'.O)
  (φe' : (𝒪 (𝒯 XD').O) ⟶ (e'.functor.sheafPushforwardContinuous RingCat.{w} (𝒯 XD').J (𝒯
      YA').J).obj (𝒪 (𝒯 YA').O))
  {H₁' : Functor.whiskerRight (NatTrans.op e'.counit) (𝒪 (𝒯 YA').O).obj =
      (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm' fs').toRingedToposSiteHom.fSharpRing.hom
        ≫ e'.inverse.op.whiskerLeft φe'.hom}
  {H₂' : φe'.hom ≫ e'.functor.op.whiskerLeft (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposSiteHom.fSharpRing.hom ≫
      Functor.whiskerRight (NatTrans.op e'.unit) (𝒪 (𝒯 XD').O).obj = 𝟙 (𝒪 (𝒯 XD').O).obj}
  (g₀ : AlgebraicGeometry.RingedSite.HomGeneral YA' YA)
  [hc₅ : g₀.toRingedToposSiteHom.u.IsContinuous (𝒯 YA).J (𝒯 YA').J]
  {Φm φ₂r : SheafOfModules.{w} (𝒪 (𝒯 XD').O) ⥤ SheafOfModules.{w} (𝒪 (𝒯 XD).O)}

/-- Sections over `W` of the inverse of the equivalence of pushforwards, read on the site `D`. -/
def castSectionsInverse (M : SheafOfModules.{w} (𝒪 (𝒯 XD).O)) (W : (𝒯 YA).C) (z :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
    (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD)
    (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj M)))) :
    ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).obj
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj M)) := z

/-- Sections over `e⁻¹ W` read as sections of the inverse of the equivalence of pushforwards. -/
def castSectionsToInverse (M : SheafOfModules.{w} (𝒪 (𝒯 XD).O)) (W : (𝒯 YA).C) (z :
    ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).obj
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj M))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X :=
      XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj M))) := z

/-- Sections of the inverse of the equivalence of pushforwards read as sections of the
pushforward along the morphism of ringed sites. -/
def castSectionsInverseToPushforwardModules (M : SheafOfModules.{w} (𝒪 (𝒯 XD).O)) (W : (𝒯 YA).C) (z
    : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
    (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD)
    (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj M)))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).obj ((pushforwardModules (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm
      fs).toRingedToposHom.toRingedToposModulesHom).obj M))) := z

/-- Sections of the direct image of modules along the ringed topos morphism of `g₀` read as
sections of the pushforward along its structure map. -/
def castSectionsPushforwardModules (M : SheafOfModules.{w} (𝒪 (𝒯 YA').O)) (W : (𝒯 YA).C) (z :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
    (𝒯 YA).O)).obj ((pushforwardModules g₀.toRingedToposHom.toRingedToposModulesHom).obj M)))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).obj ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).obj M)))
      := z

/-- The same along the second equivalence of pushforwards, under the pushforward along `g₀`. -/
def castSectionsPushforwardInverse (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C)
    (z : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).obj
      ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N))))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).obj ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e' φe' (HomGeneral.mk (X := XD') (Y :=
      YA') e'.inverse hm' fs').toRingedToposSiteHom.fSharpRing H₁' H₂').inverse.obj N)))) := z

/-- The comparison of the two pushforwards along the morphism of ringed sites of `e`, with the
target written as the inverse of the equivalence of pushforwards. -/
def homGeneralPushforwardInverseIso : (pushforwardModules (HomGeneral.mk (X := XD) (Y := YA)
    e.inverse hm fs).toRingedToposHom.toRingedToposModulesHom) ≅
    (SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
    e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse := (HomGeneral.mk (X := XD) (Y
    := YA) e.inverse hm fs).pushforwardModulesToposIsoGeneral

/-- The comparison of the two pushforwards along `g₀`, with the target written as the
pushforward along the structure map. -/
def pushforwardModulesIsoPushforward : (pushforwardModules
    g₀.toRingedToposHom.toRingedToposModulesHom) ≅ (SheafOfModules.pushforward.{w}
    g₀.toRingedToposSiteHom.fSharpRing) := g₀.pushforwardModulesToposIsoGeneral

omit [XD.J.HasSheafCompose (forget RingCat)] [XD.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [YA.J.HasSheafCompose (forget RingCat)] [YA.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The inverse of the equivalence of pushforwards on sections of a morphism, read on the site
`D` through the casts of sections. -/
theorem sections_inverse_map_castSections (M M' : SheafOfModules.{w} (𝒪 (𝒯 XD).O)) (f : M ⟶ M') (W
    : (𝒯 YA).C)
    (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X
      := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj M)))) (y
      : ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).obj
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj M')))
    (h : ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).map (f)) (castSectionsInverse (e := e) (hm := hm)
      (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) M W x)) = y) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X :=
      XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.map f)) x) =
      castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) M' W y
      := h

/-- The inverse comparison of the two pushforwards along the morphism of ringed sites of `e` is
the cast of sections. -/
theorem sections_homGeneralPushforwardInverseIso_inv_app (M : SheafOfModules.{w} (𝒪 (𝒯 XD).O)) (W :
    (𝒯 YA).C)
    (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X
      := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj M)))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe)
      (H₁ := H₁) (H₂ := H₂)).inv.app M)) x) = castSectionsInverseToPushforwardModules (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) M W x :=
  AlgebraicGeometry.RingedSite.HomGeneral.val_app_pushforwardModulesToposIsoGeneral_inv_app
      (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm fs) M (@Opposite.op (𝒯 YA).C W) x

omit [YA.J.HasSheafCompose (forget RingCat)]
  [YA.J.HasSheafCompose (forget₂ CommRingCat RingCat)] hc₅ in
/-- The pushforward along `g₀` of the comparison of the two pushforwards along the morphism of
ringed sites of `e'` is the cast of sections. -/
theorem sections_pushforward_map_homGeneralPushforwardInverseIso_hom_app (N : SheafOfModules.{w} (𝒪
    (𝒯 XD').O)) (W : (𝒯 YA).C)
    (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).obj
      ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N))))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).map
      ((homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ := H₁')
      (H₂ := H₂')).hom.app N))) x) =
      castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁')
        (H₂' := H₂') (g₀ := g₀) N W x :=
  have : g₀.toRingedToposSiteHom.u.IsContinuous (𝒯 YA).J (𝒯 YA').J :=
    g₀.toRingedToposSiteHom.isContinuous
  (sections_pushforward_map g₀.toRingedToposSiteHom.fSharpRing ((homGeneralPushforwardInverseIso
      (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ := H₁') (H₂ := H₂')).hom.app N) W x).trans
    (AlgebraicGeometry.RingedSite.HomGeneral.sections_pushforwardModulesToposIsoGeneral_hom_app
      (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm' fs') N (@Opposite.op (𝒯 YA').C
        (g₀.toRingedToposSiteHom.u.obj W)) x)

omit hc₃ in
/-- The comparison of the two pushforwards along `g₀`, at a pushforward along the morphism of
ringed sites of `e'`, is the cast of sections. -/
theorem sections_pushforwardModulesIsoPushforward_hom_app (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W
    : (𝒯 YA).C)
    (x : (Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj (((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom) ⋙ (pushforwardModules
      g₀.toRingedToposHom.toRingedToposModulesHom)).obj N))) :
    (Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
      YA).O)).map (X := ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom) ⋙ (pushforwardModules
      g₀.toRingedToposHom.toRingedToposModulesHom)).obj N) ((pushforwardModulesIsoPushforward (g₀
      := g₀)).hom.app ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N))) x =
      castSectionsPushforwardModules (g₀ := g₀) ((pushforwardModules (HomGeneral.mk (X := XD') (Y
        := YA') e'.inverse hm' fs').toRingedToposHom.toRingedToposModulesHom).obj N) W x :=
  AlgebraicGeometry.RingedSite.HomGeneral.val_app_pushforwardModulesToposIsoGeneral_hom_app g₀
      ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N) (@Opposite.op (𝒯 YA).C W) x

variable {sbc : @CategoryTheory.Functor (𝒯 XD).C (𝒯 XD).category (𝒯 XD').C (𝒯 XD').category} [hc₆ :
    sbc.IsContinuous (𝒯 XD).J (𝒯 XD').J]
  {σ : (𝒪 (𝒯 XD).O) ⟶ (sbc.sheafPushforwardContinuous RingCat.{w} (𝒯 XD).J (𝒯 XD').J).obj (𝒪 (𝒯
      XD').O)}
  (s : sbc ⋙ e'.functor ≅ e.functor ⋙ g₀.toRingedToposSiteHom.u)
  (χ : Φm ≅ SheafOfModules.pushforward.{w} σ) (μ : φ₂r ≅ Φm)
  {χr : SheafOfModules.{w} (𝒪 (𝒯 XD').O) ⥤ SheafOfModules.{w} (𝒪 (𝒯 YA).O)}
  (τ₁ : (pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom) ⋙ (pushforwardModules
      g₀.toRingedToposHom.toRingedToposModulesHom) ≅ χr) (τ₂ : φ₂r ⋙ (pushforwardModules
      (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm fs).toRingedToposHom.toRingedToposModulesHom)
      ≅ χr)
  (Rμ : ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (V : (𝒯 XD).C), ((Sheaf.sectionsFunctor (𝒯 XD).J
      (@Opposite.op (𝒯 XD).C V)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj (Φm.obj N))) →
      ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C V)).obj ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 XD).O)).obj (φ₂r.obj N))))

/-- The comparison `μ` on sections over the site `D`. -/
def SectionsInvApp : Prop :=
  ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (V : (𝒯 XD).C) (x : ((Sheaf.sectionsFunctor (𝒯 XD).J
      (@Opposite.op (𝒯 XD).C V)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj (Φm.obj N)))),
    ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C V)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 XD).O)).map (μ.inv.app N)) x) = Rμ N V x

/-- The value of the left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on sections, after
the three comparisons of pushforwards along morphisms of ringed sites are read as identities, is
the right-hand side of `Stacks.ReindexSquare.LHSSections`. -/
def LHSSectionsTail : Prop :=
  ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C) (x : ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N))))),
    castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁')
      (H₂' := H₂') (g₀ := g₀) N W (castSectionsPushforwardModules (g₀ := g₀) ((pushforwardModules
      (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N) W ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map ((τ₁.inv.app N)))
      ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((τ₂.hom.app N))) (castSectionsInverseToPushforwardModules (e := e) (hm := hm)
      (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W)
      (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj
      N) W x))))))) =
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.map
        (e'.inverse.map (g₀.toRingedToposSiteHom.u.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op
        ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).map (χ.hom.app N)) x)

/-- The left-hand side of `Stacks.ReindexSquare.LHSSectionsTail` has the value `F`. -/
def LHSSectionsTailEq (F : ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C),
    ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N)))) →
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.obj
          (@Opposite.op (𝒯 XD').C (e'.inverse.obj (g₀.toRingedToposSiteHom.u.obj W)))) : Prop :=
  ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C) (x : ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N))))),
    castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁')
      (H₂' := H₂') (g₀ := g₀) N W (castSectionsPushforwardModules (g₀ := g₀) ((pushforwardModules
      (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N) W ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map ((τ₁.inv.app N)))
      ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((τ₂.hom.app N))) (castSectionsInverseToPushforwardModules (e := e) (hm := hm)
      (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W)
      (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj
      N) W x))))))) = F N W x

/-- The value `F` is the right-hand side of `Stacks.ReindexSquare.LHSSectionsTail`. -/
def LHSSectionsTailValue (F : ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C),
    ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N)))) →
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.obj
          (@Opposite.op (𝒯 XD').C (e'.inverse.obj (g₀.toRingedToposSiteHom.u.obj W)))) : Prop :=
  ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C) (x : ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N))))),
    F N W x = ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.map
        (e'.inverse.map (g₀.toRingedToposSiteHom.u.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op
        ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).map (χ.hom.app N)) x)

/-- The components of the inverse of the conjugate of `s`: the restriction map of the
right-hand side of `Stacks.ReindexSquare.LHSSectionsTail`. -/
def conjRestriction (W : (𝒯 YA).C) : e'.inverse.obj (g₀.toRingedToposSiteHom.u.obj W) ⟶
    sbc.obj (e.inverse.obj W) :=
  e'.inverse.map (g₀.toRingedToposSiteHom.u.map (e.counitIso.inv.app W)) ≫
    e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫ e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))

omit hc₅ in
/-- `Stacks.ReindexSquare.LHSSectionsTail` through an intermediate value `F`. -/
theorem lhsSectionsTail_of_eq (F : ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C),
    ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj N)))) →
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.obj
          (@Opposite.op (𝒯 XD').C (e'.inverse.obj (g₀.toRingedToposSiteHom.u.obj W))))
    (hF : LHSSectionsTailEq (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)
        (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀)
        (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) F)
    (hR : LHSSectionsTailValue (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)
        (e' := e') (g₀ := g₀) (s := s) (χ := χ) F) :
    LHSSectionsTail (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (e' := e')
        (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (s := s)
        (χ := χ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) :=
  fun N W x => (hF N W x).trans (hR N W x)

omit hc₅ in
/-- `Stacks.ReindexSquare.LHSSectionsTail` from the value of the left-hand side written through
`Stacks.ReindexSquare.conjRestriction` and a family `Gχ` of maps of sections over the objects of
the site `D` that is `χ` on sections over each object. -/
theorem lhsSectionsTail_of_chart
    (Gχ : ∀ (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (V : (𝒯 XD).C),
      (Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C V)).obj
        ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).obj (Φm.obj N)) →
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.obj (@Opposite.op (𝒯 XD').C (sbc.obj V)))
    (hG : ∀ N V y, (Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C V)).map
        ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).map (χ.hom.app N)) y = Gχ N V y)
    (hF : LHSSectionsTailEq (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)
        (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀)
        (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ)
      (fun N W x => ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.map
        (conjRestriction (e := e) (e' := e') (g₀ := g₀) (s := s) W).op
        (Gχ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe)
            (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x)))) :
    LHSSectionsTail (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (e' := e')
        (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (s := s)
        (χ := χ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) :=
  lhsSectionsTail_of_eq (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (e' := e')
      (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (s := s) (χ := χ)
      (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) _ hF
    (fun N W x => congrArg (fun y => ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.map
        (conjRestriction (e := e) (e' := e') (g₀ := g₀) (s := s) W).op y)
      (hG N (e.inverse.obj W) (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe)
          (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x)).symm)

omit [XD'.J.HasSheafCompose (forget RingCat)]
  [XD'.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [XD'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The first two factors of the left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on
sections: `μ⁻¹` on sections over the site `D`, then the casts of sections. -/
theorem sections_lhs_first_two (hμ : SectionsInvApp (μ := μ) (Rμ := Rμ)) (N : SheafOfModules.{w} (𝒪
    (𝒯 XD').O)) (W : (𝒯 YA).C) (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence
    e φe (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁
    H₂).inverse.obj (Φm.obj N))))) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe)
      (H₁ := H₁) (H₂ := H₂)).inv.app (φ₂r.obj N))) ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op
      (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
      e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.map (μ.inv.app N))) x)) =
      (castSectionsInverseToPushforwardModules (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
      (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁
      := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm :=
      hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x)))) :=
  (congrArg (fun z => ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map ((homGeneralPushforwardInverseIso (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)).inv.app (φ₂r.obj N))) z))
    (sections_inverse_map_castSections (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ :=
      H₂) (Φm.obj N) (φ₂r.obj N) (μ.inv.app N) W x _
      (hμ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ :=
        H₁) (H₂ := H₂) (Φm.obj N) W x)))).trans
    (sections_homGeneralPushforwardInverseIso_inv_app (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁
      := H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe :=
      φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W) (castSectionsInverse (e := e)
      (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x))))

/-- The last three factors of the left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on
sections: `τ₁⁻¹`, then the casts of sections. -/
theorem sections_lhs_last_three (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C) (y : _) :
    ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map ((SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).map
      ((homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ := H₁')
      (H₂ := H₂')).hom.app N))) ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (X := ((pushforwardModules (HomGeneral.mk (X :=
      XD') (Y := YA') e'.inverse hm' fs').toRingedToposHom.toRingedToposModulesHom) ⋙
      (pushforwardModules g₀.toRingedToposHom.toRingedToposModulesHom)).obj N)
      ((pushforwardModulesIsoPushforward (g₀ := g₀)).hom.app ((pushforwardModules (HomGeneral.mk (X
      := XD') (Y := YA') e'.inverse hm' fs').toRingedToposHom.toRingedToposModulesHom).obj N)))
      ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map (τ₁.inv.app N)) y))) =
      castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁')
        (H₂' := H₂') (g₀ := g₀) N W (castSectionsPushforwardModules (g₀ := g₀) ((pushforwardModules
        (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
        fs').toRingedToposHom.toRingedToposModulesHom).obj N) W ((Sheaf.sectionsFunctor (𝒯 YA).J
        (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₁.inv.app N))
        y)) :=
  (congrArg (fun z => ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map ((SheafOfModules.pushforward.{w}
      g₀.toRingedToposSiteHom.fSharpRing).map ((homGeneralPushforwardInverseIso (e := e') (hm :=
      hm') (fs := fs') (φe := φe') (H₁ := H₁') (H₂ := H₂')).hom.app N))) z))
    (sections_pushforwardModulesIsoPushforward_hom_app (e' := e') (hm' := hm') (fs' := fs') (g₀ :=
      g₀) N W ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₁.inv.app N)) y))).trans
    (sections_pushforward_map_homGeneralPushforwardInverseIso_hom_app (e' := e') (hm' := hm') (fs'
      := fs') (H₁' := H₁') (H₂' := H₂') (φe' := φe') (g₀ := g₀) N W _)

/-- The left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on sections, up to its last
factor, when the three comparisons of pushforwards are those of morphisms of ringed sites. -/
theorem sections_lhs_eq_of_homGeneral (hμ : SectionsInvApp (μ := μ) (Rμ := Rμ))
    (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C)
    (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X
      := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj
      N))))) :
    (Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
      YA).O)).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
        e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.map (μ.inv.app N) ≫
        (homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂
        := H₂)).inv.app (φ₂r.obj N) ≫ τ₂.hom.app N ≫ τ₁.inv.app N ≫
        (pushforwardModulesIsoPushforward (g₀ := g₀)).hom.app ((pushforwardModules (HomGeneral.mk
          (X := XD') (Y := YA') e'.inverse hm' fs').toRingedToposHom.toRingedToposModulesHom).obj
          N) ≫
        (SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).map
          ((homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ :=
          H₁') (H₂ := H₂')).hom.app N))) x =
      (castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' :=
        H₁') (H₂' := H₂') (g₀ := g₀) N W (castSectionsPushforwardModules (g₀ := g₀)
        ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
        fs').toRingedToposHom.toRingedToposModulesHom).obj N) W ((Sheaf.sectionsFunctor (𝒯 YA).J
        (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₁.inv.app N))
        ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor
        (𝒪 (𝒯 YA).O)).map (τ₂.hom.app N)) (castSectionsInverseToPushforwardModules (e := e) (hm :=
        hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e :=
        e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N
        (e.inverse.obj W) (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
        (H₂ := H₂) (Φm.obj N) W x)))))))) :=
  sections_comp₆_eq (M₅ := ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom) ⋙ (pushforwardModules
      g₀.toRingedToposHom.toRingedToposModulesHom)).obj N) _ _ _ _ _ _ x
      (castSectionsInverseToPushforwardModules (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
      (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁
      := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm :=
      hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x)))) ((Sheaf.sectionsFunctor (𝒯
      YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₂.hom.app
      N)) (castSectionsInverseToPushforwardModules (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ :=
      H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe := φe)
      (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x)))))
      (castSectionsPushforwardInverse (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' :=
      H₁') (H₂' := H₂') (g₀ := g₀) N W (castSectionsPushforwardModules (g₀ := g₀)
      ((pushforwardModules (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
      fs').toRingedToposHom.toRingedToposModulesHom).obj N) W ((Sheaf.sectionsFunctor (𝒯 YA).J
      (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₁.inv.app N))
      ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪
      (𝒯 YA).O)).map (τ₂.hom.app N)) (castSectionsInverseToPushforwardModules (e := e) (hm := hm)
      (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm
      := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W)
      (castSectionsInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj
      N) W x))))))))
    (sections_lhs_first_two (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) μ Rμ hμ
      N W x) rfl (sections_lhs_last_three (e' := e') (hm' := hm') (fs' := fs') (H₁' := H₁') (H₂' :=
      H₂') (φe' := φe') (g₀ := g₀) (τ₁ := τ₁) N W ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯
      YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 YA).O)).map (τ₂.hom.app N))
      (castSectionsInverseToPushforwardModules (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
      (H₂ := H₂) (φ₂r.obj N) W (castSectionsToInverse (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁
      := H₁) (H₂ := H₂) (φ₂r.obj N) W (Rμ N (e.inverse.obj W) (castSectionsInverse (e := e) (hm :=
      hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (Φm.obj N) W x))))))

/-- The left-hand side of `Stacks.Mates.RightAdjointSquareCompat` on sections when the three
comparisons of pushforwards are those of morphisms of ringed sites. -/
theorem sections_lhs_of_homGeneral (hμ : SectionsInvApp (μ := μ) (Rμ := Rμ))
    (h₇ : LHSSectionsTail (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (e' :=
      e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (s := s) (χ
      := χ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ))
    (N : SheafOfModules.{w} (𝒪 (𝒯 XD').O)) (W : (𝒯 YA).C)
    (x : ((Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).obj ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 YA).O)).obj ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X
      := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.obj (Φm.obj
      N))))) :
    (Sheaf.sectionsFunctor (𝒯 YA).J (@Opposite.op (𝒯 YA).C W)).map ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
      YA).O)).map
      ((SheafOfModules.pushforwardPushforwardEquivalence e φe (HomGeneral.mk (X := XD) (Y := YA)
        e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂).inverse.map (μ.inv.app N) ≫
        (homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂
        := H₂)).inv.app (φ₂r.obj N) ≫ τ₂.hom.app N ≫ τ₁.inv.app N ≫
        (pushforwardModulesIsoPushforward (g₀ := g₀)).hom.app ((pushforwardModules (HomGeneral.mk
          (X := XD') (Y := YA') e'.inverse hm' fs').toRingedToposHom.toRingedToposModulesHom).obj
          N) ≫
        (SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing).map
          ((homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ :=
          H₁') (H₂ := H₂')).hom.app N))) x =
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD').O)).obj N).obj.map
        (e'.inverse.map (g₀.toRingedToposSiteHom.u.map (e.counitIso.inv.app W)) ≫
          e'.inverse.map (s.inv.app (e.inverse.obj W)) ≫
          e'.unitIso.inv.app (sbc.obj (e.inverse.obj W))).op
        ((Sheaf.sectionsFunctor (𝒯 XD).J (@Opposite.op (𝒯 XD).C (e.inverse.obj W))).map
          ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 XD).O)).map (χ.hom.app N)) x) :=
  (sections_lhs_eq_of_homGeneral (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)
      (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (μ :=
      μ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) hμ N W x).trans (h₇ N W x)

/-- `Stacks.ReindexSquare.LHSSections` when the three comparisons of pushforwards are those of
morphisms of ringed sites, from `μ` on sections and the value of the remaining composite. -/
theorem lhsSections_of_homGeneral (hμ : SectionsInvApp (μ := μ) (Rμ := Rμ))
    (h₇ : LHSSectionsTail (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂) (e' :=
      e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀) (s := s) (χ
      := χ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ)) :
    LHSSections (A := (𝒯 YA).C) (D := (𝒯 XD).C) (A' := (𝒯 YA').C) (D' := (𝒯 XD').C) (JA := (𝒯
      YA).J) (JD := (𝒯 XD).J) (JA' := (𝒯 YA').J) (JD' := (𝒯 XD').J)
      (RA := (𝒪 (𝒯 YA).O)) (RD := (𝒪 (𝒯 XD).O)) (RA' := (𝒪 (𝒯 YA').O)) (RD' := (𝒪 (𝒯 XD').O)) (e :=
        e) (e' := e')
      (φe := φe) (ψe := (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm
        fs).toRingedToposSiteHom.fSharpRing) (H₁ := H₁) (H₂ := H₂)
      (φe' := φe') (ψe' := (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
        fs').toRingedToposSiteHom.fSharpRing) (H₁' := H₁') (H₂' := H₂')
      (bc := g₀.toRingedToposSiteHom.u) (ρ := g₀.toRingedToposSiteHom.fSharpRing) s χ μ τ₁ τ₂
        (pushforwardModulesIsoPushforward (g₀ := g₀))
      (homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ := H₁')
        (H₂ := H₂')) (homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁
        := H₁) (H₂ := H₂)) :=
  fun N W x => sections_lhs_of_homGeneral (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂
      := H₂) (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀)
      (s := s) (χ := χ) (μ := μ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) hμ h₇ N W x

/-- `Stacks.Mates.RightAdjointSquareCompat` for the two equivalences of pushforwards of morphisms
of ringed sites `e` and `e'`, the three comparisons of pushforwards along morphisms of ringed
sites, and a square `Sg` of right adjoints satisfying `Stacks.ReindexSquare.SectionsSquareInv`,
from `μ` on sections and the value of the remaining composite. -/
theorem rightAdjointSquareCompat_of_homGeneral
    (Sg : SheafOfModules.pushforward.{w} g₀.toRingedToposSiteHom.fSharpRing ⋙
      SheafOfModules.pushforward.{w} φe ≅ SheafOfModules.pushforward.{w} φe' ⋙ Φm)
    (hSg : SectionsSquareInv s χ Sg)
    (hμ : SectionsInvApp (μ := μ) (Rμ := Rμ))
    (h₇ : LHSSectionsTail (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁) (H₂ := H₂)
      (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀)
      (s := s) (χ := χ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ)) :
    Stacks.Mates.RightAdjointSquareCompat
      (SheafOfModules.pushforwardPushforwardEquivalence e φe
        (HomGeneral.mk (X := XD) (Y := YA) e.inverse hm fs).toRingedToposSiteHom.fSharpRing H₁ H₂)
      (SheafOfModules.pushforwardPushforwardEquivalence e' φe'
        (HomGeneral.mk (X := XD') (Y := YA') e'.inverse hm'
            fs').toRingedToposSiteHom.fSharpRing H₁' H₂')
      μ τ₁ τ₂ (pushforwardModulesIsoPushforward (g₀ := g₀))
      (homGeneralPushforwardInverseIso (e := e') (hm := hm') (fs := fs') (φe := φe') (H₁ := H₁')
        (H₂ := H₂'))
      (homGeneralPushforwardInverseIso (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
        (H₂ := H₂))
      Sg :=
  rightAdjointSquareCompat_of_sections (s := s) (χ := χ) (μ := μ)
    (hSg := hSg)
    (hL := lhsSections_of_homGeneral (e := e) (hm := hm) (fs := fs) (φe := φe) (H₁ := H₁)
      (H₂ := H₂)
      (e' := e') (hm' := hm') (fs' := fs') (φe' := φe') (H₁' := H₁') (H₂' := H₂') (g₀ := g₀)
      (s := s) (χ := χ) (μ := μ) (τ₁ := τ₁) (τ₂ := τ₂) (Rμ := Rμ) hμ h₇)

end HomGeneralSquare

end Stacks.ReindexSquare

namespace AlgebraicGeometry.Space

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The structure sheaf of rings of `yoneda.obj U` at the spelling of the native 04M0
equivalence. -/
noncomputable abbrev representedSiteRing (U : BigFppfOver B S hS) :=
  Stacks.SheafOfModules.Tensor.ringSheaf (AlgebraicGeometry.RingedSite.toRingedTopos
    (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj U))
      (SmallEtale.topology B S hS (yoneda.obj U))
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))).O

/-- The structure sheaf of rings of the scheme underlying `U` at the spelling of the ringed
topos of its small étale site. -/
noncomputable abbrev representedSchemeRing (U : BigFppfOver B S hS) :=
  Stacks.SheafOfModules.Tensor.ringSheaf (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) U.left.obj U.left.property).toRingedTopos.O

/-- Base change of schemes along `g` is continuous, at the ringed-topos spellings. -/
instance isContinuous_representedSchemeBaseChange_toRingedTopos :
    (representedSchemeBaseChange B S hS g).IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).toRingedTopos.J :=
  isContinuous_representedSchemeBaseChange B S hS g

/-- Base change of charts along `φ` is continuous, at the ringed-topos spellings. -/
instance isContinuous_representedSmallBaseChange_toRingedTopos :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).IsContinuous
      (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
          (SmallEtale.topology B S hS (yoneda.obj T))
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
      (AlgebraicGeometry.RingedSite.toRingedTopos
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
          (SmallEtale.topology B S hS (yoneda.obj T'))
          (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).J :=
  isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg

/-- `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` on sections. -/
theorem sectionsSquareInv_representedModulePushforwardSquareIso :
    Stacks.ReindexSquare.SectionsSquareInv.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
      (JA := representedSchemeSmallEtaleTopology B S hS T)
      (JA' := representedSchemeSmallEtaleTopology B S hS T')
      (JD := SmallEtale.topology B S hS (yoneda.obj T))
      (JD' := SmallEtale.topology B S hS (yoneda.obj T'))
      (representedSmallEtaleBaseChangeIso B S hS g hg)
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
      (representedModulePushforwardSquareIso B S hS g hg) :=
  Stacks.ReindexSquare.sectionsSquareInv_of_squareIso
    (JA := representedSchemeSmallEtaleTopology B S hS T)
    (JA' := representedSchemeSmallEtaleTopology B S hS T')
    (JD := SmallEtale.topology B S hS (yoneda.obj T))
    (JD' := SmallEtale.topology B S hS (yoneda.obj T'))
    (representedSmallEtaleBaseChangeIso B S hS g hg)
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (representedStructureMapRing_square B S hS g hg)

/-- `AlgebraicGeometry.Space.representedSitePushforwardSquareIso` on sections. -/
theorem sectionsSquareInv_representedSitePushforwardSquareIso :
    Stacks.ReindexSquare.SectionsSquareInv.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
        (JA := representedSchemeSmallEtaleTopology B S hS T)
      (JA' := representedSchemeSmallEtaleTopology B S hS T')
      (JD := SmallEtale.topology B S hS (yoneda.obj T))
      (JD' := SmallEtale.topology B S hS (yoneda.obj T'))
      (RD := representedSiteRing B S hS T) (RD' := representedSiteRing B S hS T')
      (RA := representedSchemeRing B S hS T) (RA' := representedSchemeRing B S hS T')
      (representedSmallEtaleBaseChangeIso B S hS g hg)
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
      (representedSitePushforwardSquareIso B S hS g hg) :=
  sectionsSquareInv_representedModulePushforwardSquareIso B S hS g hg

/-- A functor to types takes the same value on equal morphisms. -/
private theorem functor_map_apply_congr {C : Type*} [Category C] {F : C ⥤ Type*} {X Y : C}
    {f g : X ⟶ Y} (h : f = g) (x : F.obj X) : F.map f x = F.map g x :=
  congrArg (fun k => F.map k x) h

/-- The inverse comparison of the two direct images along `φ` is the identity on sections. -/
theorem sections_modulePushforwardIso_inv_app_representedSpaceMap
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))
    (V : SmallEtale B S hS (yoneda.obj T))
    (x : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T)) (op V)).obj
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O)).obj
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj N))) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T)) (op V)).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O)).map
      ((modulePushforwardIso B S hS (representedSpaceMap B S hS g)).inv.app N)) x = x :=
  functor_map_apply_congr
    (moduleSheafFunctor_map_modulePushforwardIso_inv_app (representedSpaceMap B S hS g) N) x

/-- The structure sheaf of rings of `yoneda.obj U` at the spelling of its small étale ringed
topos. -/
noncomputable abbrev representedToposRing (U : BigFppfOver B S hS) :=
  Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The inverse comparison of the two direct images along the reindexing of `U` is the
identity on sections. -/
theorem sections_representedReindexSiteHom_pushforwardModulesToposIsoGeneral_inv_app
    (U : BigFppfOver B S hS) (N : SheafOfModules.{u} (representedToposRing B S hS U))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (x : (Sheaf.sectionsFunctor _ W).obj
        ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS U)).obj
      ((representedReindexSitePushforwardEquivalence B S hS U).inverse.obj N))) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS U)).map
      ((representedReindexSiteHom B S hS U).pushforwardModulesToposIsoGeneral.inv.app N)) x = x :=
  AlgebraicGeometry.RingedSite.HomGeneral.val_app_pushforwardModulesToposIsoGeneral_inv_app
    (representedReindexSiteHom B S hS U) N W x

/-- The first two factors of the space route of the square are the identity on sections. -/
theorem sections_representedSquare_reindexInverse_modulePushforwardIso
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (x : (Sheaf.sectionsFunctor _ W).obj
        ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).obj
      ((representedReindexSitePushforwardEquivalence B S hS T).inverse.obj
      ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj N)))) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).map
      ((representedReindexSiteHom B S hS T).pushforwardModulesToposIsoGeneral.inv.app
        ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS g))).obj N)))
      ((Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor
          (representedSchemeRing B S hS T)).map
        ((representedReindexSitePushforwardEquivalence B S hS T).inverse.map
          ((modulePushforwardIso B S hS (representedSpaceMap B S hS g)).inv.app N))) x) = x :=
  (sections_representedReindexSiteHom_pushforwardModulesToposIsoGeneral_inv_app B S hS T
      ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS
      (representedSpaceMap B S hS g))).obj N) W
    ((Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor
        (representedSchemeRing B S hS T)).map
        ((representedReindexSitePushforwardEquivalence B S hS T).inverse.map
          ((modulePushforwardIso B S hS (representedSpaceMap B S hS g)).inv.app N))) x)).trans
    (sections_modulePushforwardIso_inv_app_representedSpaceMap B S hS g N
        ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop) x)

/-- The chart comparison on sections is `AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
theorem sections_chartComparison_eq_modulePushforwardChartIso
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (V : SmallEtale B S hS (yoneda.obj T))
    (x : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T)) (op V)).obj
      ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T)).obj
        ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj N))) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T)) (op V)).map
          ((chartComparison B S hS (representedSpaceMap B S hS g) hg).hom.app
            ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T')).obj N)) x =
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T)) (op V)).map
          ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T)).map
            ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app N)) x :=
  functor_map_apply_congr (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS
    (representedSpaceMap B S hS g) hg N).symm x

/-- The comparison of direct images along the scheme route is the identity on sections. -/
theorem sections_representedSquare_schemeRoute_inv_app
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (x) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).map
          ((pushforwardModulesCompIso (representedReindexHom B S hS T')
            (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
            (fSharpSetComp_representedSquareHom B S hS g)).inv.app N)) x = x :=
  functor_map_apply_congr
    (moduleSheafFunctor_map_pushforwardModulesCompInv (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) N (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)) x

end AlgebraicGeometry.Space

namespace Stacks.ReindexSquare

open CategoryTheory Opposite

universe w

section DirectImage

variable {C D E C' : Type*} [Category C] [Category D] [Category E] [Category C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {J' : GrothendieckTopology C'} {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ C'} {G' : C' ⥤ E}
  [F.IsContinuous J K] [G.IsContinuous K L] [F'.IsContinuous J J'] [G'.IsContinuous J' L]
  [(F' ⋙ G').IsContinuous J L]

/-- On sections, a comparison of direct images of sheaves of sets built as the direct image of
the comparison `R` followed by the comparison `r` of the two composite site functors is
restriction along `r⁻¹` of `R` on sections. -/
theorem sections_directImageSquare_hom_app (r : F ⋙ G ≅ F' ⋙ G')
    {Φ : Sheaf L (Type w) ⥤ Sheaf K (Type w)} (R : Φ ≅ G.sheafPushforwardContinuous (Type w) K L)
    (P : Sheaf L (Type w)) (W : C)
    (z : (Sheaf.sectionsFunctor J (op W)).obj
      ((F.sheafPushforwardContinuous (Type w) J K).obj (Φ.obj P))) :
    (Sheaf.sectionsFunctor J (op W)).map
      ((Functor.isoWhiskerRight R (F.sheafPushforwardContinuous (Type w) J K) ≪≫
        Functor.sheafPushforwardContinuousComp' r (Type w) J K L ≪≫
        (Functor.sheafPushforwardContinuousComp F' G' (Type w) J J' L).symm).hom.app P) z =
      P.obj.map (r.inv.app W).op
        ((Sheaf.sectionsFunctor K (op (F.obj W))).map (R.hom.app P) z) :=
  rfl
end DirectImage

end Stacks.ReindexSquare

namespace AlgebraicGeometry.RingedSite

open CategoryTheory Opposite

universe w uX vX uY vY

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : AlgebraicGeometry.RingedTopos}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (h : HomGeneral X Y) (f : AlgebraicGeometry.RingedToposSiteHom (toRingedTopos Y) Z)
/-- The direct image along a morphism of ringed topoi of the comparison of the two pushforwards
along a morphism of ringed sites is the identity on sections. -/
theorem HomGeneral.sections_pushforwardTopos_map_pushforwardModulesToposIsoGeneral_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (W : Z.Cᵒᵖ)
    (y : (Sheaf.sectionsFunctor Z.J W).obj
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        (f.pushforwardTopos.obj ((Stacks.Sheaves.RingedToposModules.pushforwardModules
          h.toRingedToposHom.toRingedToposModulesHom).obj N)))) :
    (Sheaf.sectionsFunctor Z.J W).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (f.pushforwardTopos.map (h.pushforwardModulesToposIsoGeneral.hom.app N))) y = y :=
  h.val_app_pushforwardModulesToposIsoGeneral_hom_app N (op (f.u.obj W.unop)) y

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- On sections over `W`, `AlgebraicGeometry.Space.representedSquareDirectImageIso` is the chart
comparison over `e_T⁻¹ W` followed by restriction along the inverse of
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`, for every sheaf of sets. -/
theorem sections_representedSquareDirectImageIso_hom_app (P : Sheaf (smallEtaleRingedTopos B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).J (Type u))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (z) :
    (Sheaf.sectionsFunctor (representedSchemeSmallEtaleTopology B S hS T) W).map
      ((representedSquareDirectImageIso B S hS g hg).hom.app P) z =
      P.obj.map ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W.unop).op
        ((Sheaf.sectionsFunctor _
          (op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).map
          ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
            chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app P) z) :=
  Stacks.ReindexSquare.sections_directImageSquare_hom_app
    (representedEquivInverseBaseChangeIso B S hS g hg)
    (smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
      chartRanIso B S hS (representedSpaceMap B S hS g) hg) P W.unop z

/-- The comparison of direct images of modules of the space route round the square of `g`, on
sections: the chart comparison followed by restriction along the inverse of
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`. -/
theorem sections_representedSquareDirectImageIso_compIso_hom_app
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (x : (Sheaf.sectionsFunctor _ W).obj
        ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).obj
      ((pushforwardModules (representedReindexHom B S hS T)).obj
        ((pushforwardModules (smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS g))).obj N)))) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).map
      ((pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)).hom.app N)) x =
      ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T')).obj N).obj.map
        ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W.unop).op
        ((Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T))
          (op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).map
          ((chartComparison B S hS (representedSpaceMap B S hS g) hg).hom.app
            ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T')).obj N)) x) :=
  (functor_map_apply_congr
    (moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg) N) x).trans
  (sections_representedSquareDirectImageIso_hom_app B S hS g hg
      ((Sheaf.moduleSheafFunctor (representedToposRing B S hS T')).obj N) W x)

/-- The functor of the morphism of ringed sites of Stacks 070R (2) for the morphism underlying
`g` is continuous, at the ringed-topos spellings. -/
instance isContinuous_smallEtaleRingedSiteHom_u_toRingedTopos :
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).toRingedToposSiteHom.u.IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).toRingedTopos.J :=
  (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).toRingedToposSiteHom.isContinuous

/-- The comparison of the two direct images along base change of schemes is the identity on
sections. -/
theorem sections_smallEtaleRingedSiteHom_pushforwardModulesToposIsoGeneral_hom_app
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (x) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).map
        ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
            g.left).pushforwardModulesToposIsoGeneral.hom.app
          ((pushforwardModules (representedReindexHom B S hS T')).obj N))) x = x :=
  AlgebraicGeometry.RingedSite.HomGeneral.sections_pushforwardModulesToposIsoGeneral_hom_app
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left)
    ((pushforwardModules (representedReindexHom B S hS T')).obj N) W x

/-- The direct image along base change of schemes of the comparison of the two direct images
along the reindexing of `T'` is the identity on sections. -/
theorem sections_pushforwardTopos_map_representedReindexSiteHom_hom_app
    (N : SheafOfModules.{u} (representedToposRing B S hS T'))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (x) :
    (Sheaf.sectionsFunctor _ W).map ((Sheaf.moduleSheafFunctor (representedSchemeRing B S hS T)).map
      ((smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pushforwardTopos.map
        ((representedReindexSiteHom B S hS T').pushforwardModulesToposIsoGeneral.hom.app N))) x =
      x :=
  RingedSite.HomGeneral.sections_pushforwardTopos_map_pushforwardModulesToposIsoGeneral_hom_app
    (representedReindexSiteHom B S hS T')
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).toRingedToposSiteHom N W x


section HomGeneralSquare

/-! The inputs of `Stacks.ReindexSquare.rightAdjointSquareCompat_of_homGeneral` for the square of
`g`, at the uniform ringed-topos spelling of that section. -/

local notation "𝒯" => AlgebraicGeometry.RingedSite.toRingedTopos

local notation "𝒪" => Stacks.SheafOfModules.Tensor.ringSheaf

/-- Sections over a chart of the direct image of modules along `φ` read as sections of the direct
image along the morphism of small étale ringed topoi of `φ`. -/
def representedSpaceMapSectionsCast (N : SheafOfModules.{u} (𝒪 (𝒯
    (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
    (SmallEtale.topology B S hS (yoneda.obj T')) (structureSheaf B S hS (yoneda.obj T')
    (isAlgebraicSpace_yoneda B S hS T')))).O)) (V : (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u,
    u} (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C)
    (x : (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S
      hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J (@Opposite.op (𝒯
      (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)))).C V)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
      (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)))).O)).obj ((modulePushforward B S hS (representedSpaceMap
      B S hS g)).obj N))) :
    (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS
      (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J (@Opposite.op (𝒯
      (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)))).C V)).obj ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
      (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)))).O)).obj ((pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))).obj N)) := x

/-- The inverse comparison of the two direct images of modules along `φ` is the cast of sections
`AlgebraicGeometry.Space.representedSpaceMapSectionsCast` on sections over every chart. -/
theorem sectionsInvApp_modulePushforwardIso : Stacks.ReindexSquare.SectionsInvApp (XD :=
    (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T)) (structureSheaf B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)))) (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))) (μ :=
    modulePushforwardIso B S hS (representedSpaceMap B S hS g)) (Rμ :=
    representedSpaceMapSectionsCast B S hS g) :=
  fun N _ x => functor_map_apply_congr
    (moduleSheafFunctor_map_modulePushforwardIso_inv_app (representedSpaceMap B S hS g) N) x

/-- The comparison of direct images of modules along the space route round the square of `g` is
`AlgebraicGeometry.Space.representedSquareDirectImageIso` on underlying sheaves of sets, at the
ringed-topos spelling. -/
theorem moduleSheafFunctor_map_representedSquareSpaceRoute_hom_app
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)) :
    (Sheaf.moduleSheafFunctor (𝒪 (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).O)).map
    ((pushforwardModulesCompIso (smallEtaleRingedToposModulesHom B S hS
    (representedSpaceMap B S hS g)) (representedReindexHom B S hS T) (representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)).hom.app N) =
    (representedSquareDirectImageIso B S hS g hg).hom.app
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N) :=
  moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg) N

/-- `AlgebraicGeometry.Space.sections_representedSquareDirectImageIso_hom_app` at the ringed-topos
spelling, for the underlying sheaf of sets of a module. -/
theorem sections_representedSquareDirectImageIso_hom_app_toRingedTopos
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) (x) :
    (Sheaf.sectionsFunctor (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).J
    (@Opposite.op (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C W)).map
    ((representedSquareDirectImageIso B S hS g hg).hom.app
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N)) x =
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
        N).obj.map ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W).op
        ((Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
        (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C
        ((representedSmallEtaleEquivalence B S hS T).inverse.obj W))).map
        ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
        chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
        (SmallEtale.topology B S hS (yoneda.obj T')) (structureSheaf B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N)) x) :=
  Stacks.ReindexSquare.sections_directImageSquare_hom_app
      (representedEquivInverseBaseChangeIso B S hS g hg)
      (smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
      chartRanIso B S hS (representedSpaceMap B S hS g) hg)
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
      (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N) W x

/-- The chart comparison on sections is `AlgebraicGeometry.Space.modulePushforwardChartIso`, at the
ringed-topos spelling. -/
theorem sections_chartRanIso_hom_app_eq_modulePushforwardChartIso
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) (x) :
    (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
    (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C
    ((representedSmallEtaleEquivalence B S hS T).inverse.obj W))).map
    ((smallEtaleDirectImageRanIso B S hS (schemeSpaceMap g) ≪≫
    chartRanIso B S hS (schemeSpaceMap g) hg).hom.app
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N)) x =
    (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
    (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C
    ((representedSmallEtaleEquivalence B S hS T).inverse.obj W))).map
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).O)).map
    ((modulePushforwardChartIso B S hS (schemeSpaceMap g) hg).hom.app N)) x :=
  functor_map_apply_congr
    (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS (schemeSpaceMap g) hg N).symm x

/-- The components of the inverse of
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`, at the ringed-topos spelling. -/
theorem representedEquivInverseBaseChangeIso_inv_app_toRingedTopos
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) :
    (representedEquivInverseBaseChangeIso B S hS g hg).inv.app W =
    ((representedSmallEtaleEquivalence B S hS T').inverse.map
    ((smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left).toRingedToposSiteHom.u.map
    ((representedSmallEtaleEquivalence B S hS T).counitIso.inv.app W)) ≫
    (representedSmallEtaleEquivalence B S hS T').inverse.map
    ((representedSmallEtaleBaseChangeIso B S hS g hg).inv.app
    ((representedSmallEtaleEquivalence B S hS T).inverse.obj W)) ≫
    (representedSmallEtaleEquivalence B S hS T').unitIso.inv.app
    ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj
    ((representedSmallEtaleEquivalence B S hS T).inverse.obj W))) :=
  Stacks.ReindexSquare.conj_inv_app (representedSmallEtaleEquivalence B S hS T)
      (representedSmallEtaleEquivalence B S hS T') (representedSchemeBaseChange B S hS g)
      (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
      (representedSmallEtaleBaseChangeIso B S hS g hg) W

/-- The comparison of direct images of modules along the space route round the square of `g`, on
sections: the chart comparison followed by restriction along the inverse of
`AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`. -/
theorem sections_representedSquareSpaceRoute_hom_app_eq_directImage
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) (a) :
    (Sheaf.sectionsFunctor (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).J
    (@Opposite.op (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C W)).map
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).O)).map
    ((pushforwardModulesCompIso (smallEtaleRingedToposModulesHom B S hS
    (representedSpaceMap B S hS g)) (representedReindexHom B S hS T) (representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)).hom.app N)) a =
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
        N).obj.map ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W).op
        ((Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
        (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C
        ((representedSmallEtaleEquivalence B S hS T).inverse.obj W))).map
        ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
        chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app
        ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
        (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
        (SmallEtale.topology B S hS (yoneda.obj T')) (structureSheaf B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N)) a) :=
  (functor_map_apply_congr
    (moduleSheafFunctor_map_representedSquareSpaceRoute_hom_app B S hS g hg N) a).trans
      (sections_representedSquareDirectImageIso_hom_app_toRingedTopos B S hS g hg N W a)

/-- The chart comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` on sections over an
object `V` of the small étale site of `yoneda.obj T`, read as sections of the module over
`yoneda.obj T'` over the base change of `V`. -/
def representedChartSectionsMap (N : SheafOfModules.{u}
    (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
    (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (V : (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C)
    (y : (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
    (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C V)).obj
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).O)).obj
    ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj N))) :
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
        N).obj.obj (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).C
        ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)) :=
  (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
      (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
      (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
      (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C V)).map
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
      (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).O)).map
      ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app N)) y

/-- The comparison of direct images of sheaves of sets of the chart, on sections over every
object, is `AlgebraicGeometry.Space.representedChartSectionsMap`. -/
theorem sections_chartRanIso_hom_app_eq_representedChartSectionsMap
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (V : (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C) (y) :
    (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
    (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C V)).map
    ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS g) ≪≫
    chartRanIso B S hS (representedSpaceMap B S hS g) hg).hom.app
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj N)) y =
    (representedChartSectionsMap B S hS g hg) N V y :=
  functor_map_apply_congr (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS
    (representedSpaceMap B S hS g) hg N).symm y

/-- The components of the inverse of `AlgebraicGeometry.Space.representedEquivInverseBaseChangeIso`
are the restriction maps `Stacks.ReindexSquare.conjRestriction`. -/
theorem representedEquivInverseBaseChangeIso_inv_app_eq_conjRestriction
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) :
    (representedEquivInverseBaseChangeIso B S hS g hg).inv.app W =
    (Stacks.ReindexSquare.conjRestriction
    (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
    (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property))
    (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
    (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
    (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T'.left.obj T'.left.property))
    (e := (representedSmallEtaleEquivalence B S hS T))
    (e' := (representedSmallEtaleEquivalence B S hS T'))
    (g₀ := (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left))
    (sbc := (smallBaseChange B S hS (representedSpaceMap B S hS g)
    hg))  (s := (representedSmallEtaleBaseChangeIso B S hS g hg)) W) :=
  representedEquivInverseBaseChangeIso_inv_app_toRingedTopos B S hS g hg W

/-- The comparison of direct images of modules along the space route round the square of `g`, on
sections over `W`: the chart comparison over `e_T⁻¹ W` followed by restriction along
`Stacks.ReindexSquare.conjRestriction`. -/
theorem sections_representedSquareSpaceRoute_hom_app_eq_conjRestriction
    (N : SheafOfModules.{u} (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O))
    (W : (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C) (a) :
    (Sheaf.sectionsFunctor (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).J
    (@Opposite.op (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).C W)).map
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property)).O)).map
    ((pushforwardModulesCompIso (smallEtaleRingedToposModulesHom B S hS
    (representedSpaceMap B S hS g)) (representedReindexHom B S hS T) (representedSquareHom B S hS g)
    (representedSquareDirectImageIso B S hS g hg)
    (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)).hom.app N)) a =
    ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
        (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
        N).obj.map (Stacks.ReindexSquare.conjRestriction
        (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
        (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
        (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
        (associatedBigEtaleSite B) T.left.obj T.left.property))
        (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
        (SmallEtale.topology B S hS (yoneda.obj T'))
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
        (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
        (associatedBigEtaleSite B) T'.left.obj T'.left.property))
        (e := (representedSmallEtaleEquivalence B S hS T))
        (e' := (representedSmallEtaleEquivalence B S hS T'))
        (g₀ := (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left))
        (sbc := (smallBaseChange B S hS (representedSpaceMap B S hS g)
        hg))  (s := (representedSmallEtaleBaseChangeIso B S hS g hg)) W).op
        ((representedChartSectionsMap B S hS g hg) N
        ((representedSmallEtaleEquivalence B S hS T).inverse.obj W) a) := by
  refine (sections_representedSquareSpaceRoute_hom_app_eq_directImage B S hS g hg N W a).trans ?_
  refine (congrArg (fun z => ((Sheaf.moduleSheafFunctor
      (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
      (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
      N).obj.map ((representedEquivInverseBaseChangeIso B S hS g hg).inv.app W).op z)
      (sections_chartRanIso_hom_app_eq_representedChartSectionsMap B S hS g hg N
      ((representedSmallEtaleEquivalence B S hS T).inverse.obj W) a)).trans ?_
  exact congrArg (fun (k : type_of% (Stacks.ReindexSquare.conjRestriction
      (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
      (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T.left.obj T.left.property))
      (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
      (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
      (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T'.left.obj T'.left.property))
      (e := (representedSmallEtaleEquivalence B S hS T))
      (e' := (representedSmallEtaleEquivalence B S hS T'))
      (g₀ := (smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left))
      (sbc := (smallBaseChange B S hS (representedSpaceMap B S hS g)
      hg))  (s := (representedSmallEtaleBaseChangeIso B S hS g hg)) W)) =>
      ((Sheaf.moduleSheafFunctor (𝒪 (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
      (SmallEtale B S hS (yoneda.obj T')) (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))).O)).obj
      N).obj.map k.op ((representedChartSectionsMap B S hS g hg) N
      ((representedSmallEtaleEquivalence B S hS T).inverse.obj W) a))
      (representedEquivInverseBaseChangeIso_inv_app_eq_conjRestriction B S hS g hg W)

/-- `AlgebraicGeometry.Space.modulePushforwardChartIso` on sections over every object is
`AlgebraicGeometry.Space.representedChartSectionsMap`. -/
theorem sections_modulePushforwardChartIso_hom_app_eq_representedChartSectionsMap : ∀ N V y,
    (Sheaf.sectionsFunctor (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).J
    (@Opposite.op (𝒯 (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u}
    (SmallEtale B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).C V)).map
        ((Sheaf.moduleSheafFunctor (𝒪 (𝒯
            (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
            (SmallEtale.topology B S hS (yoneda.obj T))
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))).O)).map
            ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app N)) y =
            (representedChartSectionsMap B S hS g hg) N V y :=
  fun _ _ _ => rfl

/-- `Stacks.ReindexSquare.LHSSectionsTail` for the square of `g`. -/
def RepresentedLHSSectionsTail : Prop :=
    Stacks.ReindexSquare.LHSSectionsTail
    (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
    (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property))
    (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
    (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
    (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T'.left.obj T'.left.property))
    (e := representedSmallEtaleEquivalence B S hS T)
    (hc₁ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T)
    (hc₂ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T)
    (hm := (representedReindexSiteHom B S hS T).isMorphismOfSites)
    (fs := (representedReindexSiteHom B S hS T).fsharp)
    (φe := representedReindexRingHom B S hS T)
    (H₁ := representedReindexRing_counit B S hS T) (H₂ := representedReindexRing_unit B S hS T)
    (e' := representedSmallEtaleEquivalence B S hS T')
    (hc₃ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T')
    (hc₄ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T')
    (hm' := (representedReindexSiteHom B S hS T').isMorphismOfSites)
    (fs' := (representedReindexSiteHom B S hS T').fsharp)
    (φe' := representedReindexRingHom B S hS T')
    (H₁' := representedReindexRing_counit B S hS T') (H₂' := representedReindexRing_unit B S hS T')
    (g₀ := smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left)
    (hc₆ := isContinuous_representedSmallBaseChange_toRingedTopos B S hS g hg)
    (s := representedSmallEtaleBaseChangeIso B S hS g hg)
    (χ := modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (τ₁ := (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g) : _))
    (τ₂ := (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg) : _))
            (Rμ := representedSpaceMapSectionsCast B S hS g)

/-- The value of the left-hand side of the identity of comparisons of direct images round the
square of `g` on sections, once the comparisons along morphisms of ringed sites are read as
identities. -/
theorem representedLHSSectionsTail : RepresentedLHSSectionsTail B S hS g hg := by
  refine Stacks.ReindexSquare.lhsSectionsTail_of_chart
      (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
      (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T.left.obj T.left.property))
      (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
      (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
      (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T'.left.obj T'.left.property))
    (e := representedSmallEtaleEquivalence B S hS T)
    (hc₁ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T)
    (hc₂ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T)
    (hm := (representedReindexSiteHom B S hS T).isMorphismOfSites)
    (fs := (representedReindexSiteHom B S hS T).fsharp)
    (φe := representedReindexRingHom B S hS T)
    (H₁ := representedReindexRing_counit B S hS T) (H₂ := representedReindexRing_unit B S hS T)
    (e' := representedSmallEtaleEquivalence B S hS T')
    (hc₃ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T')
    (hc₄ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T')
    (hm' := (representedReindexSiteHom B S hS T').isMorphismOfSites)
    (fs' := (representedReindexSiteHom B S hS T').fsharp)
    (φe' := representedReindexRingHom B S hS T')
    (H₁' := representedReindexRing_counit B S hS T') (H₂' := representedReindexRing_unit B S hS T')
    (g₀ := smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left)
    (hc₆ := isContinuous_representedSmallBaseChange_toRingedTopos B S hS g hg)
    (s := representedSmallEtaleBaseChangeIso B S hS g hg)
    (χ := modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (τ₁ := _) (τ₂ := _) (Rμ := representedSpaceMapSectionsCast B S hS g) (Gχ := ?Gχ) (hG := ?hG)
    (hF := ?hF)
  case Gχ => exact (representedChartSectionsMap B S hS g hg)
  case hG =>
    exact sections_modulePushforwardChartIso_hom_app_eq_representedChartSectionsMap B S hS g hg
  case hF =>
    intro N W x
    refine (Stacks.Sheaves.RingedToposModules.sections_pushforwardModulesCompIso_comp_inv_app
        (representedSchemeBaseChangeHom B S hS g) (representedReindexHom B S hS T')
        (fSharpSetComp_representedSquareHom B S hS g) N
        (@Opposite.op (𝒯 (_root_.AlgebraicGeometry.smallEtaleRingedSite
        (associatedBigEtaleSite B) T.left.obj T.left.property)).C W) _).trans ?_
    exact sections_representedSquareSpaceRoute_hom_app_eq_conjRestriction B S hS g hg N W _

/-- `Stacks.ReindexSquare.rightAdjointSquareCompat_of_homGeneral` for the square of `g`, as a
proposition. -/
def RepresentedRightAdjointCompatGeneral : Prop :=
    type_of% (Stacks.ReindexSquare.rightAdjointSquareCompat_of_homGeneral
    (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
    (SmallEtale.topology B S hS (yoneda.obj T))
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
    (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property))
    (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
    (SmallEtale.topology B S hS (yoneda.obj T'))
    (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
    (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T'.left.obj T'.left.property))
    (e := representedSmallEtaleEquivalence B S hS T)
    (hc₁ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T)
    (hc₂ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T)
    (hm := (representedReindexSiteHom B S hS T).isMorphismOfSites)
    (fs := (representedReindexSiteHom B S hS T).fsharp)
    (φe := representedReindexRingHom B S hS T)
    (H₁ := representedReindexRing_counit B S hS T) (H₂ := representedReindexRing_unit B S hS T)
    (e' := representedSmallEtaleEquivalence B S hS T')
    (hc₃ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T')
    (hc₄ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T')
    (hm' := (representedReindexSiteHom B S hS T').isMorphismOfSites)
    (fs' := (representedReindexSiteHom B S hS T').fsharp)
    (φe' := representedReindexRingHom B S hS T')
    (H₁' := representedReindexRing_counit B S hS T') (H₂' := representedReindexRing_unit B S hS T')
    (g₀ := smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left)
    (hc₅ := isContinuous_smallEtaleRingedSiteHom_u_toRingedTopos B S hS g)
    (hc₆ := isContinuous_representedSmallBaseChange_toRingedTopos B S hS g hg)
    (s := representedSmallEtaleBaseChangeIso B S hS g hg)
    (χ := modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (μ := modulePushforwardIso B S hS (representedSpaceMap B S hS g))
    (τ₁ := (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS g) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g) : _))
    (τ₂ := (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg) : _))
            (Rμ := representedSpaceMapSectionsCast B S hS g)
            (Sg := representedSitePushforwardSquareIso B S hS g hg)
            (hSg := sectionsSquareInv_representedSitePushforwardSquareIso B S hS g hg)
            (sectionsInvApp_modulePushforwardIso B S hS g) (representedLHSSectionsTail B S hS g hg))

/-- The identity of comparisons of direct images round the square of `g`, at the spelling of
`Stacks.ReindexSquare.rightAdjointSquareCompat_of_homGeneral`. -/
theorem representedRightAdjointCompatGeneral :
    RepresentedRightAdjointCompatGeneral B S hS g hg := by
  refine Stacks.ReindexSquare.rightAdjointSquareCompat_of_homGeneral
      (XD := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T))
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))))
      (YA := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T.left.obj T.left.property))
      (XD' := (AlgebraicGeometry.RingedSite.mk.{u + 1, u, u} (SmallEtale B S hS (yoneda.obj T'))
      (SmallEtale.topology B S hS (yoneda.obj T'))
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))))
      (YA' := (_root_.AlgebraicGeometry.smallEtaleRingedSite
      (associatedBigEtaleSite B) T'.left.obj T'.left.property))
    (e := representedSmallEtaleEquivalence B S hS T)
    (hc₁ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T)
    (hc₂ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T)
    (hm := (representedReindexSiteHom B S hS T).isMorphismOfSites)
    (fs := (representedReindexSiteHom B S hS T).fsharp)
    (φe := representedReindexRingHom B S hS T)
    (H₁ := representedReindexRing_counit B S hS T) (H₂ := representedReindexRing_unit B S hS T)
    (e' := representedSmallEtaleEquivalence B S hS T')
    (hc₃ := isContinuous_representedSmallEtaleEquivalence_functor_toRingedTopos B S hS T')
    (hc₄ := isContinuous_representedSmallEtaleEquivalence_inverse_toRingedTopos B S hS T')
    (hm' := (representedReindexSiteHom B S hS T').isMorphismOfSites)
    (fs' := (representedReindexSiteHom B S hS T').fsharp)
    (φe' := representedReindexRingHom B S hS T')
    (H₁' := representedReindexRing_counit B S hS T') (H₂' := representedReindexRing_unit B S hS T')
    (g₀ := smallEtaleRingedSiteHom (associatedBigEtaleSite B) g.left)
    (hc₅ := isContinuous_smallEtaleRingedSiteHom_u_toRingedTopos B S hS g)
    (hc₆ := isContinuous_representedSmallBaseChange_toRingedTopos B S hS g hg)
    (s := representedSmallEtaleBaseChangeIso B S hS g hg)
    (χ := modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (μ := modulePushforwardIso B S hS (representedSpaceMap B S hS g))
    (τ₁ := _) (τ₂ := _) (Rμ := representedSpaceMapSectionsCast B S hS g)
        (Sg := representedSitePushforwardSquareIso B S hS g hg)
        (hSg := ?hSg) (hμ := ?hμ) (h₇ := ?h₇)
  case hSg => exact sectionsSquareInv_representedSitePushforwardSquareIso B S hS g hg
  case hμ => exact sectionsInvApp_modulePushforwardIso B S hS g
  case h₇ => exact representedLHSSectionsTail B S hS g hg

/-- `AlgebraicGeometry.Space.RepresentedSquarePushforwardRightAdjointCompat`: the identity of
comparisons of direct images round the square of `g` at the native spelling. -/
theorem representedSquarePushforwardRightAdjointCompat :
    RepresentedSquarePushforwardRightAdjointCompat B S hS g hg :=
  Stacks.Mates.rightAdjointSquareCompat_of_heq
      (representedRightAdjointCompatGeneral B S hS g hg) rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **The identity of comparisons of direct images round the square of a represented morphism.**
`AlgebraicGeometry.Space.RepresentedSquareRightAdjointCompat` holds for every morphism `g` of the
big fppf site over `S` whose image under the Yoneda embedding is relatively representable. -/
theorem representedSquareRightAdjointCompat : RepresentedSquareRightAdjointCompat B S hS g hg :=
  representedSquareRightAdjointCompat_of_pushforward B S hS g hg
      (representedSquarePushforwardRightAdjointCompat B S hS g hg)

end HomGeneralSquare

/-- `AlgebraicGeometry.Space.representedModulePullbackIso` with the categories of modules and the
pullbacks spelled as those of the native comparisons of Stacks 04M0
(`AlgebraicGeometry.Space.representedReindexEquivalence`) and of the morphisms of ringed sites. -/
def representedSiteModulePullbackIso : ((smallEtaleRingedToposModulesHom B S hS
    (representedSpaceMap B S hS g)).pullbackModules ⋙
    (representedReindexEquivalence B S hS T').inverse ≅
    (representedReindexEquivalence B S hS T).inverse ⋙ (smallEtaleRingedSiteHom
    (associatedBigEtaleSite B) g.left).toRingedToposSiteHom.pullbackToposGeneral) :=
  representedModulePullbackIso B S hS g hg

/-- The components of the comparison of the two factorizations of the square of `g` are those of
the inverse mate of `AlgebraicGeometry.Space.representedModulePullbackIso`. -/
theorem representedSquareModulePullbackIso_hom_app_eq_mateEquiv
    (M : (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (_root_.AlgebraicGeometry.smallEtaleRingedSite
    (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O))) :
    (representedSquareModulePullbackIso B S hS g hg).hom.app M =
        ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
        (representedReindexEquivalence B S hS T').toAdjunction).symm
        (representedSiteModulePullbackIso B S hS g hg).inv).app M :=
  (representedSquareModulePullbackIso_hom_app_of_rightAdjointCompat B S hS g hg
      (representedSquareRightAdjointCompat B S hS g hg) M).trans
    (Stacks.Mates.app_eq_of_mateEquiv_eq (representedReindexEquivalence B S hS T)
      (representedReindexEquivalence B S hS T') _ (representedSiteModulePullbackIso B S hS g hg)
      (Equiv.apply_symm_apply _ _) M).symm

/-- The comparison of the two factorizations of the square of `g` is the inverse mate of
`AlgebraicGeometry.Space.representedModulePullbackIso`. -/
theorem representedSquareModulePullbackIso_hom_eq :
    (representedSquareModulePullbackIso B S hS g hg).hom =
        ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
        (representedReindexEquivalence B S hS T').toAdjunction).symm
        (representedSiteModulePullbackIso B S hS g hg).inv) :=
  NatTrans.ext (funext fun M =>
      representedSquareModulePullbackIso_hom_app_eq_mateEquiv B S hS g hg M)

/-- Stacks 03EL round the square of `g`, with the comparison of the two factorizations written
as the inverse mate of `AlgebraicGeometry.Space.representedModulePullbackIso`. -/
theorem representedSquare_pullbackTensorIsoTransport_mateEquiv
    (M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    type_of%
      (Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq
        (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
        (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS g)
        (representedSquareDirectImageIso B S hS g hg)
        (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
        (representedReindexPullbackIso B S hS T')
        (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
        (representedReindexPullbackIso B S hS T)
        ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
            (representedReindexEquivalence B S hS T').toAdjunction).symm
            (representedSiteModulePullbackIso B S hS g hg).inv)
        (representedSquareModulePullbackIso_hom_eq B S hS g hg) M N) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq
      (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
      (representedReindexPullbackIso B S hS T')
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS T)
      ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
          (representedReindexEquivalence B S hS T').toAdjunction).symm
          (representedSiteModulePullbackIso B S hS g hg).inv)
      (representedSquareModulePullbackIso_hom_eq B S hS g hg) M N

end AlgebraicGeometry.Space

end
