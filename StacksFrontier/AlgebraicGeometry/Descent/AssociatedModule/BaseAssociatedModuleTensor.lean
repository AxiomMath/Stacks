module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# `(𝓗 ⊗ 𝓘)^a = 𝓗^a ⊗ 𝓘^a` on the big `τ`-site

Descent, Lemma 06VE (7) says that the comparison `𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX carries
a tensor product to a tensor product.  This module proves it for the big `τ`-site at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

The route is Stacks 03EL, the comparison `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` for a morphism of ringed
topoi, applied to the morphism of ringed topoi attached to the comparison of Stacks 070U by
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral`.  What makes
that applicable is that `𝓕 ↦ 𝓕^a` *is* the pullback of modules along that morphism of ringed
topoi, which is `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`, the
uniqueness of left adjoints.  Nothing about quasi-coherence or about the topology enters.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseRingedToposModulesHom`: the comparison as a morphism of
  ringed topoi in the form Stacks 03EL consumes.
* `AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`: **Stacks 03D6 (2) at
  the comparison** — the modules development's pullback along it is `𝓕 ↦ 𝓕^a`.

## Main results

* `AlgebraicGeometry.BigFppfOver.tensorSheafBifunctor_obj_eq`: the tensor bifunctor of Tag 01CA
  and the left-tensoring functor `(Stacks.SheafOfModules.Tensor.sheafTensor R).obj F` agree on
  objects.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorSheafIso` and
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso`: **Descent, Lemma 06VE (7) for
  the big `τ`-site at every `τ`**, in the two spellings of the tensor product.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheafification of abelian presheaves on the big `τ`-site, at the
`(baseRingedTopos B S hS τ).J` spelling. -/
public instance hasWeakSheafify_baseRingedTopos_J (τ : SiteKind) :
    HasWeakSheafify (baseRingedTopos B S hS τ).J AddCommGrpCat.{u} :=
  (inferInstance : HasWeakSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences of abelian presheaves on the big `τ`-site, at the
`(baseRingedTopos B S hS τ).J` spelling. -/
public instance wEqualsLocallyBijective_baseRingedTopos_J (τ : SiteKind) :
    (baseRingedTopos B S hS τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  (inferInstance : (baseOverTopology B S hS τ).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- The pushforward of sheaves of modules along the comparison is a right adjoint, the
associated-module functor being its left adjoint.  The restatement is needed because the target
of `fSharpRing` is spelled with `Functor.sheafPushforwardContinuous`, which does not unfold at
instance transparency. -/
public instance sheafPushforward_baseToZariskiRingedToposHom_isRightAdjoint (τ : SiteKind) :
    (SheafOfModules.pushforward.{u}
      (baseToZariskiRingedToposHom B S hS τ).fSharpRing).IsRightAdjoint :=
  (baseAssociatedModuleAdjunction B S hS τ).isRightAdjoint

/-- **Stacks 03D6, part (2), at the comparison of Stacks 070U.**  The pullback of sheaves of
modules along it, in the general form of
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, is the associated-module functor
`𝓕 ↦ 𝓕^a` of the big `τ`-site.  This holds by `rfl`, both functors being
`SheafOfModules.pullback` of the same structure map; the point of the statement is the left
hand side, the single-universe form `pullbackTopos` not being typeable here. -/
public theorem pullbackToposGeneral_baseToZariskiRingedToposHom (τ : SiteKind) :
    (baseToZariskiRingedToposHom B S hS τ).pullbackToposGeneral =
      baseAssociatedModule B S hS τ := rfl

/-- The morphism of ringed topos sites underlying the morphism of ringed sites is the one
Stacks 070U is registered on. -/
public theorem toRingedToposSiteHom_baseToZariskiRingedSiteHom (τ : SiteKind) :
    (baseToZariskiRingedSiteHom B S hS τ).toRingedToposSiteHom =
      baseToZariskiRingedToposHom B S hS τ := rfl

section Bridge

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The tensor product bifunctor of Tag 01CA and the left tensoring functor agree on
objects. -/
public theorem tensorSheafBifunctor_obj_eq (F G :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj (F, G) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).obj G := rfl

end Bridge

/-- The comparison `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed topoi of the
modules development, which is the form Stacks 03EL consumes. -/
public abbrev baseRingedToposModulesHom (τ : SiteKind) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (baseRingedSite B S hS τ).toRingedTopos
      S.zariskiRingedSite.toRingedTopos :=
  (baseToZariskiRingedSiteHom B S hS τ).toRingedToposHom.toRingedToposModulesHom

/-- **Stacks 03D6 (2) at the comparison of Stacks 070U**: the pullback of sheaves of modules of
the modules development, along the morphism of ringed topoi attached to the comparison, is the
associated-module functor `𝓕 ↦ 𝓕^a` of the big `τ`-site. -/
public def pullbackModulesIsoBaseAssociatedModule (τ : SiteKind) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (baseRingedSite B S hS τ).toRingedTopos)
        (Y := S.zariskiRingedSite.toRingedTopos)
        (baseRingedToposModulesHom B S hS τ) ≅
      baseAssociatedModule B S hS τ :=
  RingedSite.HomGeneral.pullbackModulesToposIsoGeneral (baseToZariskiRingedSiteHom B S hS τ)

/-- Stacks 03EL at the comparison of Stacks 070U, in the spelling of the modules
development's pullback. -/
public def pullbackModulesTensorIso (τ : SiteKind) (H I : S.Modules) :
    ((baseRingedToposModulesHom B S hS τ).pullbackModules).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I)) ≅
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
        (((baseRingedToposModulesHom B S hS τ).pullbackModules).obj H,
          ((baseRingedToposModulesHom B S hS τ).pullbackModules).obj I) :=
  (Stacks.SheafOfModules.pullbackTensorIso (baseRingedToposModulesHom B S hS τ)).app (H, I)

/-- **Descent, Lemma 06VE (7) for the big `τ`-site, at every `τ`**, in the tensor-bifunctor
spelling of Tag 01CA. -/
public def baseAssociatedModuleTensorSheafIso (τ : SiteKind) (H I : S.Modules) :
    (baseAssociatedModule B S hS τ).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I)) ≅
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
        ((baseAssociatedModule B S hS τ).obj H, (baseAssociatedModule B S hS τ).obj I) :=
  letI e := pullbackModulesIsoBaseAssociatedModule B S hS τ
  (e.app ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I))).symm ≪≫
    pullbackModulesTensorIso B S hS τ H I ≪≫
    (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).mapIso
      (Iso.prod (e.app H) (e.app I))

/-- **Descent, Lemma 06VE (7) for the big `τ`-site, at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  The comparison `𝓕 ↦ 𝓕^a` of Descent,
Proposition 03DX carries a tensor product of `𝒪_S`-modules to the tensor product of their
images: `(𝓗 ⊗_{𝒪_S} 𝓘)^a ≅ 𝓗^a ⊗_𝒪 𝓘^a` in `Mod((Sch/S)_τ, 𝒪)`.

This is Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso`, for the morphism of ringed
topoi attached to the comparison of Stacks 070U, carried across
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`.

No hypothesis is carried, and in particular quasi-coherence is not needed: the statement holds
for arbitrary `𝒪_S`-modules.  06VE states it for `QCoh(𝒪_S)` only because that is the source
category on which its functor is an equivalence, so this is the clause with its hypothesis
dropped rather than added to.

The tensor products are `(Stacks.SheafOfModules.Tensor.sheafTensor O).obj H`, the sheafification
of the objectwise tensor product of the underlying presheaves of modules (Stacks 05NB); that
functor's value agrees with the bifunctor of Tag 01CA by
`AlgebraicGeometry.BigFppfOver.tensorSheafBifunctor_obj_eq`. -/
@[stacks 06VE "part (7), big site (Sch/S)_τ at every τ, for arbitrary 𝒪_S-modules"]
public def baseAssociatedModuleTensorIso (τ : SiteKind) (H I : S.Modules) :
    (baseAssociatedModule B S hS τ).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf).obj H).obj I) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
            (FibredSite.baseStructureSheaf B S hS τ)).obj
          ((baseAssociatedModule B S hS τ).obj H)).obj
        ((baseAssociatedModule B S hS τ).obj I) :=
  baseAssociatedModuleTensorSheafIso B S hS τ H I

end AlgebraicGeometry.BigFppfOver

end
