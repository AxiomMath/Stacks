module

public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceTensor

/-!
# Reindexing along an equivalence of ringed sites of different sizes and the tensor product

Let `e : C' ≌ C` be an equivalence of sites, where `C` and `C'` live in independent object and
morphism universes, and let `𝒪` be a sheaf of commutative rings on `(C, J)`. The reindexing
`Stacks.SheafOfModules.reindexEquivalence` carries the tensor product sheaf of Stacks 01CA to the
tensor product sheaf: `(𝓕 ⊗_𝒪 𝓖)|_{C'} ≅ 𝓕|_{C'} ⊗_{𝒪|_{C'}} 𝓖|_{C'}`.

Here `C` lives in the universes `u, v` and `C'` in independent universes `u', v'`.

## Main definitions

* `Stacks.SheafOfModules.reindexRingedSiteHomAnyUniverse`: `e.inverse` as a morphism of ringed
  sites from the reindexed ringed site to the given one.
* `Stacks.SheafOfModules.pullbackModulesReindexIsoAnyUniverse`: the pullback of modules along it
  is the functor of `Stacks.SheafOfModules.reindexEquivalence`.
* `Stacks.SheafOfModules.reindexTensorIsoAnyUniverse`: the compatibility of the reindexing with
  the tensor product sheaf (Stacks 03EL along `e.inverse`).
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The structure sheaf of commutative rings transported along an equivalence of sites
`e : C' ≌ C` between categories of independent sizes: the direct image of `𝒪` under
`e.functor`. -/
abbrev reindexCommRingAnyUniverse {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) : Sheaf J' CommRingCat.{w} :=
  (e.functor.sheafPushforwardContinuous CommRingCat.{w} J' J).obj O

/-- The reindexed site, with the transported structure sheaf, as a ringed site in the universes
of `C'`. -/
abbrev reindexRingedSiteAnyUniverse {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) : AlgebraicGeometry.RingedSite.{u', v', w} where
  C := C'
  J := J'
  O := reindexCommRingAnyUniverse J' e O

/-- The structure map of the inverse of an equivalence of ringed sites of independent sizes, on
sheaves of commutative rings: the counit of `e` read on `𝒪`. -/
def reindexBackSharpCommAnyUniverse {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) :
    O ⟶ (e.inverse.sheafPushforwardContinuous CommRingCat.{w} J J').obj
      (reindexCommRingAnyUniverse J' e O) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op e.counit) O.obj)

/-- **Reindexing along an equivalence of sites of independent sizes, as a morphism of ringed
sites.** The functor is `e.inverse` and the structure map is
`Stacks.SheafOfModules.reindexBackSharpCommAnyUniverse`. -/
def reindexRingedSiteHomAnyUniverse {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J'] :
    AlgebraicGeometry.RingedSite.HomGeneral (reindexRingedSiteAnyUniverse J' e O)
      (siteRingedSite J O) where
  u := e.inverse
  isMorphismOfSites := hmos
  fsharp := reindexBackSharpCommAnyUniverse J' e O

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying functor of `Stacks.SheafOfModules.reindexRingedSiteHomAnyUniverse` is
`e.inverse`. -/
@[simp]
theorem reindexRingedSiteHomAnyUniverse_u {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) [_root_.IsMorphismOfSites.{w} e.inverse J J'] :
    (reindexRingedSiteHomAnyUniverse J' e O).u = e.inverse := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The structure map of `Stacks.SheafOfModules.reindexRingedSiteHomAnyUniverse` is
`Stacks.SheafOfModules.reindexBackSharpCommAnyUniverse`. -/
@[simp]
theorem reindexRingedSiteHomAnyUniverse_fsharp {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) [_root_.IsMorphismOfSites.{w} e.inverse J J'] :
    (reindexRingedSiteHomAnyUniverse J' e O).fsharp = reindexBackSharpCommAnyUniverse J' e O :=
  rfl

section Pullback

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- The reindexing along an equivalence of sites of independent sizes, as a morphism of ringed
topoi. -/
abbrev reindexRingedToposModulesHomAnyUniverse {C' : Type u'} [Category.{v'} C']
    (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (O : Sheaf J CommRingCat.{w}) [_root_.IsMorphismOfSites.{w} e.inverse J J']
    [J'.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [LocallySmall.{w} C'] :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (reindexRingedSiteAnyUniverse J' e O).toRingedTopos (siteRingedSite J O).toRingedTopos :=
  (reindexRingedSiteHomAnyUniverse J' e O).toRingedToposHom.toRingedToposModulesHom

variable {C' : Type u'} [Category.{v'} C']
  (J' : GrothendieckTopology C') [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (O : Sheaf J CommRingCat.{w}) [_root_.IsMorphismOfSites.{w} e.inverse J J']
  [J'.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [LocallySmall.{w} C']

/-- **The pullback of sheaves of modules along the reindexing is the functor of the reindexing
equivalence**, for sites of independent sizes: both are left adjoint to the direct image along
`e.inverse`. -/
def pullbackModulesReindexIsoAnyUniverse :
    (reindexRingedToposModulesHomAnyUniverse J' e O).pullbackModules ≅
      (reindexEquivalence.{w, w, u, v, u', v'} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor :=
  (reindexRingedSiteHomAnyUniverse J' e O).pullbackModulesToposIsoGeneral ≪≫
    Adjunction.leftAdjointUniq
      (reindexRingedSiteHomAnyUniverse J' e
        O).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (reindexEquivalence.{w, w, u, v, u', v'} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).toAdjunction

/-- **Reindexing along an equivalence of ringed sites of independent sizes carries the tensor
product sheaf to the tensor product sheaf:** `(𝓕 ⊗_𝒪 𝓖)|_{C'} ≅ 𝓕|_{C'} ⊗_{𝒪|_{C'}} 𝓖|_{C'}`,
Stacks 03EL at the morphism of ringed topoi attached to `e.inverse`. -/
def reindexTensorIsoAnyUniverse
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (reindexEquivalence.{w, w, u, v, u', v'} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
          (reindexCommRingAnyUniverse J' e O)).obj
        ((reindexEquivalence.{w, w, u, v, u', v'} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj M)).obj
        ((reindexEquivalence.{w, w, u, v, u', v'} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj N) :=
  (pullbackModulesReindexIsoAnyUniverse J' e O).symm.app _ ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso
      (reindexRingedToposModulesHomAnyUniverse J' e O)).app (M, N) ≪≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
        (reindexCommRingAnyUniverse J' e O)).mapIso
      ((pullbackModulesReindexIsoAnyUniverse J' e O).app M)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
        (reindexCommRingAnyUniverse J' e O)).obj _).mapIso
        ((pullbackModulesReindexIsoAnyUniverse J' e O).app N))

end Pullback

end Stacks.SheafOfModules

end
