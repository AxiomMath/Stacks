module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The associated module of the small étale site is monoidal, and so is its Zariski restriction

Let `S` be a scheme of a big étale site `B`.  Stacks 03DU (4) at `τ = étale` is the
associated-module functor `𝓕 ↦ 𝓕^a`, `AlgebraicGeometry.SmallEtale.associatedModule`, from
`𝒪_S`-modules on the small Zariski site of `S` to `𝒪`-modules on its small étale site, and
`AlgebraicGeometry.SmallEtale.restrictModule` is its right adjoint, restriction along the
inclusion of the small Zariski site.  This file supplies the compatibility of both with the
tensor product:

* `(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`, with no hypothesis;
* `(𝓜 ⊗_𝒪 𝓝)|_{S_Zar} ≅ 𝓜|_{S_Zar} ⊗_{𝒪_S} 𝓝|_{S_Zar}` for *quasi-coherent* `𝓜` and `𝓝`.

## What the first one is

It is **Stacks 03EL at `ε`**, the morphism of ringed sites `(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of
Stacks 070R and 08H7.  `Stacks.SheafOfModules.pullbackTensorIso` proves 03EL for an arbitrary
morphism of ringed topoi in the shape the modules development consumes, and every input it needs
at `ε` is already in the tree:

* `AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom` is `ε` as an
  `AlgebraicGeometry.RingedSite.HomGeneral`, which carries a morphism of topoi, so
  `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` and
  `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` package it in that shape.  The
  object universes of the two sites differ — `S_étale` has objects in `Type (u + 1)` and `S_Zar`
  in `Type u` — and 03EL is stated at independent universes, so nothing has to be transported.
* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` identifies the
  pullback of modules of that morphism of ringed topoi with
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, which at `ε` *is* `associatedModule`
  by `AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`.

So the comparison is 03EL at `ε` read across that identification.

## What the second one is

The restriction `restrictModule` is a right adjoint and is therefore only *lax* monoidal in
general.  On quasi-coherent modules it is the inverse of the equivalence of Descent,
Proposition 03DX (2), and an equivalence whose forward functor is monoidal has monoidal inverse;
the proof here is that statement unfolded at one pair of objects, so that no monoidal structure
has to be transported:

`𝓜 ⊗ 𝓝 ≅ (𝓜|_{S_Zar})^a ⊗ (𝓝|_{S_Zar})^a ≅ (𝓜|_{S_Zar} ⊗ 𝓝|_{S_Zar})^a`

by the counit, which is an isomorphism at a quasi-coherent module
(`AlgebraicGeometry.SmallEtale.isIso_counit`, whose second hypothesis is the theorem
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`), and then the unit, which is an
isomorphism at a quasi-coherent `𝒪_S`-module
(`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`), applied to
`𝓜|_{S_Zar} ⊗ 𝓝|_{S_Zar}` — quasi-coherent by Stacks 01CE,
`AlgebraicGeometry.tensorSheaf_isQuasicoherent`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`: `ε` in the shape of morphism of
  ringed topoi that the pullback, the pushforward and Stacks 03EL of the modules development
  consume.
* `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`: the pullback of modules along that
  morphism is the associated-module functor of Stacks 03DU (4).
* `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`: **Stacks 03EL at `ε`** — the
  associated module of a tensor product is the tensor product of the associated modules.
* `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`: **the Zariski restriction of a tensor
  product of quasi-coherent modules is the tensor product of the restrictions.**

## Main results

* `AlgebraicGeometry.SmallEtale.tensorSheafBifunctorZariski_obj` and
  `AlgebraicGeometry.SmallEtale.tensorSheafBifunctorEtale_obj`: the bifunctor Stacks 03EL is
  stated with is, on objects, the tensor product its consumers write on each of the two sites.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent`: Stacks 01CE at
  the explicit-hypothesis spelling the proof needs.

## Implementation notes

Both comparisons are stated at the bifunctor spelling of the two tensor products,
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the one Stacks 03EL is stated
with and the one the bodies produce.  The spellings the *consumers* use are identified with it on
objects by `rfl`, in `AlgebraicGeometry.SmallEtale.tensorSheafBifunctorZariski_obj` and
`AlgebraicGeometry.SmallEtale.tensorSheafBifunctorEtale_obj`: on the Zariski site the consumers'
spelling is the hand-built tensor product of Tag 01CB,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of the ringed space of `S` — the one
`Stacks.TensorSheafDedup.tensorSheaf_eq` identifies with the Tag 05NA construction — and on the
small étale site it is `Stacks.SheafOfModules.Tensor.sheafTensor`, the Tag 01CA
tensor product sheaf, which is what `AlgebraicGeometry.Space.modulesTensorObjIso` compares the
monoidal product of `𝒪`-modules with.

The bridge is kept in those two `rfl` lemmas rather than written into the result types of the
comparisons: a declared result type at the consumers' spelling forces the elaborator to check the
whole composite isomorphism against it, and that exhausts the heartbeat budget at `whnf`, while
each `rfl` lemma on its own is cheap.  This is the same split, for the same reason, as the one
recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteSheafTensor.lean`.

Stacks 01CE is applied with its two quasi-coherence hypotheses passed positionally rather than
found by instance search: the predicate is stated over
`Stacks.RingedSpace.structureSheafRing S.toRingedSpace` while the modules at hand are over
`AlgebraicGeometry.Scheme.ringCatSheaf`, and the two sheaves of rings, though definitionally
equal, are not matched by instance search.

No `@[stacks]` attribute is claimed.  Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso`, which proves it for an arbitrary morphism of ringed
topoi; this module instantiates it at one morphism and matches spellings, exactly as
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardRestriction.lean`
does for the direct image, and claims no clause of 03DU, 03DX or 070R that is not already
registered.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ε` in the shape the modules development consumes -/

/-- The morphism of ringed sites `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 070R and 08H7, in
the shape `Stacks.Sheaves.RingedToposModules.RingedToposHom` that the pullback and pushforward of
modules of Stacks 03D6 and the comparison of Stacks 03EL consume.

This is `AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom` — `ε` as a morphism of ringed sites
carrying a morphism of topoi — pushed through
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.  The two object universes of the
underlying sites differ and nothing asks them to agree. -/
abbrev toZariskiRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedSite B S hS).toRingedTopos
      S.zariskiRingedSite.toRingedTopos :=
  (toZariskiRingedSiteHom B S hS).toRingedToposHom.toRingedToposModulesHom

/-- **The pullback of sheaves of modules along `ε`, taken along the morphism of ringed topoi, is
the associated-module functor of Stacks 03DU (4).**

`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` compares it with the
pullback along the site-presented morphism, and that one *is* `associatedModule` by
`AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`. -/
def pullbackModulesToZariskiIso :
    pullbackModules.{u, u, u, u + 1, u, u} (toZariskiRingedToposModulesHom B S hS) ≅
      associatedModule B S hS :=
  (toZariskiRingedSiteHom B S hS).pullbackModulesToposIsoGeneral

/-! ### The two tensor products, at the bifunctor spelling of Stacks 03EL -/


/-- On the small Zariski site of `S` the bifunctor of Stacks 03EL is the hand-built tensor
product of Tag 01CB on the ringed space of `S`. -/
theorem tensorSheafBifunctorZariski_obj (M N : S.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.zariskiRingedSite.toRingedTopos.O).obj M).obj N =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(S).presheaf, (S).IsSheaf⟩).obj M).obj N := rfl

/-- On the small étale site of `S` the bifunctor of Stacks 03EL is the tensor product sheaf of
Tag 01CA over the structure sheaf of commutative rings. -/
theorem tensorSheafBifunctorEtale_obj (M N : SheafOfModules.{u} (structureSheaf B S hS)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
      hS).toRingedTopos.O)).obj M).obj N =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(commRingStructureSheaf B S hS).obj,
          Presheaf.isSheaf_of_isSheaf_comp _ (commRingStructureSheaf B S hS).obj
            (forget₂ CommRingCat RingCat) (structure_isSheaf B S hS)⟩).obj M).obj N := rfl

/-! ### Stacks 03EL at `ε` -/

/-- **Stacks 03EL at `ε`: the associated module of a tensor product is the tensor product of the
associated modules.**  For `𝒪_S`-modules `𝓕` and `𝓖` on the small Zariski site of `S`,

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`

on the small étale site, with no hypothesis on `𝓕` or `𝓖`.

The associated-module functor is the pullback of sheaves of modules along the morphism of ringed
topoi attached to `ε`, by `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`, and
`Stacks.SheafOfModules.pullbackTensorIso` is Stacks 03EL for that pullback. -/
def associatedModuleTensorIso (M N : S.Modules) :
    (associatedModule B S hS).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.zariskiRingedSite.toRingedTopos.O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
        hS).toRingedTopos.O)).obj ((associatedModule B S hS).obj M)).obj ((associatedModule B S
        hS).obj N) :=
  (pullbackModulesToZariskiIso B S hS).symm.app _ ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso
      (toZariskiRingedToposModulesHom B S hS)).app (M, N) ≪≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
      hS).toRingedTopos.O)).mapIso ((pullbackModulesToZariskiIso B S hS).app M)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
        hS).toRingedTopos.O)).obj _).mapIso ((pullbackModulesToZariskiIso B S hS).app N))

/-! ### The Zariski restriction of a tensor product of quasi-coherent modules -/

/-- **Stacks 01CE**, with the two quasi-coherence hypotheses explicit: the tensor product of two
quasi-coherent `𝒪_S`-modules is quasi-coherent.

`AlgebraicGeometry.tensorSheaf_isQuasicoherent` is the instance; it is restated here because its
hypotheses are over `Stacks.RingedSpace.structureSheafRing S.toRingedSpace` while a module of
`AlgebraicGeometry.Scheme.Modules` carries its quasi-coherence over
`AlgebraicGeometry.Scheme.ringCatSheaf`, and instance search does not match the two. -/
theorem isQuasicoherent_tensorSheaf_of_isQuasicoherent (M N : S.Modules)
    (hM : SheafOfModules.IsQuasicoherent M) (hN : SheafOfModules.IsQuasicoherent N) :
    SheafOfModules.IsQuasicoherent (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.zariskiRingedSite.toRingedTopos.O).obj M).obj N) :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent S.toRingedSpace M N hM hN

/-- **The Zariski restriction of a tensor product of quasi-coherent modules on the small étale
site is the tensor product of the restrictions.**  For `𝒪`-modules `𝓜` and `𝓝` on the small
étale site of `S`, both quasi-coherent in the sense of Stacks 03DL,

`(𝓜 ⊗_𝒪 𝓝)|_{S_Zar} ≅ 𝓜|_{S_Zar} ⊗_{𝒪_S} 𝓝|_{S_Zar}`.

This is the monoidality of the inverse of the equivalence of Descent, Proposition 03DX (2),
unfolded at one pair of objects.  The counit of the associated-module adjunction is an
isomorphism at a quasi-coherent module, `AlgebraicGeometry.SmallEtale.isIso_counit`, so `𝓜 ⊗ 𝓝`
is the associated module of `𝓜|_{S_Zar} ⊗ 𝓝|_{S_Zar}` by
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`; and the unit is an isomorphism at a
quasi-coherent `𝒪_S`-module, `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, which applies
to that tensor product by Stacks 01CE.

Quasi-coherence of the restrictions themselves is not a hypothesis: it is the theorem
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`. -/
def restrictModuleTensorIso (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (restrictModule B S hS).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((smallEtaleRingedSite B S hS).toRingedTopos.O)).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S.zariskiRingedSite.toRingedTopos.O).obj ((restrictModule B S hS).obj M)).obj
        ((restrictModule B S hS).obj N) := by
  have hM₀ : SheafOfModules.IsQuasicoherent ((restrictModule B S hS).obj M) :=
    isQuasicoherent_restrictModule B S hS M hM
  have hN₀ : SheafOfModules.IsQuasicoherent ((restrictModule B S hS).obj N) :=
    isQuasicoherent_restrictModule B S hS N hN
  have cM : (associatedModule B S hS).obj ((restrictModule B S hS).obj M) ≅ M :=
    @asIso _ _ _ _ _ (isIso_counit B S hS M hM hM₀)
  have cN : (associatedModule B S hS).obj ((restrictModule B S hS).obj N) ≅ N :=
    @asIso _ _ _ _ _ (isIso_counit B S hS N hN hN₀)
  have eu : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S.zariskiRingedSite.toRingedTopos.O).obj ((restrictModule B S hS).obj M)).obj
    ((restrictModule B S hS).obj N) ≅
      (restrictModule B S hS).obj ((associatedModule B S hS).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S.zariskiRingedSite.toRingedTopos.O).obj ((restrictModule B S hS).obj M)).obj
          ((restrictModule B S hS).obj N))) :=
    @asIso _ _ _ _ _ (unitIsoOnQuasicoherent B S hS
      ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S.zariskiRingedSite.toRingedTopos.O).obj ((restrictModule B S hS).obj M)).obj
        ((restrictModule B S hS).obj N),
        isQuasicoherent_tensorSheaf_of_isQuasicoherent S _ _ hM₀ hN₀⟩)
  exact (restrictModule B S hS).mapIso
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
        hS).toRingedTopos.O)).mapIso cM.symm).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ((smallEtaleRingedSite B S
        hS).toRingedTopos.O)).obj _).mapIso cN.symm) ≪≫
        (associatedModuleTensorIso B S hS _ _).symm) ≪≫ eu.symm

end AlgebraicGeometry.SmallEtale

end
