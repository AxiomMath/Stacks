module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiSectionsIso
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteTensorAgreement
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral

/-!
# `𝓕 ↦ 𝓕^a` commutes with tensor products on the small Zariski site

Clause (7) of Stacks 06VE: for `𝒪_S`-modules `𝓕`, `𝓖` on a scheme `S`,

`(𝓕 ⊗_{𝒪_S} 𝓖)^a = 𝓕^a ⊗_𝒪 𝓖^a`.

**This closes the clause at `τ = Zariski`**, which was the last of its cells: the big site at
every `τ` is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso` and the small site at
`τ = étale` is `AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso`, and Stacks 03DU
gives a
small site only for `τ ∈ {Zariski, étale}`.

The source's reason is that `𝓕 ↦ 𝓕^a` is the pullback functor for a morphism of ringed sites,
and such commute with tensor products by Modules on Sites, Lemma 03EL.  Both halves are available,
so this file is the conjugation of one by the other:

* Stacks 03EL is `Stacks.SheafOfModules.pullbackTensorIso`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensor.lean`), stated for
  `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` along the four-field
  morphism of ringed topoi.
* `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` is a morphism of ringed *sites*,
  `AlgebraicGeometry.SmallZariski.toOpensRingedSiteHom`, and the pullback along its structure
  map is `AlgebraicGeometry.SmallZariski.associatedModule`.  The two pullbacks are identified by
  `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`.

Nothing in the argument is specific to `τ = Zariski`; what was missing was the packaging of
Remark 03FH at `τ = Zariski` as an `AlgebraicGeometry.RingedSite.HomGeneral`, which
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSiteHomGeneral` now
supplies.

## Both descriptions of `𝓕^a` are covered

Stacks 03DU (4) defines `𝓕^a` **by its sections**, so a statement about the pullback-defined
`𝓕^a` is a statement about Stacks' `𝓕^a` only once the two are identified — the standard the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor` state and which earlier
pullback-form registrations at this site failed.  So the clause is proved in both descriptions:
over the pullback-defined functor, and — through Remark 03FH (1),
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections` — over the sections-defined
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections`, which is where Stacks 03DU (4) at
`τ = Zariski` is registered.

## Main results

* `AlgebraicGeometry.SmallZariski.associatedModuleTensorIsoOfComparison`: **Stacks 06VE (7) at
  `τ = Zariski`**, as an isomorphism of bifunctors.
* `AlgebraicGeometry.SmallZariski.associatedModuleTensorObjIsoOfComparison`: the same clause
  objectwise, the form in which the source states it.
* `AlgebraicGeometry.SmallZariski.associatedModuleOfSectionsTensorObjIso`: the clause for the
  sections-defined `𝓕^a` of Stacks 03DU (4).

## Implementation notes

The two bifunctor statements are made for **all** `𝒪_S`-modules, not only quasi-coherent ones;
the source states clause (7) for quasi-coherent `𝓕`, `𝓖`, and the quasi-coherent case is this
one restricted along `CategoryTheory.ObjectProperty.ι`.  Nothing in the argument uses
quasi-coherence: it is a property of the pullback functor.  The sections statement does assume
it, the sections-defined `𝓕^a` of Stacks 03DU (4) being defined for a quasi-coherent module;
quasi-coherence of `𝓕 ⊗_{𝒪_S} 𝓖` is not an added hypothesis but the library instance
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_tensorSheafBifunctor_obj` (Stacks 01CE (3)).

The names carry `OfComparison`, as in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealClosureProperties`,
because `AlgebraicGeometry.SmallZariski.associatedModuleTensorObjIso` is already taken by the
*identity reading* of `𝓕 ↦ 𝓕^a` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiClosureProperties`, where
both tensor products are one and the same bifunctor and nothing is compared.  That statement
carries no tag, and the two are about different functors.

The tensor product is the uncurried `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification
of the objectwise tensor product of the underlying presheaves of modules, which is the construction
03EL is stated over. On both sites here it lands on the nose in the category of modules over the
site's structure sheaf: `Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf of
`AlgebraicGeometry.smallZariskiRingedSite` is `AlgebraicGeometry.SmallZariski.structureSheaf` by
`rfl` (`AlgebraicGeometry.smallZariskiRingedSite_ringSheaf`), so no bridge between tensor-product
spellings is needed.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `id_{small, Zar, Zar} : (S_Zar, 𝒪) ⟶ (S_Zar, 𝒪_S)` as the four-field morphism of ringed
topoi over which pullback and pushforward of sheaves of modules are constructed. -/
public abbrev opensRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (RingedSite.toRingedTopos (smallZariskiRingedSite B S hS))
      (RingedSite.toRingedTopos S.zariskiRingedSite) :=
  (toOpensRingedSiteHom B S hS).toRingedToposHom.toRingedToposModulesHom

/-- The pullback of sheaves of modules along the four-field morphism of ringed topoi attached to
`id_{small, Zar, Zar}` is `𝓕 ↦ 𝓕^a`.

This is `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` read at that
morphism; its right-hand side is `AlgebraicGeometry.SmallZariski.associatedModule`
definitionally, by
`AlgebraicGeometry.SmallZariski.pullbackToposGeneral_toOpensRingedSiteHom`. -/
public def pullbackModulesIsoAssociatedModule :
    (opensRingedToposModulesHom B S hS).pullbackModules ≅
      associatedModule B S hS :=
  RingedSite.HomGeneral.pullbackModulesToposIsoGeneral (toOpensRingedSiteHom B S hS)

/-- **Stacks 06VE (7) at `τ = Zariski`.**  The functor `𝓕 ↦ 𝓕^a` into the `𝒪`-modules of the
small Zariski site of `S` carries the tensor product of two `𝒪_S`-modules to the tensor product
of their images:

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`,

naturally in the pair `(𝓕, 𝓖)`.

This is Modules on Sites, Lemma 03EL — `Stacks.SheafOfModules.pullbackTensorIso` — for the
morphism of ringed topoi underlying `id_{small, Zar, Zar}` of Remark 03FH, conjugated on both
sides by `AlgebraicGeometry.SmallZariski.pullbackModulesIsoAssociatedModule`.

The functor is the pullback description of Stacks 03DU (4); the clause for the sections
description, which is the one 03DU (4) gives, is
`AlgebraicGeometry.SmallZariski.associatedModuleOfSectionsTensorObjIso`.  With
`AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso` (small site at `τ = étale`) and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso` (big site, every `τ`) this
completes clause (7) at every functor the lemma quantifies over. -/
@[stacks 06VE "part (7), small site at τ = Zariski, for the PULLBACK-defined functor 𝓕 ↦ 𝓕ᵃ of \
Remark 03FH, for all 𝒪_S-modules; bifunctor form"]
public def associatedModuleTensorIsoOfComparison :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf) ⋙
        associatedModule B S hS ≅
      Functor.prod (associatedModule B S hS) (associatedModule B S hS) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallZariskiRingedSite B S hS).O) :=
  Functor.isoWhiskerLeft _ (pullbackModulesIsoAssociatedModule B S hS).symm ≪≫
    Stacks.SheafOfModules.pullbackTensorIso (opensRingedToposModulesHom B S hS) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (pullbackModulesIsoAssociatedModule B S hS)
        (pullbackModulesIsoAssociatedModule B S hS)) _

/-- **Stacks 06VE (7) at `τ = Zariski`, objectwise** — the form in which the source states it:
`(𝓕 ⊗_{𝒪_S} 𝓖)^a = 𝓕^a ⊗_𝒪 𝓖^a`, for the pullback description of `𝓕 ↦ 𝓕^a`. -/
@[stacks 06VE "part (7), small site at τ = Zariski, for the PULLBACK-defined functor 𝓕 ↦ 𝓕ᵃ of \
Remark 03FH, for all 𝒪_S-modules; objectwise form"]
public def associatedModuleTensorObjIsoOfComparison (F G : S.Modules) :
    (associatedModule B S hS).obj
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)).obj (F, G)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallZariskiRingedSite B S hS).O)).obj
        ((associatedModule B S hS).obj F, (associatedModule B S hS).obj G) :=
  (associatedModuleTensorIsoOfComparison B S hS).app (F, G)

/-- **Stacks 06VE (7) at `τ = Zariski`, for the sections-defined `𝓕^a` of Stacks 03DU (4).**
For quasi-coherent `𝒪_S`-modules `𝓕`, `𝓖`,

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`,

where `𝓕^a` is the sheaf on `S_Zar` whose sections over `f : T → S` are `Γ(T, f^*𝓕)`.

This is `AlgebraicGeometry.SmallZariski.associatedModuleTensorObjIsoOfComparison` read through
Remark 03FH (1), `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`, at the three
modules involved.  It is the description Stacks 03DU (4) gives, and so the description every
statement of this tag is about. -/
@[stacks 06VE "part (7), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4), for quasi-coherent 𝒪_S-modules"]
public def associatedModuleOfSectionsTensorObjIso (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    associatedModuleOfSections B S hS
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)).obj (F, G)) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallZariskiRingedSite B S hS).O)).obj
        (associatedModuleOfSections B S hS F, associatedModuleOfSections B S hS G) :=
  (associatedModuleIsoOfSections B S hS
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)).obj (F, G))).symm ≪≫
    associatedModuleTensorObjIsoOfComparison B S hS F G ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallZariskiRingedSite B S hS).O)).mapIso
        (Iso.prod (associatedModuleIsoOfSections B S hS F)
          (associatedModuleIsoOfSections B S hS G))

end AlgebraicGeometry.SmallZariski

end
