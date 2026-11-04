module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransportSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtalePicardIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitesFirstCohomology

/-!
# `Pic(𝒪_S) = Pic(𝒪_τ)` on each of the five big sites of a scheme

Let `S` be a scheme of a big fppf site `B` and let `τ` be one of the Zariski, étale, smooth,
syntomic or fppf topologies.  Descent, Proposition 03DX, clause (1) is the equivalence

`QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`

given by `𝓕 ↦ 𝓕^a`, and it is available at every `τ` with no hypothesis
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite`).  This file reads it on
Picard groups:

`Pic(𝒪_S) ≅ Pic(𝒪_τ)`,

with no hypothesis, sending the class of an invertible `𝒪_S`-module `𝓛` to the class of `𝓛^a`.

## The two inputs

The transport itself is
`Stacks.SheafOfModules.Picard.mapAddEquivOfSubcategory`, which asks for two object-level
comparisons of `𝓕 ↦ 𝓕^a` and for the equivalence only on the quasi-coherent modules — the
subcategory where the invertible ones already live.

* The unit comparison is `AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`: the
  pullback of the unit object along the morphism of ringed sites
  `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the unit object, the inclusion of the small Zariski site
  being final.
* The tensor comparison is **Stacks 03EL at that morphism**, and it carries no hypothesis:
  `Stacks.SheafOfModules.pullbackTensorIso` proves 03EL for an arbitrary morphism of ringed
  topoi, and `AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` identifies
  the pullback of modules of that morphism with `𝓕 ↦ 𝓕^a`.

Neither is used with any naturality and no monoidal coherence enters; see the discussion in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean`.

## The clauses of the subcategory transport, and where each comes from

* an invertible `𝒪_S`-module is quasi-coherent:
  `AlgebraicGeometry.SmallEtale.zariskiIsQuasicoherent_of_isInvertible`;
* an invertible `𝒪_τ`-module is quasi-coherent on the big `τ`-site:
  `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_of_isInvertible` below, the converse
  clause of Tag 0B8Q fed the local ringedness of the big `τ`-site,
  `AlgebraicGeometry.baseRingedSite_isLocallyRinged`, followed by finite presentation;
* `𝒪_S` is quasi-coherent, and a tensor product of quasi-coherent `𝒪_S`-modules is
  quasi-coherent (Stacks 01CE);
* `𝓕 ↦ 𝓕^a` reflects isomorphisms of quasi-coherent modules: Stacks 0GN7 for the big site,
  `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`;
* every quasi-coherent module on `(Sch/S)_τ` is an `𝓕^a`:
  `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorBifunctorIso`: **Stacks 03EL at
  `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`** — the associated module of a tensor product is the tensor
  product of the associated modules, at every `τ` and with no hypothesis.
* `AlgebraicGeometry.BigFppfOver.basePicardAddEquiv`: **`Pic(𝒪_S) ≅ Pic(𝒪_τ)`**, at every `τ`
  and with no hypothesis.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_of_isInvertible`: an invertible
  `𝒪`-module on the big `τ`-site of a scheme is quasi-coherent.
* `AlgebraicGeometry.BigFppfOver.isInvertible_baseAssociatedModule`: the associated module of an
  invertible `𝒪_S`-module is invertible on `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.basePicardAddEquiv_classOf`: the isomorphism sends the class of
  `𝓛` to the class of `𝓛^a`, which fixes it rather than only asserting that one exists.

## Implementation notes

Both comparisons are built at the bifunctor spelling of the two tensor products — the canonical
`Stacks.SheafOfModules.Tensor.sheafTensor` read on pairs through
`CategoryTheory.Functor.uncurry`, which is the spelling Stacks 03EL is stated
with — and retyped at the spelling `Stacks.SheafOfModules.Picard.map` consumes by a separate thin
definition whose body is an application.  A declared result type at the consumer's spelling on
the composite itself would force the elaborator to check the whole composite isomorphism against
it, which is expensive at `whnf`; this is the same split, for the same reason, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAssociatedModuleMonoidal.lean`.

No `@[stacks]` attribute is claimed.  Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso`; clause (1) of Stacks 03DX at every `τ` is registered
on `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite`; and Tag 01CX is
registered on `Stacks.SheafOfModules.Picard.PicardGroup`.  This module instantiates them and
matches spellings.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two tensor products, at the bifunctor spelling of Stacks 03EL -/

/-- The tensor product of `𝒪_S`-modules on the small Zariski site of `S`, as the bifunctor
Stacks 03EL is stated with: the canonical tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` read on pairs. -/
public abbrev tensorSheafBifunctorZariski :=
  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    S.zariskiRingedSite.toRingedTopos.O)

/-- The tensor product of `𝒪`-modules on the big `τ`-site of `S`, as the bifunctor Stacks 03EL
is stated with. -/
public abbrev tensorSheafBifunctorBase (τ : SiteKind) :=
  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (baseRingedSite B S hS τ).toRingedTopos.O)

/-- On the small Zariski site of `S` the bifunctor of Stacks 03EL is the tensor product sheaf of
Tag 01CA over the structure presheaf of commutative rings of `S`. -/
public theorem tensorSheafBifunctorZariski_obj (M N : S.Modules) :
    (tensorSheafBifunctorZariski S).obj (M, N) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (zariskiStructureIsSheaf S)⟩).obj M).obj N) := rfl

/-- On the big `τ`-site of `S` the bifunctor of Stacks 03EL is the tensor product sheaf of
Tag 01CA over the structure sheaf of commutative rings of that site. -/
public theorem tensorSheafBifunctorBase_obj (τ : SiteKind)
    (M N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O)) :
    (tensorSheafBifunctorBase B S hS τ).obj (M, N) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(baseRingedSite B S hS τ).O.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (baseRingedSite B S hS τ).O.obj
          (forget₂ CommRingCat RingCat)
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2⟩).obj M).obj N) :=
  rfl

/-! ### Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` -/

/-- **Stacks 03EL at the morphism `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`: the associated module of a
tensor product is the tensor product of the associated modules.**  For `𝒪_S`-modules `𝓕` and
`𝓖` on the small Zariski site of `S`,

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`

on the big `τ`-site, at every one of the five topologies and with no hypothesis on `𝓕` or `𝓖`.

The associated-module functor is the pullback of sheaves of modules along the morphism of ringed
topoi attached to that morphism of ringed sites, by
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`, and
`Stacks.SheafOfModules.pullbackTensorIso` is Stacks 03EL for that pullback. -/
public def baseAssociatedModuleTensorBifunctorIso (τ : SiteKind) (M N : S.Modules) :
    (baseAssociatedModule B S hS τ).obj ((tensorSheafBifunctorZariski S).obj (M, N)) ≅
      (tensorSheafBifunctorBase B S hS τ).obj
        ((baseAssociatedModule B S hS τ).obj M, (baseAssociatedModule B S hS τ).obj N) :=
  (pullbackModulesIsoBaseAssociatedModule B S hS τ).symm.app _ ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso
      (baseRingedToposModulesHom B S hS τ)).app (M, N) ≪≫
    (tensorSheafBifunctorBase B S hS τ).mapIso
      (Iso.prod ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app M)
        ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app N))

/-- **Stacks 03EL at `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, in the packaging of
`Stacks.SheafOfModules.Picard.map`.**  The two tensor products it is stated with are the two
here by `rfl`, as `tensorSheafBifunctorZariski_obj` and `tensorSheafBifunctorBase_obj`
record. -/
public def baseAssociatedModuleTensorIso' (τ : SiteKind) :
    Stacks.SheafOfModules.Picard.TensorIso S.presheaf (zariskiStructureIsSheaf S)
      (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ) := fun M N =>
  baseAssociatedModuleTensorBifunctorIso B S hS τ M N

/-- **The associated module of the structure sheaf is the structure sheaf**, in the packaging of
`Stacks.SheafOfModules.Picard.map`.  This is
`AlgebraicGeometry.BigFppfOver.isIso_basePullbackObjUnitToUnit`: the pullback of the unit object
along the morphism of ringed sites is the unit object, the inclusion of the small Zariski site
being final. -/
public def baseAssociatedModulePicardUnitIso (τ : SiteKind) :
    Stacks.SheafOfModules.Picard.UnitIso S.presheaf (zariskiStructureIsSheaf S)
      (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ) :=
  @asIso _ _ _ _ _ (isIso_basePullbackObjUnitToUnit B S hS τ)

/-! ### An invertible module is quasi-coherent, on each of the two sides -/

/-- **The converse clause of Tag 0B8Q on the big `τ`-site of a scheme.**  An invertible
`𝒪`-module on the big `τ`-site is finite locally free of rank one, the site being locally ringed
by `AlgebraicGeometry.baseRingedSite_isLocallyRinged`. -/
public theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (τ : SiteKind)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O))
    (hL : Stacks.SheafOfModules.IsInvertible (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 L) :
    RingedSite.IsFiniteLocallyFreeOfRank (baseRingedSite B S hS τ) L 1 :=
  have := hL
  RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
    (baseRingedSite B S hS τ) L (baseRingedSite_isLocallyRinged B S hS τ)

/-- **An invertible `𝒪`-module on the big `τ`-site of a scheme is quasi-coherent**, in the sense
of Stacks 03DL (6).  It is finite locally free of rank one, hence of finite presentation, hence
quasi-coherent. -/
public theorem isQuasicoherentOnSite_of_isInvertible (τ : SiteKind)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O))
    (hL : Stacks.SheafOfModules.IsInvertible (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 L) :
    L.IsQuasicoherentOnSite :=
  have : L.IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
      (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS τ L hL).isFiniteLocallyFreeOnSite
  inferInstance

/-- **The associated module of an invertible `𝒪_S`-module is an invertible `𝒪`-module on the big
`τ`-site of `S`**, with no hypothesis:
`Stacks.SheafOfModules.Picard.isInvertible_map_obj` at the two comparisons above. -/
public theorem isInvertible_baseAssociatedModule (τ : SiteKind)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.presheaf (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    Stacks.SheafOfModules.IsInvertible (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      ((baseAssociatedModule B S hS τ).obj L) :=
  Stacks.SheafOfModules.Picard.isInvertible_map_obj _ _ _ _ _
    (baseAssociatedModulePicardUnitIso B S hS τ) (baseAssociatedModuleTensorIso' B S hS τ) L hL

/-! ### The isomorphism of Picard groups -/

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-- **`𝓕 ↦ 𝓕^a` reflects isomorphisms of quasi-coherent modules**: this is Stacks 0GN7 for the
big site, `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`, read on objects
of the full subcategory of quasi-coherent `𝒪_S`-modules. -/
public theorem nonempty_iso_of_iso_baseAssociatedModule (τ : SiteKind) (M N : S.Modules)
    (hM : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) M)
    (hN : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) N)
    (e : (baseAssociatedModule B S hS τ).obj M ≅ (baseAssociatedModule B S hS τ).obj N) :
    Nonempty (M ≅ N) :=
  ⟨(ObjectProperty.ι (SheafOfModules.isQuasicoherent S.ringCatSheaf)).mapIso
    ((fullyFaithfulBaseAssociatedModuleQcoh B S hS τ).preimageIso
      (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) e)⟩

/-- **Every quasi-coherent module on `(Sch/S)_τ` is the associated module of a quasi-coherent
`𝒪_S`-module**: `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, read
as an existential statement rather than as a containment of essential images. -/
public theorem exists_isQuasicoherent_iso_baseAssociatedModule (τ : SiteKind)
    (A : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (hA : A.IsQuasicoherentOnSite) :
    ∃ M : S.Modules, SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) M ∧
      Nonempty ((baseAssociatedModule B S hS τ).obj M ≅ A) := by
  obtain ⟨Y, ⟨e⟩⟩ := baseQuasicoherentIsEssImageAssociatedModule B S hS τ A hA
  exact ⟨Y.obj, Y.property, ⟨e⟩⟩

/-- **`Pic(𝒪_S) ≅ Pic(𝒪_τ)`**, with no hypothesis on `S` and at every one of the five
topologies: the homomorphism of Picard groups induced by the associated-module functor of
Stacks 03DU (4) is an isomorphism of abelian groups.

Both groups are `Stacks.SheafOfModules.Picard.PicardGroup`, the group Tag 040E produces.  The
content is Descent, Proposition 03DX clause (1) at `τ`, used through
`Stacks.SheafOfModules.Picard.mapAddEquivOfSubcategory`: `𝓕 ↦ 𝓕^a` is an equivalence of the
quasi-coherent modules, and every invertible module on either side is quasi-coherent. -/
public def basePicardAddEquiv (τ : SiteKind) :
    Stacks.SheafOfModules.Picard.PicardGroup S.presheaf (zariskiStructureIsSheaf S) ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2 :=
  Stacks.SheafOfModules.Picard.mapAddEquivOfSubcategory _ _ _ _ _
    (baseAssociatedModulePicardUnitIso B S hS τ) (baseAssociatedModuleTensorIso' B S hS τ)
    (P₁ := fun M => SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) M)
    (P₂ := fun A => A.IsQuasicoherentOnSite)
    (AlgebraicGeometry.SmallEtale.zariskiIsQuasicoherent_of_isInvertible S)
    (isQuasicoherentOnSite_of_isInvertible B S hS τ)
    (AlgebraicGeometry.SmallEtale.zariskiIsQuasicoherent_of_isInvertible S _
      (Stacks.SheafOfModules.isInvertible_unit S.presheaf (zariskiStructureIsSheaf S)))
    (AlgebraicGeometry.SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent S)
    (nonempty_iso_of_iso_baseAssociatedModule B S hS τ)
    (exists_isQuasicoherent_iso_baseAssociatedModule B S hS τ)

/-- **The isomorphism sends the class of `𝓛` to the class of `𝓛^a`.**  This fixes it, rather
than only asserting that some isomorphism exists. -/
public theorem basePicardAddEquiv_classOf (τ : SiteKind)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      S.presheaf (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    basePicardAddEquiv B S hS τ
        (Stacks.SheafOfModules.Picard.classOf S.presheaf (zariskiStructureIsSheaf S) L hL) =
      Stacks.SheafOfModules.Picard.classOf (baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
        ((baseAssociatedModule B S hS τ).obj L)
        (isInvertible_baseAssociatedModule B S hS τ L hL) :=
  Stacks.SheafOfModules.Picard.map_classOf _ _ _ _ _
    (baseAssociatedModulePicardUnitIso B S hS τ) (baseAssociatedModuleTensorIso' B S hS τ) L hL

end AlgebraicGeometry.BigFppfOver

end
