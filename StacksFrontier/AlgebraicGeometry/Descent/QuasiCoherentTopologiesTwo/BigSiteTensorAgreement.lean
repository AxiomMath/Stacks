module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# Stacks 0GNE (2) at the big sites of a scheme: the tensor products agree

Descent, Lemma 0GNE (2) says that for quasi-coherent modules `𝓕`, `𝓖` on `(Sch/S)_fppf` the
tensor products `𝓕 ⊗_𝒪 𝓖` computed in `Mod((Sch/S)_Zar, 𝒪)`, in `Mod((Sch/S)_étale, 𝒪)` and in
`Mod((Sch/S)_fppf, 𝒪)` agree, and that the common value is quasi-coherent.  This file proves
both clauses, at every one of the five topologies: first for `𝓕 = 𝓗^a` and `𝓖 = 𝓘^a`, which is
the shape the source's proof produces, and then for an **arbitrary** pair of quasi-coherent
modules on `(Sch/S)_fppf`, which is the source's own scope.

The source's proof is one line: write `𝓕 = 𝓗^a` and `𝓖 = 𝓘^a`, and then
`𝓕 ⊗_𝒪 𝓖 = (𝓗 ⊗_{𝒪_S} 𝓘)^a` in `Mod((Sch/S)_τ, 𝒪)` for every `τ` by Lemma 06VE (7), so all
three are the same object.  Both halves of that line are now available:

* 06VE (7) at every `τ` is
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorSheafIso`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseAssociatedModuleTensor.lean:154`);
* that `𝓗^a` on `(Sch/S)_τ` is `𝓗^a` on `(Sch/S)_fppf` read for the coarser topology is
  `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` of
  `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence`.

What the two give together is that the `τ`-tensor product of the two readings is the reading of
an fppf sheaf, namely of `(𝓗 ⊗ 𝓘)^a`.  That is exactly the hypothesis `hunit` of
`Stacks.SheafOfModules.tensorLeftAgreement`, which until now was undischarged and which is why
that declaration carried no `stacks` attribute: the unit of "sheafify for fppf" ⊣ "read an fppf
sheaf for `τ`" is invertible precisely on the objects already in the image of the reading, and
`AlgebraicGeometry.BigFppfOver.tensorRestrictTopologyIso` exhibits the `τ`-tensor product as one
of them.

## Main results

* `AlgebraicGeometry.BigFppfOver.tensorRestrictTopologyIso`: the `τ`-tensor product of the
  readings of `𝓗^a` and `𝓘^a` is the reading of `(𝓗 ⊗_{𝒪_S} 𝓘)^a`.
* `AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_tensorRestrictTopology`: hence the unit of
  `Stacks.SheafOfModules.comparisonAdjunction` is invertible there — the hypothesis `hunit`
  discharged.
* `AlgebraicGeometry.BigFppfOver.tensorAgreementAssociatedModule`: **Stacks 0GNE (2), the
  agreement** — the tensor product computed on `(Sch/S)_fppf`, read for `τ`, is the tensor
  product computed on `(Sch/S)_τ`, at every one of the five topologies.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_tensorAssociatedModule`: **Stacks
  0GNE (2), the quasi-coherence of the common value**, again at every `τ`.
* `AlgebraicGeometry.BigFppfOver.tensorAgreementQuasicoherentOnSite` and
  `…isQuasicoherentOnSite_tensorRestrictTopology`: **the same two clauses for an arbitrary pair
  of quasi-coherent `𝒪`-modules on `(Sch/S)_fppf`**, which is the source's scope.

## Implementation notes, the arbitrary pair

The last two results are the first two carried along two isomorphisms at once.  Essential
surjectivity, `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`,
writes `𝓕 ≅ 𝓗^a` and `𝓖 ≅ 𝓘^a` with `𝓗`, `𝓘` quasi-coherent on `S`; what carries the clause
across both at once is that the tensor product is a functor on the **product** category, so
`Functor.mapIso` of a `CategoryTheory.Iso.prod` moves both arguments in one step.  That is the
one thing part (1) did not need, its comparison having a single argument, and it is why the two
halves could not simply be read off each other.

Only the *existence* of such a pair is used, and it is isolated in
`AlgebraicGeometry.BigFppfOver.exists_iso_restrictTopology_tensorRestrictTopology`: that
statement is a `Prop`, so the choice of `𝓗` and `𝓘` never enters a definition, and the agreement
below is the canonical
`Stacks.SheafOfModules.tensorLeftAgreement` — the inverse of a unit — rather than a transport
chosen by `Classical.choice`.  The quasi-coherence of `𝓗 ⊗_{𝒪_S} 𝓘` has to be supplied by hand,
`@AlgebraicGeometry.BigFppfOver.isQuasicoherent_tensorSheafBifunctor_obj` applied to the two
`FullSubcategory` properties, for the reason that instance's own docstring gives: the module
categories are indexed by two spellings of one sheaf of rings which instance search does not
identify.

## Coverage limits

* The first two results are proved for `𝓕` and `𝓖` of the form `𝓗^a`, `𝓘^a`; they are steps,
  left at that scope because that is what their statements assert, and carry no registration.
  Part (2) at the source's scope, an arbitrary pair, is the last two results, which carry the
  0GNE registrations.  Nothing is missing from part (2) any more.
* What is *not* claimed, at either scope, is part (2) for a pair that is not quasi-coherent: the
  source's `𝓕` and `𝓖` are objects of `QCoh((Sch/S)_fppf, 𝒪)` and so are these.
* The `τ`-side quasi-coherence is asserted for the common value read on `(Sch/S)_τ`.  At
  `τ = fppf` that is the source's "the common value is an object of `QCoh((Sch/S)_fppf, 𝒪)`".

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind)
  (H I : S.Modules) [H.IsQuasicoherent] [I.IsQuasicoherent]

/-- **Stacks 01CE (3)**, in the bifunctor spelling of Tag 01CA: the tensor product of two
quasi-coherent `𝒪_S`-modules is quasi-coherent.  This is
`AlgebraicGeometry.tensorSheaf_isQuasicoherent` at the ringed space underlying `S`, restated so
that instance search finds it at the spelling the statements below use; the two quasi-coherence
hypotheses are passed by `‹_›` because the module categories are indexed by two spellings of one
sheaf of rings which instance search does not identify. -/
instance isQuasicoherent_tensorSheafBifunctor_obj :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I)) :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent S.toRingedSpace H I ‹_› ‹_›

/-- **The `τ`-tensor product of two associated modules is an associated module.**  The tensor
product of the readings of `𝓗^a` and `𝓘^a` on `(Sch/S)_τ` is the reading of `(𝓗 ⊗_{𝒪_S} 𝓘)^a`.

Three steps, each of which is a statement in the library: the readings are the `τ`-associated modules
(`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, Stacks 070S (1) and
03DT), their `τ`-tensor product is the `τ`-associated module of `𝓗 ⊗_{𝒪_S} 𝓘`
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorSheafIso`, Stacks 06VE (7)), and that
is in turn the reading of the fppf associated module of `𝓗 ⊗_{𝒪_S} 𝓘` — the first step again,
at the quasi-coherent module `𝓗 ⊗_{𝒪_S} 𝓘`. -/
def tensorRestrictTopologyIso :
    (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
        ((restrictTopology B S hS τ).obj ((associatedModule B S hS).obj H),
          (restrictTopology B S hS τ).obj ((associatedModule B S hS).obj I)) ≅
      (restrictTopology B S hS τ).obj ((associatedModule B S hS).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I))) :=
  (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).mapIso
      (Iso.prod (restrictTopologyAssociatedModuleIso B S hS τ H)
        (restrictTopologyAssociatedModuleIso B S hS τ I)) ≪≫
    (baseAssociatedModuleTensorSheafIso B S hS τ H I).symm ≪≫
    (restrictTopologyAssociatedModuleIso B S hS τ
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I))).symm

/-- The unit of "sheafify for fppf" ⊣ "read an fppf sheaf for `τ`" is invertible at any object
isomorphic to a reading, since the right adjoint is fully faithful. -/
private theorem isIso_comparisonUnit_app_of_iso_restrictTopology
    {X : SheafOfModules.{u} (Stacks.SheafOfModules.ringOfLe
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS))}
    {Y : SheafOfModules.{u} (structureSheaf B S hS)} (e : X ≅ (restrictTopology B S hS τ).obj Y) :
    IsIso ((Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit.app X) :=
  (Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).isIso_unit_app_of_iso_rightObj
    (Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)) e

/-- **The hypothesis `hunit` of `Stacks.SheafOfModules.tensorLeftAgreement`, discharged at the
big sites.**  The unit of "sheafify for fppf" ⊣ "read an fppf sheaf for `τ`" is invertible at
the `τ`-tensor product of two associated modules.

The right adjoint is fully faithful, so its unit is invertible exactly at the objects
isomorphic to a reading — `CategoryTheory.Adjunction.isIso_unit_app_of_iso_rightObj` — and
`AlgebraicGeometry.BigFppfOver.tensorRestrictTopologyIso` is such an isomorphism. -/
theorem isIso_comparisonUnit_tensorRestrictTopology :
    IsIso ((Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit.app
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
          ((restrictTopology B S hS τ).obj ((associatedModule B S hS).obj H),
            (restrictTopology B S hS τ).obj ((associatedModule B S hS).obj I)))) :=
  isIso_comparisonUnit_app_of_iso_restrictTopology B S hS τ (tensorRestrictTopologyIso B S hS τ H I)

/-- **Stacks 0GNE (2), the agreement.**  For quasi-coherent `𝒪_S`-modules `𝓗` and `𝓘`, the
tensor product of `𝓗^a` and `𝓘^a` computed in `Mod((Sch/S)_fppf, 𝒪)`, read for the coarser
topology, *is* their tensor product computed in `Mod((Sch/S)_τ, 𝒪)` — at every one of the five
topologies, so in particular the Zariski, étale and fppf values of the source's statement agree.

This is `Stacks.SheafOfModules.tensorLeftAgreement` with its hypothesis discharged by
`AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_tensorRestrictTopology`.  The two spellings
of the tensor product agree on objects by
`AlgebraicGeometry.BigFppfOver.tensorSheafBifunctor_obj_eq`, which is a `rfl`.

The case of an arbitrary pair of objects of `QCoh((Sch/S)_fppf, 𝒪)` is
`AlgebraicGeometry.BigFppfOver.tensorAgreementQuasicoherentOnSite`. -/
def tensorAgreementAssociatedModule :
    (restrictTopology B S hS τ).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (FibredSite.baseStructureSheaf B S hS .fppf))).obj
          ((associatedModule B S hS).obj H, (associatedModule B S hS).obj I)) ≅
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
        ((restrictTopology B S hS τ).obj ((associatedModule B S hS).obj H),
          (restrictTopology B S hS τ).obj ((associatedModule B S hS).obj I)) :=
  Stacks.SheafOfModules.tensorLeftAgreement (baseOverTopology_le_fppf B S hS τ)
    (FibredSite.baseStructureSheaf B S hS .fppf)
    ((associatedModule B S hS).obj H) ((associatedModule B S hS).obj I)
    (isIso_comparisonUnit_tensorRestrictTopology B S hS τ H I)

/-- **Stacks 0GNE (2), the quasi-coherence of the common value.**  The tensor product of `𝓗^a`
and `𝓘^a` on `(Sch/S)_τ` is quasi-coherent on `(Sch/S)_τ`, at every one of the five topologies;
at `τ = fppf` this is the source's "the common value is an object of
`QCoh((Sch/S)_fppf, 𝒪)`".

By Stacks 06VE (7) that tensor product is `(𝓗 ⊗_{𝒪_S} 𝓘)^a`, the tensor product downstairs is
quasi-coherent by Stacks 01CE (3), and the associated module of a quasi-coherent module is
quasi-coherent on the site by Stacks 03DV — which is a theorem at every `τ`,
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`.
So the generic tensor clause of a ringed site is not needed, and could not be used: its
universe hypothesis `UnivLE.{max u v w, w}` reads `UnivLE.{u + 1, u}` on the big site of a
scheme and is false. -/
theorem isQuasicoherentOnSite_tensorAssociatedModule :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
      ((baseAssociatedModule B S hS τ).obj H,
        (baseAssociatedModule B S hS τ).obj I)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (baseAssociatedModuleTensorSheafIso B S hS τ H I)
    (isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (H, I)) inferInstance)

section ArbitraryPair

variable (F G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **The `τ`-tensor product of two quasi-coherent modules on `(Sch/S)_fppf` is the reading of
an fppf sheaf, and that reading is quasi-coherent.**  This is the one place where the arbitrary
pair is reduced to a pair of associated modules, and it is deliberately a `Prop`: the `𝓗` and
`𝓘` with `𝓕 ≅ 𝓗^a`, `𝓖 ≅ 𝓘^a` are produced by the essential surjectivity of `𝓕 ↦ 𝓕^a`
(`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, Stacks 03DX (1)
at `τ = fppf`), which is an existence statement, so letting them into a *definition* would make
the clause depend on a choice.  Both consumers below need only this.

The isomorphism is `AlgebraicGeometry.BigFppfOver.tensorRestrictTopologyIso` precomposed with
the image of `CategoryTheory.Iso.prod` under the tensor product — the step that moves both
arguments at once, which is what the tensor clause needs and the colimit clause of part (1) does
not. -/
theorem exists_iso_restrictTopology_tensorRestrictTopology
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    ∃ Y : SheafOfModules.{u} (structureSheaf B S hS),
      ((restrictTopology B S hS τ).obj Y).IsQuasicoherentOnSite ∧
      Nonempty ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
          ((restrictTopology B S hS τ).obj F, (restrictTopology B S hS τ).obj G) ≅
        (restrictTopology B S hS τ).obj Y) := by
  obtain ⟨M, ⟨eF⟩⟩ := quasicoherentIsEssImageAssociatedModule' B S hS F hF
  obtain ⟨N, ⟨eG⟩⟩ := quasicoherentIsEssImageAssociatedModule' B S hS G hG
  have : M.obj.IsQuasicoherent := M.property
  have : N.obj.IsQuasicoherent := N.property
  have := @isQuasicoherent_tensorSheafBifunctor_obj S M.obj N.obj M.property N.property
  refine ⟨(associatedModule B S hS).obj
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf)).obj (M.obj, N.obj)), ?_, ⟨?_⟩⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (restrictTopologyAssociatedModuleIso B S hS τ _).symm
      (isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ _ inferInstance)
  · exact (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).mapIso
        (Iso.prod ((restrictTopology B S hS τ).mapIso eF.symm)
          ((restrictTopology B S hS τ).mapIso eG.symm)) ≪≫
      tensorRestrictTopologyIso B S hS τ M.obj N.obj

/-- **The hypothesis `hunit` of `Stacks.SheafOfModules.tensorLeftAgreement` for an arbitrary
pair of quasi-coherent modules on `(Sch/S)_fppf`.**  Same proof as
`AlgebraicGeometry.BigFppfOver.isIso_comparisonUnit_tensorRestrictTopology`, with the target of
the reading supplied by the previous result rather than written down: the right adjoint is fully
faithful, so its unit is invertible exactly at the objects isomorphic to a reading. -/
theorem isIso_comparisonUnit_tensorRestrictTopology_of_isQuasicoherentOnSite
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((Stacks.SheafOfModules.comparisonAdjunction
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)).unit.app
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
          ((restrictTopology B S hS τ).obj F, (restrictTopology B S hS τ).obj G))) := by
  obtain ⟨Y, -, ⟨e⟩⟩ := exists_iso_restrictTopology_tensorRestrictTopology B S hS τ F G hF hG
  exact isIso_comparisonUnit_app_of_iso_restrictTopology B S hS τ e

/-- **Stacks 0GNE (2), the agreement, at the source's own scope.**  For an **arbitrary** pair
`𝓕`, `𝓖` of quasi-coherent `𝒪`-modules on `(Sch/S)_fppf`, the tensor product `𝓕 ⊗_𝒪 𝓖` computed
in `Mod((Sch/S)_fppf, 𝒪)`, read for the coarser topology, *is* the tensor product computed in
`Mod((Sch/S)_τ, 𝒪)` — at every one of the five topologies, so in particular the Zariski, étale
and fppf values of the source's statement agree.

`AlgebraicGeometry.BigFppfOver.tensorAgreementAssociatedModule` is this for `𝓕 = 𝓗^a` and
`𝓖 = 𝓘^a`; the reduction of an arbitrary pair to that case is Stacks 03DX (1) at `τ = fppf`
together with the functoriality of the tensor product in both arguments — see the implementation
notes.  The comparison itself is the same one, the inverse of the unit of "sheafify for fppf" ⊣
"read an fppf sheaf for `τ`", so this is not a transported isomorphism but the canonical one
with its invertibility now known at every quasi-coherent pair. -/
@[stacks 0GNE "part (2), the tensor products computed on (Sch/S)_fppf and on (Sch/S)_tau \
agree, for an arbitrary pair of quasi-coherent O-modules on (Sch/S)_fppf, at every one of the \
five topologies"]
def tensorAgreementQuasicoherentOnSite
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    (restrictTopology B S hS τ).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (FibredSite.baseStructureSheaf B S hS .fppf))).obj (F, G)) ≅
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
        ((restrictTopology B S hS τ).obj F, (restrictTopology B S hS τ).obj G) :=
  Stacks.SheafOfModules.tensorLeftAgreement (baseOverTopology_le_fppf B S hS τ)
    (FibredSite.baseStructureSheaf B S hS .fppf) F G
    (isIso_comparisonUnit_tensorRestrictTopology_of_isQuasicoherentOnSite B S hS τ F G hF hG)

/-- **Stacks 0GNE (2), the quasi-coherence of the common value, at the source's own scope.**  For
an arbitrary pair of quasi-coherent `𝒪`-modules on `(Sch/S)_fppf`, the common value of the
tensor products — the right-hand side of
`AlgebraicGeometry.BigFppfOver.tensorAgreementQuasicoherentOnSite` — is quasi-coherent on
`(Sch/S)_τ`, at every one of the five topologies; at `τ = fppf` this is the source's "the common
value is an object of `QCoh((Sch/S)_fppf, 𝒪)`".

By the reduction it is the reading of `(𝓗 ⊗_{𝒪_S} 𝓘)^a`, which is quasi-coherent by Stacks
01CE (3) and Stacks 03DV at every `τ`. -/
@[stacks 0GNE "part (2), quasi-coherence of the common value, for an arbitrary pair of \
quasi-coherent O-modules on (Sch/S)_fppf, at every one of the five topologies"]
theorem isQuasicoherentOnSite_tensorRestrictTopology
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.baseStructureSheaf B S hS τ))).obj
      ((restrictTopology B S hS τ).obj F,
        (restrictTopology B S hS τ).obj G)).IsQuasicoherentOnSite := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := exists_iso_restrictTopology_tensorRestrictTopology B S hS τ F G hF hG
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hY

end ArbitraryPair

end AlgebraicGeometry.BigFppfOver

end
