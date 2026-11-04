module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafifyMixed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction along a functor, the monoidal tensor product, and quasi-coherence

Two small statements that a computation with the tensor product of a *sheaf* and a *presheaf* of
modules on a subsite needs, and which the library stated only at neighbouring spellings.

The first is that restriction of presheaves of modules along a functor `v : C ⥤ C'` commutes with
**Mathlib's monoidal** tensor product of presheaves of modules — the one
`CategoryTheory.MonoidalCategory.tensorObj` on `PresheafOfModules (O ⋙ forget₂ _ _)` for a
presheaf of commutative rings `O`.  It holds on the nose.

The second is that the associated sheaf of `F|_O ⊗_O G`, for `F` a quasi-coherent sheaf of
`O♯`-modules and `G` a presheaf of `O`-modules whose associated sheaf is quasi-coherent, is
quasi-coherent.  This is [Stacks, Tag 03L6] read through the comparison
`PresheafOfModules.tensorSheafifyMixedIso` of [Stacks, Tag 0GMW]: that comparison identifies the
tensor product sheaf `F ⊗_{O♯} G♯`, which [Stacks, Tag 03L6] is stated for, with the associated
sheaf of the presheaf tensor product, which is the object a sections computation produces.

## Main definitions

* `Stacks.MonoidalRestrictionTensor.restrictModules` — restriction of presheaves of modules along
  `v`, with the restricted presheaf of commutative rings spelled `v.op ⋙ O` *before* the
  forgetful functor to rings, which is the spelling in which the monoidal structure on the
  restricted category is found by instance search.

## Main results

* `Stacks.MonoidalRestrictionTensor.restrictModules_tensorObj` — **restriction along `v` commutes
  with the monoidal tensor product of presheaves of modules**, by `rfl`.
* `Stacks.MonoidalRestrictionTensor.isQuasicoherentOnSite_moduleSheafification_tensorObj` —
  **the associated sheaf of the objectwise tensor product of a quasi-coherent sheaf of
  `O♯`-modules with a presheaf of `O`-modules whose associated sheaf is quasi-coherent is
  quasi-coherent.**

## What is and is not proved

Both statements are proved in full, for an arbitrary site and an arbitrary morphism
`a : O ⟶ O♯` to the sections of a sheaf of commutative rings which is locally injective and
locally surjective on the underlying presheaves of rings.  The hypotheses carried by the second
are exactly the quasi-coherence of the two factors — `F` and the associated sheaf of `G` — and
the sheafification instances of the site at the module universe; nothing about finiteness,
flatness or affineness.

**No tag attribute is placed.**  The first statement is a second spelling of
`Stacks.DenseSubsiteModules.presheafRestrict_tensorObj`, which records the same fact for the
mixed-universe objectwise tensor product `Stacks.tensorObj`; the two objectwise tensor products
are identified by `Stacks.SheafOfModules.TensorEncodings.tensorObj_eq_tensorObj` and
`...tensorObj_eq_tensor`, so this is one fact about one construction, recorded at the spelling
`Mathlib`'s monoidal structure uses.  The second statement carries no new mathematics either:
[Stacks, Tag 03L6] is
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` and
[Stacks, Tag 0GMW] is `PresheafOfModules.sheafificationTensorIso`, both already tagged.

This module therefore invalidates nothing; what it does invalidate elsewhere, namely the claim of
the "What is and is not proved" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionQuasicoherent.lean` that the
monoidal form of the restriction statement and a comparison between the two tensor product
sheaves were owed, is recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorRestrictionVanishing.lean`, which is
where that note's four steps are discharged.

## Implementation notes

`restrictModules` exists only to fix a spelling.  `PresheafOfModules.pushforward₀OfCommRingCat v O`
lands in `PresheafOfModules (v.op ⋙ (O ⋙ forget₂ _ _))`, and the monoidal structure Mathlib
provides is on `PresheafOfModules (R ⋙ forget₂ _ _)` for a presheaf of commutative rings `R`;
recovering `R := v.op ⋙ O` from `v.op ⋙ (O ⋙ forget₂ _ _)` asks the unifier to reassociate a
composition of functors while solving for `R`, which it does not do.  Declaring the functor with
the reassociated codomain — the two are the same functor, the reassociation being `rfl` — fixes
the spelling once, and is the device
`Stacks.DenseSubsiteModules.presheafRestrict` uses for the same reason.

The monoidal structure of the restriction is already in Mathlib, as the instance
`PresheafOfModules.instMonoidalPushforward₀OfCommRingCat` of
`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`, whose multiplication
isomorphism has identity components; `restrictModules_tensorObj` is the equality of objects that
accompanies it, which that file does not state.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

universe v₁ u₁ v₂ u₂ v u w

namespace Stacks.MonoidalRestrictionTensor

section Restrict

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C'] (v : C ⥤ C')
  (O : C'ᵒᵖ ⥤ CommRingCat.{w})

/-- **Restriction of presheaves of modules along a functor**, with the restricted presheaf of
commutative rings spelled `v.op ⋙ O`.  This is `PresheafOfModules.pushforward₀OfCommRingCat`;
only the spelling of the presheaf of rings on the source site differs, and it differs so that the
monoidal structure on the restricted category is visible to instance search. -/
noncomputable abbrev restrictModules :
    PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{w} ((v.op ⋙ O) ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀OfCommRingCat v O

/-- **Restriction along a functor commutes with the monoidal tensor product of presheaves of
modules.**  Both sides send an object `X` of the source site to
`M(v X) ⊗_{O(v X)} N(v X)`, with the same restriction maps, so this is `rfl`.

`Stacks.DenseSubsiteModules.presheafRestrict_tensorObj` is the same statement for the
mixed-universe objectwise tensor product `Stacks.tensorObj`. -/
theorem restrictModules_tensorObj
    (M N : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) :
    (restrictModules v O).obj (M ⊗ N) =
      (restrictModules v O).obj M ⊗ (restrictModules v O).obj N :=
  rfl

end Restrict

section Quasicoherent

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The associated sheaf of the objectwise tensor product of a quasi-coherent sheaf of
`O♯`-modules with a presheaf of `O`-modules whose associated sheaf is quasi-coherent is
quasi-coherent.**

This is [Stacks, Tag 03L6] —
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`, the
quasi-coherence of a tensor product of sheaves of modules — transported along
`PresheafOfModules.tensorSheafifyMixedIso`, the case of [Stacks, Tag 0GMW] in which one factor is
already a sheaf: `F ⊗_{O♯} G♯ ≅ (F|_O ⊗_O G)♯`.

The hypotheses are the quasi-coherence of `F` and of the associated sheaf of `G`, and nothing
else. -/
@[ega "I 9.1.1" "more general"]
theorem isQuasicoherentOnSite_moduleSheafification_tensorObj
    (F : SheafOfModules.{w} (toRingCat J Osharp))
    (G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    [SheafOfModules.IsQuasicoherentOnSite F]
    [SheafOfModules.IsQuasicoherentOnSite ((PresheafOfModules.moduleSheafification J a).obj G)] :
    ((PresheafOfModules.moduleSheafification J a).obj
      (PresheafOfModules.tensorObj
        ((PresheafOfModules.restrictSheafFunctor J a).obj F) G)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (PresheafOfModules.tensorSheafifyMixedIso J a F G)
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite J Osharp F
      ((PresheafOfModules.moduleSheafification J a).obj G))

end Quasicoherent

end Stacks.MonoidalRestrictionTensor

end
