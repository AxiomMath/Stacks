module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiRingedComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The module-valued direct image `Ru_{X/S, *}` along `u_{X/S}`

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The morphism of topoi
`u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` of [Stacks, Tag 07IL] is carried on abelian sheaves by
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiDirectImage` and derived there as
`...derivedZariskiDirectImageFunctor`.  This file carries it on **modules**: it builds

  `u_{X/S, *} : Mod(𝒪_{X/S}) ⥤ Mod(u_{X/S, *}𝒪_{X/S})`,

its graded right derived functors `R^j u_{X/S, *}` and the derived functor
`Ru_{X/S, *} : D⁺(Mod(𝒪_{X/S})) ⥤ D⁺(Mod(u_{X/S, *}𝒪_{X/S}))`, all of them functors between
genuine categories of sheaves of modules, and it identifies the underlying abelian sheaf of
`u_{X/S, *}F` with the abelian direct image of the underlying abelian sheaf of `F`.

## Which sheaf of rings, and why that one

A direct image of modules needs a ring on the target and a structure map `f^♯` into the direct
image of the source ring.  Two candidates live on `X_Zar`.

* **`𝒪_X`.**  This does *not* work, and the obstruction is not a universe one.  A structure map
  `𝒪_X ⟶ u_{X/S, *}𝒪_{X/S}`, equivalently `u_{X/S}^{-1}𝒪_X ⟶ 𝒪_{X/S}`, would split every divided
  power thickening of the site on sections, and
  `Crystalline.GlobalCrystallineSituation.SmallSite.isEmpty_ringHom_zmod_sq` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` shows there is
  no such splitting already for `Spec 𝔽_p ↪ Spec ℤ/p²`.  The canonical comparison runs the other
  way, `...structureToZariskiInverseImage : 𝒪_{X/S} ⟶ u_{X/S}^{-1}𝒪_X`.  That analysis is correct
  and is not disturbed here; **nothing below claims an `𝒪_X`-module structure on `Ru_{X/S, *}F`.**
  It agrees with the literature: `Ru_{X/S, *}𝒪_{X/S}` is computed by a de Rham complex, whose
  differentials are not `𝒪_X`-linear.

* **`u_{X/S, *}𝒪_{X/S}` itself.**  This is the ring that acts on `u_{X/S, *}F` with no extra
  datum at all, the structure map being the identity, and it is the one used below.  Its global
  sections are the global sections of `𝒪_{X/S}` on `Cris(X/S)`, which is the ring the chapter's
  module-valued global sections
  `Crystalline.GlobalCrystallineSituation.SmallSite.moduleGlobalSections` are already valued over.

Forming `u_{X/S, *}𝒪_{X/S}` is exactly what
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` records as
impossible at the ring universe `u`, and that record is also correct: the direct image of a
presheaf of rings is the right Kan extension of [Stacks, Tag 00XK] along `(forgetToOpens S).op`,
computed by limits indexed by `StructuredArrow (op V) (forgetToOpens S).op`, whose objects lie in
`Type (u + 1)` and whose morphisms in `Type u`, so it needs
`CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} RingCat.{u}`, i.e. `max u (u + 1) ≤ u`.

The repair is the one `SmallSite/CrisModuleDirectImage.lean` already uses for `f_{cris, *}`:
**raise the universe of the ring of sections**.  At `RingCat.{u + 1}` the same limits exist,
`max u (u + 1) = u + 1`, so `u_{X/S, *}𝒪^{ULift}_{X/S}` is formed; and raising the ring costs
nothing, because `Stacks.Modules.sheafRingULiftEquiv` is an isomorphism of categories
`SheafOfModules.{u + 1} (structureSheafULift S) ≌ ModuleSheaf S` which changes neither the
underlying presheaf of abelian groups nor the morphisms.  So the source of the functor built here
is the chapter's own `Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf S`, over the
chapter's own `𝒪_{X/S}`, and no statement below is a statement about a universe lift of
`𝒪_{X/S}` presented as one about `𝒪_{X/S}`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `zariskiRingPushforwardULift` — the direct image of sheaves of rings along `u_{X/S}` at the
  coefficients `RingCat.{u + 1}`.
* `zariskiPushforwardStructureSheaf` — **`u_{X/S, *}𝒪^{ULift}_{X/S}`**, the sheaf of rings on
  `X_Zar` over which the direct image of modules is taken.
* `ZariskiModuleSheaf` — sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules on `X_Zar`.
* `zariskiRingStructureMapULift` — the structure map `f^♯`, the identity.
* `moduleRingULiftEquivalence` — the ring-universe comparison
  `Mod(𝒪_{X/S}) ≌ Mod(𝒪^{ULift}_{X/S})` of `SmallSite/CrisModuleDirectImage.lean`, packaged as an
  equivalence of categories.
* `zariskiModuleDirectImageULift` and `zariskiModuleDirectImage` —
  **`u_{X/S, *} : Mod(𝒪_{X/S}) ⥤ Mod(u_{X/S, *}𝒪_{X/S})`**, before and after the ring-universe
  isomorphism.
* `higherZariskiModuleDirectImage` — **`R^j u_{X/S, *}`** on modules, `ℕ`-indexed.
* `derivedZariskiModuleDirectImageFunctor` and `derivedZariskiModuleDirectImage` —
  **`Ru_{X/S, *}`** on modules, between bounded below derived categories.
* `moduleULiftZariskiModuleDirectImage`, `moduleULiftHigherZariskiModuleDirectImage` and
  `moduleULiftDerivedZariskiModuleDirectImage` — the same three functors read on
  `SheafOfModules.{u} (structureSheaf S)`, the module universe at which the chapter's crystal and
  quasi-coherence predicates are stated.

## Main results

* `instHasPointwiseRightKanExtensionForgetToOpensRing` — **the Kan extension that `𝒪_{X/S}` does
  not admit at `RingCat.{u}` exists at `RingCat.{u + 1}`**; this is what makes
  `zariskiPushforwardStructureSheaf` exist.
* `zariskiModuleDirectImage_comp_toSheaf` — **the abelian sheaf underlying `u_{X/S, *}F` is the
  abelian `u_{X/S, *}` of the abelian sheaf underlying `F`**, as an equality of functors,
  with `toSheaf_obj_zariskiModuleDirectImage` its form on a single module.  This is what ties the
  functor built here to `...zariskiDirectImage`, and it is what makes the ring universe lift
  harmless.
* `instAbelianZariskiModuleSheaf` and `instEnoughInjectivesZariskiModuleSheaf` — the target
  category is abelian with enough injectives, which is what lets `R^j u_{X/S, *}` and
  `Ru_{X/S, *}` be formed.
* `isZero_higherZariskiModuleDirectImage_of_injective` — `R^j u_{X/S, *}I = 0` for `j > 0` and `I`
  injective.
* `preservesFiniteLimits_zariskiModuleDirectImage` — **`u_{X/S, *}` on modules is left exact**,
  and hence `higherZariskiModuleDirectImageZeroIso` and
  `homologyZeroDerivedZariskiModuleDirectImageIso`: `R^0 u_{X/S, *} ≅ u_{X/S, *}` and
  `H^0(Ru_{X/S, *} -) ≅ u_{X/S, *}`.
* `derivedZariskiModuleDirectImage_comp_homologyFunctor` — the cohomology of `Ru_{X/S, *}` is the
  `ℤ`-indexed `R^j u_{X/S, *}`.

## What is and is not proved

What is proved is that the direct image of sheaves of rings along `u_{X/S}` exists at the
coefficients `RingCat.{u + 1}`; that the module-valued `u_{X/S, *}`, `R^j u_{X/S, *}` and
`Ru_{X/S, *}` therefore exist, with source the chapter's own category of sheaves of
`𝒪_{X/S}`-modules; that the abelian sheaf underlying `u_{X/S, *}F` is the abelian direct
image of the abelian sheaf underlying `F`, on the nose; that `R^j u_{X/S, *}` kills injectives
in positive degree; and that `u_{X/S, *}` on modules is left exact, so that
`R^0 u_{X/S, *} ≅ u_{X/S, *}`.  Every statement is unconditional: no declaration here carries a
hypothesis beyond the global crystalline situation itself and the choice of derived category
models.

A note on left exactness.  One might expect `R^0 f_{cris, *} ≅ f_{cris, *}` to require
exhibiting `Stacks.SheafOfModules.pushforwardCocontinuous` as a right adjoint.  A right adjoint is
not needed for left exactness: `SheafOfModules.toSheaf` **reflects** finite limits, and the composite
of the module-valued direct image with it is the abelian direct image, which preserves all
limits.  That is the proof of `preservesFiniteLimits_zariskiModuleDirectImageULift` below, and
the same argument applied to the two cocontinuous factors of `f_{cris, *}` gives
`...higherCrisModuleDirectImageZeroIso` of `SmallSite/CrisModuleLeftExact.lean`.  The functor is
in fact a right adjoint as well; see below.

What is **not** proved, and what this file does not address:

* **The [Stacks, Tag 015M] factorization of module-valued crystalline cohomology through
  `Ru_{X/S, *}` is not proved here, and the one input it still lacks is named.**  The abelian
  factorization `...derivedGlobalSectionsIsoDerivedZariskiDirectImage` of
  `SmallSite/ZariskiDirectImage.lean` has two inputs: the underived comparison of global sections,
  and `...preservesInjectiveObjects_zariskiDirectImage`.  On modules the second is missing, but
  not for want of a left adjoint: `...zariskiModuleInverseImage` of
  `SmallSite/ZariskiModuleInverseImage.lean` is one, by
  `Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous`.  What is missing is that that
  left adjoint preserve monomorphisms, and by
  `...preservesInjectiveObjects_zariskiModuleDirectImage_iff` that is not merely sufficient but
  necessary.  It is also not automatic: on modules the inverse image is the abelian
  `u_{X/S}^{-1}` followed by base change along the counit
  `u_{X/S}^{-1}u_{X/S, *}𝒪_{X/S} ⟶ 𝒪_{X/S}`, which is not an isomorphism, and base change
  preserves monomorphisms only when flat
  (`Stacks.ChangeOfRings.flat_of_preservesMonomorphisms_extendScalars`).  So
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` still cannot be applied, and the
  reduction `H^i(Cris(X/S), F) ≅ H^i(X_Zar, Ru_{X/S, *}F)` is not available *as a statement about
  modules*.  It **is** available as a statement about abelian groups, as
  `...moduleDerivedGlobalSectionsIso` of `SmallSite/ZariskiRingedComparison.lean`, which is the
  abelian factorization read at the abelian sheaf underlying a module — and that is what a
  vanishing statement such as `Vanishing07MR` needs, an `A`-module being zero exactly when its
  underlying abelian group is.
* **Nothing about `𝒪_X` is claimed**; see the discussion of the two candidate rings above.
* **No comparison of this functor with the de Rham complex** is made, so [Stacks, Tag 07LM] is
  neither stated nor proved here.
* Nothing here carries a `@[stacks]` attribute.  The assertions of [Stacks, Tag 07IL] about the
  forgetful functor and the morphism of topoi are carried in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiToposMorphism.lean`; this module only
  adds module coefficients to that morphism, which is infrastructure.

## References

* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe w w' u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (S : GlobalCrystallineSituation.{u})

/-! ### The direct image of sheaves of rings at the raised ring universe -/

/-- **The limits that compute the right Kan extension along the forgetful functor of
[Stacks, Tag 07IH] exist at the coefficients `RingCat.{u + 1}`.**  They are indexed by
`StructuredArrow (op V) (forgetToOpens S).op`, whose objects lie in `Type (u + 1)` and whose
morphisms in `Type u`, and `RingCat.{u + 1}` has limits of that size because
`max u (u + 1) = u + 1`.

This is the instance that fails for `RingCat.{u}`, which is why
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ZariskiRingedComparison.lean` records
`u_{X/S, *}𝒪_{X/S}` as unformable there; it is the whole of what has to be repaired, and raising
the ring universe repairs it. -/
instance instHasPointwiseRightKanExtensionForgetToOpensRing
    (F : (CrystallineThickening S)ᵒᵖ ⥤ RingCat.{u + 1}) :
    (forgetToOpens S).op.HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- **The direct image of sheaves of rings along `u_{X/S}`**, at the coefficients
`RingCat.{u + 1}`: Mathlib's pushforward along the cocontinuous forgetful functor of
[Stacks, Tag 07IH], the same construction that `...zariskiDirectImage` is at the coefficients
`AddCommGrpCat.{u + 1}`. -/
abbrev zariskiRingPushforwardULift :
    Sheaf (smallTopology S) RingCat.{u + 1} ⥤ Sheaf (opensTopology S) RingCat.{u + 1} :=
  (forgetToOpens S).sheafPushforwardCocontinuous RingCat.{u + 1}
    (smallTopology S) (opensTopology S)

/-- **`u_{X/S, *}𝒪^{ULift}_{X/S}`, the sheaf of rings on `X_Zar` over which the direct image of
`𝒪_{X/S}`-modules is taken.**  Its sections over an open `V` of `X` are the limit of
`ULift Γ(T, 𝒪_T)` over the objects `(U, T, δ)` of `Cris(X/S)` with `U ⊆ V`.

This is *not* `𝒪_X`, and it is not claimed to be comparable with it: see the module
documentation. -/
def zariskiPushforwardStructureSheaf : Sheaf (opensTopology S) RingCat.{u + 1} :=
  (zariskiRingPushforwardULift S).obj (structureSheafULift S)

/-- **The category of sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules on the small Zariski site of
`X`**, the target of the module-valued direct image, at the chapter's module universe `u + 1`. -/
abbrev ZariskiModuleSheaf := SheafOfModules.{u + 1} (zariskiPushforwardStructureSheaf S)

/-- **The structure map `f^♯` of the module-valued direct image along `u_{X/S}`**: the identity,
the sheaf of rings on `X_Zar` having been *defined* as the direct image of the sheaf of rings on
`Cris(X/S)`.  No comparison of structure sheaves is assumed, and none is available; see the
module documentation. -/
def zariskiRingStructureMapULift :
    zariskiPushforwardStructureSheaf S ⟶
      (zariskiRingPushforwardULift S).obj (structureSheafULift S) :=
  𝟙 _

/-! ### The ring-universe comparison as an equivalence -/

/-- **Raising the universe of the coefficient rings is an equivalence
`Mod(𝒪_{X/S}) ≌ Mod(𝒪^{ULift}_{X/S})`**, with inverse
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleRingULiftDown`.  Both composites are the
identity functor on the nose, by `...moduleRingULiftUp_comp_down` and
`...moduleRingULiftDown_comp_up`, so the unit and the counit are identities: this is an
isomorphism of categories, not merely an equivalence.  It is
`Stacks.Modules.sheafRingULiftEquiv` read at the structure sheaf of the small crystalline
site. -/
def moduleRingULiftEquivalence :
    ModuleSheaf S ≌ SheafOfModules.{u + 1} (structureSheafULift S) where
  functor := moduleRingULiftUp S
  inverse := moduleRingULiftDown S
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Raising the universe of the coefficient rings is an equivalence of categories; in particular
it is exact, which is what the left exactness of the module-valued direct image below needs. -/
instance isEquivalence_moduleRingULiftUp : (moduleRingULiftUp S).IsEquivalence :=
  (moduleRingULiftEquivalence S).isEquivalence_functor

/-! ### `u_{X/S, *}` on modules -/

/-- **The direct image of sheaves of modules along `u_{X/S}`, at the lifted ring coefficients.**
It is `Stacks.SheafOfModules.pushforwardCocontinuous` of [Stacks, Tag 0FN3] for the structure map
`zariskiRingStructureMapULift`, so its underlying abelian sheaf is the abelian `u_{X/S, *}` of the
underlying abelian sheaf. -/
def zariskiModuleDirectImageULift :
    SheafOfModules.{u + 1} (structureSheafULift S) ⥤ ZariskiModuleSheaf S :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u + 1} (forgetToOpens S)
    (zariskiRingStructureMapULift S)

/-- The underlying abelian sheaf of the direct image of modules at the lifted ring coefficients is
the abelian direct image, as an equality of functors. -/
theorem zariskiModuleDirectImageULift_comp_toSheaf :
    zariskiModuleDirectImageULift S ⋙
        SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S) =
      SheafOfModules.toSheaf.{u + 1} (structureSheafULift S) ⋙ zariskiDirectImage S :=
  Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf.{u + 1} _ _

/-- The direct image of modules at the lifted ring coefficients is additive: its underlying
abelian functor is the abelian `u_{X/S, *}`, which is additive, and the forgetful functor to
abelian sheaves is faithful and additive. -/
instance additive_zariskiModuleDirectImageULift :
    (zariskiModuleDirectImageULift S).Additive := by
  have h : (zariskiModuleDirectImageULift S ⋙
      SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S)).Additive := by
    rw [zariskiModuleDirectImageULift_comp_toSheaf]
    infer_instance
  exact Functor.additive_of_comp_faithful _
    (SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S))

/-- **The module-valued direct image
`u_{X/S, *} : Mod(𝒪_{X/S}) ⥤ Mod(u_{X/S, *}𝒪_{X/S})`** along the morphism of topoi
`u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` of [Stacks, Tag 07IL].

Read the module over the universe lift of `𝒪_{X/S}`, which is an isomorphism of categories
(`moduleRingULiftUp`), then push forward.  The source is the chapter's own category of sheaves of
`𝒪_{X/S}`-modules, over the chapter's own structure sheaf and at its own module universe `u + 1`:
the universe lift of the rings is confined to the place where the right Kan extension is formed,
and is what makes it exist. -/
def zariskiModuleDirectImage : ModuleSheaf S ⥤ ZariskiModuleSheaf S :=
  moduleRingULiftUp S ⋙ zariskiModuleDirectImageULift S

/-- **The abelian sheaf underlying `u_{X/S, *}F` is the abelian direct image of the abelian
sheaf underlying `F`**, as an equality of functors
`Mod(𝒪_{X/S}) ⥤ Ab(X_Zar)`.

This is the identity that ties the module-valued direct image built here to
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiDirectImage`, and it holds on the nose:
the ring-universe comparison does not change the sections at all, and
`Stacks.SheafOfModules.pushforwardCocontinuous` carries the `𝒪`-action on the right Kan extension
itself rather than transporting it along an isomorphism. -/
theorem zariskiModuleDirectImage_comp_toSheaf :
    zariskiModuleDirectImage S ⋙
        SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S) =
      toAbelianSheaf S ⋙ zariskiDirectImage S := by
  show moduleRingULiftUp S ⋙ zariskiModuleDirectImageULift S ⋙
    SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S) = _
  rw [zariskiModuleDirectImageULift_comp_toSheaf, ← Functor.assoc,
    moduleRingULiftUp_comp_toSheaf]

/-- **The abelian sheaf underlying `u_{X/S, *}F` is the abelian direct image of the abelian
sheaf underlying `F`**, read on a single sheaf of modules. -/
theorem toSheaf_obj_zariskiModuleDirectImage (F : ModuleSheaf S) :
    (SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S)).obj
        ((zariskiModuleDirectImage S).obj F) =
      (zariskiDirectImage S).obj ((toAbelianSheaf S).obj F) :=
  Functor.congr_obj (zariskiModuleDirectImage_comp_toSheaf S) F

/-- `u_{X/S, *}` on modules is additive, being a composite of additive functors. -/
instance additive_zariskiModuleDirectImage : (zariskiModuleDirectImage S).Additive :=
  inferInstanceAs ((moduleRingULiftUp S ⋙ zariskiModuleDirectImageULift S).Additive)

/-! ### Left exactness -/

/-- **The direct image of modules along `u_{X/S}` at the lifted ring coefficients is left
exact.**  Its composite with the forgetful functor to abelian sheaves is, by
`zariskiModuleDirectImageULift_comp_toSheaf`, the abelian `u_{X/S, *}` of the underlying
abelian sheaf, and that preserves all limits, being a right adjoint
(`...preservesLimitsOfSize_zariskiDirectImage`); and `SheafOfModules.toSheaf` reflects finite
limits.  So the module-valued functor preserves them.

This is available here although the companion
`Crystalline.GlobalCrystallineSituation.SmallSite.crisModuleDirectImage` of
`SmallSite/CrisModuleDirectImage.lean` records left exactness as missing: that file's analysis
says that `Stacks.SheafOfModules.pushforwardCocontinuous` is not exhibited as a right adjoint,
which is true, but a right adjoint is not needed — reflecting the limits through
`SheafOfModules.toSheaf` suffices, and the same argument would give left exactness there. -/
@[sga "4 IV 13.6" "special case"]
instance preservesFiniteLimits_zariskiModuleDirectImageULift :
    PreservesFiniteLimits (zariskiModuleDirectImageULift S) := by
  have h : PreservesFiniteLimits (zariskiModuleDirectImageULift S ⋙
      SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S)) := by
    rw [zariskiModuleDirectImageULift_comp_toSheaf]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S))

/-- **`u_{X/S, *}` on modules is left exact**, being the composite of an equivalence of categories
with a left exact functor. -/
instance preservesFiniteLimits_zariskiModuleDirectImage :
    PreservesFiniteLimits (zariskiModuleDirectImage S) :=
  inferInstanceAs (PreservesFiniteLimits
    (moduleRingULiftUp S ⋙ zariskiModuleDirectImageULift S))

/-! ### The target category is abelian with enough injectives -/

/-- **Sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules on the small Zariski site of `X` form an
abelian category** at the module universe `u + 1`.  The opens of `X` form a `Type u` with
morphisms in `Type u` and the ring coefficients are `RingCat.{u + 1}`, so the ambient universe of
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is `max u u (u + 1) u = u + 1`. -/
instance instAbelianZariskiModuleSheaf : Abelian (ZariskiModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u, u, u + 1, u}
    (zariskiPushforwardStructureSheaf S)

/-- **Sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules on the small Zariski site of `X` have enough
injectives**, so right derived functors out of that category exist. -/
instance instEnoughInjectivesZariskiModuleSheaf : EnoughInjectives (ZariskiModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u, u, u + 1, u}
    (zariskiPushforwardStructureSheaf S)

/-! ### `R^j u_{X/S, *}` on modules -/

/-- **The module-valued higher direct image
`R^j u_{X/S, *} : Mod(𝒪_{X/S}) ⥤ Mod(u_{X/S, *}𝒪_{X/S})`**, the `j`-th right derived functor of
`zariskiModuleDirectImage`.  It exists because that functor is additive and both categories are
abelian with the source having enough injectives, by
`Crystalline.GlobalCrystallineSituation.SmallSite.instEnoughInjectivesModuleSheaf`. -/
def higherZariskiModuleDirectImage (j : ℕ) : ModuleSheaf S ⥤ ZariskiModuleSheaf S :=
  (zariskiModuleDirectImage S).rightDerived j

/-- **`R^j u_{X/S, *}I = 0` for `j > 0` and `I` an injective sheaf of `𝒪_{X/S}`-modules.** -/
theorem isZero_higherZariskiModuleDirectImage_of_injective (F : ModuleSheaf S) [Injective F]
    (j : ℕ) :
    IsZero ((higherZariskiModuleDirectImage S (j + 1)).obj F) :=
  (zariskiModuleDirectImage S).isZero_rightDerived_obj_injective_succ j F

/-- **`R^0 u_{X/S, *} ≅ u_{X/S, *}` on modules.**  The module-valued direct image is left exact,
by `preservesFiniteLimits_zariskiModuleDirectImage`, so nothing is lost in degree zero. -/
def higherZariskiModuleDirectImageZeroIso :
    higherZariskiModuleDirectImage S 0 ≅ zariskiModuleDirectImage S :=
  (zariskiModuleDirectImage S).rightDerivedZeroIsoSelf

/-! ### `Ru_{X/S, *}` on modules -/

/-- **A derived category of the sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules exists**, with its
morphisms in `Type (u + 2)`.  As everywhere in this chapter,
`CategoryTheory.HasDerivedCategory.standard` applies to any abelian category and places the
morphisms of the localization one universe up; it is not registered globally. -/
@[instance_reducible]
def hasDerivedCategoryZariskiModuleSheaf :
    HasDerivedCategory.{u + 2} (ZariskiModuleSheaf S) :=
  HasDerivedCategory.standard _

section Derived

variable [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w'} (ZariskiModuleSheaf S)]

/-- **The module-valued derived direct image
`Ru_{X/S, *} : D⁺(Mod(𝒪_{X/S})) ⥤ D⁺(Mod(u_{X/S, *}𝒪_{X/S}))`**, as a functor between bounded
below derived categories.  It is the right derived functor of `zariskiModuleDirectImage`. -/
def derivedZariskiModuleDirectImageFunctor :
    DerivedCategory.Plus (ModuleSheaf S) ⥤ DerivedCategory.Plus (ZariskiModuleSheaf S) :=
  (zariskiModuleDirectImage S).rightDerivedFunctorPlus

/-- **`Ru_{X/S, *}F` for a single sheaf of `𝒪_{X/S}`-modules `F`**: the module placed in degree
zero, then the derived direct image. -/
def derivedZariskiModuleDirectImage :
    ModuleSheaf S ⥤ DerivedCategory.Plus (ZariskiModuleSheaf S) :=
  DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0 ⋙
    derivedZariskiModuleDirectImageFunctor S

/-- Taking the degree-`j` cohomology of `Ru_{X/S, *}` is the `ℤ`-indexed `R^j u_{X/S, *}`, by
definition of the latter. -/
theorem derivedZariskiModuleDirectImage_comp_homologyFunctor (j : ℤ) :
    derivedZariskiModuleDirectImage S ⋙
        DerivedCategory.Plus.homologyFunctor (ZariskiModuleSheaf S) j =
      (zariskiModuleDirectImage S).rightDerivedPlus j :=
  rfl

/-- **`Ru_{X/S, *}I` is concentrated in degree zero for `I` an injective sheaf of
`𝒪_{X/S}`-modules**, the derived-category form of
`isZero_higherZariskiModuleDirectImage_of_injective`. -/
theorem isZero_homology_derivedZariskiModuleDirectImage_of_injective
    (F : ModuleSheaf S) [Injective F] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ZariskiModuleSheaf S) j).obj
      ((derivedZariskiModuleDirectImage S).obj F)) :=
  Functor.isZero_rightDerivedPlus_obj_injective (zariskiModuleDirectImage S) j hj F

/-- **`H^0(Ru_{X/S, *} -) ≅ u_{X/S, *}` on modules**, the derived-category form of
`higherZariskiModuleDirectImageZeroIso`.  The comparison of the `ℤ`-indexed cohomology of
`Ru_{X/S, *}` with Mathlib's `ℕ`-indexed right derived functor is
`Stacks.DerivedIndexing.rightDerivedIso`. -/
def homologyZeroDerivedZariskiModuleDirectImageIso :
    derivedZariskiModuleDirectImage S ⋙
        DerivedCategory.Plus.homologyFunctor (ZariskiModuleSheaf S) ((0 : ℕ) : ℤ) ≅
      zariskiModuleDirectImage S :=
  (Stacks.DerivedIndexing.rightDerivedIso (zariskiModuleDirectImage S) 0).symm ≪≫
    (zariskiModuleDirectImage S).rightDerivedZeroIsoSelf

end Derived

/-! ### The same three functors at the module universe of the chapter's predicates

The chapter's crystal and quasi-coherence predicates quantify over
`SheafOfModules.{u} (structureSheaf S)`, whose lift along
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULift` is a `ModuleSheaf S`.  The three
functors below are the ones above read there, exactly as
`...moduleULiftCohomology` and `...moduleULiftDerivedGlobalSections` are for global sections. -/

/-- **`u_{X/S, *}F` for a sheaf of `𝒪_{X/S}`-modules at the universe of the chapter's crystal and
quasi-coherence predicates**, valued in sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules. -/
def moduleULiftZariskiModuleDirectImage :
    SheafOfModules.{u} (structureSheaf S) ⥤ ZariskiModuleSheaf S :=
  moduleULift S ⋙ zariskiModuleDirectImage S

/-- **`R^j u_{X/S, *}F` for a sheaf of `𝒪_{X/S}`-modules at the universe of the chapter's crystal
and quasi-coherence predicates.** -/
def moduleULiftHigherZariskiModuleDirectImage (j : ℕ) :
    SheafOfModules.{u} (structureSheaf S) ⥤ ZariskiModuleSheaf S :=
  moduleULift S ⋙ higherZariskiModuleDirectImage S j

/-- **The abelian sheaf underlying `u_{X/S, *}F`, for `F` at the universe of the chapter's crystal
and quasi-coherence predicates, is the abelian direct image of
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf F`** — the very abelian sheaf the
chapter's abelian-valued assertions are about, and the value of
`...moduleZariskiDirectImage` of `SmallSite/ZariskiRingedComparison.lean`. -/
theorem toSheaf_obj_moduleULiftZariskiModuleDirectImage
    (F : SheafOfModules.{u} (structureSheaf S)) :
    (SheafOfModules.toSheaf.{u + 1} (zariskiPushforwardStructureSheaf S)).obj
        ((moduleULiftZariskiModuleDirectImage S).obj F) =
      (moduleZariskiDirectImage S).obj F :=
  toSheaf_obj_zariskiModuleDirectImage S ((moduleULift S).obj F)

/-- **`Ru_{X/S, *}F` for a sheaf of `𝒪_{X/S}`-modules at the universe of the chapter's crystal and
quasi-coherence predicates**, an object of `D⁺(Mod(u_{X/S, *}𝒪_{X/S}))`. -/
def moduleULiftDerivedZariskiModuleDirectImage
    [HasDerivedCategory.{w} (ModuleSheaf S)]
    [HasDerivedCategory.{w'} (ZariskiModuleSheaf S)] :
    SheafOfModules.{u} (structureSheaf S) ⥤ DerivedCategory.Plus (ZariskiModuleSheaf S) :=
  moduleULift S ⋙ derivedZariskiModuleDirectImage S

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
