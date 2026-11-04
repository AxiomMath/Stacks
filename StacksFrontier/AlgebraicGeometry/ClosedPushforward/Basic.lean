module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Deformation.ToposThickening.RestrictScalarsEssentialImage

/-!
# Direct image along a closed quotient morphism is fully faithful, with known essential image

Let `i : Z ⟶ X` be a morphism of ringed spaces which is a homeomorphism onto a closed subset
and whose comorphism `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective, and let `ℐ = ker i^♯`. Then
[Stacks, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS) asserts that

1. `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is exact;
2. `i_*` is fully faithful;
3. the essential image of `i_*` consists of the `𝒪_X`-modules `𝒢` with `ℐ𝒢 = 0`.

Clause (1) is
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`. This file proves
clauses (2) and (3), and transports both to a closed immersion of schemes, where the
direct image is Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward` — the two functors
are *equal*, not merely isomorphic.

## Main results

In the namespace `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`:

* `fullyFaithfulModulePushforward`: the direct image `i_*` is fully faithful.
* `modulePushforward_essImage_iff`: `𝒢` is a direct image exactly when every section of the
  kernel ideal annihilates every section of `𝒢`.

For a closed immersion of schemes:

* `Stacks.ClosedImmersion.full_pushforward`, `Stacks.ClosedImmersion.faithful_pushforward`,
  `Stacks.ClosedImmersion.pushforward_essImage_iff`: the same two clauses for
  `AlgebraicGeometry.Scheme.Modules.pushforward`.
* `Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`: for a module annihilated by the
  comorphism's kernel, the unit `M ⟶ i_* i^* M` of the pullback–pushforward adjunction is an
  isomorphism.
* `Stacks.ClosedImmersion.epi_unit_app`: for *every* module the same unit is an epimorphism.
  `i_* i^* M` is the quotient of `M` by the ideal of the closed subscheme, so no hypothesis on
  `M` is needed; the clause above is the case where that quotient map is injective as well.

## Implementation notes

Unlike the source's proof, nothing here is a stalkwise argument.

The direct image factors, *by definition* (`modulePushforward_eq`, a `rfl`), as

    Mod(𝒪_Z) --modulePushforwardPushedRing--> Mod(i_* 𝒪_Z) --restrictScalars i^♯--> Mod(𝒪_X)

and each clause is the conjunction of the corresponding statement about the two factors.

*The second factor.* Restriction of scalars along a locally surjective morphism of sheaves of
rings is fully faithful (`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`,
whose inverse on morphisms is Mathlib's
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`) and its essential image is exactly
the modules annihilated sectionwise by the kernel
(`Deformation.ToposThickening.essImage_restrictScalars_iff`). The latter is stated for an
arbitrary site and an arbitrary locally surjective morphism of sheaves of rings, so it applies
to `Opens X` verbatim; it is *not* merely a topos-level analogue of what is wanted here.

*The first factor.* It is essentially surjective because the counit of the descent adjunction is
an isomorphism (`moduleDescendCompPushforwardIso`), and `Functor.essImage_comp_of_essSurj` then
says the composite's essential image is the second factor's. It is fully faithful because the
*unit* of the underlying presheaf-level adjunction is an isomorphism, which is the one new
computation here and is cheap: the unit's component at `V` is `N.map` of the counit of
`opensMap i ⊣ opensFunctor i`, and that counit is an isomorphism because
`(opensMap i).obj ((opensFunctor i).obj V) = V` on the nose and `Opens Z` is a partial order,
so its two coherence squares are `Subsingleton.elim`.

Universes: `Deformation.ToposThickening.essImage_restrictScalars_iff` ties the module universe
to the universe of the sheaves of rings, so everything here is at the space universe `u`. That
is no restriction for the intended consumers: `RingedSpaceModuleAdjunction.modulePushforward`
and `AlgebraicGeometry.Scheme.Modules` are both at `u` already.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The comorphism of a closed quotient morphism is locally surjective as a morphism of sheaves
of rings. This is the defining field `isLocallySurjective` read through the forgetful functor
`CommRingCat ⥤ RingCat`, which changes neither the underlying sheaves of sets nor therefore
local surjectivity. -/
theorem structureSheafHom_isLocallySurjective :
    Sheaf.IsLocallySurjective (structureSheafHom S.i) := by
  have h0 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S.X.carrier)
      (((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace
        (C := CommRingCat)).map S.i).c) := S.isLocallySurjective
  have h1 := (Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 h0
  exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2 h1

/-- Membership in the kernel ideal is membership in the kernel of the comorphism read as a
morphism of sheaves of rings. The two are the same subset of the same ring: `kernelIdeal` is
the kernel of the `CommRingCat`-valued comorphism and the forgetful functor to `RingCat`
changes no carrier. -/
theorem mem_kernelIdeal_iff_mem_ker_structureSheafHom {U : (Opens S.X)ᵒᵖ}
    (a : (structureSheafRing S.X).obj.obj U) :
    a ∈ RingHom.ker ((structureSheafHom S.i).hom.app U).hom ↔ a ∈ S.kernelIdeal U.unop :=
  Iff.rfl

/-- The counit of `opensMap i ⊣ opensFunctor i` is an isomorphism: `i⁻¹(i_! V) = V`, and
`Opens Z` is a partial order, so the inverse and the two coherence squares are forced. -/
theorem isIso_opensAdjunction_counit (V : Opens S.Z) :
    IsIso (S.opensAdjunction.counit.app V) :=
  ⟨eqToHom (S.opensMap_opensFunctor_obj V).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The unit of the presheaf-level descent adjunction is an isomorphism. Its component at a
presheaf of modules `N` and an open `V` of `Z` is `N.map` of the counit of
`opensMap i ⊣ opensFunctor i` at `V`, which is an isomorphism; and
`PresheafOfModules.toPresheaf` reflects isomorphisms. -/
theorem isIso_descendPresheafAdjunction_unit :
    IsIso S.descendPresheafAdjunction.{u, u}.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((PresheafOfModules.toPresheaf (structureSheafRing S.Z).obj).map
      (S.descendPresheafAdjunction.unit.app N)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [show ((PresheafOfModules.toPresheaf _).map
        (S.descendPresheafAdjunction.unit.app N)).app V =
        N.presheaf.map (S.opensAdjunction.counit.app V.unop).op from rfl]
    have := S.isIso_opensAdjunction_counit V.unop
    exact inferInstanceAs (IsIso
      (N.presheaf.mapIso (asIso (S.opensAdjunction.counit.app V.unop)).op).hom)
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf (structureSheafRing S.Z).obj)

/-- Pushforward of presheaves of modules from `Z` to `X`, over the ring `i_* 𝒪_Z`, is fully
faithful: it is a left adjoint whose unit is an isomorphism. -/
noncomputable def fullyFaithfulPushPresheaf : S.pushPresheaf.{u, u}.FullyFaithful :=
  have := S.isIso_descendPresheafAdjunction_unit
  Adjunction.fullyFaithfulLOfIsIsoUnit S.descendPresheafAdjunction

/-- Pushforward of sheaves of modules from `Z` to `X`, over the ring `i_* 𝒪_Z`, is fully
faithful. It agrees with `pushPresheaf` under the fully faithful forgetful functors to
presheaves of modules, so full faithfulness transfers along those. -/
noncomputable def fullyFaithfulModulePushforwardPushedRing :
    S.modulePushforwardPushedRing.{u, u}.FullyFaithful := by
  have h := S.fullyFaithfulPushPresheaf
  have := h.full
  have := h.faithful
  have hc : (S.modulePushforwardPushedRing.{u, u} ⋙
      SheafOfModules.forget S.pushedRingSheaf).Faithful :=
    inferInstanceAs (SheafOfModules.forget (structureSheafRing S.Z) ⋙ S.pushPresheaf).Faithful
  have hcf : (S.modulePushforwardPushedRing.{u, u} ⋙
      SheafOfModules.forget S.pushedRingSheaf).Full :=
    inferInstanceAs (SheafOfModules.forget (structureSheafRing S.Z) ⋙ S.pushPresheaf).Full
  have := Functor.Faithful.of_comp S.modulePushforwardPushedRing.{u, u}
    (SheafOfModules.forget S.pushedRingSheaf)
  have := Functor.Full.of_comp_faithful S.modulePushforwardPushedRing.{u, u}
    (SheafOfModules.forget S.pushedRingSheaf)
  exact .ofFullyFaithful _

/-- Pushforward of sheaves of modules over the ring `i_* 𝒪_Z` is essentially surjective: the
counit of the descent adjunction is an isomorphism, so every `i_* 𝒪_Z`-module on `X` is the
pushforward of its descent. -/
instance essSurj_modulePushforwardPushedRing : S.modulePushforwardPushedRing.{u, u}.EssSurj where
  mem_essImage M := ⟨S.moduleDescend.obj M, ⟨S.moduleDescendCompPushforwardIso.app M⟩⟩

/-- The direct image is fully faithful, as the composite of the two fully faithful factors. -/
private noncomputable def fullyFaithfulModulePushforwardAux :
    (modulePushforward S.i).FullyFaithful :=
  have := S.structureSheafHom_isLocallySurjective
  S.fullyFaithfulModulePushforwardPushedRing.comp
    (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (structureSheafHom S.i))

/-- **[Stacks, Tag 08KS], full faithfulness** (faithfulness half). -/
theorem faithful_modulePushforward : (modulePushforward S.i).Faithful :=
  S.fullyFaithfulModulePushforwardAux.faithful

/-- **[Stacks, Tag 08KS], full faithfulness** (fullness half). -/
theorem full_modulePushforward : (modulePushforward S.i).Full :=
  S.fullyFaithfulModulePushforwardAux.full

/-- **[Stacks, Tag 08KS], full faithfulness.** The direct image
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` along a homeomorphism onto a closed subset with surjective
comorphism is fully faithful. -/
@[stacks 08KS "full faithfulness"]
noncomputable def fullyFaithfulModulePushforward : (modulePushforward S.i).FullyFaithful :=
  have := S.full_modulePushforward
  have := S.faithful_modulePushforward
  .ofFullyFaithful _

/-- **[Stacks, Tag 08KS], the essential image.** An `𝒪_X`-module `𝒢` is a direct image
`i_* ℱ` exactly when `ℐ𝒢 = 0`, i.e. when every section of the kernel ideal `ℐ = ker i^♯` over
an open `U` annihilates every section of `𝒢` over `U`. -/
@[stacks 08KS "the essential image"]
theorem modulePushforward_essImage_iff (M : SheafOfModules.{u} (structureSheafRing S.X)) :
    (modulePushforward S.i).essImage M ↔
      ∀ (U : Opens S.X) (a : (structureSheafRing S.X).obj.obj (op U)), a ∈ S.kernelIdeal U →
        ∀ m : M.val.obj (op U), a • m = 0 := by
  have := S.structureSheafHom_isLocallySurjective
  rw [show (modulePushforward S.i).essImage M ↔ _ from
    Iff.of_eq (congrFun (Functor.essImage_comp_of_essSurj
      (F := S.modulePushforwardPushedRing.{u, u})
      (G := SheafOfModules.restrictScalars (structureSheafHom S.i))) M)]
  refine (Deformation.ToposThickening.essImage_restrictScalars_iff
    (structureSheafHom S.i) M).trans ?_
  exact ⟨fun h U a ha m => h (op U) a ha m, fun h U a ha m => h U.unop a ha m⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

variable [AlgebraicGeometry.IsClosedImmersion i]

/-- **[Stacks, Tag 08KS], full faithfulness, for schemes** (faithfulness half). -/
theorem faithful_pushforward : (Scheme.Modules.pushforward i).Faithful :=
  (closedQuotientOfClosedImmersion i).faithful_modulePushforward

/-- **[Stacks, Tag 08KS], full faithfulness, for schemes** (fullness half). -/
theorem full_pushforward : (Scheme.Modules.pushforward i).Full :=
  (closedQuotientOfClosedImmersion i).full_modulePushforward

/-- **[Stacks, Tag 08KS], full faithfulness, for a closed immersion of schemes.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforward` along a closed immersion is fully faithful: it
is literally `RingedSpaceModuleAdjunction.modulePushforward` of the underlying morphism of
ringed spaces.

The `@[stacks 08KS]` attribute sits on the ringed-space form
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.fullyFaithfulModulePushforward`,
which is the tag's own generality; this is its specialization to schemes. -/
noncomputable def fullyFaithfulPushforward : (Scheme.Modules.pushforward i).FullyFaithful :=
  (closedQuotientOfClosedImmersion i).fullyFaithfulModulePushforward

/-- **[Stacks, Tag 08KS], the essential image, for a closed immersion of schemes.** A sheaf of
modules `M` on `X` is a direct image along `i` exactly when the kernel of the comorphism
`i^♯` annihilates it section by section: for every open `U`, every function on `U` that dies
under `i^♯` kills every section of `M` over `U`.

Both the scalars and the sections are spelled with `Γ`, which is the spelling the `Module`
instance is found at and the one `AlgebraicGeometry.zeroScheme_ideal_of_trivialization` and the
rest of the Chapter 31 API use. Mixing the two available spellings — `Γ(X, U)` scalars acting
on `M.val.obj (op U)`, the `ModuleCat` object — is what fails to elaborate; either spelling on
its own is fine, and the two conditions are interchangeable by `Iff.rfl`.

The `@[stacks 08KS]` attribute sits on the ringed-space form
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.modulePushforward_essImage_iff`,
which is the tag's own generality; this is its specialization to schemes. -/
theorem pushforward_essImage_iff (M : X.Modules) :
    (Scheme.Modules.pushforward i).essImage M ↔
      ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0 :=
  (closedQuotientOfClosedImmersion i).modulePushforward_essImage_iff M

/-- **The consumer-facing form of [Stacks, Tag 08KS].** If the kernel of the comorphism of a
closed immersion `i` annihilates `M` section by section, then the unit
`M ⟶ i_* i^* M` of the pullback–pushforward adjunction is an isomorphism.

This is what identifies `i_* i^* M` with `M` itself; combined with exactness of `i_*` it is
the form in which 08KS is used to compute cokernels on a closed subscheme. -/
theorem isIso_unit_app_of_smul_eq_zero (M : X.Modules)
    (h : ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 → ∀ m : Γ(M, U), a • m = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) := by
  have := faithful_pushforward i
  have := full_pushforward i
  exact (Adjunction.isIso_unit_app_iff_mem_essImage
    (Scheme.Modules.pullbackPushforwardAdjunction i)).mpr
      ((pushforward_essImage_iff i M).mpr h)

/-- **The unit of `i^* ⊣ i_*` along a closed immersion is an epimorphism**, at every
`𝒪_X`-module, with no hypothesis on the module: `i_* i^* M` is the quotient of `M` by the ideal
of the closed subscheme.

This is a consequence of [Stacks, Tag 08KS] and needs no stalkwise computation. The target
`i_* i^* M` is a direct image, hence annihilated by the kernel of the comorphism
(`Stacks.ClosedImmersion.pushforward_essImage_iff`); so is the image `E` of the unit, being a
submodule of it; so `E` is itself a direct image `i_* E₀`, and the inclusion `E ⟶ i_* i^* M` is
`i_*` of some `e₀ : E₀ ⟶ i^* M` because `i_*` is full. Transposing the projection
`M ⟶ E = i_* E₀` across the adjunction gives `p₀ : i^* M ⟶ E₀` with
`η_M ≫ i_*(p₀ ≫ e₀) = η_M`, and `η_M` is the image of `𝟙` under the hom-set bijection, so
`p₀ ≫ e₀ = 𝟙`. Thus `i_*(e₀)` is a split epimorphism, and the unit, which factors as the
projection onto its image followed by that inclusion, is an epimorphism. -/
theorem epi_unit_app (M : X.Modules) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) := by
  have hfull := full_pushforward i
  have hT : ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 →
      ∀ m : Γ((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj M), U), a • m = 0 :=
    (pushforward_essImage_iff i _).mp
      ((Scheme.Modules.pushforward i).obj_mem_essImage ((Scheme.Modules.pullback i).obj M))
  have hE : ∀ (U : X.Opens) (a : Γ(X, U)), (i.app U).hom a = 0 →
      ∀ m : Γ(Abelian.image ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M), U),
        a • m = 0 := by
    intro U a ha m
    refine Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono
      (Abelian.image.ι ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)) U ?_
    rw [Scheme.Modules.Hom.app_smul, map_zero]
    exact hT U a ha _
  obtain ⟨E₀, ⟨iso⟩⟩ := (pushforward_essImage_iff i _).mpr hE
  obtain ⟨e₀, he₀⟩ := (Scheme.Modules.pushforward i).map_surjective
    (iso.hom ≫ Abelian.image.ι ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M))
  obtain ⟨p₀, hp₀⟩ := ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M E₀).surjective
    (Abelian.factorThruImage ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) ≫
      iso.inv)
  rw [Adjunction.homEquiv_unit] at hp₀
  have key : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M ≫
      (Scheme.Modules.pushforward i).map (p₀ ≫ e₀) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M := by
    rw [Functor.map_comp, ← Category.assoc, hp₀, he₀, Category.assoc, Iso.inv_hom_id_assoc]
    exact Abelian.image.fac _
  have hid : p₀ ≫ e₀ = 𝟙 _ :=
    ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M _).injective (by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, key,
        CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm)
  have hfac : ((Scheme.Modules.pushforward i).map p₀ ≫ iso.hom) ≫
      Abelian.image.ι ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) = 𝟙 _ := by
    rw [Category.assoc, ← he₀, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id]
  have : Epi (Abelian.image.ι ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)) :=
    epi_of_epi_fac hfac
  rw [← Abelian.image.fac ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)]
  exact epi_comp _ _

end Stacks.ClosedImmersion

end
