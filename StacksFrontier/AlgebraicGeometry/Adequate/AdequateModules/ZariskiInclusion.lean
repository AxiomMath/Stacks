module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Cohomology
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteOpensContinuity

/-!
# The small Zariski site of the base inside a chosen big site

Let `S` be a scheme and let `B` be a chosen big `τ`-site over `S`, for `τ` any of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. The inclusion
`Stacks.Adequate.BigSite.opensToBig : S_Zar ⥤ (Sch/S)_τ` of the small Zariski site of `S` is
continuous, so it is the underlying functor of a morphism of ringed sites
`((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, and restriction along it carries `𝒪`-modules on the big site to
`𝒪_S`-modules, `𝓕 ↦ 𝓕|_{S_Zar}`, and abelian sheaves on the big site to abelian sheaves on
`S_Zar`. This is the restriction in terms of which [Stacks, Tag 06VM] (1) and (4) are stated.

## Main definitions

* `Stacks.Adequate.BigSite.zariskiStructureMap` — the comparison of structure sheaves, the
  identification of `Γ(S, U)` with the global functions of the open subscheme `U`.
* `Stacks.Adequate.BigSite.zariskiRestrictModule` — `𝓕 ↦ 𝓕|_{S_Zar}` on `𝒪`-modules.
* `Stacks.Adequate.BigSite.zariskiRestriction` — `𝓖 ↦ 𝓖|_{S_Zar}` on abelian sheaves, the
  direct image `g_*` of the morphism of sites `g : (Sch/S)_τ → S_Zar`.

## Main results

* `Stacks.Adequate.BigSite.coverPreserving_opensToBig` and
  `Stacks.Adequate.BigSite.isContinuous_opensToBig` — the inclusion is cover preserving and
  continuous, for each of the five topologies.
* `Stacks.Adequate.BigSite.zariskiRestriction_comp_zariskiGlobalSections` — global sections on
  the big site are global sections on `S_Zar` of the restriction.
* `Stacks.Adequate.BigSite.zariskiCohomologyIso` — the collapse isomorphism of the composite
  `Γ(S_Zar, −) ∘ (−)|_{S_Zar}` at a module whose higher direct images vanish.

## Implementation notes

The topology of a chosen big site is one of the five localized big-site topologies, by the field
`Stacks.Adequate.BigSite.chosen`, read as `Stacks.Adequate.BigSite.exists_eq_ofAmbient`; cover
preservation into each of those is `AlgebraicGeometry.coverPreserving_opensBelowToOver`, and the
inclusion is representably flat by `AlgebraicGeometry.representablyFlat_opensBelowToOver`, so
Mathlib's criterion gives continuity.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### Continuity of the inclusion of the small Zariski site -/

/-- **The small Zariski site of `S` is cover preserving into a chosen big `τ`-site over `S`**,
for each of the five topologies: an open covering of an open of `S` is a `τ`-covering family. -/
public theorem BigSite.coverPreserving_opensToBig (B : BigSite τ S) :
    CoverPreserving (Opens.grothendieckTopology ↥S) B.topology B.opensToBig := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  exact coverPreserving_opensBelowToOver τ 𝒮 S hS

/-- **The small Zariski site of `S` is continuous into a chosen big `τ`-site over `S`**, so it
induces a morphism of sites `(Sch/S)_τ → S_Zar` whose direct image is restriction along the
inclusion. -/
public instance BigSite.isContinuous_opensToBig (B : BigSite τ S) :
    B.opensToBig.IsContinuous (Opens.grothendieckTopology ↥S) B.topology :=
  Functor.isContinuous_iff_coverPreserving.2 B.coverPreserving_opensToBig

/-! ### The morphism of ringed sites and restriction of modules -/

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S` into
a chosen big site over `S`: over an open `U` it is the identification of `Γ(S, U)` with the
global functions of the open subscheme `U`. Together with the continuity of the inclusion this
is the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def BigSite.zariskiStructureMap (B : BigSite τ S) :
    S.ringCatSheaf ⟶ (B.opensToBig.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) B.topology).obj B.structureSheaf where
  hom :=
    { app := fun U => (CategoryTheory.forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso U.unop).inv
      naturality := fun U V h => by
        dsimp
        exact (((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
          ((congrArg _ (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm).trans
            ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map_comp _ _))) }

/-- **Restriction `𝓕 ↦ 𝓕|_{S_Zar}` of an `𝒪`-module on a chosen big site over `S` to the small
Zariski site of `S`**: the pushforward of sheaves of modules along the morphism of ringed sites
`((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`. The sections of `𝓕|_{S_Zar}` over an open `U` are the sections
of `𝓕` over the open subscheme `U`, by definition. -/
public noncomputable def BigSite.zariskiRestrictModule (B : BigSite τ S) :
    SheafOfModules.{u} B.structureSheaf ⥤ S.Modules :=
  SheafOfModules.pushforward.{u} B.zariskiStructureMap

/-! ### Restriction of abelian sheaves -/

/-- Restriction of abelian sheaves from a chosen big site over `S` to the small Zariski site of
`S`, the direct image `g_*` of the morphism of sites `g : (Sch/S)_τ → S_Zar`. -/
public noncomputable abbrev BigSite.zariskiRestriction (B : BigSite τ S) :
    Sheaf B.topology AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u} :=
  B.opensToBig.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥S) B.topology

/-- Restriction to the small Zariski site is additive. -/
public noncomputable instance BigSite.zariskiRestriction_additive (B : BigSite τ S) :
    B.zariskiRestriction.Additive :=
  ⟨rfl⟩

/-- **Global sections on a chosen big site over `S` are global sections on the small Zariski site
of `S` of the restriction.** Restriction along a continuous functor is restriction of sections,
so the composite is sections over the image of `⊤`, which is the object of the big site over
which global sections are taken. -/
public theorem BigSite.zariskiRestriction_comp_zariskiGlobalSections (B : BigSite τ S) :
    B.zariskiRestriction ⋙ zariskiGlobalSections S = B.globalSections :=
  rfl

/-- The abelian sheaf underlying the restriction of an `𝒪`-module to the small Zariski site is the
restriction of the abelian sheaf underlying the module. -/
public theorem BigSite.toSheaf_zariskiRestrictModule (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) :
    (SheafOfModules.toSheaf S.ringCatSheaf).obj (B.zariskiRestrictModule.obj F) =
      B.zariskiRestriction.obj ((SheafOfModules.toSheaf B.structureSheaf).obj F) :=
  rfl

/-! ### The collapse of the composite -/

section Collapse

variable (B : BigSite τ S) [HasSheafify B.topology AddCommGrpCat.{u}]
  [EnoughInjectives (Sheaf B.topology AddCommGrpCat.{u})]

/-- The vanishing of the higher direct images `R^q g_* F` for `q > 0` of an adequate
`𝒪`-module `F` along the morphism of sites `g : (Sch/S)_τ → S_Zar`. -/
public abbrev BigSite.HigherZariskiRestrictionVanishing
    (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  IsAdequate B F → ∀ n, 0 < n →
    IsZero ((B.zariskiRestriction.rightDerived n).obj
      ((SheafOfModules.toSheaf B.structureSheaf).obj F))

/-- **The collapse of the composite `Γ(S_Zar, −) ∘ (−)|_{S_Zar}` at an adequate module.** For an
adequate `𝒪`-module `F` on a chosen big site over `S` whose higher direct images along the
inclusion of the small Zariski site vanish, the canonical isomorphism

`H^q((Sch/S)_τ, F) ≅ H^q(S, F|_{S_Zar})`

in every degree `q`, where cohomology is the right derived functor of global sections. Global
sections on the big site are global sections on the small Zariski site of the restriction, so
the two sides are compared by the Grothendieck edge isomorphism `Stacks.RightDerivedComp.objIso`.
-/
public noncomputable def BigSite.zariskiCohomologyIso
    [B.zariskiRestriction.PreservesInjectiveObjects]
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F)
    (h03DW : B.HigherZariskiRestrictionVanishing F) (q : ℕ) :
    (B.globalSections.rightDerived q).obj ((SheafOfModules.toSheaf B.structureSheaf).obj F) ≅
      ((zariskiGlobalSections S).rightDerived q).obj
        (B.zariskiRestriction.obj ((SheafOfModules.toSheaf B.structureSheaf).obj F)) :=
  Stacks.RightDerivedComp.objIso B.zariskiRestriction
    (InjectiveResolution.of ((SheafOfModules.toSheaf B.structureSheaf).obj F)) (h03DW hF)
    (zariskiGlobalSections S) q

end Collapse

end Stacks.Adequate

end
