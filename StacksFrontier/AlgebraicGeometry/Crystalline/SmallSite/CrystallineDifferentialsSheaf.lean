module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTensorFormsAmbient
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence

/-!
# The sheaf `Ω_{X/S}` on the small crystalline site and its restriction to `T`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  The module of
differentials `Ω_{X/S}` of [Stacks, Section 60.12] is a *sheaf* of `𝒪_{X/S}`-modules on the
crystalline site `Cris(X/S)`, carrying a universal `S`-derivation `d_{X/S} : 𝒪_{X/S} → Ω_{X/S}`
([Stacks, Tag 07IX]): it is the sheaf associated with the presheaf
`(U, T, δ) ↦ Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}` of divided power differentials, `d_{X/S}` being the
universal derivation of that presheaf followed by the sheafification map.  This file constructs it
on the small crystalline site `Cris(X/S)` of [Stacks, Tag 07IG], proves its universal property
among `S`-derivations into sheaves, and proves [Stacks, Tag 07IZ]: for an object `(U, T, δ)` of
`Cris(X/S)` the restriction `(Ω_{X/S})_T` to `T_Zar` is the sheaf `Ω_{T/S,δ}` of divided power
differentials of `T` over `S`, and the restriction of `d_{X/S}` is `d_{T/S,δ}`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysAssocSheaf` and `toCrysAssocSheaf` — the sheaf of `𝒪_{X/S}`-modules associated with a
  presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`, with its sections in `Type u`, and the
  sheafification morphism; `crysAssocSheafDesc` extends a morphism into a sheaf over it.
* `crysDifferentialsSheaf` — **the sheaf `Ω_{X/S}`**, and `toCrysDifferentialsSheaf` the morphism
  from the presheaf of divided power differentials.
* `SDerivation` — an `S`-derivation of `𝒪_{X/S}` into a presheaf of `𝒪_{X/S}`-modules on
  `Cris(X/S)`, [Stacks, Tag 07IX].
* `crysSheafSDerivation` — **the universal `S`-derivation `d_{X/S} : 𝒪_{X/S} → Ω_{X/S}`**, with
  `crysSheafD` its maps on sections.
* `crysDifferentialsSheafRestriction` — the restriction `(Ω_{X/S})_T`, a sheaf of `𝒪_T`-modules
  on the ambient scheme `T` of an object, `SmallSite.ambientModuleRestriction` of `Ω_{X/S}`.
* `crysDifferentialsSheafRestrictionIso` — **[Stacks, Tag 07IZ]:
  `Ω_{T/S,δ} ≅ (Ω_{X/S})_T`** as sheaves of `𝒪_T`-modules.

## Main results

* `crysSheafSDerivation_isUniversal` — every `S`-derivation of `𝒪_{X/S}` into a sheaf of
  `𝒪_{X/S}`-modules factors uniquely through `d_{X/S}`.
* `crysDifferentialsSheafRestrictionIso_hom_app_d` — **[Stacks, Tag 07IZ]:
  `d_{X/S}|_T = d_{T/S,δ}`**: the isomorphism carries `d_{T/S,δ} b` to `d_{X/S} b` for every
  local section `b` of `𝒪_T`.

## Implementation notes

The objects of `Cris(X/S)` form a `Type (u + 1)`, so sheafification of presheaves with sections in
`Type u` is not available there directly.  As for the higher forms in
`SmallSite/DifferentialFormsSheaf.lean`, the presheaf is sheafified at the module universe
`u + 1` and the result is shrunk: over `(U, T, δ)` its sections are the sections over `T` of a
Zariski sheafification, by `...SmallSite.CrystallineThickening.restrictOpenSheafifyIso`, hence
`u`-small.  The universal property of the sheafification is transported along the shrinking with
`Stacks.SheafOfModules.moduleULiftFullyFaithful`.

[Stacks, Tag 07IZ] follows from the presheaf-level identification
`Crystalline.GlobalCrystallineSituation.comparisonIso` of the restriction of the presheaf of
differentials with the presheaf of divided power differentials of `T`, and from the fact that the
restriction to `T` of the sheafification morphism is Zariski-locally injective and surjective
(cocontinuity of the restrictions of an object to the opens of its ambient scheme): the composite
`Ω^{pre}_{T/S,δ} → (Ω_{X/S})_T` is a locally bijective morphism into a sheaf of `𝒪_T`-modules, so
its transpose out of the sheafification `Ω_{T/S,δ}` is an isomorphism.

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The sheaf associated with a presheaf of `𝒪_{X/S}`-modules, at the module universe `u` -/

section AssocSheaf

variable (P : PresheafOfModules.{u} (structureSheaf S).obj)

/-- A presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` with its sections raised to `Type (u + 1)`. -/
abbrev presheafULiftU : PresheafOfModules.{u + 1} (structureSheaf S).obj :=
  (Stacks.SheafOfModules.presheafULift.{u + 1} (structureSheaf S).obj).obj P

/-- The sheaf of `𝒪_{X/S}`-modules associated with a presheaf of `𝒪_{X/S}`-modules, at the module
universe `u + 1`, where sheafification on `Cris(X/S)` exists. -/
def crysAssocSheafULift : ModuleSheaf S :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf S).obj)).obj (presheafULiftU P)

/-- The restriction of a presheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object, as an
abelian presheaf. -/
abbrev restrictionPresheafU (A : CrystallineThickening S) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (CrystallineThickening.restrictOpenFunctor A).op ⋙ P.presheaf

/-- The Zariski sheafification of `restrictionPresheafU P A`, raised to `AddCommGrpCat.{u + 1}`. -/
abbrev restrictionSheafULift (A : CrystallineThickening S) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((presheafToSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    AddCommGrpCat.{u}).obj (restrictionPresheafU P A)).obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1}

/-- The Zariski sheafification unit of `restrictionPresheafU P A`, raised to
`AddCommGrpCat.{u + 1}`. -/
abbrev restrictionToSheafULift (A : CrystallineThickening S) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ (presheafULiftU P).presheaf ⟶
      restrictionSheafULift P A :=
  Functor.whiskerRight (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (restrictionPresheafU P A)) AddCommGrpCat.uliftFunctor.{u + 1}

/-- The lifted Zariski sheafification unit is locally injective. -/
instance isLocallyInjective_restrictionToSheafULift (A : CrystallineThickening S) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (restrictionToSheafULift P A) :=
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (toSheafify _ (restrictionPresheafU P A)) :=
    GrothendieckTopology.W.isLocallyInjective (GrothendieckTopology.W_toSheafify _ _)
  Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor _

/-- The lifted Zariski sheafification unit is locally surjective. -/
instance isLocallySurjective_restrictionToSheafULift (A : CrystallineThickening S) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (restrictionToSheafULift P A) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (toSheafify _ (restrictionPresheafU P A)) :=
    GrothendieckTopology.W.isLocallySurjective (GrothendieckTopology.W_toSheafify _ _)
  Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor _

/-- The restriction of `crysAssocSheafULift P` to the ambient scheme of an object is the universe
lift of the Zariski sheafification of the restriction of `P`. -/
def crysAssocSheafULiftRestrictionIso (A : CrystallineThickening S) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ (crysAssocSheafULift P).val.presheaf ≅
      restrictionSheafULift P A :=
  haveI := isLocallyInjective_toSheafify (presheafULiftU P).presheaf
  haveI := isLocallySurjective_toSheafify (presheafULiftU P).presheaf
  CrystallineThickening.restrictOpenSheafifyIso A
    (toSheafify (smallTopology S) (presheafULiftU P).presheaf)
    (Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor
      ((presheafToSheaf _ AddCommGrpCat.{u}).obj (restrictionPresheafU P A)).property)
    (crysAssocSheafULift P).isSheaf (restrictionToSheafULift P A)

/-- **The sections of `crysAssocSheafULift P` are `u`-small**: over `(U, T, δ)` they are the
sections over `T` of the universe lift of a Zariski sheaf with sections in `Type u`. -/
instance small_crysAssocSheafULift_obj (X : (CrystallineThickening S)ᵒᵖ) :
    Small.{u} ((crysAssocSheafULift P).val.obj X) := by
  have := CrystallineThickening.isIso_restrictOpenHom_top X.unop
  let e₁ := (crysAssocSheafULift P).val.presheaf.mapIso (asIso (X.unop.restrictOpenHom ⊤)).op
  let e₂ := (crysAssocSheafULiftRestrictionIso P X.unop).app (op ⊤)
  have : Small.{u} ((restrictionSheafULift P X.unop).obj (op ⊤)) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} _))
  exact small_map ((e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.toEquiv)

/-- **The sheaf of `𝒪_{X/S}`-modules associated with a presheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)`, with its sections in `Type u`**: the shrinking of `crysAssocSheafULift P`. -/
def crysAssocSheaf : SheafOfModules.{u} (structureSheaf S) :=
  Stacks.SheafOfModules.sheafShrink.{u, u + 1} (structureSheaf S) (crysAssocSheafULift P)

/-- The unit of the sheafification of the lifted presheaf, as a morphism of presheaves of
modules. -/
abbrev crysAssocSheafULiftUnit :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf S).obj)).unit.app
    (presheafULiftU P)

/-- **The canonical morphism from a presheaf of `𝒪_{X/S}`-modules to its associated sheaf**: the
sheafification map, read at the module universe `u`. -/
def toCrysAssocSheaf : P ⟶ (crysAssocSheaf P).val :=
  letI e := fun X : (CrystallineThickening S)ᵒᵖ ↦
    Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj X : Type (u + 1)))
  PresheafOfModules.homMk
    { app X := AddCommGrpCat.ofHom ((e X).symm.toAddMonoidHom.comp
          (((crysAssocSheafULiftUnit P).app X).hom.toAddMonoidHom.comp
            (AddEquiv.ulift.{u, u + 1}).symm.toAddMonoidHom))
      naturality X Y f := by
        ext x
        apply (e Y).injective
        refine ((e Y).apply_symm_apply _).trans ?_
        refine Eq.trans ?_ ((e Y).apply_symm_apply _).symm
        refine Eq.trans ?_ (congrArg _ ((e X).apply_symm_apply _).symm)
        exact PresheafOfModules.naturality_apply (crysAssocSheafULiftUnit P) f (ULift.up x) }
    (fun X r m ↦
      (congrArg (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj X : Type (u + 1)))).symm
        (((crysAssocSheafULiftUnit P).app X).hom.map_smul r (ULift.up m))).trans
      ((Shrink.linearEquiv ((structureSheaf S).obj.obj X)
        ((crysAssocSheafULift P).val.obj X : Type (u + 1))).symm.map_smul r _))

/-- `toCrysAssocSheaf P` on a section `m` over `X`: the shrinking of the sheafification unit of
the lifted presheaf applied to `ULift.up m`. -/
theorem toCrysAssocSheaf_app_apply (X : (CrystallineThickening S)ᵒᵖ) (m : P.obj X) :
    (toCrysAssocSheaf P).app X m =
      (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj X : Type (u + 1)))).symm
        (((crysAssocSheafULiftUnit P).app X).hom (ULift.up m)) := rfl

/-- **`toCrysAssocSheaf P`, restricted to the ambient scheme of an object, is locally
injective.** -/
theorem isLocallyInjective_restrict_toCrysAssocSheaf (A : CrystallineThickening S) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf _).map (toCrysAssocSheaf P))) where
  equalizerSieve_mem {X} x y hxy := by
    have := isLocallyInjective_toSheafify (presheafULiftU P).presheaf
    have := isLocallySurjective_toSheafify (presheafULiftU P).presheaf
    have := CrystallineThickening.isLocallyInjective_whiskerLeft_restrictOpenFunctor A
      (toSheafify (smallTopology S) (presheafULiftU P).presheaf)
    have hxy' : (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        (toSheafify (smallTopology S) (presheafULiftU P).presheaf)).app X (ULift.up x) =
        (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (presheafULiftU P).presheaf)).app X (ULift.up y) :=
      (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj
        (op (A.restrictOpen X.unop)) : Type (u + 1)))).symm.injective hxy
    have h := Presheaf.equalizerSieve_mem
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) _ _ _ hxy'
    refine (Opens.grothendieckTopology _).superset_covering ?_ h
    intro V i hi
    exact congrArg ULift.down hi

/-- **`toCrysAssocSheaf P`, restricted to the ambient scheme of an object, is locally
surjective.** -/
theorem isLocallySurjective_restrict_toCrysAssocSheaf (A : CrystallineThickening S) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf _).map (toCrysAssocSheaf P))) where
  imageSieve_mem {X} s := by
    have := isLocallyInjective_toSheafify (presheafULiftU P).presheaf
    have := isLocallySurjective_toSheafify (presheafULiftU P).presheaf
    have := CrystallineThickening.isLocallySurjective_whiskerLeft_restrictOpenFunctor A
      (toSheafify (smallTopology S) (presheafULiftU P).presheaf)
    refine (Opens.grothendieckTopology _).superset_covering ?_
      (Presheaf.imageSieve_mem _ (Functor.whiskerLeft
        (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (presheafULiftU P).presheaf))
        (U := op X) (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj
          (op (A.restrictOpen X)) : Type (u + 1))) s))
    rintro V i ⟨t, ht⟩
    refine ⟨t.down, ?_⟩
    apply (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).injective
    refine ((Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).apply_symm_apply _).trans (ht.trans ?_)
    exact ((Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).apply_symm_apply _).symm

end AssocSheaf

/-! ### The universal property of the associated sheaf -/

section AssocSheafDesc

variable (P : PresheafOfModules.{u} (structureSheaf S).obj)
  (G : SheafOfModules.{u} (structureSheaf S))

/-- A morphism from a presheaf of `𝒪_{X/S}`-modules into a sheaf, with the sections of both sides
raised to `Type (u + 1)`. -/
def presheafULiftUHom (χ₀ : P ⟶ G.val) :
    presheafULiftU P ⟶ (SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars (𝟙 (structureSheaf S).obj)).obj
        ((Stacks.SheafOfModules.moduleULift.{u + 1} (structureSheaf S)).obj G) :=
  PresheafOfModules.homMk
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map χ₀)
      AddCommGrpCat.uliftFunctor.{u + 1})
    (fun X r m ↦ congrArg ULift.up ((χ₀.app X).hom.map_smul r m.down))

/-- **The extension of a morphism from a presheaf of `𝒪_{X/S}`-modules into a sheaf over the
associated sheaf**, obtained from the sheafification adjunction at the module universe `u + 1`. -/
def crysAssocSheafDesc (χ₀ : P ⟶ G.val) : crysAssocSheaf P ⟶ G :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} (structureSheaf S)).preimage
    ((Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (structureSheaf S)
        (crysAssocSheafULift P)).hom ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 (structureSheaf S).obj)).symm
        (presheafULiftUHom P G χ₀))

/-- The extension `crysAssocSheafDesc P G χ₀` restricts to `χ₀` along `toCrysAssocSheaf P`. -/
theorem toCrysAssocSheaf_comp_crysAssocSheafDesc (χ₀ : P ⟶ G.val) :
    toCrysAssocSheaf P ≫ (crysAssocSheafDesc P G χ₀).val = χ₀ := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf S).obj)).homEquiv_unit
    (presheafULiftU P) ((Stacks.SheafOfModules.moduleULift.{u + 1} (structureSheaf S)).obj G)
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 (structureSheaf S).obj)).symm
      (presheafULiftUHom P G χ₀))
  have h' := h.symm.trans (Equiv.apply_symm_apply
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (structureSheaf S).obj))
      (presheafULiftUHom P G χ₀))
  refine PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  have e := congrArg ULift.down (congrArg (fun g ↦ (g.app X).hom (ULift.up m)) h')
  have hz : ((Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (structureSheaf S)
      (crysAssocSheafULift P)).hom.val.app X).hom (ULift.up ((toCrysAssocSheaf P).app X m)) =
      ((crysAssocSheafULiftUnit P).app X).hom (ULift.up m) :=
    (Shrink.addEquiv (α := ((crysAssocSheafULift P).val.obj X : Type (u + 1)))).apply_symm_apply _
  exact (congrArg (fun z ↦ ULift.down ((((PresheafOfModules.sheafificationHomEquiv
    (𝟙 (structureSheaf S).obj)).symm (presheafULiftUHom P G χ₀)).val.app X).hom z)) hz).trans e

/-- The sheafification adjunction applied to the universe lift of a morphism out of the
associated sheaf. -/
theorem sheafificationHomEquiv_shrinkIso_inv_comp (χ : crysAssocSheaf P ⟶ G) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (structureSheaf S).obj)
        ((Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (structureSheaf S)
          (crysAssocSheafULift P)).inv ≫
          (Stacks.SheafOfModules.moduleULift.{u + 1} (structureSheaf S)).map χ) =
      presheafULiftUHom P G (toCrysAssocSheaf P ≫ χ.val) := by
  refine ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf S).obj)).homEquiv_unit
    (presheafULiftU P) ((Stacks.SheafOfModules.moduleULift.{u + 1} (structureSheaf S)).obj G)
    _).trans ?_
  refine PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  rfl

/-- **Morphisms out of the associated sheaf are determined by their restriction along
`toCrysAssocSheaf P`.** -/
theorem crysAssocSheaf_hom_ext {χ₁ χ₂ : crysAssocSheaf P ⟶ G}
    (h : toCrysAssocSheaf P ≫ χ₁.val = toCrysAssocSheaf P ≫ χ₂.val) : χ₁ = χ₂ := by
  apply (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} (structureSheaf S)).map_injective
  refine (cancel_epi (Stacks.SheafOfModules.sheafShrinkIso.{u, u + 1} (structureSheaf S)
    (crysAssocSheafULift P)).inv).1 ?_
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (structureSheaf S).obj)).injective
  exact (sheafificationHomEquiv_shrinkIso_inv_comp P G χ₁).trans
    ((congrArg (presheafULiftUHom P G) h).trans
      (sheafificationHomEquiv_shrinkIso_inv_comp P G χ₂).symm)

end AssocSheafDesc

/-! ### The sheaf `Ω_{X/S}` and its universal derivation -/

section Differentials

variable (S)

/-- **The sheaf of crystalline differentials `Ω_{X/S}` on the small crystalline site
`Cris(X/S)`**: the sheaf of `𝒪_{X/S}`-modules associated with the presheaf `Ω_{X/S}` of divided
power differentials `(U, T, δ) ↦ Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}`, with its sections in `Type u`. -/
def crysDifferentialsSheaf : SheafOfModules.{u} (structureSheaf S) :=
  crysAssocSheaf (crysDifferentials S)

/-- The sheafification morphism from the presheaf `Ω_{X/S}` to the sheaf `Ω_{X/S}`. -/
def toCrysDifferentialsSheaf : crysDifferentials S ⟶ (crysDifferentialsSheaf S).val :=
  toCrysAssocSheaf (crysDifferentials S)

/-- **The universal derivation `d_{X/S} : 𝒪_{X/S} → Ω_{X/S}`, on sections**: over an object
`(U, T, δ)` it is the universal divided power differential `d : Γ(T, 𝒪_T) → Ω_{X/S}(U, T, δ)` of
the presheaf followed by the sheafification morphism. -/
def crysSheafD (A : CrystallineThickening S) (x : Γ(A.obj.thickening.target.scheme, ⊤)) :
    (crysDifferentialsSheaf S).val.obj (op A) :=
  (toCrysDifferentialsSheaf S).app (op A)
    ((GlobalCrystallineSituation.crysSDerivation S).app A.obj x)

variable {S}

/-- **The restriction `(Ω_{X/S})_T` of the sheaf `Ω_{X/S}` to the ambient scheme `T` of an object
`(U, T, δ)` of `Cris(X/S)`**, as a sheaf of `𝒪_T`-modules on `T_Zar`: its sections over an open
`W` of `T` are the sections of `Ω_{X/S}` over `(U ∩ W, W, δ|_W)`. -/
abbrev crysDifferentialsSheafRestriction (A : CrystallineThickening S) :
    A.obj.thickening.target.scheme.Modules :=
  ambientModuleRestriction (crysDifferentialsSheaf S) A

/-- The comparison morphism of presheaves of `𝒪_T`-modules from the presheaf of divided power
differentials of `T` over `S` to `(Ω_{X/S})_T`: the identification of [Stacks, Tag 07IY]'s
presheaf with the restriction of the presheaf `Ω_{X/S}`
(`Crystalline.GlobalCrystallineSituation.comparisonHom`), followed by the restriction of the
sheafification morphism. -/
def dpDifferentialsToCrysDifferentialsSheafRestriction (A : CrystallineThickening S) :
    dpDifferentialsPresheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).obj
        (crysDifferentialsSheafRestriction A) :=
  PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf _).map (GlobalCrystallineSituation.comparisonHom A.obj) ≫
      Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf _).map (toCrysDifferentialsSheaf S)))
    (fun W r m ↦
      ((congrArg (fun z ↦ ((toCrysDifferentialsSheaf S).app (op (A.restrictOpen W.unop))).hom z)
          (((GlobalCrystallineSituation.comparisonHom A.obj).app W).hom.map_smul r m)).trans
        (((toCrysDifferentialsSheaf S).app (op (A.restrictOpen W.unop))).hom.map_smul _ _)).trans
      (congrArg (fun s ↦ s • ((toCrysDifferentialsSheaf S).app (op (A.restrictOpen W.unop))).hom
          (((GlobalCrystallineSituation.comparisonHom A.obj).app W).hom m))
        (ringRestrictionSheafStructureIso_inv_app_apply A.obj W.unop r).symm))

/-- On sections, `dpDifferentialsToCrysDifferentialsSheafRestriction` is the comparison followed by
the sheafification morphism over the restricted object. -/
theorem dpDifferentialsToCrysDifferentialsSheafRestriction_app_apply (A : CrystallineThickening S)
    (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (m : (dpDifferentialsPresheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).obj W) :
    (dpDifferentialsToCrysDifferentialsSheafRestriction A).app W m =
      (toCrysDifferentialsSheaf S).app (op (A.restrictOpen W.unop))
        (((GlobalCrystallineSituation.comparisonHom A.obj).app W).hom m) := rfl

/-- The comparison into `(Ω_{X/S})_T` is Zariski-locally injective: it is an isomorphism of
presheaves followed by the restriction of the sheafification morphism. -/
theorem isLocallyInjective_dpDifferentialsToCrysDifferentialsSheafRestriction
    (A : CrystallineThickening S) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
        (dpDifferentialsToCrysDifferentialsSheafRestriction A)) := by
  have h₂ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).map
          (toCrysDifferentialsSheaf S))) :=
    isLocallyInjective_restrict_toCrysAssocSheaf (crysDifferentials S) A
  have h₁ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
        (GlobalCrystallineSituation.comparisonHom A.obj)) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun W ↦
      (ConcreteCategory.bijective_of_isIso
        (((PresheafOfModules.toPresheaf _).mapIso
          (GlobalCrystallineSituation.comparisonIso A.obj)).hom.app W)).1
  exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ (Opens.grothendieckTopology _) _ _ _
    ((PresheafOfModules.toPresheaf _).map (GlobalCrystallineSituation.comparisonHom A.obj))
    (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).map
          (toCrysDifferentialsSheaf S))) h₁ h₂

/-- The comparison into `(Ω_{X/S})_T` is Zariski-locally surjective. -/
theorem isLocallySurjective_dpDifferentialsToCrysDifferentialsSheafRestriction
    (A : CrystallineThickening S) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
        (dpDifferentialsToCrysDifferentialsSheafRestriction A)) := by
  have h₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).map
          (toCrysDifferentialsSheaf S))) :=
    isLocallySurjective_restrict_toCrysAssocSheaf (crysDifferentials S) A
  have h₁ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
        (GlobalCrystallineSituation.comparisonHom A.obj)) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun W ↦
      (ConcreteCategory.bijective_of_isIso
        (((PresheafOfModules.toPresheaf _).mapIso
          (GlobalCrystallineSituation.comparisonIso A.obj)).hom.app W)).2
  exact @Presheaf.isLocallySurjective_comp _ _ (Opens.grothendieckTopology _) _ _ _ _ _ _ _ _ _
    ((PresheafOfModules.toPresheaf _).map (GlobalCrystallineSituation.comparisonHom A.obj))
    (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).map
          (toCrysDifferentialsSheaf S))) h₁ h₂

/-- The transpose of the comparison out of the sheafification `Ω_{T/S,δ}` is an isomorphism. -/
theorem isIso_sheafificationHomEquiv_symm_dpDifferentialsToCrysDifferentialsSheafRestriction
    (A : CrystallineThickening S) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).symm
        (dpDifferentialsToCrysDifferentialsSheafRestriction A)) :=
  Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm _ _
    (isLocallyInjective_dpDifferentialsToCrysDifferentialsSheafRestriction A)
    (isLocallySurjective_dpDifferentialsToCrysDifferentialsSheafRestriction A)

/-- **Stacks Project, Tag 07IZ, the module identification.**  For an object `(U, T, δ)` of
`Cris(X/S)` the restriction `(Ω_{X/S})_T` of the sheaf of crystalline differentials to `T_Zar` is
the sheaf `Ω_{T/S,δ}` of divided power differentials of `T` over `S`, as sheaves of
`𝒪_T`-modules. -/
@[stacks 07IZ "(Ω_{X/S})_T = Ω_{T/S,δ}, as sheaves of 𝒪_T-modules on T_Zar"]
def crysDifferentialsSheafRestrictionIso (A : CrystallineThickening S) :
    dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom ≅
      crysDifferentialsSheafRestriction A :=
  @asIso _ _ _ _ ((PresheafOfModules.sheafificationHomEquiv
    (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).symm
      (dpDifferentialsToCrysDifferentialsSheafRestriction A))
    (isIso_sheafificationHomEquiv_symm_dpDifferentialsToCrysDifferentialsSheafRestriction A)

/-- The isomorphism `crysDifferentialsSheafRestrictionIso` restricts, along the sheafification
morphism of `Ω_{T/S,δ}`, to `dpDifferentialsToCrysDifferentialsSheafRestriction`. -/
theorem dpDifferentialsToSheaf_comp_crysDifferentialsSheafRestrictionIso_hom
    (A : CrystallineThickening S) :
    dpDifferentialsToSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).map
          (crysDifferentialsSheafRestrictionIso A).hom =
      dpDifferentialsToCrysDifferentialsSheafRestriction A := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).homEquiv_unit
      (dpDifferentialsPresheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
      (crysDifferentialsSheafRestriction A) (crysDifferentialsSheafRestrictionIso A).hom
  exact h.symm.trans (Equiv.apply_symm_apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj))
      (dpDifferentialsToCrysDifferentialsSheafRestriction A))

/-- **Stacks Project, Tag 07IZ, the derivations.**  Under the identification
`Ω_{T/S,δ} ≅ (Ω_{X/S})_T` of `crysDifferentialsSheafRestrictionIso`, the universal divided power
derivation `d_{T/S,δ}` is the restriction `d_{X/S}|_T` of the universal derivation of `Ω_{X/S}`:
for an open `W` of `T` and a section `b` of `𝒪_T` over `W`, the section `d_{T/S,δ} b` of
`Ω_{T/S,δ}` over `W` corresponds to `d_{X/S} b` over the restricted object `(U ∩ W, W, δ|_W)`. -/
@[stacks 07IZ "d_{X/S}|_T = d_{T/S,δ}"]
theorem crysDifferentialsSheafRestrictionIso_hom_app_d (A : CrystallineThickening S)
    (W : A.obj.thickening.target.scheme.Opens) (b : Γ(A.obj.thickening.target.scheme, W)) :
    (crysDifferentialsSheafRestrictionIso A).hom.val.app (op W)
        ((universalDPSchemeDerivation A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom).app W b) =
      crysSheafD S (A.restrictOpen W) (openTopRes W b) := by
  have h := congrArg (fun g ↦ (g.app (op W)).hom
      ((presheafD A.obj.thickening.target S.S.scheme A.obj.toBase.hom W).d b))
    (dpDifferentialsToSheaf_comp_crysDifferentialsSheafRestrictionIso_hom A)
  refine h.trans ?_
  exact congrArg (fun z ↦ (toCrysDifferentialsSheaf S).app (op (A.restrictOpen W)) z)
    (GlobalCrystallineSituation.comparisonHom_app_d A.obj W b)

end Differentials

/-! ### `S`-derivations on `Cris(X/S)` and the universal property of `Ω_{X/S}` -/

section SDerivation

/-- The sections of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module
over the divided power ring of global sections of its ambient divided power scheme; the two rings
are the same, but the divided power ring is a bundled object, so the instance is supplied by
name. -/
instance moduleObjDividedPowerRing (F : PresheafOfModules.{u} (structureSheaf S).obj)
    (A : CrystallineThickening S) :
    Module ↥(A.obj.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.obj.thickening.target.scheme.Opens))) ↥(F.obj (op A)) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op A)) ↥(F.obj (op A)))

/-- The sections of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module
over the ring of global sections of its ambient scheme, supplied by name for the same reason. -/
instance moduleObjGlobalSectionsSmall (F : PresheafOfModules.{u} (structureSheaf S).obj)
    (A : CrystallineThickening S) :
    Module Γ(A.obj.thickening.target.scheme, ⊤) ↥(F.obj (op A)) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op A)) ↥(F.obj (op A)))

variable (S) in
/-- **An `S`-derivation on the small crystalline site** ([Stacks, Tag 07IX]).  For a presheaf `F`
of `𝒪_{X/S}`-modules on `Cris(X/S)`, a map of presheaves of abelian groups `𝒪_{X/S} → F` such
that for every object `(U, T, δ)` and *every* open `V ⊆ S` through which `T → S` factors, the map
`Γ(T, 𝒪_T) → F(U, T, δ)` is a divided power `Γ(V, 𝒪_V)`-derivation.  For `F` the underlying
presheaf `ℱ.val` of a sheaf `ℱ` of `𝒪_{X/S}`-modules this is the definition of the source. -/
@[stacks 07IX "S-derivation O_{X/S} → F into a sheaf F of O_{X/S}-modules on Cris(X/S), \
  as SDerivation S F.val"]
structure SDerivation (F : PresheafOfModules.{u} (structureSheaf S).obj) where
  /-- The map on the global sections of the ambient divided power scheme of an object. -/
  app (A : CrystallineThickening S) : Γ(A.obj.thickening.target.scheme, ⊤) → F.obj (op A)
  /-- The maps on sections commute with the restriction maps of `Cris(X/S)`. -/
  naturality {A B : CrystallineThickening S} (g : A ⟶ B)
    (x : Γ(B.obj.thickening.target.scheme, ⊤)) :
    F.map g.op (app B x) = app A (g.hom.targetHom.hom.appTop x)
  /-- For every open `V` of the divided power base through which `T → S` factors, the map on
  sections is a divided power `Γ(V, 𝒪_V)`-derivation. -/
  dividedPowerDerivation (A : CrystallineThickening S) (V : S.S.scheme.Opens)
      (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    DividedPowerDerivation Γ(S.S.scheme, V)
      (A.obj.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.obj.thickening.target.scheme.Opens)))
      (A.obj.toBase.hom.appLE V ⊤ h).hom (F.obj (op A))
  /-- The divided power derivation at `(U, T, δ)` above `V` is the map on sections there. -/
  dividedPowerDerivation_apply (A : CrystallineThickening S) (V : S.S.scheme.Opens)
      (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
      (x : Γ(A.obj.thickening.target.scheme, ⊤)) :
    (dividedPowerDerivation A V h).toDerivation x = app A x

namespace SDerivation

variable {F : PresheafOfModules.{u} (structureSheaf S).obj}

/-- An `S`-derivation is additive on sections. -/
theorem app_add (D : SDerivation S F) (A : CrystallineThickening S)
    (x y : Γ(A.obj.thickening.target.scheme, ⊤)) :
    D.app A (x + y) = D.app A x + D.app A y := by
  simp only [← D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.obj.toBase.hom ⊤)]
  exact (D.dividedPowerDerivation A ⊤ (le_preimage_top A.obj.toBase.hom ⊤)).map_add x y

/-- The Leibniz rule for an `S`-derivation, on sections. -/
theorem leibniz (D : SDerivation S F) (A : CrystallineThickening S)
    (x y : Γ(A.obj.thickening.target.scheme, ⊤)) :
    D.app A (x * y) = x • D.app A y + y • D.app A x := by
  simp only [← D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.obj.toBase.hom ⊤)]
  exact (D.dividedPowerDerivation A ⊤ (le_preimage_top A.obj.toBase.hom ⊤)).leibniz x y

/-- An `S`-derivation kills every section pulled back from the divided power base. -/
theorem app_appLE (D : SDerivation S F) (A : CrystallineThickening S) (V : S.S.scheme.Opens)
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (a : Γ(S.S.scheme, V)) :
    D.app A (A.obj.toBase.hom.appLE V ⊤ h a) = 0 := by
  rw [← D.dividedPowerDerivation_apply A V h]
  exact (D.dividedPowerDerivation A V h).map_ringHom a

/-- The divided power chain rule for an `S`-derivation, on sections. -/
theorem app_dpow (D : SDerivation S F) (A : CrystallineThickening S) (n : ℕ) (hn : 0 < n)
    (x : Γ(A.obj.thickening.target.scheme, ⊤))
    (hx : x ∈ A.obj.thickening.target.ideal.obj
      (op (⊤ : A.obj.thickening.target.scheme.Opens))) :
    D.app A ((A.obj.thickening.target.dividedPowers.toDividedPowerRing
          (op (⊤ : A.obj.thickening.target.scheme.Opens))).dividedPowers.dpow n x) =
      (A.obj.thickening.target.dividedPowers.toDividedPowerRing
        (op (⊤ : A.obj.thickening.target.scheme.Opens))).dividedPowers.dpow (n - 1) x •
          D.app A x :=
  (D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.obj.toBase.hom ⊤) _).symm.trans
    (((D.dividedPowerDerivation A ⊤ (le_preimage_top A.obj.toBase.hom ⊤)).map_dpow n hn x
        hx).trans
      (congrArg
        (fun m ↦ (A.obj.thickening.target.dividedPowers.toDividedPowerRing
          (op (⊤ : A.obj.thickening.target.scheme.Opens))).dividedPowers.dpow (n - 1) x • m)
        (D.dividedPowerDerivation_apply A ⊤ (le_preimage_top A.obj.toBase.hom ⊤) x)))

/-- An `S`-derivation into `G`, read on the global sections at an object of `Cris(X/S)` as a
derivation relative to the global sections of the divided power base. -/
def descDerivation (D : SDerivation S F) (A : CrystallineThickening S) :
    (F.obj (op A)).Derivation (crysBaseAppLE S A.obj) :=
  ModuleCat.Derivation.mk (D.app A) (D.app_add A) (D.leibniz A)
    (fun a ↦ D.app_appLE A ⊤ (le_preimage_top A.obj.toBase.hom ⊤) a)

/-- The map on sections at an object of `Cris(X/S)` through which an `S`-derivation factors. -/
def descApp (D : SDerivation S F) (A : CrystallineThickening S) :
    (crysDifferentials S : PresheafOfModules.{u} (structureSheaf S).obj).obj (op A) ⟶
      F.obj (op A) :=
  dpConstDesc (D.descDerivation A)
    (fun n x hx ↦ D.app_dpow A (n + 1) (Nat.succ_pos n) x hx)
    (fun _ hs ↦ by
      obtain ⟨V, h, a, rfl⟩ := hs
      exact D.app_appLE A V h a)

/-- `descApp` sends `d x` to `D x`. -/
theorem descApp_d (D : SDerivation S F) (A : CrystallineThickening S)
    (x : Γ(A.obj.thickening.target.scheme, ⊤)) :
    (D.descApp A).hom ((crysDifferentialsD S A.obj).d x) = D.app A x :=
  dpConstDesc_d _ _ _ x

/-- **The factorization of an `S`-derivation on `Cris(X/S)` through the presheaf `Ω_{X/S}`.** -/
def descHom (D : SDerivation S F) :
    (crysDifferentials S : PresheafOfModules.{u} (structureSheaf S).obj) ⟶ F where
  app X := D.descApp X.unop
  naturality {X Y} i := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    have h1 := crysDifferentialsMap_d S i.unop.hom b
    have h2 := D.descApp_d Y.unop (i.unop.hom.targetHom.hom.appTop b)
    have h3 := D.descApp_d X.unop b
    have h4 := D.naturality i.unop b
    exact ((congrArg (fun z ↦ (D.descApp Y.unop).hom z) h1).trans h2).trans
      (h4.symm.trans (congrArg (fun z ↦ F.map i z) h3).symm)

/-- `descHom` sends `d x` to `D x`. -/
theorem descHom_app_d (D : SDerivation S F) (A : CrystallineThickening S)
    (x : Γ(A.obj.thickening.target.scheme, ⊤)) :
    (D.descHom).app (op A) ((crysDifferentialsD S A.obj).d x) = D.app A x :=
  D.descApp_d A x

end SDerivation

variable (S)

/-- **The universal `S`-derivation `d_{X/S} : 𝒪_{X/S} → Ω_{X/S}` of the small crystalline site,
into the sheaf `Ω_{X/S}`.**  On sections over `(U, T, δ)` it is the universal divided power
differential of `Γ(T, 𝒪_T)` relative to the base, followed by the sheafification morphism. -/
def crysSheafSDerivation : SDerivation S (crysDifferentialsSheaf S).val where
  app A x := crysSheafD S A x
  naturality {A B} g x :=
    (congrArg (fun z ↦ z) (PresheafOfModules.naturality_apply (toCrysDifferentialsSheaf S) g.op
      ((GlobalCrystallineSituation.crysSDerivation S).app B.obj x))).symm.trans
      (congrArg (fun z ↦ (toCrysDifferentialsSheaf S).app (op A) z)
        ((GlobalCrystallineSituation.crysSDerivation S).naturality g.hom x))
  dividedPowerDerivation A V h :=
    { toDerivation :=
        Derivation.mk'
          (AddMonoidHom.toIntLinearMap
            (AddMonoidHom.mk' (fun x ↦ crysSheafD S A x) fun x y ↦
              (congrArg (fun z ↦ ((toCrysDifferentialsSheaf S).app (op A)).hom z)
                ((GlobalCrystallineSituation.crysSDerivation S).app_add A.obj x y)).trans
                (((toCrysDifferentialsSheaf S).app (op A)).hom.map_add _ _)))
          (fun x y ↦
            (congrArg (fun z ↦ ((toCrysDifferentialsSheaf S).app (op A)).hom z)
              ((GlobalCrystallineSituation.crysSDerivation S).leibniz A.obj x y)).trans
              ((((toCrysDifferentialsSheaf S).app (op A)).hom.map_add _ _).trans
                (congrArg₂ (· + ·)
                  (((toCrysDifferentialsSheaf S).app (op A)).hom.map_smul x _)
                  (((toCrysDifferentialsSheaf S).app (op A)).hom.map_smul y _))))
      map_ringHom' a :=
        (congrArg (fun z ↦ ((toCrysDifferentialsSheaf S).app (op A)).hom z)
          ((GlobalCrystallineSituation.crysSDerivation S).app_appLE A.obj V h a)).trans
          (((toCrysDifferentialsSheaf S).app (op A)).hom.map_zero)
      map_dpow' n hn x hx :=
        (congrArg (fun z ↦ ((toCrysDifferentialsSheaf S).app (op A)).hom z)
          ((GlobalCrystallineSituation.crysSDerivation S).app_dpow A.obj n hn x hx)).trans
          (((toCrysDifferentialsSheaf S).app (op A)).hom.map_smul _ _) }
  dividedPowerDerivation_apply _ _ _ _ := rfl

variable {S}

/-- On sections, `crysSheafSDerivation S` is `crysSheafD S`. -/
@[simp]
theorem crysSheafSDerivation_app (A : CrystallineThickening S)
    (x : Γ(A.obj.thickening.target.scheme, ⊤)) :
    (crysSheafSDerivation S).app A x = crysSheafD S A x := rfl

/-- **The universal property of `(Ω_{X/S}, d_{X/S})` on the small crystalline site.**  Every
`S`-derivation `D : 𝒪_{X/S} → G` into a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` factors
uniquely as `χ ∘ d_{X/S}` for a morphism of sheaves of modules `χ : Ω_{X/S} → G`. -/
theorem crysSheafSDerivation_isUniversal (G : SheafOfModules.{u} (structureSheaf S))
    (D : SDerivation S G.val) :
    ∃! χ : crysDifferentialsSheaf S ⟶ G, ∀ (A : CrystallineThickening S)
      (x : Γ(A.obj.thickening.target.scheme, ⊤)),
        χ.val.app (op A) ((crysSheafSDerivation S).app A x) = D.app A x := by
  refine ⟨crysAssocSheafDesc (crysDifferentials S) G D.descHom, fun A x ↦ ?_, fun χ hχ ↦ ?_⟩
  · exact (congrArg (fun φ ↦ (φ.app (op A)).hom ((crysDifferentialsD S A.obj).d x))
      (toCrysAssocSheaf_comp_crysAssocSheafDesc (crysDifferentials S) G D.descHom)).trans
        (D.descHom_app_d A x)
  · refine crysAssocSheaf_hom_ext _ G ((?_ : toCrysAssocSheaf _ ≫ χ.val = D.descHom).trans
      (toCrysAssocSheaf_comp_crysAssocSheafDesc _ G D.descHom).symm)
    refine PresheafOfModules.hom_ext fun X ↦ dpConstDifferentials_ext fun b ↦ ?_
    exact (hχ X.unop b).trans (D.descHom_app_d X.unop b).symm

end SDerivation

end Crystalline.GlobalCrystallineSituation.SmallSite

end
