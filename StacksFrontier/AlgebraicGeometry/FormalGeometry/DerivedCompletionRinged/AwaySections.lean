module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheafLocalization

/-!
# The sections of the localization of the structure sheaf at a global section

Let `(𝒞, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`. The sheaf of rings `𝒪_f`
of `LocalizationAtGlobalSection.lean` is *defined* as a sheafification, and nothing in the
library described its sections. This file supplies that description, at the level of sheaves of
`𝒪`-modules, in the only form in which a sheafification has one: `𝒪_f` is the sheafification of
the presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations, and consequently it has a
universal property *as a sheaf of `𝒪`-modules* and not merely as a sheaf of rings.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayModulePresheaf`: the presheaf `U ↦ 𝒪(U)[1/f|_U]`, read as a
  presheaf of `𝒪`-modules, with `AlgebraicGeometry.RingedSite.unitToAwayModulePresheaf` the
  canonical map out of `𝒪`.
* `AlgebraicGeometry.RingedSite.awaySheafification`: its sheafification, as a sheaf of
  `𝒪`-modules, and `AlgebraicGeometry.RingedSite.awayModuleComparison`,
  `AlgebraicGeometry.RingedSite.awaySheafificationToAwayModule` the comparison maps to `𝒪_f`.

## Main results

* `AlgebraicGeometry.RingedSite.isLocalizedModule_unitToAwayModulePresheaf`: over every object
  the canonical map is the localization of the ring of sections away from the value of `f`
  there.
* `AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule`: **`𝒪_f`, as a sheaf of
  `𝒪`-modules, is the sheafification of the presheaf of sectionwise localizations**, compatibly
  with the canonical maps out of `𝒪`
  (`AlgebraicGeometry.RingedSite.toModuleSheafification_comp_awaySheafificationToAwayModule`).
* `AlgebraicGeometry.RingedSite.existsUnique_lift_unitToAwayModule`: **the universal property of
  `𝒪_f` as a sheaf of `𝒪`-modules.** A map `𝒪 ⟶ 𝒩` of sheaves of `𝒪`-modules on whose sections
  every power of `f` acts bijectively factors uniquely through `𝒪 ⟶ 𝒪_f`.
* `AlgebraicGeometry.RingedSite.hom_ext_unitToAwayModule`: two maps out of `𝒪_f` into such an
  `𝒩` agree as soon as they agree after restriction along `𝒪 ⟶ 𝒪_f`.

## Implementation notes

The presheaf of sectionwise localizations is taken to be the restriction of scalars along
`𝒪 ⟶ 𝒪[1/f]` of the unit presheaf of `𝒪[1/f]` — that is, the presheaf of rings
`AlgebraicGeometry.RingedSite.awayPresheaf` read as a presheaf of `𝒪`-modules — rather than the
sectionwise base change `localizationModulePresheaf` of
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf` in
`StacksFrontier/CategoryTheory/Sites/Modules/ModuleSheafLocalization.lean`. Its
modules of sections are then the localized rings on the nose, so
`AlgebraicGeometry.RingedSite.isLocalizationAway_awayPresheaf` applies directly and the
identification with `𝒪_f` is the sheafification map of `CommRingCat`-valued presheaves with its
module structure, not a tensor-product comparison.

That the comparison `AlgebraicGeometry.RingedSite.awaySheafificationToAwayModule` is invertible
is the local bijectivity of `CategoryTheory.toSheafify`: the composite of the sheafification unit
of the presheaf of modules with the comparison is that map, read in abelian groups; a map whose
composite with a locally bijective map is locally bijective is itself locally bijective; and a
locally bijective map of sheaves is an isomorphism. The same device is used by
`AlgebraicGeometry.SheafOfModules.localizationMap_isFlat` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Support/LocalizationFlat.lean`, where it occurs
inside a private proof; here it is a named declaration.

`moduleObjRingSheaf` reseats a module of sections of a presheaf of `𝒪`-modules over the
*commutative* ring of sections of `𝒪`. The scalars of a presheaf of modules live in `RingCat`
while `Submonoid`s of sections and `IsLocalizedModule` are stated over `CommRingCat`; the two
carriers agree, and `Stacks.PresheafOfModules.ChangeOfRings.moduleObj` does the same reseating
for the spelling `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.O.obj` of the presheaf of
rings. That spelling and `AlgebraicGeometry.RingedSite.ringSheaf X |>.obj` are equal, but only
after unfolding `CategoryTheory.sheafCompose`, so instance search does not cross between them and
each needs its own reseating instance. Everything below is written in the second spelling, which
is the one `AlgebraicGeometry.RingedSite.awayModule` and the sheafification of presheaves of
modules use.

Nothing here carries a `stacks` attribute: these are general facts about the localization of the
structure sheaf of a ringed site at a global section, and the source states none of them. The
tags that consume them are [Stacks, Tag 099B] and [Stacks, Tag 0A0E], whose carriers are
elsewhere.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 0EMD](https://stacks.math.columbia.edu/tag/0EMD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open Stacks.PresheafOfModules.ChangeOfRings

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- A module of sections of a presheaf of modules over the structure sheaf of a ringed site,
read as a module over the commutative ring of sections of the structure sheaf. The carriers
agree; this is a reseating of scalars along an identity of rings, not a restriction of
scalars. -/
instance moduleObjRingSheaf
    (M : PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) (U : X.Cᵒᵖ) :
    Module (X.O.obj.obj U) (M.obj U) := (M.obj U).isModule

/-- **The presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations, as a presheaf of
`𝒪`-modules**: the presheaf of rings `AlgebraicGeometry.RingedSite.awayPresheaf` with scalars
restricted along the canonical map out of `𝒪`. -/
def awayModulePresheaf : PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight (toAwayPresheaf h) (forget₂ CommRingCat.{u} RingCat.{u}))).obj
    (PresheafOfModules.unit (ringPresheaf (awayPresheaf h)))

/-- The canonical map `𝒪 ⟶ 𝒪[1/f]` of presheaves of `𝒪`-modules, which over every object is
the localization map of the ring of sections. -/
def unitToAwayModulePresheaf :
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val ⟶
      awayModulePresheaf X h :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (toAwayPresheaf h)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
    (fun U r m => by
      let r' : X.O.obj.obj U := r
      let m' : X.O.obj.obj U := m
      change ((toAwayPresheaf h).app U).hom (r' * m') =
        ((toAwayPresheaf h).app U).hom r' * ((toAwayPresheaf h).app U).hom m'
      rw [map_mul])

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- On sections the canonical map is the localization map. -/
theorem unitToAwayModulePresheaf_app_apply (U : X.Cᵒᵖ) (x : X.O.obj.obj U) :
    ((unitToAwayModulePresheaf X h).app U).hom x = ((toAwayPresheaf h).app U).hom x := rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Over every object the canonical map is a localization of modules**: the module of sections
of `𝒪[1/f]` over `U` is the localization of `𝒪(U)` away from the value of `f` there. -/
theorem isLocalizedModule_unitToAwayModulePresheaf (U : X.Cᵒᵖ) :
    IsLocalizedModule ((awayMultiplicativeSubpresheaf h).obj U)
      ((unitToAwayModulePresheaf X h).app U).hom := by
  have hloc : let := ((toAwayPresheaf h).app U).hom.toAlgebra
      IsLocalization ((awayMultiplicativeSubpresheaf h).obj U) ((awayPresheaf h).obj U) :=
    isLocalizationAway_awayPresheaf h U
  let _ := ((toAwayPresheaf h).app U).hom.toAlgebra
  exact (isLocalizedModule_iff_isLocalization' ((awayMultiplicativeSubpresheaf h).obj U)
    ((awayPresheaf h).obj U)).mpr hloc

/-- The comparison map from the presheaf of sectionwise localizations to `𝒪_f`, as presheaves of
`𝒪`-modules: over every object it is the sheafification map. -/
def awayModuleComparison : awayModulePresheaf X h ⟶ (awayModule X h).val :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (toSheafify X.J (awayPresheaf h))
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
    (fun U r m => by
      let r' : X.O.obj.obj U := r
      let m' : (awayPresheaf h).obj U := m
      change ((toSheafify X.J (awayPresheaf h)).app U).hom
          (((toAwayPresheaf h).app U).hom r' * m') =
        ((toAwaySheaf h).hom.app U).hom r' * ((toSheafify X.J (awayPresheaf h)).app U).hom m'
      rw [map_mul, toAwaySheaf_hom]
      rfl)

/-- On sections the comparison map is the sheafification map. -/
theorem awayModuleComparison_app_apply (U : X.Cᵒᵖ) (x : (awayPresheaf h).obj U) :
    ((awayModuleComparison X h).app U).hom x =
      ((toSheafify X.J (awayPresheaf h)).app U).hom x := rfl

/-- The comparison map is compatible with the canonical maps out of `𝒪`: this is the
factorisation `AlgebraicGeometry.RingedSite.toAwaySheaf_hom` of `𝒪 ⟶ 𝒪_f` through the
sectionwise localization, read in modules. -/
theorem unitToAwayModulePresheaf_comp_awayModuleComparison :
    unitToAwayModulePresheaf X h ≫ awayModuleComparison X h = (unitToAwayModule X h).val := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let x' : X.O.obj.obj U := x
  change ((toSheafify X.J (awayPresheaf h)).app U).hom (((toAwayPresheaf h).app U).hom x') =
    ((toAwaySheaf h).hom.app U).hom x'
  rw [toAwaySheaf_hom]
  rfl

/-- The sheafification of the presheaf of sectionwise localizations, as a sheaf of
`𝒪`-modules. -/
abbrev awaySheafification : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (PresheafOfModules.sheafification (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).obj
    (awayModulePresheaf X h)

/-- The comparison map from the sheafification of the presheaf of sectionwise localizations to
`𝒪_f`: the adjoint of `AlgebraicGeometry.RingedSite.awayModuleComparison`. -/
def awaySheafificationToAwayModule : awaySheafification X h ⟶ awayModule X h :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).symm
    (awayModuleComparison X h)

/-- The comparison map, read in abelian groups, is the sheafification map of
`CommRingCat`-valued presheaves. -/
theorem toPresheaf_awayModuleComparison :
    (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
        (awayModuleComparison X h) =
      Functor.whiskerRight (toSheafify X.J (awayPresheaf h))
        (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  ext U x
  rfl

/-- The adjunction bijection sends the comparison map from the sheafification to the comparison
map of presheaves. -/
private theorem sheafificationHomEquiv_awaySheafificationToAwayModule :
    (PresheafOfModules.sheafificationHomEquiv
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj))
      (awaySheafificationToAwayModule X h) = awayModuleComparison X h :=
  Equiv.apply_symm_apply _ _

/-- The comparison map factors through the sheafification unit of the presheaf of modules: this
is the triangle identity of the sheafification adjunction. -/
theorem toPresheaf_awayModuleComparison_fac :
    (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
        (awayModuleComparison X h) =
      toSheafify X.J (awayModulePresheaf X h).presheaf ≫
        (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
          (awaySheafificationToAwayModule X h).val := by
  rw [← sheafificationHomEquiv_awaySheafificationToAwayModule]
  exact PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def _ _

/-- The sheafification unit followed by the comparison map is the sheafification map of
`CommRingCat`-valued presheaves, read in abelian groups. -/
theorem toSheafify_comp_toPresheaf_awaySheafificationToAwayModule :
    toSheafify X.J (awayModulePresheaf X h).presheaf ≫
        (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
          (awaySheafificationToAwayModule X h).val =
      Functor.whiskerRight (toSheafify X.J (awayPresheaf h))
        (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  (toPresheaf_awayModuleComparison_fac X h).symm.trans (toPresheaf_awayModuleComparison X h)

/-- That composite is locally injective, being the sheafification map of a presheaf of
commutative rings read in abelian groups. -/
theorem isLocallyInjective_toSheafify_comp :
    Presheaf.IsLocallyInjective X.J
      (toSheafify X.J (awayModulePresheaf X h).presheaf ≫
        (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
          (awaySheafificationToAwayModule X h).val) := by
  constructor
  intro U x y hxy
  rw [toSheafify_comp_toPresheaf_awaySheafificationToAwayModule] at hxy
  exact Presheaf.equalizerSieve_mem X.J (toSheafify X.J (awayPresheaf h)) x y hxy

/-- That composite is locally surjective, being the sheafification map of a presheaf of
commutative rings read in abelian groups. -/
theorem isLocallySurjective_toSheafify_comp :
    Presheaf.IsLocallySurjective X.J
      (toSheafify X.J (awayModulePresheaf X h).presheaf ≫
        (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
          (awaySheafificationToAwayModule X h).val) := by
  constructor
  intro U x
  rw [toSheafify_comp_toPresheaf_awaySheafificationToAwayModule]
  exact Presheaf.imageSieve_mem X.J (toSheafify X.J (awayPresheaf h)) x

/-- **The comparison map is invertible**: the sheafification unit is locally bijective and so is
its composite with the comparison map, hence so is the comparison map, and a locally bijective
map of sheaves of modules is an isomorphism. -/
instance isIso_awaySheafificationToAwayModule : IsIso (awaySheafificationToAwayModule X h) := by
  let η := toSheafify X.J (awayModulePresheaf X h).presheaf
  let qpre := (PresheafOfModules.toPresheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj).map
    (awaySheafificationToAwayModule X h).val
  have : Presheaf.IsLocallyInjective X.J (η ≫ qpre) := isLocallyInjective_toSheafify_comp X h
  have : Presheaf.IsLocallySurjective X.J (η ≫ qpre) := isLocallySurjective_toSheafify_comp X h
  have hqI : Presheaf.IsLocallyInjective X.J qpre :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective X.J η qpre
  have hqS : Presheaf.IsLocallySurjective X.J qpre :=
    Presheaf.isLocallySurjective_of_isLocallySurjective X.J η qpre
  have hqTo : IsIso ((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map
      (awaySheafificationToAwayModule X h)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hqI, hqS⟩
  exact isIso_of_reflects_iso _
    (SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **`𝒪_f`, as a sheaf of `𝒪`-modules, is the sheafification of the presheaf
`U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations.** -/
def awaySheafificationIsoAwayModule : awaySheafification X h ≅ awayModule X h :=
  asIso (awaySheafificationToAwayModule X h)

/-- The identification of `𝒪_f` with that sheafification is compatible with the canonical maps
out of `𝒪`. -/
theorem toModuleSheafification_comp_awaySheafificationToAwayModule :
    toModuleSheafification (unitToAwayModulePresheaf X h) ≫
        awaySheafificationToAwayModule X h =
      unitToAwayModule X h := by
  rw [toModuleSheafification_comp_eq_iff]
  exact (congrArg _ (sheafificationHomEquiv_awaySheafificationToAwayModule X h)).trans
    (unitToAwayModulePresheaf_comp_awayModuleComparison X h)

/-- **The universal property of `𝒪_f` as a sheaf of `𝒪`-modules.** A map `φ : 𝒪 ⟶ 𝒩` of sheaves
of `𝒪`-modules on whose modules of sections every power of the global section `f` acts
bijectively factors uniquely through the canonical map `𝒪 ⟶ 𝒪_f`.

This is the universal property of a sheafified sectionwise localization,
`AlgebraicGeometry.RingedSite.existsUnique_comp_toModuleSheafification`, transported along
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule`. Unlike
`AlgebraicGeometry.RingedSite.existsUnique_lift_toAwaySheaf`, which lifts only maps to sheaves of
*rings*, this lifts maps to an arbitrary sheaf of `𝒪`-modules. -/
theorem existsUnique_lift_unitToAwayModule
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (φ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ N)
    (hN : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      Function.Bijective fun t : N.val.obj U => globalSectionVal h U ^ n • t) :
    ∃! ψ : awayModule X h ⟶ N, unitToAwayModule X h ≫ ψ = φ := by
  have hN' : ∀ (U : X.Cᵒᵖ) (s : (awayMultiplicativeSubpresheaf h).obj U),
      Function.Bijective fun t : N.val.obj U => (s : X.O.obj.obj U) • t := by
    intro U s
    obtain ⟨n, hn⟩ := s.2
    rw [← hn]
    exact hN U n
  obtain ⟨ψ', hψ', huniq'⟩ := existsUnique_comp_toModuleSheafification
    (G := N) (unitToAwayModulePresheaf X h) φ
    ((awayMultiplicativeSubpresheaf h).sectionwiseLocalizationLift
      (unitToAwayModulePresheaf X h) (isLocalizedModule_unitToAwayModulePresheaf X h) φ.val hN')
    ((awayMultiplicativeSubpresheaf h).comp_sectionwiseLocalizationLift
      (unitToAwayModulePresheaf X h) (isLocalizedModule_unitToAwayModulePresheaf X h) φ.val hN')
    (fun _ _ hh => (awayMultiplicativeSubpresheaf h).hom_ext_of_isLocalizedModule
      (unitToAwayModulePresheaf X h) (isLocalizedModule_unitToAwayModulePresheaf X h) hN' hh)
  refine ⟨inv (awaySheafificationToAwayModule X h) ≫ ψ', ?_, ?_⟩
  · beta_reduce
    rw [← toModuleSheafification_comp_awaySheafificationToAwayModule, Category.assoc,
      IsIso.hom_inv_id_assoc, hψ']
  · intro ψ hψ
    have h1 : toModuleSheafification (unitToAwayModulePresheaf X h) ≫
        (awaySheafificationToAwayModule X h ≫ ψ) = φ := by
      rw [← Category.assoc, toModuleSheafification_comp_awaySheafificationToAwayModule, hψ]
    rw [← huniq' _ h1, IsIso.inv_hom_id_assoc]

/-- Two maps out of `𝒪_f` into a sheaf of `𝒪`-modules on which every power of `f` acts
bijectively agree as soon as they agree after restriction along `𝒪 ⟶ 𝒪_f`. -/
theorem hom_ext_unitToAwayModule
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hN : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      Function.Bijective fun t : N.val.obj U => globalSectionVal h U ^ n • t)
    {ψ₁ ψ₂ : awayModule X h ⟶ N}
    (hψ : unitToAwayModule X h ≫ ψ₁ = unitToAwayModule X h ≫ ψ₂) : ψ₁ = ψ₂ := by
  obtain ⟨ψ, -, huniq⟩ :=
    existsUnique_lift_unitToAwayModule X h N (unitToAwayModule X h ≫ ψ₁) hN
  rw [huniq ψ₁ rfl, huniq ψ₂ hψ.symm]

end AlgebraicGeometry.RingedSite

end
