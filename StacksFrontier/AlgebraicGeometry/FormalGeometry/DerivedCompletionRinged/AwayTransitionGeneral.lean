module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechContractible

/-!
# Transition maps between localizations at arbitrary global sections

Let `(𝒞, 𝒪)` be a ringed site and let `h`, `h'` be global sections of `𝒪`. A map
`φ : 𝒪_h ⟶ 𝒪_{h'}` of sheaves of rings over `𝒪` exists as soon as every power of `h` is
invertible in `𝒪_{h'}`, is then unique, and this file collects what one does with it: it is an
isomorphism as soon as the powers of `h'` are invertible in `𝒪_h` as well, it is a map of sheaves
of `𝒪`-modules, and the powers of `h` act bijectively on `𝒪_{h'}`.

`CechContractible.lean` has all three facts for the sections
`AlgebraicGeometry.RingedSite.prodGlobalSection f ·` indexed by `Finset (Fin r)`, which is the
shape the extended alternating Čech complex is built at. The base change of that complex
along `𝒪 ⟶ 𝒪_g` replaces `𝒪_{f_S}` by `𝒪_{g f_S}`, whose index is *not* of that shape, so those
statements do not apply verbatim; the general forms are here.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayModuleMapOfComp`: a map `𝒪_h ⟶ 𝒪_{h'}` of sheaves of rings
  over `𝒪`, read as a map of sheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_of_toAwaySheaf_comp` and
  `AlgebraicGeometry.RingedSite.isIso_awayModuleMapOfComp`: **the general-section form of
  `AlgebraicGeometry.RingedSite.isIso_awayTransition_of_isUnit`** — a map over `𝒪` between two
  localizations of `𝒪` is invertible when each one inverts the section of the other.
* `AlgebraicGeometry.RingedSite.bijective_smul_awayModule_of_isUnit`: the powers of `h` act
  bijectively on the sections of `𝒪_{h'}` when they are invertible there. This is the hypothesis
  of the module universal property
  `AlgebraicGeometry.RingedSite.existsUnique_lift_unitToAwayModule`, so it is what makes a map out
  of `𝒪_h` into `𝒪_{h'}` unique.
* `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_of_comp`: invertibility is inherited along a
  factorisation of `𝒪 ⟶ 𝒪_{h'}` through `𝒪_h`, because a ring homomorphism carries a unit to a
  unit.

## Implementation notes

The invertibility criterion is proved exactly as
`AlgebraicGeometry.RingedSite.isIso_awayTransition_of_isUnit` is: the lift of `𝒪 ⟶ 𝒪_h` through
`𝒪_{h'}` is a two-sided inverse because each composite with it is a map over `𝒪` out of a
localization, as is the identity, and there is only one such map.

Nothing here carries a `stacks` attribute: these are general facts about localizations of the
structure sheaf of a ringed site at a global section, and the source states none of them.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  {h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}

/-- **The general-section form of `isIso_awayTransition_of_isUnit`.** A map `𝒪_h ⟶ 𝒪_{h'}` of
sheaves of rings over `𝒪` is invertible as soon as every power of `h'` is already invertible in
`𝒪_h`: the lift of `𝒪 ⟶ 𝒪_h` through `𝒪_{h'}` is a two-sided inverse, both composites lifting
the same map out of `𝒪`. -/
theorem isIso_of_toAwaySheaf_comp (φ : awaySheaf h ⟶ awaySheaf h')
    (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf h).hom.app U).hom (globalSectionVal h' U ^ n))) :
    IsIso φ := by
  obtain ⟨ψ, hψ, -⟩ := existsUnique_lift_toAwaySheaf h' (awaySheaf h) (toAwaySheaf h) hu
  have key : ∀ (k : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
      (χ : awaySheaf k ⟶ awaySheaf k), toAwaySheaf k ≫ χ = toAwaySheaf k → χ = 𝟙 _ := by
    intro k χ hχ
    obtain ⟨_, -, huniq⟩ := existsUnique_lift_toAwaySheaf k (awaySheaf k) (toAwaySheaf k)
      (isUnit_toAwaySheaf k)
    rw [huniq χ hχ, huniq (𝟙 _) (Category.comp_id _)]
  exact ⟨⟨ψ, key h _ (by rw [← Category.assoc, hφ, hψ]),
    key h' _ (by rw [← Category.assoc, hψ, hφ])⟩⟩

/-- A map `𝒪_h ⟶ 𝒪_{h'}` of sheaves of rings over `𝒪`, read as a map of sheaves of
`𝒪`-modules. -/
def awayModuleMapOfComp (φ : awaySheaf h ⟶ awaySheaf h')
    (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h') :
    awayModule X h ⟶ awayModule X h' :=
  SheafOfModules.unitRestrictScalarsMapOfComp (awayRingSheafMap X φ)
    (toAwayRingSheaf_comp_awayRingSheafMap X φ hφ)

/-- For `S ⊆ T` the transition map of the Čech system is this general map, at the ring map chosen
by the universal property. -/
theorem awayModuleTransition_eq_awayModuleMapOfComp {r : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    {S T : Finset (Fin r)} (hST : S ⊆ T) :
    awayModuleTransition X f hST =
      awayModuleMapOfComp X (awayTransition f hST) (toAwaySheaf_comp_awayTransition f hST) :=
  rfl

/-- The canonical maps out of `𝒪` are compatible with a map over `𝒪`, read in modules. -/
theorem unitToAwayModule_comp_awayModuleMapOfComp (φ : awaySheaf h ⟶ awaySheaf h')
    (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h') :
    unitToAwayModule X h ≫ awayModuleMapOfComp X φ hφ = unitToAwayModule X h' :=
  SheafOfModules.unitToRestrictScalarsUnit_comp _

/-- **The general-section form of `isIso_awayModuleTransition_of_subset_insert`**: a map
`𝒪_h ⟶ 𝒪_{h'}` over `𝒪` is an isomorphism of sheaves of `𝒪`-modules when each of the two
localizations inverts the section of the other. -/
theorem isIso_awayModuleMapOfComp (φ : awaySheaf h ⟶ awaySheaf h')
    (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf h).hom.app U).hom (globalSectionVal h' U ^ n))) :
    IsIso (awayModuleMapOfComp X φ hφ) := by
  have : IsIso φ := isIso_of_toAwaySheaf_comp X φ hφ hu
  exact SheafOfModules.isIso_unitRestrictScalarsMap
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) _

/-- **The powers of `h` act bijectively on the sections of `𝒪_{h'}`** as soon as they are
invertible there: the action is multiplication by the image, and multiplication by a unit is
bijective. This is the hypothesis of the universal property of `𝒪_h` as a sheaf of
`𝒪`-modules. -/
theorem bijective_smul_awayModule_of_isUnit (U : X.Cᵒᵖ) (n : ℕ)
    (hu : IsUnit (((toAwaySheaf h').hom.app U).hom (globalSectionVal h U ^ n))) :
    Function.Bijective
      fun t : (awayModule X h').val.obj U => globalSectionVal h U ^ n • t := by
  have hb : Function.Bijective
      fun t : (awaySheaf h').obj.obj U =>
        ((toAwaySheaf h').hom.app U).hom (globalSectionVal h U ^ n) * t :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hu
  exact hb

/-- Invertibility of a global section is inherited along a factorisation: if `𝒪 ⟶ 𝒪_{h'}`
factors through `𝒪_h`, then every section invertible in `𝒪_h` is invertible in `𝒪_{h'}`. -/
theorem isUnit_toAwaySheaf_of_comp (φ : awaySheaf h ⟶ awaySheaf h')
    (hφ : toAwaySheaf h ≫ φ = toAwaySheaf h')
    {k : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})} (U : X.Cᵒᵖ) (n : ℕ)
    (hu : IsUnit (((toAwaySheaf h).hom.app U).hom (globalSectionVal k U ^ n))) :
    IsUnit (((toAwaySheaf h').hom.app U).hom (globalSectionVal k U ^ n)) := by
  have heq : ((toAwaySheaf h').hom.app U).hom (globalSectionVal k U ^ n) =
      (φ.hom.app U).hom (((toAwaySheaf h).hom.app U).hom (globalSectionVal k U ^ n)) :=
    congrArg (fun α : X.O ⟶ awaySheaf h' => (α.hom.app U).hom (globalSectionVal k U ^ n)) hφ.symm
  rw [heq]
  exact hu.map (φ.hom.app U).hom

end AlgebraicGeometry.RingedSite

end
