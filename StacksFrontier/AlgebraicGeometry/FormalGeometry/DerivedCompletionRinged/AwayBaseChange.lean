module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdeal

/-!
# Inverting two global sections, one after the other

Let `(𝒞, 𝒪)` be a ringed site and let `h₁, h₂` be global sections of `𝒪`. Inverting the product
`h₁ h₂` is the same as inverting `h₂` and then inverting the image of `h₁` in `𝒪_{h₂}`:

`𝒪_{h₁ h₂} ≅ (𝒪_{h₂})_{h₁}`.

This is the *base change of the localization system* `S ↦ 𝒪_{f_S}` along `𝒪 ⟶ 𝒪_g`, read without
tensor products: the terms of the extended alternating Čech complex of `f_1, …, f_r` over the
localized ringed site `(𝒞, 𝒪_g)` — which are the sheaves `(𝒪_g)_{f_S}` — are identified with
sheaves `𝒪_{f_S g}` on the original ringed site.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayGlobalSection`: a global section read on the localized
  ringed site, with `AlgebraicGeometry.RingedSite.awayAwaySheaf` the iterated localization
  `(𝒪_{h₂})_{h₁}` and `AlgebraicGeometry.RingedSite.toAwayAwaySheaf` the canonical map into it.
* `AlgebraicGeometry.RingedSite.awayMulToAwayAway`,
  `AlgebraicGeometry.RingedSite.awayAwayToAwayMul`: the two comparison maps, and
  `AlgebraicGeometry.RingedSite.awayToAwayMul` the localization map `𝒪_{h₂} ⟶ 𝒪_{h₁ h₂}`.

## Main results

* `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_mul_left` and
  `AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_mul_right`: each factor of `h₁ h₂` becomes
  invertible in `𝒪_{h₁ h₂}`.
* `AlgebraicGeometry.RingedSite.awaySheafMulIso`: **`𝒪_{h₁ h₂} ≅ (𝒪_{h₂})_{h₁}`**, the iterated
  localization.

## Implementation notes

Everything is proved from the universal property
`AlgebraicGeometry.RingedSite.existsUnique_lift_toAwaySheaf` of a localization of sheaves of
*rings*; no module, tensor product or sheafification argument is needed. The four comparison maps
are not constructed but chosen by that universal property, and the two composites are identities
because they lift the same map out of `𝒪`.

Divisibility enters only through `isUnit_of_mul_isUnit_left`: the images of `h₁^n` and `h₂^n` in
`𝒪_{h₁ h₂}` multiply to the image of `(h₁ h₂)^n`, which is a unit, so each is a unit. The product
of the two global sections is `AlgebraicGeometry.RingedSite.mulGlobalSection`, the two-element
case of `AlgebraicGeometry.RingedSite.prodGlobalSection`.

The iterated localization is formed on `AlgebraicGeometry.RingedSite.awayRingedSite`, which has
the *same* underlying site, so `(𝒪_{h₂})_{h₁}` is again a sheaf on `𝒞` and the comparison maps
live in `Sheaf 𝒞.J CommRingCat`. The implicit ringed site of
`AlgebraicGeometry.RingedSite.awaySheaf` is therefore ambiguous at every use, and
`awayAwaySheaf` and `toAwayAwaySheaf` are introduced to pin it down once.

### What this gives together with `AwayTensorBaseChange.lean`

The identification `𝒪_{f_S} ⊗_𝒪 𝒪_g ≅ (𝒪_g)_{f_S}` that [Stacks, Tag 099B] needs is now
available: it is `AlgebraicGeometry.RingedSite.awayTensorIsoBaseChangeAwayModule` of
`AwayTensorBaseChange.lean`, at `𝒪' := 𝒪_g` and `φ := 𝒪 ⟶ 𝒪_g`, whose base-changed global section
`AlgebraicGeometry.RingedSite.baseChangeGlobalSection` is by definition the `awayGlobalSection`
of this file, and whose `baseChangeRingedSite` is this file's `awayRingedSite`. Together with
`awaySheafMulIso` below — once that isomorphism of sheaves of *rings* is read in `𝒪`-modules,
which `SheafOfModules.restrictScalars` does and which is not written out anywhere — it reads
`𝒪_{f_S} ⊗_𝒪 𝒪_g ≅ (𝒪_g)_{f_S} ≅ 𝒪_{f_S g}`, which is the form in which the terms of the Čech
complex over `(𝒞, 𝒪_g)` are sheaves on `(𝒞, 𝒪)`.

Those two halves are proved by different means, and deliberately so. This file's half is about
sheaves of *rings* and needs only their universal property. The other half is about sheaves of
*modules*: neither side of `𝒪_f ⊗_𝒪 𝒪' ≅ 𝒪'_{f'}` is presented as a tensor product or as a
localization, both being sheafifications, so it is proved by rewriting each as the sheafification
over `𝒪` of an explicit presheaf and identifying those presheaves sectionwise.

The lower row of [Stacks, Tag 099H] no longer needs anything beyond this: the identification of
the terms is assembled into an isomorphism of *complexes* by
`Stacks.Sheaves.CechFlatNeighbourhood.extendedAlternatingCechBaseChangeIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean`, through the naturality
in `S` of `𝒪_{f_S} ⊗_𝒪 𝒪' ≅ 𝒪'_{f'_S}` proved there — by a third route, the colimit of the
Koszul systems, on which the comparison is constant in `S`; see the note on the lower row in that
file for why the route through the sheafifications was not the one taken.

Nothing here carries a `stacks` attribute: these are general facts about the localization of the
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

/-- The global section `h₁` read on the ringed site obtained by inverting `h₂`: its image
under the canonical map `𝒪 ⟶ 𝒪_{h₂}`. -/
def awayGlobalSection (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections ((awayRingedSite X h₂).O.obj ⋙ forget CommRingCat.{u}) :=
  h₁ ≫ Functor.whiskerRight (toAwaySheaf h₂).hom (forget CommRingCat.{u})

/-- `(𝒪_{h₂})_{h₁}`: the sheaf of rings obtained by inverting `h₂` and then inverting the
image of `h₁`. -/
abbrev awayAwaySheaf (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Sheaf X.J CommRingCat.{u} :=
  awaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂)

/-- The canonical map `𝒪_{h₂} ⟶ (𝒪_{h₂})_{h₁}`. -/
abbrev toAwayAwaySheaf (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awaySheaf h₂ ⟶ awayAwaySheaf X h₁ h₂ :=
  toAwaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂)

/-- On sections over `U`, the value of `awayGlobalSection X h₁ h₂` is the image of the value of
`h₁` under `𝒪(U) ⟶ 𝒪_{h₂}(U)`. -/
theorem globalSectionVal_awayGlobalSection
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) :
    globalSectionVal (awayGlobalSection X h₁ h₂) U =
      ((toAwaySheaf h₂).hom.app U).hom (globalSectionVal h₁ U) := rfl

/-- The images in `𝒪_{h₁ h₂}` of a power of `h₁` and the same power of `h₂` multiply to a unit. -/
private theorem isUnit_toAwaySheaf_mul_pow_mul
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf (mulGlobalSection X h₁ h₂)).hom.app U).hom (globalSectionVal h₁ U ^ n) *
      ((toAwaySheaf (mulGlobalSection X h₁ h₂)).hom.app U).hom (globalSectionVal h₂ U ^ n)) := by
  rw [← map_mul, ← mul_pow, ← globalSectionVal_mulGlobalSection]
  exact isUnit_toAwaySheaf (mulGlobalSection X h₁ h₂) U n

/-- Every power of `h₁` becomes invertible in `𝒪_{h₁ h₂}`: its image times the image of the
corresponding power of `h₂` is a unit. -/
theorem isUnit_toAwaySheaf_mul_left
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf (mulGlobalSection X h₁ h₂)).hom.app U).hom
      (globalSectionVal h₁ U ^ n)) :=
  isUnit_of_mul_isUnit_left (isUnit_toAwaySheaf_mul_pow_mul X h₁ h₂ U n)

/-- Every power of `h₂` becomes invertible in `𝒪_{h₁ h₂}`. -/
theorem isUnit_toAwaySheaf_mul_right
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf (mulGlobalSection X h₁ h₂)).hom.app U).hom
      (globalSectionVal h₂ U ^ n)) :=
  isUnit_of_mul_isUnit_right (isUnit_toAwaySheaf_mul_pow_mul X h₁ h₂ U n)

/-- Reading the composite `𝒪 ⟶ 𝒪_{h₂} ⟶ (𝒪_{h₂})_{h₁}` on sections. -/
theorem comp_toAwaySheaf_apply
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ)
    (x : X.O.obj.obj U) :
    (((toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂).hom.app U).hom) x =
      ((toAwayAwaySheaf X h₁ h₂).hom.app U).hom
        (((toAwaySheaf h₂).hom.app U).hom x) := rfl

/-- Every power of `h₂` becomes invertible in `(𝒪_{h₂})_{h₁}`: it is already invertible in
`𝒪_{h₂}`, and a ring homomorphism carries a unit to a unit. -/
theorem isUnit_comp_toAwaySheaf_right
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂).hom.app U).hom
      (globalSectionVal h₂ U ^ n)) := by
  rw [comp_toAwaySheaf_apply]
  exact (isUnit_toAwaySheaf h₂ U n).map ((toAwayAwaySheaf X h₁ h₂).hom.app U).hom

/-- Every power of `h₁` becomes invertible in `(𝒪_{h₂})_{h₁}`. -/
theorem isUnit_comp_toAwaySheaf_left
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂).hom.app U).hom
      (globalSectionVal h₁ U ^ n)) := by
  rw [comp_toAwaySheaf_apply, map_pow, ← globalSectionVal_awayGlobalSection]
  exact isUnit_toAwaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂) U n

/-- Every power of `h₁ h₂` becomes invertible in `(𝒪_{h₂})_{h₁}`. -/
theorem isUnit_comp_toAwaySheaf_mul
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂).hom.app U).hom
      (globalSectionVal (mulGlobalSection X h₁ h₂) U ^ n)) := by
  rw [globalSectionVal_mulGlobalSection, mul_pow, map_mul]
  exact (isUnit_comp_toAwaySheaf_left X h₁ h₂ U n).mul
    (isUnit_comp_toAwaySheaf_right X h₁ h₂ U n)

/-- **The comparison `𝒪_{h₁ h₂} ⟶ (𝒪_{h₂})_{h₁}`**: the unique map of sheaves of rings through
which `𝒪 ⟶ (𝒪_{h₂})_{h₁}` factors. -/
def awayMulToAwayAway (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awaySheaf (mulGlobalSection X h₁ h₂) ⟶ awayAwaySheaf X h₁ h₂ :=
  (existsUnique_lift_toAwaySheaf (mulGlobalSection X h₁ h₂) (awayAwaySheaf X h₁ h₂)
    (toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂)
    (isUnit_comp_toAwaySheaf_mul X h₁ h₂)).choose

/-- The composite `𝒪 ⟶ 𝒪_{h₁ h₂} ⟶ (𝒪_{h₂})_{h₁}` is the composite
`𝒪 ⟶ 𝒪_{h₂} ⟶ (𝒪_{h₂})_{h₁}`. -/
theorem toAwaySheaf_comp_awayMulToAwayAway
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    toAwaySheaf (mulGlobalSection X h₁ h₂) ≫ awayMulToAwayAway X h₁ h₂ =
      toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂ :=
  (existsUnique_lift_toAwaySheaf (mulGlobalSection X h₁ h₂) (awayAwaySheaf X h₁ h₂)
    (toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂)
    (isUnit_comp_toAwaySheaf_mul X h₁ h₂)).choose_spec.1

/-- The map `𝒪_{h₂} ⟶ 𝒪_{h₁ h₂}` of the localization system. -/
def awayToAwayMul (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awaySheaf h₂ ⟶ awaySheaf (mulGlobalSection X h₁ h₂) :=
  (existsUnique_lift_toAwaySheaf h₂ (awaySheaf (mulGlobalSection X h₁ h₂))
    (toAwaySheaf (mulGlobalSection X h₁ h₂)) (isUnit_toAwaySheaf_mul_right X h₁ h₂)).choose

/-- The composite `𝒪 ⟶ 𝒪_{h₂} ⟶ 𝒪_{h₁ h₂}` is the canonical map `𝒪 ⟶ 𝒪_{h₁ h₂}`. -/
theorem toAwaySheaf_comp_awayToAwayMul
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    toAwaySheaf h₂ ≫ awayToAwayMul X h₁ h₂ = toAwaySheaf (mulGlobalSection X h₁ h₂) :=
  (existsUnique_lift_toAwaySheaf h₂ (awaySheaf (mulGlobalSection X h₁ h₂))
    (toAwaySheaf (mulGlobalSection X h₁ h₂))
    (isUnit_toAwaySheaf_mul_right X h₁ h₂)).choose_spec.1

/-- Every power of `h₁`, read on the localized ringed site, becomes invertible in
`𝒪_{h₁ h₂}`. -/
theorem isUnit_awayToAwayMul
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (((awayToAwayMul X h₁ h₂).hom.app U).hom
      (globalSectionVal (awayGlobalSection X h₁ h₂) U ^ n)) := by
  rw [globalSectionVal_awayGlobalSection, ← map_pow]
  have hcomp : ((awayToAwayMul X h₁ h₂).hom.app U).hom
        (((toAwaySheaf h₂).hom.app U).hom (globalSectionVal h₁ U ^ n)) =
      (((toAwaySheaf h₂ ≫ awayToAwayMul X h₁ h₂).hom.app U).hom)
        (globalSectionVal h₁ U ^ n) := rfl
  rw [hcomp, toAwaySheaf_comp_awayToAwayMul]
  exact isUnit_toAwaySheaf_mul_left X h₁ h₂ U n

/-- **The comparison `(𝒪_{h₂})_{h₁} ⟶ 𝒪_{h₁ h₂}`**. -/
def awayAwayToAwayMul (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awayAwaySheaf X h₁ h₂ ⟶ awaySheaf (X := X) (mulGlobalSection X h₁ h₂) :=
  (existsUnique_lift_toAwaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂)
    (awaySheaf (X := X) (mulGlobalSection X h₁ h₂)) (awayToAwayMul X h₁ h₂)
    (isUnit_awayToAwayMul X h₁ h₂)).choose

/-- The composite `𝒪_{h₂} ⟶ (𝒪_{h₂})_{h₁} ⟶ 𝒪_{h₁ h₂}` is `awayToAwayMul X h₁ h₂`. -/
theorem toAwaySheaf_comp_awayAwayToAwayMul
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    toAwayAwaySheaf X h₁ h₂ ≫ awayAwayToAwayMul X h₁ h₂ = awayToAwayMul X h₁ h₂ :=
  (existsUnique_lift_toAwaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂)
    (awaySheaf (X := X) (mulGlobalSection X h₁ h₂)) (awayToAwayMul X h₁ h₂)
    (isUnit_awayToAwayMul X h₁ h₂)).choose_spec.1

/-- The composite `𝒪_{h₂} ⟶ 𝒪_{h₁ h₂} ⟶ (𝒪_{h₂})_{h₁}` is the canonical map: both lift
`𝒪 ⟶ (𝒪_{h₂})_{h₁}` through `𝒪 ⟶ 𝒪_{h₂}`. -/
theorem awayToAwayMul_comp_awayMulToAwayAway
    (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awayToAwayMul X h₁ h₂ ≫ awayMulToAwayAway X h₁ h₂ = toAwayAwaySheaf X h₁ h₂ := by
  obtain ⟨φ₀, -, huniq⟩ := existsUnique_lift_toAwaySheaf h₂ (awayAwaySheaf X h₁ h₂)
    (toAwaySheaf h₂ ≫ toAwayAwaySheaf X h₁ h₂) (isUnit_comp_toAwaySheaf_right X h₁ h₂)
  rw [huniq (awayToAwayMul X h₁ h₂ ≫ awayMulToAwayAway X h₁ h₂) (by
      dsimp only
      rw [← Category.assoc, toAwaySheaf_comp_awayToAwayMul,
        toAwaySheaf_comp_awayMulToAwayAway]),
    huniq (toAwayAwaySheaf X h₁ h₂) rfl]

/-- **Inverting `h₁ h₂` is inverting `h₂` and then inverting `h₁`.** This is the base change of
the localization system: `𝒪_{h₁ h₂} ≅ (𝒪_{h₂})_{h₁}`. -/
def awaySheafMulIso (h₁ h₂ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    awaySheaf (mulGlobalSection X h₁ h₂) ≅ awayAwaySheaf X h₁ h₂ where
  hom := awayMulToAwayAway X h₁ h₂
  inv := awayAwayToAwayMul X h₁ h₂
  hom_inv_id := by
    obtain ⟨φ₀, -, huniq⟩ := existsUnique_lift_toAwaySheaf (mulGlobalSection X h₁ h₂)
      (awaySheaf (mulGlobalSection X h₁ h₂)) (toAwaySheaf (mulGlobalSection X h₁ h₂))
      (isUnit_toAwaySheaf (mulGlobalSection X h₁ h₂))
    rw [huniq (awayMulToAwayAway X h₁ h₂ ≫ awayAwayToAwayMul X h₁ h₂) (by
        dsimp only
        rw [← Category.assoc, toAwaySheaf_comp_awayMulToAwayAway, Category.assoc,
          toAwaySheaf_comp_awayAwayToAwayMul, toAwaySheaf_comp_awayToAwayMul]),
      huniq (𝟙 (awaySheaf (X := X) (mulGlobalSection X h₁ h₂))) (Category.comp_id _)]
  inv_hom_id := by
    obtain ⟨φ₀, -, huniq⟩ := existsUnique_lift_toAwaySheaf (X := awayRingedSite X h₂)
      (awayGlobalSection X h₁ h₂) (awayAwaySheaf X h₁ h₂) (toAwayAwaySheaf X h₁ h₂)
      (isUnit_toAwaySheaf (X := awayRingedSite X h₂) (awayGlobalSection X h₁ h₂))
    rw [huniq (awayAwayToAwayMul X h₁ h₂ ≫ awayMulToAwayAway X h₁ h₂) (by
        dsimp only
        rw [← Category.assoc, toAwaySheaf_comp_awayAwayToAwayMul,
          awayToAwayMul_comp_awayMulToAwayAway]),
      huniq (𝟙 (awayAwaySheaf X h₁ h₂)) (Category.comp_id _)]

end AlgebraicGeometry.RingedSite

end
