module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PicardGroupAndFirstCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Picard groups of first-order thickenings, and their torsion

Let `i : X ⟶ X'` be a first-order thickening of schemes, with square-zero ideal sheaf `ℐ`.
Sending a local section `f` of `ℐ` to the unit `1 + f` of `𝒪_{X'}` is a monomorphism of
sheaves of abelian groups, and the resulting sequence
`0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0` is short exact.  Its long exact cohomology sequence,
combined with the identification of the Picard group of a ringed space with the first
cohomology of its sheaf of units, is the canonical exact sequence
`0 → H⁰(X,ℐ) → H⁰(X',𝒪*_{X'}) → H⁰(X,𝒪*_X) → H¹(X,ℐ) → Pic(X') → Pic(X) → H²(X,ℐ) → ⋯`,
which continues in every degree.

## Main definitions

* `Stacks.Thickenings.onePlusHomOfSqZero`: for a square-zero ideal `I` of a commutative ring,
  the homomorphism `f ↦ 1 + f` from `I` to the units of the ring, written additively.
* `Stacks.Thickenings.idealAddSheaf`: the ideal sheaf of a morphism of schemes, viewed as a
  sheaf of abelian groups on the ambient scheme.
* `Stacks.Thickenings.idealToUnitsSheafHom`: the sheaf map `f ↦ 1 + f`.
* `Stacks.Thickenings.unitsRestrictionSheafHom`: restriction of units along the immersion.
* `Stacks.Thickenings.thickeningShortComplex`: the sequence of sheaves
  `0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0`.
* `Stacks.Thickenings.unitsCohomologyPicardEquiv`: the identification of the first cohomology
  of the sheaf of units of a scheme with its Picard group.
* `Stacks.Thickenings.idealToUnitsCohomology`, `Stacks.Thickenings.unitsToSubCohomology` and
  `Stacks.Thickenings.thickeningBoundary`: the three families of maps of the long exact
  sequence, in every degree.
* `Stacks.Thickenings.idealCohomologyEquiv` and `Stacks.Thickenings.unitsCohomologyEquiv`: the
  identifications of the cohomology of the ideal and of the units on the closed subscheme with
  the cohomology of the sheaves carried on the ambient scheme.
* `Stacks.Thickenings.picardOfIdeal`, `Stacks.Thickenings.picardRestriction` and
  `Stacks.Thickenings.picardBoundary`: the three maps `H¹(X,ℐ) → Pic(X') → Pic(X) → H²(X,ℐ)`.
* `Stacks.Thickenings.unitsToIdealCohomology`: the preceding map `H⁰(X,𝒪^*_X) → H¹(X,ℐ)` of the
  same sequence, in the spelling whose next map is `Stacks.Thickenings.picardOfIdeal`.
* `Stacks.Thickenings.cohomologyMapAddHom`: evaluation at a cohomology class, as a homomorphism
  from the group of morphisms of sheaves of abelian groups.

## Main results

* `Stacks.Thickenings.idealUnitsShortExact`: the sequence
  `0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0` is short exact.
* `Stacks.Thickenings.injective_idealToUnitsCohomology_zero`,
  `Stacks.Thickenings.exact_idealToUnitsCohomology`,
  `Stacks.Thickenings.exact_unitsToSubCohomology` and
  `Stacks.Thickenings.exact_thickeningBoundary`: the long exact sequence, in every degree.
* `Stacks.Thickenings.exact_picardOfIdeal` and
  `Stacks.Thickenings.exact_picardRestriction`: exactness at the two Picard groups.
* `Stacks.Thickenings.bijective_zsmul_cohomology_idealAddSheafOnSub`: for an integer `n`
  invertible in `𝒪_X`, multiplication by `n` is bijective on `H^k(X,ℐ)` in every degree.
* `Stacks.Thickenings.surjOn_picardRestriction_torsion`: the surjectivity half of
  [Stacks, Tag 0C6S] for a first-order thickening.
* `Stacks.Thickenings.injOn_picardRestriction_torsion`: the injectivity half of
  [Stacks, Tag 0C6S] for a first-order thickening, when the image of `H⁰(X,𝒪^*_X)` in `H¹(X,ℐ)`
  is saturated for multiplication by `n`.
* `Stacks.Thickenings.bijOn_picardRestriction_torsion`,
  `Stacks.Thickenings.bijOn_picardRestriction_torsion_of_injective_picardOfIdeal` and
  `Stacks.Thickenings.bijOn_picardRestriction_torsion_of_units_surjective`: the full statement
  of [Stacks, Tag 0C6S] for a first-order thickening, under the three successively stronger
  hypotheses that this image is saturated, that `H¹(X,ℐ) → Pic(X')` is injective, and that
  every invertible global function on `X` lifts to `X'`.
* `Stacks.Thickenings.surjOn_zsmul_of_exact`, `Stacks.Thickenings.injOn_zsmul_of_exact` and
  `Stacks.Thickenings.bijOn_zsmul_of_exact`: the underlying statement about the torsion
  subgroups along a four-term exact sequence of abelian groups.

## References

* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

attribute [local implicit_reducible]
  TopCat.Sheaf
  structureSheafRing
  RingedSpaceModuleAdjunction.structureSheafHom
  SheafOfModules.toSheaf
  PresheafOfModules.toPresheaf
  Stacks.Cohomology.SheafTorsor.sheafCohomologyOne

/-- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives. -/
local instance hasExtAbelianSheaf (Y : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  hasExt_of_enoughInjectives _

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-! ### The map `f ↦ 1 + f` on a square-zero ideal -/

section Ring

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The product of two elements of a square-zero ideal vanishes. -/
private theorem mul_eq_zero_of_mem_sqZero {I : Ideal R} (hI : I * I = ⊥) {x y : R} (hx : x ∈ I)
    (hy : y ∈ I) : x * y = 0 := by
  simpa [hI] using Ideal.mul_mem_mul hx hy

/-- For a square-zero ideal `I` of a commutative ring `R`, sending `f` to `1 + f` is a
homomorphism from `I` to the group of units of `R`, written additively. -/
def onePlusHomOfSqZero (I : Ideal R) (hI : I * I = ⊥) : I →+ Additive Rˣ where
  toFun x := Additive.ofMul ⟨1 + (x : R), 1 - (x : R), by
    have hxx : (x : R) * (x : R) = 0 := by simpa [hI] using Ideal.mul_mem_mul x.2 x.2
    linear_combination -hxx,
    by
      have hxx : (x : R) * (x : R) = 0 := by simpa [hI] using Ideal.mul_mem_mul x.2 x.2
      linear_combination -hxx⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    apply Units.ext
    have hxy : (x : R) * (y : R) = 0 := by simpa [hI] using Ideal.mul_mem_mul x.2 y.2
    change 1 + ((x : R) + (y : R)) = (1 + (x : R)) * (1 + (y : R))
    linear_combination -hxy

/-- A ring homomorphism carrying a square-zero ideal into a square-zero ideal commutes with
`f ↦ 1 + f`. -/
theorem onePlusHomOfSqZero_map (I : Ideal R) (hI : I * I = ⊥) (J : Ideal S) (hJ : J * J = ⊥)
    (f : R →+* S) (x : I) (hx : f x ∈ J) :
    Units.map f ((onePlusHomOfSqZero I hI x).toMul) =
      (onePlusHomOfSqZero J hJ ⟨f x, hx⟩).toMul := by
  apply Units.ext
  simp [onePlusHomOfSqZero]

/-- The map `f ↦ 1 + f` on a square-zero ideal is injective. -/
theorem onePlusHomOfSqZero_injective (I : Ideal R) (hI : I * I = ⊥) :
    Function.Injective (onePlusHomOfSqZero I hI) := by
  intro x y h
  have h' : (1 + (x : R) : R) = 1 + (y : R) :=
    congrArg (fun z : Rˣ => (z : R)) (congrArg Additive.toMul h)
  exact Subtype.ext (add_left_cancel (a := (1 : R)) h')

/-- A unit dies under a ring homomorphism with kernel `I` exactly when it is of the form `1 + f`
with `f` in `I`. -/
private theorem map_units_eq_one_iff_exists_onePlus (I : Ideal R) (hI : I * I = ⊥) (f : R →+* S)
    (hker : RingHom.ker f = I) (u : Rˣ) :
    Units.map f.toMonoidHom u = 1 ↔ ∃ x : I, (onePlusHomOfSqZero I hI x).toMul = u := by
  constructor
  · intro hu
    have hfu : f (u : R) = 1 := by simpa using congrArg (fun z : Sˣ => (z : S)) hu
    have hval : (u : R) - 1 ∈ I := by
      rw [← hker, RingHom.mem_ker, map_sub, hfu]
      simp
    refine ⟨⟨(u : R) - 1, hval⟩, ?_⟩
    apply Units.ext
    simp [onePlusHomOfSqZero]
  · rintro ⟨x, rfl⟩
    apply Units.ext
    change f (1 + (x : R)) = 1
    have hx : f (x : R) = 0 := RingHom.mem_ker.mp (hker ▸ x.2)
    rw [map_add, hx]
    simp

/-- A unit of the form `1 + f` with `f` in the ideal is trivial modulo that ideal. -/
theorem onePlusHomOfSqZero_quotient_eq_one (I : Ideal R) (hI : I * I = ⊥) (x : I) :
    Units.map (Ideal.Quotient.mk I).toMonoidHom ((onePlusHomOfSqZero I hI x).toMul) = 1 :=
  (map_units_eq_one_iff_exists_onePlus I hI (Ideal.Quotient.mk I) Ideal.mk_ker _).mpr ⟨x, rfl⟩

/-- A unit that is trivial modulo a square-zero ideal is of the form `1 + f` with `f` in that
ideal. -/
theorem units_eq_onePlus_of_quotient_eq_one (I : Ideal R) (hI : I * I = ⊥) (u : Rˣ)
    (hu : Units.map (Ideal.Quotient.mk I).toMonoidHom u = 1) :
    ∃ x : I, (onePlusHomOfSqZero I hI x).toMul = u :=
  (map_units_eq_one_iff_exists_onePlus I hI (Ideal.Quotient.mk I) Ideal.mk_ker _).mp hu

/-- A unit is trivial modulo a square-zero ideal exactly when it is of the form `1 + f` with
`f` in that ideal. -/
@[ega "IV 21.13.9" "more general", sga "6 XII 3.1" "partial"]
theorem onePlusHomOfSqZero_exact_at_units (I : Ideal R) (hI : I * I = ⊥) (u : Rˣ) :
    Units.map (Ideal.Quotient.mk I).toMonoidHom u = 1 ↔
      ∃ x : I, (onePlusHomOfSqZero I hI x).toMul = u :=
  map_units_eq_one_iff_exists_onePlus I hI (Ideal.Quotient.mk I) Ideal.mk_ker _

/-- A unit dies under a ring homomorphism with square-zero kernel exactly when it is of the
form `1 + f` with `f` in that kernel. -/
@[sga "6 XII 3.1" "partial"]
theorem onePlusHomOfSqZero_exact_for (I : Ideal R) (hI : I * I = ⊥) (f : R →+* S)
    (hker : RingHom.ker f = I) (u : Rˣ) :
    Units.map f.toMonoidHom u = 1 ↔
      ∃ x : I, (onePlusHomOfSqZero I hI x).toMul = u :=
  map_units_eq_one_iff_exists_onePlus I hI f hker u

/-- A surjection of commutative rings with square-zero kernel is surjective on units. -/
theorem unitsMap_surjective_of_sqZero_ker (I : Ideal R) (f : R →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f = I) (hI : I * I = ⊥) (u : Sˣ) :
    ∃ v : Rˣ, Units.map f.toMonoidHom v = u := by
  obtain ⟨a, ha⟩ := hf (u : S)
  obtain ⟨b, hb⟩ := hf ((u⁻¹ : Sˣ) : S)
  have hxker : a * b - 1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_mul, ha, hb]
    simp
  have hxI : a * b - 1 ∈ I := by simpa [hker] using hxker
  have hxx := mul_eq_zero_of_mem_sqZero hI hxI hxI
  exact ⟨⟨a, b * (1 - (a * b - 1)), by linear_combination -hxx, by linear_combination -hxx⟩,
    Units.ext ha⟩

end Ring

/-! ### Sections of the ideal of a first-order thickening -/

section Affine

variable {X X' : Scheme.{u}}

/-- On an affine open of the ambient scheme the kernel ideal of a first-order thickening is
square-zero. -/
theorem affineKer_sq_eq_bot (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (U : X'.affineOpens) : (i.ker.ideal U) ^ 2 = ⊥ := by
  simpa using congrArg (fun J : X'.IdealSheafData => J.ideal U) hi.2

/-- On an affine open of the ambient scheme the kernel ideal of a first-order thickening has
zero self-product. -/
private theorem affineKer_mul_eq_bot (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (U : X'.affineOpens) : i.ker.ideal U * i.ker.ideal U = ⊥ := by
  simpa [pow_two] using affineKer_sq_eq_bot i hi U

/-- A section of the kernel ideal of a first-order thickening over an affine open squares to
zero. -/
theorem affineKer_section_sq (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (U : X'.affineOpens) (x : Γ(X', U)) (hx : x ∈ i.ker.ideal U) : x * x = 0 :=
  mul_eq_zero_of_mem_sqZero (affineKer_mul_eq_bot i hi U) hx hx

/-- Two sections of the kernel ideal of a first-order thickening over an affine open have zero
product. -/
theorem affineKer_section_mul (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (U : X'.affineOpens) (x y : Γ(X', U))
    (hx : x ∈ i.ker.ideal U) (hy : y ∈ i.ker.ideal U) : x * y = 0 :=
  mul_eq_zero_of_mem_sqZero (affineKer_mul_eq_bot i hi U) hx hy

/-- Over an affine open, a unit of the ambient scheme restricts to the identity on the closed
subscheme exactly when it is `1 + f` for a section `f` of the kernel ideal. -/
theorem affineKer_units_exact (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.affineOpens) (u : Γ(X', U)ˣ) :
    Units.map (CommRingCat.Hom.hom (i.app (U : X'.Opens))).toMonoidHom u = 1 ↔
      ∃ x : i.ker.ideal U,
        (onePlusHomOfSqZero (i.ker.ideal U)
          (by simpa [pow_two] using affineKer_sq_eq_bot i hi U) x).toMul = u := by
  let f := CommRingCat.Hom.hom (i.app (U : X'.Opens))
  simpa [f] using onePlusHomOfSqZero_exact_for (i.ker.ideal U)
    (affineKer_mul_eq_bot i hi U) f (Scheme.Hom.ker_apply i U).symm u

/-- A closed immersion is surjective on sections over an affine open of the target. -/
theorem app_surjective_of_isClosedImmersion (i : X ⟶ X') (hi : IsClosedImmersion i)
    (U : X'.affineOpens) :
    Function.Surjective (CommRingCat.Hom.hom (i.app (U : X'.Opens))) := by
  let : IsClosedImmersion i := hi
  exact Scheme.Hom.app_surjective i U U.2

/-- Over an affine open, a first-order thickening is surjective on units. -/
theorem affineKer_units_surjective (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.affineOpens) :
    Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app U)).toMonoidHom) :=
  unitsMap_surjective_of_sqZero_ker (i.ker.ideal U)
    (CommRingCat.Hom.hom (i.app U)) (app_surjective_of_isClosedImmersion i hi.1 U)
    (Scheme.Hom.ker_apply i U).symm (affineKer_mul_eq_bot i hi U)

end Affine

/-! ### The short exact sequence of sheaves -/

section Sheaves

variable {X X' : Scheme.{u}}

/-- The ideal sheaf of a morphism of schemes, as a sheaf of modules on the ambient scheme. -/
abbrev idealModuleSheaf (i : X ⟶ X') :
    _root_.SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace) :=
  Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom

/-- The ideal sheaf of a morphism of schemes, viewed as a sheaf of abelian groups on the
ambient scheme. -/
abbrev idealAddSheaf (i : X ⟶ X') : TopCat.Sheaf AddCommGrpCat.{u} X' :=
  (_root_.SheafOfModules.toSheaf (structureSheafRing X'.toSheafedSpace)).obj (idealModuleSheaf i)

/-- The sheaf of units of the closed subscheme, pushed forward to the ambient scheme. -/
abbrev pushforwardUnitsSheaf (i : X ⟶ X') : TopCat.Sheaf AddCommGrpCat.{u} X' :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj
    (Stacks.Cohomology.Generators.unitsSheaf X.toLocallyRingedSpace.toRingedSpace)

/-- The ideal sheaf of a morphism of schemes, pulled back to the closed subscheme. -/
abbrev idealAddSheafOnSub (i : X ⟶ X') : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} i.base).obj (idealAddSheaf i)

/-- The inclusion of the ideal sheaf of a morphism of schemes into the structure sheaf of the
ambient scheme: the ideal sheaf is the kernel of restriction of functions. -/
abbrev idealInclusion (i : X ⟶ X') :
    idealModuleSheaf i ⟶ _root_.SheafOfModules.unit (structureSheafRing X'.toSheafedSpace) :=
  kernel.ι (_root_.SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom i.toLRSHom.toShHom))

/-- Restriction of units along a morphism of schemes, as a map of sheaves of abelian groups on
the ambient scheme. -/
def unitsRestrictionSheafHom (i : X ⟶ X') :
    Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace ⟶
      pushforwardUnitsSheaf i := by
  let J := Opens.grothendieckTopology X'.toSheafedSpace
  let f₁ := sheafCompose J (forget₂ CommRingCat CommMonCat)
  let f₂ := sheafCompose J CommMonCat.units
  let f₃ := sheafCompose J commGroupAddCommGroupEquivalence.functor
  let c : X'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat i.base).obj X.sheaf :=
    ObjectProperty.homMk i.c
  change f₃.obj (f₂.obj (f₁.obj X'.sheaf)) ⟶ _
  exact f₃.map (f₂.map (f₁.map c))

/-- Restriction of units is restriction of units on sections. -/
theorem unitsRestrictionSheafHom_app (i : X ⟶ X') (U : X'.Opens) (s : Γ(X', U)ˣ) :
    (unitsRestrictionSheafHom i).hom.app (op U) (Additive.ofMul s) =
      Additive.ofMul (Units.map (i.app U).hom.toMonoidHom s) :=
  rfl

/-- A section of the ideal sheaf, viewed as a section of the structure sheaf of the ambient
scheme. -/
abbrev idealSection (i : X ⟶ X') (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) : Γ(X', U) :=
  (idealInclusion i).val.app (op U) s

/-- Restriction of a section of the ideal sheaf to a smaller open. -/
abbrev idealRestrict (i : X ⟶ X') {U V : X'.Opens} (h : V ≤ U)
    (s : (idealModuleSheaf i).val.obj (op U)) : (idealModuleSheaf i).val.obj (op V) :=
  (idealModuleSheaf i).val.map (homOfLE h).op s

/-- Viewing the zero section of the ideal sheaf in the structure sheaf gives zero. -/
theorem idealSection_zero (i : X ⟶ X') (U : X'.Opens) :
    idealSection i U 0 = 0 :=
  map_zero (ConcreteCategory.hom ((idealInclusion i).val.app (op U)))

/-- Viewing a section of the ideal sheaf in the structure sheaf is additive. -/
theorem idealSection_add (i : X ⟶ X') (U : X'.Opens)
    (s t : (idealModuleSheaf i).val.obj (op U)) :
    idealSection i U (s + t) = idealSection i U s + idealSection i U t :=
  map_add (ConcreteCategory.hom ((idealInclusion i).val.app (op U))) s t

/-- A section of the ideal sheaf dies on the closed subscheme. -/
theorem idealSection_map_zero (i : X ⟶ X') (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    (i.app U).hom (idealSection i U s) = 0 := by
  have h := congrArg
    (fun f : idealModuleSheaf i ⟶
        (_root_.SheafOfModules.pushforward (structureSheafHom i.toLRSHom.toShHom)).obj
          (_root_.SheafOfModules.unit (structureSheafRing X.toSheafedSpace)) =>
      ConcreteCategory.hom (f.val.app (op U)) s)
    (kernel.condition (_root_.SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom)))
  simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  exact h

/-- Over an affine open, a section of the ideal sheaf lies in the kernel ideal. -/
theorem idealSection_mem_ker (i : X ⟶ X') [QuasiCompact i] (U : X'.affineOpens)
    (s : (idealModuleSheaf i).val.obj (op (U : X'.Opens))) :
    idealSection i U s ∈ i.ker.ideal U := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  exact idealSection_map_zero i (U : X'.Opens) s

/-- Viewing a section of the ideal sheaf in the structure sheaf commutes with restriction. -/
theorem idealSection_restrict (i : X ⟶ X') {U V : X'.Opens} (h : V ≤ U)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    ConcreteCategory.hom (X'.presheaf.map (homOfLE h).op) (idealSection i U s) =
      idealSection i V (idealRestrict i h s) :=
  (PresheafOfModules.naturality_apply (idealInclusion i).val (homOfLE h).op s).symm

/-- The inclusion of the ideal sheaf into the structure sheaf is injective on sections. -/
theorem idealSection_injective (i : X ⟶ X') (U : X'.Opens) :
    Function.Injective (idealSection i U) := by
  have hm : Mono ((_root_.SheafOfModules.evaluation (structureSheafRing X'.toSheafedSpace)
      (op U)).map (idealInclusion i)) :=
    Functor.map_mono _ (idealInclusion i)
  exact (ModuleCat.mono_iff_injective _).mp hm

/-- Over an affine open, every section of the kernel ideal comes from a section of the ideal
sheaf. -/
theorem idealSection_lift_affine (i : X ⟶ X') [QuasiCompact i] (U : X'.affineOpens)
    (a : Γ(X', U.1)) (ha : a ∈ i.ker.ideal U) :
    ∃ s : (idealModuleSheaf i).val.obj (op U.1), idealSection i U.1 s = a := by
  let q := _root_.SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom i.toLRSHom.toShHom)
  let E := _root_.SheafOfModules.evaluation (structureSheafRing X'.toSheafedSpace) (op U.1)
  let : E.PreservesZeroMorphisms := ⟨by
    intro A B
    ext z
    rfl⟩
  have hqa : (q.val.app (op U.1)).hom a = 0 := by
    change (i.app U).hom a = 0
    exact RingHom.mem_ker.mp (by rwa [← Scheme.Hom.ker_apply])
  let κ : (kernel q).val.obj (op U.1) ≅ kernel (q.val.app (op U.1)) :=
    PreservesKernel.iso E q
  let sa : (q.val.app (op U.1)).hom.ker := ⟨a, LinearMap.mem_ker.mpr hqa⟩
  refine ⟨κ.inv.hom ((ModuleCat.kernelIsoKer (q.val.app (op U.1))).inv.hom sa), ?_⟩
  have hκ : κ.inv ≫ (kernel.ι q).val.app (op U.1) = kernel.ι (q.val.app (op U.1)) :=
    PreservesKernel.iso_inv_ι E q
  have h := congrArg (fun f => f.hom
      ((ModuleCat.kernelIsoKer (q.val.app (op U.1))).inv.hom sa)) hκ
  have hsub : (kernel.ι (q.val.app (op U.1))).hom
      ((ModuleCat.kernelIsoKer (q.val.app (op U.1))).inv.hom sa) = a := by
    change ((ModuleCat.kernelIsoKer (q.val.app (op U.1))).inv ≫
      kernel.ι (q.val.app (op U.1))).hom sa = a
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  exact h.trans hsub

/-- Two sections of the ideal sheaf of a first-order thickening have zero product. -/
theorem idealSection_mul_zero (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens)
    (s t : (idealModuleSheaf i).val.obj (op U)) :
    idealSection i U s * idealSection i U t = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := X'.presheaf) X'.IsSheaf
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  have hVU' : (⟨V, hV⟩ : X'.affineOpens).1 ≤ U := by simpa using hVU
  refine ⟨V, hVU', hxV, ?_⟩
  rw [map_mul, map_zero, idealSection_restrict, idealSection_restrict]
  exact affineKer_section_mul i hi ⟨V, hV⟩ _ _
    (idealSection_mem_ker i ⟨V, hV⟩ (idealRestrict i hVU' s))
    (idealSection_mem_ker i ⟨V, hV⟩ (idealRestrict i hVU' t))

/-- A section of the ideal sheaf of a first-order thickening squares to zero. -/
theorem idealSection_sq_zero (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    idealSection i U s * idealSection i U s = 0 :=
  idealSection_mul_zero i hi U s s

/-- A section `f` of the ideal sheaf of a first-order thickening gives the unit `1 + f` of the
structure sheaf of the ambient scheme. -/
def idealSectionOnePlusUnit (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) : Γ(X', U)ˣ where
  val := 1 + idealSection i U s
  inv := 1 - idealSection i U s
  val_inv := by linear_combination -idealSection_sq_zero i hi U s
  inv_val := by linear_combination -idealSection_sq_zero i hi U s

/-- A unit of the form `1 + f`, with `f` a section of the ideal sheaf, restricts to the
identity on the closed subscheme. -/
theorem idealSectionOnePlusUnit_map_eq_one (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    Units.map (i.app U).hom.toMonoidHom (idealSectionOnePlusUnit i hi U s) = 1 := by
  apply Units.ext
  change (i.app U).hom (1 + idealSection i U s) = 1
  rw [map_add, map_one, idealSection_map_zero, add_zero]

/-- Over an affine open, a unit restricting to the identity on the closed subscheme is `1 + f`
for a section `f` of the ideal sheaf. -/
theorem idealSectionOnePlus_affine_kernel (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.affineOpens) (u : Γ(X', U.1)ˣ)
    (hu : Units.map (CommRingCat.Hom.hom (i.app U)).toMonoidHom u = 1) :
    ∃ s : (idealModuleSheaf i).val.obj (op U.1), idealSectionOnePlusUnit i hi U.1 s = u := by
  obtain ⟨x, hx⟩ := (affineKer_units_exact i hi U u).mp hu
  obtain ⟨s, hs⟩ := idealSection_lift_affine i U x x.2
  refine ⟨s, ?_⟩
  apply Units.ext
  change (1 : Γ(X', U.1)) + idealSection i U.1 s = (u : Γ(X', U.1))
  rw [hs]
  exact congrArg Units.val hx

/-- On each open, `f ↦ 1 + f` is a homomorphism from the sections of the ideal sheaf to the
units of the structure sheaf of the ambient scheme, written additively. -/
def idealSectionOnePlusHom (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens) :
    (idealModuleSheaf i).val.obj (op U) →+ Additive (Γ(X', U)ˣ) where
  toFun s := Additive.ofMul (idealSectionOnePlusUnit i hi U s)
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    change (1 : Γ(X', U)) + idealSection i U 0 = 1
    rw [idealSection_zero, add_zero]
  map_add' s t := by
    apply Additive.toMul.injective
    apply Units.ext
    change 1 + idealSection i U (s + t) =
      (1 + idealSection i U s) * (1 + idealSection i U t)
    rw [idealSection_add]
    linear_combination -idealSection_mul_zero i hi U s t

/-- The map `f ↦ 1 + f` is injective on sections over every open. -/
theorem idealSectionOnePlusHom_injective (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens) :
    Function.Injective (idealSectionOnePlusHom i hi U) := by
  intro s t h
  have hu : idealSectionOnePlusUnit i hi U s = idealSectionOnePlusUnit i hi U t :=
    congrArg Additive.toMul h
  have hval := congrArg (fun z : Γ(X', U)ˣ => (z : Γ(X', U))) hu
  exact idealSection_injective i U (add_left_cancel hval)

/-- The map `f ↦ 1 + f` commutes with restriction. -/
theorem idealSectionOnePlusHom_natural (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) {U V : X'.Opens} (h : V ≤ U)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace).obj.map
        (homOfLE h).op (idealSectionOnePlusHom i hi U s) =
      idealSectionOnePlusHom i hi V (idealRestrict i h s) := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change ConcreteCategory.hom (X'.presheaf.map (homOfLE h).op)
      ((1 : Γ(X', U)) + idealSection i U s) =
    (1 : Γ(X', V)) + idealSection i V (idealRestrict i h s)
  rw [map_add, map_one, idealSection_restrict]

/-- The map of sheaves of abelian groups `f ↦ 1 + f` from the ideal sheaf of a first-order
thickening to the sheaf of units of the ambient scheme. -/
def idealToUnitsSheafHom (i : X ⟶ X') [QuasiCompact i] (hi : IsFirstOrderThickening i) :
    idealAddSheaf i ⟶
      Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace := by
  let α : (idealAddSheaf i).obj ⟶
      (Stacks.Cohomology.Generators.unitsSheaf
        X'.toLocallyRingedSpace.toRingedSpace).obj :=
    { app := fun U => AddCommGrpCat.ofHom (idealSectionOnePlusHom i hi U.unop)
      naturality := by
        intro U V f
        ext s
        exact (idealSectionOnePlusHom_natural i hi f.unop.le s).symm }
  exact ObjectProperty.homMk α

/-- On sections, the sheaf map of a first-order thickening really is `f ↦ 1 + f`. -/
theorem idealToUnitsSheafHom_app (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) (U : X'.Opens)
    (s : (idealModuleSheaf i).val.obj (op U)) :
    ((idealToUnitsSheafHom i hi).hom.app (op U) s).toMul.val = 1 + idealSection i U s :=
  rfl

/-- The composite of `f ↦ 1 + f` with restriction of units to the closed subscheme is zero. -/
theorem idealToUnitsSheafHom_comp (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) :
    idealToUnitsSheafHom i hi ≫ unitsRestrictionSheafHom i = 0 := by
  apply Sheaf.hom_ext
  ext U s
  exact congrArg Additive.ofMul (idealSectionOnePlusUnit_map_eq_one i hi U.unop s)

/-- A morphism of sheaves of abelian groups that is injective on sections over every open is a
monomorphism. -/
private theorem mono_of_injective_app {Y : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (f : F ⟶ G) (h : ∀ U : (Opens Y)ᵒᵖ, Function.Injective (f.hom.app U)) : Mono f := by
  have (U : (Opens Y)ᵒᵖ) : Mono (f.hom.app U) := (AddCommGrpCat.mono_iff_injective _).mpr (h U)
  have : Mono f.hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

/-- The map `f ↦ 1 + f` is a monomorphism of sheaves. -/
theorem idealToUnitsSheafHom_mono (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) : Mono (idealToUnitsSheafHom i hi) :=
  mono_of_injective_app _ fun U => idealSectionOnePlusHom_injective i hi U.unop

/-- Restriction of units along a first-order thickening is an epimorphism of sheaves. -/
theorem unitsRestrictionSheafHom_epi (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) : Epi (unitsRestrictionSheafHom i) := by
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp <|
    (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun U t x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  obtain ⟨s, hs⟩ := affineKer_units_surjective i hi ⟨V, hV⟩
    ((pushforwardUnitsSheaf i).obj.map (homOfLE hVU).op t).toMul
  exact ⟨V, hVU, ⟨Additive.ofMul s, congrArg Additive.ofMul hs⟩, hxV⟩

/-- A monomorphism of sheaves of abelian groups is injective on sections over every open. -/
theorem monoHomApp_injective {Y : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (f : F ⟶ G) (hf : Mono f) (V : Opens Y) :
    Function.Injective (((sheafSections (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj (op V)).map f) :=
  (AddCommGrpCat.mono_iff_injective _).mp
    (@Functor.map_mono _ _ _ _
      ((sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op V))
      (by infer_instance) _ _ f hf)

/-- Sections of the kernel of a map of sheaves of abelian groups inject into the sections of
the source sheaf. -/
theorem kernelHomApp_injective {Y : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (g : F ⟶ G) (V : Opens Y) : Function.Injective ((kernel.ι g).hom.app (op V)) :=
  monoHomApp_injective (kernel.ι g) (inferInstanceAs (Mono (equalizer.ι g 0))) V

/-- For a first-order thickening with ideal sheaf `ℐ`, the sequence of sheaves of abelian
groups `0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0`, whose first map is `f ↦ 1 + f`, is short exact. -/
theorem idealUnitsShortExact (i : X ⟶ X') [QuasiCompact i]
    (hi : IsFirstOrderThickening i) :
    (ShortComplex.mk (idealToUnitsSheafHom i hi) (unitsRestrictionSheafHom i)
      (idealToUnitsSheafHom_comp i hi)).ShortExact := by
  let f := idealToUnitsSheafHom i hi
  let g := unitsRestrictionSheafHom i
  let h := idealToUnitsSheafHom_comp i hi
  let S := ShortComplex.mk f g h
  have : Mono S.f := idealToUnitsSheafHom_mono i hi
  have : Epi S.g := unitsRestrictionSheafHom_epi i hi
  change S.ShortExact
  refine { exact := ?_ }
  apply S.exact_iff_epi_kernel_lift.mpr
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let v := (kernel.ι g).hom.app (op V) ((kernel g).obj.map (homOfLE hVU).op t)
  have hv : g.hom.app (op V) v = 0 :=
    congrArg (fun k => k.hom.app (op V) ((kernel g).obj.map (homOfLE hVU).op t))
      (kernel.condition g)
  obtain ⟨s, hs⟩ := idealSectionOnePlus_affine_kernel i hi ⟨V, hV⟩ v.toMul
    (congrArg Additive.toMul hv)
  exact ⟨V, hVU, ⟨s, kernelHomApp_injective g V <|
    (congrArg (fun k => k.hom.app (op V) s) (kernel.lift_ι g f h)).trans
      (congrArg Additive.ofMul hs)⟩, hxV⟩

end Sheaves

/-! ### The long exact cohomology sequence -/

section Cohomology

/-- The connecting map of the long exact cohomology sequence of a short exact sequence of
sheaves of abelian groups: composition with the extension class of the sequence. -/
def cohomologyBoundary {Y : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y)} (hS : S.ShortExact) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} S.X₃ n →+ CategoryTheory.Sheaf.H.{u} S.X₁ (n + 1) :=
  hS.extClass.postcomp
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) rfl

/-- Cohomology is exact at the middle sheaf of a short exact sequence. -/
theorem cohomology_exact_middle {Y : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (CategoryTheory.Sheaf.H.map.{u} S.f n) (CategoryTheory.Sheaf.H.map.{u} S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Abelian.Ext.covariant_sequence_exact₂' _ hS n)

/-- Cohomology is exact at the quotient sheaf of a short exact sequence, the next map being the
connecting map. -/
theorem cohomology_exact_quotient {Y : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (CategoryTheory.Sheaf.H.map.{u} S.g n) (cohomologyBoundary hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Abelian.Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl)

/-- Cohomology is exact at the subsheaf of a short exact sequence, the previous map being the
connecting map. -/
theorem cohomology_exact_sub {Y : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyBoundary hS n) (CategoryTheory.Sheaf.H.map.{u} S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Abelian.Ext.covariant_sequence_exact₁' _ hS n (n + 1) rfl)

/-- A monomorphism of sheaves of abelian groups is injective on global sections, hence on
degree-zero cohomology. -/
theorem cohomology_zero_injective {Y : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} Y} (f : F ⟶ G) (hf : Mono f) :
    Function.Injective (CategoryTheory.Sheaf.H.map.{u} f 0) := by
  have hT : IsTerminal (⊤ : Opens Y) := isTerminalTop
  intro x y h
  apply (CategoryTheory.Sheaf.H.equiv₀ F hT).injective
  apply monoHomApp_injective f hf (⊤ : Opens Y)
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality hT f x).trans
    ((congrArg (CategoryTheory.Sheaf.H.equiv₀ G hT) h).trans
      (CategoryTheory.Sheaf.H.equiv₀_naturality hT f y).symm)

/-- For a closed immersion of schemes, cohomology of a sheaf of abelian groups on the closed
subscheme agrees with cohomology of its pushforward. -/
def closedImmersionCohomologyEquiv {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsClosedImmersion i) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n ≃+
      CategoryTheory.Sheaf.H.{u}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F) n :=
  ((Stacks.ClosedImmersion.cohomologyPushforwardIso.{u, u, u} i.base
    hi.isClosedEmbedding n).app F).addCommGroupIsoToAddEquiv

/-- Global sections are corepresented by the constant sheaf of integers, with the normalization
given by evaluating a homomorphism at `1`. -/
def sectionsCoyonedaIso (Y : TopCat.{u}) :
    preadditiveCoyoneda.obj (op
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens Y)) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    (isTerminalTop : IsTerminal (⊤ : Opens Y))
  refine NatIso.ofComponents (fun F =>
    ((adj.homAddEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) ?_
  intro F G f
  ext s
  change ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) at s
  change f.hom.app (op (⊤ : Opens Y))
      ((adj.homEquiv _ F s) (ULift.up 1)) =
    (adj.homEquiv _ G (s ≫ f)) (ULift.up 1)
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- First cohomology computed as the first right-derived functor of global sections agrees with
first cohomology computed as `Ext` from the constant sheaf of integers. -/
def sheafCohomologyOneExtEquiv (Y : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} Y) :
    Stacks.Cohomology.SheafTorsor.sheafCohomologyOne Y F ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} F 1) :=
  (ModuleSheafCohomology.rightDerivedIso (sectionsCoyonedaIso Y).symm 1).app F ≪≫
    (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) 0).app F

/-- **Stacks Project, Tag 09NU.** The first cohomology of the sheaf of units of a scheme is
canonically isomorphic, as an abelian group, to its Picard group. -/
@[ega "IV 21.3.6" "special case"]
def unitsCohomologyPicardEquiv (X : Scheme.{u}) :
    CategoryTheory.Sheaf.H.{u}
        (Stacks.Cohomology.Generators.unitsSheaf X.toLocallyRingedSpace.toRingedSpace) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property :=
  (sheafCohomologyOneExtEquiv X.carrier
      (Stacks.Cohomology.Generators.unitsSheaf
        X.toLocallyRingedSpace.toRingedSpace)).symm.addCommGroupIsoToAddEquiv.trans
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup
      X.toLocallyRingedSpace.toRingedSpace)

/-- An isomorphism of sheaves of abelian groups induces an isomorphism on cohomology. -/
def cohomologyEquivOfIso {Y : TopCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (e : F ≅ G) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n ≃+ CategoryTheory.Sheaf.H.{u} G n where
  toFun := CategoryTheory.Sheaf.H.map.{u} e.hom n
  invFun := CategoryTheory.Sheaf.H.map.{u} e.inv n
  left_inv x := by
    rw [← CategoryTheory.Sheaf.H.map_comp_apply, e.hom_inv_id,
      CategoryTheory.Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← CategoryTheory.Sheaf.H.map_comp_apply, e.inv_hom_id,
      CategoryTheory.Sheaf.H.map_id_apply]
  map_add' := map_add (CategoryTheory.Sheaf.H.map.{u} e.hom n)

/-- Transport an exact pair of group homomorphisms along isomorphisms of the three groups. -/
theorem exact_addEquiv_transport {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A →+ B) (g : B →+ C) (h : Function.Exact f g)
    (a : A' ≃+ A) (b : B ≃+ B') (c : C ≃+ C') :
    Function.Exact (fun x => b (f (a x))) (fun y => c (g (b.symm y))) := by
  intro y
  dsimp only
  rw [map_eq_zero_iff c c.injective, h]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a.symm x, ?_⟩
    dsimp only
    rw [a.apply_symm_apply, hx, b.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨a x, ?_⟩
    rw [← hx, b.symm_apply_apply]

end Cohomology

/-! ### The sequence of a first-order thickening -/

section Sequence

variable {X X' : Scheme.{u}}

/-- Pushforward of sheaves of abelian groups along a homeomorphism is an equivalence. -/
theorem sheafPushforward_isEquivalence_of_isIso {Y Z : TopCat.{u}} (i : Y ⟶ Z) [IsIso i] :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).IsEquivalence := by
  let e := Opens.mapMapIso (asIso i)
  let J := Opens.grothendieckTopology Z
  let K := Opens.grothendieckTopology Y
  have : e.functor.IsContinuous J K :=
    inferInstanceAs ((Opens.map i).IsContinuous
      (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y))
  have : e.inverse.IsContinuous K J :=
    inferInstanceAs ((Opens.map (inv i)).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z))
  have := Functor.isContinuous_comp e.functor e.inverse J K J
  have := Functor.isContinuous_comp e.inverse e.functor K J K
  let F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} i
  let G := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inv i)
  let η : 𝟭 _ ≅ F ⋙ G :=
    (Functor.sheafPushforwardContinuousId' e.counitIso AddCommGrpCat.{u} K).symm
  let ε : G ⋙ F ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousId' e.unitIso.symm AddCommGrpCat.{u} J
  exact (CategoryTheory.Equivalence.mk F G η ε).isEquivalence_functor

/-- A thickening is a homeomorphism on underlying topological spaces. -/
theorem isIso_base_of_isFirstOrderThickening (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    IsIso i.base :=
  TopCat.isIso_of_bijective_of_isClosedMap i.base
    ⟨hi.1.isClosedEmbedding.injective, hi.isThickening.2⟩ hi.1.isClosedEmbedding.isClosedMap

/-- For a thickening the unit of the pullback-pushforward adjunction at the ideal sheaf is
invertible. -/
theorem idealAdjunctionUnit_isIso (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i.base).unit.app
      (idealAddSheaf i)) := by
  have := isIso_base_of_isFirstOrderThickening i hi
  have := sheafPushforward_isEquivalence_of_isIso i.base
  infer_instance

/-- The short exact sequence of sheaves of abelian groups attached to a first-order thickening:
`0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0`. -/
def thickeningShortComplex (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X') :=
  haveI : IsClosedImmersion i := hi.1
  ShortComplex.mk (idealToUnitsSheafHom i hi) (unitsRestrictionSheafHom i)
    (idealToUnitsSheafHom_comp i hi)

/-- The sequence of sheaves `0 ⟶ ℐ ⟶ 𝒪_{X'}^* ⟶ i_* 𝒪_X^* ⟶ 0` of a first-order thickening is
short exact. -/
@[stacks 0C6R "the short exact sequence of sheaves"]
theorem thickeningShortComplex_shortExact (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    (thickeningShortComplex i hi).ShortExact :=
  have : IsClosedImmersion i := hi.1
  idealUnitsShortExact i hi

/-- The map `H^n(X', ℐ) → H^n(X', 𝒪_{X'}^*)` induced by `f ↦ 1 + f`. -/
def idealToUnitsCohomology (i : X ⟶ X') (hi : IsFirstOrderThickening i) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) n →+
      CategoryTheory.Sheaf.H.{u}
        (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace) n :=
  haveI : IsClosedImmersion i := hi.1
  CategoryTheory.Sheaf.H.map.{u} (idealToUnitsSheafHom i hi) n

/-- The map `H^n(X', 𝒪_{X'}^*) → H^n(X', i_* 𝒪_X^*)` induced by restriction of units. -/
def unitsToSubCohomology (i : X ⟶ X') (n : ℕ) :
    CategoryTheory.Sheaf.H.{u}
        (Stacks.Cohomology.Generators.unitsSheaf
          X'.toLocallyRingedSpace.toRingedSpace) n →+
      CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) n :=
  CategoryTheory.Sheaf.H.map.{u} (unitsRestrictionSheafHom i) n

/-- The connecting map `H^n(X', i_* 𝒪_X^*) → H^{n+1}(X', ℐ)` of the long exact sequence. -/
def thickeningBoundary (i : X ⟶ X') (hi : IsFirstOrderThickening i) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) n →+
      CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) (n + 1) :=
  cohomologyBoundary (thickeningShortComplex_shortExact i hi) n

/-- For a thickening, the ideal sheaf on the ambient scheme is canonically the pushforward of
its restriction to the closed subscheme; the comparison is the unit of the
pullback-pushforward adjunction. -/
def idealAdjunctionUnitIso (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    idealAddSheaf i ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj (idealAddSheafOnSub i) :=
  haveI := idealAdjunctionUnit_isIso i hi
  asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i.base).unit.app
    (idealAddSheaf i))

/-- Cohomology of the ideal sheaf on the closed subscheme agrees with cohomology of the ideal
sheaf on the ambient scheme. -/
def idealCohomologyEquiv (i : X ⟶ X') (hi : IsFirstOrderThickening i) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) n ≃+
      CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) n :=
  (closedImmersionCohomologyEquiv i hi.1 (idealAddSheafOnSub i) n).trans
    (cohomologyEquivOfIso (idealAdjunctionUnitIso i hi) n).symm

/-- Cohomology of the sheaf of units on the closed subscheme agrees with cohomology of its
pushforward to the ambient scheme. -/
def unitsCohomologyEquiv (i : X ⟶ X') (hi : IsFirstOrderThickening i) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u}
        (Stacks.Cohomology.Generators.unitsSheaf
          X.toLocallyRingedSpace.toRingedSpace) n ≃+
      CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) n :=
  closedImmersionCohomologyEquiv i hi.1
    (Stacks.Cohomology.Generators.unitsSheaf X.toLocallyRingedSpace.toRingedSpace) n

/-- The map `H¹(X, ℐ) → Pic(X')` of the sequence: the degree-one map induced by `f ↦ 1 + f`,
read through the identification of the Picard group with the first cohomology of the sheaf of
units. -/
def picardOfIdeal (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 1 →+
      Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property :=
  (unitsCohomologyPicardEquiv X').toAddMonoidHom.comp
    ((idealToUnitsCohomology i hi 1).comp (idealCohomologyEquiv i hi 1).toAddMonoidHom)

/-- The restriction map `Pic(X') → Pic(X)` of the sequence: restriction of units in degree one,
read through the identifications of the Picard groups with first cohomology. -/
def picardRestriction (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property →+
      Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property :=
  (unitsCohomologyPicardEquiv X).toAddMonoidHom.comp
    (((unitsCohomologyEquiv i hi 1).symm.toAddMonoidHom).comp
      ((unitsToSubCohomology i 1).comp
        (unitsCohomologyPicardEquiv X').symm.toAddMonoidHom))

/-- The connecting map `Pic(X) → H²(X, ℐ)` of the sequence: the degree-one connecting map of
the long exact sequence, read through the identification of the Picard group with the first
cohomology of the sheaf of units. -/
def picardBoundary (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property →+
      CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 2 :=
  ((idealCohomologyEquiv i hi 2).symm.toAddMonoidHom).comp
    ((thickeningBoundary i hi 1).comp
      ((unitsCohomologyEquiv i hi 1).toAddMonoidHom.comp
        (unitsCohomologyPicardEquiv X).symm.toAddMonoidHom))

/-- The sequence starts with an injection: a global section of the ideal sheaf giving the unit
`1` is zero. -/
@[stacks 0C6R "injectivity at the global sections of the ideal"]
theorem injective_idealToUnitsCohomology_zero (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) :
    Function.Injective (idealToUnitsCohomology i hi 0) :=
  cohomology_zero_injective _ (thickeningShortComplex_shortExact i hi).mono_f

/-- Exactness at `H^n(X', 𝒪_{X'}^*)`. -/
@[stacks 0C6R "exactness at the cohomology of the units of the thickening"]
theorem exact_idealToUnitsCohomology (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (n : ℕ) :
    Function.Exact (idealToUnitsCohomology i hi n) (unitsToSubCohomology i n) :=
  cohomology_exact_middle (thickeningShortComplex_shortExact i hi) n

/-- Exactness at `H^n(X, 𝒪_X^*)`. -/
@[stacks 0C6R "exactness at the cohomology of the units of the closed subscheme"]
theorem exact_unitsToSubCohomology (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (n : ℕ) :
    Function.Exact (unitsToSubCohomology i n) (thickeningBoundary i hi n) :=
  cohomology_exact_quotient (thickeningShortComplex_shortExact i hi) n

/-- Exactness at `H^{n+1}(X, ℐ)`. -/
@[stacks 0C6R "exactness at the cohomology of the ideal"]
theorem exact_thickeningBoundary (i : X ⟶ X') (hi : IsFirstOrderThickening i) (n : ℕ) :
    Function.Exact (thickeningBoundary i hi n) (idealToUnitsCohomology i hi (n + 1)) :=
  cohomology_exact_sub (thickeningShortComplex_shortExact i hi) n

/-- Exactness at `Pic(X')`. -/
@[stacks 0C6R "exactness at the Picard group of the thickening"]
theorem exact_picardOfIdeal (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    Function.Exact (picardOfIdeal i hi) (picardRestriction i hi) :=
  exact_addEquiv_transport (idealToUnitsCohomology i hi 1) (unitsToSubCohomology i 1)
    (exact_idealToUnitsCohomology i hi 1) (idealCohomologyEquiv i hi 1)
    (unitsCohomologyPicardEquiv X')
    ((unitsCohomologyEquiv i hi 1).symm.trans (unitsCohomologyPicardEquiv X))

/-- Exactness at `Pic(X)`. -/
@[stacks 0C6R "exactness at the Picard group of the closed subscheme"]
theorem exact_picardRestriction (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    Function.Exact (picardRestriction i hi) (picardBoundary i hi) :=
  exact_addEquiv_transport (unitsToSubCohomology i 1) (thickeningBoundary i hi 1)
    (exact_unitsToSubCohomology i hi 1) (unitsCohomologyPicardEquiv X').symm
    ((unitsCohomologyEquiv i hi 1).symm.trans (unitsCohomologyPicardEquiv X))
    (idealCohomologyEquiv i hi 2).symm

end Sequence

/-! ### Torsion along a four-term exact sequence -/

section AbstractTorsion

variable {E A B C D : Type*} [AddCommGroup E] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D]

/-- Let `A → B → C → D` be exact at `B` and at `C`, let multiplication by `n` be surjective on
`A` and injective on `D`.  Then the middle map carries the `n`-torsion of `B` onto the
`n`-torsion of `C`. -/
theorem surjOn_zsmul_of_exact (f : A →+ B) (g : B →+ C) (h : C →+ D)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h) (n : ℤ)
    (hA : Function.Surjective fun a : A => n • a)
    (hD : Function.Injective fun d : D => n • d) :
    Set.SurjOn g {b : B | n • b = 0} {c : C | n • c = 0} := by
  intro c hc
  have hc0 : n • c = 0 := hc
  have hhc : h c = 0 := by
    apply hD
    change n • h c = n • (0 : D)
    rw [← map_zsmul, hc0, map_zero, smul_zero]
  obtain ⟨b, hb⟩ := (hgh c).mp hhc
  obtain ⟨a, ha⟩ := (hfg (n • b)).mp (by rw [map_zsmul, hb, hc0])
  obtain ⟨a', ha'⟩ := hA a
  have ha'' : n • a' = a := ha'
  refine ⟨b - f a', ?_, ?_⟩
  · change n • (b - f a') = 0
    rw [smul_sub, ← map_zsmul, ha'', ha, sub_self]
  · rw [map_sub, hb, (hfg (f a')).mpr ⟨a', rfl⟩, sub_zero]

/-- Let `E → A → B → C` be exact at `A` and at `B`, and let the image of `E` in `A` be saturated
for multiplication by `n`.  Then the last map is injective on the `n`-torsion of `B`. -/
theorem injOn_zsmul_of_exact (e : E →+ A) (f : A →+ B) (g : B →+ C)
    (hef : Function.Exact e f) (hfg : Function.Exact f g) (n : ℤ)
    (hsat : ∀ a : A, n • a ∈ Set.range e → a ∈ Set.range e) :
    Set.InjOn g {b : B | n • b = 0} := by
  intro b₁ h₁ b₂ h₂ hg
  have hb₁ : n • b₁ = 0 := h₁
  have hb₂ : n • b₂ = 0 := h₂
  have hb : n • (b₁ - b₂) = 0 := by rw [smul_sub, hb₁, hb₂, sub_zero]
  obtain ⟨a, ha⟩ := (hfg (b₁ - b₂)).mp (by rw [map_sub, hg, sub_self])
  have hfa : f (n • a) = 0 := by rw [map_zsmul, ha, hb]
  have hz : f a = 0 := (hef a).mpr (hsat a ((hef (n • a)).mp hfa))
  exact sub_eq_zero.mp (ha.symm.trans hz)

/-- The two halves together: along an exact `E → A → B → C → D` with multiplication by `n`
bijective on `A`, injective on `D`, and the image of `E` in `A` saturated for multiplication by
`n`, the middle map is a bijection from the `n`-torsion of `B` to the `n`-torsion of `C`. -/
theorem bijOn_zsmul_of_exact (e : E →+ A) (f : A →+ B) (g : B →+ C) (h : C →+ D)
    (hef : Function.Exact e f) (hfg : Function.Exact f g) (hgh : Function.Exact g h) (n : ℤ)
    (hA : Function.Surjective fun a : A => n • a)
    (hD : Function.Injective fun d : D => n • d)
    (hsat : ∀ a : A, n • a ∈ Set.range e → a ∈ Set.range e) :
    Set.BijOn g {b : B | n • b = 0} {c : C | n • c = 0} :=
  ⟨fun b hb => by
      change n • g b = 0
      rw [← map_zsmul, (hb : n • b = 0), map_zero],
    injOn_zsmul_of_exact e f g hef hfg n hsat,
    surjOn_zsmul_of_exact f g h hfg hgh n hA hD⟩

end AbstractTorsion

/-! ### An integer invertible on the closed subscheme -/

section InvertibleInteger

variable {X X' : Scheme.{u}}

/-- An integer invertible in `𝒪_X` is invertible in `𝒪_{X'}` over every open, for `X ⊂ X'` a
thickening. -/
theorem isUnit_intCast_of_isThickening (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) (U : X'.Opens) :
    IsUnit ((n : ℤ) : Γ(X', U)) := by
  apply RingedSpace.isUnit_of_isUnit_germ
  intro y hy
  obtain ⟨x, rfl⟩ := hi.2 y
  refine (isUnit_map_iff (i.stalkMap x).hom _).mp ?_
  have h2 : IsUnit ((n : ℤ) : X.presheaf.stalk x) := by
    simpa only [map_intCast] using hn.map (X.presheaf.germ ⊤ x trivial).hom
  rwa [show ((i.stalkMap x).hom) (X'.presheaf.germ U (i.base x) hy ((n : ℤ) : Γ(X', U))) =
      ((n : ℤ) : X.presheaf.stalk x) by rw [map_intCast, map_intCast]]

/-- Multiplication by an integer invertible in `𝒪_X` is bijective on the sections of the ideal
sheaf of a thickening over every open. -/
theorem bijective_zsmul_idealSections (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) (U : X'.Opens) :
    Function.Bijective fun s : (idealModuleSheaf i).val.obj (op U) => n • s := by
  have hR : IsUnit ((n : ℤ) : (structureSheafRing X'.toSheafedSpace).obj.obj (op U)) :=
    isUnit_intCast_of_isThickening i hi hn U
  obtain ⟨v, hv⟩ := hR
  have key : ∀ s : (idealModuleSheaf i).val.obj (op U),
      Units.val v⁻¹ • (n • s) = s := fun s => by
    rw [← Int.cast_smul_eq_zsmul ((structureSheafRing X'.toSheafedSpace).obj.obj (op U)) n s, ← hv,
      smul_smul, Units.inv_mul, one_smul]
  refine ⟨fun s t hst => ?_, fun t => ⟨Units.val v⁻¹ • t, ?_⟩⟩
  · rw [← key s, ← key t]
    exact congrArg (fun z => Units.val v⁻¹ • z) hst
  · change n • (Units.val v⁻¹ • t) = t
    rw [← Int.cast_smul_eq_zsmul ((structureSheafRing X'.toSheafedSpace).obj.obj (op U)) n
      (Units.val v⁻¹ • t), ← hv, smul_smul, Units.mul_inv, one_smul]

/-- Multiplication by an integer invertible in `𝒪_X` is an automorphism of the ideal sheaf of a
thickening, viewed as a sheaf of abelian groups. -/
theorem isIso_zsmul_id_idealAddSheaf (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) : IsIso (n • 𝟙 (idealAddSheaf i)) := by
  have hbij := bijective_zsmul_idealSections i hi hn
  have hmono : Mono (n • 𝟙 (idealAddSheaf i)) :=
    mono_of_injective_app _ fun U => (hbij U.unop).1
  have hepi : Epi (n • 𝟙 (idealAddSheaf i)) := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp <|
      (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun U t x hx => ?_
    obtain ⟨s, hs⟩ := (hbij U).2 ((idealAddSheaf i).obj.map (homOfLE (le_refl U)).op t)
    exact ⟨U, le_rfl, ⟨s, hs⟩, hx⟩
  exact isIso_of_mono_of_epi _

/-- Evaluation at a fixed cohomology class, as a homomorphism from the group of morphisms of
sheaves of abelian groups: `f ↦ H^k(f)(x)` is additive in `f`. -/
def cohomologyMapAddHom {Y : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} Y} (k : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} F k) :
    (F ⟶ G) →+ CategoryTheory.Sheaf.H.{u} G k :=
  AddMonoidHom.mk' (fun f => CategoryTheory.Sheaf.H.map.{u} f k x)
    (fun f g => CategoryTheory.Sheaf.H.map_add_apply f g x)

/-- Cohomology of multiplication by an integer on a sheaf of abelian groups is multiplication by
that integer on cohomology. -/
theorem cohomology_map_zsmul_id_apply {Y : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} Y)
    (k : ℕ) (n : ℤ) (x : CategoryTheory.Sheaf.H.{u} F k) :
    CategoryTheory.Sheaf.H.map.{u} (n • 𝟙 F) k x = n • x :=
  ((cohomologyMapAddHom k x).map_zsmul n (𝟙 F)).trans
    (congrArg (fun y => n • y) (CategoryTheory.Sheaf.H.map_id_apply x))

/-- Multiplication by an integer invertible in `𝒪_X` is bijective on the cohomology, in every
degree, of the ideal sheaf of a thickening carried on the ambient scheme. -/
theorem bijective_zsmul_cohomology_idealAddSheaf (i : X ⟶ X') (hi : IsThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) (k : ℕ) :
    Function.Bijective fun y : CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) k => n • y := by
  have hiso : IsIso (n • 𝟙 (idealAddSheaf i)) := isIso_zsmul_id_idealAddSheaf i hi hn
  have heq : (fun y : CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) k => n • y) =
      cohomologyEquivOfIso (@asIso _ _ _ _ (n • 𝟙 (idealAddSheaf i)) hiso) k := by
    funext y
    exact (cohomology_map_zsmul_id_apply _ k n y).symm
  rw [heq]
  exact (cohomologyEquivOfIso (@asIso _ _ _ _ (n • 𝟙 (idealAddSheaf i)) hiso) k).bijective

/-- Multiplication by an integer invertible in `𝒪_X` is bijective on `H^k(X, ℐ)`, the cohomology
of the ideal sheaf of a first-order thickening taken on the closed subscheme. -/
theorem bijective_zsmul_cohomology_idealAddSheafOnSub (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) (k : ℕ) :
    Function.Bijective
      fun y : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) k => n • y := by
  have h := bijective_zsmul_cohomology_idealAddSheaf i hi.isThickening hn k
  refine ⟨fun y₁ y₂ hy => (idealCohomologyEquiv i hi k).injective (h.1 ?_), fun y => ?_⟩
  · change n • (idealCohomologyEquiv i hi k) y₁ = n • (idealCohomologyEquiv i hi k) y₂
    rw [← map_zsmul, ← map_zsmul]
    exact congrArg (idealCohomologyEquiv i hi k) hy
  · obtain ⟨z, hz⟩ := h.2 (idealCohomologyEquiv i hi k y)
    have hz' : n • z = idealCohomologyEquiv i hi k y := hz
    refine ⟨(idealCohomologyEquiv i hi k).symm z, ?_⟩
    apply (idealCohomologyEquiv i hi k).injective
    change (idealCohomologyEquiv i hi k) (n • (idealCohomologyEquiv i hi k).symm z) = _
    rw [map_zsmul, AddEquiv.apply_symm_apply, hz']

end InvertibleInteger

/-! ### Torsion in the Picard groups of a thickening -/

section PicardTorsion

variable {X X' : Scheme.{u}}

/-- The map `H⁰(X, 𝒪_X^*) → H¹(X, ℐ)` of the sequence of Tag 0C6R, in the spelling whose next
map is `Stacks.Thickenings.picardOfIdeal`: the degree-zero connecting map, read through the
identification of the cohomology of the ideal on the closed subscheme with its cohomology on the
ambient scheme. -/
def unitsToIdealCohomology (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0 →+
      CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 1 :=
  ((idealCohomologyEquiv i hi 1).symm.toAddMonoidHom).comp (thickeningBoundary i hi 0)

/-- Exactness of the sequence of Tag 0C6R at `H¹(X, ℐ)`, in the spelling of the Picard-group
maps: the kernel of `H¹(X, ℐ) → Pic(X')` is the image of `H⁰(X, 𝒪_X^*)`. -/
theorem exact_unitsToIdealCohomology (i : X ⟶ X') (hi : IsFirstOrderThickening i) :
    Function.Exact (unitsToIdealCohomology i hi) (picardOfIdeal i hi) :=
  exact_addEquiv_transport (thickeningBoundary i hi 0) (idealToUnitsCohomology i hi 1)
    (exact_thickeningBoundary i hi 0)
    (AddEquiv.refl (CategoryTheory.Sheaf.H.{u} (pushforwardUnitsSheaf i) 0))
    (idealCohomologyEquiv i hi 1).symm (unitsCohomologyPicardEquiv X')

/-- If every invertible global function on `X` is the restriction of an invertible global
function on `X'`, then restriction of units is surjective on degree-zero cohomology. -/
theorem surjective_unitsToSubCohomology_zero (i : X ⟶ X')
    (hu : Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom)) :
    Function.Surjective (unitsToSubCohomology i 0) := by
  have hT : IsTerminal (⊤ : Opens X') := isTerminalTop
  intro y
  obtain ⟨v, hv⟩ := hu (CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT y).toMul
  refine ⟨(CategoryTheory.Sheaf.H.equiv₀
    (Stacks.Cohomology.Generators.unitsSheaf X'.toLocallyRingedSpace.toRingedSpace) hT).symm
      (Additive.ofMul v), ?_⟩
  have hnat := CategoryTheory.Sheaf.H.equiv₀_symm_naturality (hT := hT)
    (f := unitsRestrictionSheafHom i) (Additive.ofMul v)
  rw [unitsRestrictionSheafHom_app, hv] at hnat
  exact hnat.trans
    ((CategoryTheory.Sheaf.H.equiv₀ (pushforwardUnitsSheaf i) hT).symm_apply_apply y)

/-- If restriction of units is surjective on degree-zero cohomology, the map
`H¹(X, ℐ) → Pic(X')` of the sequence of Tag 0C6R is injective. -/
theorem injective_picardOfIdeal_of_surjective_unitsToSubCohomology (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (hu : Function.Surjective (unitsToSubCohomology i 0)) :
    Function.Injective (picardOfIdeal i hi) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨y, hy⟩ := (exact_unitsToIdealCohomology i hi a).mp ha
  obtain ⟨z, hz⟩ := hu y
  have hby : thickeningBoundary i hi 0 y = 0 :=
    (exact_unitsToSubCohomology i hi 0 y).mpr ⟨z, hz⟩
  rw [← hy]
  change (idealCohomologyEquiv i hi 1).symm (thickeningBoundary i hi 0 y) = 0
  rw [hby, map_zero]

/-- Surjectivity half of the statement of Tag 0C6S for a first-order thickening: for `n`
invertible in `𝒪_X`, every `n`-torsion class on `X` is the restriction of an `n`-torsion class on
`X'`. -/
theorem surjOn_picardRestriction_torsion (i : X ⟶ X') (hi : IsFirstOrderThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤))) :
    Set.SurjOn (picardRestriction i hi)
      {b : Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property | n • b = 0}
      {c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property | n • c = 0} :=
  surjOn_zsmul_of_exact (picardOfIdeal i hi) (picardRestriction i hi) (picardBoundary i hi)
    (exact_picardOfIdeal i hi) (exact_picardRestriction i hi) n
    (bijective_zsmul_cohomology_idealAddSheafOnSub i hi hn 1).2
    (bijective_zsmul_cohomology_idealAddSheafOnSub i hi hn 2).1

/-- Injectivity half of the statement of Tag 0C6S for a first-order thickening, under the
hypothesis that the image of `H⁰(X, 𝒪_X^*)` in `H¹(X, ℐ)` is saturated for multiplication by
`n`: restriction is injective on `Pic(X')[n]`. -/
theorem injOn_picardRestriction_torsion (i : X ⟶ X') (hi : IsFirstOrderThickening i) {n : ℤ}
    (hsat : ∀ a : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 1,
      n • a ∈ Set.range (unitsToIdealCohomology i hi) →
        a ∈ Set.range (unitsToIdealCohomology i hi)) :
    Set.InjOn (picardRestriction i hi)
      {b : Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property | n • b = 0} :=
  injOn_zsmul_of_exact (unitsToIdealCohomology i hi) (picardOfIdeal i hi)
    (picardRestriction i hi) (exact_unitsToIdealCohomology i hi) (exact_picardOfIdeal i hi)
    n hsat

/-- The statement of Tag 0C6S for a first-order thickening, under the saturation hypothesis of
`Stacks.Thickenings.injOn_picardRestriction_torsion`: for `n` invertible in `𝒪_X`, restriction
is a bijection `Pic(X')[n] → Pic(X)[n]`. -/
theorem bijOn_picardRestriction_torsion (i : X ⟶ X') (hi : IsFirstOrderThickening i) {n : ℤ}
    (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hsat : ∀ a : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 1,
      n • a ∈ Set.range (unitsToIdealCohomology i hi) →
        a ∈ Set.range (unitsToIdealCohomology i hi)) :
    Set.BijOn (picardRestriction i hi)
      {b : Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property | n • b = 0}
      {c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property | n • c = 0} :=
  bijOn_zsmul_of_exact (unitsToIdealCohomology i hi) (picardOfIdeal i hi)
    (picardRestriction i hi) (picardBoundary i hi) (exact_unitsToIdealCohomology i hi)
    (exact_picardOfIdeal i hi) (exact_picardRestriction i hi) n
    (bijective_zsmul_cohomology_idealAddSheafOnSub i hi hn 1).2
    (bijective_zsmul_cohomology_idealAddSheafOnSub i hi hn 2).1 hsat

/-- The statement of Tag 0C6S for a first-order thickening whose sequence of Tag 0C6R starts
with an injection `H¹(X, ℐ) → Pic(X')`: for `n` invertible in `𝒪_X`, restriction is a bijection
`Pic(X')[n] → Pic(X)[n]`. -/
theorem bijOn_picardRestriction_torsion_of_injective_picardOfIdeal (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hinj : Function.Injective (picardOfIdeal i hi)) :
    Set.BijOn (picardRestriction i hi)
      {b : Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property | n • b = 0}
      {c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property | n • c = 0} := by
  refine bijOn_picardRestriction_torsion i hi hn fun a ⟨y, hy⟩ => ?_
  have h0 : picardOfIdeal i hi (n • a) = 0 := by
    rw [← hy]
    exact (exact_unitsToIdealCohomology i hi _).mpr ⟨y, rfl⟩
  have h1 : n • a = 0 := hinj (by rw [h0, map_zero])
  have h2 : a = 0 :=
    (bijective_zsmul_cohomology_idealAddSheafOnSub i hi hn 1).1 (h1.trans (smul_zero n).symm)
  exact ⟨0, by rw [h2, map_zero]⟩

/-- The statement of Tag 0C6S for a first-order thickening on which every invertible global
function lifts: for `n` invertible in `𝒪_X`, restriction is a bijection
`Pic(X')[n] → Pic(X)[n]`. -/
theorem bijOn_picardRestriction_torsion_of_units_surjective (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) {n : ℤ} (hn : IsUnit ((n : ℤ) : Γ(X, ⊤)))
    (hu : Function.Surjective (Units.map (CommRingCat.Hom.hom (i.app ⊤)).toMonoidHom)) :
    Set.BijOn (picardRestriction i hi)
      {b : Stacks.SheafOfModules.Picard.PicardGroup X'.sheaf.obj
        (structureSheaf X'.sheaf).property | n • b = 0}
      {c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property | n • c = 0} :=
  bijOn_picardRestriction_torsion_of_injective_picardOfIdeal i hi hn
    (injective_picardOfIdeal_of_surjective_unitsToSubCohomology i hi
      (surjective_unitsToSubCohomology_zero i hu))

end PicardTorsion

end Stacks.Thickenings

end
