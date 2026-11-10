module

public import Mathlib.Algebra.Group.Pi.Units
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.PiStalkSheaf
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.SheafifyBasis
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.AffineGeneral
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.Sections

/-!
# Comparing the total quotient presheaf with the generic-point product

The canonical map from the sheaf of regular functions to the generic-point product inverts every
section whose germs are everywhere nonzerodivisors, because at a generic point a nonzerodivisor of
the local ring is a unit. It therefore extends to the presheaf of total quotient rings, and on an
affine open the extension is an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointProduct.stalkToSections`: the canonical map from the local
  ring at a generic point to the sections of its local scheme over an open set.
* `Stacks.AlgebraicGeometry.GenericPointProduct.totalQuotientToPiStalk`: the comparison morphism
  out of the presheaf of total quotient rings.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.GenericPointProduct

open Stacks.AlgebraicGeometry.GenericPointGluing Stacks.AlgebraicGeometry.GenericPointSheaf

variable (X : Scheme.{u})

/-- The canonical map from the local ring at a generic point `η` to the sections, over an open set
`U`, of the local scheme at `η`. Together with the germ map at `η` it factors the pullback of
sections along `Spec 𝒪_{X, η} ⟶ X`. -/
noncomputable def stalkToSections (η : genericPoints X) (U : X.Opens) :
    X.presheaf.stalk η.1 ⟶ (stalkPresheaf X η).obj (op U) :=
  (Scheme.ΓSpecIso (X.presheaf.stalk η.1)).inv ≫
    (Spec (X.presheaf.stalk η.1)).presheaf.map
      (homOfLE (le_top : (X.fromSpecStalk η.1) ⁻¹ᵁ U ≤ ⊤)).op

/-- The pullback of sections along `Spec 𝒪_{X, η} ⟶ X` is the germ map at `η` followed by
`Stacks.AlgebraicGeometry.GenericPointProduct.stalkToSections`. -/
theorem fromSpecStalk_c_app_eq (η : genericPoints X) {U : X.Opens} (hη : (η : X) ∈ U) :
    (X.fromSpecStalk η.1).c.app (op U) =
      X.presheaf.germ U η.1 hη ≫ stalkToSections X η U :=
  Scheme.fromSpecStalk_app hη

/-- Over an open set containing the generic point `η`, the canonical map from the local ring at
`η` to the sections of its local scheme is an isomorphism: the preimage of the open set is the
whole of `Spec 𝒪_{X, η}`. -/
theorem isIso_stalkToSections (η : genericPoints X) {U : X.Opens} (hη : (η : X) ∈ U) :
    IsIso (stalkToSections X η U) := by
  have h : (X.fromSpecStalk η.1) ⁻¹ᵁ U = ⊤ := fromSpecStalk_preimage_eq_top η.2 hη
  have he : (homOfLE (le_top : (X.fromSpecStalk η.1) ⁻¹ᵁ U ≤ ⊤)) = eqToHom h :=
    Subsingleton.elim _ _
  rw [stalkToSections, he]
  have : IsIso ((eqToHom h : (X.fromSpecStalk η.1) ⁻¹ᵁ U ⟶ ⊤)).op := inferInstance
  infer_instance

/-- The generic-point product has no sections over an open set missing the generic point. -/
theorem subsingleton_stalkPresheaf_obj {η : genericPoints X} {U : X.Opens} (hη : (η : X) ∉ U) :
    Subsingleton ((stalkPresheaf X η).obj (op U)) := by
  have h : (X.fromSpecStalk η.1) ⁻¹ᵁ U = ⊥ := fromSpecStalk_preimage_eq_bot η.2 hη
  change Subsingleton
    ((Spec (X.presheaf.stalk η.1)).presheaf.obj (op ((X.fromSpecStalk η.1) ⁻¹ᵁ U)))
  rw [h]
  infer_instance

/-- The denominator submonoid of the presheaf of total quotient rings: the sections whose germ at
every point of the open set is a nonzerodivisor. -/
noncomputable abbrev nzdSubmonoidPresheaf : X.presheaf.SubmonoidPresheaf :=
  X.presheaf.submonoidPresheafOfStalk fun x ↦ (X.presheaf.stalk x)⁰

/-- A section whose germs are everywhere nonzerodivisors becomes a unit in the generic-point
product. At a generic point inside the open set this is because a nonzerodivisor of the local ring
there is a unit; at a generic point outside it, the factor is the zero ring. -/
theorem isUnit_toPiStalkPresheaf_app (U : (Opens X)ᵒᵖ) (y : (nzdSubmonoidPresheaf X).obj U) :
    IsUnit ((toPiStalkPresheaf X).app U y.1) := by
  rw [Pi.isUnit_iff]
  intro η
  by_cases hη : (η : X) ∈ U.unop
  · have hy : X.presheaf.germ U.unop η.1 hη y.1 ∈ (X.presheaf.stalk η.1)⁰ := by
      have h2 := y.2
      simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
        Submonoid.mem_comap] at h2
      exact h2 ⟨η.1, hη⟩
    have : (toPiStalkPresheaf X).app U y.1 η =
        stalkToSections X η U.unop (X.presheaf.germ U.unop η.1 hη y.1) :=
      ConcreteCategory.congr_hom (fromSpecStalk_c_app_eq X η hη) y.1
    rw [this]
    exact (isUnit_of_mem_nonZeroDivisors_stalk η.2 hy).map (stalkToSections X η U.unop).hom
  · have := subsingleton_stalkPresheaf_obj X (η := η) (U := U.unop) hη
    exact isUnit_of_subsingleton _

/-- The sections of the presheaf of total quotient rings over an open set, as an algebra over the
regular functions there. This is the standard localization algebra structure, transported across
the definitional unfolding of the total quotient presheaf, which typeclass search does not see. -/
@[instance_reducible]
noncomputable def algebraTotalQuotientObj (U : (Opens X)ᵒᵖ) :
    Algebra (X.presheaf.obj U) (X.presheaf.totalQuotientPresheaf.obj U) :=
  inferInstanceAs (Algebra _ ((nzdSubmonoidPresheaf X).localizationPresheaf.obj U))

/-- The sections of the presheaf of total quotient rings over an open set are the localization of
the regular functions there at the sections with everywhere-nonzerodivisor germs. -/
theorem isLocalizationTotalQuotientObj (U : (Opens X)ᵒᵖ) :
    letI := algebraTotalQuotientObj X U
    IsLocalization ((nzdSubmonoidPresheaf X).obj U)
      (X.presheaf.totalQuotientPresheaf.obj U) :=
  inferInstanceAs (IsLocalization _ ((nzdSubmonoidPresheaf X).localizationPresheaf.obj U))

/-- Two morphisms out of the sections of the presheaf of total quotient rings which agree on the
image of the regular functions are equal, that presheaf being an objectwise localization. -/
theorem hom_ext_totalQuotient {U : (Opens X)ᵒᵖ} {A : CommRingCat.{u}}
    {j k : X.presheaf.totalQuotientPresheaf.obj U ⟶ A}
    (h : ∀ r : X.presheaf.obj U, j (X.presheaf.toTotalQuotientPresheaf.app U r) =
      k (X.presheaf.toTotalQuotientPresheaf.app U r)) : j = k := by
  let := algebraTotalQuotientObj X U
  have := isLocalizationTotalQuotientObj X U
  exact CommRingCat.hom_ext
    (IsLocalization.ringHom_ext ((nzdSubmonoidPresheaf X).obj U) (RingHom.ext h))

/-- The component at an open set of the comparison morphism to the generic-point product: the
extension of the family of pullbacks of sections along the objectwise localization. -/
noncomputable def totalQuotientToPiStalkApp (U : (Opens X)ᵒᵖ) :
    X.presheaf.totalQuotientPresheaf.obj U ⟶ (piStalkPresheaf X).obj U :=
  CommRingCat.ofHom (IsLocalization.lift (M := (nzdSubmonoidPresheaf X).obj U)
    (S := (nzdSubmonoidPresheaf X).localizationPresheaf.obj U)
    (g := ((toPiStalkPresheaf X).app U).hom) (isUnit_toPiStalkPresheaf_app X U))

/-- On the image of a regular function, the component of the comparison morphism is the family of
its pullbacks to the generic points. -/
@[simp]
theorem totalQuotientToPiStalkApp_apply_app (U : (Opens X)ᵒᵖ) (r : X.presheaf.obj U) :
    totalQuotientToPiStalkApp X U (X.presheaf.toTotalQuotientPresheaf.app U r) =
      (toPiStalkPresheaf X).app U r :=
  IsLocalization.lift_eq (S := (nzdSubmonoidPresheaf X).localizationPresheaf.obj U)
    (isUnit_toPiStalkPresheaf_app X U) r

/-- The localization map to the presheaf of total quotient rings commutes with restriction. -/
theorem toTotalQuotientPresheaf_map {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (r : X.presheaf.obj U) :
    X.presheaf.totalQuotientPresheaf.map i (X.presheaf.toTotalQuotientPresheaf.app U r) =
      X.presheaf.toTotalQuotientPresheaf.app V (X.presheaf.map i r) :=
  (ConcreteCategory.congr_hom (X.presheaf.toTotalQuotientPresheaf.naturality i) r).symm

/-- The canonical map to the generic-point product commutes with restriction. -/
theorem toPiStalkPresheaf_map {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (r : X.presheaf.obj U) :
    (piStalkPresheaf X).map i ((toPiStalkPresheaf X).app U r) =
      (toPiStalkPresheaf X).app V (X.presheaf.map i r) :=
  (ConcreteCategory.congr_hom ((toPiStalkPresheaf X).naturality i) r).symm

/-- The comparison morphism from the presheaf of total quotient rings to the generic-point
product: on the image of the regular functions it is the family of pullbacks, and this determines
it because the total quotient presheaf is an objectwise localization. -/
noncomputable def totalQuotientToPiStalk :
    X.presheaf.totalQuotientPresheaf ⟶ piStalkPresheaf X where
  app := totalQuotientToPiStalkApp X
  naturality {U V} i := by
    refine hom_ext_totalQuotient X fun r ↦ ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, toTotalQuotientPresheaf_map,
      totalQuotientToPiStalkApp_apply_app, totalQuotientToPiStalkApp_apply_app,
      toPiStalkPresheaf_map]

/-- The component of `totalQuotientToPiStalk` at an open set is `totalQuotientToPiStalkApp`. -/
@[simp]
theorem totalQuotientToPiStalk_app (U : (Opens X)ᵒᵖ) :
    (totalQuotientToPiStalk X).app U = totalQuotientToPiStalkApp X U := rfl

/-- Over an open set containing the generic point `η`, the canonical map from the local ring at
`η` to the sections of its local scheme, as an isomorphism. -/
noncomputable def stalkSectionsIso (η : genericPoints X) {U : X.Opens} (hη : (η : X) ∈ U) :
    X.presheaf.stalk η.1 ≅ (stalkPresheaf X η).obj (op U) :=
  letI := isIso_stalkToSections X η hη
  asIso (stalkToSections X η U)

/-- The forward map of `stalkSectionsIso` is `stalkToSections`. -/
theorem stalkSectionsIso_hom (η : genericPoints X) {U : X.Opens} (hη : (η : X) ∈ U) :
    (stalkSectionsIso X η hη).hom = stalkToSections X η U := rfl

/-- The restriction of the generic-point product to the generic points lying in a given open set,
where the remaining factors have no sections. -/
noncomputable def piStalkRestrict (U : X.Opens) :
    (piStalkPresheaf X).obj (op U) ⟶
      CommRingCat.of (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
  CommRingCat.ofHom (RingHom.pi fun η ↦
    ((stalkSectionsIso X η.1 η.2).inv).hom.comp (Pi.evalRingHom _ η.1))

/-- The component of `piStalkRestrict` at a generic point `η` in the open set is the inverse of
`stalkSectionsIso` applied to the factor at `η`. -/
theorem piStalkRestrict_apply (U : X.Opens) (s : (piStalkPresheaf X).obj (op U))
    (η : {η : genericPoints X // η.1 ∈ U}) :
    piStalkRestrict X U s η = (stalkSectionsIso X η.1 η.2).inv (s η.1) := rfl

/-- Restricting the generic-point product to the generic points inside an open set loses nothing:
the factors at the generic points outside it have no sections. -/
theorem bijective_piStalkRestrict (U : X.Opens) :
    Function.Bijective (piStalkRestrict X U) := by
  classical
  refine ⟨fun s t hst ↦ funext fun η ↦ ?_, fun v ↦
    ⟨fun η ↦ if h : (η : X) ∈ U then (stalkSectionsIso X η h).hom (v ⟨η, h⟩) else 0,
      funext fun η ↦ ?_⟩⟩
  · by_cases hη : (η : X) ∈ U
    · have h := congrFun hst ⟨η, hη⟩
      rw [piStalkRestrict_apply, piStalkRestrict_apply] at h
      have := congrArg (stalkSectionsIso X η hη).hom h
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
    · have := subsingleton_stalkPresheaf_obj X (η := η) (U := U) hη
      exact Subsingleton.elim _ _
  · rw [piStalkRestrict_apply, dite_eq_left η.2]
    exact Iso.hom_inv_id_apply _ _

variable {X}

/-- On an affine open, the comparison morphism from the presheaf of total quotient rings to the
generic-point product is an isomorphism: after restricting to the generic points inside that open
it is the affine decomposition of the meromorphic functions into the local rings there, and that
restriction loses nothing. -/
theorem isIso_totalQuotientToPiStalkApp
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    {U : X.Opens} (hU : IsAffineOpen U)
    (hfin : (irreducibleComponents (U : Set X)).Finite) :
    IsIso (totalQuotientToPiStalkApp X (op U)) := by
  let : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom.toAlgebra
  let : ∀ η : {η : genericPoints X // η.1 ∈ U}, Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  have key : totalQuotientToPiStalkApp X (op U) ≫ piStalkRestrict X U =
      CommRingCat.ofHom
        (totalQuotientObjAlgEquivPiStalk hass hU hfin).toRingEquiv.toRingHom := by
    refine hom_ext_totalQuotient X fun r ↦ ?_
    rw [ConcreteCategory.comp_apply, totalQuotientToPiStalkApp_apply_app]
    funext η
    rw [piStalkRestrict_apply, toPiStalkPresheaf_app_apply,
      ConcreteCategory.congr_hom (fromSpecStalk_c_app_eq X η.1 η.2) r,
      ConcreteCategory.comp_apply, ← stalkSectionsIso_hom X η.1 η.2, Iso.hom_inv_id_apply]
    exact (totalQuotientObjAlgEquivPiStalk_apply_algebraMap hass hU hfin r η).symm
  have hc : ∀ t, piStalkRestrict X U (totalQuotientToPiStalkApp X (op U) t) =
      totalQuotientObjAlgEquivPiStalk hass hU hfin t :=
    fun t ↦ ConcreteCategory.congr_hom key t
  rw [ConcreteCategory.isIso_iff_bijective]
  have he := (totalQuotientObjAlgEquivPiStalk hass hU hfin).bijective
  refine ⟨fun a b hab ↦ he.1 ?_, fun w ↦ ?_⟩
  · rw [← hc a, ← hc b, hab]
  · obtain ⟨x, hx⟩ := he.2 (piStalkRestrict X U w)
    exact ⟨x, (bijective_piStalkRestrict X U).1 (by rw [hc x, hx])⟩

/-- The affine opens of a scheme form a basis, indexed by the type of affine opens. -/
theorem isBasis_range_affineOpens (X : Scheme.{u}) :
    Opens.IsBasis (Set.range (Subtype.val : X.affineOpens → X.Opens)) := by
  rw [Subtype.range_coe]
  exact X.isBasis_affineOpens

/-- The sheaf of total quotient rings is the generic-point product: the comparison morphism,
extended to the sheafification, is an isomorphism at every open set. This is the content of the
decomposition, before it is transported into the category of modules. -/
theorem isIso_sheafifyLift_totalQuotientToPiStalk_app
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents (U : Set X)).Finite)
    (U : X.Opens) :
    IsIso ((sheafifyLift (Opens.grothendieckTopology X) (totalQuotientToPiStalk X)
      (piStalkSheaf X).property).app (op U)) :=
  isIso_sheafifyLift_app_of_isIso_basis (G := piStalkSheaf X) (isBasis_range_affineOpens X)
    (totalQuotientToPiStalk X)
    (fun V ↦ isIso_totalQuotientToPiStalkApp hass V.2 (hfin V.1 V.2.isCompact)) U

end Stacks.AlgebraicGeometry.GenericPointProduct
