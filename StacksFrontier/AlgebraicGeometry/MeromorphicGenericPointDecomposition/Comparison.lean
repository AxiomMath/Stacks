module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Local

/-!
# The comparison map from meromorphic functions to the generic-point contributions

Let `X` be a scheme all of whose weakly associated points are generic points of irreducible
components. For a generic point `η` the local ring `𝒪_{X, η}` has dimension zero, so every
regular section becomes invertible after taking its germ at `η`. Therefore the objectwise
localization defining the presheaf of meromorphic functions maps to the pushforward
`j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` along the canonical morphism `j_η : Spec 𝒪_{X, η} ⟶ X`, and
hence so does the sheaf of meromorphic functions.

This file builds that map, both as a morphism of sheaves of rings and as a morphism of
`𝒪_X`-modules, and records the two descriptions of the sections of a product that the
comparison is tested against.

## Main definitions

* `AlgebraicGeometry.stalkSpecPushforward`: the sheaf `j_{x, *} 𝒪_{Spec 𝒪_{X, x}}` of rings
  on `X`.
* `AlgebraicGeometry.toStalkSpecPushforwardPresheaf`,
  `AlgebraicGeometry.toStalkSpecPushforwardSheaf`: the comparison maps out of the presheaf and
  out of the sheaf of meromorphic functions.
* `AlgebraicGeometry.algebraSheafAsModule`, `AlgebraicGeometry.algebraSheafAsModuleMap`: a
  sheaf of rings over `𝒪_X` as an `𝒪_X`-module, and the module map induced by a morphism of
  such.
* `AlgebraicGeometry.meromorphicFunctions`, `AlgebraicGeometry.genericPointStalkModule`: the
  two sides of the decomposition, as `𝒪_X`-modules.
* `AlgebraicGeometry.toGenericPointStalkModule`: the comparison map between them.
* `AlgebraicGeometry.modulesSectionsPiEquiv`, `AlgebraicGeometry.ringSheafSectionsPiEquiv`: the
  sections of a product of `𝒪_X`-modules, resp. of sheaves of rings, as families of sections.

## Main results

* `AlgebraicGeometry.toLocalizationPresheaf_app_comp_toStalkSpecPushforwardApp`: the comparison
  map restricts along the localization map to the map on sections induced by `j_η`.
* `AlgebraicGeometry.toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf`: the same statement
  for the sheaf-level comparison map.

## Implementation notes

The `𝒪_X`-module structure on a sheaf of rings `K` under `𝒪_X` is restriction of scalars of
the unit module along the given morphism; `algebraSheafAsModule` is exactly the shape in which
the sheaf of meromorphic functions is presented. That the pushforward of the unit module of
`Spec 𝒪_{X, η}` is of this shape is definitional, which is what makes
`algebraSheafAsModuleMap` usable for the comparison.

Sections of a product are computed through `CategoryTheory.Limits.Concrete.productEquiv` and
the preservation of products by evaluation on an open; the two preservation instances have to
be supplied by hand because the composite functor is not found by instance search.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace ConcreteCategory

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The comparison map at a generic point -/

/-- The submonoid presheaf of sections that are nonzerodivisors in every stalk. -/
abbrev regularSubmonoidPresheaf (X : Scheme.{u}) : X.presheaf.SubmonoidPresheaf :=
  X.presheaf.submonoidPresheafOfStalk fun y ↦ nonZeroDivisors (X.presheaf.stalk y)

/-- The localization of the structure presheaf at its regular sections is the presheaf of total
quotient rings. -/
lemma localizationPresheaf_regularSubmonoidPresheaf (X : Scheme.{u}) :
    (regularSubmonoidPresheaf X).localizationPresheaf = X.presheaf.totalQuotientPresheaf := rfl

/-- A section that is a nonzerodivisor in every stalk becomes invertible on the spectrum of the
local ring at a generic point. -/
lemma isUnit_fromSpecStalk_app (η : genericPoints X) (U : X.Opens)
    (s : Γ(X, U)) (hs : s ∈ (regularSubmonoidPresheaf X).obj (Opposite.op U)) :
    IsUnit (((X.fromSpecStalk η.1).app U).hom s) := by
  by_cases hmem : (η : X) ∈ U
  · have h1 : IsUnit ((X.presheaf.germ U η.1 hmem).hom s) :=
      isUnit_of_mem_nonZeroDivisors_stalk_of_mem_genericPoints η.2
        (Submonoid.mem_iInf.mp hs ⟨η.1, hmem⟩)
    rw [Scheme.fromSpecStalk_app hmem]
    simp only [CommRingCat.comp_apply]
    exact (h1.map (Scheme.ΓSpecIso (X.presheaf.stalk η.1)).inv.hom).map _
  · have hbot : X.fromSpecStalk η.1 ⁻¹ᵁ U = ⊥ := fromSpecStalk_preimage_eq_bot η.2 hmem
    have hsub : Subsingleton Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) := by
      rw [hbot]
      infer_instance
    rw [Subsingleton.elim (((X.fromSpecStalk η.1).app U).hom s)
      (1 : Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U))]
    exact isUnit_one

/-- The structure sheaf of the spectrum of the local ring at a point, pushed forward to `X`
along the canonical morphism. -/
def stalkSpecPushforward (X : Scheme.{u}) (x : X) : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat (X.fromSpecStalk x).base).obj
    (Spec (X.presheaf.stalk x)).sheaf

/-- The sections of `stalkSpecPushforward X x` over `U` are the sections of the structure sheaf
of `Spec 𝒪_{X, x}` over the preimage of `U`. -/
lemma stalkSpecPushforward_presheaf_obj (X : Scheme.{u}) (x : X) (U : (Opens X)ᵒᵖ) :
    (stalkSpecPushforward X x).presheaf.obj U =
      Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U.unop) := rfl

/-- The underlying ring hom of the comparison map on an open: the localization of the sections
over that open at its regular sections, mapped to the sections of the pushforward. -/
def toStalkSpecPushforwardAppHom (η : genericPoints X) (U : (Opens X)ᵒᵖ) :
    ((regularSubmonoidPresheaf X).localizationPresheaf.obj U : Type u) →+*
      Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U.unop) :=
  IsLocalization.lift (M := (regularSubmonoidPresheaf X).obj U)
    fun y ↦ isUnit_fromSpecStalk_app η U.unop y.1 y.2

/-- The comparison map on an open. -/
def toStalkSpecPushforwardApp (η : genericPoints X) (U : (Opens X)ᵒᵖ) :
    (regularSubmonoidPresheaf X).localizationPresheaf.obj U ⟶
      (stalkSpecPushforward X η.1).presheaf.obj U :=
  ConcreteCategory.ofHom (C := CommRingCat) (toStalkSpecPushforwardAppHom η U)

/-- The underlying ring hom of `toStalkSpecPushforwardApp η U` is
`toStalkSpecPushforwardAppHom η U`. -/
lemma toStalkSpecPushforwardApp_hom (η : genericPoints X) (U : (Opens X)ᵒᵖ) :
    (toStalkSpecPushforwardApp η U).hom = toStalkSpecPushforwardAppHom η U := rfl

/-- Composing the comparison map with the localization map gives the map on sections induced by
the canonical morphism from the spectrum of the local ring. -/
lemma toLocalizationPresheaf_app_comp_toStalkSpecPushforwardApp
    (η : genericPoints X) (U : (Opens X)ᵒᵖ) :
    (regularSubmonoidPresheaf X).toLocalizationPresheaf.app U ≫
        toStalkSpecPushforwardApp η U = (X.fromSpecStalk η.1).c.app U :=
  CommRingCat.hom_ext <| IsLocalization.lift_comp fun y ↦ isUnit_fromSpecStalk_app η U.unop y.1 y.2

/-- The comparison map from the presheaf of meromorphic functions to the pushforward of the
structure sheaf of the spectrum of the local ring at a generic point. -/
def toStalkSpecPushforwardPresheaf (η : genericPoints X) :
    (regularSubmonoidPresheaf X).localizationPresheaf ⟶
      (stalkSpecPushforward X η.1).presheaf where
  app U := toStalkSpecPushforwardApp η U
  naturality {U V} f := by
    have key : (regularSubmonoidPresheaf X).toLocalizationPresheaf.app U ≫
        ((regularSubmonoidPresheaf X).localizationPresheaf.map f ≫
          toStalkSpecPushforwardApp η V) =
        (regularSubmonoidPresheaf X).toLocalizationPresheaf.app U ≫
          (toStalkSpecPushforwardApp η U ≫ (stalkSpecPushforward X η.1).presheaf.map f) := by
      rw [← Category.assoc, ← Category.assoc,
        ← (regularSubmonoidPresheaf X).toLocalizationPresheaf.naturality f,
        Category.assoc, toLocalizationPresheaf_app_comp_toStalkSpecPushforwardApp,
        toLocalizationPresheaf_app_comp_toStalkSpecPushforwardApp]
      exact (X.fromSpecStalk η.1).c.naturality f
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext ((regularSubmonoidPresheaf X).obj U) ?_
    exact congrArg CommRingCat.Hom.hom key

/-- The canonical morphism of sheaves of rings from the structure sheaf to the pushforward of
the structure sheaf of the spectrum of the local ring at a point. -/
def toStalkSpecPushforwardStructure (X : Scheme.{u}) (x : X) :
    X.sheaf ⟶ stalkSpecPushforward X x :=
  ObjectProperty.homMk (X.fromSpecStalk x).c

/-- The comparison map from the sheaf of meromorphic functions to the pushforward of the
structure sheaf of the spectrum of the local ring at a generic point. -/
def toStalkSpecPushforwardSheaf (η : genericPoints X) :
    X.totalQuotientSheaf ⟶ stalkSpecPushforward X η.1 :=
  ObjectProperty.homMk (CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (toStalkSpecPushforwardPresheaf η) (stalkSpecPushforward X η.1).property)

/-- The underlying presheaf morphism of `toStalkSpecPushforwardSheaf η` is the lift of
`toStalkSpecPushforwardPresheaf η` along sheafification. -/
lemma toStalkSpecPushforwardSheaf_hom (η : genericPoints X) :
    (toStalkSpecPushforwardSheaf η).hom = CategoryTheory.sheafifyLift
      (Opens.grothendieckTopology X) (toStalkSpecPushforwardPresheaf η)
      (stalkSpecPushforward X η.1).property := rfl

/-- The sheafification unit composed with the sheaf-level comparison map is the presheaf-level
comparison map. -/
lemma toSheafify_comp_toStalkSpecPushforwardSheaf_hom (η : genericPoints X) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf ≫ (toStalkSpecPushforwardSheaf η).hom =
      toStalkSpecPushforwardPresheaf η :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

/-- The sheaf-level comparison map is a map of `𝒪_X`-algebras. -/
lemma toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf (η : genericPoints X) :
    X.toTotalQuotientSheaf ≫ toStalkSpecPushforwardSheaf η =
      toStalkSpecPushforwardStructure X η.1 := by
  apply CategoryTheory.Sheaf.hom_ext
  have e1 : X.toTotalQuotientSheaf.hom ≫ (toStalkSpecPushforwardSheaf η).hom =
      X.presheaf.toTotalQuotientPresheaf ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf ≫ (toStalkSpecPushforwardSheaf η).hom) := by
    rw [Scheme.toTotalQuotientSheaf_hom]
    exact Category.assoc _ _ _
  show X.toTotalQuotientSheaf.hom ≫ (toStalkSpecPushforwardSheaf η).hom =
    (X.fromSpecStalk η.1).c
  rw [e1, toSheafify_comp_toStalkSpecPushforwardSheaf_hom]
  exact NatTrans.ext <| funext <| toLocalizationPresheaf_app_comp_toStalkSpecPushforwardApp η

/-! ### Sheaves of rings over the structure sheaf as modules -/

/-- A sheaf of rings `K` with a morphism from the structure sheaf, viewed as an
`𝒪_X`-module. -/
abbrev algebraSheafAsModule {K : TopCat.Sheaf CommRingCat.{u} X} (α : X.sheaf ⟶ K) : X.Modules :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map α)).obj
    (SheafOfModules.unit
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj K))

/-- The component of `AlgebraicGeometry.algebraSheafAsModuleMap` on an open, as a linear map. -/
def algebraSheafAsModuleMapLinear {K L : TopCat.Sheaf CommRingCat.{u} X}
    (α : X.sheaf ⟶ K) (β : X.sheaf ⟶ L) (γ : K ⟶ L)
    (hcomp : ∀ (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U),
      (γ.hom.app U).hom ((α.hom.app U).hom r) = (β.hom.app U).hom r)
    (U : (Opens X)ᵒᵖ) :
    (algebraSheafAsModule α).val.obj U →ₗ[X.ringCatSheaf.obj.obj U]
      (algebraSheafAsModule β).val.obj U where
  toFun x := (γ.hom.app U).hom x
  map_add' a b := map_add _ a b
  map_smul' r x := by
    have hy : ∀ y : ↑(K.obj.obj U), (γ.hom.app U).hom ((α.hom.app U).hom r * y) =
        (β.hom.app U).hom r * (γ.hom.app U).hom y := by
      intro y
      rw [map_mul, hcomp U r]
    exact hy x

/-- A morphism of sheaves of rings under the structure sheaf induces a morphism of the
corresponding `𝒪_X`-modules. -/
def algebraSheafAsModuleMap {K L : TopCat.Sheaf CommRingCat.{u} X}
    (α : X.sheaf ⟶ K) (β : X.sheaf ⟶ L) (γ : K ⟶ L) (hγ : α ≫ γ = β) :
    algebraSheafAsModule α ⟶ algebraSheafAsModule β :=
  have hcomp : ∀ (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U),
      (γ.hom.app U).hom ((α.hom.app U).hom r) = (β.hom.app U).hom r := by
    intro U r
    rw [← hγ]
    rfl
  ⟨{ app := fun U ↦ ConcreteCategory.ofHom (algebraSheafAsModuleMapLinear α β γ hcomp U)
     naturality := fun {U V} f ↦ by
       ext x
       exact ConcreteCategory.congr_hom (γ.hom.naturality f) x }⟩

/-- On sections over an open, `algebraSheafAsModuleMap α β γ hγ` is the map of sections
induced by `γ`. -/
lemma algebraSheafAsModuleMap_app_apply {K L : TopCat.Sheaf CommRingCat.{u} X}
    (α : X.sheaf ⟶ K) (β : X.sheaf ⟶ L) (γ : K ⟶ L) (hγ : α ≫ γ = β)
    (U : (Opens X)ᵒᵖ) (x : (algebraSheafAsModule α).val.obj U) :
    ((algebraSheafAsModuleMap α β γ hγ).val.app U).hom x = (γ.hom.app U).hom x := rfl

/-! ### The two sides of the decomposition -/

/-- The sheaf of meromorphic functions, regarded as an `𝒪_X`-module through the canonical
map from the structure sheaf to the sheaf of total quotient rings. -/
abbrev meromorphicFunctions (X : Scheme.{u}) : X.Modules :=
  algebraSheafAsModule X.toTotalQuotientSheaf

/-- The structure sheaf of the spectrum of the stalk at a generic point, pushed forward
along the canonical morphism to `X` as an `𝒪_X`-module. -/
abbrev genericPointStalkModule (X : Scheme.{u}) (η : genericPoints X) : X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
    (SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf)

/-- The generic-point contribution at `η` is the `𝒪_X`-module associated with the canonical
morphism `toStalkSpecPushforwardStructure X η.1`. -/
lemma genericPointStalkModule_eq (X : Scheme.{u}) (η : genericPoints X) :
    genericPointStalkModule X η =
      algebraSheafAsModule (toStalkSpecPushforwardStructure X η.1) := rfl

/-- The comparison map from the `𝒪_X`-module of meromorphic functions to the generic-point
contribution at `η`. -/
def toGenericPointStalkModule (η : genericPoints X) :
    meromorphicFunctions X ⟶ genericPointStalkModule X η :=
  algebraSheafAsModuleMap X.toTotalQuotientSheaf (toStalkSpecPushforwardStructure X η.1)
    (toStalkSpecPushforwardSheaf η) (toTotalQuotientSheaf_comp_toStalkSpecPushforwardSheaf η)

/-- On sections over an open, `toGenericPointStalkModule η` is the map of sections induced by
`toStalkSpecPushforwardSheaf η`. -/
lemma toGenericPointStalkModule_app_apply (η : genericPoints X) (U : (Opens X)ᵒᵖ)
    (x : (meromorphicFunctions X).val.obj U) :
    ((toGenericPointStalkModule η).val.app U).hom x =
      ((toStalkSpecPushforwardSheaf η).hom.app U).hom x := rfl

/-! ### Sections of a product -/

/-- Evaluating an `𝒪_X`-module on an open set. -/
abbrev modulesSectionsFunctor (X : Scheme.{u}) (U : X.Opens) : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf X ⋙ (evaluation ((Opens X)ᵒᵖ) Ab.{u}).obj (Opposite.op U)

/-- Evaluating a sheaf of rings on an open set. -/
abbrev ringSheafSectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    TopCat.Sheaf CommRingCat.{u} X ⥤ CommRingCat.{u} :=
  TopCat.Sheaf.forget CommRingCat.{u} X ⋙
    (evaluation ((Opens X)ᵒᵖ) CommRingCat.{u}).obj (Opposite.op U)

/-- Sections of a product of `𝒪_X`-modules are the families of sections. -/
def modulesSectionsPiEquiv {ι : Type u} (M : ι → X.Modules) (U : X.Opens) :
    ToType ((modulesSectionsFunctor X U).obj (∏ᶜ M)) ≃
      ∀ i, ToType ((modulesSectionsFunctor X U).obj (M i)) := by
  have h1 : PreservesLimitsOfShape (Discrete ι) (Scheme.Modules.toPresheaf X) := inferInstance
  have h2 : PreservesLimitsOfShape (Discrete ι)
      ((evaluation ((Opens X)ᵒᵖ) Ab.{u}).obj (Opposite.op U)) := inferInstance
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (PreservesProduct.iso (modulesSectionsFunctor X U) M).hom)).trans
    (Limits.Concrete.productEquiv _)

/-- The `i`-th component of the family attached to a section of `∏ᶜ M` is its image under the
projection `Pi.π M i`. -/
lemma modulesSectionsPiEquiv_apply {ι : Type u} (M : ι → X.Modules) (U : X.Opens)
    (x : ToType ((modulesSectionsFunctor X U).obj (∏ᶜ M))) (i : ι) :
    modulesSectionsPiEquiv M U x i = (modulesSectionsFunctor X U).map (Pi.π M i) x := by
  have h1 : PreservesLimitsOfShape (Discrete ι) (Scheme.Modules.toPresheaf X) := inferInstance
  have h2 : PreservesLimitsOfShape (Discrete ι)
      ((evaluation ((Opens X)ᵒᵖ) Ab.{u}).obj (Opposite.op U)) := inferInstance
  show Limits.Concrete.productEquiv _
    ((PreservesProduct.iso (modulesSectionsFunctor X U) M).hom x) i = _
  rw [Limits.Concrete.productEquiv_apply_apply, ← ConcreteCategory.comp_apply,
    PreservesProduct.iso_hom, piComparison_comp_π]

/-- Sections of a product of sheaves of rings are the families of sections. -/
def ringSheafSectionsPiEquiv {ι : Type u} (L : ι → TopCat.Sheaf CommRingCat.{u} X) (U : X.Opens) :
    ToType ((ringSheafSectionsFunctor X U).obj (∏ᶜ L)) ≃
      ∀ i, ToType ((ringSheafSectionsFunctor X U).obj (L i)) := by
  have h1 : PreservesLimitsOfShape (Discrete ι)
      (TopCat.Sheaf.forget CommRingCat.{u} X) := inferInstance
  have h2 : PreservesLimitsOfShape (Discrete ι)
      ((evaluation ((Opens X)ᵒᵖ) CommRingCat.{u}).obj (Opposite.op U)) := inferInstance
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (PreservesProduct.iso (ringSheafSectionsFunctor X U) L).hom)).trans
    (Limits.Concrete.productEquiv _)

/-- The `i`-th component of the family attached to a section of `∏ᶜ L` is its image under the
projection `Pi.π L i`. -/
lemma ringSheafSectionsPiEquiv_apply {ι : Type u} (L : ι → TopCat.Sheaf CommRingCat.{u} X)
    (U : X.Opens) (x : ToType ((ringSheafSectionsFunctor X U).obj (∏ᶜ L))) (i : ι) :
    ringSheafSectionsPiEquiv L U x i = (ringSheafSectionsFunctor X U).map (Pi.π L i) x := by
  have h1 : PreservesLimitsOfShape (Discrete ι)
      (TopCat.Sheaf.forget CommRingCat.{u} X) := inferInstance
  have h2 : PreservesLimitsOfShape (Discrete ι)
      ((evaluation ((Opens X)ᵒᵖ) CommRingCat.{u}).obj (Opposite.op U)) := inferInstance
  show Limits.Concrete.productEquiv _
    ((PreservesProduct.iso (ringSheafSectionsFunctor X U) L).hom x) i = _
  rw [Limits.Concrete.productEquiv_apply_apply, ← ConcreteCategory.comp_apply,
    PreservesProduct.iso_hom, piComparison_comp_π]

end AlgebraicGeometry
