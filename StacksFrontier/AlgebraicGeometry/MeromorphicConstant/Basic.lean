module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Comparison
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Meromorphic functions on an integral scheme

On an integral scheme `X` with generic point `η` the sheaf of meromorphic functions — the
sheafification of the presheaf localizing the regular functions at the sections with
everywhere-nonzerodivisor germs — is the constant sheaf with value the function field
`𝒪_{X, η}`.

## Main definitions

* `Stacks.AlgebraicGeometry.MeromorphicConstant.toSkyscraper`: the comparison from the presheaf
  of total quotient rings to the skyscraper sheaf at the generic point with value the function
  field, given by the germ at the generic point.
* `Stacks.AlgebraicGeometry.MeromorphicConstant.constantToSkyscraper`: the same comparison out
  of the constant presheaf.
* `Stacks.AlgebraicGeometry.MeromorphicConstant.sheafIso`: the resulting isomorphism from the
  sheaf of total quotient rings to the constant sheaf.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicConstant.totalQuotientSheafIsoConstant`: the sheaf of
  total quotient rings of an integral scheme is isomorphic to the constant sheaf with value the
  function field, by an isomorphism carrying the image of a regular function to the constant
  section given by its germ at the generic point.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicConstant

variable (X : Scheme.{u}) [IsIntegral X]

/-- Membership of the generic point in an open set is decidable, classically. -/
noncomputable local instance decidableGenericPointMem (U : Opens X) :
    Decidable (genericPoint X ∈ U) := Classical.dec _

/-- The generic point of an integral scheme is one of its generic points. -/
theorem genericPoint_mem_genericPoints : genericPoint X ∈ genericPoints X := by
  rw [genericPoints_eq_singleton]
  rfl

/-- The germ at the generic point of a section over `U` whose germs at all points of `U` are
nonzerodivisors is a unit. -/
theorem isUnit_germ_genericPoint {U : X.Opens} (hU : genericPoint X ∈ U)
    (y : (GenericPointProduct.nzdSubmonoidPresheaf X).obj (op U)) :
    IsUnit (X.presheaf.germ U (genericPoint X) hU y.1) :=
  GenericPointSheaf.isUnit_of_mem_nonZeroDivisors_stalk (genericPoint_mem_genericPoints X)
    (Submonoid.mem_iInf.mp y.2 ⟨genericPoint X, hU⟩)

/-- Over an open set containing the generic point, the ring map from the total quotient ring to
the function field extending the germ at the generic point. -/
noncomputable def toFunctionFieldApp {U : X.Opens} (hU : genericPoint X ∈ U) :
    X.presheaf.totalQuotientPresheaf.obj (op U) ⟶ X.functionField :=
  CommRingCat.ofHom (IsLocalization.lift
    (M := (GenericPointProduct.nzdSubmonoidPresheaf X).obj (op U))
    (S := (GenericPointProduct.nzdSubmonoidPresheaf X).localizationPresheaf.obj (op U))
    (g := (X.presheaf.germ U (genericPoint X) hU).hom) (isUnit_germ_genericPoint X hU))

/-- `toFunctionFieldApp` sends the class of a regular function to its germ at the generic
point. -/
@[simp]
theorem toFunctionFieldApp_apply {U : X.Opens} (hU : genericPoint X ∈ U) (r : Γ(X, U)) :
    toFunctionFieldApp X hU (X.presheaf.toTotalQuotientPresheaf.app (op U) r) =
      X.presheaf.germ U (genericPoint X) hU r :=
  IsLocalization.lift_eq
    (S := (GenericPointProduct.nzdSubmonoidPresheaf X).localizationPresheaf.obj (op U))
    (isUnit_germ_genericPoint X hU) r

/-- The germ-at-the-generic-point extension commutes with restriction. -/
theorem toFunctionFieldApp_restrict {U V : X.Opens} (i : V ⟶ U) (hV : genericPoint X ∈ V) :
    X.presheaf.totalQuotientPresheaf.map i.op ≫ toFunctionFieldApp X hV =
      toFunctionFieldApp X (i.le hV) := by
  refine GenericPointProduct.hom_ext_totalQuotient X fun r ↦ ?_
  rw [ConcreteCategory.comp_apply, GenericPointProduct.toTotalQuotientPresheaf_map,
    toFunctionFieldApp_apply, toFunctionFieldApp_apply]
  exact X.presheaf.germ_res_apply i _ _ r

/-- The germ maps to the function field form a cocone on the diagram computing the stalk of the
total quotient presheaf at the generic point. -/
noncomputable def functionFieldCocone :
    Cocone ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf.totalQuotientPresheaf) :=
  Cocone.mk X.functionField
    { app := fun V ↦ toFunctionFieldApp X V.unop.2
      naturality := fun V W i ↦ by
        simpa using toFunctionFieldApp_restrict X ((OpenNhds.inclusion _).map i.unop) W.unop.2 }

/-- The canonical map from the stalk of the total quotient presheaf at the generic point to the
function field. -/
noncomputable def stalkToFunctionField :
    X.presheaf.totalQuotientPresheaf.stalk (genericPoint X) ⟶ X.functionField :=
  colimit.desc _ (functionFieldCocone X)

/-- The germ map of the total quotient presheaf at the generic point followed by
`stalkToFunctionField` is `toFunctionFieldApp`. -/
@[simp]
theorem germ_stalkToFunctionField {U : X.Opens} (hU : genericPoint X ∈ U) :
    X.presheaf.totalQuotientPresheaf.germ U (genericPoint X) hU ≫ stalkToFunctionField X =
      toFunctionFieldApp X hU :=
  colimit.ι_desc (functionFieldCocone X) (op ⟨U, hU⟩)

/-- A nonempty open subset of an irreducible space contains the generic point. -/
theorem genericPoint_mem_of_nonempty {U : X.Opens} (hne : Nonempty U) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)

/-- The nonempty affine opens of a scheme form a basis of its topology. -/
theorem isBasis_nonemptyAffineOpens (Y : Scheme.{u}) :
    Opens.IsBasis (Set.range
      (fun U : {U : Y.Opens // IsAffineOpen U ∧ Nonempty U} ↦ U.1)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hx
  exact ⟨V, ⟨⟨V, hV, ⟨⟨x, hxV⟩⟩⟩, rfl⟩, hxV, hVU⟩

/-- Over an open set containing the generic point, the sections of the skyscraper sheaf at the
generic point are the function field. -/
theorem skyObj {U : X.Opens} (hU : genericPoint X ∈ U) :
    (skyscraperPresheaf (genericPoint X) X.functionField).obj (op U) = X.functionField :=
  (skyscraperPresheaf_obj (genericPoint X) X.functionField (op U)).trans (ite_eq_left hU)

/-- The sections of the constant presheaf are its value. -/
theorem constObj (U : X.Opens) :
    (constantPresheafOnSpace X CommRingCat.{u} X.functionField).obj (op U) = X.functionField :=
  rfl

/-- The germ at the generic point, read as a map into the sections of the constant presheaf. -/
noncomputable def constantGerm {U : X.Opens} (h : genericPoint X ∈ U) :
    Γ(X, U) ⟶ (constantPresheafOnSpace X CommRingCat.{u} X.functionField).obj (op U) :=
  X.presheaf.germ U (genericPoint X) h ≫ eqToHom (constObj X U).symm

/-- The comparison morphism from the presheaf of total quotient rings to the skyscraper sheaf at
the generic point with value the function field. -/
noncomputable def toSkyscraper :
    X.presheaf.totalQuotientPresheaf ⟶ skyscraperPresheaf (genericPoint X) X.functionField :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _ (stalkToFunctionField X)

/-- A map into the skyscraper sheaf built from a stalk map is, over an open set containing the
generic point, the germ followed by that stalk map. -/
private theorem toSkyscraperPresheaf_app_comp {F : TopCat.Presheaf CommRingCat.{u} X}
    (f : F.stalk (genericPoint X) ⟶ X.functionField) {U : X.Opens} (hU : genericPoint X ∈ U) :
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _ f).app (op U) ≫
      eqToHom (skyObj X hU) = F.germ U (genericPoint X) hU ≫ f := by
  have h := StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk _
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _ f) U hU
  rw [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper] at h
  exact h.symm

/-- Over an open set containing the generic point, the comparison morphism to the skyscraper is
the germ-at-the-generic-point extension. -/
theorem toSkyscraper_app_comp {U : X.Opens} (hU : genericPoint X ∈ U) :
    (toSkyscraper X).app (op U) ≫ eqToHom (skyObj X hU) = toFunctionFieldApp X hU := by
  rw [toSkyscraper, toSkyscraperPresheaf_app_comp X _ hU, germ_stalkToFunctionField]

/-- On a nonempty affine open the germ-at-the-generic-point extension is an isomorphism. -/
theorem isIso_toFunctionFieldApp {U : X.Opens} (hU : IsAffineOpen U) (hne : Nonempty U) :
    IsIso (toFunctionFieldApp X (genericPoint_mem_of_nonempty X hne)) := by
  let _ : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    GenericPointProduct.algebraTotalQuotientObj X (op U)
  have : IsLocalization (nonZeroDivisors Γ(X, U))
      (X.presheaf.totalQuotientPresheaf.obj (op U)) := by
    rw [← submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU]
    exact GenericPointProduct.isLocalizationTotalQuotientObj X (op U)
  have : IsLocalization (nonZeroDivisors Γ(X, U)) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let e := IsLocalization.algEquiv (nonZeroDivisors Γ(X, U))
    (X.presheaf.totalQuotientPresheaf.obj (op U)) X.functionField
  have key : (toFunctionFieldApp X (genericPoint_mem_of_nonempty X hne)).hom =
      e.toAlgHom.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, U)) (RingHom.ext fun r ↦ ?_)
    change toFunctionFieldApp X (genericPoint_mem_of_nonempty X hne)
        (X.presheaf.toTotalQuotientPresheaf.app (op U) r) = e (algebraMap _ _ r)
    rw [toFunctionFieldApp_apply, e.commutes]
    simp [RingHom.algebraMap_toAlgebra]
  rw [ConcreteCategory.isIso_iff_bijective]
  convert e.bijective using 1
  exact funext (DFunLike.congr_fun key)

/-- Over an open set containing the generic point, the comparison to the skyscraper is the
germ-at-the-generic-point extension, read into the skyscraper's value. -/
theorem toSkyscraper_app_eq {U : X.Opens} (hU : genericPoint X ∈ U) :
    (toSkyscraper X).app (op U) =
      toFunctionFieldApp X hU ≫ inv (eqToHom (skyObj X hU)) := by
  rw [IsIso.eq_comp_inv, toSkyscraper_app_comp X hU]

/-- On a nonempty affine open the comparison to the skyscraper is an isomorphism. -/
theorem isIso_toSkyscraper_app {U : X.Opens} (hU : IsAffineOpen U) (hne : Nonempty U) :
    IsIso ((toSkyscraper X).app (op U)) := by
  have := isIso_toFunctionFieldApp X hU hne
  rw [toSkyscraper_app_eq X (genericPoint_mem_of_nonempty X hne)]
  infer_instance

/-- The constant cocone on the diagram computing the stalk of the constant presheaf. -/
noncomputable def constantCocone :
    Cocone ((OpenNhds.inclusion (genericPoint X)).op ⋙
      constantPresheafOnSpace X CommRingCat.{u} X.functionField) :=
  Cocone.mk X.functionField
    { app := fun _ ↦ 𝟙 X.functionField
      naturality := fun V W i ↦ by simp [constantPresheafOnSpace] }

/-- The canonical map from the stalk of the constant presheaf at the generic point to its
value. -/
noncomputable def constantStalkToFunctionField :
    (constantPresheafOnSpace X CommRingCat.{u} X.functionField).stalk (genericPoint X) ⟶
      X.functionField :=
  colimit.desc _ (constantCocone X)

/-- The germ map of the constant presheaf at the generic point followed by
`constantStalkToFunctionField` is the identity. -/
@[simp]
theorem germ_constantStalkToFunctionField {U : X.Opens} (hU : genericPoint X ∈ U) :
    (constantPresheafOnSpace X CommRingCat.{u} X.functionField).germ U (genericPoint X) hU ≫
        constantStalkToFunctionField X = 𝟙 X.functionField :=
  colimit.ι_desc (constantCocone X) (op ⟨U, hU⟩)

/-- The comparison morphism from the constant presheaf to the skyscraper sheaf. -/
noncomputable def constantToSkyscraper :
    constantPresheafOnSpace X CommRingCat.{u} X.functionField ⟶
      skyscraperPresheaf (genericPoint X) X.functionField :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _ (constantStalkToFunctionField X)

/-- Over an open set containing the generic point, the comparison from the constant presheaf to
the skyscraper is the identity. -/
theorem constantToSkyscraper_app_comp {U : X.Opens} (hU : genericPoint X ∈ U) :
    (constantToSkyscraper X).app (op U) ≫ eqToHom (skyObj X hU) =
      eqToHom (constObj X U) := by
  rw [constantToSkyscraper, toSkyscraperPresheaf_app_comp X _ hU, germ_constantStalkToFunctionField]
  rfl

/-- Over an open set containing the generic point, the comparison from the constant presheaf to
the skyscraper is the canonical identification of the sections. -/
theorem constantToSkyscraper_app_eq {U : X.Opens} (hU : genericPoint X ∈ U) :
    (constantToSkyscraper X).app (op U) =
      eqToHom (constObj X U) ≫ inv (eqToHom (skyObj X hU)) := by
  rw [IsIso.eq_comp_inv, constantToSkyscraper_app_comp X hU]

/-- The comparison from the constant presheaf to the skyscraper is an isomorphism over every
open set containing the generic point. -/
theorem isIso_constantToSkyscraper_app {U : X.Opens} (hU : genericPoint X ∈ U) :
    IsIso ((constantToSkyscraper X).app (op U)) := by
  rw [constantToSkyscraper_app_eq X hU]
  infer_instance

/-- The skyscraper presheaf at the generic point with value the function field is a sheaf. -/
theorem isSheaf_skyscraper : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (skyscraperPresheaf (genericPoint X) X.functionField) :=
  skyscraperPresheaf_isSheaf _ _

/-- A map from a presheaf to the skyscraper sheaf at the generic point which is an isomorphism on
every nonempty affine open induces an isomorphism from the sheafification. -/
private theorem isIso_sheafifyLift_skyscraper {F : TopCat.Presheaf CommRingCat.{u} X}
    (ψ : F ⟶ skyscraperPresheaf (genericPoint X) X.functionField)
    (hψ : ∀ V : {U : X.Opens // IsAffineOpen U ∧ Nonempty U}, IsIso (ψ.app (op V.1))) :
    IsIso (sheafifyLift (Opens.grothendieckTopology X) ψ (isSheaf_skyscraper X)) :=
  GenericPointProduct.isIso_sheafifyLift_of_isIso_basis
    (G := skyscraperSheaf (genericPoint X) X.functionField)
    (isBasis_nonemptyAffineOpens X) ψ hψ

/-- The morphism from the sheafification of the presheaf of total quotient rings to the
skyscraper sheaf at the generic point induced by `toSkyscraper` is an isomorphism. -/
theorem isIso_sheafifyLift_toSkyscraper :
    IsIso (sheafifyLift (Opens.grothendieckTopology X) (toSkyscraper X)
      (isSheaf_skyscraper X)) :=
  isIso_sheafifyLift_skyscraper X _ fun V ↦ isIso_toSkyscraper_app X V.2.1 V.2.2

/-- The morphism from the sheafification of the constant presheaf to the skyscraper sheaf at the
generic point induced by `constantToSkyscraper` is an isomorphism. -/
theorem isIso_sheafifyLift_constantToSkyscraper :
    IsIso (sheafifyLift (Opens.grothendieckTopology X) (constantToSkyscraper X)
      (isSheaf_skyscraper X)) :=
  isIso_sheafifyLift_skyscraper X _ fun V ↦
    isIso_constantToSkyscraper_app X (genericPoint_mem_of_nonempty X V.2.2)

/-- The sheafification of the presheaf of total quotient rings is the skyscraper sheaf at the
generic point. -/
noncomputable def skyscraperPresheafIso :
    sheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ≅
      skyscraperPresheaf (genericPoint X) X.functionField :=
  haveI := isIso_sheafifyLift_toSkyscraper X
  asIso (sheafifyLift (Opens.grothendieckTopology X) (toSkyscraper X) (isSheaf_skyscraper X))

/-- The forward map of `skyscraperPresheafIso` is the sheafification lift of `toSkyscraper`. -/
theorem skyscraperPresheafIso_hom :
    (skyscraperPresheafIso X).hom =
      sheafifyLift (Opens.grothendieckTopology X) (toSkyscraper X) (isSheaf_skyscraper X) := rfl

/-- The sheafification of the constant presheaf is the skyscraper sheaf at the generic point. -/
noncomputable def constantPresheafSkyscraperIso :
    sheafify (Opens.grothendieckTopology X)
        (constantPresheafOnSpace X CommRingCat.{u} X.functionField) ≅
      skyscraperPresheaf (genericPoint X) X.functionField :=
  haveI := isIso_sheafifyLift_constantToSkyscraper X
  asIso (sheafifyLift (Opens.grothendieckTopology X) (constantToSkyscraper X)
    (isSheaf_skyscraper X))

/-- The forward map of `constantPresheafSkyscraperIso` is the sheafification lift of
`constantToSkyscraper`. -/
theorem constantPresheafSkyscraperIso_hom :
    (constantPresheafSkyscraperIso X).hom =
      sheafifyLift (Opens.grothendieckTopology X) (constantToSkyscraper X)
        (isSheaf_skyscraper X) := rfl

/-- The two comparisons agree on the image of the regular functions: the total quotient class of
a regular function and the constant section given by its germ at the generic point have the same
image in the skyscraper sheaf. -/
theorem toSkyscraper_apply_eq_constantToSkyscraper_apply {U : X.Opens}
    (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    (toSkyscraper X).app (op U) (X.presheaf.toTotalQuotientPresheaf.app (op U) s) =
      (constantToSkyscraper X).app (op U) (constantGerm X h s) := by
  refine (ConcreteCategory.bijective_of_isIso (eqToHom (skyObj X h))).1 ?_
  have e1 := ConcreteCategory.congr_hom (toSkyscraper_app_comp X h)
    (X.presheaf.toTotalQuotientPresheaf.app (op U) s)
  have e2 : eqToHom (skyObj X h) ((constantToSkyscraper X).app (op U) (constantGerm X h s)) =
      eqToHom (constObj X U) (constantGerm X h s) :=
    ConcreteCategory.congr_hom (constantToSkyscraper_app_comp X h) _
  rw [ConcreteCategory.comp_apply, toFunctionFieldApp_apply] at e1
  rw [e1, e2]
  rfl

/-- The sheafification of the presheaf of total quotient rings is the sheafification of the
constant presheaf with value the function field. -/
noncomputable def presheafIso :
    sheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ≅
      sheafify (Opens.grothendieckTopology X)
        (constantPresheafOnSpace X CommRingCat.{u} X.functionField) :=
  skyscraperPresheafIso X ≪≫ (constantPresheafSkyscraperIso X).symm

/-- The forward map of `presheafIso` is the forward map of `skyscraperPresheafIso` followed by the
inverse of `constantPresheafSkyscraperIso`. -/
theorem presheafIso_hom :
    (presheafIso X).hom =
      (skyscraperPresheafIso X).hom ≫ (constantPresheafSkyscraperIso X).inv := rfl

/-- The sheaf of total quotient rings of an integral scheme is the constant sheaf with value its
function field. -/
noncomputable def sheafIso :
    totalQuotientSheaf X.sheaf ≅ constantSheafOnSpace X CommRingCat.{u} X.functionField :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).preimageIso
    (presheafIso X)

/-- The underlying morphism of presheaves of the forward map of `sheafIso` is the forward map of
`presheafIso`. -/
theorem sheafIso_hom_hom : (sheafIso X).hom.hom = (presheafIso X).hom :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map_preimage _

/-- The sheafification unit followed by the identification with the skyscraper sheaf is the
comparison morphism. -/
@[reassoc]
theorem toSheafify_comp_skyscraperPresheafIso (U : (Opens X)ᵒᵖ) :
    (toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf).app U ≫
        (skyscraperPresheafIso X).hom.app U = (toSkyscraper X).app U := by
  rw [skyscraperPresheafIso_hom, ← NatTrans.comp_app, toSheafify_sheafifyLift]

/-- The sheafification unit of the constant presheaf followed by the identification with the
skyscraper sheaf is the comparison morphism. -/
@[reassoc]
theorem toSheafify_comp_constantPresheafSkyscraperIso (U : (Opens X)ᵒᵖ) :
    (toSheafify (Opens.grothendieckTopology X)
          (constantPresheafOnSpace X CommRingCat.{u} X.functionField)).app U ≫
        (constantPresheafSkyscraperIso X).hom.app U = (constantToSkyscraper X).app U := by
  rw [constantPresheafSkyscraperIso_hom, ← NatTrans.comp_app, toSheafify_sheafifyLift]

/-- The two comparisons agree on the regular functions, as morphisms. -/
@[reassoc]
theorem toTotalQuotient_comp_toSkyscraper {U : X.Opens} (h : genericPoint X ∈ U) :
    X.presheaf.toTotalQuotientPresheaf.app (op U) ≫ (toSkyscraper X).app (op U) =
      constantGerm X h ≫ (constantToSkyscraper X).app (op U) :=
  CommRingCat.hom_ext (RingHom.ext fun s ↦
    toSkyscraper_apply_eq_constantToSkyscraper_apply X h s)

/-- The identification of the sheafifications sends the image of a regular function to the
constant section given by its germ at the generic point. -/
theorem presheafIso_hom_app_comp {U : X.Opens} (h : genericPoint X ∈ U) :
    X.presheaf.toTotalQuotientPresheaf.app (op U) ≫
        ((toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf).app (op U) ≫
            (presheafIso X).hom.app (op U)) =
      constantGerm X h ≫
        (toSheafify (Opens.grothendieckTopology X)
          (constantPresheafOnSpace X CommRingCat.{u} X.functionField)).app (op U) := by
  rw [presheafIso_hom, NatTrans.comp_app,
    toSheafify_comp_skyscraperPresheafIso_assoc,
    toTotalQuotient_comp_toSkyscraper_assoc X h,
    ← toSheafify_comp_constantPresheafSkyscraperIso_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- `sheafIso` sends the image of a regular function `s` in the sheaf of total quotient rings to
the image in the sheafified constant presheaf of the germ of `s` at the generic point. -/
theorem sheafIso_hom_app_apply (U : X.Opens) (s : Γ(X, U)) (h : genericPoint X ∈ U) :
    (sheafIso X).hom.hom.app (op U) ((toTotalQuotientSheaf X.sheaf).hom.app (op U) s) =
      (toSheafify (Opens.grothendieckTopology X)
        (constantPresheafOnSpace X CommRingCat.{u} X.functionField)).app (op U)
          (X.presheaf.germ U (genericPoint X) h s) :=
  ConcreteCategory.congr_hom (presheafIso_hom_app_comp X h) s

/-- On an integral scheme the sheaf of meromorphic functions is the constant sheaf with value the
function field, by an isomorphism carrying the image of a regular function to the constant
section given by its germ at the generic point. -/
@[stacks 01X5 "part (1)", ega "I 7.3.6" "F = O_X, integral"]
noncomputable def totalQuotientSheafIsoConstant :
    { e : totalQuotientSheaf X.sheaf ≅ constantSheafOnSpace X CommRingCat.{u} X.functionField //
      ∀ (U : X.Opens) (s : X.presheaf.obj (op U)) (h : genericPoint X ∈ U),
        (e.hom.hom.app (op U)).hom
          ((toTotalQuotientSheaf X.sheaf).hom.app (op U) s) =
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)
            (X.presheaf.germ U (genericPoint X) h s) } :=
  ⟨sheafIso X, fun U s h ↦ sheafIso_hom_app_apply X U s h⟩

end Stacks.AlgebraicGeometry.MeromorphicConstant

end
