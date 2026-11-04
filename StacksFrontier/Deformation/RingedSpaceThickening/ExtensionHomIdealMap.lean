module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInjective

/-!
# The map of ideals induced by a map of square-zero extensions

Let `𝒪'₁` and `𝒪'₂` be square-zero extensions of `𝒪_X` by `𝒢₁` and `𝒢₂`, over possibly different
bases, with bijective identifications of their ideals, and let `β : 𝒪'₁ ⟶ 𝒪'₂` be a ring map over
`𝒪_X`. Then `β` carries the ideal of `𝒪'₁` into the ideal of `𝒪'₂`, and the induced map
`𝒢₁ ⟶ 𝒢₂` is `𝒪_X`-linear.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.idealMapOfHom`: the
  morphism `𝒢₁ ⟶ 𝒢₂` of `𝒪_X`-modules induced by `β`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.hom_idealIncl_eq`: `β` on the
  inclusion of a section `n` of `𝒢₁` is the inclusion of its image.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Sites.Conormal (kernelIdeal presentationScalar)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension

variable {X T₁ T₂ : RingedSpace.{u, u}} {h₁ : X ⟶ T₁} {h₂ : X ⟶ T₂}
  {G₁ G₂ : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P₁ : AlgebraSquareZeroExtension h₁ G₁) (P₂ : AlgebraSquareZeroExtension h₂ G₂)
  (hP₁ : ∀ U, Function.Bijective (P₁.ideal.app U)) (hP₂ : ∀ U, Function.Bijective (P₂.ideal.app U))
  (β : P₁.sheaf ⟶ P₂.sheaf) (hβ : β ≫ P₂.reduction = P₁.reduction)

include hβ in
/-- A map of extensions over `𝒪_X` carries the ideal into the ideal. -/
theorem hom_idealIncl_mem (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U) :
    (β.hom.app U).hom (P₁.idealIncl hP₁ U n) ∈ kernelIdeal P₂.reduction.hom U :=
  (congrArg (fun t : P₁.sheaf ⟶ X.sheaf => (t.hom.app U).hom (P₁.idealIncl hP₁ U n)) hβ).trans
    (P₁.reduction_idealIncl hP₁ U n)

/-- The map `𝒢₁(U) ⟶ 𝒢₂(U)` induced by a map of extensions. -/
def idealMapApp (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U) : G₂.val.obj U :=
  P₂.ideal.app U ⟨(β.hom.app U).hom (P₁.idealIncl hP₁ U n), P₁.hom_idealIncl_mem P₂ hP₁ β hβ U n⟩

/-- **A map of extensions on the inclusion of `𝒢₁`** is the inclusion of the induced map. -/
theorem hom_idealIncl_eq (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U) :
    (β.hom.app U).hom (P₁.idealIncl hP₁ U n) =
      P₂.idealIncl hP₂ U (P₁.idealMapApp P₂ hP₁ β hβ U n) :=
  (P₂.idealIncl_ideal hP₂ U ⟨_, P₁.hom_idealIncl_mem P₂ hP₁ β hβ U n⟩).symm

/-- The induced map sends `n` to the preimage of any element of the ideal that `n` is sent to. -/
private theorem idealMapApp_eq_ideal_app (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U)
    (x : ↥(kernelIdeal P₂.reduction.hom U))
    (h : (β.hom.app U).hom (P₁.idealIncl hP₁ U n) = x.1) :
    P₁.idealMapApp P₂ hP₁ β hβ U n = P₂.ideal.app U x :=
  congrArg (P₂.ideal.app U) (Subtype.ext h)

/-- The map `𝒢₁(U) ⟶ 𝒢₂(U)` induced by a map of extensions is additive. -/
theorem idealMapApp_add (U : (Opens X.carrier)ᵒᵖ) (n n' : G₁.val.obj U) :
    P₁.idealMapApp P₂ hP₁ β hβ U (n + n') =
      P₁.idealMapApp P₂ hP₁ β hβ U n + P₁.idealMapApp P₂ hP₁ β hβ U n' := by
  refine (P₁.idealMapApp_eq_ideal_app P₂ hP₁ β hβ U _ _ ?_).trans (map_add (P₂.ideal.app U) _ _)
  exact (congrArg _ (P₁.idealIncl_add hP₁ U n n')).trans (map_add _ _ _)

/-- The maps `𝒢₁(U) ⟶ 𝒢₂(U)` induced by a map of extensions commute with restriction. -/
theorem idealMapApp_map {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V) (n : G₁.val.obj U) :
    P₁.idealMapApp P₂ hP₁ β hβ V (G₁.val.map k n) =
      G₂.val.map k (P₁.idealMapApp P₂ hP₁ β hβ U n) := by
  refine (P₁.idealMapApp_eq_ideal_app P₂ hP₁ β hβ V _ _ ?_).trans (P₂.ideal.app_map k _)
  change (β.hom.app V).hom (P₁.idealIncl hP₁ V (G₁.val.map k n)) =
    (P₂.sheaf.obj.map k).hom ((β.hom.app U).hom (P₁.idealIncl hP₁ U n))
  rw [P₁.idealIncl_map hP₁ k]
  exact congrArg (fun t => t.hom (P₁.idealIncl hP₁ U n)) (β.hom.naturality k)

/-- The induced map is linear over the sections of `𝒪_X` which lift to `𝒪'₁`. -/
theorem idealMapApp_smul_reduction (U : (Opens X.carrier)ᵒᵖ) (b : P₁.sheaf.obj.obj U)
    (n : G₁.val.obj U) :
    P₁.idealMapApp P₂ hP₁ β hβ U (presentationScalar P₁.reduction U b • n) =
      presentationScalar P₁.reduction U b • P₁.idealMapApp P₂ hP₁ β hβ U n := by
  have hb : presentationScalar P₂.reduction U ((β.hom.app U).hom b) =
      presentationScalar P₁.reduction U b :=
    congrArg (fun t : P₁.sheaf ⟶ X.sheaf => (t.hom.app U).hom b) hβ
  have h1 : (β.hom.app U).hom (P₁.idealIncl hP₁ U (presentationScalar P₁.reduction U b • n)) =
      (β.hom.app U).hom b * (β.hom.app U).hom (P₁.idealIncl hP₁ U n) := by
    rw [← P₁.mul_idealIncl hP₁ U, map_mul]
  refine (P₁.idealMapApp_eq_ideal_app P₂ hP₁ β hβ U _
    ((β.hom.app U).hom b • ⟨(β.hom.app U).hom (P₁.idealIncl hP₁ U n),
      P₁.hom_idealIncl_mem P₂ hP₁ β hβ U n⟩) h1).trans ?_
  rw [P₂.ideal.app_smul, hb]
  rfl

/-- **The induced map is `𝒪_X`-linear.** -/
theorem idealMapApp_smul (U : (Opens X.carrier)ᵒᵖ)
    (a : ↥((ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf).obj.obj U))
    (n : G₁.val.obj U) :
    P₁.idealMapApp P₂ hP₁ β hβ U (a • n) = a • P₁.idealMapApp P₂ hP₁ β hβ U n := by
  obtain ⟨U⟩ := U
  have hsurj := (TopCat.Presheaf.isLocallySurjective_iff P₁.reduction.hom).1
    P₁.reduction_surjective U (show ↥(X.sheaf.obj.obj (op U)) from a)
  choose V hVU hV hxV using fun x : U => hsurj x.1 x.2
  choose b hb using hV
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨G₂.val.presheaf, G₂.isSheaf⟩ V U (fun x => homOfLE (hVU x))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxV _⟩) _ _ (fun x => ?_)
  have hres : (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf).obj.map
      (homOfLE (hVU x)).op a = presentationScalar P₁.reduction (op (V x)) (b x) := (hb x).symm
  change G₂.val.map (homOfLE (hVU x)).op _ = G₂.val.map (homOfLE (hVU x)).op _
  rw [← idealMapApp_map, G₁.val.map_smul, G₂.val.map_smul, ← idealMapApp_map, hres]
  exact P₁.idealMapApp_smul_reduction P₂ hP₁ β hβ (op (V x)) (b x) _

/-- **The morphism `𝒢₁ ⟶ 𝒢₂` of `𝒪_X`-modules induced by a map of extensions over `𝒪_X`.** -/
def idealMapOfHom : G₁ ⟶ G₂ where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := P₁.idealMapApp P₂ hP₁ β hβ U
          map_add' := P₁.idealMapApp_add P₂ hP₁ β hβ U
          map_smul' := P₁.idealMapApp_smul P₂ hP₁ β hβ U }
      naturality := fun k => ModuleCat.hom_ext (LinearMap.ext fun n =>
        P₁.idealMapApp_map P₂ hP₁ β hβ k n) }

/-- On sections over `U`, the morphism `idealMapOfHom` is the map `idealMapApp`. -/
theorem idealMapOfHom_app (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U) :
    ((P₁.idealMapOfHom P₂ hP₁ β hβ).val.app U).hom n = P₁.idealMapApp P₂ hP₁ β hβ U n :=
  rfl

/-- **A map of extensions is, on the ideals, the induced morphism of modules.** -/
theorem hom_idealIncl_idealMapOfHom (U : (Opens X.carrier)ᵒᵖ) (n : G₁.val.obj U) :
    (β.hom.app U).hom (P₁.idealIncl hP₁ U n) =
      P₂.idealIncl hP₂ U (((P₁.idealMapOfHom P₂ hP₁ β hβ).val.app U).hom n) :=
  P₁.hom_idealIncl_eq P₂ hP₁ hP₂ β hβ U n

end AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension
