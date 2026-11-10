module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationDiagram
public import StacksFrontier.Deformation.RingedSpaceThickening.LiftSquareInverseImage
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionObstruction
import StacksFrontier.Topology.Sheaves.RingedSpace.ThickeningTrivialization
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel

/-!
# One layer of the diagram of Stacks 08U8 on the reduced space

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces. Its underlying
continuous map is a homeomorphism `X ≅ X'`, and the source of Stacks 08U8 identifies the two
spaces: `𝒪_{X'}` is then a sheaf of rings on `X`, namely the direct image
`k_*𝒪_{X'}` along the inverse homeomorphism `k : X' ⟶ X`, and `i^♯` is a surjection
`k_*𝒪_{X'} ⟶ 𝒪_X` with square-zero kernel. This file records that reading, together with a
module `𝒢` on `X` identified with the ideal of `i`, as a layer
`Deformation.ToposThickening.LiftSquare` on `X`, the base of the layer being a first order
thickening `t : S ⟶ S'` read on `X` through `f : X ⟶ S`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.thickeningHomeo`: the homeomorphism underlying a
  thickening.
* `AlgebraicGeometry.RingedSpaceThickening.thickenedRing` and
  `AlgebraicGeometry.RingedSpaceThickening.thickeningReduction`: the thickened structure sheaf
  read on the reduced space, and the reduction `k_*𝒪_{X'} ⟶ 𝒪_X`.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningKernelInclusion`: the inclusion
  `𝒢 ⟶ k_*𝒪_{X'}` of the module identified with the ideal.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.thickeningReduction_isLocallySurjective` and
  `AlgebraicGeometry.RingedSpaceThickening.thickeningReduction_squareZero`: the reduction is
  locally surjective with square-zero kernel.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningKernelUniversal`: the inclusion identifies
  `𝒢` with the kernel of the reduction, section by section.

## Implementation notes

The direct image along the inverse homeomorphism is used rather than the inverse image along
the thickening: its sections are those of `𝒪_{X'}` (`k_*𝒪_{X'}(U) = 𝒪_{X'}(k⁻¹U)`), so a morphism
into it is a comorphism, and the reduction is `i^♯` on `k⁻¹U` followed by the identification of
`i⁻¹k⁻¹U` with `U` (the components of Mathlib's `TopCat.Presheaf.pushforwardToOfIso` of `i^♯`).
All sectionwise identities below are proved by collapsing composites of restriction maps into one
restriction map; two morphisms between the same two opens are equal.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The structure sheaf of a ringed space, spelled as a sheaf on the site of opens. -/
abbrev ringOf (X : RingedSpace.{u, u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  X.sheaf

/-- A first order thickening is a thickening. -/
theorem IsFirstOrderThickening.isThickening {X X' : RingedSpace.{u, u}} {i : X ⟶ X'}
    (h : IsFirstOrderThickening i) : IsThickening i :=
  h.1

section Homeo

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X') (hi : IsThickening i)

/-- The homeomorphism underlying a thickening. -/
def thickeningHomeo : X.carrier ≅ X'.carrier :=
  @asIso _ _ _ _ i.hom.base hi.1

/-- The homeomorphism underlying a thickening is the underlying map of the thickening. -/
@[simp]
theorem thickeningHomeo_hom : (thickeningHomeo i hi).hom = i.hom.base := rfl

/-- The thickened structure sheaf `𝒪_{X'}` read on the reduced space, as the direct image along
the inverse of the homeomorphism underlying the thickening. -/
abbrev thickenedRing : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  (ringPushforward (thickeningHomeo i hi).inv).obj (ringOf X')

/-- The preimage of an open under the composite of the inverse homeomorphism and the
thickening is the open itself. -/
theorem thickening_preimage_preimage (U : Opens X.carrier) :
    (Opens.map i.hom.base).obj ((Opens.map (thickeningHomeo i hi).inv).obj U) = U := by
  rw [← Opens.map_comp_obj]
  change (Opens.map ((thickeningHomeo i hi).hom ≫ (thickeningHomeo i hi).inv)).obj U = U
  rw [Iso.hom_inv_id]
  rfl

/-- The preimage of an open under the composite of the thickening and the inverse homeomorphism
is the open itself. -/
theorem thickening_preimage_preimage' (W : Opens X'.carrier) :
    (Opens.map (thickeningHomeo i hi).inv).obj ((Opens.map i.hom.base).obj W) = W := by
  rw [← Opens.map_comp_obj]
  change (Opens.map ((thickeningHomeo i hi).inv ≫ (thickeningHomeo i hi).hom)).obj W = W
  rw [Iso.inv_hom_id]
  rfl

/-- **The reduction `k_*𝒪_{X'} ⟶ 𝒪_X` of a thickening**, the comorphism `i^♯` read on the reduced
space: on an open `U` of `X` it is `i^♯` on `k⁻¹U`, followed by the identification of
`i⁻¹k⁻¹U` with `U`. -/
def thickeningReduction : thickenedRing i hi ⟶ ringOf X :=
  ObjectProperty.homMk
    { app := fun U => i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U.unop)) ≫
        X.presheaf.map (homOfLE (thickening_preimage_preimage i hi U.unop).ge).op
      naturality := fun U V g => by
        change X'.presheaf.map _ ≫ i.hom.c.app _ ≫ X.presheaf.map _ =
          (i.hom.c.app _ ≫ X.presheaf.map _) ≫ X.presheaf.map g
        rw [← Category.assoc, i.hom.c.naturality, Category.assoc, Category.assoc]
        change i.hom.c.app _ ≫ X.presheaf.map ((Opens.map i.hom.base).op.map
            ((Opens.map (thickeningHomeo i hi).inv).op.map g)) ≫ X.presheaf.map _ =
          i.hom.c.app _ ≫ X.presheaf.map _ ≫ X.presheaf.map g
        rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
        rfl }

/-- The reduction on sections. -/
theorem thickeningReduction_apply (U : Opens X.carrier)
    (x : X'.presheaf.obj (op ((Opens.map (thickeningHomeo i hi).inv).obj U))) :
    (thickeningReduction i hi).hom.app (op U) x =
      X.presheaf.map (homOfLE (thickening_preimage_preimage i hi U).ge).op
        (i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U)) x) := rfl

end Homeo

section Restrict

variable {Z : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} Z)

/-- Two restriction maps of a presheaf of commutative rings compose to one. -/
theorem presheaf_map_map_apply {U V W : (Opens Z)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (x : F.obj U) :
    F.map g (F.map f x) = F.map (f ≫ g) x := by
  rw [F.map_comp, ConcreteCategory.comp_apply]

/-- A restriction map of a presheaf of commutative rings depends only on its source and
target. -/
theorem presheaf_map_congr {U V : (Opens Z)ᵒᵖ} (f g : U ⟶ V) (x : F.obj U) :
    F.map f x = F.map g x := by
  rw [Subsingleton.elim f g]

/-- Restricting between two opens contained in each other is injective. -/
theorem presheaf_map_homOfLE_injective {U V : Opens Z} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (F.map (homOfLE h).op) := by
  intro x y hxy
  have key : ∀ z, F.map (homOfLE h').op (F.map (homOfLE h).op z) = z := fun z => by
    rw [presheaf_map_map_apply, show (homOfLE h).op ≫ (homOfLE h').op = 𝟙 (op U) from rfl,
      F.map_id]
    rfl
  rw [← key x, ← key y, hxy]

/-- Two restriction maps of a presheaf of commutative rings compose to any restriction map with
the same source and target. -/
private theorem presheaf_map_map_eq {U V W : (Opens Z)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W)
    (x : F.obj U) : F.map g (F.map f x) = F.map h x :=
  (presheaf_map_map_apply F f g x).trans (presheaf_map_congr F _ h x)

/-- Naturality of the comorphism of a morphism of ringed spaces, on sections. -/
private theorem c_app_map_apply {A B : RingedSpace.{u, u}} (α : A ⟶ B) {U V : (Opens B.carrier)ᵒᵖ}
    (g : U ⟶ V) (a : B.presheaf.obj U) :
    α.hom.c.app V (B.presheaf.map g a) =
      A.presheaf.map ((Opens.map α.hom.base).op.map g) (α.hom.c.app U a) :=
  ConcreteCategory.congr_hom (α.hom.c.naturality g) a

end Restrict

section Reduction

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X') (hi : IsThickening i)

/-- **The reduction of a thickening is locally surjective.** -/
theorem thickeningReduction_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (thickeningReduction i hi).hom := by
  constructor
  intro U s y hy
  let W : Opens X'.carrier := (Opens.map (thickeningHomeo i hi).inv).obj U
  have hUW := thickening_preimage_preimage i hi U
  let s' : X.presheaf.obj (op ((Opens.map i.hom.base).obj W)) :=
    X.presheaf.map (homOfLE hUW.le).op s
  obtain ⟨W', iW, ⟨t, ht⟩, hyW'⟩ :=
    (isLocallySurjective_comorphism_of_isThickening i hi).imageSieve_mem s' (i.hom.base y)
      (hUW.ge hy)
  let V : Opens X.carrier := (Opens.map i.hom.base).obj W'
  have hVU : V ≤ U := fun z hz => hUW.le (iW.le hz)
  have hW'V := thickening_preimage_preimage' i hi W'
  refine ⟨V, homOfLE hVU, ⟨X'.presheaf.map (homOfLE hW'V.le).op t, ?_⟩, hyW'⟩
  change (thickeningReduction i hi).hom.app (op V) (X'.presheaf.map (homOfLE hW'V.le).op t) =
    X.presheaf.map (homOfLE hVU).op s
  rw [thickeningReduction_apply, c_app_map_apply, ht]
  change X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _ s')) = _
  simp only [s', presheaf_map_map_apply]
  exact presheaf_map_map_eq _ _ _ _ _

/-- **The kernel of the reduction of a first order thickening has square zero.** -/
theorem thickeningReduction_squareZero (hfo : IsFirstOrderThickening i)
    (U : (Opens X.carrier)ᵒᵖ) :
    (RingHom.ker ((thickeningReduction i hfo.isThickening).hom.app U).hom) ^ 2 = ⊥ := by
  obtain ⟨U⟩ := U
  change RingHom.ker ((X.presheaf.map (homOfLE
    (thickening_preimage_preimage i hfo.isThickening U).ge).op).hom.comp
      (i.hom.c.app (op ((Opens.map (thickeningHomeo i hfo.isThickening).inv).obj U))).hom) ^ 2 = ⊥
  rw [RingHom.ker_comp_of_injective _ (presheaf_map_homOfLE_injective X.presheaf _
    (thickening_preimage_preimage i hfo.isThickening U).le)]
  exact hfo.2 _

end Reduction

section ModuleRestrict

variable {Z : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}
  (M : SheafOfModules.{u} R)

/-- Restriction of sections of a sheaf of modules on a space, with its codomain spelled as the
sections of the sheaf itself. -/
def mres {U V : Opens Z} (h : V ≤ U) (x : M.val.obj (op U)) : M.val.obj (op V) :=
  M.val.map (homOfLE h).op x

/-- Restricting twice is restricting once. -/
theorem mres_mres {U V W : Opens Z} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : M.val.obj (op U)) :
    mres M h₂ (mres M h₁ x) = mres M (h₂.trans h₁) x :=
  module_map_map M h₁ h₂ x

/-- Restricting from an open to itself is the identity. -/
theorem mres_self {U : Opens Z} (h : U ≤ U) (x : M.val.obj (op U)) : mres M h x = x :=
  module_map_self M h x

/-- Restriction is additive. -/
theorem mres_add {U V : Opens Z} (h : V ≤ U) (x y : M.val.obj (op U)) :
    mres M h (x + y) = mres M h x + mres M h y :=
  map_add (M.val.map (homOfLE h).op).hom x y

/-- Restriction kills zero. -/
theorem mres_zero {U V : Opens Z} (h : V ≤ U) : mres M h (0 : M.val.obj (op U)) = 0 :=
  map_zero (M.val.map (homOfLE h).op).hom

/-- Restriction is semilinear over restriction of scalars. -/
theorem mres_smul {U V : Opens Z} (h : V ≤ U) (r : R.obj.obj (op U)) (x : M.val.obj (op U)) :
    mres M h (r • x) = R.obj.map (homOfLE h).op r • mres M h x :=
  PresheafOfModules.map_smul M.val (homOfLE h).op r x

/-- Morphisms of sheaves of modules commute with restriction. -/
theorem mres_naturality {N : SheafOfModules.{u} R} (φ : M ⟶ N) {U V : Opens Z} (h : V ≤ U)
    (x : M.val.obj (op U)) : φ.val.app (op V) (mres M h x) = mres N h (φ.val.app (op U) x) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

/-- Restricting between two opens contained in each other is injective. -/
theorem mres_injective {U V : Opens Z} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (mres M h) := by
  intro x y hxy
  rw [← mres_self M (le_refl U) x, ← mres_self M (le_refl U) y, ← mres_mres M h h',
    ← mres_mres M h h', hxy]

end ModuleRestrict

section Kernel

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X') (hi : IsThickening i)
  (G : SheafOfModules.{u} (structureSheafRing X))
  (kernelIso : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅ (modulePushforward i).obj G)

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` on the thickened space: the identification of `i_*𝒢` with the
ideal of `i`, followed by the inclusion of the ideal. -/
abbrev thickeningIdealInclusion :
    (modulePushforward i).obj G ⟶ SheafOfModules.unit (structureSheafRing X') :=
  kernelIso.inv ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` on the sections over an open `W` of `X'`, a map from the
sections of `𝒢` over `i⁻¹W`. -/
def layerIdealIncl (W : Opens X'.carrier) :
    G.val.obj (op ((Opens.map i.hom.base).obj W)) →+ X'.presheaf.obj (op W) :=
  ((thickeningIdealInclusion i G kernelIso).val.app (op W)).hom.toAddMonoidHom

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` is killed by `i^♯`. -/
theorem layerIdealIncl_comp (W : Opens X'.carrier)
    (x : G.val.obj (op ((Opens.map i.hom.base).obj W))) :
    i.hom.c.app (op W) (layerIdealIncl i G kernelIso W x) = 0 :=
  congrArg (fun k => k.val.app (op W) (kernelIso.inv.val.app (op W) x))
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)))

/-- An isomorphism of sheaves of modules is inverted by its inverse, on sections. -/
private theorem iso_inv_hom_app_apply {Z : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Z)
    RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) (U : (Opens Z)ᵒᵖ) (z : N.val.obj U) :
    e.hom.val.app U (e.inv.val.app U z) = z :=
  congrArg (fun k => k.val.app U z) e.inv_hom_id

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` is injective on sections. -/
theorem layerIdealIncl_injective (W : Opens X'.carrier) :
    Function.Injective (layerIdealIncl i G kernelIso W) := by
  intro x y hxy
  have h1 := Stacks.SheafOfModules.injective_app_kernel_ι
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) (op W) hxy
  have h2 := congrArg (fun z => kernelIso.hom.val.app (op W) z) h1
  exact (iso_inv_hom_app_apply kernelIso _ x).symm.trans
    (h2.trans (iso_inv_hom_app_apply kernelIso _ y))

/-- The sections of `𝒪_{X'}` killed by `i^♯` are those of `i_*𝒢`. -/
theorem exists_idealIncl (W : Opens X'.carrier) (a : X'.presheaf.obj (op W))
    (ha : i.hom.c.app (op W) a = 0) : ∃ x, layerIdealIncl i G kernelIso W x = a := by
  obtain ⟨b, hb⟩ := exists_kernel_section
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)) (op W) a ha
  refine ⟨kernelIso.hom.val.app (op W) b, ?_⟩
  have e := iso_inv_hom_app_apply kernelIso.symm (op W) b
  exact (congrArg (fun z => (kernel.ι
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).val.app (op W) z) e).trans hb

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` commutes with restriction. -/
theorem layerIdealIncl_naturality {W W' : Opens X'.carrier} (h : W' ≤ W)
    (x : G.val.obj (op ((Opens.map i.hom.base).obj W))) :
    layerIdealIncl i G kernelIso W' (mres G (opensMap_le i.hom.base h) x) =
      X'.presheaf.map (homOfLE h).op (layerIdealIncl i G kernelIso W x) :=
  PresheafOfModules.naturality_apply (thickeningIdealInclusion i G kernelIso).val (homOfLE h).op x

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` is linear, `𝒪_{X'}` acting on `𝒢` through `i^♯`. -/
theorem layerIdealIncl_smul (W : Opens X'.carrier) (r : X'.presheaf.obj (op W))
    (x : G.val.obj (op ((Opens.map i.hom.base).obj W))) :
    layerIdealIncl i G kernelIso W
        ((show (structureSheafRing X).obj.obj (op ((Opens.map i.hom.base).obj W)) from
          i.hom.c.app (op W) r) • x) = r * layerIdealIncl i G kernelIso W x :=
  ((thickeningIdealInclusion i G kernelIso).val.app (op W)).hom.map_smul r x

/-- The components of the inclusion `𝒢 ⟶ k_*𝒪_{X'}`: a section of `𝒢` over `U` is moved to
`i⁻¹k⁻¹U = U` and sent into `𝒪_{X'}(k⁻¹U)` by the inclusion of the ideal. -/
def thickeningKernelInclusionApp (U : Opens X.carrier) :
    G.val.obj (op U) →+ X'.presheaf.obj (op ((Opens.map (thickeningHomeo i hi).inv).obj U)) where
  toFun m := layerIdealIncl i G kernelIso _ (mres G (thickening_preimage_preimage i hi U).le m)
  map_zero' := by rw [mres_zero, map_zero]
  map_add' a b := by rw [mres_add, map_add]

/-- The components of the inclusion, written out. -/
theorem thickeningKernelInclusionApp_apply (U : Opens X.carrier) (m : G.val.obj (op U)) :
    thickeningKernelInclusionApp i hi G kernelIso U m =
      layerIdealIncl i G kernelIso _ (mres G (thickening_preimage_preimage i hi U).le m) := rfl

/-- The components of the inclusion `𝒢 ⟶ k_*𝒪_{X'}` commute with restriction. -/
theorem thickeningKernelInclusionApp_naturality {U V : Opens X.carrier} (h : V ≤ U)
    (m : G.val.obj (op U)) :
    thickeningKernelInclusionApp i hi G kernelIso V (mres G h m) =
      X'.presheaf.map (homOfLE (opensMap_le (thickeningHomeo i hi).inv h)).op
        (thickeningKernelInclusionApp i hi G kernelIso U m) := by
  rw [thickeningKernelInclusionApp_apply, thickeningKernelInclusionApp_apply,
    ← layerIdealIncl_naturality i G kernelIso (opensMap_le (thickeningHomeo i hi).inv h),
    mres_mres, mres_mres]

/-- The components of the inclusion are killed by `i^♯`. -/
theorem thickeningKernelInclusionApp_comp (U : Opens X.carrier) (m : G.val.obj (op U)) :
    i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U))
      (thickeningKernelInclusionApp i hi G kernelIso U m) = 0 :=
  layerIdealIncl_comp i G kernelIso _ _

/-- The components of the inclusion are linear over `k_*𝒪_{X'}` acting through the
reduction. -/
theorem thickeningKernelInclusionApp_smul (U : Opens X.carrier)
    (r : X'.presheaf.obj (op ((Opens.map (thickeningHomeo i hi).inv).obj U)))
    (m : G.val.obj (op U)) :
    thickeningKernelInclusionApp i hi G kernelIso U
        ((show (structureSheafRing X).obj.obj (op U) from
          (thickeningReduction i hi).hom.app (op U) r) • m) =
      r * thickeningKernelInclusionApp i hi G kernelIso U m := by
  rw [thickeningKernelInclusionApp_apply, thickeningKernelInclusionApp_apply, mres_smul]
  have hr : (structureSheafRing X).obj.map
      (homOfLE (thickening_preimage_preimage i hi U).le).op
      (show (structureSheafRing X).obj.obj (op U) from
        (thickeningReduction i hi).hom.app (op U) r) =
      i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U)) r := by
    refine (presheaf_map_map_eq X.presheaf _ _ (𝟙 _) _).trans ?_
    rw [X.presheaf.map_id]
    rfl
  rw [hr]
  exact layerIdealIncl_smul i G kernelIso _ r _

/-- The components of the inclusion are injective. -/
theorem thickeningKernelInclusionApp_injective (U : Opens X.carrier) :
    Function.Injective (thickeningKernelInclusionApp i hi G kernelIso U) := by
  intro m m' h
  have hU := thickening_preimage_preimage i hi U
  exact mres_injective G hU.le hU.ge (layerIdealIncl_injective i G kernelIso _ h)

/-- The sections of `k_*𝒪_{X'}` killed by `i^♯` are in the image of the components of the
inclusion. -/
theorem exists_thickeningKernelInclusionApp (U : Opens X.carrier)
    (a : X'.presheaf.obj (op ((Opens.map (thickeningHomeo i hi).inv).obj U)))
    (ha : i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U)) a = 0) :
    ∃ m, thickeningKernelInclusionApp i hi G kernelIso U m = a := by
  have hU := thickening_preimage_preimage i hi U
  obtain ⟨x, hx⟩ := exists_idealIncl i G kernelIso _ a ha
  refine ⟨mres G hU.ge x, ?_⟩
  rwa [thickeningKernelInclusionApp_apply, mres_mres, mres_self]

/-- **The inclusion `𝒢 ⟶ k_*𝒪_{X'}` of the module identified with the ideal**, on the reduced
space, with components `thickeningKernelInclusionApp`. It is linear over `k_*𝒪_{X'}` acting on
`𝒢` through the reduction. -/
def thickeningKernelInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X.carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (thickeningReduction i hi))).obj G ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (thickenedRing i hi)) where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (thickeningKernelInclusionApp i hi G kernelIso U.unop)
      naturality := fun U V g => by
        ext m
        exact thickeningKernelInclusionApp_naturality i hi G kernelIso g.unop.le m }
    (fun U r m => thickeningKernelInclusionApp_smul i hi G kernelIso U.unop r m)

/-- The inclusion of the module identified with the ideal, on sections. -/
theorem thickeningKernelInclusion_apply (U : Opens X.carrier) (m : G.val.obj (op U)) :
    (thickeningKernelInclusion i hi G kernelIso).val.app (op U) m =
      thickeningKernelInclusionApp i hi G kernelIso U m := rfl

/-- The reduction kills the image of the inclusion of the module identified with the ideal. -/
theorem thickeningKernelZero (U : (Opens X.carrier)ᵒᵖ) (m : G.val.obj U) :
    (thickeningReduction i hi).hom.app U
      (show (thickenedRing i hi).obj.obj U from
        (thickeningKernelInclusion i hi G kernelIso).val.app U m) = 0 := by
  obtain ⟨U⟩ := U
  change X.presheaf.map _ (i.hom.c.app _ (thickeningKernelInclusionApp i hi G kernelIso U m)) = 0
  rw [thickeningKernelInclusionApp_comp, map_zero]

/-- **The inclusion identifies the module with the kernel of the reduction, section by
section.** -/
theorem thickeningKernelUniversal (U : (Opens X.carrier)ᵒᵖ) (a : (thickenedRing i hi).obj.obj U)
    (ha : (thickeningReduction i hi).hom.app U a = 0) :
    ∃! m : G.val.obj U,
      (show (thickenedRing i hi).obj.obj U from
        (thickeningKernelInclusion i hi G kernelIso).val.app U m) = a := by
  obtain ⟨U⟩ := U
  have hU := thickening_preimage_preimage i hi U
  have ha' : i.hom.c.app (op ((Opens.map (thickeningHomeo i hi).inv).obj U)) a = 0 := by
    apply presheaf_map_homOfLE_injective X.presheaf hU.ge hU.le
    rwa [map_zero]
  obtain ⟨m, hm⟩ := exists_thickeningKernelInclusionApp i hi G kernelIso U a ha'
  exact ⟨m, hm, fun m' hm' => thickeningKernelInclusionApp_injective i hi G kernelIso U
    (hm'.trans hm.symm)⟩

end Kernel

section CompC

/-- **Equal composites of morphisms of ringed spaces have equal comorphisms on sections**, up to
restriction to a common open. -/
theorem comp_c_congr {A B B' C : RingedSpace.{u, u}} {α : A ⟶ B} {β : B ⟶ C} {γ : A ⟶ B'}
    {δ : B' ⟶ C} (h : α ≫ β = γ ≫ δ) (W : Opens C.carrier) {V : Opens A.carrier}
    (g₁ : op ((Opens.map α.hom.base).obj ((Opens.map β.hom.base).obj W)) ⟶ op V)
    (g₂ : op ((Opens.map γ.hom.base).obj ((Opens.map δ.hom.base).obj W)) ⟶ op V)
    (a : C.presheaf.obj (op W)) :
    A.presheaf.map g₁ (α.hom.c.app _ (β.hom.c.app (op W) a)) =
      A.presheaf.map g₂ (γ.hom.c.app _ (δ.hom.c.app (op W) a)) := by
  have e := congrArg (fun k => k a) (SheafedSpace.congr_hom_app h (op W))
  exact (congrArg (A.presheaf.map g₁) e).trans (presheaf_map_map_eq A.presheaf _ _ g₂ _)

end CompC

section StructureMap

variable {X S : RingedSpace.{u, u}} (f : X ⟶ S)

/-- The comorphism `𝒪_S ⟶ f_*𝒪_X` of a morphism of ringed spaces, as a morphism of sheaves on the
site of opens. -/
abbrev comorphism : ringOf S ⟶ (ringPushforward f.hom.base).obj (ringOf X) :=
  ObjectProperty.homMk f.hom.c

/-- The structure map `f⁻¹𝒪_S ⟶ 𝒪_X` of a morphism of ringed spaces,
`Stacks.SheafOfModules.ringedSpaceStructureMap`, with its type spelled on the site of opens. -/
abbrev structureMap : (ringPullback f.hom.base).obj (ringOf S) ⟶ ringOf X :=
  Stacks.SheafOfModules.ringedSpaceStructureMap f

/-- The structure map is the adjoint transpose of the comorphism. -/
theorem homEquiv_structureMap :
    (ringAdjunction f.hom.base).homEquiv _ _ (structureMap f) = comorphism f :=
  Equiv.apply_symm_apply _ _

end StructureMap

section Layer

variable {X X' S S' : RingedSpace.{u, u}} (i : X ⟶ X') (t : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
  (comm : i ≫ f' = f ≫ t)

/-- The thickening composed with the inverse homeomorphism, on points. -/
theorem thickeningHomeo_inv_hom_apply (hi : IsThickening i) (z : X'.carrier) :
    i.hom.base ((thickeningHomeo i hi).inv z) = z :=
  ConcreteCategory.congr_hom (thickeningHomeo i hi).inv_hom_id z

/-- The inverse homeomorphism composed with the thickening, on points. -/
theorem thickeningHomeo_hom_inv_apply (hi : IsThickening i) (x : X.carrier) :
    (thickeningHomeo i hi).inv (i.hom.base x) = x :=
  ConcreteCategory.congr_hom (thickeningHomeo i hi).hom_inv_id x

include comm in
/-- The square of thickenings on points: `f' ∘ i = t ∘ f`. -/
theorem thickening_comm_apply (x : X.carrier) :
    f'.hom.base (i.hom.base x) = t.hom.base (f.hom.base x) :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.hom.base) comm) x

include comm in
/-- The opens over which the structure map of a layer is defined. -/
theorem thickening_structure_le (hi : IsThickening i) (ht : IsThickening t) (V : Opens S.carrier) :
    (Opens.map (thickeningHomeo i hi).inv).obj ((Opens.map f.hom.base).obj V) ≤
      (Opens.map f'.hom.base).obj ((Opens.map (thickeningHomeo t ht).inv).obj V) := by
  intro z hz
  have h1 : f'.hom.base z = t.hom.base (f.hom.base ((thickeningHomeo i hi).inv z)) := by
    conv_lhs => rw [← thickeningHomeo_inv_hom_apply i hi z]
    exact thickening_comm_apply i t f f' comm _
  change (thickeningHomeo t ht).inv (f'.hom.base z) ∈ V
  rw [h1, thickeningHomeo_hom_inv_apply]
  exact hz

/-- **The structure map of the thickened square, read on the reduced spaces**:
`k_*𝒪_{S'} ⟶ f_*k_*𝒪_{X'}`, the comorphism of `f'` on `k⁻¹V` followed by restriction to the
equal open `k⁻¹f⁻¹V`. -/
def thickeningStructure (hi : IsThickening i) (ht : IsThickening t) :
    thickenedRing t ht ⟶ (ringPushforward f.hom.base).obj (thickenedRing i hi) :=
  ObjectProperty.homMk
    { app := fun V => f'.hom.c.app (op ((Opens.map (thickeningHomeo t ht).inv).obj V.unop)) ≫
        X'.presheaf.map (homOfLE (thickening_structure_le i t f f' comm hi ht V.unop)).op
      naturality := fun U V g => by
        change S'.presheaf.map _ ≫ f'.hom.c.app _ ≫ X'.presheaf.map _ =
          (f'.hom.c.app _ ≫ X'.presheaf.map _) ≫ X'.presheaf.map _
        rw [← Category.assoc, f'.hom.c.naturality, Category.assoc, Category.assoc]
        change f'.hom.c.app _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _ =
          f'.hom.c.app _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _
        rw [← X'.presheaf.map_comp, ← X'.presheaf.map_comp]
        rfl }

/-- The structure map of the thickened square on sections. -/
theorem thickeningStructure_apply (hi : IsThickening i) (ht : IsThickening t) (V : Opens S.carrier)
    (a : S'.presheaf.obj (op ((Opens.map (thickeningHomeo t ht).inv).obj V))) :
    (thickeningStructure i t f f' comm hi ht).hom.app (op V) a =
      X'.presheaf.map (homOfLE (thickening_structure_le i t f f' comm hi ht V)).op
        (f'.hom.c.app (op ((Opens.map (thickeningHomeo t ht).inv).obj V)) a) := rfl

/-- The reduced structure map read on the thickened base: the adjoint transpose of
`thickeningStructure`, a morphism `f⁻¹k_*𝒪_{S'} ⟶ k_*𝒪_{X'}` of sheaves of rings on `X`. -/
def thickeningStructureMap (hi : IsThickening i) (ht : IsThickening t) :
    (ringPullback f.hom.base).obj (thickenedRing t ht) ⟶ thickenedRing i hi :=
  ((ringAdjunction f.hom.base).homEquiv _ _).symm (thickeningStructure i t f f' comm hi ht)

/-- The two reductions of the square of a layer commute with the structure maps. -/
theorem thickeningStructure_comp_reduction (hi : IsThickening i) (ht : IsThickening t) :
    thickeningStructure i t f f' comm hi ht ≫
        (ringPushforward f.hom.base).map (thickeningReduction i hi) =
      thickeningReduction t ht ≫ comorphism f := by
  refine sheafHom_ext _ fun V a => ?_
  obtain ⟨V⟩ := V
  change X.presheaf.map _ (i.hom.c.app _ (X'.presheaf.map _ (f'.hom.c.app _ a))) =
    f.hom.c.app _ (S.presheaf.map _ (t.hom.c.app _ a))
  rw [c_app_map_apply i, c_app_map_apply f]
  exact (presheaf_map_map_apply X.presheaf _ _ _).trans (comp_c_congr comm _ _ _ a)

include comm in
/-- The square of a layer commutes. -/
theorem thickeningLayer_comm (hi : IsThickening i) (ht : IsThickening t) :
    thickeningStructureMap i t f f' comm hi ht ≫ thickeningReduction i hi =
      (ringPullback f.hom.base).map (thickeningReduction t ht) ≫ structureMap f := by
  apply ((ringAdjunction f.hom.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    thickeningStructureMap, Equiv.apply_symm_apply, homEquiv_structureMap]
  exact thickeningStructure_comp_reduction i t f f' comm hi ht

variable (hi : IsFirstOrderThickening i) (ht : IsFirstOrderThickening t)
  (G : SheafOfModules.{u} (structureSheafRing X))
  (kernelIso : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅ (modulePushforward i).obj G)

/-- **One layer of the diagram of Stacks 08U8 on the reduced space.** For a commutative square
`i ≫ f' = f ≫ t` of ringed spaces whose rows are first order thickenings, and a module `𝒢` on
`X` identified with the ideal of `i`: the base is `f⁻¹𝒪_S` thickened to `f⁻¹k_*𝒪_{S'}`, the
source is `𝒪_X` thickened to `k_*𝒪_{X'}`, the structure maps are those of `f` and `f'`, and the
ideal module is `𝒢`. -/
def thickeningLayer : LiftSquare.{u, u, u} (Opens.grothendieckTopology X.carrier) where
  OB := Stacks.SheafOfModules.inverseImageMiddleRing f
  OB' := (ringPullback f.hom.base).obj (thickenedRing t ht.isThickening)
  O := ringOf X
  O' := thickenedRing i hi.isThickening
  baseReduction := (ringPullback f.hom.base).map (thickeningReduction t ht.isThickening)
  reduction := thickeningReduction i hi.isThickening
  f := structureMap f
  f' := thickeningStructureMap i t f f' comm hi.isThickening ht.isThickening
  comm := thickeningLayer_comm i t f f' comm hi.isThickening ht.isThickening
  baseLocallySurjective := isLocallySurjective_inverseImage_map f.hom.base _ _
    (thickeningReduction_isLocallySurjective t ht.isThickening)
  baseSquareZero := ker_pow_two_inverseImage f.hom.base _ _ (thickeningReduction_squareZero t ht)
  locallySurjective := thickeningReduction_isLocallySurjective i hi.isThickening
  squareZero := thickeningReduction_squareZero i hi
  G := G
  kernelInclusion := thickeningKernelInclusion i hi.isThickening G kernelIso
  kernelZero := thickeningKernelZero i hi.isThickening G kernelIso
  kernelUniversal := thickeningKernelUniversal i hi.isThickening G kernelIso

end Layer

end AlgebraicGeometry.RingedSpaceThickening

end
