module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge

/-!
# The pulled-back ideal of a square-zero base is the coefficient sheaf `𝒪_X ⊗_k M`

Let `X` be a scheme over a field `k`, `M` a finite-dimensional `k`-vector space and
`k[M] = k ⊕ M` the square-zero object of `𝒞_Λ` it defines. The module of the deformation problem
of Stacks 08U7 attached to deformations of `X` over `k[M]` is `f^* 𝒥`, the pullback along the
structure morphism `f : X ⟶ Spec k` of the ideal `𝒥` of the closed point of `Spec k[M]`
(`Deformation.Examples.SchemeDeformationCategory.pulledIdeal`). This file identifies it with the
coefficient sheaf `𝒪_X ⊗_k M = f^* M^~` in which the obstruction of Stacks 0E3V lives, and
computes the identification on the sections it is built from: a global function `s` of
`Spec k[M]` with value `(0, m)` goes to the global section `1 ⊗ m`.

The ideal of the closed point of the one-point space `Spec k[M]` is read off its global
sections, which are the elements of `k[M]` with vanishing first coordinate, i.e. `M`.

## Main definitions

* `Deformation.Examples.squareZeroIdealSheafIso`: the ideal of the closed point of `Spec k[M]` is
  the pushforward of `M^~`.
* `Deformation.Examples.pulledIdealCoefficientIso`: `f^* 𝒥 ≅ f^* M^~`.

## Main results

* `Deformation.Examples.pulledIdealCoefficientIso_hom_prescribedIdealSection`: the identification
  sends the section `s` with `s = (0, m)` to `1 ⊗ m`.
* `Deformation.Examples.coefficientSheaf_hom_ext`: a morphism out of `f^* M^~` is determined by
  its values on the sections `1 ⊗ m`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

/-- The spectrum of a field is a single point. -/
instance subsingleton_specField (k : Type u) [Field k] : Subsingleton (Spec (CommRingCat.of k)) :=
  Ring.KrullDimLE.subsingleton_primeSpectrum k

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Maps out of `𝒪_X ⊗_k M` -/

/-- Every global section of `M^~` on `Spec k` is the section given by a vector of `M`. -/
theorem exists_tildeTopSection_eq (M : FGModuleCat.{u} k)
    (x : (tilde (R := CommRingCat.of k) M.obj).val.obj (op ⊤)) :
    ∃ m : M, tildeTopSection M m = x :=
  (tilde.isoTop (R := CommRingCat.of k) M.obj).toLinearEquiv.surjective x

/-- **A morphism out of `𝒪_X ⊗_k M` is determined by its values on the sections `1 ⊗ m`.** Its
adjoint `M^~ ⟶ f_* 𝒢` lives on the one-point space `Spec k`, where it is determined by its value
on global sections, and the global sections of `M^~` are the vectors of `M`. -/
theorem coefficientSheaf_hom_ext {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    (M : FGModuleCat.{u} k) {F : X.Modules}
    {φ ψ : (Scheme.Modules.pullback p).obj (tilde M.obj) ⟶ F}
    (h : ∀ m : M, (φ.val.app (op ⊤)).hom (coefficientSheafSection p M m) =
      (ψ.val.app (op ⊤)).hom (coefficientSheafSection p M m)) : φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine moduleHom_ext_top ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨m, rfl⟩ := exists_tildeTopSection_eq M x
  exact h m

/-! ### The ideal of the closed point of `Spec k[M]` -/

section Ideal

variable (M : FGModuleCat.{u} k)

/-- The second coordinate, in `M`, of a global function on `Spec k[M]`. -/
def squareZeroCoordinate
    (s : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤)) :
    M :=
  TrivSqZeroExt.snd (R := k) (M := M) ((Scheme.ΓSpecIso
    (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom s)

/-- The comorphism of the closed point of `Spec k[M]` on global sections, read through
`Γ(Spec -)`, is the residue map. -/
private theorem ΓSpecIso_hom_residueSpecMap_app_top
    (c : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤)) :
    (Scheme.ΓSpecIso (.of k)).hom.hom
        (((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom c) =
      Deformation.Artin.residueMap _ ((Scheme.ΓSpecIso _).hom.hom c) :=
  congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (Deformation.Artin.residueMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))))

/-- A global function on `Spec k[M]` vanishing at the closed point has vanishing first
coordinate. -/
theorem squareZero_fst_eq_zero
    (s : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤))
    (hs : (((residueSpecMap
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom s) = 0) :
    TrivSqZeroExt.fst (R := k) (M := M)
      ((Scheme.ΓSpecIso
        (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom s) = 0 := by
  exact (ΓSpecIso_hom_residueSpecMap_app_top M s).symm.trans
    ((congrArg (fun y => (Scheme.ΓSpecIso (.of k)).hom.hom y) hs).trans
    (map_zero _))

/-- The global function on `Spec k[M]` underlying a global section of the ideal sheaf of the
closed point. -/
abbrev squareZeroIdealFunction
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).val.obj
        (op ⊤)) :
    (structureSheafRing (baseSpec
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toRingedSpace).obj.obj (op ⊤) :=
  ((Stacks.ClosedImmersion.idealSheafι
    (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).val.app
      (op ⊤)).hom y

/-- A global section of the ideal sheaf of the closed point vanishes at the closed point. -/
theorem squareZeroIdealFunction_app_eq_zero
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).val.obj
        (op ⊤)) :
    ((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom
      (squareZeroIdealFunction M y) = 0 :=
  congrArg (fun φ => (φ.val.app (op ⊤)).hom y)
    (kernel.condition (RingedSpaceModuleAdjunction.structureSheafModuleHom
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom))

/-- The comorphism of the closed point of `Spec k[M]` on global sections is the first
coordinate. -/
theorem residueSpecMap_app_top_eq
    (c : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤)) :
    ((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom c =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (TrivSqZeroExt.fst (R := k) (M := M)
        ((Scheme.ΓSpecIso
          (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom c)) := by
  exact ((congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom z)
    (ΓSpecIso_hom_residueSpecMap_app_top M c)).symm.trans
    (congrArg (fun φ => φ.hom
      (((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom c))
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id)).symm

/-- `M^~` on `Spec k`, as a sheaf of modules over the structure sheaf of the underlying ringed
space. -/
abbrev tildeSheaf :
    SheafOfModules.{u} (structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace) :=
  tilde (R := CommRingCat.of k) M.obj

/-- A scalar of `k`, read as a global function on `Spec k`. -/
abbrev specFieldScalar (r : k) : (Spec (CommRingCat.of k)).ringCatSheaf.obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r

/-- The scalar action of `k` on the global sections of `M^~` is the action of the global
functions of `Spec k`. -/
theorem smul_tildeTopSection (r : k) (m : M) :
    tildeTopSection M (r • m) = specFieldScalar r • tildeTopSection M m := by
  have h2 : ((Spec (CommRingCat.of k)).presheaf.map
      (⊤ : (Spec (CommRingCat.of k)).Opens).leTop.op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r := by
    rw [show (⊤ : (Spec (CommRingCat.of k)).Opens).leTop.op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have h3 := Scheme.Modules.smul_Spec_def (R := CommRingCat.of k) (M := tilde M.obj) (U := ⊤) r
    ((tilde.toOpen (R := CommRingCat.of k) M.obj ⊤).hom m)
  rw [h2] at h3
  exact ((tilde.toOpen (R := CommRingCat.of k) M.obj ⊤).hom.map_smul r m).trans h3

/-- **The ideal of the closed point of `Spec k[M]` on global sections**: a global function
vanishing at the closed point is `(0, m)`, and goes to the global section of `M^~` given by
`m`. -/
def squareZeroIdealTop :
    (SheafOfModules.evaluation _ (op ⊤)).obj (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom) ⟶
      (SheafOfModules.evaluation _ (op ⊤)).obj ((modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj
          (tilde M.obj)) :=
  letI : Module kᵐᵒᵖ M :=
    Module.compHom M {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let L : (SheafOfModules.evaluation _ (op ⊤)).obj (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom) →ₗ[_]
      (SheafOfModules.evaluation _ (op ⊤)).obj ((modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj
          (tildeSheaf M)) :=
    { toFun := fun y => tildeTopSection M (squareZeroCoordinate M (squareZeroIdealFunction M y))
      map_add' := fun y y' => by
        have h1 : squareZeroIdealFunction M (y + y') =
            squareZeroIdealFunction M y + squareZeroIdealFunction M y' := map_add _ y y'
        rw [h1, squareZeroCoordinate, map_add]
        exact tildeTopSection_add M _ _
      map_smul' := fun c y => by
        have h0 := squareZero_fst_eq_zero M _ (squareZeroIdealFunction_app_eq_zero M y)
        have h1 : squareZeroIdealFunction M (c • y) = c * squareZeroIdealFunction M y :=
          map_smul _ c y
        have hm : (Scheme.ΓSpecIso (CommRingCat.of
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom
              (c * squareZeroIdealFunction M y) =
            (Scheme.ΓSpecIso (CommRingCat.of
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom c *
            (Scheme.ΓSpecIso (CommRingCat.of
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom
                (squareZeroIdealFunction M y) := map_mul _ c _
        have h2 : squareZeroCoordinate M (squareZeroIdealFunction M (c • y)) =
            TrivSqZeroExt.fst (R := k) (M := M) ((Scheme.ΓSpecIso (CommRingCat.of
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom c) •
              squareZeroCoordinate M (squareZeroIdealFunction M y) := by
          rw [h1, squareZeroCoordinate, hm]
          refine (TrivSqZeroExt.snd_mul _ _).trans ?_
          rw [h0]
          simp only [MulOpposite.op_zero, zero_smul, add_zero]
          rfl
        refine (congrArg (tildeTopSection M) h2).trans ?_
        refine (smul_tildeTopSection M _ _).trans ?_
        exact congrArg (fun z => z • tildeTopSection M (squareZeroCoordinate M
          (squareZeroIdealFunction M y))) (residueSpecMap_app_top_eq M c).symm }
  ModuleCat.ofHom (X := ↑((SheafOfModules.evaluation _ (op ⊤)).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom)))
    (Y := ↑((SheafOfModules.evaluation _ (op ⊤)).obj ((modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj
          (tildeSheaf M)))) L

/-- `squareZeroIdealTop` on a section. -/
theorem squareZeroIdealTop_apply
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).val.obj
        (op ⊤)) :
    (squareZeroIdealTop (Λ := Λ) M).hom y =
      tildeTopSection M (squareZeroCoordinate M (squareZeroIdealFunction M y)) :=
  rfl

/-- The global sections of the ideal of the closed point of `Spec k[M]` are the vectors of
`M`: `squareZeroIdealTop` is bijective. -/
theorem squareZeroIdealTop_bijective : Function.Bijective (squareZeroIdealTop (Λ := Λ) M).hom := by
  refine ⟨fun y y' h => ?_, fun x => ?_⟩
  · have hΓ : (Scheme.ΓSpecIso (CommRingCat.of
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom
          (squareZeroIdealFunction M y) =
        (Scheme.ΓSpecIso (CommRingCat.of
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom
            (squareZeroIdealFunction M y') :=
      TrivSqZeroExt.ext
        ((squareZero_fst_eq_zero M _ (squareZeroIdealFunction_app_eq_zero M y)).trans
          (squareZero_fst_eq_zero M _ (squareZeroIdealFunction_app_eq_zero M y')).symm)
        ((tilde.isoTop (R := CommRingCat.of k) M.obj).toLinearEquiv.injective h)
    exact Stacks.ClosedImmersion.injective_idealSheafι_val_app _ ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).commRingCatIsoToRingEquiv.injective
          hΓ)
  · obtain ⟨m, rfl⟩ := exists_tildeTopSection_eq M x
    let a : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).inv.hom
          (TrivSqZeroExt.inr (R := k) (M := M) m)
    have hΓa : (Scheme.ΓSpecIso (CommRingCat.of
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom a = TrivSqZeroExt.inr m :=
      congrArg (fun φ => φ.hom (TrivSqZeroExt.inr (R := k) (M := M) m))
        (Scheme.ΓSpecIso (CommRingCat.of
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).inv_hom_id
    have hta : ((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app ⊤).hom a
        = 0 := by
      rw [residueSpecMap_app_top_eq, hΓa]
      exact map_zero (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    obtain ⟨y, hy⟩ := Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom ⊤ a hta
    refine ⟨y, ?_⟩
    rw [squareZeroIdealTop_apply]
    have hy' : squareZeroIdealFunction M y = a := hy
    rw [squareZeroCoordinate, hy', hΓa]
    rfl

/-- The global sections of the ideal of the closed point of `Spec k[M]` are `M`. -/
def squareZeroIdealTopIso :
    (SheafOfModules.evaluation _ (op ⊤)).obj (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom) ≅
      (SheafOfModules.evaluation _ (op ⊤)).obj ((modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj
          (tildeSheaf M)) :=
  (LinearEquiv.ofBijective (squareZeroIdealTop (Λ := Λ) M).hom
    (squareZeroIdealTop_bijective M)).toModuleIso

/-- **The ideal of the closed point of `Spec k[M]` is the pushforward of `M^~`.** The spectrum of
`k[M]` is a single point, where a sheaf of modules is its module of global sections, and the
global sections of the ideal are the functions `(0, m)`, which are the vectors of `M`. -/
def squareZeroIdealSheafIso :
    AlgebraicGeometry.SheafOfModules.idealSheaf
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom ≅
      (modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj (tildeSheaf M) :=
  moduleIsoOfTop (squareZeroIdealTopIso (Λ := Λ) M)

/-- `squareZeroIdealSheafIso` on global sections. -/
theorem squareZeroIdealSheafIso_hom_app_top
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).val.obj
        (op ⊤)) :
    ((squareZeroIdealSheafIso (Λ := Λ) M).hom.val.app (op ⊤)).hom y =
      tildeTopSection M (squareZeroCoordinate M (squareZeroIdealFunction M y)) :=
  congrArg (fun φ => φ.hom y) (moduleHomOfTop_apply
    (M := AlgebraicGeometry.SheafOfModules.idealSheaf
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom)
    (N := (modulePushforward (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).obj (tildeSheaf M))
    (R := structureSheafRing
      (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toRingedSpace)
    (squareZeroIdealTopIso (Λ := Λ) M).hom)

/-- **The conormal sheaf of the closed point of `Spec k[M]` is `M^~`.** -/
def squareZeroConormalIso :
    Stacks.Thickenings.schemeConormalSheaf
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) ≅ tildeSheaf M :=
  haveI := residueSpecMap_isClosedImmersion ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
  conormalIsoOfIdealSheafIso (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    ((residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).app_surjective ⊤
      (isAffineOpen_top _)) (squareZeroIdealSheafIso (Λ := Λ) M)

/-- The conormal identification is the pullback of the ideal identification followed by the
counit, so its transpose is the ideal identification. -/
theorem homEquiv_squareZeroConormalIso_hom :
    (modulePullbackPushforwardAdjunction (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).homEquiv _ _
        (squareZeroConormalIso (Λ := Λ) M).hom = (squareZeroIdealSheafIso (Λ := Λ) M).hom := by
  show (modulePullbackPushforwardAdjunction _).homEquiv _ _
    ((modulePullback _).map (squareZeroIdealSheafIso (Λ := Λ) M).hom ≫
      (modulePullbackPushforwardAdjunction _).counit.app _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, Category.comp_id]

end Ideal

/-! ### The pulled-back ideal -/

section Pulled

variable (M : FGModuleCat.{u} k) (X : Over (Spec (CommRingCat.of k)))

/-- **The pulled-back ideal of the square-zero base `k[M]` is the coefficient sheaf
`𝒪_X ⊗_k M`**: the pullback along the structure morphism of `X` of the identification of the
conormal sheaf of the closed point of `Spec k[M]` with `M^~`. -/
def pulledIdealCoefficientIso :
    SchemeDeformationCategory.pulledIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) X ≅
      (modulePullback X.hom.toLRSHom.toShHom).obj (tildeSheaf M) :=
  (modulePullback X.hom.toLRSHom.toShHom).mapIso (squareZeroConormalIso (Λ := Λ) M)

/-- **The transpose of `(f ∘ t)^* ≅ t^* ⋙ f^*`** is the composite of the two units. -/
theorem homEquiv_modulePullbackCompUniq_hom_app {X' Y' Z' : RingedSpace.{u, u}} (f : X' ⟶ Y')
    (g : Y' ⟶ Z') (N : SheafOfModules.{u} (structureSheafRing Z')) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        ((modulePullbackCompUniq f g).hom.app N ≫ 𝟙 _) =
      (modulePullbackPushforwardAdjunction g).unit.app N ≫
        (modulePushforward g).map ((modulePullbackPushforwardAdjunction f).unit.app _) ≫
        (modulePushforwardCompSymm f g).inv.app _ := by
  rw [Category.comp_id, modulePullbackCompUniq, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

/-- **The pulled-back identification on the sections it is built from**: the section of `f^* 𝒥`
given by a global function `s = (0, m)` of `Spec k[M]` goes to the global section `1 ⊗ m` of
`f^* M^~`. -/
theorem pulledIdealCoefficientIso_hom_prescribedIdealSection
    (s : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤))
    (hs : ((residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom.hom.c.app
      (op ⊤)).hom s = 0) (m : M)
    (hsm : (Scheme.ΓSpecIso
        (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom s =
      TrivSqZeroExt.inr (R := k) (M := M) m) :
    ((pulledIdealCoefficientIso (Λ := Λ) M X).hom.val.app _).hom
        (prescribedIdealSection (f := X.hom.toLRSHom.toShHom) (𝟙 _) (op ⊤) s hs) =
      coefficientSheafSection X.hom M m := by
  have h1 := congrArg (fun φ => (φ.val.app (op ⊤)).hom (baseIdealSection
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (op ⊤) s hs))
    (homEquiv_modulePullbackCompUniq_hom_app X.hom.toLRSHom.toShHom
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (AlgebraicGeometry.SheafOfModules.idealSheaf
        (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom))
  refine (congrArg ((pulledIdealCoefficientIso (Λ := Λ) M X).hom.val.app _).hom h1).trans ?_
  have h3 := congrArg (fun φ => (φ.val.app (op ⊤)).hom (baseIdealSection
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (op ⊤) s hs)) (homEquiv_squareZeroConormalIso_hom (Λ := Λ) M)
  rw [Adjunction.homEquiv_unit] at h3
  have h2 := congrArg (fun φ => (φ.val.app (op ⊤)).hom
      ((((modulePullbackPushforwardAdjunction (residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom).unit.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf (residueSpecMap
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom)).val.app
            (op ⊤)).hom
        (baseIdealSection
          (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
          (op ⊤) s hs)))
    ((modulePullbackPushforwardAdjunction X.hom.toLRSHom.toShHom).unit.naturality
      (squareZeroConormalIso (Λ := Λ) M).hom)
  refine h2.symm.trans ?_
  refine (congrArg (((modulePullbackPushforwardAdjunction X.hom.toLRSHom.toShHom).unit.app
    (tildeSheaf M)).val.app (op ⊤)).hom h3).trans ?_
  rw [squareZeroIdealSheafIso_hom_app_top]
  have hι : squareZeroIdealFunction M (baseIdealSection
      (residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom
      (op ⊤) s hs) = s :=
    idealSheafι_baseIdealSection _ (op ⊤) s hs
  rw [hι, squareZeroCoordinate, hsm]
  rfl

/-- **The inverse of the pulled-back identification on the sections `1 ⊗ m`**: the global section
`1 ⊗ m` of `f^* M^~` goes to the section of `f^* 𝒥` given by the function `(0, m)`. -/
theorem pulledIdealCoefficientIso_inv_coefficientSheafSection
    (s : (baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).presheaf.obj (op ⊤))
    (hs : ((residueSpecMap
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).toLRSHom.toShHom.hom.c.app
      (op ⊤)).hom s = 0) (m : M)
    (hsm : (Scheme.ΓSpecIso
        (CommRingCat.of ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))).hom.hom s =
      TrivSqZeroExt.inr (R := k) (M := M) m) :
    ((pulledIdealCoefficientIso (Λ := Λ) M X).inv.val.app _).hom
        (coefficientSheafSection X.hom M m) =
      prescribedIdealSection (f := X.hom.toLRSHom.toShHom) (𝟙 _) (op ⊤) s hs := by
  rw [← pulledIdealCoefficientIso_hom_prescribedIdealSection M X s hs m hsm]
  exact congrArg (fun φ => (φ.val.app _).hom
    (prescribedIdealSection (f := X.hom.toLRSHom.toShHom) (𝟙 _) (op ⊤) s hs))
    (pulledIdealCoefficientIso (Λ := Λ) M X).hom_inv_id

end Pulled


end Deformation.Examples
