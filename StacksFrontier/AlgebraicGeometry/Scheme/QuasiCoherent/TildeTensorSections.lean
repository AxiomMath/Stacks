module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison

/-!
# Global sections of a tensor product of quasi-coherent modules on `Spec R`

`StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison` proves the tensor half
of Stacks 01I8 as a statement about *sheaves*: the comparison morphism
`(M ⊗_R N)~ ⟶ M̃ ⊗_{𝒪_{Spec R}} Ñ` is an isomorphism.  This file reads that statement on *global
sections*, which is the form the affine criterion
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` and the reduction
`Stacks.ProjectionFormula.isIso_projectionFormulaMap_iff_isIso_moduleSpecΓ` consume.

The statement is proved for arbitrary quasi-coherent `F` and `G`, not only for associated sheaves:
the canonical map `Γ(Spec R, F) ⊗_R Γ(Spec R, G) ⟶ Γ(Spec R, F ⊗ G)` is bijective.  The route is
the associated-sheaf case, which is `TildeTensorComparison`'s theorem transported along
`AlgebraicGeometry.tilde.isoTop`, together with naturality and the fact that a quasi-coherent
module is isomorphic to the associated sheaf of its own global sections
(`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`).

## Main definitions

* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMapIso`: the tensor product of two
  isomorphisms of sheaves of modules on a ringed space, as an isomorphism.
* `AlgebraicGeometry.TildeTensor.gammaTensorMap`: the canonical `R`-linear map
  `Γ(Spec R, F) ⊗_R Γ(Spec R, G) ⟶ Γ(Spec R, F ⊗ G)`, sending `s ⊗ t` to the image of `s ⊗ t`
  under `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`.
* `AlgebraicGeometry.TildeTensor.tildeTensorΓIso`: `M ⊗_R N ≅ Γ(Spec R, M̃ ⊗ Ñ)`.
* `AlgebraicGeometry.TildeTensor.gammaTensorEquiv`: the same for quasi-coherent `F` and `G`.

## Main results

* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf_hom_ext`: a morphism out of a tensor
  product of sheaves of modules is determined by its effect on the images of pure tensors of
  sections.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_id` and
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_comp`: functoriality of
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`.  Both are proved `private`
  elsewhere in this repository --- see the implementation notes --- so neither copy could be used
  and they are proved again here.
* `AlgebraicGeometry.TildeTensor.tildeTensorΓIso_hom_apply`: the isomorphism
  `M ⊗_R N ≅ Γ(Spec R, M̃ ⊗ Ñ)` is `topTensorMap`.
* `AlgebraicGeometry.TildeTensor.gammaTensorMap_naturality`: naturality of the canonical map, which
  is naturality of the sheafification unit.
* `AlgebraicGeometry.TildeTensor.bijective_gammaTensorMap`: **the tensor half of Stacks 01I8 on
  global sections** --- the canonical map is bijective for quasi-coherent `F` and `G`.

## Implementation notes

The category of sheaves of modules on `Spec R` has two spellings in play --- `(Spec R).Modules`,
which Mathlib's `tilde` machinery and `moduleSpecΓFunctor` are indexed by, and
`SheafOfModules (structureSheafRing (Spec R).toRingedSpace)`, which
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` is indexed by.  The two `Category`
instances are equal but not syntactically equal.  Terms, morphisms and isomorphisms cross
freely, so `modSheaf` and `modTensor` do the retyping once each on bare variables; *instance
search* does not cross, which is why `isIso_specModules` exists rather than an `IsIso` being
found.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

universe u

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- `tensorSheafMap` takes the identity pair to the identity. -/
lemma tensorSheafMap_id (F G : SheafOfModules.{u} (structureSheafRing X)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map ((𝟙 F, 𝟙 G) : (F, G) ⟶ (F, G)) =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩)).map_id (F, G)

/-- The tensor product of two isomorphisms of sheaves of modules. -/
def tensorSheafMapIso {F F' G G' : SheafOfModules.{u} (structureSheafRing X)}
    (e : F ≅ F') (d : G ≅ G') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).obj (F, G) ≅
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).obj (F', G') :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩)).mapIso (Iso.prod e d)

/-- **The tensor product of two isomorphisms is an isomorphism.** -/
instance isIso_tensorSheafMap {F F' G G' : SheafOfModules.{u} (structureSheafRing X)}
    (φ : F ⟶ F') (ψ : G ⟶ G') [IsIso φ] [IsIso ψ] :
    IsIso ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map ((φ, ψ) : (F, G) ⟶ (F', G'))) :=
  (tensorSheafMapIso (asIso φ) (asIso ψ)).isIso_hom

/-- `toTensorSheafSection` is additive. -/
lemma toTensorSheafSection_add (X) (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (t t' : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    toTensorSheafSection X F G U (t + t')
      = toTensorSheafSection X F G U t + toTensorSheafSection X F G U t' :=
  map_add ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom t t'

/-- `toTensorSheafSection` is `𝒪_X(U)`-linear.  The scalar acting on the right is ascribed at
`(Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj U`, which is
`X.presheaf.obj U` by one iota step; the module structure on the sections of a `sheafTensor`
object is the one carried by that spelling, and instance search does not cross the
difference. -/
lemma toTensorSheafSection_smul (X) (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U)
    (t : TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U)) :
    toTensorSheafSection X F G U (c • t) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf
        (⟨X.presheaf, X.IsSheaf⟩ :
          Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})).obj.obj U from c) •
        toTensorSheafSection X F G U t :=
  map_smul ((sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).app U).hom c t

/-- **A morphism out of a tensor product of sheaves of modules is determined by its effect on
the images of pure tensors of sections.**  The tensor product is a sheafification, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` is the unit of the
  sheafification adjunction, so
precomposition with it is injective on morphisms into a sheaf; the reduction from a general
element of the presheaf tensor product to pure tensors is `TensorProduct.induction_on`.

This is the uniqueness principle a diagram chase ending in `tensorSheaf` needs: it replaces
proving an equality of morphisms by a computation on sections. -/
lemma tensorSheaf_hom_ext {F G K : SheafOfModules.{u} (structureSheafRing X)}
    {α β : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) ⟶ K}
    (h : ∀ (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (m : F.val.obj U) (n : G.val.obj U),
      (α.val.app U).hom (toTensorSheafSection X F G U (m ⊗ₜ[X.presheaf.obj U] n))
        = (β.val.app U).hom (toTensorSheafSection X F G U (m ⊗ₜ[X.presheaf.obj U] n))) :
    α = β := by
  apply ((PresheafOfModules.sheafificationAdjunction (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).homEquiv
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) K).injective
  apply PresheafOfModules.Hom.ext
  ext U t
  change (ModuleCat.Hom.hom (α.val.app U)) (toTensorSheafSection X F G U t)
      = (ModuleCat.Hom.hom (β.val.app U)) (toTensorSheafSection X F G U t)
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact h U m n
  | add a b ha hb =>
      rw [toTensorSheafSection_add X F G U a b, map_add, map_add, ha, hb]

end Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.TildeTensor

variable {R : CommRingCat.{u}}

/-! ### The canonical map `Γ(F) ⊗_R Γ(G) ⟶ Γ(F ⊗ G)` on `Spec R` -/

/-- A sheaf of modules on `Spec R`, retyped over
  `structureSheafRing`, which is the
spelling `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` is indexed by.  The crossing of
  the `rfl`-equality of the two
spellings of the structure sheaf is done here, once, on a bare variable. -/
abbrev modSheaf (F : (Spec R).Modules) :
    SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace) := F

/-- The tensor product of two sheaves of modules on `Spec R`, retyped as an object of
`(Spec R).Modules`. -/
abbrev modTensor (F G : (Spec R).Modules) : (Spec R).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩).obj
      (modSheaf F)).obj (modSheaf G))

/-- The global section of `F ⊗ G` attached to a pair of global sections of `F` and `G`. -/
def gammaTmul (F G : (Spec R).Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩).obj
        (modSheaf F)).obj (modSheaf G))).val.obj (op ⊤) :=
  toTensorSheafSection (Spec R).toRingedSpace (modSheaf F) (modSheaf G) (op ⊤)
    (s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t)

/-- `gammaTmul`, retyped into the global-sections module where `R` acts. -/
def gammaTmulG (F G : (Spec R).Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) : Γ(modTensor F G, ⊤) :=
  gammaTmul F G s t

/-- `gammaTmul` is additive in its left argument. -/
lemma gammaTmul_add_left (F G : (Spec R).Modules) (s s' : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTmulG F G (s + s') t = gammaTmulG F G s t + gammaTmulG F G s' t :=
  (congrArg _ (TensorProduct.add_tmul (R := (Spec R).presheaf.obj (op ⊤)) s s' t)).trans
    (toTensorSheafSection_add (Spec R).toRingedSpace (modSheaf F) (modSheaf G) (op ⊤) _ _)

/-- `gammaTmul` is additive in its right argument. -/
lemma gammaTmul_add_right (F G : (Spec R).Modules) (s : Γ(F, ⊤)) (t t' : Γ(G, ⊤)) :
    gammaTmulG F G s (t + t') = gammaTmulG F G s t + gammaTmulG F G s t' :=
  (congrArg _ (TensorProduct.tmul_add (R := (Spec R).presheaf.obj (op ⊤)) s t t')).trans
    (toTensorSheafSection_add (Spec R).toRingedSpace (modSheaf F) (modSheaf G) (op ⊤) _ _)

/-- `gammaTmulG` of a pair is `r • _` once the pure tensor is `cTop r • (s ⊗ₜ t)`. -/
private lemma toTensorSheafSection_eq_smul_gammaTmulG (F G : (Spec R).Modules) (r : R)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤))
    (x : TensorProduct ((Spec R).presheaf.obj (op ⊤)) Γ(F, ⊤) Γ(G, ⊤))
    (h : x = cTop r • (s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t)) :
    toTensorSheafSection (Spec R).toRingedSpace (modSheaf F) (modSheaf G) (op ⊤) x =
      r • gammaTmulG F G s t :=
  ((congrArg _ h).trans
    (toTensorSheafSection_smul (Spec R).toRingedSpace (modSheaf F) (modSheaf G) (op ⊤)
      (cTop r) _)).trans
    (Scheme.Modules.smul_Spec_def (M := modTensor F G) r (gammaTmulG F G s t)).symm

/-- `gammaTmul` is `R`-linear in its left argument: the `R`-action on global sections over
`Spec R` is the `𝒪_{Spec R}(⊤)`-action through `cTop`. -/
lemma gammaTmul_smul_left (F G : (Spec R).Modules) (r : R) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTmulG F G (r • s) t = r • gammaTmulG F G s t := by
  have h1 : (r • s) ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t
      = cTop r • (s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t) :=
    (congrArg (· ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t)
      (Scheme.Modules.smul_Spec_def (M := F) r s)).trans (TensorProduct.smul_tmul' _ _ _)
  exact toTensorSheafSection_eq_smul_gammaTmulG F G r s t _ h1

/-- `gammaTmul` is `R`-linear in its right argument. -/
lemma gammaTmul_smul_right (F G : (Spec R).Modules) (r : R) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTmulG F G s (r • t) = r • gammaTmulG F G s t := by
  have h1 : s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] (r • t)
      = cTop r • (s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] t) :=
    (congrArg (s ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] ·)
      (Scheme.Modules.smul_Spec_def (M := G) r t)).trans (TensorProduct.tmul_smul _ _ _)
  exact toTensorSheafSection_eq_smul_gammaTmulG F G r s t _ h1

/-- **The canonical map on global sections** `Γ(Spec R, F) ⊗_R Γ(Spec R, G) ⟶ Γ(Spec R, F ⊗ G)`. -/
def gammaTensorMap (F G : (Spec R).Modules) :
    (Γ(F, ⊤) ⊗[R] Γ(G, ⊤)) →ₗ[R] Γ(modTensor F G, ⊤) :=
  TensorProduct.lift (LinearMap.mk₂ (R : Type u) (gammaTmulG F G)
    (gammaTmul_add_left F G) (gammaTmul_smul_left F G)
    (gammaTmul_add_right F G) (gammaTmul_smul_right F G))

/-- `gammaTensorMap F G` sends `s ⊗ t` to `gammaTmulG F G s t`. -/
@[simp] lemma gammaTensorMap_tmul (F G : (Spec R).Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTensorMap F G (s ⊗ₜ[R] t) = gammaTmulG F G s t := rfl

/-! ### Naturality -/

/-- **Moving `IsIso` from the Tag 01CB spelling of the category of modules on `Spec R` to
`(Spec R).Modules`.**  The two categories carry equal but not syntactically equal `Category`
instances; terms unify at default transparency, but instance search does not cross the
difference, so an `IsIso` for one spelling is not found as an instance for the other. -/
lemma isIso_specModules {F F' : (Spec R).Modules} {φ : F ⟶ F'}
    (h : @IsIso (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) _
      (modSheaf F) (modSheaf F') φ) : IsIso φ := h

/-- A morphism of sheaves of modules on `Spec R`, read on global sections as an `R`-linear map. -/
def gammaMap {F F' : (Spec R).Modules} (φ : F ⟶ F') : Γ(F, ⊤) →ₗ[R] Γ(F', ⊤) :=
  ((moduleSpecΓFunctor (R := R)).map φ).hom

/-- `gammaMap` of an isomorphism is bijective. -/
lemma bijective_gammaMap {F F' : (Spec R).Modules} (φ : F ⟶ F') [IsIso φ] :
    Function.Bijective (gammaMap φ) :=
  (ConcreteCategory.isIso_iff_bijective ((moduleSpecΓFunctor (R := R)).map φ)).mp
    (Functor.map_isIso (moduleSpecΓFunctor (R := R)) φ)

/-- **The canonical map on global sections is natural.**  This is naturality of the
sheafification unit,
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection`. -/
lemma gammaTensorMap_naturality {F F' G G' : (Spec R).Modules} (φ : F ⟶ F') (ψ : G ⟶ G')
    (x : Γ(F, ⊤) ⊗[R] Γ(G, ⊤)) :
    gammaMap ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Spec R).toRingedSpace).presheaf, ((Spec R).toRingedSpace).IsSheaf⟩)).map
        ((φ, ψ) : (_, _) ⟶ (_, _))) (gammaTensorMap F G x)
      = gammaTensorMap F' G' (TensorProduct.map (gammaMap φ) (gammaMap ψ) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul leftSection rightSection =>
      exact tensorSheafMap_app_toTensorSheafSection (Spec R).toRingedSpace
        (modSheaf F) (modSheaf G) (modSheaf F') (modSheaf G') φ ψ ⊤ leftSection rightSection
  | add left right left_eq right_eq => simp only [map_add, left_eq, right_eq]

/-! ### The case of an associated sheaf -/

variable (M N : ModuleCat.{u} R)

/-- **The tensor half of Stacks 01I8 on global sections, as an isomorphism of `R`-modules**:
`M ⊗_R N ≅ Γ(Spec R, M̃ ⊗ Ñ)`.  This is `isIso_tildeTensorComparison` transported along the
global-sections identification `AlgebraicGeometry.tilde.isoTop`. -/
def tildeTensorΓIso : ModuleCat.of (R : Type u) (M ⊗[R] N) ≅
    (moduleSpecΓFunctor (R := R)).obj (tildeTensor M N) :=
  tilde.isoTop (ModuleCat.of (R : Type u) (M ⊗[R] N)) ≪≫
    (moduleSpecΓFunctor (R := R)).mapIso (tildeTensorIso M N)

/-- **The isomorphism `M ⊗_R N ≅ Γ(Spec R, M̃ ⊗ Ñ)` is `topTensorMap`.**  This is
`tildeTensorComparison_app_top` together with the fact that the unit of `tilde ⊣ Γ` is
`AlgebraicGeometry.tilde.toOpen` at `⊤`. -/
lemma tildeTensorΓIso_hom_apply (z : M ⊗[R] N) :
    (tildeTensorΓIso M N).hom.hom z = topTensorMap M N z :=
  tildeTensorComparison_app_top M N z

/-- The global-sections identification `A ≅ Γ(Ã, ⊤)` as an `R`-linear equivalence.  This is
Mathlib's `AlgebraicGeometry.tilde.isoTop`. -/
def topEquiv (A : ModuleCat.{u} R) : A ≃ₗ[R] Γ(tilde A, ⊤) := (tilde.isoTop A).toLinearEquiv

/-- `topEquiv A` sends `a` to the global section `topSec A a`. -/
@[simp] lemma topEquiv_apply (A : ModuleCat.{u} R) (a : A) : topEquiv A a = topSec A a := rfl

/-- **The map on global sections of `(M ⊗_R N)~` is the canonical one.**  `topTensorMap` is
`gammaTensorMap` for the two associated sheaves, read through `topEquiv`. -/
lemma topTensorMap_eq :
    topTensorMap M N =
      (gammaTensorMap (tilde M) (tilde N)).comp
        (TensorProduct.congr (topEquiv M) (topEquiv N)).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/-- **The tensor half of Stacks 01I8 on global sections, for associated sheaves**: the canonical
map `M ⊗_R N ⟶ Γ(Spec R, M̃ ⊗ Ñ)` is bijective. -/
lemma bijective_topTensorMap : Function.Bijective (topTensorMap M N) := by
  have h := (ConcreteCategory.isIso_iff_bijective (tildeTensorΓIso M N).hom).mp
    (tildeTensorΓIso M N).isIso_hom
  rwa [show ((tildeTensorΓIso M N).hom.hom : (M ⊗[R] N) → _) = topTensorMap M N from
    funext (tildeTensorΓIso_hom_apply M N)] at h

/-- **The canonical map on global sections is bijective for two associated sheaves.** -/
lemma bijective_gammaTensorMap_tilde :
    Function.Bijective (gammaTensorMap (tilde M) (tilde N)) := by
  have h := bijective_topTensorMap M N
  rw [topTensorMap_eq] at h
  exact (Function.Bijective.of_comp_iff _
    (TensorProduct.congr (topEquiv M) (topEquiv N)).bijective).mp h

/-! ### The tensor half of Stacks 01I8 on global sections -/

/-- **The canonical map `Γ(F) ⊗_R Γ(G) ⟶ Γ(F ⊗ G)` is bijective for quasi-coherent `F` and
`G`.**  This is the global-sections form of the tensor half of Stacks 01I8.

Both `F` and `G` are isomorphic to the associated sheaf of their own global sections
(`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`), so this follows from
`bijective_gammaTensorMap_tilde` and `gammaTensorMap_naturality`. -/
theorem bijective_gammaTensorMap (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (gammaTensorMap F G) := by
  have hF : IsIso F.fromTildeΓ := inferInstance
  have hG : IsIso G.fromTildeΓ := inferInstance
  let e := @asIso (Spec R).Modules _ _ _ F.fromTildeΓ hF
  let d := @asIso (Spec R).Modules _ _ _ G.fromTildeΓ hG
  have hiso : @IsIso (Spec R).Modules _ _ (modTensor F G)
      (tensorSheafMapIso (X := (Spec R).toRingedSpace) e d).hom :=
    isIso_specModules (R := R)
      (tensorSheafMapIso (X := (Spec R).toRingedSpace) e d).isIso_hom
  have hmid : Function.Bijective
      (gammaMap (R := R) (tensorSheafMapIso (X := (Spec R).toRingedSpace) e d).hom) :=
    bijective_gammaMap (R := R)
      (φ := (tensorSheafMapIso (X := (Spec R).toRingedSpace) e d).hom)
  have hbe : Function.Bijective (gammaMap e.hom) := bijective_gammaMap (φ := e.hom)
  have hbd : Function.Bijective (gammaMap d.hom) := bijective_gammaMap (φ := d.hom)
  have hcomp : Function.Bijective
      ((gammaTensorMap F G) ∘ (TensorProduct.map (gammaMap e.hom) (gammaMap d.hom))) := by
    have he : ((gammaTensorMap F G) ∘
          (TensorProduct.map (gammaMap e.hom) (gammaMap d.hom)) : _ → _) =
        (gammaMap (R := R) (tensorSheafMapIso (X := (Spec R).toRingedSpace) e d).hom) ∘
          (gammaTensorMap _ _) :=
      funext fun x => (gammaTensorMap_naturality e.hom d.hom x).symm
    rw [he]
    exact hmid.comp (bijective_gammaTensorMap_tilde _ _)
  refine (Function.Bijective.of_comp_iff _ ?_).mp hcomp
  exact (TensorProduct.congr (LinearEquiv.ofBijective _ hbe)
    (LinearEquiv.ofBijective _ hbd)).bijective

/-- **The tensor half of Stacks 01I8 on global sections, as an isomorphism**: for quasi-coherent
`F` and `G` on `Spec R`, `Γ(Spec R, F) ⊗_R Γ(Spec R, G) ≅ Γ(Spec R, F ⊗ G)`. -/
def gammaTensorEquiv (F G : (Spec R).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (Γ(F, ⊤) ⊗[R] Γ(G, ⊤)) ≃ₗ[R] Γ(modTensor F G, ⊤) :=
  LinearEquiv.ofBijective _ (bijective_gammaTensorMap F G)

/-- `gammaTensorEquiv F G` sends `s ⊗ t` to `gammaTmulG F G s t`. -/
@[simp] lemma gammaTensorEquiv_tmul (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTensorEquiv F G (s ⊗ₜ[R] t) = gammaTmulG F G s t := rfl

end AlgebraicGeometry.TildeTensor
end
