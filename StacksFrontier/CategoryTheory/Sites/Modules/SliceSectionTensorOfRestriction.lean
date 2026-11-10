module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.HomologyRestrictionAdjoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSectionsTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# A sheafification which is a tensor on a slice

Let `O` be a sheaf of commutative rings on a small site `C`, `P` a presheaf of `O`-modules and
`W₀` an object of `C`. Write `Γ` for the ring of global functions of the slice `C/W₀`, which
evaluation at the final object identifies with `O(W₀)`, and `M` for the `Γ`-module `P(W₀)`.
For every object `q : U ⟶ W₀` of the slice there is the `O(U)`-linear map

`O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)`,  `s ⊗ m ↦ s · m|_U`

(`PresheafOfModules.restrictionAdjoint`). This file proves that if it is bijective for a family
of objects of the slice which covers every object of the slice, then the restriction of the
sheafification `P⁺` of `P` to the slice is the sheaf `M ⊗_Γ 𝒪` attached to `M`
(`Stacks.SheafOfModules.SliceRestrictionTensor.isIso_sliceHom`).

The comparison is the morphism `M ⊗_Γ 𝒪 ⟶ P⁺|_{W₀}` adjoint to the image of `P(W₀)` in the
global sections of `P⁺|_{W₀}`. On presheaves it is `s ⊗ m ↦ s · m|_U` followed by the
sheafification map `P ⟶ P⁺`; the first map is bijective on the given family, which covers, so
it is locally bijective, and the sheafification map is locally bijective. A morphism of sheaves
receiving locally bijective maps from the sheafification of the same presheaf is an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.SliceRestrictionTensor.globalModule`: `P(W₀)` as a module over the
  global functions of the slice.
* `Stacks.SheafOfModules.SliceRestrictionTensor.sliceHom`: the comparison
  `M ⊗_Γ 𝒪 ⟶ P⁺|_{W₀}`.

## Main results

* `Stacks.SheafOfModules.SliceRestrictionTensor.isIso_sliceHom`: if the objects `U ⟶ W₀` over
  which `O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)` is bijective cover every object of the slice, then
  `sliceHom` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open scoped ChangeOfRings

universe u

namespace Stacks.SheafOfModules.SliceRestrictionTensor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
  (P : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) (W₀ : C)

/-! ### The global functions of the slice -/

/-- The final object `𝟙 W₀` of the slice at `W₀`. -/
abbrev sliceTop : Over W₀ := Over.mk (𝟙 W₀)

/-- The unique morphism from an object of the slice to its final object. -/
abbrev toSliceTop (U : Over W₀) : U ⟶ sliceTop W₀ := Over.homMk U.hom

/-- The final object of the slice is final. -/
def sliceTopIsTerminal : IsTerminal (sliceTop W₀) :=
  IsTerminal.ofUniqueHom (fun U => toSliceTop W₀ U) (fun U m =>
    Over.OverMorphism.ext (by simpa using Over.w m))

/-- The structure sheaf restricted to the slice at `W₀`. -/
abbrev sliceRing : Sheaf (J.over W₀) CommRingCat.{u} := O.over W₀

/-- The ring `Γ` of global functions of the slice at `W₀`. -/
abbrev sliceGlobalRing : Type u := GlobalFunctionRing (sliceRing O W₀)

/-- Evaluation of a global function of the slice at its final object. -/
abbrev evalTop : sliceGlobalRing O W₀ →+* O.obj.obj (op W₀) :=
  globalSectionEvalHom (sliceRing O W₀) (op (sliceTop W₀))

/-- Evaluation at the final object, read in the sections of the ring sheaf of `P` over `W₀`. -/
abbrev evalTopRing : sliceGlobalRing O W₀ →+*
    (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀) :=
  evalTop O W₀

/-- A global function of the slice, evaluated at an object `q : U ⟶ W₀`, is the restriction along
`q` of its value at the final object. -/
theorem evalTop_restrict (U : Over W₀) (γ : sliceGlobalRing O W₀) :
    (O.obj.map U.hom.op).hom (evalTop O W₀ γ) = γ.1 (op U) :=
  globalSectionEvalHom_naturality (toSliceTop W₀ U).op γ

/-- The global function of the slice restricted from a section of `O` over `W₀`. -/
def globalSectionOf (a : O.obj.obj (op W₀)) : sliceGlobalRing O W₀ :=
  ⟨fun U => (O.obj.map U.unop.hom.op).hom a, fun {U₁ U₂} g => by
    have h : O.obj.map U₁.unop.hom.op ≫ O.obj.map g.unop.left.op = O.obj.map U₂.unop.hom.op := by
      rw [← Functor.map_comp, ← op_comp, Over.w g.unop]
    exact ConcreteCategory.congr_hom h a⟩

/-- The global function of the slice restricted from `a` takes the value `a` at the final
object. -/
theorem evalTop_globalSectionOf (a : O.obj.obj (op W₀)) :
    evalTop O W₀ (globalSectionOf O W₀ a) = a :=
  ConcreteCategory.congr_hom (O.obj.map_id (op W₀)) a

/-! ### `P(W₀)` over the global functions of the slice -/

/-- **`P(W₀)` as a module over the global functions `Γ` of the slice at `W₀`**, through
evaluation at the final object. -/
abbrev globalModule : ModuleCat.{u} (sliceGlobalRing O W₀) :=
  (ModuleCat.restrictScalars (evalTopRing O W₀)).obj (P.obj (op W₀))

/-! ### `O(U) ⊗_Γ P(W₀) = O(U) ⊗_{O(W₀)} P(W₀)` -/

/-- The ring map `O(W₀) → O(U)` of an object `U ⟶ W₀` of the slice. -/
abbrev restrictHom (U : Over W₀) := PresheafOfModules.sectionRestrictionHom O U.hom.op

/-- The tensor product over `Γ` of the presheaf `U ↦ O(U) ⊗_Γ P(W₀)`. -/
abbrev globalTensor (U : Over W₀) : Type u :=
  TensorProduct (sliceGlobalRing O W₀) ((sliceRing O W₀).obj.obj (op U)) (globalModule O P W₀)

/-- The tensor product over `O(W₀)`, the source of the adjoint of a restriction map. -/
abbrev localTensor (U : Over W₀) : Type u :=
  (ModuleCat.extendScalars (restrictHom O W₀ U)).obj (P.obj (op W₀))

/-- A section of the slice ring over `U`, read in the ring sheaf of `P` over `U.left`. -/
abbrev ofSlice (U : Over W₀) (s : (sliceRing O W₀).obj.obj (op U)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left) :=
  s

/-- An element of the `Γ`-module `P(W₀)` read as an element of `P(W₀)`. -/
abbrev ofGlobal (m : globalModule O P W₀) : P.obj (op W₀) := m

/-- The action of a global function on a section over `U` is multiplication by the restriction of
its value at the final object. -/
theorem ofSlice_smul (U : Over W₀) (γ : sliceGlobalRing O W₀)
    (s : (sliceRing O W₀).obj.obj (op U)) :
    ofSlice O W₀ U (γ • s) = restrictHom O W₀ U (evalTopRing O W₀ γ) * ofSlice O W₀ U s :=
  congrArg (· * s) (evalTop_restrict O W₀ U γ).symm

/-- `O(U) ⊗_Γ P(W₀) ⟶ O(U) ⊗_{O(W₀)} P(W₀)`, `s ⊗ m ↦ s ⊗ m`. -/
def toLocalTensor (U : Over W₀) : globalTensor O P W₀ U →+ localTensor O P W₀ U :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun m =>
            ofSlice O W₀ U s ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀),
              restrictHom O W₀ U] ofGlobal O P W₀ m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun _ => TensorProduct.zero_tmul _ _
      map_add' := fun _ _ => AddMonoidHom.ext fun _ => TensorProduct.add_tmul _ _ _ }
    (fun γ s m => (congrArg
      (fun x : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left) =>
        x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀), restrictHom O W₀ U]
          ofGlobal O P W₀ m)
      (ofSlice_smul O W₀ U γ s)).trans
        (ModuleCat.extendScalars_mul_tmul (restrictHom O W₀ U) (evalTopRing O W₀ γ)
          (ofSlice O W₀ U s) (ofGlobal O P W₀ m)))

/-- `toLocalTensor` sends `s ⊗ m` to `s ⊗ m`. -/
theorem toLocalTensor_tmul (U : Over W₀) (s : (sliceRing O W₀).obj.obj (op U))
    (m : globalModule O P W₀) :
    toLocalTensor O P W₀ U (s ⊗ₜ m) =
      ofSlice O W₀ U s ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀),
        restrictHom O W₀ U] ofGlobal O P W₀ m :=
  rfl

/-- A section of the ring sheaf of `P` over `U.left`, read in the slice ring over `U`. -/
abbrev toSlice (U : Over W₀)
    (s : (ModuleCat.restrictScalars (restrictHom O W₀ U)).obj
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left))
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left)))) :
    (sliceRing O W₀).obj.obj (op U) :=
  s

/-- An element of `P(W₀)` read as an element of the `Γ`-module `P(W₀)`. -/
abbrev toGlobal (m : P.obj (op W₀)) : globalModule O P W₀ := m

/-- In the `Γ`-module `P(W₀)`, the action of `r ∈ O(W₀)` is that of the global function of the
slice restricted from `r`. -/
theorem toGlobal_smul (r : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀))
    (m : P.obj (op W₀)) :
    toGlobal O P W₀ (r • m) = globalSectionOf O W₀ r • toGlobal O P W₀ m := by
  refine Eq.trans ?_ (ModuleCat.restrictScalars.smul_def (evalTopRing O W₀)
    (globalSectionOf O W₀ r) (toGlobal O P W₀ m)).symm
  exact congrArg (· • m) (evalTop_globalSectionOf O W₀ r).symm

/-- On sections over `U`, the action of `r ∈ O(W₀)` is that of the global function of the slice
restricted from `r`. -/
theorem toSlice_smul (U : Over W₀) (r : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀))
    (s : (ModuleCat.restrictScalars (restrictHom O W₀ U)).obj
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left))
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op U.left)))) :
    toSlice O W₀ U (r • s) = globalSectionOf O W₀ r • toSlice O W₀ U s :=
  rfl

/-- `O(U) ⊗_{O(W₀)} P(W₀) ⟶ O(U) ⊗_Γ P(W₀)`, `s ⊗ m ↦ s ⊗ m`. -/
def ofLocalTensor (U : Over W₀) : localTensor O P W₀ U →+ globalTensor O P W₀ U :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun m => toSlice O W₀ U s ⊗ₜ[sliceGlobalRing O W₀] toGlobal O P W₀ m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun m₁ m₂ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun m => TensorProduct.zero_tmul _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun m => TensorProduct.add_tmul _ _ _ }
    (fun r s m => by
      change toSlice O W₀ U (r • s) ⊗ₜ[sliceGlobalRing O W₀] toGlobal O P W₀ m =
        toSlice O W₀ U s ⊗ₜ[sliceGlobalRing O W₀] toGlobal O P W₀ (r • m)
      rw [toSlice_smul, toGlobal_smul]
      exact TensorProduct.smul_tmul _ _ _)

/-- **`O(U) ⊗_Γ P(W₀) = O(U) ⊗_{O(W₀)} P(W₀)`**, `Γ → O(W₀)` being bijective. -/
def tensorEquiv (U : Over W₀) : globalTensor O P W₀ U ≃+ localTensor O P W₀ U where
  toFun := toLocalTensor O P W₀ U
  invFun := ofLocalTensor O P W₀ U
  left_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  right_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add a b ha hb =>
      exact (congrArg (toLocalTensor O P W₀ U) (map_add (ofLocalTensor O P W₀ U) a b)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) ha hb))
  map_add' := map_add _

/-! ### The comparison morphism -/

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafification `P⁺` of `P`. -/
abbrev sheafified : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj P

/-- The sheafification map `P ⟶ P⁺`. -/
abbrev sheafifiedUnit :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app P

/-- The restriction `P⁺|_{W₀}` of the sheafification to the slice at `W₀`, read over the
structure sheaf of the slice in the spelling of the global-sections API. -/
abbrev sliceSheaf : SheafOfModules.{u} (ringSheafOfSite.{u, u, u} (sliceRing O W₀)) :=
  (sheafified O P).over W₀

/-- The image of `m ∈ P(W₀)` in `P⁺(W₀)`, read as a section of `P⁺|_{W₀}` over the final object. -/
abbrev unitTop (m : P.obj (op W₀)) : (sliceSheaf O P W₀).val.obj (op (sliceTop W₀)) :=
  (sheafifiedUnit O P).app (op W₀) m

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `unitTop` is additive. -/
theorem unitTop_add (m₁ m₂ : P.obj (op W₀)) :
    unitTop O P W₀ (m₁ + m₂) = unitTop O P W₀ m₁ + unitTop O P W₀ m₂ :=
  map_add ((sheafifiedUnit O P).app (op W₀)).hom m₁ m₂

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `unitTop` is linear over `O(W₀)`. -/
theorem unitTop_smul (r : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (op W₀))
    (m : P.obj (op W₀)) :
    unitTop O P W₀ (r • m) =
      (show (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj.obj (op (sliceTop W₀)) from r) •
        unitTop O P W₀ m :=
  map_smul ((sheafifiedUnit O P).app (op W₀)).hom r m

/-- The global section of `P⁺|_{W₀}` restricted from the image of `m ∈ P(W₀)`. -/
abbrev sliceSection (m : P.obj (op W₀)) : (sliceSheaf O P W₀).sections :=
  (sliceSheaf O P W₀).val.sectionsOfIsTerminal (sliceTopIsTerminal W₀) (unitTop O P W₀ m)

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `sliceSection` is additive. -/
theorem sliceSection_add (m₁ m₂ : P.obj (op W₀)) :
    sliceSection O P W₀ (m₁ + m₂) = sliceSection O P W₀ m₁ + sliceSection O P W₀ m₂ := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  exact (congrArg ((sliceSheaf O P W₀).val.map ((sliceTopIsTerminal W₀).from U.unop).op)
    (unitTop_add O P W₀ m₁ m₂)).trans (map_add _ _ _)

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `sliceSection` is `Γ`-linear, `Γ` acting on `P(W₀)` through evaluation at the final
object. -/
theorem sliceSection_smul (γ : sliceGlobalRing O W₀) (m : P.obj (op W₀)) :
    sliceSection O P W₀ (evalTopRing O W₀ γ • m) = γ • sliceSection O P W₀ m := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  refine (congrArg ((sliceSheaf O P W₀).val.map ((sliceTopIsTerminal W₀).from U.unop).op)
    (unitTop_smul O P W₀ (evalTopRing O W₀ γ) m)).trans ?_
  refine ((sliceSheaf O P W₀).val.map_smul _ _ _).trans ?_
  exact congrArg (· • _) (globalSectionEvalHom_naturality _ γ)

/-- **The `Γ`-linear map `P(W₀) ⟶ Γ(P⁺|_{W₀})`**, sending `m` to the global section restricted
from its image in `P⁺(W₀)`. -/
def sliceTheta : globalModule O P W₀ ⟶
    (globalSectionsFunctor.{u, u, u, u} (ringSheafOfSite.{u, u, u} (sliceRing O W₀))).obj
      (sliceSheaf O P W₀) :=
  ModuleCat.ofHom (X := globalModule O P W₀)
      (Y := (globalSectionsFunctor.{u, u, u, u} (ringSheafOfSite.{u, u, u} (sliceRing O W₀))).obj
        (sliceSheaf O P W₀))
    { toFun := fun m => sliceSection O P W₀ m
      map_add' := fun m₁ m₂ => sliceSection_add O P W₀ m₁ m₂
      map_smul' := fun γ m => sliceSection_smul O P W₀ γ m }

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The value over an object `U ⟶ W₀` of the global section attached to `m`. -/
theorem sliceTheta_apply_val (m : globalModule O P W₀) (U : Over W₀) :
    ((sliceTheta O P W₀).hom m).val (op U) =
      (sliceSheaf O P W₀).val.map ((sliceTopIsTerminal W₀).from U).op (unitTop O P W₀ m) :=
  rfl

/-- Two additive maps out of a tensor product which agree on pure tensors agree everywhere. -/
private theorem tensor_addMonoidHom_apply_eq {R M N A : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [AddCommMonoid A] (f g : M ⊗[R] N →+ A)
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) (t : M ⊗[R] N) : f t = g t := by
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-! ### The presheaf comparison `s ⊗ m ↦ s · m|_U` -/

/-- `O(U) ⊗_Γ P(W₀) ⟶ P(U)`, `s ⊗ m ↦ s · m|_U`: the identification of the tensor over `Γ` with
the tensor over `O(W₀)`, followed by the adjoint of the restriction map of `P`. -/
def restrictTensorHom (U : Over W₀) : globalTensor O P W₀ U →+ P.obj (op U.left) :=
  (PresheafOfModules.restrictionAdjoint O U.hom.op P).hom.toAddMonoidHom.comp
    (tensorEquiv O P W₀ U).toAddMonoidHom

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `restrictTensorHom` sends `s ⊗ m` to `s · m|_U`. -/
theorem restrictTensorHom_tmul (U : Over W₀) (s : (sliceRing O W₀).obj.obj (op U))
    (m : globalModule O P W₀) :
    restrictTensorHom O P W₀ U (s ⊗ₜ m) =
      ofSlice O W₀ U s • (P.map U.hom.op (ofGlobal O P W₀ m) : ToType (P.obj (op U.left))) :=
  PresheafOfModules.restrictionAdjoint_tmul O U.hom.op P (ofSlice O W₀ U s) (ofGlobal O P W₀ m)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `restrictTensorHom` is bijective as soon as the adjoint of the restriction map is. -/
theorem bijective_restrictTensorHom (U : Over W₀)
    (h : Function.Bijective (PresheafOfModules.restrictionAdjoint O U.hom.op P).hom) :
    Function.Bijective (restrictTensorHom O P W₀ U) :=
  h.comp (tensorEquiv O P W₀ U).bijective

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `restrictTensorHom` commutes with restriction. -/
theorem restrictTensorHom_restrict {U V : Over W₀} (f : V ⟶ U) (t : globalTensor O P W₀ U) :
    restrictTensorHom O P W₀ V (tensorRestriction (O := sliceRing O W₀) (globalModule O P W₀)
        f.op t) = P.map f.left.op (restrictTensorHom O P W₀ U t) := by
  refine tensor_addMonoidHom_apply_eq
    ((restrictTensorHom O P W₀ V).comp
      (tensorRestriction (O := sliceRing O W₀) (globalModule O P W₀) f.op).toAddMonoidHom)
    ((P.map f.left.op).hom.toAddMonoidHom.comp (restrictTensorHom O P W₀ U))
    (fun s m => ?_) t
  refine (restrictTensorHom_tmul O P W₀ V _ m).trans ?_
  refine Eq.trans ?_ (congrArg (P.map f.left.op) (restrictTensorHom_tmul O P W₀ U s m)).symm
  refine Eq.trans ?_ (P.map_smul f.left.op (ofSlice O W₀ U s) _).symm
  refine congrArg (_ • ·) ?_
  refine Eq.trans ?_ (PresheafOfModules.map_comp_apply P U.hom.op f.left.op _)
  rw [← op_comp, Over.w f]

/-- The presheaf comparison `U ↦ (O(U) ⊗_Γ P(W₀) ⟶ P(U))` on the slice, as a morphism of presheaves
of abelian groups. -/
def restrictTensorNatTrans :
    (PresheafOfModules.toPresheaf _).obj
        (sectionTensorPresheaf (O := sliceRing O W₀) (globalModule O P W₀)) ⟶
      (Over.forget W₀).op ⋙ (PresheafOfModules.toPresheaf _).obj P where
  app U := AddCommGrpCat.ofHom (restrictTensorHom O P W₀ U.unop)
  naturality {U V} f := by
    ext t
    exact restrictTensorHom_restrict O P W₀ f.unop t

/-! ### The comparison `M ⊗_Γ 𝒪 ⟶ P⁺|_{W₀}` -/

/-- The morphism of presheaves of modules on the slice `(U ↦ O(U) ⊗_Γ P(W₀)) ⟶ P⁺|_{W₀}`,
`s ⊗ m ↦ s · (image of m)|_U`. -/
abbrev slicePresheafHom :
    sectionTensorPresheaf (O := sliceRing O W₀) (globalModule O P W₀) ⟶
      underlyingPresheaf (O := sliceRing O W₀) (sliceSheaf O P W₀) :=
  sectionTensorPresheafHomOfSections.{u, u, u, u} (sliceTheta O P W₀)

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Over `U ⟶ W₀`, the comparison is `s ⊗ m ↦ s · m|_U` followed by the sheafification map. -/
theorem slicePresheafHom_app (U : Over W₀) (t : globalTensor O P W₀ U) :
    ((slicePresheafHom O P W₀).app (op U)).hom t =
      ((sheafifiedUnit O P).app (op U.left)).hom (restrictTensorHom O P W₀ U t) := by
  refine tensor_addMonoidHom_apply_eq (((slicePresheafHom O P W₀).app (op U)).hom.toAddMonoidHom)
    (((sheafifiedUnit O P).app (op U.left)).hom.toAddMonoidHom.comp
      (restrictTensorHom O P W₀ U)) (fun s m => ?_) t
  refine Eq.trans ?_ (congrArg ((sheafifiedUnit O P).app (op U.left)).hom
    (restrictTensorHom_tmul O P W₀ U s m)).symm
  refine Eq.trans ?_ (((sheafifiedUnit O P).app (op U.left)).hom.map_smul _ _).symm
  refine Eq.trans ?_ (congrArg (ofSlice O W₀ U s • ·)
    (PresheafOfModules.naturality_apply (sheafifiedUnit O P) U.hom.op (ofGlobal O P W₀ m)).symm)
  rfl

omit [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison factors through the sheafification map**: on presheaves of abelian groups it
is `s ⊗ m ↦ s · m|_U` followed by the restriction to the slice of `P ⟶ P⁺`. -/
theorem toPresheaf_map_slicePresheafHom :
    (PresheafOfModules.toPresheaf _).map (slicePresheafHom O P W₀) =
      restrictTensorNatTrans O P W₀ ≫ Functor.whiskerLeft (Over.forget W₀).op
        ((PresheafOfModules.toPresheaf _).map (sheafifiedUnit O P)) := by
  ext U t
  exact slicePresheafHom_app O P W₀ U.unop t

/-- **The comparison `M ⊗_Γ 𝒪 ⟶ P⁺|_{W₀}`**, adjoint through sheafification to
`s ⊗ m ↦ s · (image of m)|_U`. -/
def sliceHom :
    (sectionTensorSheafFunctor.{u, u, u, u} (sliceRing O W₀)).obj (globalModule O P W₀) ⟶
      sliceSheaf O P W₀ :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).homEquiv _ _).symm
    (slicePresheafHom O P W₀)

/-- `sliceHom` composed with the sheafification map of `U ↦ O(U) ⊗_Γ P(W₀)` is
`slicePresheafHom`. -/
theorem sliceHom_fac :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).unit.app
        (sectionTensorPresheaf (O := sliceRing O W₀) (globalModule O P W₀)) ≫
      (sliceHom O P W₀).val = slicePresheafHom O P W₀ :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).homEquiv_unit _ _ _).symm.trans
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).homEquiv _ _).apply_symm_apply _)

/-- The objects `U ⟶ W₀` of the slice over which `O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)` is bijective. -/
def GoodPresieve (U : Over W₀) : Presieve U :=
  fun V _ => Function.Bijective (PresheafOfModules.restrictionAdjoint O V.hom.op P).hom

variable {O P W₀}

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If the objects over which `O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)` is bijective cover every object of
the slice, then `restrictTensorNatTrans` is locally injective. -/
theorem isLocallyInjective_restrictTensorNatTrans
    (hcov : ∀ U : Over W₀, Sieve.generate (GoodPresieve O P W₀ U) ∈ J.over W₀ U) :
    Presheaf.IsLocallyInjective (J.over W₀) (restrictTensorNatTrans O P W₀) where
  equalizerSieve_mem {U} x y h := by
    refine GrothendieckTopology.superset_covering _ ?_ (hcov U.unop)
    rw [Sieve.generate_le_iff]
    intro V g hg
    refine (bijective_restrictTensorHom O P W₀ V hg).1 ?_
    exact (restrictTensorHom_restrict O P W₀ g x).trans
      ((congrArg (P.map g.left.op) h).trans (restrictTensorHom_restrict O P W₀ g y).symm)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over W₀) AddCommGrpCat.{u}]
  [(J.over W₀).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If the objects over which `O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)` is bijective cover every object of
the slice, then `restrictTensorNatTrans` is locally surjective. -/
theorem isLocallySurjective_restrictTensorNatTrans
    (hcov : ∀ U : Over W₀, Sieve.generate (GoodPresieve O P W₀ U) ∈ J.over W₀ U) :
    Presheaf.IsLocallySurjective (J.over W₀) (restrictTensorNatTrans O P W₀) where
  imageSieve_mem {U} p := by
    refine GrothendieckTopology.superset_covering _ ?_ (hcov U)
    rw [Sieve.generate_le_iff]
    intro V g hg
    obtain ⟨t, ht⟩ := (bijective_restrictTensorHom O P W₀ V hg).2 (P.map g.left.op p)
    exact ⟨t, ht⟩

/-- **The restriction to a slice of the sheafification of `P` is the sheaf attached to `P(W₀)`**,
provided the objects `U ⟶ W₀` over which `O(U) ⊗_{O(W₀)} P(W₀) ⟶ P(U)` is bijective cover every
object of the slice. -/
theorem isIso_sliceHom
    (hcov : ∀ U : Over W₀, Sieve.generate (GoodPresieve O P W₀ U) ∈ J.over W₀ U) :
    IsIso (sliceHom O P W₀) := by
  have := isLocallyInjective_restrictTensorNatTrans hcov
  have := isLocallySurjective_restrictTensorNatTrans hcov
  have hw₁ : Presheaf.IsLocallyInjective (J.over W₀) (Functor.whiskerLeft (Over.forget W₀).op
      ((PresheafOfModules.toPresheaf _).map (sheafifiedUnit O P))) :=
    Presheaf.isLocallyInjective_whisker (J.over W₀) J (Over.forget W₀)
      ((PresheafOfModules.toPresheaf _).map (sheafifiedUnit O P))
  have hw₂ : Presheaf.IsLocallySurjective (J.over W₀) (Functor.whiskerLeft (Over.forget W₀).op
      ((PresheafOfModules.toPresheaf _).map (sheafifiedUnit O P))) :=
    Presheaf.isLocallySurjective_whisker (J.over W₀) J (Over.forget W₀)
      ((PresheafOfModules.toPresheaf _).map (sheafifiedUnit O P))
  have hi : PresheafOfModules.IsLocallyInjective (J.over W₀) (slicePresheafHom O P W₀) := by
    change Presheaf.IsLocallyInjective _ ((PresheafOfModules.toPresheaf _).map _)
    rw [toPresheaf_map_slicePresheafHom]
    exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ (J.over W₀) _ _ _ _ _
      (isLocallyInjective_restrictTensorNatTrans hcov) hw₁
  have hs : PresheafOfModules.IsLocallySurjective (J.over W₀) (slicePresheafHom O P W₀) := by
    change Presheaf.IsLocallySurjective _ ((PresheafOfModules.toPresheaf _).map _)
    rw [toPresheaf_map_slicePresheafHom]
    exact @Presheaf.isLocallySurjective_comp _ _ (J.over W₀) _ _ _ _ _ _ _ _ _ _ _
      (isLocallySurjective_restrictTensorNatTrans hcov) hw₂
  have hu₁ : PresheafOfModules.IsLocallyInjective (J.over W₀)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).unit.app
        (sectionTensorPresheaf (O := sliceRing O W₀) (globalModule O P W₀))) := by
    change Presheaf.IsLocallyInjective _ (CategoryTheory.toSheafify _ _)
    infer_instance
  have hu₂ : PresheafOfModules.IsLocallySurjective (J.over W₀)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheafOfSite.{u, u, u} (sliceRing O W₀)).obj)).unit.app
        (sectionTensorPresheaf (O := sliceRing O W₀) (globalModule O P W₀))) := by
    change Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ _)
    infer_instance
  exact @Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective _ _ _ _ _ _ _ _ _
    (sliceHom O P W₀) (sliceHom_fac O P W₀) hu₁ hu₂ hi hs

end Comparison

end Stacks.SheafOfModules.SliceRestrictionTensor

end
