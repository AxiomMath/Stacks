module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators

/-!
# Morphisms out of a tensor product of two inverse images are determined on unit sections

Let `φ : Z ⟶ Z₁` and `ψ : Z ⟶ Z₂` be morphisms of ringed spaces, let `A` be a sheaf of
`𝒪_{Z₁}`-modules and `B` a sheaf of `𝒪_{Z₂}`-modules. Two morphisms of `𝒪_Z`-modules

`φ^{-1}A ⊗_{𝒪_Z} ψ^{-1}B ⟶ C`

which agree on the images of pure tensors of *pullback-unit* local sections are equal.

Morphisms out of a tensor product sheaf are determined by their values on the images of pure
tensors of arbitrary local sections (`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`), and an
arbitrary local section of an inverse image lies, on a covering sieve, in the span of restricted
pullback-unit sections (`Stacks.PullbackUnitGenerators.spanSieve_mem`). Two span inductions, one
per tensor factor, carry agreement from the unit sections to that span, and separatedness of the
target closes the sieve.

## Main definitions

* `Stacks.PullbackUnitGenerators.tensorEvalMap`: a morphism out of a tensor product sheaf, read
  as a linear map on the presheaf tensor product of local sections, so that its additivity and
  linearity are available for a span induction.

## Main results

* `Stacks.PullbackUnitGenerators.tensorEvalMap_restrict`: the evaluation on a pure tensor
  commutes with restriction of sections.
* `Stacks.PullbackUnitGenerators.tensorEvalMap_eq_of_mem_spanSubmodule`: agreement on pure
  tensors of members of two families of local sections propagates to the spans of their
  restrictions, in both variables.
* `Stacks.PullbackUnitGenerators.tensor_hom_ext_of_unitSections`: **two morphisms out of
  `φ^{-1}A ⊗ ψ^{-1}B` which agree on pure tensors of pullback-unit sections are equal.**

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.PullbackUnitGenerators

section Eval

variable {Z : RingedSpace.{u, u}} {M N C : SheafOfModules.{u} (structureSheafRing Z)}

/-- A morphism out of the tensor product sheaf, read as a linear map on the presheaf tensor
product of local sections: the sheafification unit followed by the morphism. -/
def tensorEvalMap
    (u : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf,
      ((Z)).IsSheaf⟩).obj (M)).obj (N)) ⟶ C)
    (U : (Opens Z.carrier)ᵒᵖ) :
    TensorProduct (Z.presheaf.obj U) (M.val.obj U) (N.val.obj U) →ₗ[Z.presheaf.obj U]
      C.val.obj U :=
  ((sheafifyUnit Z (PresheafOfModules.tensorObj (O := Z.presheaf) M.val N.val)).app U ≫
    u.val.app U).hom

/-- On the image of a pure tensor the linear map is the value of the morphism, which is the
shape `Stacks.SheafOfModules.OnSpace.tensor_hom_ext` consumes. -/
theorem tensorEvalMap_tmul
    (u : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf,
      ((Z)).IsSheaf⟩).obj (M)).obj (N)) ⟶ C)
    (U : (Opens Z.carrier)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
      (u.val.app U).hom (toTensorSheafSection Z M N U (x ⊗ₜ[Z.presheaf.obj U] y)) :=
  rfl

/-- **The evaluation on a pure tensor commutes with restriction of sections.** -/
theorem tensorEvalMap_restrict
    (u : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf,
      ((Z)).IsSheaf⟩).obj (M)).obj (N)) ⟶ C)
    {U V : (Opens Z.carrier)ᵒᵖ}
    (i : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    C.val.map i (tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y)) =
      tensorEvalMap u V
        (M.val.map i x ⊗ₜ[Z.presheaf.obj V] N.val.map i y) :=
  Eq.trans
    (PresheafOfModules.naturality_apply u.val i
      (toTensorSheafSection Z M N U (x ⊗ₜ[Z.presheaf.obj U] y))).symm
    (congrArg (fun t => u.val.app V t)
      (PresheafOfModules.naturality_apply
        (sheafifyUnit Z ((PresheafOfModules.tensorObj (O := (Z).presheaf) (M.val) (N.val)))) i
        (x ⊗ₜ[Z.presheaf.obj U] y)).symm)

variable (u v : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf,
    ((Z)).IsSheaf⟩).obj (M)).obj (N)) ⟶ C)

/-- The difference of two morphisms out of the tensor product sheaf with the left tensor factor
fixed to a local section, as a linear map on the sections of the right factor. -/
def tensorEvalSubLeft {U : (Opens Z.carrier)ᵒᵖ} (x : M.val.obj U) :
    N.val.obj U →ₗ[Z.presheaf.obj U] C.val.obj U :=
  LinearMap.comp (tensorEvalMap u U - tensorEvalMap v U)
    (TensorProduct.mk (Z.presheaf.obj U) (M.val.obj U) (N.val.obj U) x)

/-- The difference of two morphisms out of the tensor product sheaf with the right tensor factor
fixed to a local section, as a linear map on the sections of the left factor. -/
def tensorEvalSubRight {U : (Opens Z.carrier)ᵒᵖ} (y : N.val.obj U) :
    M.val.obj U →ₗ[Z.presheaf.obj U] C.val.obj U :=
  LinearMap.comp (tensorEvalMap u U - tensorEvalMap v U)
    ((TensorProduct.mk (Z.presheaf.obj U) (M.val.obj U) (N.val.obj U)).flip y)

/-- Vanishing of the difference at a section of the right factor is agreement on the
corresponding pure tensor. -/
theorem tensorEvalSubLeft_eq_zero_iff {U : (Opens Z.carrier)ᵒᵖ} (x : M.val.obj U)
    (y : N.val.obj U) :
    tensorEvalSubLeft u v x y = 0 ↔
      tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
        tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y) := by
  simp only [tensorEvalSubLeft, LinearMap.comp_apply, LinearMap.sub_apply,
    TensorProduct.mk_apply, sub_eq_zero]

/-- Vanishing of the difference at a section of the left factor is agreement on the
corresponding pure tensor. -/
theorem tensorEvalSubRight_eq_zero_iff {U : (Opens Z.carrier)ᵒᵖ} (x : M.val.obj U)
    (y : N.val.obj U) :
    tensorEvalSubRight u v y x = 0 ↔
      tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
        tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y) := by
  simp only [tensorEvalSubRight, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, sub_eq_zero]

/-- A linear map vanishing on the restrictions of a family of local sections vanishes on the span
of that family. -/
private theorem map_eq_zero_of_mem_spanSubmodule {U : (Opens Z.carrier)ᵒᵖ} {Q : Type*}
    [AddCommGroup Q] [Module (Z.presheaf.obj U) Q] {P : SheafOfModules.{u} (structureSheafRing Z)}
    (f : P.val.obj U →ₗ[Z.presheaf.obj U] Q) {T : ∀ W : (Opens Z.carrier)ᵒᵖ, Set (P.val.obj W)}
    (h : ∀ (W : (Opens Z.carrier)ᵒᵖ) (g : W ⟶ U) (z : P.val.obj W), z ∈ T W →
      f (P.val.map g z) = 0)
    {y : P.val.obj U} (hy : y ∈ (spanSubmodule P T).obj U) : f y = 0 := by
  have hker : Submodule.span (Z.presheaf.obj U)
      {w : P.val.obj U | ∃ (W : (Opens Z.carrier)ᵒᵖ) (g : W ⟶ U) (z : P.val.obj W),
        z ∈ T W ∧ P.val.map g z = w} ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨W, g, z, hz, rfl⟩
    exact h W g z hz
  exact hker hy

/-- Agreement on pure tensors whose right factor runs over a family of local sections
propagates to the span of the restrictions of that family. -/
theorem tensorEvalMap_eq_of_mem_spanSubmodule_right (U : (Opens Z.carrier)ᵒᵖ) (x : M.val.obj U)
    {T : ∀ W : (Opens Z.carrier)ᵒᵖ, Set (N.val.obj W)}
    (h : ∀ (W : (Opens Z.carrier)ᵒᵖ) (g : W ⟶ U) (z : N.val.obj W), z ∈ T W →
      tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] N.val.map g z) =
        tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] N.val.map g z))
    {y : N.val.obj U} (hy : y ∈ (spanSubmodule N T).obj U) :
    tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
      tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y) := by
  exact (tensorEvalSubLeft_eq_zero_iff u v x y).1
    (map_eq_zero_of_mem_spanSubmodule _ (fun W g z hz =>
      (tensorEvalSubLeft_eq_zero_iff u v x _).2 (h W g z hz)) hy)

/-- **Agreement on pure tensors of members of two families of local sections propagates to the
spans of their restrictions.** -/
theorem tensorEvalMap_eq_of_mem_spanSubmodule (U : (Opens Z.carrier)ᵒᵖ)
    {S : ∀ W : (Opens Z.carrier)ᵒᵖ, Set (M.val.obj W)}
    {T : ∀ W : (Opens Z.carrier)ᵒᵖ, Set (N.val.obj W)}
    (hS : ∀ (W W' : (Opens Z.carrier)ᵒᵖ) (i : W ⟶ W') {w : M.val.obj W}, w ∈ S W →
      M.val.map i w ∈ S W')
    (hT : ∀ (W W' : (Opens Z.carrier)ᵒᵖ) (i : W ⟶ W') {w : N.val.obj W}, w ∈ T W →
      N.val.map i w ∈ T W')
    (h : ∀ (W : (Opens Z.carrier)ᵒᵖ) (x : M.val.obj W) (y : N.val.obj W), x ∈ S W → y ∈ T W →
      tensorEvalMap u W (x ⊗ₜ[Z.presheaf.obj W] y) =
        tensorEvalMap v W (x ⊗ₜ[Z.presheaf.obj W] y))
    {x : M.val.obj U} (hx : x ∈ (spanSubmodule M S).obj U)
    {y : N.val.obj U} (hy : y ∈ (spanSubmodule N T).obj U) :
    tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
      tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y) := by
  exact (tensorEvalSubRight_eq_zero_iff u v x y).1
    (map_eq_zero_of_mem_spanSubmodule _ (fun W g z hz =>
      (tensorEvalSubRight_eq_zero_iff u v _ y).2
        (tensorEvalMap_eq_of_mem_spanSubmodule_right u v U _
          (fun W' g' z' hz' => h U _ _ (hS W U g hz) (hT W' U g' hz')) hy)) hx)

end Eval

section Pullback

variable {Z Z₁ Z₂ : RingedSpace.{u, u}} (φ : Z ⟶ Z₁) (ψ : Z ⟶ Z₂)
  (A : SheafOfModules.{u} (structureSheafRing Z₁))
  (B : SheafOfModules.{u} (structureSheafRing Z₂))
  {C : SheafOfModules.{u} (structureSheafRing Z)}

/-- **Two morphisms out of `φ^{-1}A ⊗ ψ^{-1}B` which agree on pure tensors of pullback-unit
sections are equal.** -/
theorem tensor_hom_ext_of_unitSections
    {u v : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf,
      ((Z)).IsSheaf⟩).obj (((modulePullback φ).obj A))).obj
        (((modulePullback ψ).obj B))) ⟶ C}
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ)
        (x : ((modulePullback φ).obj A).val.obj U)
        (y : ((modulePullback ψ).obj B).val.obj U),
        x ∈ unitSections φ A U → y ∈ unitSections ψ B U →
      tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
        tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y)) :
    u = v := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z (fun U x y => ?_)
  have hxS := spanSieve_mem φ A U x
  have hyS := spanSieve_mem ψ B U y
  have hS : Presheaf.equalizerSieve (F := C.val.presheaf)
      (tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y))
      (tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y)) ∈ JX Z U.unop := by
    refine (JX Z).superset_covering ?_ ((JX Z).intersection_covering hxS hyS)
    rintro W i ⟨hi₁, hi₂⟩
    change C.val.map i.op (tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y)) =
      C.val.map i.op (tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y))
    exact Eq.trans (tensorEvalMap_restrict u i.op x y)
      (Eq.trans
        (tensorEvalMap_eq_of_mem_spanSubmodule u v (op W)
          (fun _ _ j _ hw => map_mem_unitSections φ A j hw)
          (fun _ _ j _ hw => map_mem_unitSections ψ B j hw)
          (fun W' x' y' hx' hy' => h W' x' y' hx' hy') hi₁ hi₂)
        (tensorEvalMap_restrict v i.op x y).symm)
  exact C.isSheaf.isSeparated _ _ hS _ _ (fun _ _ hf => hf)

end Pullback

end Stacks.PullbackUnitGenerators

end
