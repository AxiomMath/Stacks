module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Tensoring the inclusion of a sheaf of ideals with a module killed by that ideal

Let `(C, O)` be a ringed site and `I ⊆ O` a sheaf of ideals. For a sheaf of `O`-modules `G`
all of whose sections are killed by the corresponding sections of `I`, the map

`I ⊗_O G ⟶ O ⊗_O G`

induced in the first variable by the inclusion `I ⟶ O` is zero. This applies to the graded
pieces `Iⁿ/Iⁿ⁺¹` of the filtration of the structure sheaf by the powers of `I`.

## Main results

* `Stacks.tmul_eq_zero_of_smul_eq_zero`: a pure tensor `a ⊗ y` in `A ⊗_A M` vanishes as soon as
  `a • y = 0`.
* `Stacks.PresheafOfModules.Submodule.whiskerRight_ι_eq_zero`: for a submodule `I` of the free
  rank-one presheaf of modules whose sections kill those of `N`, the map `I ⊗ N ⟶ O ⊗ N` of
  presheaves of modules vanishes.
* `Stacks.Sites.sheafTensor_map_idealι_app_eq_zero`: the map `I ⊗_O G ⟶ O ⊗_O G` of sheaves of
  modules vanishes for a sheaf of ideals `I` whose sections kill those of `G`.
* `Stacks.Sites.smul_adicGradedPiece_eq_zero`: the sections of `I` kill the sections of the
  graded piece `Iⁿ/Iⁿ⁺¹`.
* `Stacks.Sites.sheafTensor_map_idealι_app_adicGradedPiece_eq_zero`: the map
  `I ⊗_O Iⁿ/Iⁿ⁺¹ ⟶ O ⊗_O Iⁿ/Iⁿ⁺¹` vanishes.

## Implementation notes

The tensor product of sheaves of modules is the sheafification of the objectwise tensor product
of the underlying presheaves of modules, so the map in question is the sheafification of the
presheaf-level map, and sheafification is additive, being a left adjoint of the additive
forgetful functor. The presheaf-level map is objectwise the tensor product of the inclusion
`I(U) ⟶ O(U)` with the identity of `G(U)`, which on pure tensors is `a ⊗ g ↦ a ⊗ g`; reading
the latter in `O(U) ⊗_{O(U)} G(U)` as `1 ⊗ (a · g)` shows that it vanishes as soon as `a · g`
does.

That the sections of `I` kill those of `Iⁿ/Iⁿ⁺¹` is not objectwise information: the projection
`Iⁿ ⟶ Iⁿ/Iⁿ⁺¹` is an epimorphism of sheaves of modules, hence only locally surjective on
sections, so a section `g` of `Iⁿ/Iⁿ⁺¹` is only locally the image of a section `t` of `Iⁿ`.
Where it is, the product of a section of `I` with `t` lies in `I · Iⁿ ⊆ Iⁿ⁺¹` and so dies in the
quotient. Vanishing of a section is itself a local condition, because a sheaf is separated, and
that is what turns the local statement into the objectwise one.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory

universe w v₁ u₁ u v

namespace Stacks

/-- **A pure tensor in `A ⊗_A M` dies with the product of its factors.** Under the left unit
isomorphism `A ⊗_A M ≅ M` the pure tensor `a ⊗ y` is the product `a • y`. -/
theorem tmul_eq_zero_of_smul_eq_zero {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (a : A) (y : M) (h : a • y = 0) : a ⊗ₜ[A] y = 0 := by
  rw [← (TensorProduct.lid A M).injective.eq_iff, map_zero, TensorProduct.lid_tmul, h]

end Stacks

namespace Stacks.PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **Tensoring the inclusion of a sheaf of ideals with a presheaf of modules it kills gives
zero, objectwise.** For a submodule `I` of the free rank-one presheaf of modules over a presheaf
of commutative rings, whose sections over every object kill the sections of `N` there, the map
`I ⊗ N ⟶ O ⊗ N` induced by the inclusion `I ⟶ O` vanishes: over every object it sends a pure
tensor `a ⊗ y` to `a ⊗ y = 1 ⊗ (a · y) = 0`. -/
theorem whiskerRight_ι_eq_zero
    {N : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (I : (_root_.PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).Submodule)
    (h : ∀ (U : Cᵒᵖ) (a : (R ⋙ forget₂ CommRingCat RingCat).obj U), a ∈ I.obj U →
      ∀ y : N.obj U, a • y = 0) :
    I.ι ▷ N = 0 := by
  refine _root_.PresheafOfModules.hom_ext fun U => ?_
  rw [_root_.PresheafOfModules.zero_app]
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  exact Stacks.tmul_eq_zero_of_smul_eq_zero
    (A := ToType ((R ⋙ forget₂ CommRingCat RingCat).obj U)) x.val y (h U x.val x.2 y)

end Stacks.PresheafOfModules.Submodule

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Sheafification of presheaves of modules is additive.** It is a left adjoint of the
forgetful functor, which is additive. -/
lemma additive_sheafifyMod : (PresheafOfModules.sheafification.{w}
    (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Additive := by
  let : HasBinaryBiproducts (SheafOfModules.{w} (ringSheaf R)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  exact PresheafOfModules.sheafification_additive.{u₁, v₁, w, w} (ringSheaf.{u₁, v₁, w} R)
    (𝟙 (ringSheaf.{u₁, v₁, w} R).obj)

end Stacks.SheafOfModules.Tensor

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Tensoring the inclusion of a sheaf of ideals with a sheaf of modules it kills gives
zero.** For a sheaf of ideals `I ⊆ O` whose sections over every object of the site kill the
sections of `G` there, the map `I ⊗_O G ⟶ O ⊗_O G` induced by the inclusion `I ⟶ O` vanishes.
The tensor product of sheaves of modules is the sheafification of the objectwise one, and
sheafification is additive, so it suffices that the objectwise map vanish. -/
theorem sheafTensor_map_idealι_app_eq_zero (I : IdealSubsheaf.{v, u, w} X.O)
    (G : Modules.{u, v, w} X)
    (hG : ∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
      a ∈ I.obj U → ∀ g : G.val.obj U, a • g = 0) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app G = 0 := by
  have h0 : PresheafOfModules.tensorHom (O := X.O.obj) I.ι.val (𝟙 G.val) = 0 :=
    Stacks.PresheafOfModules.Submodule.whiskerRight_ι_eq_zero (R := X.O.obj) I.toSubmodule hG
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_map_app, h0]
  exact Functor.map_zero _ _ _

section Quotient

variable (I : IdealSubsheaf.{v, u, w} X.O)
  {M : _root_.SheafOfModules.{w, v, u, w}
    (C := X.C) (J := X.J)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {N' N : _root_.SheafOfModules.Submodule.{w, v, u, w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) M}
  (h : N' ≤ N)
  (hs : idealSmul.{w, v, u, w} (C := X.C) (J := X.J) (O := X.O) (M := M) I N ≤ N')

include h hs

/-- **A step of a filtration whose next term absorbs the product with `I` has a quotient killed
by `I`.** The inclusion of `I · N` into `N`, composed with the projection onto `N/N'`,
vanishes. -/
@[reassoc]
theorem idealSmul_homOfLE_comp_cokernelπ :
    Stacks.SheafOfModules.Submodule.homOfLE (hs.trans h) ≫
      cokernel.π (Stacks.SheafOfModules.Submodule.homOfLE h) = 0 := by
  rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_homOfLE hs h, Category.assoc,
    cokernel.condition, comp_zero]

/-- **The image in `N/N'` of a section of `N` is killed by every section of `I`.** The product
of a section of `I` with a section of `N` lies in `I · N`, which is contained in `N'` and
therefore dies in the quotient. -/
theorem smul_cokernelπ_homOfLE_app_eq_zero (V : X.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) (ha : a ∈ I.obj V)
    (t : (N.toSheafOfModules).val.obj V) :
    a • (cokernel.π (Stacks.SheafOfModules.Submodule.homOfLE h)).val.app V t = 0 := by
  rw [← map_smul]
  exact Stacks.SheafOfModules.val_app_apply_eq_zero _ _
    (idealSmul_homOfLE_comp_cokernelπ I h hs) V
    ⟨a • t.val, smul_mem_idealSmul I ha t.2⟩

/-- **The sections of a sheaf of ideals kill the sections of such a quotient.** A section of
`N/N'` is, after restriction along the arrows of some covering sieve, the image of a section of
`N`, because the projection onto the quotient is an epimorphism of sheaves of modules and hence
locally surjective; there the product with a section of `I` vanishes. A sheaf is separated, so
the product vanishes outright. -/
theorem smul_cokernel_homOfLE_eq_zero (U : X.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (ha : a ∈ I.obj U)
    (g : (cokernel (Stacks.SheafOfModules.Submodule.homOfLE h)).val.obj U) : a • g = 0 := by
  obtain ⟨S, hS, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (cokernel.π (Stacks.SheafOfModules.Submodule.homOfLE h)) g
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hS fun {V} f hf => ?_
  obtain ⟨t, ht⟩ := hlift f hf
  rw [PresheafOfModules.map_smul,
    ← show (cokernel.π (Stacks.SheafOfModules.Submodule.homOfLE h)).val.app (op V) t =
      (cokernel (Stacks.SheafOfModules.Submodule.homOfLE h)).val.map f.op g from ht]
  exact smul_cokernelπ_homOfLE_app_eq_zero I h hs (op V) _ (I.map_mem f.op ha) t

/-- **Tensoring the inclusion of a sheaf of ideals with such a quotient gives zero.** The map
`I ⊗_O N/N' ⟶ O ⊗_O N/N'` induced by the inclusion `I ⟶ O` vanishes, because `I` kills the
sections of `N/N'`. -/
theorem sheafTensor_map_idealι_app_cokernel_homOfLE_eq_zero :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app
      (cokernel (Stacks.SheafOfModules.Submodule.homOfLE h)) = 0 :=
  sheafTensor_map_idealι_app_eq_zero I _ (smul_cokernel_homOfLE_eq_zero I h hs)

end Quotient

/-- **The image in `Iⁿ/Iⁿ⁺¹` of a section of `Iⁿ` is killed by every section of `I`.** The
product of a section of `I` with a section of `Iⁿ` lies in `I · Iⁿ`, which is contained in
`Iⁿ⁺¹` and therefore dies in the quotient. -/
theorem smul_adicGradedPieceπ_app_eq_zero (I : IdealSubsheaf.{v, u, w} X.O) (n : ℕ) (V : X.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V)
    (ha : a ∈ I.obj V)
    (t : ((idealPow I n).toSheafOfModules).val.obj V) :
    a • (adicGradedPieceπ (X := X) I n).val.app V t = 0 :=
  smul_cokernelπ_homOfLE_app_eq_zero I (idealPow_succ_le I n)
    (idealSmul_idealPow_le_idealPow_succ I n) V a ha t

/-- **The sections of a sheaf of ideals kill the sections of its graded pieces.** -/
theorem smul_adicGradedPiece_eq_zero (I : IdealSubsheaf.{v, u, w} X.O) (n : ℕ) (U : X.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (ha : a ∈ I.obj U)
    (g : (adicGradedPiece (X := X) I n).val.obj U) : a • g = 0 :=
  smul_cokernel_homOfLE_eq_zero I (idealPow_succ_le I n)
    (idealSmul_idealPow_le_idealPow_succ I n) U a ha g

/-- **Tensoring the inclusion of a sheaf of ideals with one of its graded pieces gives zero.**
The map `I ⊗_O Iⁿ/Iⁿ⁺¹ ⟶ O ⊗_O Iⁿ/Iⁿ⁺¹` induced by the inclusion `I ⟶ O` vanishes, because `I`
kills the sections of `Iⁿ/Iⁿ⁺¹`. -/
theorem sheafTensor_map_idealι_app_adicGradedPiece_eq_zero (I : IdealSubsheaf.{v, u, w} X.O)
    (n : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app
      (adicGradedPiece (X := X) I n) = 0 :=
  sheafTensor_map_idealι_app_cokernel_homOfLE_eq_zero I (idealPow_succ_le I n)
    (idealSmul_idealPow_le_idealPow_succ I n)

end Stacks.Sites

end
