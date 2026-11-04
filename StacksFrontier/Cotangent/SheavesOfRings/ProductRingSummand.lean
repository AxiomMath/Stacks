module

public import StacksFrontier.Cotangent.SheavesOfRings.ProductRingsSectionwise
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The second summand of a module over a product of sheaves of rings

Let `B` and `D` be sheaves of commutative rings on a site and let `B ⨯ D` be their product. A
sheaf of `B ⨯ D`-modules `M` splits as `e_B M ⊕ e_D M`, where `e_B` and `e_D` are the two
idempotent sections `(1, 0)` and `(0, 1)`, and the second summand `e_D M = ker(e_B)` is
naturally a sheaf of `D`-modules. This file constructs that summand as a functor
`Mod(B ⨯ D) ⥤ Mod(D)` and shows that it is both left and right adjoint to restriction of
scalars along the second projection, hence exact.

## Main definitions

* `CategoryTheory.Sheaf.prodSection`: the section of `B ⨯ D` with prescribed components.
* `CategoryTheory.Sheaf.prodMulFst`: multiplication by the idempotent `e_B = (1, 0)`, as an
  endomorphism of a sheaf of `B ⨯ D`-modules.
* `CategoryTheory.Sheaf.prodSndSummand`: the functor `Mod(B ⨯ D) ⥤ Mod(D)`, `M ↦ e_D M`.
* `CategoryTheory.Sheaf.prodSndSummandAdjunction`: `prodSndSummand` is left adjoint to restriction
  of scalars along the second projection.
* `CategoryTheory.Sheaf.prodRestrictSndSummandAdjunction`: `prodSndSummand` is right adjoint to
  restriction of scalars along the second projection.

## Main results

* `CategoryTheory.Sheaf.isZero_prodSndSummand_prodRestrictFst`: the second summand of a
  `B`-module read over `B ⨯ D` vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {B D : Sheaf J CommRingCat.{max u v w}}

/-- The product `B ⨯ D` of two sheaves of commutative rings. -/
abbrev prodObj (B D : Sheaf J CommRingCat.{max u v w}) : Sheaf J CommRingCat.{max u v w} := B ⨯ D

/-- The second projection `prodObj J B D ⟶ D`. -/
abbrev prodSndHom (B D : Sheaf J CommRingCat.{max u v w}) : prodObj J B D ⟶ D := prod.snd

/-- The first projection `prodObj J B D ⟶ B`. -/
abbrev prodFstHom (B D : Sheaf J CommRingCat.{max u v w}) : prodObj J B D ⟶ B := prod.fst

/-! ## Sections of the product -/

/-- The section of `B ⨯ D` over `U` whose two components are `b` and `d`. -/
def prodSection (U : Cᵒᵖ) (b : B.obj.obj U) (d : D.obj.obj U) : (B ⨯ D).obj.obj U :=
  Function.surjInv (bijective_prod_sections J U).2 (b, d)

/-- The first component of the section `(b, d)` of `B ⨯ D` is `b`. -/
lemma fst_prodSection (U : Cᵒᵖ) (b : B.obj.obj U) (d : D.obj.obj U) :
    (prod.fst : B ⨯ D ⟶ B).hom.app U (prodSection J U b d) = b :=
  congrArg _root_.Prod.fst (Function.surjInv_eq (bijective_prod_sections J U).2 (b, d))

/-- The second component of the section `(b, d)` of `B ⨯ D` is `d`. -/
lemma snd_prodSection (U : Cᵒᵖ) (b : B.obj.obj U) (d : D.obj.obj U) :
    (prod.snd : B ⨯ D ⟶ D).hom.app U (prodSection J U b d) = d :=
  congrArg _root_.Prod.snd (Function.surjInv_eq (bijective_prod_sections J U).2 (b, d))

/-- Two sections of `B ⨯ D` with the same components are equal. -/
lemma prod_section_ext {U : Cᵒᵖ} {x y : (B ⨯ D).obj.obj U}
    (h₁ : (prod.fst : B ⨯ D ⟶ B).hom.app U x = (prod.fst : B ⨯ D ⟶ B).hom.app U y)
    (h₂ : (prod.snd : B ⨯ D ⟶ D).hom.app U x = (prod.snd : B ⨯ D ⟶ D).hom.app U y) :
    x = y :=
  (bijective_prod_sections J U).1 (_root_.Prod.ext h₁ h₂)

/-- Restriction of a section `(b, d)` of `B ⨯ D` is computed componentwise. -/
lemma prodSection_map {U V : Cᵒᵖ} (g : U ⟶ V) (b : B.obj.obj U) (d : D.obj.obj U) :
    (B ⨯ D).obj.map g (prodSection J U b d) =
      prodSection J V (B.obj.map g b) (D.obj.map g d) := by
  refine prod_section_ext J ?_ ?_
  · rw [fst_prodSection, ← CommRingCat.comp_apply, (prod.fst : B ⨯ D ⟶ B).hom.naturality,
      CommRingCat.comp_apply, fst_prodSection]
  · rw [snd_prodSection, ← CommRingCat.comp_apply, (prod.snd : B ⨯ D ⟶ D).hom.naturality,
      CommRingCat.comp_apply, snd_prodSection]

/-! ## The idempotents, read in the sheaf of rings over which modules are taken -/

/-- The sheaf of rings `B ⨯ D` over which modules are taken. -/
abbrev prodRing (B D : Sheaf J CommRingCat.{max u v w}) : Sheaf J RingCat.{max u v w} :=
  Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (B ⨯ D)

/-- Multiplication in the sections of the sheaf of rings underlying a sheaf of commutative rings
is commutative. -/
lemma ringSheaf_mul_comm (O : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ)
    (x y : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} O).obj.obj U) :
    x * y = y * x :=
  mul_comm (x : O.obj.obj U) y

/-- The first projection on sections of the sheaf of rings `B ⨯ D`. -/
abbrev prodFstApp (U : Cᵒᵖ) :
    (prodRing J B D).obj.obj U →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj.obj U :=
  ((squareTargetRing.{u, v, w} J (prod.fst : B ⨯ D ⟶ B)).hom.app U).hom

/-- The second projection on sections of the sheaf of rings `B ⨯ D`. -/
abbrev prodSndApp (U : Cᵒᵖ) :
    (prodRing J B D).obj.obj U →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U :=
  ((squareTargetRing.{u, v, w} J (prod.snd : B ⨯ D ⟶ D)).hom.app U).hom

/-- Two sections of the sheaf of rings `B ⨯ D` with the same components are equal. -/
lemma prodRing_ext {U : Cᵒᵖ} {x y : (prodRing J B D).obj.obj U}
    (h₁ : prodFstApp J U x = prodFstApp J U y) (h₂ : prodSndApp J U x = prodSndApp J U y) :
    x = y :=
  prod_section_ext J (x := x) (y := y) h₁ h₂

/-- The idempotent `e = (1, 0)` of the sections of `B ⨯ D`. -/
def prodIdemFst (U : Cᵒᵖ) : (prodRing J B D).obj.obj U := prodSection J U 1 0

/-- The section `(0, d)` of `B ⨯ D`. -/
def prodIncSnd (U : Cᵒᵖ)
    (d : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    (prodRing J B D).obj.obj U :=
  prodSection J U 0 d

/-- The first component of the idempotent `e = (1, 0)` is `1`. -/
lemma prodFstApp_prodIdemFst (U : Cᵒᵖ) : prodFstApp J U (prodIdemFst J (B := B) (D := D) U) = 1 :=
  fst_prodSection J U _ _

/-- The second component of the idempotent `e = (1, 0)` is `0`. -/
lemma prodSndApp_prodIdemFst (U : Cᵒᵖ) : prodSndApp J U (prodIdemFst J (B := B) (D := D) U) = 0 :=
  snd_prodSection J U _ _

/-- The first component of `(0, d)` is `0`. -/
lemma prodFstApp_prodIncSnd (U : Cᵒᵖ)
    (d : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    prodFstApp J U (prodIncSnd J (B := B) U d) = 0 :=
  fst_prodSection J U _ _

/-- The second component of `(0, d)` is `d`. -/
lemma prodSndApp_prodIncSnd (U : Cᵒᵖ)
    (d : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    prodSndApp J U (prodIncSnd J (B := B) U d) = d :=
  snd_prodSection J U _ _

/-- `d ↦ (0, d)` is multiplicative. -/
lemma prodIncSnd_mul (U : Cᵒᵖ)
    (d d' : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    prodIncSnd J (B := B) U (d * d') = prodIncSnd J (B := B) U d * prodIncSnd J (B := B) U d' := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIncSnd, prodSndApp_prodIncSnd]

/-- `d ↦ (0, d)` is additive. -/
lemma prodIncSnd_add (U : Cᵒᵖ)
    (d d' : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    prodIncSnd J (B := B) U (d + d') = prodIncSnd J (B := B) U d + prodIncSnd J (B := B) U d' := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIncSnd, prodSndApp_prodIncSnd]

/-- `d ↦ (0, d)` sends `0` to `0`. -/
lemma prodIncSnd_zero (U : Cᵒᵖ) :
    prodIncSnd J (B := B) U
      (0 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) = 0 := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIncSnd, prodSndApp_prodIncSnd]

/-- The two idempotents `(0, 1)` and `e = (1, 0)` add up to `1`. -/
lemma prodIncSnd_one_add_prodIdemFst (U : Cᵒᵖ) :
    prodIncSnd J (B := B) U
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) +
      prodIdemFst J (B := B) (D := D) U = 1 := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIncSnd, prodSndApp_prodIncSnd, prodFstApp_prodIdemFst,
    prodSndApp_prodIdemFst]

/-- The idempotent `e = (1, 0)` annihilates `(0, d)`. -/
lemma prodIdemFst_mul_prodIncSnd (U : Cᵒᵖ)
    (d : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    prodIdemFst J (B := B) (D := D) U * prodIncSnd J (B := B) U d = 0 := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIncSnd, prodSndApp_prodIdemFst]

/-- Every section of `B ⨯ D` is the sum of its `B`-part `r e` and its `D`-part `(0, r₂)`. -/
lemma prodRing_decomp (U : Cᵒᵖ) (r : (prodRing J B D).obj.obj U) :
    r = r * prodIdemFst J (B := B) (D := D) U + prodIncSnd J (B := B) U (prodSndApp J U r) := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIdemFst, prodFstApp_prodIncSnd, prodSndApp_prodIdemFst,
    prodSndApp_prodIncSnd]

/-- The idempotent `e = (1, 0)` is compatible with restriction. -/
lemma prodIdemFst_map {U V : Cᵒᵖ} (g : U ⟶ V) :
    (prodRing J B D).obj.map g (prodIdemFst J (B := B) (D := D) U) =
      prodIdemFst J (B := B) (D := D) V := by
  show (B ⨯ D).obj.map g (prodSection J U 1 0) = prodSection J V 1 0
  rw [prodSection_map, map_one, map_zero]

/-- `d ↦ (0, d)` is compatible with restriction. -/
lemma prodIncSnd_map {U V : Cᵒᵖ} (g : U ⟶ V)
    (d : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U) :
    (prodRing J B D).obj.map g (prodIncSnd J (B := B) U d) =
      prodIncSnd J (B := B) V
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.map g d) :=
  (prodSection_map J g 0 (d : D.obj.obj U)).trans (by rw [map_zero]; rfl)

/-! ## Multiplication by the idempotent `e = (1, 0)` -/

/-- **Multiplication by `e = (1, 0)`**, as an endomorphism of a sheaf of `B ⨯ D`-modules. -/
def prodMulFst (M : targetModules.{u, v, w} J (B ⨯ D)) : M ⟶ M where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => prodIdemFst.{u, v, w} J (B := B) (D := D) U • m
          map_add' := fun x y => smul_add _ x y
          map_smul' := fun r m => by
            change prodIdemFst.{u, v, w} J (B := B) (D := D) U • (r • m) =
              r • (prodIdemFst.{u, v, w} J (B := B) (D := D) U • m)
            rw [smul_smul, smul_smul, ringSheaf_mul_comm] }
      naturality := fun {U V} g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change prodIdemFst.{u, v, w} J (B := B) (D := D) V • M.val.map g m =
          M.val.map g (prodIdemFst.{u, v, w} J (B := B) (D := D) U • m)
        rw [M.val.map_smul, prodIdemFst_map] }

/-- Multiplication by `e = (1, 0)`, on sections. -/
lemma prodMulFst_app_apply (M : targetModules.{u, v, w} J (B ⨯ D)) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    (prodMulFst J M).val.app U m = prodIdemFst.{u, v, w} J (B := B) (D := D) U • m :=
  rfl

/-- `prodMulFst` is natural in the module. -/
lemma prodMulFst_naturality {M M' : targetModules.{u, v, w} J (B ⨯ D)} (φ : M ⟶ M') :
    φ ≫ prodMulFst J M' = prodMulFst J M ≫ φ := by
  ext U m
  exact ((φ.val.app U).hom.map_smul (prodIdemFst.{u, v, w} J (B := B) (D := D) U) m).symm

/-! ## The kernel of `e` and its structure of `D`-module -/

/-- The kernel of multiplication by `e = (1, 0)`: the summand `e_D M` of `M`. -/
abbrev prodSndKernel (M : targetModules.{u, v, w} J (B ⨯ D)) : targetModules.{u, v, w} J (B ⨯ D) :=
  kernel (prodMulFst.{u, v, w} J M)

/-- The inclusion of the kernel of `e` is injective on sections. -/
lemma prodSndKernel_ι_injective (M : targetModules.{u, v, w} J (B ⨯ D)) (U : Cᵒᵖ) :
    Function.Injective ((kernel.ι (prodMulFst.{u, v, w} J M)).val.app U) := by
  have : Mono (kernel.ι (prodMulFst.{u, v, w} J M)).val :=
    inferInstanceAs (Mono ((SheafOfModules.forget _).map (kernel.ι (prodMulFst.{u, v, w} J M))))
  exact PresheafOfModules.injective_of_mono _ U

/-- The idempotent `e = (1, 0)` kills the sections of the kernel of multiplication by `e`. -/
lemma prodIdemFst_smul_prodSndKernel (M : targetModules.{u, v, w} J (B ⨯ D)) (U : Cᵒᵖ)
    (k : (prodSndKernel J M).val.obj U) :
    prodIdemFst.{u, v, w} J (B := B) (D := D) U • k = 0 := by
  apply prodSndKernel_ι_injective J M U
  rw [map_smul, map_zero]
  exact congrArg (fun φ : prodSndKernel J M ⟶ M => (φ.val.app U) k)
    (kernel.condition (prodMulFst.{u, v, w} J M))

/-- The action of `D` on the sections of the kernel of `e`: `d • k = (0, d) • k`. -/
@[instance_reducible]
def prodSndKernelModule (M : targetModules.{u, v, w} J (B ⨯ D)) (U : Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U)
      ((prodSndKernel J M).val.obj U) where
  smul d k := prodIncSnd.{u, v, w} J (B := B) (D := D) U d • k
  one_smul k := by
    change prodIncSnd.{u, v, w} J (B := B) (D := D) U 1 • k = k
    have h := congrArg (· • k) (prodIncSnd_one_add_prodIdemFst.{u, v, w} J (B := B) (D := D) U)
    simp only [add_smul, one_smul, prodIdemFst_smul_prodSndKernel, add_zero] at h
    exact h
  mul_smul d d' k := by
    change prodIncSnd.{u, v, w} J (B := B) (D := D) U (d * d') • k =
      prodIncSnd.{u, v, w} J (B := B) (D := D) U d •
        prodIncSnd.{u, v, w} J (B := B) (D := D) U d' • k
    rw [prodIncSnd_mul, mul_smul]
  smul_zero d := smul_zero _
  smul_add d k k' := smul_add _ k k'
  add_smul d d' k := by
    change prodIncSnd.{u, v, w} J (B := B) (D := D) U (d + d') • k =
      prodIncSnd.{u, v, w} J (B := B) (D := D) U d • k +
        prodIncSnd.{u, v, w} J (B := B) (D := D) U d' • k
    rw [prodIncSnd_add, add_smul]
  zero_smul k := by
    change prodIncSnd.{u, v, w} J (B := B) (D := D) U 0 • k = 0
    rw [prodIncSnd_zero, zero_smul]

/-- The summand `e_D M` as a presheaf of modules over the sheaf of rings `D`. -/
def prodSndPresheaf (M : targetModules.{u, v, w} J (B ⨯ D)) :
    PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj where
  obj U := letI := prodSndKernelModule J M U; ModuleCat.of _ ((prodSndKernel J M).val.obj U)
  map {U V} g :=
    letI := prodSndKernelModule J M U
    letI := prodSndKernelModule J M V
    ModuleCat.ofHom (X := ModuleCat.of _ ((prodSndKernel J M).val.obj U))
      (Y := (ModuleCat.restrictScalars
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.map g).hom).obj
          (ModuleCat.of _ ((prodSndKernel J M).val.obj V)))
      { toFun := (prodSndKernel J M).val.map g
        map_add' := map_add _
        map_smul' := fun d k => by
          change (prodSndKernel J M).val.map g (prodIncSnd.{u, v, w} J (B := B) (D := D) U d • k) =
            prodIncSnd.{u, v, w} J (B := B) (D := D) V
              ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.map g d) •
              (prodSndKernel J M).val.map g k
          rw [PresheafOfModules.map_smul, prodIncSnd_map] }

/-- The map of kernels of `e` induced by a morphism of sheaves of `B ⨯ D`-modules. -/
abbrev prodSndKernelMap {M M' : targetModules.{u, v, w} J (B ⨯ D)} (φ : M ⟶ M') :
    prodSndKernel J M ⟶ prodSndKernel J M' :=
  kernel.map (prodMulFst.{u, v, w} J M) (prodMulFst.{u, v, w} J M') φ φ
    (prodMulFst_naturality J φ).symm

/-- **The second summand functor** `Mod(B ⨯ D) ⥤ Mod(D)`, `M ↦ e_D M = ker(e)`, with the
action of `D` through `d ↦ (0, d)`. -/
def prodSndSummand : targetModules.{u, v, w} J (B ⨯ D) ⥤ targetModules.{u, v, w} J D where
  obj M := ⟨prodSndPresheaf J M, (prodSndKernel J M).isSheaf⟩
  map {M M'} φ := ⟨
    { app := fun U =>
        letI := prodSndKernelModule J M U
        letI := prodSndKernelModule J M' U
        ModuleCat.ofHom (X := ModuleCat.of _ ((prodSndKernel J M).val.obj U))
          (Y := ModuleCat.of _ ((prodSndKernel J M').val.obj U))
          { toFun := (prodSndKernelMap J φ).val.app U
            map_add' := map_add _
            map_smul' := fun d k => ((prodSndKernelMap J φ).val.app U).hom.map_smul
              (prodIncSnd.{u, v, w} J (B := B) (D := D) U d) k }
      naturality := fun {U V} g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun k => ?_)
        exact PresheafOfModules.naturality_apply (prodSndKernelMap J φ).val g k }⟩
  map_id M := by
    have h : prodSndKernelMap J (𝟙 M) = 𝟙 _ := by simp
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun k => ?_))
    change (prodSndKernelMap J (𝟙 M)).val.app U k = k
    rw [h]
    rfl
  map_comp {M M' M''} φ ψ := by
    have h : prodSndKernelMap J (φ ≫ ψ) = prodSndKernelMap J φ ≫ prodSndKernelMap J ψ := by
      refine (cancel_mono (kernel.ι (prodMulFst.{u, v, w} J M''))).1 ?_
      simp [prodSndKernelMap]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun k => ?_))
    change (prodSndKernelMap J (φ ≫ ψ)).val.app U k =
      (prodSndKernelMap J ψ).val.app U ((prodSndKernelMap J φ).val.app U k)
    rw [h]
    rfl

/-! ## The splitting `M ⟶ e_D M ⟶ M` -/

/-- `e = (1, 0)` is idempotent. -/
lemma prodIdemFst_mul_self (U : Cᵒᵖ) :
    prodIdemFst.{u, v, w} J (B := B) (D := D) U * prodIdemFst.{u, v, w} J (B := B) (D := D) U =
      prodIdemFst.{u, v, w} J (B := B) (D := D) U := by
  refine prodRing_ext J ?_ ?_ <;>
    simp [prodFstApp_prodIdemFst, prodSndApp_prodIdemFst]

/-- Multiplication by `e` is idempotent. -/
lemma prodMulFst_comp_self (M : targetModules.{u, v, w} J (B ⨯ D)) :
    prodMulFst.{u, v, w} J M ≫ prodMulFst.{u, v, w} J M = prodMulFst.{u, v, w} J M := by
  ext U m
  show prodIdemFst.{u, v, w} J (B := B) (D := D) U •
      prodIdemFst.{u, v, w} J (B := B) (D := D) U • m =
    prodIdemFst.{u, v, w} J (B := B) (D := D) U • m
  rw [smul_smul, prodIdemFst_mul_self]

/-- The projection `M ⟶ e_D M`, `m ↦ (1 - e) m`. -/
def prodSndKernelLift (M : targetModules.{u, v, w} J (B ⨯ D)) : M ⟶ prodSndKernel J M :=
  kernel.lift _ (𝟙 M - prodMulFst.{u, v, w} J M) (by
    rw [Preadditive.sub_comp, Category.id_comp, prodMulFst_comp_self, sub_self])

/-- The lift into the kernel of multiplication by `e`, followed by the inclusion, is
`1 - e`. -/
@[reassoc (attr := simp)]
lemma prodSndKernelLift_ι (M : targetModules.{u, v, w} J (B ⨯ D)) :
    prodSndKernelLift J M ≫ kernel.ι (prodMulFst.{u, v, w} J M) =
      𝟙 M - prodMulFst.{u, v, w} J M :=
  kernel.lift_ι _ _ _

/-- The inclusion of the kernel of multiplication by `e`, followed by the lift, is the
identity. -/
@[reassoc (attr := simp)]
lemma ι_prodSndKernelLift (M : targetModules.{u, v, w} J (B ⨯ D)) :
    kernel.ι (prodMulFst.{u, v, w} J M) ≫ prodSndKernelLift J M = 𝟙 _ := by
  refine (cancel_mono (kernel.ι (prodMulFst.{u, v, w} J M))).1 ?_
  rw [Category.assoc, prodSndKernelLift_ι, Preadditive.comp_sub, Category.comp_id,
    kernel.condition, sub_zero, Category.id_comp]

/-- Multiplication by `e` vanishes on a `D`-module read over `B ⨯ D`. -/
lemma prodMulFst_prodRestrictSnd (N : targetModules.{u, v, w} J D) :
    prodMulFst.{u, v, w} J ((prodRestrictSnd J B D).obj N) = 0 := by
  ext U n
  show ((prodSndApp J U) (prodIdemFst.{u, v, w} J (B := B) (D := D) U)) •
    (show N.val.obj U from n) = (0 : N.val.obj U)
  rw [prodSndApp_prodIdemFst, zero_smul]

/-- Multiplication by `e` is the identity on a `B`-module read over `B ⨯ D`. -/
lemma prodMulFst_prodRestrictFst (N : targetModules.{u, v, w} J B) :
    prodMulFst.{u, v, w} J ((prodRestrictFst J B D).obj N) = 𝟙 _ := by
  ext U n
  show ((prodFstApp J U) (prodIdemFst.{u, v, w} J (B := B) (D := D) U)) •
    (show N.val.obj U from n) = (show N.val.obj U from n)
  rw [prodFstApp_prodIdemFst, one_smul]

/-- On `e_D M` a section `r` of `B ⨯ D` acts through its second component. -/
lemma prodIncSnd_smul_prodSndKernel (M : targetModules.{u, v, w} J (B ⨯ D)) (U : Cᵒᵖ)
    (r : (prodRing J B D).obj.obj U) (k : (prodSndKernel J M).val.obj U) :
    prodIncSnd.{u, v, w} J (B := B) (D := D) U (prodSndApp J U r) • k = r • k := by
  conv_rhs => rw [prodRing_decomp J U r]
  rw [add_smul, mul_smul, prodIdemFst_smul_prodSndKernel, smul_zero, zero_add]

/-- `e_D M`, read back over `B ⨯ D`, is the kernel of `e`: the identity on sections. -/
def prodRestrictSndSummandIso (M : targetModules.{u, v, w} J (B ⨯ D)) :
    (prodRestrictSnd J B D).obj ((prodSndSummand J).obj M) ≅ prodSndKernel J M where
  hom := ⟨{ app := fun U => ConcreteCategory.ofHom (C := ModuleCat _)
              (X := ((prodRestrictSnd J B D).obj ((prodSndSummand J).obj M)).val.obj U)
              (Y := (prodSndKernel J M).val.obj U)
              { toFun := fun k => (k : (prodSndKernel J M).val.obj U)
                map_add' := fun _ _ => rfl
                map_smul' := fun r k => prodIncSnd_smul_prodSndKernel J M U r k }
            naturality := fun _ => rfl }⟩
  inv := ⟨{ app := fun U => ConcreteCategory.ofHom (C := ModuleCat _)
              (X := (prodSndKernel J M).val.obj U)
              (Y := ((prodRestrictSnd J B D).obj ((prodSndSummand J).obj M)).val.obj U)
              { toFun := fun k => k
                map_add' := fun _ _ => rfl
                map_smul' := fun r k => (prodIncSnd_smul_prodSndKernel J M U r k).symm }
            naturality := fun _ => rfl }⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison `e_D M ⟶ M` read over `B ⨯ D`: the identification with the kernel of `e`,
followed by the inclusion. -/
def prodSndSummandIncl (M : targetModules.{u, v, w} J (B ⨯ D)) :
    (prodRestrictSnd J B D).obj ((prodSndSummand J).obj M) ⟶ M :=
  (prodRestrictSndSummandIso J M).hom ≫ kernel.ι (prodMulFst.{u, v, w} J M)

/-- The inclusion of the second summand is a monomorphism. -/
instance (M : targetModules.{u, v, w} J (B ⨯ D)) : Mono (prodSndSummandIncl J M) := by
  dsimp only [prodSndSummandIncl]
  infer_instance

/-- The inclusion `e_D M ⟶ M` is natural in `M`. -/
@[reassoc]
lemma prodSndSummandIncl_naturality {M M' : targetModules.{u, v, w} J (B ⨯ D)} (φ : M ⟶ M') :
    (prodRestrictSnd J B D).map ((prodSndSummand J).map φ) ≫ prodSndSummandIncl J M' =
      prodSndSummandIncl J M ≫ φ := by
  dsimp only [prodSndSummandIncl]
  ext U k
  have h := congrArg (fun χ : prodSndKernel J M ⟶ M' => (χ.val.app U) k)
    (kernel.lift_ι (prodMulFst.{u, v, w} J M') (kernel.ι (prodMulFst.{u, v, w} J M) ≫ φ) (by
      rw [Category.assoc, prodMulFst_naturality, ← Category.assoc, kernel.condition,
        zero_comp]))
  exact h

/-- The splitting `M ⟶ e_D M`, read over `B ⨯ D`. -/
def prodSndSummandProj (M : targetModules.{u, v, w} J (B ⨯ D)) :
    M ⟶ (prodRestrictSnd J B D).obj ((prodSndSummand J).obj M) :=
  prodSndKernelLift J M ≫ (prodRestrictSndSummandIso J M).inv

/-- Projecting to the second summand and including it back is `1 - e`. -/
@[reassoc (attr := simp)]
lemma prodSndSummandProj_incl (M : targetModules.{u, v, w} J (B ⨯ D)) :
    prodSndSummandProj J M ≫ prodSndSummandIncl J M = 𝟙 M - prodMulFst.{u, v, w} J M := by
  simp [prodSndSummandProj, prodSndSummandIncl]

/-- Including the second summand and projecting to it is the identity. -/
@[reassoc (attr := simp)]
lemma prodSndSummandIncl_proj (M : targetModules.{u, v, w} J (B ⨯ D)) :
    prodSndSummandIncl J M ≫ prodSndSummandProj J M = 𝟙 _ := by
  simp [prodSndSummandProj, prodSndSummandIncl]

/-- On a `D`-module read over `B ⨯ D` the splitting composed with the inclusion is the
identity. -/
lemma prodSndSummandProj_incl_prodRestrictSnd (N : targetModules.{u, v, w} J D) :
    prodSndSummandProj J ((prodRestrictSnd J B D).obj N) ≫
        prodSndSummandIncl J ((prodRestrictSnd J B D).obj N) = 𝟙 _ := by
  rw [prodSndSummandProj_incl, prodMulFst_prodRestrictSnd, sub_zero]

/-! ## Restriction along the second projection is fully faithful -/

/-- The projection `B ⨯ D ⟶ D` is surjective on sections. -/
lemma surjective_prodSndApp (U : Cᵒᵖ) : Function.Surjective (prodSndApp J (B := B) (D := D) U) :=
  fun d => ⟨prodIncSnd.{u, v, w} J (B := B) (D := D) U d, prodSndApp_prodIncSnd J U d⟩

/-- The projection `B ⨯ D ⟶ D` is locally surjective, as a map of sheaves of rings. -/
lemma isLocallySurjective_prodSnd :
    Sheaf.IsLocallySurjective (squareTargetRing.{u, v, w} J (prod.snd : B ⨯ D ⟶ D)) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_surjective J _
    (surjective_prodSndApp J (B := B) (D := D))

/-- Restriction of scalars along the second projection is fully faithful. -/
def prodRestrictSndFullyFaithful : (prodRestrictSnd J B D).FullyFaithful :=
  haveI := isLocallySurjective_prodSnd.{u, v, w} J (B := B) (D := D)
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective _

/-! ## The two adjunctions -/

/-- **The second summand is left adjoint to restriction of scalars along the second
projection.** -/
def prodSndSummandAdjunction : prodSndSummand.{u, v, w} J (B := B) (D := D) ⊣
    prodRestrictSnd J B D where
  unit :=
    { app := fun M => prodSndSummandProj J M
      naturality := fun {M M'} φ => by
        refine (cancel_mono (prodSndSummandIncl J M')).1 ?_
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Category.assoc,
          prodSndSummandProj_incl, Functor.comp_map, prodSndSummandIncl_naturality,
          prodSndSummandProj_incl_assoc, Preadditive.comp_sub, Category.comp_id,
          Preadditive.sub_comp, Category.id_comp, prodMulFst_naturality] }
  counit :=
    { app := fun N => (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).preimage
        (prodSndSummandIncl J ((prodRestrictSnd J B D).obj N))
      naturality := fun {N N'} g => by
        refine (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).map_injective ?_
        simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
          Functor.map_comp, Functor.FullyFaithful.map_preimage]
        exact prodSndSummandIncl_naturality J ((prodRestrictSnd J B D).map g) }
  left_triangle_components M := by
    refine (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).map_injective ?_
    dsimp only
    simp only [Functor.comp_obj, Functor.map_comp, Functor.FullyFaithful.map_preimage,
      Functor.map_id]
    rw [prodSndSummandIncl_naturality, prodSndSummandIncl_proj]
  right_triangle_components N := by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.FullyFaithful.map_preimage]
    exact prodSndSummandProj_incl_prodRestrictSnd J N

/-- **The second summand is right adjoint to restriction of scalars along the second
projection.** -/
def prodRestrictSndSummandAdjunction : prodRestrictSnd J B D ⊣
    prodSndSummand.{u, v, w} J (B := B) (D := D) where
  unit :=
    { app := fun N => (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).preimage
        (prodSndSummandProj J ((prodRestrictSnd J B D).obj N))
      naturality := fun {N N'} g => by
        refine (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).map_injective ?_
        refine (cancel_mono (prodSndSummandIncl J ((prodRestrictSnd J B D).obj N'))).1 ?_
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.map_comp,
          Functor.FullyFaithful.map_preimage, Category.assoc, Functor.comp_map,
          prodSndSummandIncl_naturality, prodSndSummandProj_incl_assoc,
          prodSndSummandProj_incl_prodRestrictSnd, Category.comp_id, prodMulFst_prodRestrictSnd,
          sub_zero, Category.id_comp] }
  counit :=
    { app := fun M => prodSndSummandIncl J M
      naturality := fun {M M'} φ => prodSndSummandIncl_naturality J φ }
  left_triangle_components N := by
    simp only [Functor.comp_obj, Functor.id_obj, Functor.FullyFaithful.map_preimage]
    exact prodSndSummandProj_incl_prodRestrictSnd J N
  right_triangle_components M := by
    refine (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).map_injective ?_
    refine (cancel_mono (prodSndSummandIncl J M)).1 ?_
    dsimp only
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp,
      Functor.FullyFaithful.map_preimage, Category.assoc, prodSndSummandIncl_naturality,
      prodSndSummandProj_incl_assoc, prodMulFst_prodRestrictSnd, sub_zero, Category.id_comp,
      Functor.map_id]

/-- The second summand functor is a left adjoint. -/
instance : (prodSndSummand.{u, v, w} J (B := B) (D := D)).IsLeftAdjoint :=
  ⟨_, ⟨prodSndSummandAdjunction.{u, v, w} J⟩⟩

/-- The second summand functor is a right adjoint. -/
instance : (prodSndSummand.{u, v, w} J (B := B) (D := D)).IsRightAdjoint :=
  ⟨_, ⟨prodRestrictSndSummandAdjunction.{u, v, w} J⟩⟩

/-- The second summand functor is additive. -/
instance : (prodSndSummand.{u, v, w} J (B := B) (D := D)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The second summand functor preserves finite limits. -/
instance : PreservesFiniteLimits (prodSndSummand.{u, v, w} J (B := B) (D := D)) :=
  inferInstance

/-- The second summand functor preserves finite colimits. -/
instance : PreservesFiniteColimits (prodSndSummand.{u, v, w} J (B := B) (D := D)) :=
  inferInstance

/-- The second summand of a `D`-module read over `B ⨯ D` is the module itself. -/
instance (N : targetModules.{u, v, w} J D) :
    IsIso ((prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app N) := by
  have := (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).full
  have := (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).faithful
  infer_instance

/-- The second summand of a `B`-module read over `B ⨯ D` vanishes. -/
lemma isZero_prodSndSummand_prodRestrictFst (X : targetModules.{u, v, w} J B) :
    IsZero ((prodSndSummand.{u, v, w} J (B := B) (D := D)).obj
      ((prodRestrictFst J B D).obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  refine (prodRestrictSndFullyFaithful.{u, v, w} J (B := B) (D := D)).map_injective ?_
  refine (cancel_mono (prodSndSummandIncl J ((prodRestrictFst J B D).obj X))).1 ?_
  have h := prodSndSummandProj_incl J ((prodRestrictFst J B D).obj X)
  rw [prodMulFst_prodRestrictFst, sub_self] at h
  rw [Functor.map_id, Functor.map_zero, zero_comp, Category.id_comp,
    ← prodSndSummandIncl_proj_assoc J _ (prodSndSummandIncl J _), h, comp_zero]

end CategoryTheory.Sheaf

end
