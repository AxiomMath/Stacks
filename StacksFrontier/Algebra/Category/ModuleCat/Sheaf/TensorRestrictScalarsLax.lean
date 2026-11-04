module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The lax comparison of the tensor product with restriction of scalars

Let `ρ : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on a topological space `Y`, so
that an `ℬ`-module restricts to an `𝒜`-module.  Tensoring does not commute with restriction of
scalars, but there is a canonical comparison in one direction: a pure tensor of two sections is
a pure tensor whichever of the two rings it is formed over, and this gives a morphism

`(M|_𝒜) ⊗_𝒜 (N|_𝒜) ⟶ (M ⊗_ℬ N)|_𝒜`

of sheaves of `𝒜`-modules, natural in `M` and in `N`.

## Main definitions

* `Stacks.SheafOfModules.TensorRestrictScalars.sectionComparison`: the canonical additive map
  `M ⊗_R N → M ⊗_S N` for a ring homomorphism `R → S` and two `S`-modules, `m ⊗ n ↦ m ⊗ n`.
* `Stacks.SheafOfModules.TensorRestrictScalars.presheafComparison`: **the comparison for
  presheaves of modules**, `(M|_𝒜) ⊗^{pre}_𝒜 (N|_𝒜) ⟶ (M ⊗^{pre}_ℬ N)|_𝒜`.
* `Stacks.SheafOfModules.TensorRestrictScalars.laxComparison`: **the comparison for sheaves of
  modules**, `(M|_𝒜) ⊗_𝒜 (N|_𝒜) ⟶ (M ⊗_ℬ N)|_𝒜`, obtained from the presheaf comparison by the
  sheafification adjunction.

## Main results

* `sectionComparison_tmul`, `sectionMap_eq` and `presheafComparison_app_apply`: the presheaf
  comparison takes `m ⊗_𝒜 n` to `m ⊗_ℬ n` on sections.
* `homEquiv_laxComparison`: along the sheafification adjunction the comparison is the presheaf
  comparison followed by the sheafification unit.
* `laxComparison_toTensorSheafSection`: the value of the comparison on the canonical sections
  of a tensor product sheaf.
* `presheafComparison_naturality` and `laxComparison_naturality`: the comparison is natural in
  both module variables, before and after sheafification.

## Implementation notes

The two sheaves of rings live on one space, so both sides of the comparison are tensor products
of modules over a ringed space in the sense of [Stacks, Tag 01CA]: the space with each of the two
sheaves of rings is read as a ringed space by `PresheafOfModules.ringedSpaceOfSheaf`.  The two
sheaves of rings are explicit arguments throughout, since a sheaf of rings cannot be recovered
from `PresheafOfModules.ringedSpaceOfSheaf` of it by unification.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

attribute [local implicit_reducible] PresheafOfModules.tensorObj

open CategoryTheory Opposite TensorProduct TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open PresheafOfModules (ringedSpaceOfSheaf)

universe u

namespace Stacks.SheafOfModules.TensorRestrictScalars

/-! ### The comparison on sections -/

section Algebraic

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (M N : ModuleCat.{u} S)

/-- **The canonical additive map `M ⊗_R N → M ⊗_S N`** attached to a ring homomorphism
`φ : R → S` and two `S`-modules `M`, `N`, where the source is formed for the restrictions of
scalars along `φ`.  It sends a pure tensor to the pure tensor with the same entries. -/
noncomputable def sectionComparison :
    TensorProduct R ((ModuleCat.restrictScalars φ).obj M)
        ((ModuleCat.restrictScalars φ).obj N) →+
      TensorProduct S M N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => (TensorProduct.mk S M N m).toAddMonoidHom)
      (fun m m' => AddMonoidHom.ext (fun n =>
        TensorProduct.add_tmul (m : M) (m' : M) (n : N))))
    (fun r m n =>
      show ((φ r • (m : M)) ⊗ₜ[S] (n : N)) = (m : M) ⊗ₜ[S] (φ r • (n : N)) from
        TensorProduct.smul_tmul (φ r) (m : M) (n : N))

/-- The comparison sends `m ⊗_R n` to `m ⊗_S n`. -/
theorem sectionComparison_tmul (m : ((ModuleCat.restrictScalars φ).obj M))
    (n : ((ModuleCat.restrictScalars φ).obj N)) :
    sectionComparison φ M N (m ⊗ₜ[R] n) = (m : M) ⊗ₜ[S] (n : N) := rfl

end Algebraic

variable {Y : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})
  (ρ : A ⟶ B)

/-! ### Restriction of scalars along a morphism of sheaves of commutative rings -/

/-- The morphism of presheaves of (not necessarily commutative) rings underlying a morphism of
sheaves of commutative rings. -/
noncomputable def ringMap : O (ringedSpaceOfSheaf A) ⟶ O (ringedSpaceOfSheaf B) :=
  Functor.whiskerRight ρ.hom (forget₂ CommRingCat.{u} RingCat.{u})

/-- On sections over an open set, `ringMap` is the ring homomorphism `ρ` gives there. -/
theorem ringMap_app (U : (Opens ↥Y)ᵒᵖ) :
    (ringMap A B ρ).app U = (forget₂ CommRingCat.{u} RingCat.{u}).map (ρ.hom.app U) := rfl

/-- Restriction of scalars on presheaves of modules along a morphism of sheaves of commutative
rings. -/
noncomputable abbrev restrictScalarsPresheaf :
    PresheafOfModules.{u} (O (ringedSpaceOfSheaf B)) ⥤
      PresheafOfModules.{u} (O (ringedSpaceOfSheaf A)) :=
  PresheafOfModules.restrictScalars (ringMap A B ρ)

/-- The morphism of sheaves of rings underlying a morphism of sheaves of commutative rings. -/
noncomputable def sheafRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf A) ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map ρ

/-- The two forms of the underlying morphism of sheaves of rings agree. -/
theorem sheafRingMap_hom : (sheafRingMap A B ρ).hom = ringMap A B ρ := rfl

/-- Restriction of scalars on sheaves of modules along a morphism of sheaves of commutative
rings. -/
@[sga "4 IV 11.1.4" "Res(u), special case"]
noncomputable abbrev restrictScalarsSheaf :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf B)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf A)) :=
  SheafOfModules.restrictScalars (sheafRingMap A B ρ)

/-! ### The comparison for presheaves of modules -/

variable (M N : PresheafOfModules.{u} (O (ringedSpaceOfSheaf B)))

/-- The comparison `M(U) ⊗_{𝒜(U)} N(U) → M(U) ⊗_{ℬ(U)} N(U)` on sections over an open set. -/
noncomputable def sectionMap (U : (Opens ↥Y)ᵒᵖ) :
    TensorProduct (A.obj.obj U) (((restrictScalarsPresheaf A B ρ).obj M).obj U)
        (((restrictScalarsPresheaf A B ρ).obj N).obj U) →+
      TensorProduct (B.obj.obj U) (M.obj U) (N.obj U) :=
  sectionComparison ((ρ.hom.app U).hom) (M.obj U) (N.obj U)

/-- The comparison on sections is the algebraic one for the ring homomorphism `𝒜(U) → ℬ(U)`. -/
theorem sectionMap_eq (U : (Opens ↥Y)ᵒᵖ) :
    sectionMap A B ρ M N U = sectionComparison ((ρ.hom.app U).hom) (M.obj U) (N.obj U) := rfl

/-- Two composites of additive maps out of a tensor product agree if they agree on pure
tensors. -/
private theorem comp_tmul_ext {R M N X Y Z F₁ G₁ F₂ G₂ : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module R M] [Module R N] [FunLike F₁ (M ⊗[R] N) X] [AddMonoidHomClass F₁ (M ⊗[R] N) X]
    [FunLike G₁ X Z] [AddMonoidHomClass G₁ X Z] [FunLike F₂ (M ⊗[R] N) Y]
    [AddMonoidHomClass F₂ (M ⊗[R] N) Y] [FunLike G₂ Y Z] [AddMonoidHomClass G₂ Y Z]
    (f₁ : F₁) (g₁ : G₁) (f₂ : F₂) (g₂ : G₂) (h : ∀ m n, g₁ (f₁ (m ⊗ₜ n)) = g₂ (f₂ (m ⊗ₜ n)))
    (t : M ⊗[R] N) : g₁ (f₁ t) = g₂ (f₂ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- The comparison on sections commutes with the restriction maps of the two presheaf tensor
products. -/
theorem sectionMap_tRestrAdd {V W : (Opens ↥Y)ᵒᵖ} (f : V ⟶ W)
    (t : TensorProduct (A.obj.obj V) (((restrictScalarsPresheaf A B ρ).obj M).obj V)
      (((restrictScalarsPresheaf A B ρ).obj N).obj V)) :
    sectionMap A B ρ M N W
        ((PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsPresheaf A B ρ).obj M)
          ((restrictScalarsPresheaf A B ρ).obj N)).restrictₛₗ f t)
      = (PresheafOfModules.tensorObj (O := B.obj) M N).restrictₛₗ f
          (sectionMap A B ρ M N V t) := by
  refine comp_tmul_ext _ _ _ _ ?_ t
  exact fun _ _ => rfl

/-- The comparison as a morphism of the underlying presheaves of abelian groups. -/
noncomputable def presheafNat :
    (PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsPresheaf A B ρ).obj M)
        ((restrictScalarsPresheaf A B ρ).obj N)).presheaf ⟶
      (PresheafOfModules.tensorObj (O := B.obj) M N).presheaf where
  app U := AddCommGrpCat.ofHom (sectionMap A B ρ M N U)
  naturality _ _ f := AddCommGrpCat.hom_ext (AddMonoidHom.ext (sectionMap_tRestrAdd A B ρ M N f))

/-- The comparison on sections is `𝒜(U)`-linear, the scalar action on the target being the one
restricted along `ρ`. -/
theorem sectionMap_smul (V : (Opens ↥Y)ᵒᵖ) (a : A.obj.obj V)
    (t : TensorProduct (A.obj.obj V) (((restrictScalarsPresheaf A B ρ).obj M).obj V)
      (((restrictScalarsPresheaf A B ρ).obj N).obj V)) :
    sectionMap A B ρ M N V (a • t) = ((ρ.hom.app V).hom a) • sectionMap A B ρ M N V t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **The comparison for presheaves of modules**
`(M|_𝒜) ⊗^{pre}_𝒜 (N|_𝒜) ⟶ (M ⊗^{pre}_ℬ N)|_𝒜`, on sections `m ⊗_𝒜 n ↦ m ⊗_ℬ n`. -/
noncomputable def presheafComparison :
    PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsPresheaf A B ρ).obj M)
        ((restrictScalarsPresheaf A B ρ).obj N) ⟶
      (restrictScalarsPresheaf A B ρ).obj (PresheafOfModules.tensorObj (O := B.obj) M N) :=
  PresheafOfModules.homMk (presheafNat A B ρ M N) (sectionMap_smul A B ρ M N)

/-- On sections the presheaf comparison is `sectionMap`. -/
theorem presheafComparison_app_apply (U : (Opens ↥Y)ᵒᵖ)
    (t : TensorProduct (A.obj.obj U) (((restrictScalarsPresheaf A B ρ).obj M).obj U)
      (((restrictScalarsPresheaf A B ρ).obj N).obj U)) :
    ((presheafComparison A B ρ M N).app U).hom t = sectionMap A B ρ M N U t := rfl

/-! ### The comparison for sheaves of modules -/

section Sheaf

variable (F G : SheafOfModules.{u} (Tensor.ringSheaf B))

/-- The transpose of the comparison: the presheaf comparison followed by the sheafification unit
of the tensor product over `ℬ`. -/
noncomputable def laxLeg :
    PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsSheaf A B ρ).obj F).val
        ((restrictScalarsSheaf A B ρ).obj G).val ⟶
      (SheafOfModules.forget (Tensor.ringSheaf A) ⋙
          PresheafOfModules.restrictScalars (𝟙 (Tensor.ringSheaf A).obj)).obj
        ((restrictScalarsSheaf A B ρ).obj
          (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G)) :=
  presheafComparison A B ρ F.val G.val ≫
    (restrictScalarsPresheaf A B ρ).map
      ((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
          (𝟙 (Tensor.ringSheaf B).obj)).unit.app
        (PresheafOfModules.tensorObj (O := B.obj) F.val G.val))

/-- The transpose is the presheaf comparison followed by the restriction of the sheafification
unit. -/
theorem laxLeg_eq :
    laxLeg A B ρ F G = presheafComparison A B ρ F.val G.val ≫
      (restrictScalarsPresheaf A B ρ).map
        ((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
            (𝟙 (Tensor.ringSheaf B).obj)).unit.app
          (PresheafOfModules.tensorObj (O := B.obj) F.val G.val)) := rfl

/-- **The lax comparison of the tensor product with restriction of scalars**
`(M|_𝒜) ⊗_𝒜 (N|_𝒜) ⟶ (M ⊗_ℬ N)|_𝒜` for sheaves of modules: the transpose of `laxLeg` along the
sheafification adjunction for `𝒜`-modules. -/
noncomputable def laxComparison :
    ((Tensor.sheafTensor.{u, u, u, u, u} A).obj ((restrictScalarsSheaf A B ρ).obj F)).obj
        ((restrictScalarsSheaf A B ρ).obj G) ⟶
      (restrictScalarsSheaf A B ρ).obj
        (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G) :=
  ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf A)
      (𝟙 (Tensor.ringSheaf A).obj)).homEquiv
    (PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsSheaf A B ρ).obj F).val
      ((restrictScalarsSheaf A B ρ).obj G).val)
    ((restrictScalarsSheaf A B ρ).obj
      (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G))).symm
    (laxLeg A B ρ F G)

/-- Along the sheafification adjunction, the lax comparison is the presheaf comparison followed
by the sheafification unit. -/
theorem homEquiv_laxComparison :
    (PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf A)
        (𝟙 (Tensor.ringSheaf A).obj)).homEquiv
        (PresheafOfModules.tensorObj (O := A.obj) ((restrictScalarsSheaf A B ρ).obj F).val
          ((restrictScalarsSheaf A B ρ).obj G).val)
        ((restrictScalarsSheaf A B ρ).obj
          (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G))
      (laxComparison A B ρ F G) = laxLeg A B ρ F G :=
  Equiv.apply_symm_apply _ _

/-- **The comparison on the canonical sections of a tensor product sheaf**: it carries the image
of `t` in `(M|_𝒜) ⊗_𝒜 (N|_𝒜)` to the image of `sectionMap t` in `M ⊗_ℬ N`. -/
theorem laxComparison_toTensorSheafSection (U : (Opens ↥Y)ᵒᵖ)
    (t : TensorProduct (A.obj.obj U) (((restrictScalarsPresheaf A B ρ).obj F.val).obj U)
      (((restrictScalarsPresheaf A B ρ).obj G.val).obj U)) :
    ((laxComparison A B ρ F G).val.app U).hom
        (toTensorSheafSection (ringedSpaceOfSheaf A) ((restrictScalarsSheaf A B ρ).obj F)
          ((restrictScalarsSheaf A B ρ).obj G) U t)
      = toTensorSheafSection (ringedSpaceOfSheaf B) F G U
        (sectionMap A B ρ F.val G.val U t) :=
  congrArg (fun f => ((PresheafOfModules.Hom.app f U).hom) t)
    (homEquiv_laxComparison A B ρ F G)

end Sheaf

/-! ### Naturality in both variables -/

section Naturality

variable {M N} {M' N' : PresheafOfModules.{u} (O (ringedSpaceOfSheaf B))}

/-- **The presheaf comparison is natural in both module variables.** -/
theorem presheafComparison_naturality (φ : M ⟶ M') (ψ : N ⟶ N') :
    PresheafOfModules.tensorHom (O := A.obj) ((restrictScalarsPresheaf A B ρ).map φ)
          ((restrictScalarsPresheaf A B ρ).map ψ) ≫ presheafComparison A B ρ M' N'
      = presheafComparison A B ρ M N ≫
        (restrictScalarsPresheaf A B ρ).map
          (PresheafOfModules.tensorHom (O := B.obj) φ ψ) := by
  apply PresheafOfModules.Hom.ext
  ext U t
  change sectionMap A B ρ M' N' U
      (((PresheafOfModules.tensorHom (O := A.obj) ((restrictScalarsPresheaf A B ρ).map φ)
        ((restrictScalarsPresheaf A B ρ).map ψ)).app U).hom t) =
    ((PresheafOfModules.tensorHom (O := B.obj) φ ψ).app U).hom (sectionMap A B ρ M N U t)
  refine comp_tmul_ext _ _ _ _ ?_ t
  exact fun _ _ => rfl

end Naturality

section SheafNaturality

variable {F F' G G' : SheafOfModules.{u} (Tensor.ringSheaf B)}

/-- The sheafification unit is natural for the morphisms of presheaf tensor products induced by
a pair of morphisms of sheaves of modules. -/
theorem presheafTensorMap_comp_sheafifyUnit (φ : F ⟶ F') (ψ : G ⟶ G') :
    PresheafOfModules.tensorHom (O := B.obj) φ.val ψ.val ≫
        (PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
            (𝟙 (Tensor.ringSheaf B).obj)).unit.app
          (PresheafOfModules.tensorObj (O := B.obj) F'.val G'.val)
      = (PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
            (𝟙 (Tensor.ringSheaf B).obj)).unit.app
          (PresheafOfModules.tensorObj (O := B.obj) F.val G.val) ≫
        (SheafOfModules.forget (Tensor.ringSheaf B) ⋙
            PresheafOfModules.restrictScalars (𝟙 (Tensor.ringSheaf B).obj)).map
          ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u} B)).map
            (X := (F, G)) (Y := (F', G')) (φ, ψ)) := by
  have computation := congrArg
    (fun morphism => (SheafOfModules.forget (Tensor.ringSheaf B) ⋙
      PresheafOfModules.restrictScalars (𝟙 (Tensor.ringSheaf B).obj)).map morphism)
    (Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} B φ ψ)
  exact ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf B)
    (𝟙 (Tensor.ringSheaf B).obj)).unit.naturality
      (PresheafOfModules.tensorHom (O := B.obj) φ.val ψ.val)).trans
        (congrArg (fun morphism => (PresheafOfModules.sheafificationAdjunction.{u}
          (R := Tensor.ringSheaf B) (𝟙 (Tensor.ringSheaf B).obj)).unit.app
          (PresheafOfModules.tensorObj (O := B.obj) F.val G.val) ≫ morphism) computation.symm)

/-- The transpose of the comparison is natural in both module variables. -/
theorem laxLeg_naturality (φ : F ⟶ F') (ψ : G ⟶ G') :
    PresheafOfModules.tensorHom (O := A.obj) ((restrictScalarsPresheaf A B ρ).map φ.val)
          ((restrictScalarsPresheaf A B ρ).map ψ.val) ≫ laxLeg A B ρ F' G'
      = laxLeg A B ρ F G ≫
        (restrictScalarsPresheaf A B ρ).map
          ((SheafOfModules.forget (Tensor.ringSheaf B) ⋙
              PresheafOfModules.restrictScalars (𝟙 (Tensor.ringSheaf B).obj)).map
            ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u} B)).map
              (X := (F, G)) (Y := (F', G')) (φ, ψ))) := by
  show PresheafOfModules.tensorHom (O := A.obj) ((restrictScalarsPresheaf A B ρ).map φ.val)
        ((restrictScalarsPresheaf A B ρ).map ψ.val) ≫
      (presheafComparison A B ρ F'.val G'.val ≫
        (restrictScalarsPresheaf A B ρ).map
          ((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
              (𝟙 (Tensor.ringSheaf B).obj)).unit.app
            (PresheafOfModules.tensorObj (O := B.obj) F'.val G'.val))) = _
  rw [← Category.assoc, presheafComparison_naturality A B ρ φ.val ψ.val, Category.assoc,
    ← (restrictScalarsPresheaf A B ρ).map_comp
      (PresheafOfModules.tensorHom (O := B.obj) φ.val ψ.val)
      ((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf B)
          (𝟙 (Tensor.ringSheaf B).obj)).unit.app
        (PresheafOfModules.tensorObj (O := B.obj) F'.val G'.val)),
    presheafTensorMap_comp_sheafifyUnit B φ ψ]
  exact (congrArg (fun z => presheafComparison A B ρ F.val G.val ≫ z)
    ((restrictScalarsPresheaf A B ρ).map_comp _ _)).trans (Category.assoc _ _ _).symm

/-- **The lax comparison is natural in both module variables.** -/
theorem laxComparison_naturality (φ : F ⟶ F') (ψ : G ⟶ G') :
    (Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u} A)).map
          (X := ((restrictScalarsSheaf A B ρ).obj F, (restrictScalarsSheaf A B ρ).obj G))
          (Y := ((restrictScalarsSheaf A B ρ).obj F', (restrictScalarsSheaf A B ρ).obj G'))
          ((restrictScalarsSheaf A B ρ).map φ, (restrictScalarsSheaf A B ρ).map ψ) ≫
        laxComparison A B ρ F' G'
      = laxComparison A B ρ F G ≫
        (restrictScalarsSheaf A B ρ).map
          ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u} B)).map
            (X := (F, G)) (Y := (F', G')) (φ, ψ)) := by
  let adjunction := PresheafOfModules.sheafificationAdjunction.{u}
    (R := Tensor.ringSheaf A) (𝟙 (Tensor.ringSheaf A).obj)
  let targetMap := (restrictScalarsSheaf A B ρ).map
    ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u} B)).map
      (X := (F, G)) (Y := (F', G')) (φ, ψ))
  have square := adjunction.homEquiv_naturality_right_square
    (X := PresheafOfModules.tensorObj (O := A.obj)
      ((restrictScalarsSheaf A B ρ).obj F').val ((restrictScalarsSheaf A B ρ).obj G').val)
    (X' := PresheafOfModules.tensorObj (O := A.obj)
      ((restrictScalarsSheaf A B ρ).obj F).val ((restrictScalarsSheaf A B ρ).obj G).val)
    (Y := (restrictScalarsSheaf A B ρ).obj
      (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).obj G))
    (Y' := (restrictScalarsSheaf A B ρ).obj
      (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F').obj G'))
    (PresheafOfModules.tensorHom (O := A.obj)
      ((restrictScalarsPresheaf A B ρ).map φ.val)
      ((restrictScalarsPresheaf A B ρ).map ψ.val))
    (laxLeg A B ρ F' G') (laxLeg A B ρ F G)
    targetMap
    (laxLeg_naturality A B ρ φ ψ)
  exact (congrArg (fun morphism => morphism ≫ laxComparison A B ρ F' G')
    (Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} A
      ((restrictScalarsSheaf A B ρ).map φ)
      ((restrictScalarsSheaf A B ρ).map ψ))).trans square

end SheafNaturality

end Stacks.SheafOfModules.TensorRestrictScalars

end
