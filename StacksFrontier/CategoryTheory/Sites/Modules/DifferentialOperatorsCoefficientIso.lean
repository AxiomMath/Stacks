module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators

/-!
# Differential operators under maps of the coefficient modules

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of rings on a site. An operator on the local sections
of sheaves of `O₂`-modules may be composed on either side with a morphism of sheaves of modules,
and such a composition does not raise the order of a differential operator. Conjugation by
isomorphisms of the modules preserves the order exactly, so the differential operators of order at
most `k` between two modules are those between any pair of isomorphic modules.

## Main definitions

* `DiffOp.RawOp.postcomp` and `DiffOp.RawOp.precomp`: composition of an operator over a base
  object with a morphism of the target, respectively source, module.
* `DiffOp.GlobalOp.precomp`: precomposition of a global operator with a morphism of the source
  module.
* `DiffOp.RawOp.congrIso`: conjugation of an operator over a base object by isomorphisms of the
  source and target modules.
* `DiffOp.diffOpCongrIso`: the resulting equivalence between the differential operators of order
  at most `k` for the two pairs of modules.

## Main results

* `DiffOp.isDiffOpOfOrder_postcomp` and `DiffOp.isDiffOpOfOrder_precomp`: composing with a
  morphism of the target, respectively source, module preserves the order of a differential
  operator.
* `DiffOp.isDiffOpOfOrder_congrIso`: conjugation by isomorphisms of the source and target modules
  preserves the order of a differential operator in both directions.
* `DiffOp.isGlobalDiffOpOfOrder_postcomp_precomp_iff`: the same statement for global operators.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m

namespace DiffOp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J RingCat.{w}}
variable {F F' F'' G G' G'' : SheafOfModules.{m} O₂}

namespace RawOp

variable {U : C}

/-- Postcomposition of an operator on local sections over a base object with a morphism of the
target module. -/
def postcomp (D : RawOp F G U) (f : G ⟶ G') : RawOp F G' U :=
  comp ((AlgebraicGeometry.SheafOfModules.homGlobalOp f).restrict U) D

/-- Precomposition of an operator on local sections over a base object with a morphism of the
source module. -/
def precomp (D : RawOp F G U) (f : F' ⟶ F) : RawOp F' G U :=
  comp D ((AlgebraicGeometry.SheafOfModules.homGlobalOp f).restrict U)

/-- Postcomposition acts on local sections by applying the morphism after the operator. -/
@[simp] theorem postcomp_apply (D : RawOp F G U) (f : G ⟶ G') (Y : Over U)
    (s : F.val.obj (op Y.left)) :
    D.postcomp f Y s = (f.val.app (op Y.left)).hom (D Y s) := rfl

/-- Precomposition acts on local sections by applying the morphism before the operator. -/
@[simp] theorem precomp_apply (D : RawOp F G U) (f : F' ⟶ F) (Y : Over U)
    (s : F'.val.obj (op Y.left)) :
    D.precomp f Y s = D Y ((f.val.app (op Y.left)).hom s) := rfl

/-- Postcomposition with the identity changes nothing. -/
theorem postcomp_id (D : RawOp F G U) : D.postcomp (𝟙 G) = D := rfl

/-- Precomposition with the identity changes nothing. -/
theorem precomp_id (D : RawOp F G U) : D.precomp (𝟙 F) = D := rfl

/-- Iterated postcomposition is postcomposition with the composite. -/
theorem postcomp_postcomp (D : RawOp F G U) (f : G ⟶ G') (g : G' ⟶ G'') :
    (D.postcomp f).postcomp g = D.postcomp (f ≫ g) := rfl

/-- Iterated precomposition is precomposition with the composite. -/
theorem precomp_precomp (D : RawOp F G U) (f : F' ⟶ F) (g : F'' ⟶ F') :
    (D.precomp f).precomp g = D.precomp (g ≫ f) := rfl

/-- Composition on the source and on the target commute. -/
theorem precomp_postcomp (D : RawOp F G U) (f : F' ⟶ F) (g : G ⟶ G') :
    (D.postcomp g).precomp f = (D.precomp f).postcomp g := rfl

/-- Conjugating an operator on local sections over a base object by isomorphisms of the source and
target modules. -/
def congrIso (eF : F ≅ F') (eG : G ≅ G') : RawOp F G U ≃ RawOp F' G' U where
  toFun D := (D.precomp eF.inv).postcomp eG.hom
  invFun D := (D.precomp eF.hom).postcomp eG.inv
  left_inv D := by
    change (((D.precomp eF.inv).postcomp eG.hom).precomp eF.hom).postcomp eG.inv = D
    rw [precomp_postcomp, precomp_precomp, eF.hom_inv_id, precomp_id, postcomp_postcomp,
      eG.hom_inv_id, postcomp_id]
  right_inv D := by
    change (((D.precomp eF.hom).postcomp eG.inv).precomp eF.inv).postcomp eG.hom = D
    rw [precomp_postcomp, precomp_precomp, eF.inv_hom_id, precomp_id, postcomp_postcomp,
      eG.inv_hom_id, postcomp_id]

/-- Conjugation acts on local sections by the inverse isomorphism of the source, the operator and
the isomorphism of the target. -/
theorem congrIso_apply (eF : F ≅ F') (eG : G ≅ G') (D : RawOp F G U) (Y : Over U)
    (s : F'.val.obj (op Y.left)) :
    congrIso eF eG D Y s =
      (eG.hom.val.app (op Y.left)).hom (D Y ((eF.inv.val.app (op Y.left)).hom s)) := rfl

end RawOp

namespace GlobalOp

/-- Precomposition of a global operator on local sections with a morphism of the source module. -/
def precomp (D : GlobalOp F G) (f : F' ⟶ F) : GlobalOp F' G :=
  D.comp (AlgebraicGeometry.SheafOfModules.homGlobalOp f)

/-- Restriction to a base object commutes with precomposition. -/
@[simp] theorem restrict_precomp (D : GlobalOp F G) (f : F' ⟶ F) (U : C) :
    (D.precomp f).restrict U = (D.restrict U).precomp f := rfl

/-- Restriction to a base object commutes with postcomposition. -/
@[simp] theorem restrict_postcomp (D : GlobalOp F G) (f : G ⟶ G') (U : C) :
    (AlgebraicGeometry.SheafOfModules.postcomp D f).restrict U = (D.restrict U).postcomp f := rfl

end GlobalOp

/-- Postcomposition with a morphism of the target module preserves the order of a differential
operator. -/
theorem isDiffOpOfOrder_postcomp (φ : O₁ ⟶ O₂) (k : ℕ) {U : C} (D : RawOp F G U)
    (hD : IsDiffOpOfOrder φ k D) (f : G ⟶ G') :
    IsDiffOpOfOrder φ k (D.postcomp f) :=
  isDiffOpOfOrder_comp_raw φ (k + 0) k 0 rfl D _ hD
    (AlgebraicGeometry.SheafOfModules.homGlobalOp_isOrderZero φ f U)

/-- Precomposition with a morphism of the source module preserves the order of a differential
operator. -/
theorem isDiffOpOfOrder_precomp (φ : O₁ ⟶ O₂) (k : ℕ) {U : C} (D : RawOp F G U)
    (hD : IsDiffOpOfOrder φ k D) (f : F' ⟶ F) :
    IsDiffOpOfOrder φ k (D.precomp f) :=
  Nat.zero_add k ▸ isDiffOpOfOrder_comp_raw φ (0 + k) 0 k rfl
    ((AlgebraicGeometry.SheafOfModules.homGlobalOp f).restrict U) D
    (AlgebraicGeometry.SheafOfModules.homGlobalOp_isOrderZero φ f U) hD

/-- Conjugating an operator on local sections by isomorphisms of the source and target modules
preserves the order of a differential operator, in both directions. -/
theorem isDiffOpOfOrder_congrIso (φ : O₁ ⟶ O₂) (k : ℕ) {U : C} (eF : F ≅ F') (eG : G ≅ G')
    (D : RawOp F G U) :
    IsDiffOpOfOrder φ k (RawOp.congrIso eF eG D) ↔ IsDiffOpOfOrder φ k D :=
  ⟨fun h ↦ (RawOp.congrIso (U := U) eF eG).symm_apply_apply D ▸
      isDiffOpOfOrder_postcomp φ k _ (isDiffOpOfOrder_precomp φ k _ h eF.hom) eG.inv,
    fun h ↦ isDiffOpOfOrder_postcomp φ k _ (isDiffOpOfOrder_precomp φ k D h eF.inv) eG.hom⟩

/-- The differential operators of order at most `k` between two sheaves of modules are the
differential operators of order at most `k` between any pair of isomorphic sheaves of modules. -/
def diffOpCongrIso (φ : O₁ ⟶ O₂) (k : ℕ) {U : C} (eF : F ≅ F') (eG : G ≅ G') :
    {D : RawOp F G U // IsDiffOpOfOrder φ k D} ≃
      {D : RawOp F' G' U // IsDiffOpOfOrder φ k D} :=
  Equiv.subtypeEquiv (RawOp.congrIso eF eG) fun D ↦
    (isDiffOpOfOrder_congrIso φ k eF eG D).symm

/-- Conjugating a global operator on local sections by isomorphisms of the source and target
modules preserves the order of a differential operator, in both directions. -/
theorem isGlobalDiffOpOfOrder_postcomp_precomp_iff (φ : O₁ ⟶ O₂) (k : ℕ) (eF : F ≅ F')
    (eG : G ≅ G') (D : GlobalOp F G) :
    IsGlobalDiffOpOfOrder φ k
        (AlgebraicGeometry.SheafOfModules.postcomp (D.precomp eF.inv) eG.hom) ↔
      IsGlobalDiffOpOfOrder φ k D :=
  forall_congr' fun U ↦ isDiffOpOfOrder_congrIso φ k eF eG (D.restrict U)

/-- Precomposition with a morphism of the source module preserves the order of a global
differential operator. -/
theorem isGlobalDiffOpOfOrder_precomp (φ : O₁ ⟶ O₂) (k : ℕ) (D : GlobalOp F G)
    (hD : IsGlobalDiffOpOfOrder φ k D) (f : F' ⟶ F) :
    IsGlobalDiffOpOfOrder φ k (D.precomp f) :=
  fun U ↦ isDiffOpOfOrder_precomp φ k (D.restrict U) (hD U) f

end DiffOp

end
