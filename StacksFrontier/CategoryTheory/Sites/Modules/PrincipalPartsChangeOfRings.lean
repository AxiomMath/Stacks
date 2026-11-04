module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
import StacksCore.Tactic.StacksAttribute

/-!
# Change of rings for sheaves of principal parts

Let
```
A ──φ──▸ B
│         │
α         β
▼         ▼
A' ─φ'─▸ B'
```
be a commutative square of sheaves of rings on a site, let `F` be a sheaf of `B`-modules, let
`F'` be a sheaf of `B'`-modules and let `uF : F ⟶ β^* F'` be a `B`-linear map. Precomposing a
differential operator out of `F'` with `uF` is a differential operator out of `F` of the same
order, so corepresentability of differential operators gives, for every order `k`, a canonical
map `P^k_{B/A}(F) ⟶ β^* P^k_{B'/A'}(F')` of sheaves of principal parts. These maps send
universal generators to universal generators and commute with the canonical maps that reduce
the order from `k + 1` to `k`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.precompRaw`: precomposition of a raw operator with a map of
  coefficient modules.
* `AlgebraicGeometry.SheafOfModules.principalPartsOrderReduction`: the canonical map from
  principal parts of order `k + 1` to those of order `k`.
* `AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare`: the change-of-rings map on
  principal parts.

## Main results

* `AlgebraicGeometry.SheafOfModules.isDiffOpOfOrder_precompRaw`: precomposition with a
  compatible module map preserves the order of a differential operator.
* `AlgebraicGeometry.SheafOfModules.principalPartsOrderReduction_universalOperator` and
  `AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare_universalOperator`: both maps are
  described by their effect on the universal local generators.
* `AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare_comp_orderReduction`:
  compatibility of the change-of-rings maps with reduction of the order.

## Implementation notes

Principal parts are the corepresenting objects `moduleOfPrincipalParts` of
`differentialOperatorsFunctor`, so every map constructed here is the unique factorisation of an
explicitly given differential operator through the universal one; nothing is chosen. The
order-reduction map is the factorisation of the universal operator of order `k`, regarded as an
operator of order at most `k + 1`. The change-of-rings map is linear over the source
coefficient sheaf after restriction of scalars along `β`, which is why its target carries
`SheafOfModules.restrictScalars β`.

The name `principalPartsMap` is already taken in this namespace by the functoriality of
principal parts in the *coefficient module* over a fixed morphism of ring sheaves; the map
constructed here varies the morphism of ring sheaves as well, hence the suffix `OfSquare`.

## References

* [Stacks Project, Tag 09CX](https://stacks.math.columbia.edu/tag/09CX)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A B A' B' : Sheaf J RingCat.{w}}
variable (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
variable (h : φ ≫ β = α ≫ φ')
variable (F : _root_.SheafOfModules.{max u v w m} B)
variable (F' : _root_.SheafOfModules.{max u v w m} B')
variable (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')

/-- Precomposition of a raw operator out of `F'` with a map `F ⟶ β^* F'` of coefficient
modules. -/
noncomputable def precompRaw
    (f : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    {G' : _root_.SheafOfModules.{max u v w m} B'} {U : C} (D : DiffOp.RawOp F' G' U) :
    DiffOp.RawOp F ((_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj G') U :=
  fun Y ↦ (D Y).comp ((f.val.app (op Y.left)).hom.toAddMonoidHom)

private lemma sectionRingHom_natural {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : B.obj.obj X) :
    DiffOp.sectionRingHom β Y ((B.obj.map f) b) =
      (B'.obj.map f) (DiffOp.sectionRingHom β X b) :=
  congrArg (fun q : B.obj.obj X ⟶ B'.obj.obj Y ↦ q.hom b)
    (((sheafToPresheaf J RingCat).map β).naturality f)

private lemma sectionRingHom_square (h : φ ≫ β = α ≫ φ') (X : Cᵒᵖ) (a : A.obj.obj X) :
    DiffOp.sectionRingHom β X (DiffOp.sectionRingHom φ X a) =
      DiffOp.sectionRingHom φ' X (DiffOp.sectionRingHom α X a) := by
  simpa [DiffOp.sectionRingHom] using
    congrArg (fun f ↦ f a) (congrArg (fun q : A ⟶ B' ↦ DiffOp.sectionRingHom q X) h)

private lemma moduleMap_natural
    (f : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (s : F.val.obj X) :
    (f.val.app Y).hom ((F.val.presheaf.map g) s) =
      (F'.val.presheaf.map g) ((f.val.app X).hom s) :=
  congrArg (fun q ↦ q.hom s) (f.val.naturality g)

private lemma precompRaw_commutator {U : C} {G' : _root_.SheafOfModules.{max u v w m} B'}
    (f : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    (D : DiffOp.RawOp F' G' U) (Y : Over U) (g : B.obj.obj (op Y.left)) :
    DiffOp.RawOp.commutator g
      (DiffOp.RawOp.slice (precompRaw.{v, u, w, m} β F F' f D) Y) =
      precompRaw.{v, u, w, m} β F F' f
        (DiffOp.RawOp.commutator (DiffOp.sectionRingHom β (op Y.left) g)
          (DiffOp.RawOp.slice D Y)) := by
  funext Z
  ext s
  let : Module (B.obj.obj (op (Over.mk (Z.hom ≫ Y.hom)).left))
      (G'.val.obj (op (Over.mk (Z.hom ≫ Y.hom)).left)) :=
    (inferInstance : Module (B.obj.obj (op (Over.mk (Z.hom ≫ Y.hom)).left))
      (((_root_.SheafOfModules.restrictScalars β).obj G').val.obj
        (op (Over.mk (Z.hom ≫ Y.hom)).left)))
  change (D (Over.mk (Z.hom ≫ Y.hom)))
        ((f.val.app (op Z.left)).hom
          ((B.obj.map Z.hom.op) g • s)) -
      (show B.obj.obj (op (Over.mk (Z.hom ≫ Y.hom)).left) from
        (B.obj.map Z.hom.op) g) •
        (D (Over.mk (Z.hom ≫ Y.hom))) ((f.val.app (op Z.left)).hom s) =
    (D (Over.mk (Z.hom ≫ Y.hom)))
        ((B'.obj.map Z.hom.op) (DiffOp.sectionRingHom β (op Y.left) g) •
          (show F'.val.obj (op Z.left) from (f.val.app (op Z.left)).hom s)) -
      (B'.obj.map Z.hom.op) (DiffOp.sectionRingHom β (op Y.left) g) •
        (D (Over.mk (Z.hom ≫ Y.hom))) ((f.val.app (op Z.left)).hom s)
  rw [(f.val.app (op Z.left)).hom.map_smul]
  change (D (Over.mk (Z.hom ≫ Y.hom)))
        ((DiffOp.sectionRingHom β (op Z.left) ((B.obj.map Z.hom.op) g)) •
          (show F'.val.obj (op Z.left) from (f.val.app (op Z.left)).hom s)) -
      DiffOp.sectionRingHom β (op Z.left) ((B.obj.map Z.hom.op) g) •
        (D (Over.mk (Z.hom ≫ Y.hom))) ((f.val.app (op Z.left)).hom s) =
    (D (Over.mk (Z.hom ≫ Y.hom)))
        ((B'.obj.map Z.hom.op) (DiffOp.sectionRingHom β (op Y.left) g) •
          (show F'.val.obj (op Z.left) from (f.val.app (op Z.left)).hom s)) -
      (B'.obj.map Z.hom.op) (DiffOp.sectionRingHom β (op Y.left) g) •
        (D (Over.mk (Z.hom ≫ Y.hom))) ((f.val.app (op Z.left)).hom s)
  rw [sectionRingHom_natural β Z.hom.op g]

/-- Precomposition with a compatible map of coefficient modules preserves the order of a
differential operator. -/
theorem isDiffOpOfOrder_precompRaw (k : ℕ) {U : C}
    {G' : _root_.SheafOfModules.{max u v w m} B'}
    (α : A ⟶ A') (h : φ ≫ β = α ≫ φ')
    (f : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    (D : DiffOp.RawOp F' G' U)
    (hD : DiffOp.IsDiffOpOfOrder φ' k D) :
    DiffOp.IsDiffOpOfOrder φ k (precompRaw.{v, u, w, m} β F F' f D) := by
  induction k generalizing U D with
  | zero =>
      rcases hD with ⟨hDnat, hDlin⟩
      refine ⟨?_, ?_⟩
      · intro Y Y' q s
        change (D Y) ((f.val.app (op Y.left)).hom
          ((F.val.presheaf.map q.left.op) s)) =
          (G'.val.presheaf.map q.left.op)
            ((D Y') ((f.val.app (op Y'.left)).hom s))
        rw [moduleMap_natural.{v, u, w, m} β F F' f q.left.op s]
        exact hDnat Y Y' q ((f.val.app (op Y'.left)).hom s)
      · intro Y r s
        let : Module (B.obj.obj (op Y.left)) (G'.val.obj (op Y.left)) :=
          (inferInstance : Module (B.obj.obj (op Y.left))
            (((_root_.SheafOfModules.restrictScalars β).obj G').val.obj (op Y.left)))
        change (D Y) ((f.val.app (op Y.left)).hom (r • s)) =
          r • (D Y) ((f.val.app (op Y.left)).hom s)
        rw [(f.val.app (op Y.left)).hom.map_smul]
        change (D Y) (DiffOp.sectionRingHom β (op Y.left) r •
          (show F'.val.obj (op Y.left) from (f.val.app (op Y.left)).hom s)) =
          DiffOp.sectionRingHom β (op Y.left) r •
            (D Y) ((f.val.app (op Y.left)).hom s)
        exact hDlin Y (DiffOp.sectionRingHom β (op Y.left) r)
          (show F'.val.obj (op Y.left) from (f.val.app (op Y.left)).hom s)
  | succ k ih =>
      rcases hD with ⟨hDnat, hDlin, hDcomm⟩
      refine ⟨?_, ?_, ?_⟩
      · intro Y Y' q s
        change (D Y) ((f.val.app (op Y.left)).hom
          ((F.val.presheaf.map q.left.op) s)) =
          (G'.val.presheaf.map q.left.op)
            ((D Y') ((f.val.app (op Y'.left)).hom s))
        rw [moduleMap_natural.{v, u, w, m} β F F' f q.left.op s]
        exact hDnat Y Y' q ((f.val.app (op Y'.left)).hom s)
      · intro Y a s
        let : Module (B.obj.obj (op Y.left)) (G'.val.obj (op Y.left)) :=
          (inferInstance : Module (B.obj.obj (op Y.left))
            (((_root_.SheafOfModules.restrictScalars β).obj G').val.obj (op Y.left)))
        change (D Y) ((f.val.app (op Y.left)).hom
          (DiffOp.sectionRingHom φ (op Y.left) a • s)) =
          DiffOp.sectionRingHom φ (op Y.left) a •
            (D Y) ((f.val.app (op Y.left)).hom s)
        rw [(f.val.app (op Y.left)).hom.map_smul]
        change (D Y) (DiffOp.sectionRingHom β (op Y.left)
          (DiffOp.sectionRingHom φ (op Y.left) a) •
            (show F'.val.obj (op Y.left) from (f.val.app (op Y.left)).hom s)) =
          DiffOp.sectionRingHom β (op Y.left)
            (DiffOp.sectionRingHom φ (op Y.left) a) •
            (D Y) ((f.val.app (op Y.left)).hom s)
        rw [sectionRingHom_square φ φ' α β h (op Y.left) a]
        exact hDlin Y (DiffOp.sectionRingHom α (op Y.left) a)
          (show F'.val.obj (op Y.left) from (f.val.app (op Y.left)).hom s)
      · intro Y g
        change DiffOp.IsDiffOpOfOrder φ k
          (DiffOp.RawOp.commutator g
            (DiffOp.RawOp.slice (precompRaw.{v, u, w, m} β F F' f D) Y))
        rw [precompRaw_commutator]
        exact ih _ (hDcomm Y (DiffOp.sectionRingHom β (op Y.left) g))

/-- The canonical map from principal parts of order `k + 1` to those of order `k`. -/
noncomputable def principalPartsOrderReduction
    (φ : A ⟶ B) (F : _root_.SheafOfModules.{max u v w m} B) (k : ℕ) :
    moduleOfPrincipalParts.{v, u, w, m} φ F (k + 1) ⟶
      moduleOfPrincipalParts.{v, u, w, m} φ F k :=
  (differentialOperatorsFunctor.{v, u, w, m} φ F (k + 1)).corepresentableBy.homEquiv.symm
    ⟨(differentialOperatorsFunctor.{v, u, w, m} φ F k).coreprx.1,
      fun U ↦ DiffOp.RawOp.isDiffOpOfOrder_succ_of_isDiffOpOfOrder φ k
        ((differentialOperatorsFunctor.{v, u, w, m} φ F k).coreprx.1.restrict U)
        ((differentialOperatorsFunctor.{v, u, w, m} φ F k).coreprx.2 U)⟩

/-- Reduction of order fixes each universal local generator. -/
theorem principalPartsOrderReduction_universalOperator
    (φ : A ⟶ B) (F : _root_.SheafOfModules.{max u v w m} B) (k : ℕ)
    (X : Cᵒᵖ) (s : F.val.obj X) :
    ((principalPartsOrderReduction.{v, u, w, m} φ F k).val.app X).hom
      ((differentialOperatorsFunctor.{v, u, w, m} φ F (k + 1)).coreprx.1 X s) =
        (differentialOperatorsFunctor.{v, u, w, m} φ F k).coreprx.1 X s := by
  let D := differentialOperatorsFunctor.{v, u, w, m} φ F (k + 1)
  let E := differentialOperatorsFunctor.{v, u, w, m} φ F k
  have hmap : D.corepresentableBy.homEquiv
      (principalPartsOrderReduction.{v, u, w, m} φ F k) =
        (⟨E.coreprx.1, fun U ↦ DiffOp.RawOp.isDiffOpOfOrder_succ_of_isDiffOpOfOrder
          φ k (E.coreprx.1.restrict U) (E.coreprx.2 U)⟩ : D.obj E.coreprX) :=
    D.corepresentableBy.homEquiv.apply_symm_apply _
  have hcomp := D.corepresentableBy.homEquiv_comp
    (principalPartsOrderReduction.{v, u, w, m} φ F k) (𝟙 D.coreprX)
  rw [Category.id_comp, hmap] at hcomp
  have hop : E.coreprx.1 =
      postcomp D.coreprx.1 (principalPartsOrderReduction.{v, u, w, m} φ F k) := by
    have hh := congrArg Subtype.val hcomp
    change E.coreprx.1 =
      (homGlobalOp (principalPartsOrderReduction.{v, u, w, m} φ F k)).comp
        D.coreprx.1 at hh
    exact hh
  have hEval := congrArg (fun q : DiffOp.GlobalOp F E.coreprX => q X s) hop.symm
  simpa [postcomp, homGlobalOp, DiffOp.GlobalOp.comp] using hEval

/-- **Stacks 09CX.** The map on order-`k` principal parts induced by a commutative square of
sheaves of rings together with a compatible linear map of module sheaves. -/
@[stacks 09CX "maps"]
noncomputable def principalPartsMapOfSquare
    (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (h : φ ≫ β = α ≫ φ')
    (F : _root_.SheafOfModules.{max u v w m} B)
    (F' : _root_.SheafOfModules.{max u v w m} B')
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    (k : ℕ) :
    moduleOfPrincipalParts.{v, u, w, m} φ F k ⟶
      (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj
        (moduleOfPrincipalParts.{v, u, w, m} φ' F' k) := by
  let T := differentialOperatorsFunctor.{v, u, w, m} φ F k
  let T' := differentialOperatorsFunctor.{v, u, w, m} φ' F' k
  let D : DiffOp.GlobalOp F
      ((_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj T'.coreprX) :=
    fun X ↦ (T'.coreprx.1 X).comp ((uF.val.app X).hom.toAddMonoidHom)
  have hD : DiffOp.IsGlobalDiffOpOfOrder φ k D := by
    intro U
    change DiffOp.IsDiffOpOfOrder φ k
      (precompRaw.{v, u, w, m} β F F' uF (T'.coreprx.1.restrict U))
    exact isDiffOpOfOrder_precompRaw.{v, u, w, m}
      (φ := φ) (φ' := φ') (β := β) (F := F) (F' := F') (k := k)
      (α := α) (h := h) uF (T'.coreprx.1.restrict U) (T'.coreprx.2 U)
  exact T.corepresentableBy.homEquiv.symm ⟨D, hD⟩

/-- The induced map sends each universal local generator to the generator associated to its
image under the module map. -/
@[stacks 09CX "maps"]
theorem principalPartsMapOfSquare_universalOperator (k : ℕ) (X : Cᵒᵖ) (s : F.val.obj X) :
    ((principalPartsMapOfSquare φ φ' α β h F F' uF k).val.app X).hom
      ((differentialOperatorsFunctor.{v, u, w, m} φ F k).coreprx.1 X s) =
      (differentialOperatorsFunctor.{v, u, w, m} φ' F' k).coreprx.1 X
        ((uF.val.app X).hom s) := by
  let T := differentialOperatorsFunctor.{v, u, w, m} φ F k
  let T' := differentialOperatorsFunctor.{v, u, w, m} φ' F' k
  let D : DiffOp.GlobalOp F
      ((_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj T'.coreprX) :=
    fun Y ↦ (T'.coreprx.1 Y).comp ((uF.val.app Y).hom.toAddMonoidHom)
  have hD : DiffOp.IsGlobalDiffOpOfOrder φ k D := by
    intro U
    change DiffOp.IsDiffOpOfOrder φ k
      (precompRaw.{v, u, w, m} β F F' uF (T'.coreprx.1.restrict U))
    exact isDiffOpOfOrder_precompRaw.{v, u, w, m}
      (φ := φ) (φ' := φ') (β := β) (F := F) (F' := F') (k := k)
      (α := α) (h := h) uF (T'.coreprx.1.restrict U) (T'.coreprx.2 U)
  have hmap : T.corepresentableBy.homEquiv
      (principalPartsMapOfSquare φ φ' α β h F F' uF k) =
        (⟨D, hD⟩ : T.obj
          ((_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj T'.coreprX)) :=
    T.corepresentableBy.homEquiv.apply_symm_apply _
  have hcomp := T.corepresentableBy.homEquiv_comp
    (principalPartsMapOfSquare φ φ' α β h F F' uF k) (𝟙 T.coreprX)
  rw [Category.id_comp, hmap] at hcomp
  have hop : D = postcomp T.coreprx.1
      (principalPartsMapOfSquare φ φ' α β h F F' uF k) := by
    have hh := congrArg Subtype.val hcomp
    change D = (homGlobalOp
      (principalPartsMapOfSquare φ φ' α β h F F' uF k)).comp T.coreprx.1 at hh
    exact hh
  have hEval := congrArg
    (fun q : DiffOp.GlobalOp F
      ((_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj T'.coreprX) => q X s)
    hop.symm
  change ((principalPartsMapOfSquare φ φ' α β h F F' uF k).val.app X).hom
      (T.coreprx.1 X s) = T'.coreprx.1 X ((uF.val.app X).hom s) at hEval
  exact hEval

/-- The induced maps commute with the canonical maps reducing the order from `k + 1` to `k`. -/
@[stacks 09CX "maps"]
theorem principalPartsMapOfSquare_comp_orderReduction (k : ℕ) :
    principalPartsOrderReduction.{v, u, w, m} φ F k ≫
        principalPartsMapOfSquare φ φ' α β h F F' uF k =
      principalPartsMapOfSquare φ φ' α β h F F' uF (k + 1) ≫
        (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
          (principalPartsOrderReduction.{v, u, w, m} φ' F' k) := by
  let T := differentialOperatorsFunctor.{v, u, w, m} φ F (k + 1)
  let f := principalPartsOrderReduction.{v, u, w, m} φ F k ≫
    principalPartsMapOfSquare φ φ' α β h F F' uF k
  let g := principalPartsMapOfSquare φ φ' α β h F F' uF (k + 1) ≫
    (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
      (principalPartsOrderReduction.{v, u, w, m} φ' F' k)
  apply T.corepresentableBy.homEquiv.injective
  rw [T.corepresentableBy.homEquiv_eq f, T.corepresentableBy.homEquiv_eq g]
  apply Subtype.ext
  funext X
  ext s
  change ((principalPartsMapOfSquare φ φ' α β h F F' uF k).val.app X).hom
      (((principalPartsOrderReduction.{v, u, w, m} φ F k).val.app X).hom
        (T.coreprx.1 X s)) =
    (((_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
      (principalPartsOrderReduction.{v, u, w, m} φ' F' k)).val.app X).hom
      (((principalPartsMapOfSquare φ φ' α β h F F' uF (k + 1)).val.app X).hom
        (T.coreprx.1 X s))
  rw [principalPartsOrderReduction_universalOperator φ F k X s,
    principalPartsMapOfSquare_universalOperator φ φ' α β h F F' uF k X s,
    principalPartsMapOfSquare_universalOperator φ φ' α β h F F' uF (k + 1) X s]
  symm
  exact principalPartsOrderReduction_universalOperator φ' F' k X ((uF.val.app X).hom s)

end AlgebraicGeometry.SheafOfModules

end

/-!
# Composition of the change-of-rings maps on principal parts

The map on sheaves of principal parts induced by a commuting square of sheaves of rings and a
compatible map of module sheaves is functorial: the map attached to a composite of two such
squares is the composite of the two maps, in every order `k`.

Both sides are maps out of the sheaf of principal parts of order `k`, which corepresents the
differential operators of order at most `k`, so they agree as soon as they agree after
composing with the universal operator — and there
`AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare_universalOperator` computes both to
the universal operator of the outer square applied to the composite module map.

## Main results

* `AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare_comp`: the composition law.

## Implementation notes

Restriction of scalars is used to regard each target sheaf of principal parts as a module over
the source coefficient sheaf; accordingly the composite of the two module maps is the first one
followed by the restriction of scalars of the second. The change-of-rings map itself is
`principalPartsMapOfSquare` of Tag 09CX, and the corepresenting functor is
`differentialOperatorsFunctor` of Tag 09CT.

This section supplies the composition clause of Tag 09CX; the maps themselves and their
compatibility with reduction of the order are
`AlgebraicGeometry.SheafOfModules.principalPartsMapOfSquare` and its companions above. The
remaining clause of the tag, compatibility with the short exact sequences of Tag 09CW, is
`StacksFrontier/CategoryTheory/Sites/Modules/PrincipalPartsSequenceNaturality.lean`.

## References

* [Stacks Project, Tag 09CX](https://stacks.math.columbia.edu/tag/09CX)
-/

@[expose] public section

open CategoryTheory

universe v u w m

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A B A' B' A'' B'' : Sheaf J RingCat.{w}}

/-- **Stacks 09CX.** The map on principal parts associated to two successive compatible squares
is the composite of their maps on principal parts. -/
@[stacks 09CX "composition of the maps"]
theorem principalPartsMapOfSquare_comp
    (φ : A ⟶ B) (φ' : A' ⟶ B') (φ'' : A'' ⟶ B'')
    (α : A ⟶ A') (β : B ⟶ B')
    (α' : A' ⟶ A'') (β' : B' ⟶ B'')
    (h : φ ≫ β = α ≫ φ') (h' : φ' ≫ β' = α' ≫ φ'')
    (F : _root_.SheafOfModules.{max u v w m} B)
    (F' : _root_.SheafOfModules.{max u v w m} B')
    (F'' : _root_.SheafOfModules.{max u v w m} B'')
    (uF : F ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj F')
    (uF' : F' ⟶ (_root_.SheafOfModules.restrictScalars.{max u v w m} β').obj F'')
    (k : ℕ) :
    principalPartsMapOfSquare.{v, u, w, m} φ φ'' (α ≫ α') (β ≫ β')
        (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])
        F F'' (uF ≫ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map uF') k =
      principalPartsMapOfSquare.{v, u, w, m} φ φ' α β h F F' uF k ≫
        (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
          (principalPartsMapOfSquare.{v, u, w, m} φ' φ'' α' β' h' F' F'' uF' k) := by
      set P := differentialOperatorsFunctor.{v, u, w, m} φ F k with hP
      have homEquiv_map (G : _root_.SheafOfModules.{max u v w m} B)
          (f : P.coreprX ⟶ G) : P.corepresentableBy.homEquiv f = P.map f P.coreprx := by
        simpa [Functor.coreprx] using
          (P.corepresentableBy.homEquiv_comp f (𝟙 P.coreprX))
      set G := (_root_.SheafOfModules.restrictScalars.{max u v w m} β).obj
        ((_root_.SheafOfModules.restrictScalars.{max u v w m} β').obj
          (differentialOperatorsFunctor.{v, u, w, m} φ'' F'' k).coreprX) with hG
      apply (P.corepresentableBy.homEquiv (Y := G)).injective
      refine (homEquiv_map G _).trans (Eq.trans ?_ (homEquiv_map G _).symm)
      apply Subtype.ext
      funext X
      apply AddMonoidHom.ext
      intro s
      change ((principalPartsMapOfSquare φ φ'' (α ≫ α') (β ≫ β')
        (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])
        F F''
        (uF ≫ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map uF') k).val.app X).hom
          ((P.coreprx).1 X s) =
        (((principalPartsMapOfSquare φ φ' α β h F F' uF k ≫
          (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
            (principalPartsMapOfSquare φ' φ'' α' β' h' F' F'' uF' k)).val.app X).hom)
          ((P.coreprx).1 X s)
      change ((principalPartsMapOfSquare φ φ'' (α ≫ α') (β ≫ β')
        (by rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])
        F F''
        (uF ≫ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map uF') k).val.app X).hom
          ((P.coreprx).1 X s) =
        (((_root_.SheafOfModules.restrictScalars.{max u v w m} β).map
          (principalPartsMapOfSquare φ' φ'' α' β' h' F' F'' uF' k)).val.app X).hom
          (((principalPartsMapOfSquare φ φ' α β h F F' uF k).val.app X).hom
            ((P.coreprx).1 X s))
      rw [principalPartsMapOfSquare_universalOperator]
      rw [principalPartsMapOfSquare_universalOperator]
      change ((differentialOperatorsFunctor.{v, u, w, m} φ'' F'' k).coreprx.1 X)
          (((uF ≫ (_root_.SheafOfModules.restrictScalars.{max u v w m} β).map uF').val.app X).hom
            s) =
        ((principalPartsMapOfSquare φ' φ'' α' β' h' F' F'' uF' k).val.app X).hom
          ((differentialOperatorsFunctor.{v, u, w, m} φ' F' k).coreprx.1 X
            ((uF.val.app X).hom s))
      exact (principalPartsMapOfSquare_universalOperator φ' φ'' α' β' h' F' F'' uF' k X
        ((uF.val.app X).hom s)).symm

end AlgebraicGeometry.SheafOfModules
