module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Contractibility of the extended Cech complex of a family containing the whole open

Let `X` be a topological space, `F` a presheaf of abelian groups on `X`, `U` an open of `X` and
`V : I → Opens X` a family of opens all contained in `U`. If one member of the family is `U`
itself, then the Cech complex of `F` for that family, extended by the canonical augmentation
from the sections of `F` over `U`, is homotopy equivalent to zero. This is Stacks 0G6S.

The contraction is the explicit one of the source: a cochain in Cech degree `n + 1` is sent to
the cochain in degree `n` obtained by inserting the index of the member equal to `U` in front,
which is legitimate because every member is contained in `U` and restriction along that
inclusion is the identity there. Together with the degree-zero case, which is the restriction
along the equality `V i = U`, these maps form a homotopy between the identity of the augmented
complex and zero.

## Main definitions

* `Stacks.Cech.cechAugmentation`: the canonical map from the sections of `F` over `U` to the
  degree-zero Cech cochains of the family.

## Main results

* `Stacks.Cech.cechComplex_augment_homotopyEquiv_zero_of_eq`: adjoining the canonical
  augmentation makes the Cech complex homotopy equivalent to zero as soon as one member of the
  family is `U`.

## Implementation notes

Mathlib's `CochainComplex.augment` puts the augmenting object in degree zero and shifts the
original nonnegative complex up by one, so it is the source's extended complex with all degrees
shifted up by one from the convention in which the augmenting object sits in degree `-1`.

The covering hypothesis is taken in the form `∀ i, V i ≤ U` together with `V i = U` for the
distinguished index, rather than as the equality `U = ⨆ i, V i`. The two are equivalent in the
presence of a member equal to `U`: the supremum equality gives `∀ i, V i ≤ U`, and conversely
`∀ i, V i ≤ U` with `V i = U` forces `⨆ i, V i = U`.

An abelian presheaf is `TopCat.Presheaf Ab X`, presheaves valued in the category of abelian
groups, which is the form Stacks 006K takes in this library.

## References

* [Stacks Project, Tag 0G6S](https://stacks.math.columbia.edu/tag/0G6S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cech

-- The Čech term in degree `n` is `((cechComplexFunctor V).obj F).X n` on one side and
-- `((FormalCoproduct.evalOp _ _).obj F).obj (op (_.cech.obj (op ⦋n⦌)))` on the other. The two
-- agree, but only after unfolding `FormalCoproduct.evalOp`, which is a semireducible `def`,
-- so a composite written with one spelling is not type-correct at `implicit` transparency
-- when read at the other, and `rw`/`simp only` refuse inside it. Mathlib already marks the
-- neighbouring `FormalCoproduct.cech` `@[implicit_reducible]` for exactly this reason; naming
-- the one remaining declaration here is the narrow form of that, in place of a file-scope
-- `backward.isDefEq.respectTransparency` option.
attribute [local implicit_reducible]
  FormalCoproduct.evalOp

/-- Insertion of the index `i` with `V i = U` in front: the map of Čech index objects
`⦋n⦌ → ⦋n + 1⦌` sending a family `a` of indices to `i, a 0, …, a n`, together with the
inclusion of opens it covers. -/
private noncomputable def insertIndex
    (X : TopCat.{u}) {I : Type u} {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ) :
    (FormalCoproduct.mk _ V).cech.obj (op {len := n}) ⟶
      (FormalCoproduct.mk _ V).cech.obj (op {len := n + 1}) where
  f a := fun j ↦ Fin.cases i a j
  φ a := by
    dsimp [FormalCoproduct.cech,
      FormalCoproduct.power]
    refine Pi.lift fun j ↦ Fin.cases ?_ (fun k ↦ Pi.π _ k) j
    exact homOfLE ((leOfHom (Pi.π (V ∘ a) 0)).trans (hV _) |>.trans_eq hi.symm)

/-- The contraction in positive Čech degree: restriction along `insertIndex`, taking a cochain
in degree `n + 1` to the cochain in degree `n` obtained by inserting the index `i` in front. -/
private noncomputable def contractionSucc
    (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) (n : ℕ) :
    ((cechComplexFunctor V).obj F).X (n + 1) ⟶
      ((cechComplexFunctor V).obj F).X n :=
  ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
    (insertIndex X V hV i hi n).op

/-- Inserting the index `i` and then deleting the zeroth entry is the identity. -/
private theorem insertIndex_comp_face_zero
    (X : TopCat.{u}) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ) :
    insertIndex X V hV i hi n ≫
      ((FormalCoproduct.mk _ V).cech.map
        (SimplexCategory.δ 0).op) = 𝟙 _ := by
  refine FormalCoproduct.hom_ext ?_ ?_
  · funext a
    funext j
    dsimp [insertIndex, FormalCoproduct.cech,
      FormalCoproduct.power,
      FormalCoproduct.mapPower, SimplexCategory.δ,
      SimplexCategory.mkHom]
    change Fin.cases i a (Fin.succAbove 0 j) = a j
    rw [Fin.succAbove_zero_apply]
    rfl
  · intro a
    exact Subsingleton.elim _ _

/-- Inserting the index `i` commutes with deleting an entry other than the zeroth, the index
of the deleted entry shifting by one across the insertion. -/
private theorem insertIndex_comp_face_succ
    (X : TopCat.{u}) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ)
    (k : Fin (n + 2)) :
    insertIndex X V hV i hi (n + 1) ≫
      ((FormalCoproduct.mk _ V).cech.map
        (SimplexCategory.δ k.succ).op) =
    ((FormalCoproduct.mk _ V).cech.map
        (SimplexCategory.δ k).op) ≫ insertIndex X V hV i hi n := by
  refine FormalCoproduct.hom_ext ?_ ?_
  · funext a
    funext j
    dsimp [insertIndex, FormalCoproduct.cech,
      FormalCoproduct.power,
      FormalCoproduct.mapPower, SimplexCategory.δ,
      SimplexCategory.mkHom]
    change Fin (n + 2) at j
    change (Fin.cases i a : Fin (n + 3) → I) (Fin.succAbove k.succ j) =
      (Fin.cases i (a ∘ Fin.succAbove k) : Fin (n + 2) → I) j
    by_cases hj : j = 0
    · subst j
      simp only [Fin.succ_succAbove_zero]
      exact Fin.cases_zero (motive := fun _ => I) (zero := i) (succ := a)
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      simp only [Fin.succ_succAbove_succ]
      exact Fin.cases_succ (motive := fun _ => I) (zero := i) (succ := a)
        (k.succAbove j)
  · intro a
    exact Subsingleton.elim _ _

/-- The degree-zero insertion: the map from the one-point formal coproduct on `U` to the
degree-zero Čech index object picking out the index `i`, covered by the equality `V i = U`. -/
private noncomputable def insertIndexZero
    (X : TopCat.{u}) {I : Type u} {U : Opens X}
    (V : I → Opens X) (i : I) (hi : V i = U) :
    FormalCoproduct.mk PUnit (fun _ ↦ U) ⟶
      (FormalCoproduct.mk _ V).cech.obj (op {len := 0}) where
  f _ := fun _ ↦ i
  φ _ := by
    dsimp [FormalCoproduct.cech,
      FormalCoproduct.power]
    exact Pi.lift fun _ ↦ eqToHom hi.symm

/-- The contraction in Čech degree zero: restriction along `insertIndexZero`, taking a
degree-zero cochain to its value at the index `i`, read on `U` through `V i = U`. -/
private noncomputable def contractionZero
    (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (i : I) (hi : V i = U) :
    ((cechComplexFunctor V).obj F).X 0 ⟶ F.obj (op U) :=
  ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
    (insertIndexZero X V i hi).op ≫ Pi.π _ PUnit.unit

/-- The component of `FormalCoproduct.evalOp`'s action on a morphism of formal coproducts:
restricting along `f` and then projecting to the factor `a` is projecting to the factor
`f.f a` and then restricting along `f.φ a`. -/
private theorem evalOp_map_comp_projection {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X)
    {A B : FormalCoproduct (Opens X)}
    (f : A ⟶ B) (a : A.I) :
    ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map f.op ≫
        Pi.π (fun b : A.I => F.obj (op (A.obj b))) a =
      Pi.π (fun b : B.I => F.obj (op (B.obj b))) (f.f a) ≫
        F.map (f.φ a).op := by
  simp [FormalCoproduct.evalOp]

/-- The canonical map from sections on `U` to degree-zero Čech cochains for a family of open
subsets of `U`. Its component at `i : Fin 1 → I` is restriction to the one-fold intersection
indexed by `i`. -/
noncomputable def cechAugmentation (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    F.obj (op U) ⟶ ((cechComplexFunctor V).obj F).X 0 :=
  Pi.lift fun i ↦ F.map (Pi.π (fun j ↦ V (i j)) 0 ≫ homOfLE (hV (i 0))).op

/-- The map of index objects underlying the augmentation: the degree-zero Čech index object
maps to the one-point formal coproduct on `U`, covered by the inclusion `V (a 0) ≤ U`. -/
private noncomputable def cechAugmentationIndex {X : TopCat.{u}}
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    (FormalCoproduct.mk _ V).cech.obj (op {len := 0}) ⟶
      FormalCoproduct.mk PUnit (fun _ ↦ U) where
  f _ := PUnit.unit
  φ a := Pi.π (fun j : Fin 1 ↦ V (a j)) 0 ≫ homOfLE (hV (a 0))

/-- The augmentation index map followed by the degree-zero insertion is the insertion
followed by deletion of the first entry. -/
private theorem cechAugmentationIndex_comp_insertIndexZero {X : TopCat.{u}}
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) :
    cechAugmentationIndex V hV ≫ insertIndexZero X V i hi =
      insertIndex X V hV i hi 0 ≫
        ((FormalCoproduct.mk _ V).cech.map
          (SimplexCategory.δ 1).op) := by
  refine FormalCoproduct.hom_ext ?_ ?_
  · funext a
    funext j
    dsimp [cechAugmentationIndex, insertIndexZero, insertIndex,
      FormalCoproduct.cech,
      FormalCoproduct.power,
      FormalCoproduct.mapPower,
      SimplexCategory.δ, SimplexCategory.mkHom]
    fin_cases j
    rfl
  · intro a
    exact Subsingleton.elim _ _

/-- The degree-zero insertion is a section of the augmentation index map: the index
components are inverse and the covering morphisms of opens are unique. -/
private theorem insertIndexZero_comp_cechAugmentationIndex {X : TopCat.{u}}
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) :
    insertIndexZero X V i hi ≫ cechAugmentationIndex V hV = 𝟙 _ := by
  refine FormalCoproduct.hom_ext rfl ?_
  intro a
  exact Subsingleton.elim _ _

/-- Either coface map followed by the augmentation index map gives the same morphism of
formal coproducts: the index components are both constant at `PUnit.unit`, and the covering
morphisms of opens are unique. -/
private theorem face_comp_cechAugmentationIndex {X : TopCat.{u}}
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U) (k l : Fin 2) :
    (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ k).op ≫
        cechAugmentationIndex V hV =
      (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ l).op ≫
        cechAugmentationIndex V hV := by
  refine FormalCoproduct.hom_ext rfl ?_
  intro a
  exact Subsingleton.elim _ _

/-- The sections of `F` over `U` as the evaluation of `F` on the one-point formal coproduct
on `U`. -/
private noncomputable def cechSingletonLift {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {U : Opens X} :
    F.obj (op U) ⟶
      ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).obj
        (op (FormalCoproduct.mk PUnit (fun _ ↦ U))) :=
  Pi.lift fun _ ↦ 𝟙 _

/-- The augmentation is the evaluation of `F` on `cechAugmentationIndex`, read through
`cechSingletonLift`. This is what lets the augmentation be composed with coface maps by
functoriality rather than componentwise. -/
private theorem cechAugmentation_eq_eval {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    cechAugmentation X F V hV =
      cechSingletonLift F ≫
        ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
          (cechAugmentationIndex V hV).op := by
  apply Pi.hom_ext
  intro a
  rw [cechAugmentation, Pi.lift_π, Category.assoc]
  have hEval :
      ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
          (cechAugmentationIndex V hV).op ≫
        Pi.π
          (fun b : (unop ((Functor.rightOp
            (FormalCoproduct.mk _ V).cech).obj {len := 0})).I =>
            F.obj (op ((unop ((Functor.rightOp
              (FormalCoproduct.mk _ V).cech).obj {len := 0})).obj b))) a =
        Pi.π
            (fun b => F.obj (op
              ((FormalCoproduct.mk PUnit (fun _ ↦ U)).obj b)))
            ((cechAugmentationIndex V hV).f a) ≫
          F.map ((cechAugmentationIndex V hV).φ a).op := by
    simp [FormalCoproduct.cech]
  rw [hEval]
  simp only [cechSingletonLift, cechAugmentationIndex, Pi.lift_π_assoc,
    Category.id_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The `k`-th coface map of the Čech complex: restriction along the map of index objects
that deletes the `k`-th entry. -/
private noncomputable def cechFaceMap {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} (V : I → Opens X) (n : ℕ)
    (k : Fin (n + 2)) :
    ((cechComplexFunctor V).obj F).X n ⟶
      ((cechComplexFunctor V).obj F).X (n + 1) :=
  ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
    (((FormalCoproduct.mk _ V).cech.map
      (SimplexCategory.δ k).op).op)

/-- The two routes from Čech degree zero back to itself through degree one agree. -/
private theorem contractionZero_comp_augmentation_eq_face_one_comp_contractionSucc
    {X : TopCat.{u}} (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X}
    (V : I → Opens X) (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) :
    contractionZero X F V i hi ≫ cechAugmentation X F V hV =
      cechFaceMap F V 0 1 ≫ contractionSucc X F V hV i hi 0 := by
  let G := (FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F
  have hunit :
      Pi.π
          (fun _ : PUnit => F.obj (op U)) PUnit.unit ≫ cechSingletonLift F =
    𝟙 (G.obj (op (FormalCoproduct.mk PUnit (fun _ ↦ U)))) := by
    apply Pi.hom_ext
    intro j
    simp [cechSingletonLift, G, FormalCoproduct.evalOp]
  rw [cechAugmentation_eq_eval]
  change
    G.map (insertIndexZero X V i hi).op ≫
        Pi.π (fun _ : PUnit => F.obj (op U)) PUnit.unit ≫
        cechSingletonLift F ≫ G.map (cechAugmentationIndex V hV).op =
      G.map (((FormalCoproduct.mk _ V).cech.map
        (SimplexCategory.δ (1 : Fin 2)).op).op) ≫
        G.map (insertIndex X V hV i hi 0).op
  calc
    _ = G.map (insertIndexZero X V i hi).op ≫
        (Pi.π (fun _ : PUnit => F.obj (op U)) PUnit.unit ≫
          cechSingletonLift F) ≫ G.map (cechAugmentationIndex V hV).op := by
      simp only [Category.assoc]
    _ = G.map (insertIndexZero X V i hi).op ≫ 𝟙 _ ≫
        G.map (cechAugmentationIndex V hV).op := by rw [hunit]
    _ = G.map (insertIndexZero X V i hi).op ≫
        G.map (cechAugmentationIndex V hV).op := by simp
    _ = G.map (cechAugmentationIndex V hV ≫ insertIndexZero X V i hi).op := by
      rw [← Functor.map_comp]
      rfl
    _ = G.map (insertIndex X V hV i hi 0 ≫
        (FormalCoproduct.mk _ V).cech.map
          (SimplexCategory.δ (1 : Fin 2)).op).op := by
      rw [cechAugmentationIndex_comp_insertIndexZero V hV i hi]
    _ = G.map (((FormalCoproduct.mk _ V).cech.map
        (SimplexCategory.δ (1 : Fin 2)).op).op) ≫
        G.map (insertIndex X V hV i hi 0).op := by
      rw [← Functor.map_comp]
      rfl

/-- The contraction commutes with every coface map except the zeroth. -/
private theorem contractionSucc_comp_face_succ {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ)
    (k : Fin (n + 2)) :
    contractionSucc X F V hV i hi n ≫ cechFaceMap F V n k =
      cechFaceMap F V (n + 1) k.succ ≫ contractionSucc X F V hV i hi (n + 1) := by
  refine Eq.trans
    (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_comp _ _).symm
    (Eq.trans ?_ (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_comp _ _))
  exact congrArg
    (fun f => ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map (Quiver.Hom.op f))
    (insertIndex_comp_face_succ X V hV i hi n k).symm

/-- The zeroth coface map followed by the contraction is the identity. -/
private theorem contractionSucc_comp_face_zero {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ) :
    cechFaceMap F V n 0 ≫ contractionSucc X F V hV i hi n = 𝟙 _ := by
  refine Eq.trans
    (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_comp _ _).symm
    (Eq.trans ?_ (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_id _))
  exact congrArg
    (fun f => ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map (Quiver.Hom.op f))
    (insertIndex_comp_face_zero X V hV i hi n)

/-- The differential of the Čech complex in degree `n` is the alternating coface-map sum of the
underlying cosimplicial object.

This is not `rfl`: `CochainComplex.of.d` is a `dite` on `n + 1 = n + 1`, whose `Decidable`
instance is `Nat.decEq n n`, which does not reduce for a variable `n`. The `dite` is discharged
by `CochainComplex.of_d`, reached from the complex through the simp lemma
`FormalCoproduct.cochainComplexFunctor_obj_d`. -/
private theorem cechComplex_d_eq_objD {X : TopCat.{u}} (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} (V : I → Opens X) (n : ℕ) :
    ((cechComplexFunctor V).obj F).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ V).cech).obj F) n :=
  (FormalCoproduct.cochainComplexFunctor_obj_d
      (FormalCoproduct.mk _ V).cech F n (n + 1)).trans
    (CochainComplex.of_d _ _ n)

/-- The Čech differential is the alternating sum of the coface maps. -/
private theorem cechDifferential_eq_sum {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} (V : I → Opens X) (n : ℕ) :
    ((cechComplexFunctor V).obj F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • cechFaceMap F V n k := by
  rw [cechComplex_d_eq_objD F V n, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rfl

/-- In degree zero the Čech differential is the difference of the two coface maps. -/
private theorem cechDifferential_zero {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} (V : I → Opens X) :
    ((cechComplexFunctor V).obj F).d 0 1 =
      cechFaceMap F V 0 0 - cechFaceMap F V 0 1 := by
  rw [cechDifferential_eq_sum]
  simp
  abel

/-- Composing the augmentation with a degree-zero coface map does not depend on which of the
two coface maps is used: both compositions factor through the one-point formal coproduct, where
the remaining data is a morphism of opens and hence unique. -/
private theorem cechAugmentation_comp_cechFaceMap {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (k l : Fin 2) :
    cechAugmentation X F V hV ≫ cechFaceMap F V 0 k =
      cechAugmentation X F V hV ≫ cechFaceMap F V 0 l := by
  have e : ∀ m : Fin 2,
      cechAugmentation X F V hV ≫ cechFaceMap F V 0 m =
        cechSingletonLift F ≫ ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
          (((FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ m).op ≫
            cechAugmentationIndex V hV).op) := fun m =>
    (congrArg (fun z => z ≫ cechFaceMap F V 0 m)
        (cechAugmentation_eq_eval F V hV)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => cechSingletonLift F ≫ z)
          (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_comp _ _).symm))
  refine (e k).trans (Eq.trans ?_ (e l).symm)
  exact congrArg
    (fun g => cechSingletonLift F ≫
      ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map (Quiver.Hom.op g))
    (face_comp_cechAugmentationIndex V hV k l)

/-- The contraction in degree zero is a section of the augmentation. -/
private theorem cechAugmentation_comp_contractionZero {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) :
    cechAugmentation X F V hV ≫ contractionZero X F V i hi = 𝟙 (F.obj (op U)) := by
  have key : ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
        ((cechAugmentationIndex V hV).op ≫ (insertIndexZero X V i hi).op) = 𝟙 _ :=
    (congrArg
        (fun g => ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map (Quiver.Hom.op g))
        (insertIndexZero_comp_cechAugmentationIndex V hV i hi)).trans
      (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map_id _)
  have step :
      cechSingletonLift F ≫ ((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
          (cechAugmentationIndex V hV).op ≫
          (((FormalCoproduct.evalOp (Opens X) Ab.{u}).obj F).map
            (insertIndexZero X V i hi).op ≫
            Pi.π (fun _ : PUnit => F.obj (op U)) PUnit.unit) =
        cechSingletonLift F ≫ Pi.π (fun _ : PUnit => F.obj (op U)) PUnit.unit := by
    rw [← Functor.map_comp_assoc, key, Category.id_comp]
  refine Eq.trans (congrArg (fun z => z ≫ contractionZero X F V i hi)
    (cechAugmentation_eq_eval F V hV)) ?_
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans step ?_)
  simp [cechSingletonLift]

/-- The homotopy identity above Čech degree zero: all terms of the two alternating sums
cancel in pairs except the one coming from the zeroth coface map, which gives the identity. -/
private theorem cechContraction_succ_identity {X : TopCat.{u}}
    (F : TopCat.Presheaf Ab.{u} X) {I : Type u} {U : Opens X} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (i : I) (hi : V i = U) (n : ℕ) :
    contractionSucc X F V hV i hi n ≫
        ((cechComplexFunctor V).obj F).d n (n + 1) +
      ((cechComplexFunctor V).obj F).d (n + 1) (n + 2) ≫
        contractionSucc X F V hV i hi (n + 1) = 𝟙 _ := by
  rw [cechDifferential_eq_sum F V n, cechDifferential_eq_sum F V (n + 1)]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  conv_lhs =>
    arg 2
    rw [Fin.sum_univ_succ]
  rw [contractionSucc_comp_face_zero]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  have hsum :
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (contractionSucc X F V hV i hi n ≫ cechFaceMap F V n k)) +
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ ((k : ℕ) + 1) •
          (cechFaceMap F V (n + 1) k.succ ≫
            contractionSucc X F V hV i hi (n + 1)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    rw [contractionSucc_comp_face_succ]
    simp [pow_succ]
  simp only [Fin.val_succ]
  conv_lhs =>
    arg 2
    rw [add_comm]
  rw [← add_assoc, hsum]
  simp

/-- In Čech degree zero the augmentation composed with the differential vanishes. -/
private theorem cechAugmentation_comp_d_zero {X : TopCat.{u}} (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U) :
    cechAugmentation X F V hV ≫ ((cechComplexFunctor V).obj F).d 0 1 = 0 := by
  rw [cechDifferential_zero F V, Preadditive.comp_sub, sub_eq_zero]
  exact cechAugmentation_comp_cechFaceMap F V hV 0 1

/-- The contracting homotopy of the augmented Čech complex of a family containing `U`. -/
private noncomputable def cechAugmentHomotopy (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U)
    (w : cechAugmentation X F V hV ≫ ((cechComplexFunctor V).obj F).d 0 1 = 0) :
    Homotopy (𝟙 (((cechComplexFunctor V).obj F).augment (cechAugmentation X F V hV) w)) 0 := by
  let K := (cechComplexFunctor V).obj F
  subst U
  have hi : V i = V i := rfl
  let L := K.augment (cechAugmentation X F V hV) w
  let hzero : L.X 1 ⟶ L.X 0 := contractionZero X F V i hi
  let hone : L.X 2 ⟶ L.X 1 := contractionSucc X F V hV i hi 0
  have hz : (𝟙 L : L ⟶ L).f 0 = L.d 0 1 ≫ hzero :=
    (cechAugmentation_comp_contractionZero F V hV i hi).symm
  have ho : (𝟙 L : L ⟶ L).f 1 = hzero ≫ L.d 0 1 + L.d 1 2 ≫ hone := by
    change 𝟙 (K.X 0) =
      contractionZero X F V i hi ≫ cechAugmentation X F V hV +
        K.d 0 1 ≫ contractionSucc X F V hV i hi 0
    rw [contractionZero_comp_augmentation_eq_face_one_comp_contractionSucc,
      cechDifferential_zero F V, Preadditive.sub_comp, contractionSucc_comp_face_zero]
    simp
    rfl
  let hComp : ∀ n, L.X (n + 1) ⟶ L.X n := fun n ↦
    match n with
    | 0 => hzero
    | m + 1 => contractionSucc X F V hV i hi m
  let hMap : ∀ n j, L.X n ⟶ L.X j := fun n j ↦
    if hj : j + 1 = n then hj ▸ hComp j else 0
  exact {
    hom := hMap
    zero := by
      intro n j hj
      dsimp [hMap]
      split_ifs with h
      · have hr : (ComplexShape.up ℕ).Rel j n := by
          rw [← h]
          simp [ComplexShape.up]
        exact (hj hr).elim
      · rfl
    comm := by
      intro n
      change (𝟙 L : L ⟶ L).f n =
        dNext n hMap + prevD n hMap + (0 : L ⟶ L).f n
      rw [HomologicalComplex.zero_f, add_zero]
      rcases n with _ | _ | n
      · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex]
        simpa [hMap, hComp] using hz
      · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        simpa [hMap, hComp, add_comm, CochainComplex.augment_d_succ_succ] using ho
      · rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        refine Eq.trans ?_ (add_comm _ _)
        simp only [K, L, hMap, hComp, CochainComplex.augment_X_succ,
          CochainComplex.augment_d_succ_succ, HomologicalComplex.id_f, dite_eq_left]
        exact (cechContraction_succ_identity F V hV i hi n).symm
    }

/-- If a family of open subsets of `U` contains `U`, its extended Čech complex is homotopy
equivalent to zero. The existential proof is precisely the fact that the canonical augmentation
squares to zero; the resulting augmented complex is independent of that proof by proof
irrelevance. -/
@[stacks 0G6S]
lemma cechComplex_augment_homotopyEquiv_zero_of_eq
    (X : TopCat.{u}) (F : TopCat.Presheaf Ab.{u} X)
    {I : Type u} {U : Opens X} (V : I → Opens X) (hV : ∀ i, V i ≤ U)
    (i : I) (hi : V i = U) :
    ∃ (w : cechAugmentation X F V hV ≫
        ((cechComplexFunctor V).obj F).d 0 1 = 0),
      Nonempty (HomotopyEquiv
        (((cechComplexFunctor V).obj F).augment
          (cechAugmentation X F V hV) w)
        (HomologicalComplex.zero : CochainComplex Ab.{u} ℕ)) := by
  let w := cechAugmentation_comp_d_zero F V hV
  refine ⟨w, ⟨?_⟩⟩
  exact
    { hom := 0
      inv := 0
      homotopyHomInvId := by simpa using (cechAugmentHomotopy X F V hV i hi w).symm
      homotopyInvHomId := Homotopy.ofEq (by
        ext i
        dsimp [HomologicalComplex.zero]
        let _ : Subsingleton _ :=
          AddCommGrpCat.isZero_iff_subsingleton.mp
            (isZero_zero (C := AddCommGrpCat))
        exact Subsingleton.elim _ _)
    }

end Stacks.Cech

end
