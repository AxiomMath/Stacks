module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsOrder
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Differential operators and principal parts for sheaves of modules

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of rings on a site. A differential operator of
order at most `k` between sheaves of `O₂`-modules is an `O₁`-linear map on local sections
whose commutator with every local section of `O₂` is a differential operator of order at most
`k - 1`; at order zero this means an `O₂`-linear map. For a fixed sheaf `F` of `O₂`-modules,
the differential operators of order at most `k` out of `F` form a covariant functor of the
target module, and this functor is represented by a sheaf of modules, the sheaf of principal
parts.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.homGlobalOp`: a morphism of sheaves of modules, regarded
  as an operator on local sections.
* `AlgebraicGeometry.SheafOfModules.postcomp`: postcomposition of an operator on local
  sections with a morphism of sheaves of modules.
* `AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor` sends a sheaf of
  `O₂`-modules `G` to the type of differential operators of order at most `k` from `F` to
  `G`.

## Main results

* `AlgebraicGeometry.SheafOfModules.homGlobalOp_isOrderZero`: a morphism of sheaves of
  modules is a differential operator of order zero.
* `AlgebraicGeometry.SheafOfModules.postcomp_isDiffOpOfOrder`: postcomposing with a morphism
  of sheaves of modules does not raise the order of a differential operator.
* `AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor_isCorepresentable`: the
  sheaf of principal parts, together with its universal property.

## Implementation notes

The identification of differential operators of order at most `k` out of `F` with module
homomorphisms out of a single sheaf of modules, canonically and naturally in the target
module, is expressed by corepresentability. Thus Mathlib's `Functor.coreprX` is the sheaf of
principal parts and `Functor.corepresentableBy` is the canonical natural isomorphism. The
functor acts on morphisms by pointwise postcomposition. Its module-sheaf universe is at least
as large as the universes of the site and of the coefficient sheaves, so the representing
sheaf need not be smaller than the data from which it is constructed.

The construction quotients the free modules on local sections by the intersection of the
kernels of all differential operators, and then sheafifies. The quotient evaluations jointly
detect equality, so they detect the recursive order condition. Because the recursion runs
through presheaves of modules, the order condition is restated for presheaves as
`presheafOrder`, which agrees with `DiffOp.IsDiffOpOfOrder` on sheaves.

## References

* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
* [Stacks Project, Tag 09CT](https://stacks.math.columbia.edu/tag/09CT)
* [Stacks Project, Tag 0G3Q](https://stacks.math.columbia.edu/tag/0G3Q)
-/

@[expose] public section

open CategoryTheory Opposite

add_to_stacks 09CR DiffOp.IsGlobalDiffOpOfOrder
add_to_stacks 0G3Q DiffOp.IsGlobalDiffOpOfOrder
add_to_stacks 0G3X "differential operators on X/S, for the map f♯ : f⁻¹𝒪_S ⟶ 𝒪_X"
  DiffOp.IsGlobalDiffOpOfOrder

universe v u w m n

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J RingCat.{w}}

/-- A morphism of sheaves of modules, regarded as an additive operator on sections. -/
def homGlobalOp {F G : _root_.SheafOfModules.{m} O₂} (f : F ⟶ G) :
    DiffOp.GlobalOp F G :=
  fun X ↦ (f.val.app X).hom.toAddMonoidHom

/-- A morphism of sheaves of modules is a differential operator of order zero. -/
lemma homGlobalOp_isOrderZero (phi : O₁ ⟶ O₂)
    {F G : _root_.SheafOfModules.{m} O₂}
    (f : F ⟶ G) : DiffOp.IsGlobalDiffOpOfOrder phi 0 (homGlobalOp f) := by
  intro U
  refine ⟨?_, ?_⟩
  · intro Y Y' h s
    exact congrArg (fun q ↦ q.hom s) (f.val.naturality h.left.op)
  · intro Y r s
    exact (f.val.app (op Y.left)).hom.map_smul r s

/-- Postcomposition of a global additive operator with a morphism of module sheaves. -/
def postcomp {F G H : _root_.SheafOfModules.{m} O₂}
    (D : DiffOp.GlobalOp F G) (f : G ⟶ H) :
    DiffOp.GlobalOp F H :=
  (homGlobalOp f).comp D

/-- Postcomposition by a module morphism preserves the order of a differential operator. -/
lemma postcomp_isDiffOpOfOrder (phi : O₁ ⟶ O₂) (k : ℕ)
    {F G H : _root_.SheafOfModules.{m} O₂} (D : DiffOp.GlobalOp F G)
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D) (f : G ⟶ H) :
    DiffOp.IsGlobalDiffOpOfOrder phi k (postcomp D f) := by
  change DiffOp.IsGlobalDiffOpOfOrder phi k ((homGlobalOp f).comp D)
  exact DiffOp.isGlobalDiffOpOfOrder_comp phi D (homGlobalOp f) hD
    (homGlobalOp_isOrderZero phi f)

/-- The covariant functor of differential operators of order at most `k` out of `F`.
Its action on a morphism of target modules is postcomposition. -/
@[sga "3 VIIA 1.4" "more general"]
def differentialOperatorsFunctor (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂)
    (k : ℕ) : _root_.SheafOfModules.{max u v w m} O₂ ⥤ Type (max u v w m) where
  obj G := {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}
  map {G H} f := TypeCat.ofHom (fun
      (D : {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}) ↦
    (⟨postcomp D.1 f, postcomp_isDiffOpOfOrder phi k D.1 D.2 f⟩ :
      {D : DiffOp.GlobalOp F H // DiffOp.IsGlobalDiffOpOfOrder phi k D}))
  map_id G := by
    ext D
    funext X
    ext x
    rfl
  map_comp f g := by
    ext D
    funext X
    ext x
    rfl

/-- A target module for differential operators of order at most `k` out of `F`, together
with such an operator into it. -/
private abbrev OperatorTarget (phi : O₁ ⟶ O₂) (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) :=
  Σ G : _root_.SheafOfModules.{m} O₂,
    {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}

/-- The restriction map of the presheaf of free modules on the local sections of `F`, as a
semilinear map along the restriction map of `O₂`. -/
private noncomputable def freeSectionMap (F : _root_.SheafOfModules.{m} O₂)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((F.val.obj X) →₀ (O₂.obj.obj X)) →ₛₗ[(O₂.obj.map f).hom]
      ((F.val.obj Y) →₀ (O₂.obj.obj Y)) :=
  (Finsupp.lmapDomain _ _ (fun s ↦ F.val.map f s)).comp
    (Finsupp.mapRange.linearMap (O₂.obj.map f).hom.toSemilinearMap)

/-- The restriction map of the free modules sends a generator to a generator. -/
private lemma freeSectionMap_single (F : _root_.SheafOfModules.{m} O₂)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.val.obj X) (r : O₂.obj.obj X) :
    freeSectionMap F f (Finsupp.single s r) =
      Finsupp.single (α := F.val.obj Y) (F.val.map f s) (O₂.obj.map f r) := by
  change Finsupp.mapDomain (fun t ↦ F.val.map f t)
    (Finsupp.mapRange (O₂.obj.map f).hom (map_zero _) (Finsupp.single s r)) = _
  simp; rfl

/-- A differential operator of any order is compatible with restriction. -/
private lemma operator_naturality {phi : O₁ ⟶ O₂} {F G : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} {D : DiffOp.GlobalOp F G} (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.val.obj X) :
    D Y (F.val.map f s) = G.val.map f (D X s) := by
  have h : (D.restrict X.unop).IsNatural := by
    cases k <;> exact (hD X.unop).1
  exact h (Over.mk f.unop) (Over.mk (𝟙 X.unop))
    (Over.homMk f.unop (by simp)) s

/-- Evaluation of a differential operator on the free module of local sections of `F`. -/
private noncomputable abbrev freeEvaluation {phi : O₁ ⟶ O₂}
    {F : _root_.SheafOfModules.{m} O₂} {k : ℕ} (i : OperatorTarget phi F k) (X : Cᵒᵖ) :=
  Finsupp.linearCombination (O₂.obj.obj X) (i.2.1 X)

/-- Evaluation of a differential operator on a generator of the free module. -/
private lemma freeEvaluation_single {phi : O₁ ⟶ O₂} {F : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} (i : OperatorTarget phi F k) (X : Cᵒᵖ) (s : F.val.obj X) (r : O₂.obj.obj X) :
    freeEvaluation i X (Finsupp.single s r) = r • i.2.1 X s := by
  simp

/-- Evaluation of a differential operator on the free modules is compatible with
restriction. -/
private lemma freeEvaluation_map {phi : O₁ ⟶ O₂} {F : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} (i : OperatorTarget phi F k) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.val.obj X →₀ O₂.obj.obj X) :
    freeEvaluation i Y (freeSectionMap F f x) =
      i.1.val.map f (freeEvaluation i X x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp; rfl
  | add x y hx hy => simp [hx, hy]; rfl
  | single s r =>
      have h1 : freeEvaluation i Y (freeSectionMap F f (Finsupp.single s r)) =
          O₂.obj.map f r • i.2.1 Y (F.val.map f s) :=
        (congrArg (freeEvaluation i Y) (freeSectionMap_single F f s r)).trans
          (freeEvaluation_single i Y _ _)
      have h2 : i.1.val.map f (freeEvaluation i X (Finsupp.single s r)) =
          O₂.obj.map f r • i.2.1 Y (F.val.map f s) := by
        rw [freeEvaluation_single, PresheafOfModules.map_smul,
          operator_naturality i.2.2]
        rfl
      exact h1.trans h2.symm

/-- The submodule of relations imposed on the free module of local sections of `F` by all
differential operators of order at most `k`. -/
private noncomputable def principalRelations (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) (X : Cᵒᵖ) :
    Submodule (O₂.obj.obj X) (F.val.obj X →₀ O₂.obj.obj X) :=
  ⨅ i : OperatorTarget phi F k, (freeEvaluation i X).ker

/-- The sections over `X` of the presheaf of principal parts of order at most `k`. -/
private noncomputable abbrev principalSection (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) (X : Cᵒᵖ) :=
  (F.val.obj X →₀ O₂.obj.obj X) ⧸ principalRelations phi F k X

/-- The map on sections induced by a differential operator of order at most `k`. -/
private noncomputable def sectionEvaluation {phi : O₁ ⟶ O₂}
    {F : _root_.SheafOfModules.{m} O₂} {k : ℕ} (i : OperatorTarget phi F k) (X : Cᵒᵖ) :
    principalSection phi F k X →ₗ[O₂.obj.obj X] i.1.val.obj X :=
  (principalRelations phi F k X).liftQ (freeEvaluation i X) (iInf_le _ i)

/-- The induced map on sections computes the differential operator on representatives. -/
private lemma sectionEvaluation_mk {phi : O₁ ⟶ O₂} {F : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} (i : OperatorTarget phi F k) (X : Cᵒᵖ)
    (x : F.val.obj X →₀ O₂.obj.obj X) :
    sectionEvaluation i X (Submodule.Quotient.mk x) = freeEvaluation i X x := rfl

/-- The induced maps on sections jointly detect equality. -/
private lemma principalSection_ext {phi : O₁ ⟶ O₂} {F : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} {X : Cᵒᵖ} (x y : principalSection phi F k X)
    (h : ∀ i : OperatorTarget phi F k, sectionEvaluation i X x = sectionEvaluation i X y) :
    x = y := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  apply (Submodule.Quotient.eq _).2
  simp only [principalRelations, Submodule.mem_iInf, LinearMap.mem_ker, map_sub, sub_eq_zero]
  intro i
  exact (sectionEvaluation_mk i X x).symm.trans ((h i).trans (sectionEvaluation_mk i X y))

/-- The restriction map of the presheaf of principal parts of order at most `k`. -/
private noncomputable def principalSectionMap (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    principalSection phi F k X →ₛₗ[(O₂.obj.map f).hom] principalSection phi F k Y :=
  (principalRelations phi F k X).mapQ (principalRelations phi F k Y)
    (freeSectionMap F f) (by
      intro x hx
      change freeSectionMap F f x ∈ principalRelations phi F k Y
      simp only [principalRelations, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
      intro i
      rw [freeEvaluation_map, hx i]
      exact map_zero _)

/-- The induced maps on sections are compatible with restriction. -/
private lemma sectionEvaluation_map {phi : O₁ ⟶ O₂} {F : _root_.SheafOfModules.{m} O₂}
    {k : ℕ} (i : OperatorTarget phi F k) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : principalSection phi F k X) :
    sectionEvaluation i Y (principalSectionMap phi F k f x) =
      i.1.val.map f (sectionEvaluation i X x) := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  exact freeEvaluation_map i f x

/-- The presheaf of principal parts of order at most `k`: the free modules on the local
sections of `F`, modulo the relations imposed by all differential operators of order at
most `k`. -/
private noncomputable def principalPresheaf (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) : PresheafOfModules.{max w m} O₂.obj where
  obj X := ModuleCat.of _ (principalSection phi F k X)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (O₂.obj.map f).hom).obj
      (ModuleCat.of _ (principalSection phi F k Y)))
    { toFun := principalSectionMap phi F k f
      map_add' := map_add _
      map_smul' := (principalSectionMap phi F k f).map_smul' }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply principalSection_ext
    intro i
    change sectionEvaluation i X (principalSectionMap phi F k (𝟙 X) x) =
      sectionEvaluation i X x
    rw [sectionEvaluation_map]
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply principalSection_ext
    intro i
    change sectionEvaluation i _ (principalSectionMap phi F k (f ≫ g) x) =
      sectionEvaluation i _ (principalSectionMap phi F k g
        (principalSectionMap phi F k f x))
    simp only [sectionEvaluation_map, PresheafOfModules.map_comp_apply]
    rfl

/-- The universal operator into the presheaf of principal parts: a local section of `F` is
sent to the class of the corresponding generator. -/
private noncomputable def principalGenerator (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) (X : Cᵒᵖ) :
    F.val.obj X →+ (principalPresheaf phi F k).obj X where
  toFun s := Submodule.Quotient.mk (Finsupp.single s 1)
  map_zero' := by
    refine principalSection_ext _ _ fun i ↦ ?_
    rw [sectionEvaluation_mk, freeEvaluation_single, one_smul, map_zero]
    exact (map_zero _).symm
  map_add' s t := by
    refine principalSection_ext _ _ fun i ↦ ?_
    calc
      _ = sectionEvaluation i X (Submodule.Quotient.mk (Finsupp.single s 1)) +
          sectionEvaluation i X (Submodule.Quotient.mk (Finsupp.single t 1)) := by
            simp [sectionEvaluation_mk, freeEvaluation]
      _ = _ := ((sectionEvaluation i X).map_add _ _).symm

/-- Composing the universal operator with the map induced by a differential operator
recovers that operator. -/
private lemma sectionEvaluation_generator {phi : O₁ ⟶ O₂}
    {F : _root_.SheafOfModules.{m} O₂} {k : ℕ} (i : OperatorTarget phi F k)
    (X : Cᵒᵖ) (s : F.val.obj X) :
    sectionEvaluation i X (principalGenerator phi F k X s) = i.2.1 X s := by
  change sectionEvaluation i X (Submodule.Quotient.mk (Finsupp.single s 1)) = _
  simp [sectionEvaluation_mk, freeEvaluation]

/-- The sectionwise recursive order condition, stated for presheaves of modules. -/
private def presheafOrder (phi : O₁ ⟶ O₂)
    {A : PresheafOfModules.{m} O₂.obj} {B : PresheafOfModules.{n} O₂.obj} :
    ∀ (_k : ℕ) {U : C}, (∀ Y : Over U, A.obj (op Y.left) → B.obj (op Y.left)) → Prop
  | 0, U, d =>
      (∀ (Y Y' : Over U) (h : Y ⟶ Y') s, d Y (A.map h.left.op s) = B.map h.left.op (d Y' s)) ∧
      ∀ (Y : Over U) (r : O₂.obj.obj (op Y.left)) s, d Y (r • s) = r • d Y s
  | k + 1, U, d =>
      (∀ (Y Y' : Over U) (h : Y ⟶ Y') s, d Y (A.map h.left.op s) = B.map h.left.op (d Y' s)) ∧
      (∀ Y a s, d Y (DiffOp.sectionRingHom phi (op Y.left) a • s) =
        DiffOp.sectionRingHom phi (op Y.left) a • d Y s) ∧
      ∀ (Y : Over _) (g : O₂.obj.obj (op Y.left)),
        presheafOrder phi k (fun Z s ↦
          d (Over.mk (Z.hom ≫ Y.hom)) ((O₂.obj.map Z.hom.op) g • s) -
            (O₂.obj.map Z.hom.op) g • d (Over.mk (Z.hom ≫ Y.hom)) s)

/-- On sheaves of modules, the presheaf-level order condition is the order condition for
differential operators. -/
private lemma presheafOrder_iff (phi : O₁ ⟶ O₂) (k : ℕ)
    {F : _root_.SheafOfModules.{m} O₂} {G : _root_.SheafOfModules.{n} O₂} {U : C}
    (D : DiffOp.RawOp F G U) :
    presheafOrder phi k (fun Y s ↦ D Y s) ↔ DiffOp.IsDiffOpOfOrder phi k D := by
  induction k generalizing U with
  | zero => rfl
  | succ k ih =>
      simp only [presheafOrder, DiffOp.IsDiffOpOfOrder]
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun Y ↦ forall_congr' fun g ↦
          ih (DiffOp.RawOp.commutator g (DiffOp.RawOp.slice D Y))))

/-- An operator into the presheaf of principal parts has order at most `ℓ` as soon as all
its evaluations under differential operators of order at most `k` do. -/
private lemma principalOrder_of_evaluations (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k ℓ : ℕ) {U : C}
    (d : ∀ Y : Over U, F.val.obj (op Y.left) → (principalPresheaf phi F k).obj (op Y.left))
    (hd : ∀ i : OperatorTarget phi F k,
      presheafOrder phi ℓ (fun Y s ↦ sectionEvaluation i (op Y.left) (d Y s))) :
    presheafOrder phi ℓ d := by
  induction ℓ generalizing U with
  | zero =>
      refine ⟨fun Y Y' h s ↦ ?_, fun Y r s ↦ ?_⟩
      · exact principalSection_ext _ _ fun i ↦
          ((hd i).1 Y Y' h s).trans (sectionEvaluation_map i h.left.op _).symm
      · exact principalSection_ext _ _ fun i ↦
          ((hd i).2 Y r s).trans ((sectionEvaluation i _).map_smul r (d Y s)).symm
  | succ ℓ ih =>
      refine ⟨fun Y Y' h s ↦ ?_, fun Y a s ↦ ?_, fun Y g ↦ ih _ fun i ↦ ?_⟩
      · exact principalSection_ext _ _ fun i ↦
          ((hd i).1 Y Y' h s).trans (sectionEvaluation_map i h.left.op _).symm
      · exact principalSection_ext _ _ fun i ↦
          ((hd i).2.1 Y a s).trans ((sectionEvaluation i _).map_smul _ (d Y s)).symm
      · convert (hd i).2.2 Y g using 1
        funext Z s
        exact ((sectionEvaluation i _).map_sub _ _).trans
          (congrArg₂ (· - ·) rfl ((sectionEvaluation i _).map_smul _ _))

/-- Postcomposing an operator of order at most `k` with a morphism of presheaves of modules
again gives an operator of order at most `k`. -/
private lemma presheafOrder_map (phi : O₁ ⟶ O₂) (k : ℕ)
    {A : PresheafOfModules.{m} O₂.obj} {B H : PresheafOfModules.{n} O₂.obj}
    (f : B ⟶ H) {U : C} (d : ∀ Y : Over U, A.obj (op Y.left) → B.obj (op Y.left))
    (hd : presheafOrder phi k d) :
    presheafOrder phi k (fun Y s ↦ f.app (op Y.left) (d Y s)) := by
  induction k generalizing U with
  | zero =>
      refine ⟨fun Y Y' h s ↦ ?_, fun Y r s ↦ ?_⟩
      · exact (congrArg (fun x ↦ f.app (op Y.left) x) (hd.1 Y Y' h s)).trans
          (PresheafOfModules.naturality_apply f h.left.op (d Y' s))
      · exact (congrArg (fun x ↦ f.app (op Y.left) x) (hd.2 Y r s)).trans
          ((f.app _).hom.map_smul r _)
  | succ k ih =>
      refine ⟨fun Y Y' h s ↦ ?_, fun Y a s ↦ ?_, fun Y g ↦ ?_⟩
      · exact (congrArg (fun x ↦ f.app (op Y.left) x) (hd.1 Y Y' h s)).trans
          (PresheafOfModules.naturality_apply f h.left.op (d Y' s))
      · exact (congrArg (fun x ↦ f.app (op Y.left) x) (hd.2.1 Y a s)).trans
          ((f.app _).hom.map_smul _ _)
      · simpa only [Over.mk_left, map_sub, map_smul] using ih _ (hd.2.2 Y g)

/-- The universal operator into the presheaf of principal parts has order at most `k`. -/
private lemma principalGenerator_order (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{m} O₂) (k : ℕ) (U : C) :
    presheafOrder phi k (U := U) (fun Y s ↦ principalGenerator phi F k (op Y.left) s) := by
  apply principalOrder_of_evaluations
  intro i
  simp only [sectionEvaluation_generator]
  exact (presheafOrder_iff phi k (i.2.1.restrict U)).2 (i.2.2 U)

/-- Two maps out of the presheaf of principal parts agree as soon as they agree on the
image of the universal operator. -/
private lemma principalPresheaf_hom_ext {phi : O₁ ⟶ O₂}
    {F : _root_.SheafOfModules.{m} O₂} {k : ℕ} {G : PresheafOfModules.{max w m} O₂.obj}
    (f g : principalPresheaf phi F k ⟶ G)
    (h : ∀ X s, f.app X (principalGenerator phi F k X s) =
      g.app X (principalGenerator phi F k X s)) : f = g := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with | _ x =>
  have he : (f.app X).hom.comp (principalRelations phi F k X).mkQ =
      (g.app X).hom.comp (principalRelations phi F k X).mkQ := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s (1 : O₂.obj.obj X) := by
      simp
    rw [hr]
    simp only [map_smul]
    exact congrArg (r • ·) (h X s)
  exact DFunLike.congr_fun he x

/-- Abelian presheaves on an essentially small site have a sheafification. -/
private lemma hasAddSheafify : HasSheafify J AddCommGrpCat.{max u v m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v m, v, u} J

/-- On an essentially small site, the maps inverted by sheafification of abelian presheaves
are exactly the locally bijective ones. -/
private lemma addWEqualsLocallyBijective :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} := by
  let := smallSiteWEqualsLocallyBijective
    ((equivSmallModel.{max u v m} C).inverse.inducedTopology J)
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v m} J

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u v w m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]

/-- The sheaf of principal parts of order at most `k`: the sheafification of the presheaf of
principal parts. -/
private noncomputable abbrev principalParts (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :=
  (PresheafOfModules.sheafification (𝟙 O₂.obj)).obj (principalPresheaf phi F k)

/-- The unit of sheafification at the presheaf of principal parts. -/
private noncomputable def principalUnit (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    principalPresheaf phi F k ⟶ (principalParts.{v, u, w, m} phi F k).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 O₂.obj)).unit.app _

/-- The universal differential operator of order at most `k` out of `F`, with values in the
sheaf of principal parts. -/
private noncomputable def universalOperator (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    DiffOp.GlobalOp F (principalParts.{v, u, w, m} phi F k) :=
  fun X ↦ ((principalUnit.{v, u, w, m} phi F k).app X).hom.toAddMonoidHom.comp
    (principalGenerator phi F k X)

/-- The universal operator has order at most `k`. -/
private lemma universalOperator_order (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    DiffOp.IsGlobalDiffOpOfOrder phi k (universalOperator.{v, u, w, m} phi F k) := by
  intro U
  exact (presheafOrder_iff phi k _).1 <| presheafOrder_map phi k
    (principalUnit.{v, u, w, m} phi F k) _ (principalGenerator_order phi F k U)

/-- The map out of the presheaf of principal parts induced by a differential operator of
order at most `k`. -/
private noncomputable def principalEvaluation (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ)
    {G : _root_.SheafOfModules.{max u v w m} O₂}
    (D : {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}) :
    principalPresheaf phi F k ⟶ G.val where
  app X := ModuleCat.ofHom (sectionEvaluation ⟨G, D⟩ X)
  naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact sectionEvaluation_map ⟨G, D⟩ f x

/-- The map out of the sheaf of principal parts induced by a differential operator of order
at most `k`. -/
private noncomputable def principalLift (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ)
    {G : _root_.SheafOfModules.{max u v w m} O₂}
    (D : {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}) :
    principalParts.{v, u, w, m} phi F k ⟶ G :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 O₂.obj)).homEquiv _ _).symm
    (principalEvaluation.{v, u, w, m} phi F k D)

/-- The induced map out of the sheaf of principal parts factors the induced map out of the
presheaf of principal parts through the unit of sheafification. -/
private lemma principalLift_fac (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ)
    {G : _root_.SheafOfModules.{max u v w m} O₂}
    (D : {D : DiffOp.GlobalOp F G // DiffOp.IsGlobalDiffOpOfOrder phi k D}) :
    principalUnit.{v, u, w, m} phi F k ≫ (principalLift.{v, u, w, m} phi F k D).val =
      principalEvaluation.{v, u, w, m} phi F k D :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 O₂.obj)).homEquiv _ _).apply_symm_apply _

/-- Two maps out of the sheaf of principal parts agree as soon as their composites with the
universal operator agree. -/
private lemma principalParts_hom_ext (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ)
    {G : _root_.SheafOfModules.{max u v w m} O₂}
    (f g : principalParts.{v, u, w, m} phi F k ⟶ G)
    (h : postcomp (universalOperator.{v, u, w, m} phi F k) f =
      postcomp (universalOperator.{v, u, w, m} phi F k) g) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 O₂.obj)).homEquiv _ _).injective
  exact principalPresheaf_hom_ext _ _ fun X s ↦ congrArg (fun D : DiffOp.GlobalOp F G ↦ D X s) h

/-- The sheaf of principal parts corepresents the functor of differential operators of order
at most `k` out of `F`, by postcomposition with the universal operator. -/
private noncomputable def principalCorepresentation (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    (differentialOperatorsFunctor.{v, u, w, m} phi F k).CorepresentableBy
      (principalParts.{v, u, w, m} phi F k) where
  homEquiv := {
    toFun := fun f ↦ ⟨postcomp (universalOperator.{v, u, w, m} phi F k) f,
      postcomp_isDiffOpOfOrder phi k _ (universalOperator_order.{v, u, w, m} phi F k) f⟩
    invFun := principalLift.{v, u, w, m} phi F k
    left_inv := by
      intro f
      apply principalParts_hom_ext.{v, u, w, m} phi F k
      funext X
      apply AddMonoidHom.ext
      intro s
      exact (congrArg (fun f ↦ (PresheafOfModules.Hom.app f X)
        (principalGenerator phi F k X s))
        (principalLift_fac.{v, u, w, m} phi F k
          ⟨postcomp (universalOperator.{v, u, w, m} phi F k) f,
            postcomp_isDiffOpOfOrder phi k _
              (universalOperator_order.{v, u, w, m} phi F k) f⟩)).trans
        (sectionEvaluation_generator _ X s)
    right_inv := by
      intro D
      apply Subtype.ext
      funext X
      apply AddMonoidHom.ext
      intro s
      exact (congrArg (fun f ↦ (PresheafOfModules.Hom.app f X)
        (principalGenerator phi F k X s)) (principalLift_fac.{v, u, w, m} phi F k D)).trans
          (sectionEvaluation_generator _ X s) }
  homEquiv_comp := by
    intros
    apply Subtype.ext
    funext X
    apply AddMonoidHom.ext
    intro s
    rfl

end Sheafification

/-- Differential operators of order at most `k` out of a fixed module sheaf are
represented by a sheaf of modules (the sheaf of principal parts). -/
@[stacks 09CT,
  ega "IV 16.8.3" "(16.8.3.1)",
  sga "6 II AppII.1.2.3",
  sga "6 II AppII.1.2.2" "(1.2.2.1)"]
noncomputable instance differentialOperatorsFunctor_isCorepresentable (phi : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u v w m} O₂) (k : ℕ) :
    (differentialOperatorsFunctor.{v, u, w, m} phi F k).IsCorepresentable := by
  let := hasAddSheafify.{v, u, max w m} (J := J)
  let := addWEqualsLocallyBijective.{v, u, max w m} (J := J)
  exact (principalCorepresentation.{v, u, w, m} phi F k).isCorepresentable

end AlgebraicGeometry.SheafOfModules
