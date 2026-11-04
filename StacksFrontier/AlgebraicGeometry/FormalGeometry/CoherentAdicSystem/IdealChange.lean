module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition

/-!
# Changing the ideal of a coherent adic system

Let `X` be a Noetherian scheme and let `ℐ, 𝒥 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals cutting
out the *same* closed subset of `X`. Then the categories `Coh(X, ℐ)` and `Coh(X, 𝒥)` of coherent
adic inverse systems are equivalent: this is [Stacks, Tag 0EHR].

Equality of the closed subsets means exactly that each ideal sheaf has a power inside the other,
`ℐ ᵃ ⊆ 𝒥` and `𝒥 ᵇ ⊆ ℐ` with `a, b ≥ 1`. Given such an `a`, an object `(F_n)` of `Coh(X, ℐ)` is
sent to the reindexed system
`(F_{a(n+1)} / 𝒥 ⁿ⁺¹ F_{a(n+1)})`,
which is an object of `Coh(X, 𝒥)`: its `n`-th term is annihilated by `𝒥 ⁿ⁺¹` by construction, and
it is the quotient of its `(n+1)`-st term by `𝒥 ⁿ⁺¹` because, modulo `𝒥 ⁿ⁺¹`, the transition map
of `(F_n)` between the indices `a(n+1)` and `a(n+2)` is invertible — those indices are far enough
apart that `ℐ ᵃ⁽ⁿ⁺¹⁾ ⊆ 𝒥 ⁿ⁺¹`. Running the construction with `b` in the other direction gives a
functor back, and the two composites are isomorphic to the identity for the same reason.

## Main definitions

* `Stacks.Coherent.transferIndex` — the reindexing `n ↦ a (n + 1)`.
* `Stacks.Coherent.transferSystem` — the reindexed-and-reduced inverse system, with
  `Stacks.Coherent.transferTerm`, `transferStep` and `transferProjection` for its terms,
  transitions and quotient projections.
* `Stacks.Coherent.transferFunctor` — the functor `Coh(X, ℐ) ⥤ Coh(X, 𝒥)` it defines, for
  `ℐ ᵃ ⊆ 𝒥`.

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_transferSystem` — the transferred system is a coherent
  adic system along `𝒥`.
* `Stacks.Coherent.transferFunctorCompIso` — the composite of the two transfer functors is
  isomorphic to the identity.
* `Stacks.Coherent.coherentAdicSystemsEquivOfSupportEq` — **[Stacks, Tag 0EHR]**, the equivalence
  `Coh(X, ℐ) ≌ Coh(X, 𝒥)` for ideal sheaves with the same closed support.

## Implementation notes

The `+ 1` in `transferIndex a n = a * (n + 1)` is there because the systems are zero-indexed, with
term `n` representing the source's `F_{n+1}`: it is the exponent `a (n + 1)` of `ℐ` at that index
which makes `ℐ ᵃ⁽ⁿ⁺¹⁾ ⊆ 𝒥 ⁿ⁺¹` available from `ℐ ᵃ ⊆ 𝒥`.

Every identity about the transferred system is proved by cancelling the epimorphism
`transferProjection`, the quotient projection `F_{a(n+1)} ⟶ (transferSystem 𝒥 a F)_n`: by
`Stacks.Algebraization.idealPowerQuotientMap_π` that projection intertwines the reduction maps with
the maps of `F` itself, so a diagram of reductions commutes as soon as the corresponding diagram in
`F` does. The two quotient clauses are then exactly the two identifications packaged in
`Stacks.Algebraization.idealPowerQuotientIsoOfIsIso` and
`Stacks.Algebraization.doubleIdealPowerQuotientIso`.

The proofs below are written as explicit `Category.assoc` and `congrArg` chains rather than with
`rw`. A hom type written in this file resolves `Quiver X.Modules` through `catToReflQuiver`, while
the hom types coming out of `CategoryTheory.NatTrans.app` and `CategoryTheory.Functor.map` resolve
it through `CategoryStruct.toQuiver`; the two are definitionally equal but not syntactically so, so
`rw` cannot reassociate a composite that mixes them, while `Eq.trans` and `congrArg` need only the
definitional equality. For the same reason `Category.assoc` is applied with its category argument
named, and `transferSystem_obj` is supplied as a `dsimp` lemma for the objects.

An inverse system and a morphism of inverse systems over `ℕᵒᵖ` are assembled from their values at
the successor steps with `CategoryTheory.Functor.ofOpSequence` and
`CategoryTheory.NatTrans.ofOpSequence`. Morphisms of `ℕᵒᵖ` with equal source and target are equal
(`ℕᵒᵖ` is a preorder category), so composites of transitions are identified with
`Subsingleton.elim` rather than by computing with `homOfLE`.

## References

* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### The reindexing -/

/-- The reindexing `n ↦ a (n + 1)` used to transfer an adic system from `ℐ` to `𝒥` when
`ℐ ᵃ ⊆ 𝒥`: at index `a (n + 1)` the exponent of `ℐ` is large enough that `ℐ` annihilates the term
as strongly as `𝒥 ⁿ⁺¹` must. -/
public def transferIndex (a n : ℕ) : ℕ := a * (n + 1)

/-- The reindexing is monotone. -/
public theorem transferIndex_mono (a : ℕ) : Monotone (transferIndex a) :=
  fun _ _ h => Nat.mul_le_mul_left a (Nat.add_le_add_right h 1)

/-- Consecutive reindexed indices are ordered. -/
public theorem transferIndex_le_succ (a n : ℕ) :
    transferIndex a n ≤ transferIndex a (n + 1) :=
  transferIndex_mono a (Nat.le_succ n)

/-- For a positive factor the reindexing only increases the index. -/
public theorem le_transferIndex {a : ℕ} (ha : 1 ≤ a) (n : ℕ) : n ≤ transferIndex a n :=
  (Nat.le_succ n).trans (by simpa [transferIndex] using Nat.mul_le_mul_right (n + 1) ha)

/-- `CategoryTheory.eq_whisker` with its arguments in the order the chains below use.

The chains are built from `CategoryTheory.whisker_eq` and this, rather than from `congrArg` with an
explicit lambda, so that the object through which the two sides are whiskered is supplied by an
explicit argument instead of being read off a hom type. -/
public theorem whiskerRight_eq {C : Type*} [Category C] {A B D : C} (h : B ⟶ D) {f g : A ⟶ B}
    (w : f = g) : f ≫ h = g ≫ h := eq_whisker w h

/-- Two successive transitions of an inverse system over `ℕᵒᵖ` compose to the transition between
the outer indices. -/
private theorem map_homOfLE_op_comp {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C) {k m n : ℕ}
    (h₁ : m ≤ n) (h₂ : k ≤ m) (h₃ : k ≤ n) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE h₃).op :=
  (F.map_comp _ _).symm.trans (congrArg F.map (Subsingleton.elim _ _))

/-- If `f` and `p'` slide past `p` and `q` in the two squares below, then the composite `p ≫ q`
slides past `m`. -/
private theorem comp_comp_comp_eq_of_squares {C : Type*} [Category C] {A B D E A' B' : C}
    {p : A ⟶ B} {q : B ⟶ D} {m : D ⟶ E} {e : B ⟶ B'} {f : A ⟶ A'} {p' : A' ⟶ B'}
    {q' : B' ⟶ E} (h₁ : q ≫ m = e ≫ q') (h₂ : p ≫ e = f ≫ p') :
    (p ≫ q) ≫ m = f ≫ p' ≫ q' := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

/-! ### The transferred system -/

/-- The `n`-th term of the transferred system: the reindexed term `F_{a(n+1)}`, divided by
`𝒥 ⁿ⁺¹`. -/
public abbrev transferTerm {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) : X.Modules :=
  idealPowerQuotient J (n + 1) (F.obj (op (transferIndex a n)))

/-- The transition map of the transferred system, induced by the transition of `F` between the
reindexed indices together with `𝒥 ⁿ⁺² ⊆ 𝒥 ⁿ⁺¹`. -/
public abbrev transferStep {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) :
    transferTerm J a F (n + 1) ⟶ transferTerm J a F n :=
  idealPowerQuotientMap J J (n + 2) (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le J (Nat.le_succ (n + 1)))
    (F.map (homOfLE (transferIndex_le_succ a n)).op)

/-- The reindexed-and-reduced inverse system `n ↦ F_{a(n+1)} / 𝒥 ⁿ⁺¹ F_{a(n+1)}`. -/
public def transferSystem {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) : ℕᵒᵖ ⥤ X.Modules where
  obj n := transferTerm J a F n.unop
  map {_ _} f := (Functor.ofOpSequence (X := transferTerm J a F) (transferStep J a F)).map f
  map_id _ := (Functor.ofOpSequence (X := transferTerm J a F) (transferStep J a F)).map_id _
  map_comp f g :=
    (Functor.ofOpSequence (X := transferTerm J a F) (transferStep J a F)).map_comp f g

/-- The terms of the transferred system are the `transferTerm`s.

This is `rfl`, and is a `dsimp` lemma because the two spellings are not interchangeable for `rw`:
goals about `transferSystem` arrive with `(transferSystem J a F).obj (op n)` inside the ideal-power
multiples, while every lemma about those multiples is stated for the module itself. -/
@[simp]
public theorem transferSystem_obj {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕᵒᵖ) :
    (transferSystem J a F).obj n = transferTerm J a F n.unop := rfl

/-- The transition of the transferred system between two indices, with its source and target
written as `transferTerm`s.

Hom types written in this file and hom types produced by `CategoryTheory.Functor.map` resolve
`Quiver X.Modules` differently, so composites that mix them cannot be manipulated; naming the
transition at the `transferTerm` spelling keeps every composite below in one of the two. -/
public abbrev transferTransition {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) {m n : ℕ} (h : m ≤ n) :
    transferTerm J a F n ⟶ transferTerm J a F m :=
  (transferSystem J a F).map (homOfLE h).op

/-- The successor transition of the transferred system is `transferStep`. -/
public theorem transferTransition_succ {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) :
    transferTransition J a F (Nat.le_succ n) = transferStep J a F n := by
  dsimp [transferTransition, transferSystem]
  simp only [Functor.ofOpSequence_map_homOfLE_succ]

/-- A transition of the transferred system splits off its first step. -/
public theorem transferTransition_succ_comp {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) {m n : ℕ} (h : m ≤ n) :
    transferTransition J a F (Nat.le_succ_of_le h) =
      transferStep J a F n ≫ transferTransition J a F h :=
  (map_homOfLE_op_comp (transferSystem J a F) (Nat.le_succ n) h (Nat.le_succ_of_le h)).symm.trans
    (whiskerRight_eq (transferTransition J a F h) (transferTransition_succ J a F n))

/-- The quotient projection from the reindexed term of `F` onto the corresponding term of the
transferred system. -/
public abbrev transferProjection {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) :
    F.obj (op (transferIndex a n)) ⟶ transferTerm J a F n :=
  cokernel.π (C := X.Modules)
    (idealPowerMultiple J (n + 1) (F.obj (op (transferIndex a n)))).ι

/-- The projections onto the terms of the transferred system are epimorphisms. -/
public instance epi_transferProjection {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) : Epi (transferProjection J a F n) :=
  epi_cokernel_π_submodule_ι _

/-- The composite of two projections, for a doubly-transferred system, is an epimorphism. -/
public instance epi_transferProjection_comp {X : Scheme.{u}} (I J : X.IdealSheafData) (a b : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) :
    Epi (transferProjection J a F (transferIndex b n) ≫
      transferProjection I b (transferSystem J a F) n) := by
  have h1 : Epi (transferProjection J a F (transferIndex b n)) :=
    epi_cokernel_π_submodule_ι _
  have h2 : Epi (transferProjection I b (transferSystem J a F) n) :=
    epi_cokernel_π_submodule_ι _
  exact @epi_comp _ _ _ _ _ _ h1 _ h2

/-- The projection intertwines one transition of the transferred system with the corresponding
transition of `F`. -/
public theorem transferProjection_transferStep {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) (n : ℕ) :
    transferProjection J a F (n + 1) ≫ transferStep J a F n =
      F.map (homOfLE (transferIndex_le_succ a n)).op ≫ transferProjection J a F n :=
  idealPowerQuotientMap_π _ _ _ _ _ _

/-- The projections intertwine the transitions of the transferred system with those of `F`. -/
public theorem transferProjection_map {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) {m n : ℕ} (h : m ≤ n) :
    transferProjection J a F n ≫ transferTransition J a F h =
      F.map (homOfLE (transferIndex_mono a h)).op ≫ transferProjection J a F m := by
  induction n, h using Nat.le_induction with
  | base =>
      have h1 : ∀ hh : m ≤ m, transferTransition J a F hh = 𝟙 _ := fun _ =>
        (congrArg (transferSystem J a F).map (Subsingleton.elim _ (𝟙 (op m)))).trans
          ((transferSystem J a F).map_id (op m))
      have h2 : ∀ hh : transferIndex a m ≤ transferIndex a m,
          F.map (homOfLE hh).op = 𝟙 _ := fun _ =>
        (congrArg F.map (Subsingleton.elim _ _)).trans (F.map_id (op (transferIndex a m)))
      rw [h1, h2]
      exact (Category.comp_id (obj := X.Modules) _).trans
        (Category.id_comp (obj := X.Modules) _).symm
  | succ n h ih =>
      calc transferProjection J a F (n + 1) ≫
              transferTransition J a F (Nat.le_succ_of_le h)
          = transferProjection J a F (n + 1) ≫
              transferStep J a F n ≫ transferTransition J a F h :=
            whisker_eq (transferProjection J a F (n + 1))
              (transferTransition_succ_comp J a F h)
        _ = (transferProjection J a F (n + 1) ≫ transferStep J a F n) ≫
              transferTransition J a F h :=
            (Category.assoc (obj := X.Modules) _ _ _).symm
        _ = (F.map (homOfLE (transferIndex_le_succ a n)).op ≫ transferProjection J a F n) ≫
              transferTransition J a F h :=
            whiskerRight_eq (transferTransition J a F h)
              (transferProjection_transferStep J a F n)
        _ = F.map (homOfLE (transferIndex_le_succ a n)).op ≫
              transferProjection J a F n ≫ transferTransition J a F h :=
            Category.assoc (obj := X.Modules) _ _ _
        _ = F.map (homOfLE (transferIndex_le_succ a n)).op ≫
              F.map (homOfLE (transferIndex_mono a h)).op ≫ transferProjection J a F m :=
            whisker_eq _ ih
        _ = F.map (homOfLE (transferIndex_mono a (Nat.le_succ_of_le h))).op ≫
              transferProjection J a F m :=
            (Category.assoc (obj := X.Modules) _ _ _).symm.trans
              (whiskerRight_eq _ (map_homOfLE_op_comp F _ _ _))

/-! ### Functoriality of the transfer -/

/-- The component at `n` of the morphism of transferred systems induced by `η : F ⟶ G`. -/
public abbrev transferSystemComponent {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) (n : ℕ) :
    transferTerm J a F n ⟶ transferTerm J a G n :=
  idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl (η.app (op (transferIndex a n)))

/-- The projection intertwines the induced map of transferred systems with `η`. -/
public theorem transferProjection_transferSystemComponent {X : Scheme.{u}}
    (J : X.IdealSheafData) (a : ℕ) {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) (n : ℕ) :
    transferProjection J a F n ≫ transferSystemComponent J a η n =
      η.app (op (transferIndex a n)) ≫ transferProjection J a G n :=
  idealPowerQuotientMap_π _ _ _ _ _ _

/-- The morphism of transferred systems induced by a morphism `η : F ⟶ G` of inverse systems. -/
public def transferMap {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) :
    transferSystem J a F ⟶ transferSystem J a G :=
  NatTrans.ofOpSequence (F := transferSystem J a F) (G := transferSystem J a G)
    (transferSystemComponent J a η) (fun n => by
      refine (cancel_epi (transferProjection J a F (n + 1))).1 ?_
      refine (congrArg (fun z => transferProjection J a F (n + 1) ≫
        z ≫ transferSystemComponent J a η n) (transferTransition_succ J a F n)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => transferProjection J a F (n + 1) ≫
        transferSystemComponent J a η (n + 1) ≫ z) (transferTransition_succ J a G n)).symm
      calc transferProjection J a F (n + 1) ≫
              transferStep J a F n ≫ transferSystemComponent J a η n
          = (transferProjection J a F (n + 1) ≫ transferStep J a F n) ≫
              transferSystemComponent J a η n :=
            (Category.assoc (obj := X.Modules) _ _ _).symm
        _ = (F.map (homOfLE (transferIndex_le_succ a n)).op ≫ transferProjection J a F n) ≫
              transferSystemComponent J a η n :=
            whiskerRight_eq (transferSystemComponent J a η n)
              (transferProjection_transferStep J a F n)
        _ = F.map (homOfLE (transferIndex_le_succ a n)).op ≫
              transferProjection J a F n ≫ transferSystemComponent J a η n :=
            Category.assoc (obj := X.Modules) _ _ _
        _ = F.map (homOfLE (transferIndex_le_succ a n)).op ≫
              η.app (op (transferIndex a n)) ≫ transferProjection J a G n :=
            whisker_eq (F.map (homOfLE (transferIndex_le_succ a n)).op)
              (transferProjection_transferSystemComponent J a η n)
        _ = (F.map (homOfLE (transferIndex_le_succ a n)).op ≫
              η.app (op (transferIndex a n))) ≫ transferProjection J a G n :=
            (Category.assoc (obj := X.Modules) _ _ _).symm
        _ = (η.app (op (transferIndex a (n + 1))) ≫
              G.map (homOfLE (transferIndex_le_succ a n)).op) ≫ transferProjection J a G n :=
            whiskerRight_eq (transferProjection J a G n)
              (η.naturality (homOfLE (transferIndex_le_succ a n)).op)
        _ = η.app (op (transferIndex a (n + 1))) ≫
              G.map (homOfLE (transferIndex_le_succ a n)).op ≫ transferProjection J a G n :=
            Category.assoc (obj := X.Modules) _ _ _
        _ = η.app (op (transferIndex a (n + 1))) ≫
              transferProjection J a G (n + 1) ≫ transferStep J a G n :=
            whisker_eq (η.app (op (transferIndex a (n + 1))))
              (transferProjection_transferStep J a G n).symm
        _ = (η.app (op (transferIndex a (n + 1))) ≫ transferProjection J a G (n + 1)) ≫
              transferStep J a G n := (Category.assoc (obj := X.Modules) _ _ _).symm
        _ = (transferProjection J a F (n + 1) ≫ transferSystemComponent J a η (n + 1)) ≫
              transferStep J a G n :=
            whiskerRight_eq (transferStep J a G n)
              (transferProjection_transferSystemComponent J a η (n + 1)).symm
        _ = transferProjection J a F (n + 1) ≫
              transferSystemComponent J a η (n + 1) ≫ transferStep J a G n :=
            Category.assoc (obj := X.Modules) _ _ _)

/-- The components of `transferMap` are the maps induced on the quotients. -/
public theorem transferMap_app {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) (n : ℕᵒᵖ) :
    (transferMap J a η).app n = transferSystemComponent J a η n.unop :=
  NatTrans.ofOpSequence_app _ _ _

/-- The projections are natural in the inverse system. -/
public theorem transferProjection_naturality {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ)
    {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) (n : ℕ) :
    transferProjection J a F n ≫ (transferMap J a η).app (op n) =
      η.app (op (transferIndex a n)) ≫ transferProjection J a G n :=
  (congrArg (fun z => transferProjection J a F n ≫ z) (transferMap_app J a η (op n))).trans
    (transferProjection_transferSystemComponent J a η n)

/-- The transfer, as an endofunctor of the category of inverse systems of `𝒪_X`-modules. -/
public def transferSystemFunctor {X : Scheme.{u}} (J : X.IdealSheafData) (a : ℕ) :
    (ℕᵒᵖ ⥤ X.Modules) ⥤ (ℕᵒᵖ ⥤ X.Modules) where
  obj F := transferSystem J a F
  map η := transferMap J a η
  map_id F := NatTrans.ext (funext fun n =>
    (transferMap_app J a (𝟙 F) n).trans
      (idealPowerQuotientMap_id J (n.unop + 1) (F.obj (op (transferIndex a n.unop)))))
  map_comp {_ _ _} η θ := NatTrans.ext (funext fun n =>
    (transferMap_app J a (η ≫ θ) n).trans
      ((idealPowerQuotientMap_comp J (n.unop + 1) (η.app (op (transferIndex a n.unop)))
          (θ.app (op (transferIndex a n.unop)))).trans
        (congrArg₂ (fun z w => z ≫ w) (transferMap_app J a η n).symm
          (transferMap_app J a θ n).symm)))

/-! ### The transferred system is a coherent adic system -/

/-- **The transfer lands in `Coh(X, 𝒥)`.** If `(F_n)` is a coherent adic system along `ℐ` and
`ℐ ᵃ ⊆ 𝒥`, then the reindexed-and-reduced system is a coherent adic system along `𝒥`.

Coherence and annihilation are immediate from the construction. The quotient clause is
`Stacks.Algebraization.idealPowerQuotientIsoOfIsIso` applied to the transition
`F_{a(n+2)} ⟶ F_{a(n+1)}`, whose reduction modulo `𝒥 ⁿ⁺¹` is invertible by
`IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map`, the hypothesis `ℐ ᵃ⁽ⁿ⁺¹⁾⁺¹ ⊆ 𝒥 ⁿ⁺¹` coming
from `ℐ ᵃ ⊆ 𝒥`. -/
public theorem isCoherentAdicSystem_transferSystem {X : Scheme.{u}} [IsNoetherian X]
    {I J : X.IdealSheafData} {a : ℕ} {F : ℕᵒᵖ ⥤ X.Modules} (hpow : I ^ a ≤ J)
    (hF : IsCoherentAdicSystem I F) :
    IsCoherentAdicSystem J (transferSystem J a F) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have := hF.isCoherent (transferIndex a n)
    exact isCoherent_idealPowerQuotient J (n + 1) _
  · dsimp only [transferSystem_obj, unop_op]
    have := hF.isQuasicoherent (transferIndex a n)
    exact idealPowerMultiple_idealPowerQuotient_eq_bot J (n + 1) _
  · dsimp only [transferSystem_obj, unop_op]
    have hmk : transferIndex a n ≤ transferIndex a (n + 1) := transferIndex_le_succ a n
    -- `ℐ ᵏ⁺¹ ⊆ 𝒥 ⁿ⁺¹` for `k = a (n + 1)`, since `ℐ ᵏ = (ℐ ᵃ) ⁿ⁺¹ ⊆ 𝒥 ⁿ⁺¹`.
    have hpowR : I ^ (transferIndex a n + 1) ≤ J ^ (n + 1) := fun U => by
      calc I.ideal U ^ (transferIndex a n + 1) ≤ I.ideal U ^ transferIndex a n :=
            Ideal.pow_le_pow_right (Nat.le_succ _)
        _ = (I.ideal U ^ a) ^ (n + 1) := by dsimp only [transferIndex]; rw [pow_mul]
        _ ≤ J.ideal U ^ (n + 1) := pow_le_pow_left' (hpow U) (n + 1)
    have hqc : (F.obj (op (transferIndex a (n + 1)))).IsQuasicoherent :=
      hF.isQuasicoherent (transferIndex a (n + 1))
    have hiso : IsIso (idealPowerQuotientMap J J (n + 1) (n + 1) le_rfl
        (F.map (homOfLE hmk).op)) :=
      hF.isIso_idealPowerQuotientMap_map J (n + 1) hmk hpowR
    exact ⟨(idealPowerQuotientIsoOfIsIso J (n + 1) (F.map (homOfLE hmk).op)).1,
      ((idealPowerQuotientIsoOfIsIso J (n + 1) (F.map (homOfLE hmk).op)).2).trans
        (transferTransition_succ J a F n).symm⟩

/-- The transfer functor `Coh(X, ℐ) ⥤ Coh(X, 𝒥)` attached to a containment `ℐ ᵃ ⊆ 𝒥`. -/
public def transferFunctor {X : Scheme.{u}} [IsNoetherian X] (I J : X.IdealSheafData) (a : ℕ)
    (hpow : I ^ a ≤ J) :
    CoherentAdicSystems I ⥤ CoherentAdicSystems J where
  obj F := ⟨transferSystem J a F.obj, isCoherentAdicSystem_transferSystem hpow F.property⟩
  map f := ObjectProperty.homMk (transferMap J a f.hom)
  map_id F := ObjectProperty.hom_ext _ ((transferSystemFunctor J a).map_id F.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((transferSystemFunctor J a).map_comp f.hom g.hom)

/-! ### The two transfers are mutually inverse -/

/-- The composite of the two projections intertwines the transitions of the doubly-transferred
system with those of `F`. -/
public theorem transferProjection_comp_map {X : Scheme.{u}} (I J : X.IdealSheafData) (a b : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) {m n : ℕ} (h : m ≤ n) :
    (transferProjection J a F (transferIndex b n) ≫
        transferProjection I b (transferSystem J a F) n) ≫
      transferTransition I b (transferSystem J a F) h =
      F.map (homOfLE (transferIndex_mono a (transferIndex_mono b h))).op ≫
        transferProjection J a F (transferIndex b m) ≫
          transferProjection I b (transferSystem J a F) m :=
  comp_comp_comp_eq_of_squares (transferProjection_map I b (transferSystem J a F) h)
    (transferProjection_map J a F (transferIndex_mono b h))

/-- The composite of the two projections is natural in the inverse system. -/
public theorem transferProjection_comp_naturality {X : Scheme.{u}} (I J : X.IdealSheafData)
    (a b : ℕ) {F G : ℕᵒᵖ ⥤ X.Modules} (η : F ⟶ G) (n : ℕ) :
    (transferProjection J a F (transferIndex b n) ≫
        transferProjection I b (transferSystem J a F) n) ≫
      (transferMap I b (transferMap J a η)).app (op n) =
      η.app (op (transferIndex a (transferIndex b n))) ≫
        transferProjection J a G (transferIndex b n) ≫
          transferProjection I b (transferSystem J a G) n :=
  comp_comp_comp_eq_of_squares (transferProjection_naturality I b (transferMap J a η) n)
    (transferProjection_naturality J a η (transferIndex b n))

variable {X : Scheme.{u}} {I J : X.IdealSheafData} {a b : ℕ} {F : ℕᵒᵖ ⥤ X.Modules}

/-- The identification of the `n`-th term of the doubly-transferred system with `F_n`, together
with its compatibility with the two projections.

With `l = transferIndex b n` and `k = transferIndex a l`, the `n`-th term of the double transfer is
`(F_k / 𝒥 ˡ⁺¹ F_k) / ℐ ⁿ⁺¹ (…)`, so this is exactly
`Stacks.Algebraization.doubleIdealPowerQuotientIso` for the transition `F_k ⟶ F_n`: dividing `F_k`
by `𝒥 ˡ⁺¹` is invisible modulo `ℐ ⁿ⁺¹` because `𝒥 ˡ⁺¹ ⊆ ℐ ⁿ⁺¹`, the transition is invertible modulo
`ℐ ⁿ⁺¹`, and `F_n` is already its own `ℐ ⁿ⁺¹`-quotient since `ℐ ⁿ⁺¹ F_n = 0`. -/
public def transferCompositeIsoData [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    {e : transferTerm I b (transferSystem J a F) n ≅ F.obj (op n) //
      transferProjection J a F (transferIndex b n) ≫
        transferProjection I b (transferSystem J a F) n ≫ e.hom =
        F.map (homOfLE ((le_transferIndex hb n).trans
          (le_transferIndex ha (transferIndex b n)))).op} := by
  have hnk : n ≤ transferIndex a (transferIndex b n) :=
    (le_transferIndex hb n).trans (le_transferIndex ha (transferIndex b n))
  -- `𝒥 ˡ⁺¹ ⊆ ℐ ⁿ⁺¹` for `l = b (n + 1)`, since `𝒥 ˡ = (𝒥 ᵇ) ⁿ⁺¹ ⊆ ℐ ⁿ⁺¹`.
  have hpow : J ^ (transferIndex b n + 1) ≤ I ^ (n + 1) := fun U => by
    calc J.ideal U ^ (transferIndex b n + 1) ≤ J.ideal U ^ transferIndex b n :=
          Ideal.pow_le_pow_right (Nat.le_succ _)
      _ = (J.ideal U ^ b) ^ (n + 1) := by dsimp only [transferIndex]; rw [pow_mul]
      _ ≤ I.ideal U ^ (n + 1) := pow_le_pow_left' (hJI U) (n + 1)
  have hqc : (F.obj (op (transferIndex a (transferIndex b n)))).IsQuasicoherent :=
    hF.isQuasicoherent _
  have hiso : IsIso (idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl
      (F.map (homOfLE hnk).op)) :=
    hF.isIso_idealPowerQuotientMap_map I (n + 1) hnk le_rfl
  exact doubleIdealPowerQuotientIso I J (n + 1) (transferIndex b n + 1) hpow
    (F.map (homOfLE hnk).op) (hF.idealPowerMultiple_eq_bot n)

/-- The identification of the `n`-th term of the doubly-transferred system with `F_n`. -/
public def transferCompositeIsoApp [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    transferTerm I b (transferSystem J a F) n ≅ F.obj (op n) :=
  (transferCompositeIsoData ha hb hJI hF n).1

/-- The identification of the double transfer is compatible with the two projections. -/
public theorem transferCompositeIsoApp_projection [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) (n : ℕ) :
    (transferProjection J a F (transferIndex b n) ≫
        transferProjection I b (transferSystem J a F) n) ≫
      (transferCompositeIsoApp ha hb hJI hF n).hom =
      F.map (homOfLE ((le_transferIndex hb n).trans
        (le_transferIndex ha (transferIndex b n)))).op :=
  (Category.assoc (obj := X.Modules) _ _ _).trans (transferCompositeIsoData ha hb hJI hF n).2

/-- The comparison morphism from the double transfer of an inverse system to the system itself. -/
public def transferCompositeHom [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) :
    transferSystem I b (transferSystem J a F) ⟶ F :=
  NatTrans.ofOpSequence (F := transferSystem I b (transferSystem J a F)) (G := F)
    (fun n => (transferCompositeIsoApp ha hb hJI hF n).hom) (fun n => by
      refine (cancel_epi (transferProjection J a F (transferIndex b (n + 1)) ≫
        transferProjection I b (transferSystem J a F) (n + 1))).1 ?_
      calc (transferProjection J a F (transferIndex b (n + 1)) ≫
                transferProjection I b (transferSystem J a F) (n + 1)) ≫
              transferTransition I b (transferSystem J a F) (Nat.le_succ n) ≫
                (transferCompositeIsoApp ha hb hJI hF n).hom
          = ((transferProjection J a F (transferIndex b (n + 1)) ≫
                transferProjection I b (transferSystem J a F) (n + 1)) ≫
              transferTransition I b (transferSystem J a F) (Nat.le_succ n)) ≫
                (transferCompositeIsoApp ha hb hJI hF n).hom :=
            (Category.assoc (obj := X.Modules) _ _ _).symm
        _ = (F.map (homOfLE (transferIndex_mono a
                  (transferIndex_mono b (Nat.le_succ n)))).op ≫
              transferProjection J a F (transferIndex b n) ≫
                transferProjection I b (transferSystem J a F) n) ≫
                  (transferCompositeIsoApp ha hb hJI hF n).hom :=
            whiskerRight_eq ((transferCompositeIsoApp ha hb hJI hF n).hom)
              (transferProjection_comp_map I J a b F (Nat.le_succ n))
        _ = F.map (homOfLE (transferIndex_mono a
                (transferIndex_mono b (Nat.le_succ n)))).op ≫
              (transferProjection J a F (transferIndex b n) ≫
                transferProjection I b (transferSystem J a F) n) ≫
                  (transferCompositeIsoApp ha hb hJI hF n).hom :=
            Category.assoc (obj := X.Modules) _ _ _
        _ = F.map (homOfLE (transferIndex_mono a
                (transferIndex_mono b (Nat.le_succ n)))).op ≫
              F.map (homOfLE ((le_transferIndex hb n).trans
                (le_transferIndex ha (transferIndex b n)))).op :=
            congrArg (fun z => F.map (homOfLE (transferIndex_mono a
              (transferIndex_mono b (Nat.le_succ n)))).op ≫ z)
              (transferCompositeIsoApp_projection ha hb hJI hF n)
        _ = F.map ((homOfLE (transferIndex_mono a
                (transferIndex_mono b (Nat.le_succ n)))).op ≫
              (homOfLE ((le_transferIndex hb n).trans
                (le_transferIndex ha (transferIndex b n)))).op) := (F.map_comp _ _).symm
        _ = F.map ((homOfLE ((le_transferIndex hb (n + 1)).trans
                (le_transferIndex ha (transferIndex b (n + 1))))).op ≫
              (homOfLE (Nat.le_succ n)).op) := congrArg F.map (Subsingleton.elim _ _)
        _ = F.map (homOfLE ((le_transferIndex hb (n + 1)).trans
                (le_transferIndex ha (transferIndex b (n + 1))))).op ≫
              F.map (homOfLE (Nat.le_succ n)).op := F.map_comp _ _
        _ = ((transferProjection J a F (transferIndex b (n + 1)) ≫
                transferProjection I b (transferSystem J a F) (n + 1)) ≫
              (transferCompositeIsoApp ha hb hJI hF (n + 1)).hom) ≫
                F.map (homOfLE (Nat.le_succ n)).op :=
            whiskerRight_eq (F.map (homOfLE (Nat.le_succ n)).op)
              (transferCompositeIsoApp_projection ha hb hJI hF (n + 1)).symm
        _ = (transferProjection J a F (transferIndex b (n + 1)) ≫
                transferProjection I b (transferSystem J a F) (n + 1)) ≫
              (transferCompositeIsoApp ha hb hJI hF (n + 1)).hom ≫
                F.map (homOfLE (Nat.le_succ n)).op :=
            Category.assoc (obj := X.Modules) _ _ _)

/-- The components of `transferCompositeHom` are the identifications of the terms. -/
public theorem transferCompositeHom_app [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) (n : ℕᵒᵖ) :
    (transferCompositeHom ha hb hJI hF).app n =
      (transferCompositeIsoApp ha hb hJI hF n.unop).hom :=
  NatTrans.ofOpSequence_app _ _ _

/-- The double transfer of an inverse system is isomorphic to the system itself. -/
public def transferCompositeIso [IsNoetherian X] (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hJI : J ^ b ≤ I) (hF : IsCoherentAdicSystem I F) :
    transferSystem I b (transferSystem J a F) ≅ F :=
  NatIso.ofComponents (fun n => transferCompositeIsoApp ha hb hJI hF n.unop) (fun {i j} f =>
    ((whisker_eq ((transferSystem I b (transferSystem J a F)).map f)
          (transferCompositeHom_app ha hb hJI hF j)).symm.trans
        ((transferCompositeHom ha hb hJI hF).naturality f)).trans
      (whiskerRight_eq (F.map f) (transferCompositeHom_app ha hb hJI hF i)))

/-- The composite of the two transfer functors is isomorphic to the identity of `Coh(X, ℐ)`. -/
public def transferFunctorCompIso [IsNoetherian X] (I J : X.IdealSheafData) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hIJ : I ^ a ≤ J) (hJI : J ^ b ≤ I) :
    transferFunctor I J a hIJ ⋙ transferFunctor J I b hJI ≅ 𝟭 (CoherentAdicSystems I) := by
  refine NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ (transferCompositeIso ha hb hJI G.property)) ?_
  intro G H η
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun n => ?_)
  change (transferMap I b (transferMap J a η.hom)).app n ≫
      (transferCompositeIsoApp ha hb hJI H.property n.unop).hom =
    (transferCompositeIsoApp ha hb hJI G.property n.unop).hom ≫ η.hom.app n
  refine (cancel_epi (transferProjection J a G.obj (transferIndex b n.unop) ≫
    transferProjection I b (transferSystem J a G.obj) n.unop)).1 ?_
  calc (transferProjection J a G.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a G.obj) n.unop) ≫
          (transferMap I b (transferMap J a η.hom)).app n ≫
            (transferCompositeIsoApp ha hb hJI H.property n.unop).hom
      = ((transferProjection J a G.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a G.obj) n.unop) ≫
          (transferMap I b (transferMap J a η.hom)).app n) ≫
            (transferCompositeIsoApp ha hb hJI H.property n.unop).hom :=
        (Category.assoc (obj := X.Modules) _ _ _).symm
    _ = (η.hom.app (op (transferIndex a (transferIndex b n.unop))) ≫
          transferProjection J a H.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a H.obj) n.unop) ≫
              (transferCompositeIsoApp ha hb hJI H.property n.unop).hom :=
        whiskerRight_eq ((transferCompositeIsoApp ha hb hJI H.property n.unop).hom)
          (transferProjection_comp_naturality I J a b η.hom n.unop)
    _ = η.hom.app (op (transferIndex a (transferIndex b n.unop))) ≫
          (transferProjection J a H.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a H.obj) n.unop) ≫
              (transferCompositeIsoApp ha hb hJI H.property n.unop).hom :=
        Category.assoc (obj := X.Modules) _ _ _
    _ = η.hom.app (op (transferIndex a (transferIndex b n.unop))) ≫
          H.obj.map (homOfLE ((le_transferIndex hb n.unop).trans
            (le_transferIndex ha (transferIndex b n.unop)))).op :=
        whisker_eq (η.hom.app (op (transferIndex a (transferIndex b n.unop))))
          (transferCompositeIsoApp_projection ha hb hJI H.property n.unop)
    _ = G.obj.map (homOfLE ((le_transferIndex hb n.unop).trans
            (le_transferIndex ha (transferIndex b n.unop)))).op ≫ η.hom.app (op n.unop) :=
        (η.hom.naturality _).symm
    _ = ((transferProjection J a G.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a G.obj) n.unop) ≫
          (transferCompositeIsoApp ha hb hJI G.property n.unop).hom) ≫ η.hom.app (op n.unop) :=
        whiskerRight_eq (η.hom.app (op n.unop))
          (transferCompositeIsoApp_projection ha hb hJI G.property n.unop).symm
    _ = (transferProjection J a G.obj (transferIndex b n.unop) ≫
            transferProjection I b (transferSystem J a G.obj) n.unop) ≫
          (transferCompositeIsoApp ha hb hJI G.property n.unop).hom ≫ η.hom.app (op n.unop) :=
        Category.assoc (obj := X.Modules) _ _ _

/-- **[Stacks, Tag 0EHR].** Let `X` be a Noetherian scheme and let `ℐ, 𝒥 ⊆ 𝒪_X` be quasi-coherent
sheaves of ideals. If `V(ℐ) = V(𝒥)` as closed subsets of `X`, then the categories `Coh(X, ℐ)` and
`Coh(X, 𝒥)` of coherent adic inverse systems are equivalent.

Equal supports give positive exponents with `ℐ ᵃ ⊆ 𝒥` and `𝒥 ᵇ ⊆ ℐ`, and the two transfer functors
they define are mutually quasi-inverse. -/
@[stacks 0EHR]
public def coherentAdicSystemsEquivOfSupportEq (X : Scheme.{u}) [IsNoetherian X]
    (I J : X.IdealSheafData) (h : I.support = J.support) :
    CoherentAdicSystems I ≌ CoherentAdicSystems J := by
  refine Classical.choice ?_
  obtain ⟨a, b, ha, hb, hIJ, hJI⟩ :=
    Scheme.IdealSheafData.exists_pos_pow_le_and_pow_le_of_support_eq h
  exact ⟨CategoryTheory.Equivalence.mk (transferFunctor I J a hIJ) (transferFunctor J I b hJI)
    (transferFunctorCompIso I J a b ha hb hIJ hJI).symm
    (transferFunctorCompIso J I b a hb ha hJI hIJ)⟩

end Stacks.Coherent

end
