module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.System
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# Systems of morphism sets along a directed system over a base, for a pullback pseudofunctor

Let `P` be a coherent pullback pseudofunctor datum on a category `A`: a category `D a` for each
object, an inverse image `f^* : D b ⥤ D a` for each morphism `f : a ⟶ b`, and the coherent unit
and composition comparisons.  Let `j ↦ T_j` be a directed system of objects of `A` over a base `b`,
with transition morphisms `t_{ij} : T_j ⟶ T_i` over `b` and a cone `T ⟶ T_j` over `b`.  For two
objects `X`, `Y` of `D b` the inverse images to the stages and to the vertex give a system of
morphism sets

`Hom(k_j^*X, k_j^*Y) ⟶ Hom(k^*X, k^*Y)`,

whose maps apply the inverse image along the morphisms of the system and read the result through
the comparisons.  This file sets up that system and proves the closure properties of the statement
that `Hom(k^*X, k^*Y)` is its filtered colimit.  It is the abstract form of
`Stacks.LimitHomDescent.SchemeSystem` of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitHomDescent/System.lean`, which is the case of the
derived pullback on schemes; the case used here is the derived pullback of modules on algebraic
spaces, `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`.

## Main definitions

* `CategoryTheory.PullbackData.factorHom`: the map of morphism sets attached to a factorisation
  `f ≫ g = k`.
* `CategoryTheory.PullbackData.LimitSystem`: a directed system over a base with a cone.
* `CategoryTheory.PullbackData.LimitSystem.trans` and `projHom`: the maps of the system of
  morphism sets.
* `CategoryTheory.PullbackData.LimitSystem.IsColim`: `Hom(k^*X, k^*Y)` is the filtered colimit
  of the `Hom(k_j^*X, k_j^*Y)`.
* `CategoryTheory.PullbackData.LimitSystem.Hom`: a morphism of systems over the same base.
* `CategoryTheory.PullbackData.LimitSystem.comp`: a system read over a further base.

## Main results

* `CategoryTheory.PullbackData.factorHom_comp`: the maps attached to factorisations compose,
  which is the associativity coherence of the datum.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_iso_fst`, `of_iso_snd`, `biprod` and
  `obj₃`: the closure properties in the two arguments.
* `CategoryTheory.PullbackData.LimitSystem.Hom.isColim_iff`: transfer along a morphism of
  systems inducing bijections.
* `CategoryTheory.PullbackData.LimitSystem.isColim_comp_iff`: change of base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D)

/-! ### The map attached to a factorisation -/

section Factor

variable {a b c : A}

/-- **The map of morphism sets attached to a factorisation** `f ≫ g = k`: a morphism
`g^*X ⟶ g^*Y` is sent to its inverse image along `f`, read through the comparison
`k^* ≅ g^* ⋙ f^*` at both ends. -/
def factorHom {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) {X Y : D c}
    (φ : (P.pull g).obj X ⟶ (P.pull g).obj Y) : (P.pull k).obj X ⟶ (P.pull k).obj Y :=
  Functor.conjHom (P.triangle h) φ

/-- Conjugation by the composition comparison `(k ≫ f)^* ≅ k^* ⋙ f^*`, as a bijection of
morphism sets. -/
def compEquiv {c b b' : A} (k : c ⟶ b) (f : b ⟶ b') (X Y : D b') :
    ((P.pull k).obj ((P.pull f).obj X) ⟶ (P.pull k).obj ((P.pull f).obj Y)) ≃
      ((P.pull (k ≫ f)).obj X ⟶ (P.pull (k ≫ f)).obj Y) :=
  Iso.homCongr ((P.compIso k f).app X).symm ((P.compIso k f).app Y).symm

variable {P}

/-- The map attached to a factorisation depends on the first factor only through its value. -/
theorem factorHom_congr {f f' : a ⟶ b} (hf : f = f') {g : b ⟶ c} {k : a ⟶ c}
    (h : f ≫ g = k) (h' : f' ≫ g = k) {X Y : D c} (φ : (P.pull g).obj X ⟶ (P.pull g).obj Y) :
    P.factorHom h φ = P.factorHom h' φ := by
  subst hf
  rfl

/-- **The maps attached to factorisations compose**: for `f ≫ g = k`, `g ≫ p = q`, `f ≫ q = r`
and `k ≫ p = r`, the map attached to `k ≫ p = r` is the map attached to `g ≫ p = q` followed by
the map attached to `f ≫ q = r`.  This is the associativity coherence of the datum. -/
theorem factorHom_comp (hP : P.IsCoherent) {d : A} {f : a ⟶ b} {g : b ⟶ c} {p : c ⟶ d}
    {k : a ⟶ c} {q : b ⟶ d} {r : a ⟶ d} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r)
    (hkr : k ≫ p = r) {X Y : D d} (φ : (P.pull p).obj X ⟶ (P.pull p).obj Y) :
    P.factorHom hkr φ = P.factorHom hr (P.factorHom hq φ) :=
  Functor.conjHom_comp _ _ _ _ (hP.triangle_comp' hk hq hr hkr) φ

/-- The maps attached to two factorisations of the same morphism through a commuting square
agree after composing. -/
private theorem factorHom_comp_comm (hP : P.IsCoherent) {d : A} {b' : A} {f : a ⟶ b} {g : b ⟶ c}
    {f' : a ⟶ b'} {g' : b' ⟶ c} {p : c ⟶ d} {q : b ⟶ d} {q' : b' ⟶ d} {r : a ⟶ d}
    (hsq : f ≫ g = f' ≫ g') (hq : g ≫ p = q) (hq' : g' ≫ p = q') (hr : f ≫ q = r)
    (hr' : f' ≫ q' = r) {X Y : D d} (φ : (P.pull p).obj X ⟶ (P.pull p).obj Y) :
    P.factorHom hr (P.factorHom hq φ) = P.factorHom hr' (P.factorHom hq' φ) := by
  rw [← factorHom_comp hP rfl hq hr (by rw [Category.assoc, hq, hr]),
    ← factorHom_comp hP rfl hq' hr' (by rw [Category.assoc, hq', hr'])]
  exact factorHom_congr hsq _ _ φ

/-- The map attached to a factorisation is natural in its source. -/
theorem factorHom_map_comp {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k)
    {X X' : D c} (Y : D c) (x : X ⟶ X') (φ : (P.pull g).obj X' ⟶ (P.pull g).obj Y) :
    P.factorHom h ((P.pull g).map x ≫ φ) = (P.pull k).map x ≫ P.factorHom h φ := by
  have nat := (P.triangle h).hom.naturality x
  simp only [Functor.comp_map] at nat
  simp only [factorHom, Functor.conjHom, Functor.map_comp, ← Category.assoc, nat]

/-- The map attached to a factorisation is natural in its target. -/
theorem factorHom_comp_map {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k)
    (X : D c) {Y Y' : D c} (y : Y ⟶ Y') (φ : (P.pull g).obj X ⟶ (P.pull g).obj Y) :
    P.factorHom h (φ ≫ (P.pull g).map y) = P.factorHom h φ ≫ (P.pull k).map y := by
  have nat := (P.triangle h).inv.naturality y
  simp only [Functor.comp_map] at nat
  simp only [factorHom, Functor.conjHom, Functor.map_comp, Category.assoc, nat]

section Preadditive

variable [∀ a, Preadditive (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]

/-- The map attached to a factorisation is additive. -/
theorem factorHom_add {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) {X Y : D c}
    (φ ψ : (P.pull g).obj X ⟶ (P.pull g).obj Y) :
    P.factorHom h (φ + ψ) = P.factorHom h φ + P.factorHom h ψ := by
  simp only [factorHom, Functor.conjHom, Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]

/-- The map attached to a factorisation sends `0` to `0`. -/
theorem factorHom_zero {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) (X Y : D c) :
    P.factorHom h (0 : (P.pull g).obj X ⟶ (P.pull g).obj Y) = 0 := by
  simp only [factorHom, Functor.conjHom, Functor.map_zero, zero_comp, comp_zero]

/-- The map attached to a factorisation commutes with subtraction. -/
theorem factorHom_sub {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) {X Y : D c}
    (φ ψ : (P.pull g).obj X ⟶ (P.pull g).obj Y) :
    P.factorHom h (φ - ψ) = P.factorHom h φ - P.factorHom h ψ := by
  simp only [factorHom, Functor.conjHom, Functor.map_sub, Preadditive.comp_sub,
    Preadditive.sub_comp]

end Preadditive

end Factor

/-! ### Systems over a base -/

/-- **A directed system over a base `b`, with a cone over it.**  The stages `T_j`, the structure
morphisms `k_j : T_j ⟶ b`, the transition morphisms `t_{ij} : T_j ⟶ T_i` over `b` for `i ≤ j`,
which compose, and a vertex `T` with a structure morphism `T ⟶ b` and projections `p_j : T ⟶ T_j`
over `b` compatible with the transition morphisms. -/
structure LimitSystem (b : A) (J : Type w) [Preorder J] where
  /-- The stage `T_j`. -/
  stage : J → A
  /-- The structure morphism `T_j ⟶ b`. -/
  toBase : ∀ j, stage j ⟶ b
  /-- The transition morphism `T_j ⟶ T_i` for `i ≤ j`. -/
  transition : ∀ {i j : J}, i ≤ j → (stage j ⟶ stage i)
  /-- The transition morphisms lie over `b`. -/
  transition_toBase : ∀ {i j : J} (h : i ≤ j), transition h ≫ toBase i = toBase j
  /-- The transition morphisms compose. -/
  transition_comp : ∀ {i j k : J} (h : i ≤ j) (h' : j ≤ k),
    transition h' ≫ transition h = transition (h.trans h')
  /-- The vertex `T`. -/
  limit : A
  /-- The structure morphism `T ⟶ b`. -/
  limitToBase : limit ⟶ b
  /-- The projection `T ⟶ T_j`. -/
  proj : ∀ j, limit ⟶ stage j
  /-- The projections lie over `b`. -/
  proj_toBase : ∀ j, proj j ≫ toBase j = limitToBase
  /-- The projections are compatible with the transition morphisms. -/
  proj_transition : ∀ {i j : J} (h : i ≤ j), proj j ≫ transition h = proj i

namespace LimitSystem

variable {P} {b : A} {J : Type w} [Preorder J] (S : LimitSystem (A := A) b J)

/-- The transition map `Hom(k_i^*X, k_i^*Y) ⟶ Hom(k_j^*X, k_j^*Y)` for `i ≤ j`. -/
def trans (P : PullbackData A D) (X Y : D b) (i j : J) (h : i ≤ j) :
    ((P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) →
      ((P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) :=
  P.factorHom (S.transition_toBase h)

/-- The map `Hom(k_j^*X, k_j^*Y) ⟶ Hom(k^*X, k^*Y)` to the vertex. -/
def projHom (P : PullbackData A D) (X Y : D b) (j : J) :
    ((P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) →
      ((P.pull S.limitToBase).obj X ⟶ (P.pull S.limitToBase).obj Y) :=
  P.factorHom (S.proj_toBase j)

/-- **`Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)`**, in the
elementwise form `Stacks.IsStagesColimit`. -/
def IsColim (P : PullbackData A D) (X Y : D b) : Prop :=
  Stacks.IsStagesColimit (S.trans P X Y) (S.projHom P X Y)

variable {S}

section Coherent

variable (hP : P.IsCoherent)
include hP

/-- The maps to the vertex are compatible with the transition maps. -/
theorem projHom_trans (X Y : D b) {i j : J} (h : i ≤ j)
    (φ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    S.projHom P X Y j (S.trans P X Y i j h φ) = S.projHom P X Y i φ :=
  (factorHom_comp hP (S.proj_transition h) (S.transition_toBase h) (S.proj_toBase j)
    (S.proj_toBase i) φ).symm

/-- The transition maps compose. -/
theorem trans_trans (X Y : D b) {i j k : J} (h : i ≤ j) (h' : j ≤ k)
    (φ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    S.trans P X Y j k h' (S.trans P X Y i j h φ) = S.trans P X Y i k (h.trans h') φ :=
  (factorHom_comp hP (S.transition_comp h h') (S.transition_toBase h)
    (S.transition_toBase h') (S.transition_toBase (h.trans h')) φ).symm

end Coherent

/-- The transition maps commute with precomposition by the pullback of a morphism `X ⟶ X'`. -/
theorem trans_map_comp {X X' : D b} (Y : D b) (x : X ⟶ X') {i j : J} (h : i ≤ j)
    (φ : (P.pull (S.toBase i)).obj X' ⟶ (P.pull (S.toBase i)).obj Y) :
    S.trans P X Y i j h ((P.pull (S.toBase i)).map x ≫ φ) =
      (P.pull (S.toBase j)).map x ≫ S.trans P X' Y i j h φ :=
  factorHom_map_comp _ Y x φ

/-- The maps to the vertex commute with precomposition by the pullback of a morphism `X ⟶ X'`. -/
theorem projHom_map_comp {X X' : D b} (Y : D b) (x : X ⟶ X') (j : J)
    (φ : (P.pull (S.toBase j)).obj X' ⟶ (P.pull (S.toBase j)).obj Y) :
    S.projHom P X Y j ((P.pull (S.toBase j)).map x ≫ φ) =
      (P.pull S.limitToBase).map x ≫ S.projHom P X' Y j φ :=
  factorHom_map_comp _ Y x φ

/-- The transition maps commute with postcomposition by the pullback of a morphism `Y ⟶ Y'`. -/
theorem trans_comp_map (X : D b) {Y Y' : D b} (y : Y ⟶ Y') {i j : J} (h : i ≤ j)
    (φ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    S.trans P X Y' i j h (φ ≫ (P.pull (S.toBase i)).map y) =
      S.trans P X Y i j h φ ≫ (P.pull (S.toBase j)).map y :=
  factorHom_comp_map _ X y φ

/-- The maps to the vertex commute with postcomposition by the pullback of a morphism `Y ⟶ Y'`. -/
theorem projHom_comp_map (X : D b) {Y Y' : D b} (y : Y ⟶ Y') (j : J)
    (φ : (P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) :
    S.projHom P X Y' j (φ ≫ (P.pull (S.toBase j)).map y) =
      S.projHom P X Y j φ ≫ (P.pull S.limitToBase).map y :=
  factorHom_comp_map _ X y φ

/-! ### Invariance under isomorphisms -/

section Iso

variable (hP : P.IsCoherent)
include hP

/-- The statement depends on its first argument only up to isomorphism. -/
theorem IsColim.of_iso_fst [IsDirected J (· ≤ ·)] {X X' : D b} {Y : D b} (e : X ≅ X')
    (hX : S.IsColim P X Y) : S.IsColim P X' Y where
  ι_trans i j h φ := projHom_trans hP X' Y h φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := hX.exists_stage ((P.pull S.limitToBase).map e.hom ≫ ψ)
    refine ⟨i, (P.pull (S.toBase i)).map e.inv ≫ φ, ?_⟩
    rw [projHom_map_comp, hφ, ← Functor.map_comp_assoc, e.inv_hom_id, Functor.map_id,
      Category.id_comp]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := hX.exists_trans_eq i ((P.pull (S.toBase i)).map e.hom ≫ φ)
      ((P.pull (S.toBase i)).map e.hom ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_map_comp, trans_map_comp] at hj
    simpa only [← Functor.map_comp_assoc, e.inv_hom_id, Functor.map_id, Category.id_comp]
      using congrArg (fun t => (P.pull (S.toBase j)).map e.inv ≫ t) hj

/-- The statement depends on its second argument only up to isomorphism. -/
theorem IsColim.of_iso_snd [IsDirected J (· ≤ ·)] (X : D b) {Y Y' : D b} (e : Y ≅ Y')
    (hY : S.IsColim P X Y) : S.IsColim P X Y' where
  ι_trans i j h φ := projHom_trans hP X Y' h φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := hY.exists_stage (ψ ≫ (P.pull S.limitToBase).map e.inv)
    refine ⟨i, φ ≫ (P.pull (S.toBase i)).map e.hom, ?_⟩
    rw [projHom_comp_map, hφ, Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      Functor.map_id, Category.comp_id]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := hY.exists_trans_eq i (φ ≫ (P.pull (S.toBase i)).map e.inv)
      (φ' ≫ (P.pull (S.toBase i)).map e.inv) (by rw [projHom_comp_map, projHom_comp_map, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_comp_map, trans_comp_map] at hj
    simpa only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id,
      Category.comp_id] using congrArg (fun t => t ≫ (P.pull (S.toBase j)).map e.hom) hj

/-- The statement for isomorphic pairs of objects agrees. -/
theorem isColim_iff_of_iso [IsDirected J (· ≤ ·)] {X X' Y Y' : D b} (e : X ≅ X')
    (e' : Y ≅ Y') : S.IsColim P X Y ↔ S.IsColim P X' Y' :=
  ⟨fun h => (h.of_iso_fst hP e).of_iso_snd hP X' e',
    fun h => (h.of_iso_fst hP e.symm).of_iso_snd hP X e'.symm⟩

end Iso

/-! ### Binary biproducts and distinguished triangles in the first argument -/

section Additive

variable [∀ a, Preadditive (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]

/-- The transition maps send zero to zero. -/
theorem trans_zero (X Y : D b) {i j : J} (h : i ≤ j) : S.trans P X Y i j h 0 = 0 :=
  factorHom_zero _ X Y

/-- The maps to the vertex send zero to zero. -/
theorem projHom_zero (X Y : D b) (j : J) : S.projHom P X Y j 0 = 0 :=
  factorHom_zero _ X Y

/-- The transition maps commute with subtraction. -/
theorem trans_sub (X Y : D b) {i j : J} (h : i ≤ j)
    (φ ψ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    S.trans P X Y i j h (φ - ψ) = S.trans P X Y i j h φ - S.trans P X Y i j h ψ :=
  factorHom_sub _ φ ψ

/-- The maps to the vertex commute with subtraction. -/
theorem projHom_sub (X Y : D b) (j : J)
    (φ ψ : (P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) :
    S.projHom P X Y j (φ - ψ) = S.projHom P X Y j φ - S.projHom P X Y j ψ :=
  factorHom_sub _ φ ψ

/-- The maps to the vertex commute with addition. -/
theorem projHom_add (X Y : D b) (j : J)
    (φ ψ : (P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) :
    S.projHom P X Y j (φ + ψ) = S.projHom P X Y j φ + S.projHom P X Y j ψ :=
  factorHom_add _ φ ψ

/-- A morphism out of the image of a binary biproduct under an additive functor is the sum of
its two components. -/
theorem eq_map_fst_comp_add {C E : Type*} [Category* C] [Category* E] [Preadditive C]
    [Preadditive E] (F : C ⥤ E) [F.Additive] {A₁ A₂ : C} [HasBinaryBiproduct A₁ A₂] {W : E}
    (x : F.obj (A₁ ⊞ A₂) ⟶ W) :
    x = F.map biprod.fst ≫ F.map biprod.inl ≫ x + F.map biprod.snd ≫ F.map biprod.inr ≫ x := by
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Preadditive.add_comp, ← F.map_add,
    biprod.total, Functor.map_id, Category.id_comp]

variable (hP : P.IsCoherent)
include hP

/-- **The statement is closed under binary biproducts in its first argument.** -/
theorem IsColim.biprod [IsDirected J (· ≤ ·)] {X₁ X₂ Y : D b} [HasBinaryBiproduct X₁ X₂]
    (h₁ : S.IsColim P X₁ Y) (h₂ : S.IsColim P X₂ Y) : S.IsColim P (X₁ ⊞ X₂) Y where
  ι_trans i j h φ := projHom_trans hP _ Y h φ
  exists_stage ψ := by
    obtain ⟨i₁, φ₁, hφ₁⟩ := h₁.exists_stage ((P.pull S.limitToBase).map biprod.inl ≫ ψ)
    obtain ⟨i₂, φ₂, hφ₂⟩ := h₂.exists_stage ((P.pull S.limitToBase).map biprod.inr ≫ ψ)
    obtain ⟨m, h₁m, h₂m⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨m, (P.pull (S.toBase m)).map biprod.fst ≫ S.trans P X₁ Y i₁ m h₁m φ₁ +
      (P.pull (S.toBase m)).map biprod.snd ≫ S.trans P X₂ Y i₂ m h₂m φ₂, ?_⟩
    rw [projHom_add, projHom_map_comp, projHom_map_comp, projHom_trans hP,
      projHom_trans hP, hφ₁, hφ₂]
    exact (eq_map_fst_comp_add (P.pull S.limitToBase) ψ).symm
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j₁, hij₁, hj₁⟩ := h₁.exists_trans_eq i ((P.pull (S.toBase i)).map biprod.inl ≫ φ)
      ((P.pull (S.toBase i)).map biprod.inl ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    obtain ⟨j₂, hij₂, hj₂⟩ := h₂.exists_trans_eq i ((P.pull (S.toBase i)).map biprod.inr ≫ φ)
      ((P.pull (S.toBase i)).map biprod.inr ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    obtain ⟨m, h₁m, h₂m⟩ := directed_of (· ≤ ·) j₁ j₂
    refine ⟨m, hij₁.trans h₁m, ?_⟩
    have e₁ := congrArg (S.trans P X₁ Y j₁ m h₁m) hj₁
    have e₂ := congrArg (S.trans P X₂ Y j₂ m h₂m) hj₂
    simp only [trans_trans hP, trans_map_comp] at e₁ e₂
    rw [eq_map_fst_comp_add (P.pull (S.toBase m)) (S.trans P _ Y i m _ φ),
      eq_map_fst_comp_add (P.pull (S.toBase m)) (S.trans P _ Y i m _ φ')]
    rw [show (hij₁.trans h₁m) = (hij₂.trans h₂m) from rfl] at e₁
    rw [e₁, e₂]

end Additive

section Triangulated

variable [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)] [∀ a, HasShift (D a) ℤ]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated]

/-- **The five lemma: the statement is closed under distinguished triangles in its first
argument.**  For a distinguished triangle `A₁ ⟶ A₂ ⟶ A₃ ⟶ A₁⟦1⟧` of `D b`, the statement for
`A₁`, `A₂`, `A₁⟦1⟧` and `A₂⟦1⟧` gives the statement for `A₃`. -/
theorem IsColim.obj₃ (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] {A₁ A₂ A₃ Y : D b}
    {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃} {h : A₃ ⟶ A₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang (D b))
    (h₁ : S.IsColim P A₁ Y) (h₂ : S.IsColim P A₂ Y) (h₁' : S.IsColim P (A₁⟦(1 : ℤ)⟧) Y)
    (h₂' : S.IsColim P (A₂⟦(1 : ℤ)⟧) Y) : S.IsColim P A₃ Y where
  ι_trans i j hij φ := projHom_trans hP A₃ Y hij φ
  exists_stage ψ := by
    obtain ⟨i, y, hy⟩ := h₂.exists_stage ((P.pull S.limitToBase).map g ≫ ψ)
    have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    obtain ⟨j, hij, hj⟩ := h₁.exists_trans_eq i ((P.pull (S.toBase i)).map f ≫ y) 0 (by
      rw [projHom_map_comp, hy, projHom_zero, ← Functor.map_comp_assoc, hfg,
        Functor.map_zero, zero_comp])
    rw [trans_map_comp] at hj
    have hj' : (P.pull (S.toBase j)).map f ≫ S.trans P A₂ Y i j hij y = 0 :=
      hj.trans (trans_zero _ _ _)
    obtain ⟨x, hx⟩ := Stacks.LimitHomDescent.SchemeSystem.exists_eq_map_comp₂
      (P.pull (S.toBase j)) f g h hT _ hj'
    have hd : (P.pull S.limitToBase).map g ≫ (S.projHom P A₃ Y j x - ψ) = 0 := by
      rw [Preadditive.comp_sub, ← projHom_map_comp, ← hx, projHom_trans hP, hy, sub_self]
    obtain ⟨s, hs⟩ := Stacks.LimitHomDescent.SchemeSystem.exists_eq_map_comp₃
      (P.pull S.limitToBase) f g h hT _ hd
    obtain ⟨k, z, hz⟩ := h₁'.exists_stage s
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    refine ⟨m, S.trans P A₃ Y j m hjm x -
      (P.pull (S.toBase m)).map h ≫ S.trans P _ Y k m hkm z, ?_⟩
    rw [projHom_sub, projHom_map_comp, projHom_trans hP, projHom_trans hP, hz, ← hs,
      sub_sub_cancel]
  exists_trans_eq i x x' hxx := by
    have hw : S.projHom P A₃ Y i (x - x') = 0 := by
      rw [projHom_sub, hxx, sub_self]
    obtain ⟨j, hij, hj⟩ := h₂.exists_trans_eq i ((P.pull (S.toBase i)).map g ≫ (x - x')) 0 (by
      rw [projHom_map_comp, hw, comp_zero, projHom_zero])
    rw [trans_map_comp, trans_zero] at hj
    obtain ⟨s, hs⟩ := Stacks.LimitHomDescent.SchemeSystem.exists_eq_map_comp₃
      (P.pull (S.toBase j)) f g h hT _ hj
    have hps : (P.pull S.limitToBase).map h ≫ S.projHom P _ Y j s = 0 := by
      rw [← projHom_map_comp, ← hs, projHom_trans hP, hw]
    obtain ⟨r, hr⟩ := Stacks.LimitHomDescent.SchemeSystem.exists_eq_map_comp₁
      (P.pull S.limitToBase) f g h hT _ hps
    obtain ⟨k, q, hq⟩ := h₂'.exists_stage r
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    obtain ⟨m, hlm, hm⟩ := h₁'.exists_trans_eq l
      (S.trans P _ Y j l hjl s - (P.pull (S.toBase l)).map (f⟦(1 : ℤ)⟧') ≫
        S.trans P _ Y k l hkl q) 0
      (by
        rw [projHom_sub, projHom_map_comp, projHom_trans hP, projHom_trans hP, hq, ← hr,
          sub_self, projHom_zero])
    refine ⟨m, hij.trans (hjl.trans hlm), ?_⟩
    rw [trans_sub, trans_zero, sub_eq_zero, trans_trans hP, trans_map_comp,
      trans_trans hP] at hm
    have hhf : h ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    have key : S.trans P A₃ Y i m (hij.trans (hjl.trans hlm)) (x - x') = 0 := by
      rw [← trans_trans hP A₃ Y hij (hjl.trans hlm), hs, trans_map_comp, hm,
        ← Functor.map_comp_assoc, hhf, Functor.map_zero, zero_comp]
    rw [trans_sub] at key
    exact sub_eq_zero.mp key

end Triangulated

/-! ### Morphisms of systems -/

/-- **A morphism of systems over `b`**, from `S'` to `S`: morphisms from the stages and the
vertex of `S'` to those of `S`, over `b` and compatible with the transition morphisms and the
projections. -/
structure Hom (S' S : LimitSystem (A := A) b J) where
  /-- The morphism of stages. -/
  app : ∀ j, S'.stage j ⟶ S.stage j
  app_toBase : ∀ j, app j ≫ S.toBase j = S'.toBase j
  app_transition : ∀ {i j : J} (h : i ≤ j), app j ≫ S.transition h = S'.transition h ≫ app i
  /-- The morphism of vertices. -/
  limitApp : S'.limit ⟶ S.limit
  limitApp_toBase : limitApp ≫ S.limitToBase = S'.limitToBase
  limitApp_proj : ∀ j, limitApp ≫ S.proj j = S'.proj j ≫ app j

namespace Hom

variable {S' : LimitSystem (A := A) b J} (α : Hom S' S) (X Y : D b)

/-- The map of morphism sets induced by a morphism of systems at a stage. -/
def stageMap (P : PullbackData A D) (j : J) :
    ((P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) →
      ((P.pull (S'.toBase j)).obj X ⟶ (P.pull (S'.toBase j)).obj Y) :=
  P.factorHom (α.app_toBase j)

/-- The map of morphism sets induced by a morphism of systems at the vertex. -/
def limitMap (P : PullbackData A D) :
    ((P.pull S.limitToBase).obj X ⟶ (P.pull S.limitToBase).obj Y) →
      ((P.pull S'.limitToBase).obj X ⟶ (P.pull S'.limitToBase).obj Y) :=
  P.factorHom α.limitApp_toBase

variable (hP : P.IsCoherent)
include hP

/-- The maps induced by a morphism of systems at the stages commute with the transition maps. -/
theorem stageMap_trans {i j : J} (h : i ≤ j)
    (φ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    α.stageMap X Y P j (S.trans P X Y i j h φ) = S'.trans P X Y i j h (α.stageMap X Y P i φ) := by
  exact factorHom_comp_comm hP (α.app_transition h) (S.transition_toBase h) (α.app_toBase i)
    (α.app_toBase j) (S'.transition_toBase h) φ

/-- The maps induced by a morphism of systems at the stages and at the vertex commute with the maps
to the vertex. -/
theorem limitMap_projHom (j : J)
    (φ : (P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y) :
    α.limitMap X Y P (S.projHom P X Y j φ) = S'.projHom P X Y j (α.stageMap X Y P j φ) := by
  exact factorHom_comp_comm hP (α.limitApp_proj j) (S.proj_toBase j) (α.app_toBase j)
    α.limitApp_toBase (S'.proj_toBase j) φ

/-- **Transfer along a morphism of systems inducing bijections on morphism sets.** -/
theorem isColim_iff (hst : ∀ j, Function.Bijective (α.stageMap X Y P j))
    (hlim : Function.Bijective (α.limitMap X Y P)) :
    S.IsColim P X Y ↔ S'.IsColim P X Y := by
  refine ⟨fun hS => ?_, fun hS' => ?_⟩
  · refine Stacks.IsStagesColimit.ofEquiv (S'.trans P X Y) (S'.projHom P X Y)
      (fun j => (Equiv.ofBijective _ (hst j)).symm) (Equiv.ofBijective _ hlim).symm ?_ ?_ hS
    · intro i j h s
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, stageMap_trans α X Y hP]
      exact congrArg _ (Equiv.ofBijective_apply_symm_apply _ (hst i) s).symm
    · intro i s
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, limitMap_projHom α X Y hP]
      exact congrArg _ (Equiv.ofBijective_apply_symm_apply _ (hst i) s).symm
  · refine Stacks.IsStagesColimit.ofEquiv (S.trans P X Y) (S.projHom P X Y)
      (fun j => Equiv.ofBijective _ (hst j)) (Equiv.ofBijective _ hlim) ?_ ?_ hS'
    · intro i j h s
      simp only [Equiv.ofBijective_apply, stageMap_trans α X Y hP]
    · intro i s
      simp only [Equiv.ofBijective_apply, limitMap_projHom α X Y hP]

end Hom

/-! ### Change of base -/

/-- The system `S` read over `b'` through a morphism `f : b ⟶ b'`. -/
def comp {b' : A} (f : b ⟶ b') : LimitSystem (A := A) b' J where
  stage := S.stage
  toBase j := S.toBase j ≫ f
  transition := S.transition
  transition_toBase h := by rw [← Category.assoc, S.transition_toBase]
  transition_comp := S.transition_comp
  limit := S.limit
  limitToBase := S.limitToBase ≫ f
  proj := S.proj
  proj_toBase j := by rw [← Category.assoc, S.proj_toBase]
  proj_transition := S.proj_transition

/-- Conjugating by the comparisons of two factorisations through `f^*` commutes with the map
attached to a further factorisation. -/
theorem factorHom_compEquiv (hP : P.IsCoherent) {V W b' : A} (t : V ⟶ W) (a : W ⟶ b)
    (c : V ⟶ b) (f : b ⟶ b') (hc : t ≫ a = c) (X Y : D b')
    (φ : (P.pull a).obj ((P.pull f).obj X) ⟶ (P.pull a).obj ((P.pull f).obj Y)) :
    P.factorHom (show t ≫ (a ≫ f) = c ≫ f by rw [← Category.assoc, hc])
        (P.compEquiv a f X Y φ) =
      P.compEquiv c f X Y (P.factorHom hc φ) := by
  have key := hP.triangle_comp (f := t) (g := a) (p := f) (k := c) (q := a ≫ f) (r := c ≫ f)
    hc rfl (by rw [← Category.assoc, hc]) rfl
  have hX := NatTrans.congr_app (congrArg Iso.hom key) X
  have hY := NatTrans.congr_app (congrArg Iso.inv key) Y
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] at hX hY
  simp only [factorHom, compEquiv, Functor.conjHom, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  simp only [triangle_rfl] at hX hY
  rw [← reassoc_of% hX, hY]

/-- **Change of base.**  The statement for `S` read over `b'` at `X`, `Y` is the statement for
`S` at `f^*X`, `f^*Y`. -/
theorem isColim_comp_iff (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] {b' : A} (f : b ⟶ b')
    (X Y : D b') :
    (S.comp f).IsColim P X Y ↔ S.IsColim P ((P.pull f).obj X) ((P.pull f).obj Y) := by
  let e : ∀ j : J, ((P.pull (S.toBase j)).obj ((P.pull f).obj X) ⟶
      (P.pull (S.toBase j)).obj ((P.pull f).obj Y)) ≃
      ((P.pull ((S.comp f).toBase j)).obj X ⟶ (P.pull ((S.comp f).toBase j)).obj Y) := fun j =>
    P.compEquiv (S.toBase j) f X Y
  let eT : ((P.pull S.limitToBase).obj ((P.pull f).obj X) ⟶
      (P.pull S.limitToBase).obj ((P.pull f).obj Y)) ≃
      ((P.pull (S.comp f).limitToBase).obj X ⟶ (P.pull (S.comp f).limitToBase).obj Y) :=
    P.compEquiv S.limitToBase f X Y
  have he : ∀ (i j : J) (h : i ≤ j) (s : (P.pull (S.toBase i)).obj ((P.pull f).obj X) ⟶
      (P.pull (S.toBase i)).obj ((P.pull f).obj Y)),
      e j (S.trans P _ _ i j h s) = (S.comp f).trans P X Y i j h (e i s) := fun i j h s =>
    (factorHom_compEquiv hP (S.transition h) (S.toBase i) (S.toBase j) f
      (S.transition_toBase h) X Y s).symm
  have heT : ∀ (i : J) (s : (P.pull (S.toBase i)).obj ((P.pull f).obj X) ⟶
      (P.pull (S.toBase i)).obj ((P.pull f).obj Y)),
      eT (S.projHom P _ _ i s) = (S.comp f).projHom P X Y i (e i s) := fun i s =>
    (factorHom_compEquiv hP (S.proj i) (S.toBase i) S.limitToBase f (S.proj_toBase i) X Y
      s).symm
  refine ⟨Stacks.IsStagesColimit.ofEquiv (S.trans P _ _) (S.projHom P _ _) e eT he heT,
    fun h => ?_⟩
  refine Stacks.IsStagesColimit.ofEquiv ((S.comp f).trans P X Y) ((S.comp f).projHom P X Y)
    (fun j => (e j).symm) eT.symm ?_ ?_ h
  · intro i j hij s
    apply (e j).injective
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
  · intro i s
    apply eT.injective
    rw [Equiv.apply_symm_apply, heT, Equiv.apply_symm_apply]

end LimitSystem

end CategoryTheory.PullbackData

end
