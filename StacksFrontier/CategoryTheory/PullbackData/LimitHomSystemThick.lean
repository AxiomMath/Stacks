module

public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The colimit statement for a system over a base is closed under thick operations

Let `P` be a coherent pullback pseudofunctor datum with triangulated fibres and triangulated
inverse images, and let `S` be a directed system over a base `b` with a cone.  For objects `X`,
`Y` of the fibre over `b`, `CategoryTheory.PullbackData.LimitSystem.IsColim` says that
`Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)`.  The file
`StacksFrontier/CategoryTheory/PullbackData/LimitHomSystem.lean` proves that this statement is
invariant under isomorphisms and closed under binary biproducts and distinguished triangles in its
*first* argument.  This file adds the closure under retracts in both arguments, under zero objects,
and under distinguished triangles in the *second* argument, and deduces that the statement with
both arguments shifted arbitrarily cuts out a **thick** subcategory in each argument.  Hence it
holds for all objects of the triangulated envelope of an object `G` as soon as it holds for `G`
against itself with arbitrary shifts.

## Main definitions

* `CategoryTheory.PullbackData.LimitSystem.IsShiftedColim`: the colimit statement for `X⟦n⟧` and
  `Y⟦m⟧`, for all integers `n` and `m`.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_retract_fst` and `of_retract_snd`: closure
  under retracts.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_isZero_fst`: a zero first argument.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.obj₃_snd`: the five lemma in the second
  argument.
* `CategoryTheory.PullbackData.LimitSystem.isShiftedColim_of_triangEnvelope`: the statement holds
  on the triangulated envelope of `G` as soon as it holds for `G` against itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {P : PullbackData A D}

namespace LimitSystem

variable {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}

/-! ### Retracts -/

section Retract

variable (hP : P.IsCoherent)
include hP

/-- **The statement passes to a retract of its first argument.** -/
theorem IsColim.of_retract_fst {X X' Y : D b} (r : Retract X X') (h : S.IsColim P X' Y) :
    S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := h.exists_stage ((P.pull S.limitToBase).map r.r ≫ ψ)
    refine ⟨i, (P.pull (S.toBase i)).map r.i ≫ φ, ?_⟩
    rw [projHom_map_comp, hφ, ← Functor.map_comp_assoc, r.retract, Functor.map_id,
      Category.id_comp]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := h.exists_trans_eq i ((P.pull (S.toBase i)).map r.r ≫ φ)
      ((P.pull (S.toBase i)).map r.r ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_map_comp, trans_map_comp] at hj
    have := congrArg (fun t => (P.pull (S.toBase j)).map r.i ≫ t) hj
    simpa only [← Functor.map_comp_assoc, r.retract, Functor.map_id, Category.id_comp]
      using this

/-- **The statement passes to a retract of its second argument.** -/
theorem IsColim.of_retract_snd (X : D b) {Y Y' : D b} (r : Retract Y Y')
    (h : S.IsColim P X Y') : S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := h.exists_stage (ψ ≫ (P.pull S.limitToBase).map r.i)
    refine ⟨i, φ ≫ (P.pull (S.toBase i)).map r.r, ?_⟩
    rw [projHom_comp_map, hφ, Category.assoc, ← Functor.map_comp, r.retract, Functor.map_id,
      Category.comp_id]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := h.exists_trans_eq i (φ ≫ (P.pull (S.toBase i)).map r.i)
      (φ' ≫ (P.pull (S.toBase i)).map r.i) (by rw [projHom_comp_map, projHom_comp_map, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_comp_map, trans_comp_map] at hj
    have := congrArg (fun t => t ≫ (P.pull (S.toBase j)).map r.r) hj
    simpa only [Category.assoc, ← Functor.map_comp, r.retract, Functor.map_id,
      Category.comp_id] using this

end Retract

/-! ### Zero objects -/

section Zero

variable [∀ a, Preadditive (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
  (hP : P.IsCoherent)
include hP

/-- **The statement holds when the first argument is a zero object**: every morphism set of the
system is then a singleton. -/
theorem IsColim.of_isZero_fst [Nonempty J] {X : D b} (Y : D b) (hX : IsZero X) :
    S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i⟩ := (inferInstance : Nonempty J)
    exact ⟨i, 0, ((Functor.map_isZero (P.pull S.limitToBase) hX).eq_of_src _ _)⟩
  exists_trans_eq i φ φ' _ :=
    ⟨i, le_refl i, congrArg _ ((Functor.map_isZero (P.pull (S.toBase i)) hX).eq_of_src φ φ')⟩

end Zero

/-! ### Distinguished triangles in the second argument -/

section Triangle

variable {C E : Type*} [Category* C] [Category* E] [HasZeroObject C] [HasZeroObject E]
  [Preadditive C] [Preadditive E] [HasShift C ℤ] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated E] (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
  {B₁ B₂ B₃ : C} (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) (h : B₃ ⟶ B₁⟦(1 : ℤ)⟧)
  (hT : Triangle.mk f g h ∈ distTriang C) {W : E}

include hT

/-- Exactness of `Hom(W, F(-))` at `F(B₂)` for a distinguished triangle. -/
theorem exists_eq_comp_map₂ (φ : W ⟶ F.obj B₂) (hφ : φ ≫ F.map g = 0) :
    ∃ ψ : W ⟶ F.obj B₁, φ = ψ ≫ F.map f :=
  Triangle.coyoneda_exact₂ _ (F.map_distinguished _ hT) φ hφ

/-- Exactness of `Hom(W, F(-))` at `F(B₃)` for a distinguished triangle. -/
theorem exists_eq_comp_map₃ (φ : W ⟶ F.obj B₃) (hφ : φ ≫ F.map h = 0) :
    ∃ ψ : W ⟶ F.obj B₂, φ = ψ ≫ F.map g :=
  Triangle.coyoneda_exact₃ _ (F.map_distinguished _ hT) φ (by
    change φ ≫ F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app B₁ = 0
    rw [← Category.assoc, hφ, zero_comp])

/-- Exactness of `Hom(W, F(-))` at `F(B₁⟦1⟧)` for a distinguished triangle. -/
theorem exists_eq_comp_map₁ (φ : W ⟶ F.obj (B₁⟦(1 : ℤ)⟧)) (hφ : φ ≫ F.map (f⟦(1 : ℤ)⟧') = 0) :
    ∃ ψ : W ⟶ F.obj B₃, φ = ψ ≫ F.map h :=
  exists_eq_comp_map₃ F g h (-f⟦(1 : ℤ)⟧') (rot_of_distTriang _ hT) φ (by
    rw [F.map_neg, Preadditive.comp_neg, hφ, neg_zero])

end Triangle

/-- A shift-stable property closed under third objects and containing zero is triangulated. -/
private theorem isTriangulated_of_isTriangulatedClosed₃ {C : Type*} [Category* C]
    [HasZeroObject C] [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (Q : ObjectProperty C) [Q.IsStableUnderShift ℤ]
    [Q.IsTriangulatedClosed₃] (h₀ : Q 0) : Q.IsTriangulated :=
  have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  { exists_zero := ⟨0, isZero_zero _, h₀⟩ }

section Triangulated

variable [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)] [∀ a, HasShift (D a) ℤ]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated]

/-- **The five lemma in the second argument.**  For a distinguished triangle
`B₁ ⟶ B₂ ⟶ B₃ ⟶ B₁⟦1⟧` of the fibre over `b`, the statement for `B₁`, `B₂`, `B₁⟦1⟧` and `B₂⟦1⟧`
gives the statement for `B₃`. -/
theorem IsColim.obj₃_snd (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] (X : D b) {B₁ B₂ B₃ : D b}
    {f : B₁ ⟶ B₂} {g : B₂ ⟶ B₃} {h : B₃ ⟶ B₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang (D b))
    (h₁ : S.IsColim P X B₁) (h₂ : S.IsColim P X B₂) (h₁' : S.IsColim P X (B₁⟦(1 : ℤ)⟧))
    (h₂' : S.IsColim P X (B₂⟦(1 : ℤ)⟧)) : S.IsColim P X B₃ where
  ι_trans i j hij φ := projHom_trans hP X B₃ hij φ
  exists_stage ψ := by
    have hhf : h ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    obtain ⟨i, y, hy⟩ := h₁'.exists_stage (ψ ≫ (P.pull S.limitToBase).map h)
    obtain ⟨j, hij, hj⟩ := h₂'.exists_trans_eq i (y ≫ (P.pull (S.toBase i)).map (f⟦(1 : ℤ)⟧')) 0
      (by rw [projHom_comp_map, hy, projHom_zero, Category.assoc, ← Functor.map_comp, hhf,
        Functor.map_zero, comp_zero])
    rw [trans_comp_map, trans_zero] at hj
    obtain ⟨x, hx⟩ := exists_eq_comp_map₁ (P.pull (S.toBase j)) f g h hT _ hj
    have hd : (S.projHom P X B₃ j x - ψ) ≫ (P.pull S.limitToBase).map h = 0 := by
      rw [Preadditive.sub_comp, ← projHom_comp_map, ← hx, projHom_trans hP, hy, sub_self]
    obtain ⟨s, hs⟩ := exists_eq_comp_map₃ (P.pull S.limitToBase) f g h hT _ hd
    obtain ⟨k, z, hz⟩ := h₂.exists_stage s
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    refine ⟨m, S.trans P X B₃ j m hjm x -
      S.trans P X B₂ k m hkm z ≫ (P.pull (S.toBase m)).map g, ?_⟩
    rw [projHom_sub, projHom_comp_map, projHom_trans hP, projHom_trans hP, hz, ← hs,
      sub_sub_cancel]
  exists_trans_eq i x x' hxx := by
    have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    have hw : S.projHom P X B₃ i (x - x') = 0 := by
      rw [projHom_sub, hxx, sub_self]
    obtain ⟨j, hij, hj⟩ := h₁'.exists_trans_eq i ((x - x') ≫ (P.pull (S.toBase i)).map h) 0
      (by rw [projHom_comp_map, hw, zero_comp, projHom_zero])
    rw [trans_comp_map, trans_zero] at hj
    obtain ⟨s, hs⟩ := exists_eq_comp_map₃ (P.pull (S.toBase j)) f g h hT _ hj
    have hps : S.projHom P X B₂ j s ≫ (P.pull S.limitToBase).map g = 0 := by
      rw [← projHom_comp_map, ← hs, projHom_trans hP, hw]
    obtain ⟨r, hr⟩ := exists_eq_comp_map₂ (P.pull S.limitToBase) f g h hT _ hps
    obtain ⟨k, q, hq⟩ := h₁.exists_stage r
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    obtain ⟨m, hlm, hm⟩ := h₂.exists_trans_eq l
      (S.trans P X B₂ j l hjl s - S.trans P X B₁ k l hkl q ≫ (P.pull (S.toBase l)).map f) 0
      (by
        rw [projHom_sub, projHom_comp_map, projHom_trans hP, projHom_trans hP, hq, ← hr,
          sub_self, projHom_zero])
    refine ⟨m, hij.trans (hjl.trans hlm), ?_⟩
    rw [trans_sub, trans_zero, sub_eq_zero, trans_trans hP, trans_comp_map,
      trans_trans hP] at hm
    have key : S.trans P X B₃ i m (hij.trans (hjl.trans hlm)) (x - x') = 0 := by
      rw [← trans_trans hP X B₃ hij (hjl.trans hlm), hs, trans_comp_map, hm, Category.assoc,
        ← Functor.map_comp, hfg, Functor.map_zero, comp_zero]
    rw [trans_sub] at key
    exact sub_eq_zero.mp key

/-! ### The statement with both arguments shifted -/

variable (S P) in
/-- **The colimit statement with both arguments shifted**: `Hom(k^*X⟦n⟧, k^*Y⟦m⟧)` is the filtered
colimit of the `Hom(k_j^*X⟦n⟧, k_j^*Y⟦m⟧)` for all integers `n` and `m`. -/
def IsShiftedColim (X Y : D b) : Prop :=
  ∀ n m : ℤ, S.IsColim P (X⟦n⟧) (Y⟦m⟧)

variable (S P) in
/-- The objects `X` for which the shifted statement holds against a fixed `Y`. -/
def shiftedColimFst (Y : D b) : ObjectProperty (D b) := fun X => S.IsShiftedColim P X Y

variable (S P) in
/-- The objects `Y` for which the shifted statement holds against a fixed `X`. -/
def shiftedColimSnd (X : D b) : ObjectProperty (D b) := fun Y => S.IsShiftedColim P X Y

variable (hP : P.IsCoherent) [IsDirected J (· ≤ ·)] [Nonempty J]
include hP

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [Nonempty J] in
/-- The objects `X` for which the shifted statement holds against a fixed `Y` are closed under
isomorphisms. -/
theorem isClosedUnderIsomorphisms_shiftedColimFst (Y : D b) :
    (S.shiftedColimFst P Y).IsClosedUnderIsomorphisms :=
  ⟨fun e hX n m => (hX n m).of_iso_fst hP ((shiftFunctor (D b) n).mapIso e)⟩

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [Nonempty J] in
/-- The objects `X` for which the shifted statement holds against a fixed `Y` are stable under
shifts. -/
theorem isStableUnderShift_shiftedColimFst (Y : D b) :
    (S.shiftedColimFst P Y).IsStableUnderShift ℤ :=
  ⟨fun a => ⟨fun X hX n m => (hX (a + n) m).of_iso_fst hP ((shiftFunctorAdd (D b) a n).app X)⟩⟩

omit [Nonempty J] in
/-- The objects `X` for which the shifted statement holds against a fixed `Y` are closed under
third objects of distinguished triangles. -/
theorem isTriangulatedClosed₃_shiftedColimFst (Y : D b) :
    (S.shiftedColimFst P Y).IsTriangulatedClosed₃ := by
  have := isClosedUnderIsomorphisms_shiftedColimFst (S := S) hP Y
  refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT h₁ h₂ n m => ?_
  have hT' := Triangle.shift_distinguished T hT n
  exact IsColim.obj₃ hP (f := ((shiftFunctor (Triangle (D b)) n).obj T).mor₁)
    (g := ((shiftFunctor (Triangle (D b)) n).obj T).mor₂)
    (h := ((shiftFunctor (Triangle (D b)) n).obj T).mor₃) hT' (h₁ n m) (h₂ n m)
    ((h₁ (n + 1) m).of_iso_fst hP ((shiftFunctorAdd (D b) n 1).app T.obj₁))
    ((h₂ (n + 1) m).of_iso_fst hP ((shiftFunctorAdd (D b) n 1).app T.obj₂))

/-- The objects `X` for which the shifted statement holds against a fixed `Y` form a
triangulated subcategory. -/
theorem isTriangulated_shiftedColimFst (Y : D b) :
    (S.shiftedColimFst P Y).IsTriangulated := by
  have := isStableUnderShift_shiftedColimFst (S := S) hP Y
  have := isTriangulatedClosed₃_shiftedColimFst (S := S) hP Y
  exact isTriangulated_of_isTriangulatedClosed₃ _ fun n m => IsColim.of_isZero_fst hP _
    (Functor.map_isZero (shiftFunctor (D b) n) (isZero_zero _))

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- The objects `X` for which the shifted statement holds against a fixed `Y` are stable under
retracts. -/
theorem isStableUnderRetracts_shiftedColimFst (Y : D b) :
    (S.shiftedColimFst P Y).IsStableUnderRetracts :=
  ⟨fun r hX n m => (hX n m).of_retract_fst hP (r.map (shiftFunctor (D b) n))⟩

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [Nonempty J] in
/-- The objects `Y` for which the shifted statement holds against a fixed `X` are closed under
isomorphisms. -/
theorem isClosedUnderIsomorphisms_shiftedColimSnd (X : D b) :
    (S.shiftedColimSnd P X).IsClosedUnderIsomorphisms :=
  ⟨fun e hY n m => (hY n m).of_iso_snd hP _ ((shiftFunctor (D b) m).mapIso e)⟩

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [Nonempty J] in
/-- The objects `Y` for which the shifted statement holds against a fixed `X` are stable under
shifts. -/
theorem isStableUnderShift_shiftedColimSnd (X : D b) :
    (S.shiftedColimSnd P X).IsStableUnderShift ℤ :=
  ⟨fun a => ⟨fun Y hY n m =>
    (hY n (a + m)).of_iso_snd hP _ ((shiftFunctorAdd (D b) a m).app Y)⟩⟩

omit [Nonempty J] in
/-- The objects `Y` for which the shifted statement holds against a fixed `X` are closed under
third objects of distinguished triangles. -/
theorem isTriangulatedClosed₃_shiftedColimSnd (X : D b) :
    (S.shiftedColimSnd P X).IsTriangulatedClosed₃ := by
  have := isClosedUnderIsomorphisms_shiftedColimSnd (S := S) hP X
  refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT h₁ h₂ n m => ?_
  have hT' := Triangle.shift_distinguished T hT m
  exact IsColim.obj₃_snd hP _ (f := ((shiftFunctor (Triangle (D b)) m).obj T).mor₁)
    (g := ((shiftFunctor (Triangle (D b)) m).obj T).mor₂)
    (h := ((shiftFunctor (Triangle (D b)) m).obj T).mor₃) hT' (h₁ n m) (h₂ n m)
    ((h₁ n (m + 1)).of_iso_snd hP _ ((shiftFunctorAdd (D b) m 1).app T.obj₁))
    ((h₂ n (m + 1)).of_iso_snd hP _ ((shiftFunctorAdd (D b) m 1).app T.obj₂))

omit [IsDirected J (· ≤ ·)] in
/-- The statement holds when the second argument is a zero object. -/
theorem IsColim.of_isZero_snd (X : D b) {Y : D b} (hY : IsZero Y) : S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i⟩ := (inferInstance : Nonempty J)
    exact ⟨i, 0, (Functor.map_isZero (P.pull S.limitToBase) hY).eq_of_tgt _ _⟩
  exists_trans_eq i φ φ' _ :=
    ⟨i, le_refl i, congrArg _ ((Functor.map_isZero (P.pull (S.toBase i)) hY).eq_of_tgt φ φ')⟩

/-- The objects `Y` for which the shifted statement holds against a fixed `X` form a
triangulated subcategory. -/
theorem isTriangulated_shiftedColimSnd (X : D b) :
    (S.shiftedColimSnd P X).IsTriangulated := by
  have := isStableUnderShift_shiftedColimSnd (S := S) hP X
  have := isTriangulatedClosed₃_shiftedColimSnd (S := S) hP X
  exact isTriangulated_of_isTriangulatedClosed₃ _ fun n m => IsColim.of_isZero_snd hP _
    (Functor.map_isZero (shiftFunctor (D b) m) (isZero_zero _))

omit [∀ a, HasZeroObject (D a)] [∀ a, Preadditive (D a)]
  [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] [∀ a, Pretriangulated (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).CommShift ℤ]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).IsTriangulated] [IsDirected J (· ≤ ·)] [Nonempty J] in
/-- The objects `Y` for which the shifted statement holds against a fixed `X` are stable under
retracts. -/
theorem isStableUnderRetracts_shiftedColimSnd (X : D b) :
    (S.shiftedColimSnd P X).IsStableUnderRetracts :=
  ⟨fun r hY n m => (hY n m).of_retract_snd hP _ (r.map (shiftFunctor (D b) m))⟩

variable [∀ a, IsTriangulated (D a)]

omit [∀ a, IsTriangulated (D a)] in
/-- **The shifted statement holds on the triangulated envelope of an object** `G` as soon as it
holds for `G` against itself: both arguments range over thick subcategories containing `G`. -/
theorem isShiftedColim_of_triangEnvelope {G : D b} (hG : S.IsShiftedColim P G G) {X Y : D b}
    (hX : (ObjectProperty.singleton G).triangEnvelope X)
    (hY : (ObjectProperty.singleton G).triangEnvelope Y) : S.IsShiftedColim P X Y := by
  have := isTriangulated_shiftedColimSnd (S := S) hP G
  have := isStableUnderRetracts_shiftedColimSnd (S := S) hP G
  have key (Q : ObjectProperty (D b)) [Q.IsTriangulated] [Q.IsStableUnderRetracts] (hQ : Q G)
      (Z : D b) (hZ : (ObjectProperty.singleton G).triangEnvelope Z) : Q Z :=
    (ObjectProperty.singleton G).triangEnvelope_le_iff.2
      (ObjectProperty.singleton_le_iff.2 hQ) Z hZ
  have := isTriangulated_shiftedColimFst (S := S) hP Y
  have := isStableUnderRetracts_shiftedColimFst (S := S) hP Y
  exact key (S.shiftedColimFst P Y) (key (S.shiftedColimSnd P G) hG Y hY) X hX

end Triangulated

end LimitSystem

end CategoryTheory.PullbackData

end
