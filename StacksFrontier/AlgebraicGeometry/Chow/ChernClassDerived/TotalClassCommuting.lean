module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedIntertwining
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction

/-!
# Total classes commuting with a bivariant class

Let `(S, δ)` be as in Situation 02QL, let `g : X' ⟶ X` be locally of finite type and let
`c ∈ A^q(X' ⟶ X)` be a bivariant class. Let `h : Y ⟶ X` be locally of finite type. A total Chow
cohomology class `x = (x_0, x_1, …)` of `Y` *commutes with `c` along `h`* if

  `c ∩ (x_i ∩ α) = x_i ∩ (c ∩ α)`   in   `A_{k-i-q}(X' ×_X W)`

for every test scheme `m : W ⟶ Y`, every `α ∈ A_k(W)` and every `i`; here `c` caps at the test
scheme `W ⟶ Y ⟶ X`, and `x_i` operates on `X' ×_X W` through its projection to `W`. At
`x = c(E)` the total Chern class of a perfect object this is clause (2) of Stacks 0FAC.

On a test scheme the relation says that the operation of `c` intertwines the operations of `x`
on `W` and on `X' ×_X W` (`Stacks.Chow.GradedCapFamily.Intertwines`). Since the operation of a
total class on a test scheme is a ring homomorphism, the total classes commuting with `c` along
`h` form a subring, which contains the inverse of each of its units `1 + x_1 + x_2 + ⋯`.

## Main definitions

* `Stacks.Chow.TotalChowClass.capAlong` — capping with `c` at the test scheme `W ⟶ Y ⟶ X`.
* `Stacks.Chow.TotalChowClass.CommutesWith` — the relation.

## Main results

* `Stacks.Chow.TotalChowClass.CommutesWith.mul` and the other closure properties.
* `Stacks.Chow.TotalChowClass.CommutesWith.inv` — closure under inverses of units with
  component `1` in degree `0`.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable (C : ChowSituation.{u}) {X X' Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (g : X' ⟶ X) [LocallyOfFiniteType g] {q : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl q)
  (h : Y ⟶ X) [LocallyOfFiniteType h] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (hY : h ≫ sX = sY)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
  [LocallyOfFiniteType sY] in
include hY in
/-- The base change `X' ×_X W` of `g` along `W ⟶ Y ⟶ X`, as a test scheme over `Y` through its
projection to `W`, has the structure morphism of the base change. -/
theorem testStructure_eq {W : Scheme.{u}} (m : W ⟶ Y) :
    pullback.fst g (m ≫ h) ≫ (g ≫ sX) = (pullback.snd g (m ≫ h) ≫ m) ≫ sY := by
  rw [← hY, ← Category.assoc, pullback.condition]
  simp only [Category.assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType h] [LocallyOfFiniteType sY] in
include hY in
/-- The structure morphism of `W` as a test scheme over `Y` through `m` equals its structure
morphism as a test scheme over `X` through `m ≫ h`. -/
theorem comp_structure_eq {W : Scheme.{u}} (m : W ⟶ Y) : m ≫ sY = (m ≫ h) ≫ sX := by
  rw [Category.assoc, hY]

/-- **Capping with `c` at a test scheme over `Y`**: for `m : W ⟶ Y`, the cap operation of `c` at
`W ⟶ Y ⟶ X`, read from the Chow groups of `W` to those of `X' ×_X W`, both as test schemes over
`Y`. -/
def capAlong {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ) :
    chowGroup C (m ≫ sY) k →+ chowGroup C ((pullback.snd g (m ≫ h) ≫ m) ≫ sY) (k - q) :=
  (chowGroupCongr C (testStructure_eq C sX g h sY hY m) (k - q)).toAddMonoidHom.comp
    ((c.cap (m ≫ h) k).comp (chowGroupCongr C (comp_structure_eq C sX h sY hY m) k).toAddMonoidHom)

/-- `capAlong` applied to `α` is the cap of `c` at `m ≫ h`, transported along the equalities of
structure morphisms. -/
theorem capAlong_apply {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ)
    (α : chowGroup C (m ≫ sY) k) :
    capAlong C sX g c h sY hY m k α =
      chowGroupCongr C (testStructure_eq C sX g h sY hY m) (k - q)
        (c.cap (m ≫ h) k (chowGroupCongr C (comp_structure_eq C sX h sY hY m) k α)) :=
  rfl

/-- `capAlong` is the cap operation of `c`, up to the transports of structure morphisms. -/
theorem capAlong_heq {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ)
    (α : chowGroup C (m ≫ sY) k) (α' : chowGroup C ((m ≫ h) ≫ sX) k) (hα : α ≍ α') :
    capAlong C sX g c h sY hY m k α ≍ c.cap (m ≫ h) k α' := by
  rw [capAlong_apply]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  rw [eq_of_heq ((chowGroupCongr_heq C _ k α).trans hα)]

/-- `capAlong` is the cap operation of `c` applied to the transported class. -/
private theorem capAlong_heq_cap {W : Scheme.{u}} (m : W ⟶ Y) [LocallyOfFiniteType m] (k : ℤ)
    (α : chowGroup C (m ≫ sY) k) :
    capAlong C sX g c h sY hY m k α ≍
      c.cap (m ≫ h) k (chowGroupCongr C (comp_structure_eq C sX h sY hY m) k α) :=
  capAlong_heq C sX g c h sY hY m k α _ (chowGroupCongr_heq C _ k α).symm

/-- **A total class commuting with `c` along `h`**: on every test scheme `m : W ⟶ Y` the cap
operation of `c` intertwines the operation of `x` on `W` with its operation on `X' ×_X W`, that
is `c ∩ (x_i ∩ α) = x_i ∩ (c ∩ α)` for every index `i`. -/
def CommutesWith (x : TotalChowClass C sY) : Prop :=
  ∀ ⦃W : Scheme.{u}⦄ (m : W ⟶ Y) [LocallyOfFiniteType m],
    (x.op m).Intertwines q (capAlong C sX g c h sY hY m) (x.op (pullback.snd g (m ≫ h) ≫ m))

namespace CommutesWith

variable {C sX g c h sY hY}

/-- The total class `1` commutes with `c` along `h`. -/
theorem one : (1 : TotalChowClass C sY).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_one, op_one]
  exact GradedCapFamily.Intertwines.one

/-- The total class `0` commutes with `c` along `h`. -/
theorem zero : (0 : TotalChowClass C sY).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_zero, op_zero]
  exact GradedCapFamily.Intertwines.zero

/-- A sum of total classes commuting with `c` along `h` commutes with `c` along `h`. -/
theorem add {x y : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY)
    (hy : y.CommutesWith C sX g c h sY hY) : (x + y).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_add, op_add]
  exact (hx m).add (hy m)

/-- The negative of a total class commuting with `c` along `h` commutes with `c` along `h`. -/
theorem neg {x : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY) :
    (-x).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_neg, op_neg]
  exact (hx m).neg

/-- A difference of total classes commuting with `c` along `h` commutes with `c` along `h`. -/
theorem sub {x y : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY)
    (hy : y.CommutesWith C sX g c h sY hY) : (x - y).CommutesWith C sX g c h sY hY := by
  rw [sub_eq_add_neg]
  exact add hx (neg hy)

/-- A product of total classes commuting with `c` along `h` commutes with `c` along `h`. -/
theorem mul {x y : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY)
    (hy : y.CommutesWith C sX g c h sY hY) : (x * y).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_mul, op_mul]
  exact (hx m).mul (hy m)

/-- An integer multiple of a total class commuting with `c` along `h` commutes with `c` along
`h`. -/
theorem zsmul {x : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY) (n : ℤ) :
    (n • x).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [show (n • x).op m = n • x.op m from map_zsmul (opHom m) n x,
    show (n • x).op (pullback.snd g (m ≫ h) ≫ m) = n • x.op (pullback.snd g (m ≫ h) ≫ m) from
      map_zsmul (opHom _) n x]
  exact (hx m).zsmul n

/-- A finite sum of total classes commuting with `c` along `h` commutes with `c` along `h`. -/
theorem sum {ι : Type*} (s : Finset ι) {x : ι → TotalChowClass C sY}
    (hx : ∀ t ∈ s, (x t).CommutesWith C sX g c h sY hY) :
    (∑ t ∈ s, x t).CommutesWith C sX g c h sY hY := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact zero
  | insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact add (hx t (Finset.mem_insert_self t s))
      (ih fun t' ht' ↦ hx t' (Finset.mem_insert_of_mem ht'))

/-- The product of a list of total classes commuting with `c` along `h` commutes with `c` along
`h`. -/
theorem list_prod {l : List (TotalChowClass C sY)}
    (hl : ∀ x ∈ l, x.CommutesWith C sX g c h sY hY) :
    l.prod.CommutesWith C sX g c h sY hY := by
  induction l with
  | nil => exact one
  | cons x l ih =>
    rw [List.prod_cons]
    exact mul (hl x List.mem_cons_self) (ih fun y hy ↦ hl y (List.mem_cons_of_mem x hy))

/-- A power of a total class commuting with `c` along `h` commutes with `c` along `h`. -/
theorem pow {x : TotalChowClass C sY} (hx : x.CommutesWith C sX g c h sY hY) (n : ℕ) :
    (x ^ n).CommutesWith C sX g c h sY hY := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one
  | succ n ih =>
    rw [pow_succ]
    exact mul ih hx

/-- The operation of the inverse of a unit `1 + x_1 + x_2 + ⋯` is the formal inverse of its
operation. -/
theorem op_inv_eq_gradedRightInv (x : (TotalChowClass C sY)ˣ)
    (hx : (x : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0) {T : Scheme.{u}}
    (t : T ⟶ Y) [LocallyOfFiniteType t] :
    (↑x⁻¹ : TotalChowClass C sY).op t = gradedRightInv ((x : TotalChowClass C sY).op t) := by
  have h0 : ∀ k, (x : TotalChowClass C sY).op t k 0 = (1 : GradedCapFamily _) k 0 := by
    intro k
    rw [← op_one t]
    refine AddMonoidHom.ext fun α ↦ ?_
    rw [op_apply, op_apply, hx]
  exact left_inv_eq_right_inv (by rw [← op_mul, Units.inv_mul, op_one]) (mul_gradedRightInv h0)

/-- **Inverses.** The inverse of a unit `1 + x_1 + x_2 + ⋯` commuting with `c` commutes with
`c`. -/
theorem inv (x : (TotalChowClass C sY)ˣ)
    (hx0 : (x : TotalChowClass C sY) 0 = (1 : TotalChowClass C sY) 0)
    (hx : (x : TotalChowClass C sY).CommutesWith C sX g c h sY hY) :
    (↑x⁻¹ : TotalChowClass C sY).CommutesWith C sX g c h sY hY := by
  intro W m _
  rw [op_inv_eq_gradedRightInv x hx0, op_inv_eq_gradedRightInv x hx0]
  exact (hx m).gradedRightInv

end CommutesWith

/-! ### Restriction -/

section Restriction

variable {C sX g h sY}

/-- The cap operation of `c` at two equal test morphisms. -/
theorem cap_heq_of_eq {W : Scheme.{u}} {t t' : W ⟶ X} [LocallyOfFiniteType t]
    [LocallyOfFiniteType t'] (e : t = t') (k : ℤ) {α : chowGroup C (t ≫ sX) k}
    {α' : chowGroup C (t' ≫ sX) k} (hα : α ≍ α') : c.cap t k α ≍ c.cap t' k α' := by
  subst e
  cases hα
  rfl

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] in
/-- The operation of a total class on the base changes `X' ×_X W` along two equal test morphisms
`t = t' : W ⟶ X`, read over `Y` through the same morphism `W ⟶ Y`. -/
theorem op_snd_heq_of_eq (x : TotalChowClass C sY) {W : Scheme.{u}} {t t' : W ⟶ X}
    (e : t = t') (m : W ⟶ Y) [LocallyOfFiniteType (pullback.snd g t ≫ m)]
    [LocallyOfFiniteType (pullback.snd g t' ≫ m)] (k : ℤ) (i : ℕ)
    {β : chowGroup C ((pullback.snd g t ≫ m) ≫ sY) k}
    {β' : chowGroup C ((pullback.snd g t' ≫ m) ≫ sY) k} (hβ : β ≍ β') :
    x.op (pullback.snd g t ≫ m) k i β ≍ x.op (pullback.snd g t' ≫ m) k i β' := by
  subst e
  cases hβ
  rfl

/-- The operation of a total class at two equal test morphisms. -/
theorem op_heq_of_eq (x : TotalChowClass C sY) {W : Scheme.{u}}
    {n n' : W ⟶ Y} [LocallyOfFiniteType n] [LocallyOfFiniteType n'] (e : n = n') (k : ℤ)
    (i : ℕ) {β : chowGroup C (n ≫ sY) k} {β' : chowGroup C (n' ≫ sY) k} (hβ : β ≍ β') :
    x.op n k i β ≍ x.op n' k i β' := by
  subst e
  cases hβ
  rfl

/-- **Commuting at the test schemes factoring through `u`.** If the restriction of `x` along
`u : Y₁ ⟶ Y` commutes with `c` along `u ≫ h`, then the operation of `c` intertwines the
operations of `x` at every test scheme `m : W ⟶ Y` factoring through `u`. -/
theorem intertwines_of_res {Y₁ : Scheme.{u}} (u : Y₁ ⟶ Y) [LocallyOfFiniteType u]
    (sY₁ : Y₁ ⟶ C.S) [LocallyOfFiniteType sY₁] (hu : u ≫ sY = sY₁) (x : TotalChowClass C sY)
    (hx : (res u hu x).CommutesWith C sX g c (u ≫ h) sY₁ (by rw [Category.assoc, hY, hu]))
    {W : Scheme.{u}} (a : W ⟶ Y₁) [LocallyOfFiniteType a] (m : W ⟶ Y) [LocallyOfFiniteType m]
    (hm : a ≫ u = m) :
    (x.op m).Intertwines q (capAlong C sX g c h sY hY m) (x.op (pullback.snd g (m ≫ h) ≫ m)) := by
  subst hm
  have e : (a ≫ u) ≫ h = a ≫ (u ≫ h) := Category.assoc a u h
  have hY₁ : (u ≫ h) ≫ sX = sY₁ := by rw [Category.assoc, hY, hu]
  refine GradedCapFamily.Intertwines.iff_heq.2 fun k i α ↦ ?_
  have hau : (a ≫ u) ≫ sY = a ≫ sY₁ := by rw [Category.assoc, hu]
  have hα : chowGroupCongr C hau k α ≍ α := chowGroupCongr_heq C _ k α
  have hres := TotalChowClass.op_res_apply u hu x a k i (chowGroupCongr C hau k α) α hα
  have s1 := capAlong_heq_cap C sX g c h sY hY (a ≫ u) (k - i) (x.op (a ≫ u) k i α)
  have s2 := cap_heq_of_eq c e (k - i)
    (((chowGroupCongr_heq C (comp_structure_eq C sX h sY hY (a ≫ u)) (k - i) _).trans
      hres.symm).trans (chowGroupCongr_heq C (comp_structure_eq C sX (u ≫ h) sY₁ hY₁ a) (k - i)
      ((res u hu x).op a k i (chowGroupCongr C hau k α))).symm)
  have s3 := capAlong_heq_cap C sX g c (u ≫ h) sY₁ hY₁ a (k - i)
    ((res u hu x).op a k i (chowGroupCongr C hau k α))
  have s4 := (hx a).heq k i (chowGroupCongr C hau k α)
  have hn : (pullback.snd g (a ≫ u ≫ h) ≫ a) ≫ sY₁ =
      ((pullback.snd g (a ≫ u ≫ h) ≫ a) ≫ u) ≫ sY := by
    rw [← hu]
    simp only [Category.assoc]
  have s5 := TotalChowClass.op_res_apply u hu x (pullback.snd g (a ≫ u ≫ h) ≫ a) (k - q) i
    (capAlong C sX g c (u ≫ h) sY₁ hY₁ a k (chowGroupCongr C hau k α))
    (chowGroupCongr C hn (k - q)
      (capAlong C sX g c (u ≫ h) sY₁ hY₁ a k (chowGroupCongr C hau k α)))
    (chowGroupCongr_heq C hn (k - q) _).symm
  have hn' : (pullback.snd g (a ≫ u ≫ h) ≫ a) ≫ sY₁ =
      (pullback.snd g (a ≫ u ≫ h) ≫ a ≫ u) ≫ sY := by
    rw [← hu]
    simp only [Category.assoc]
  have s6 := op_heq_of_eq x (Category.assoc (pullback.snd g (a ≫ u ≫ h)) a u) (k - q) i
    (β := chowGroupCongr C hn (k - q)
      (capAlong C sX g c (u ≫ h) sY₁ hY₁ a k (chowGroupCongr C hau k α)))
    (β' := chowGroupCongr C hn' (k - q)
      (capAlong C sX g c (u ≫ h) sY₁ hY₁ a k (chowGroupCongr C hau k α)))
    ((chowGroupCongr_heq C hn (k - q) _).trans (chowGroupCongr_heq C hn' (k - q) _).symm)
  have hβ : capAlong C sX g c h sY hY (a ≫ u) k α ≍
      chowGroupCongr C hn' (k - q)
        (capAlong C sX g c (u ≫ h) sY₁ hY₁ a k (chowGroupCongr C hau k α)) := by
    refine (capAlong_heq_cap C sX g c h sY hY (a ≫ u) k α).trans ?_
    refine (cap_heq_of_eq c e k ?_).trans
      ((capAlong_heq_cap C sX g c (u ≫ h) sY₁ hY₁ a k _).symm.trans
        (chowGroupCongr_heq C hn' (k - q) _).symm)
    exact (chowGroupCongr_heq C _ k α).trans (hα.symm.trans (chowGroupCongr_heq C _ k _).symm)
  have s7 := op_snd_heq_of_eq x e (a ≫ u) (k - q) i hβ
  exact s1.trans (s2.trans (s3.symm.trans (s4.trans (s5.trans (s6.trans s7.symm)))))

end Restriction

end TotalChowClass

end Stacks.Chow

end
