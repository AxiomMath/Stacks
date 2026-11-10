module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.ChernCapSquareZero
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.Hinge

/-!
# A product of `n` shift operators is an `n`-fold iterated cap product

`StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.Hinge` performs its computation in the
ring `AddMonoid.End` of the graded product `Stacks.Chow.ChowGradedProduct` of the Chow groups, so
the objects it manipulates are products of `Stacks.Chow.firstChernShift` operators read off in a
chosen degree by `Stacks.Chow.evalChowGraded`. The vanishing theorems of Stacks 0FDX, on the
other hand, are stated over `Stacks.Chow.iteratedChernCapOnChow`, the cap product of a *list* of
`Stacks.Chow.ChernCapOperator`. Nothing related the two encodings at arity larger than two: the
file `StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.ChernCapSquareZero` did exactly the
`n = 2` case, in order to produce the hinge's hypothesis `hsq`.

This file is the `n`-fold identification, and then the consequence the hinge needs: its
hypothesis `hzero`.

## The identification

For a family `ℒ_0, …, ℒ_{r-1}` of invertible modules and a Chow class `α` of degree `deg`,

  `evalChowGraded α r (c₁(ℒ_0) ⋯ c₁(ℒ_{r-1})) = c₁(ℒ_0) ∩ ⋯ ∩ c₁(ℒ_{r-1}) ∩ α`

with the left side a product of shift operators evaluated in degree `r` and the right side the
iterated cap product of the list of operators `Stacks.Chow.invCap ℒ_i`, read as a map
`A_{deg}(X) ⟶ A_{deg-r}(X)`. The head of the list is applied last on both sides — the identity
`Stacks.Chow.evalChowGraded_firstChernShift_mul` peels the leftmost factor of the product and the
recursion `Stacks.Chow.iteratedChernCapOnChow_cons_eq` peels the head of the list — so the
induction is over the list structure, with `List.ofFn_succ` matching the two peelings up.

## The degree transport

`chowGroup C p i` for varying `i` are different types, so the two sides do not even have the same
type until a degree is transported: the left side consumes `α` in degree `deg` and the right side
consumes a class in degree `(deg - r) + r`, the same integer written differently. Every statement
below therefore takes the class in the degree its right-hand side iterates from, together with a
heterogeneous equality `α ≍ β`, which is the convention of
`Stacks.Chow.iteratedChernCapOnChow_cons_eq` and of `Stacks.Chow.iteratedChernCapOnChow_append`.

Under the induction this costs exactly one transport per step, which is the point of taking the
class heterogeneously rather than inserting `Stacks.Chow.chowGroupCast` into the statement: the
inductive hypothesis is at the *same* `deg` and the *same* `α`, with only the family shifted, so
the transports do not accumulate.

## Main results

* `Stacks.Chow.evalChowGraded_prod_ofFn_firstChernShift_eq_iteratedChernCapOnChow` — **the
  bridge**, at an arbitrary finite family.
* `Stacks.Chow.evalChowGraded_firstChernShift_pow_eq_iteratedChernCapOnChow` — the bridge at a
  constant family, where the product of shifts is a power.
* `Stacks.Chow.evalChowGraded_prod_ofFn_firstChernShift_eq_zero_of_topologicalKrullDim_le` —
  Stacks 0FDX read through the bridge: a product of `d + 1` shift operators of pullbacks from a
  base of dimension at most `d` annihilates every class of every test scheme.
* `Stacks.Chow.evalChowGraded_firstChernShift_pow_eq_zero_of_topologicalKrullDim_le` — **the
  hypothesis `hzero` of the hinge**, at every exponent `n ≥ d + 1`.
* `Stacks.Chow.isOfFinAddOrder_evalChowGraded_listProd_of_topologicalKrullDim_le` — the hinge
  with `hzero` discharged.

## Implementation notes

### Why `n ≥ d + 1` and not `n = d + 1`

In the source the class `β_n`, the `n`-th power of `c₁(𝒩)` capped with the fundamental class of
`Sⁿ(X)`, is killed because `𝒩` is pulled back from a scheme of dimension `g` with `n > g`, not
because `n = g + 1`. The extra factors are harmless:
the head of a list of cap operators acts last, so the first `n - (d+1)` factors are applied to a
class that the last `d + 1` have already killed. That is
`Stacks.Chow.iteratedChernCapOnChow_append` together with `map_zero`.

### No Stacks registration

Everything here is the content of
`Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le`, which carries the
Stacks 0FDX registration, read through the repository's other encoding of a product of first
Chern class cap operations. No clause of Stacks 0FDX is covered that is not already covered
there, so no tag is placed, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.ChernCapSquareZero`.

### What remains open for the Voevodsky nilpotence statement

The two hypotheses of the hinge that this file does not touch are `hM`, which for
`𝒩' ≅ (ℒ_1 ⊗ ⋯ ⊗ ℒ_n)^{⊗ m}` is Stacks 02SP and available as
`Stacks.Chow.firstChernShift_eq_add_of_iso_tensorObj`, and `hcomm`, which is Stacks 02TJ carried
in the repository's own form. Beyond the hinge, the geometric inputs of the source — the
symmetric power `Sⁿ(X)` as a scheme, the norm-group identification `π^*𝒩 ≅ (ℒ_1 ⊗ ⋯ ⊗ ℒ_n)^{⊗
(n-1)!}`, the Picard scheme `Pic^n_{X/k}` with `dim Pic^n = g`, and the projective space bundle
clause that writes `𝒩 = f^*ℳ` — are all still open, and the finiteness of `π` with it.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-! ### The bridge -/

/-- An iterated cap product at equal lists of operators, the class transported along the
equality of degrees. -/
private theorem iteratedChernCapOnChow_eq_cast_of_eq {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {Os Os' : List (ChernCapOperator C p)} (hO : Os = Os') (d : ℤ)
    (e : d + (Os.length : ℤ) = d + (Os'.length : ℤ)) (x : chowGroup C p (d + (Os.length : ℤ))) :
    iteratedChernCapOnChow C p Os d x = iteratedChernCapOnChow C p Os' d (chowGroupCast C p e x) :=
  chowGroup_eq_of_heq C p
    (iteratedChernCapOnChow_heq_of_eq C p hO _ (chowGroupCast_heq C p e x).symm)

/-- **A product of `r` shift operators, read in degree `r`, is the `r`-fold iterated cap
product.** For invertible modules `ℒ_0, …, ℒ_{r-1}` whose first Chern class cap products descend
to Chow groups,

  `evalChowGraded α r (c₁(ℒ_0) ⋯ c₁(ℒ_{r-1})) = c₁(ℒ_0) ∩ ⋯ ∩ c₁(ℒ_{r-1}) ∩ α`,

the left side a product in `AddMonoid.End` of `Stacks.Chow.ChowGradedProduct` evaluated on the
graded unit of `α`, the right side `Stacks.Chow.iteratedChernCapOnChow` at the list of operators
`Stacks.Chow.invCap ℒ_i`.

The class `β` is `α` read in the degree the iterated cap product iterates from, namely
`(deg - r) + r`; that is what `hαβ` carries.

This is the `Fin r` generalisation of `Stacks.Chow.iteratedChernCapOnChow_pair_eq` together with
the step pattern of `Stacks.Chow.firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one`.
The induction peels the leftmost factor of the product with
`Stacks.Chow.evalChowGraded_firstChernShift_mul` and the head of the list with
`Stacks.Chow.iteratedChernCapOnChow_cons_eq`, which `List.ofFn_succ` matches up, and identifies
the two one-step operations with `Stacks.Chow.firstChernCapStep_eq_invCap_capOnChow`. -/
theorem evalChowGraded_prod_ofFn_firstChernShift_eq_iteratedChernCapOnChow {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (deg : ℤ) (α : chowGroup C p deg) {r : ℕ}
    (L : Fin r → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    (hfac : ∀ i, InvertibleChernCapDescends C p (L i))
    (β : chowGroup C p (deg - (r : ℤ) + ((List.ofFn fun i => invCap C p (L i)).length : ℤ)))
    (hαβ : α ≍ β) :
    evalChowGraded C p deg α r
        (List.ofFn fun i => firstChernShift C p deg (L i) (hfac i)).prod =
      iteratedChernCapOnChow C p (List.ofFn fun i => invCap C p (L i)) (deg - (r : ℤ)) β := by
  induction r with
  | zero =>
    have hlhs : evalChowGraded C p deg α 0
        (List.ofFn fun i => firstChernShift C p deg (L i) (hfac i)).prod ≍ α := by
      change (List.ofFn fun i => firstChernShift C p deg (L i) (hfac i)).prod
          (chowGradedUnit C p deg α) 0 ≍ α
      rw [List.ofFn_zero, List.prod_nil]
      change chowGradedUnit C p deg α 0 ≍ α
      change chowGroupDegreeCast C p _ (AddMonoidHom.id _) α ≍ α
      rw [chowGroupDegreeCast_apply]
      exact chowGroupCast_heq C p _ α
    have hrhs : iteratedChernCapOnChow C p (List.ofFn fun i => invCap C p (L i))
        (deg - ((0 : ℕ) : ℤ)) β ≍ β := by
      rw [iteratedChernCapOnChow_eq_cast_of_eq C p List.ofFn_zero _ (by simp) β]
      exact (iteratedChernCapOnChow_nil_heq C p _ _).trans (chowGroupCast_heq C p (by simp) β)
    exact chowGroup_eq_of_heq C p (hlhs.trans (hαβ.trans hrhs.symm))
  | succ r ih =>
    have hcons : (List.ofFn fun i : Fin (r + 1) => invCap C p (L i)) =
        invCap C p (L 0) :: List.ofFn fun i : Fin r => invCap C p (L i.succ) := List.ofFn_succ
    have e1 : deg - ((r + 1 : ℕ) : ℤ) +
          ((List.ofFn fun i : Fin (r + 1) => invCap C p (L i)).length : ℤ) =
        deg - ((r + 1 : ℕ) : ℤ) +
          ((invCap C p (L 0) ::
            List.ofFn fun i : Fin r => invCap C p (L i.succ)).length : ℤ) := by
      simp
    have e2 : deg - ((r + 1 : ℕ) : ℤ) +
          ((invCap C p (L 0) ::
            List.ofFn fun i : Fin r => invCap C p (L i.succ)).length : ℤ) =
        deg - ((r + 1 : ℕ) : ℤ) + 1 +
          ((List.ofFn fun i : Fin r => invCap C p (L i.succ)).length : ℤ) := by
      simp; ring
    have hL : ∀ (y : chowGroup C p (deg - ((r + 1 : ℕ) : ℤ) + 1 +
          ((List.ofFn fun i : Fin r => invCap C p (L i.succ)).length : ℤ))), α ≍ y →
        evalChowGraded C p deg α (r + 1)
            (List.ofFn fun i : Fin (r + 1) => firstChernShift C p deg (L i) (hfac i)).prod =
          (invCap C p (L 0)).capOnChow C p (deg - ((r + 1 : ℕ) : ℤ))
            (iteratedChernCapOnChow C p (List.ofFn fun i : Fin r => invCap C p (L i.succ))
              (deg - ((r + 1 : ℕ) : ℤ) + 1) y) := by
      intro y hy
      rw [List.ofFn_succ, List.prod_cons, evalChowGraded_firstChernShift_mul]
      have hd : deg - (r : ℤ) = deg - ((r + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      have hlen : deg = deg - (r : ℤ) +
          ((List.ofFn fun i : Fin r => invCap C p (L i.succ)).length : ℤ) := by simp
      refine firstChernCapStep_eq_invCap_capOnChow C p deg (L 0) (hfac 0) r _
        (iteratedChernCapOnChow C p (List.ofFn fun i : Fin r => invCap C p (L i.succ))
          (deg - ((r + 1 : ℕ) : ℤ) + 1) y) ?_
      rw [ih (fun i : Fin r => L i.succ) (fun i => hfac i.succ) (chowGroupCast C p hlen α)
        (chowGroupCast_heq C p hlen α).symm]
      exact iteratedChernCapOnChow_heq C p _ hd ((chowGroupCast_heq C p hlen α).trans hy)
    have h1 : iteratedChernCapOnChow C p (List.ofFn fun i : Fin (r + 1) => invCap C p (L i))
          (deg - ((r + 1 : ℕ) : ℤ)) β =
        iteratedChernCapOnChow C p
            (invCap C p (L 0) :: List.ofFn fun i : Fin r => invCap C p (L i.succ))
            (deg - ((r + 1 : ℕ) : ℤ)) (chowGroupCast C p e1 β) :=
      iteratedChernCapOnChow_eq_cast_of_eq C p hcons _ e1 β
    have h2 := iteratedChernCapOnChow_cons_eq C p (invCap C p (L 0))
      (List.ofFn fun i : Fin r => invCap C p (L i.succ)) (deg - ((r + 1 : ℕ) : ℤ))
      (chowGroupCast C p e1 β) (chowGroupCast C p e2 (chowGroupCast C p e1 β))
      (chowGroupCast_heq C p e2 (chowGroupCast C p e1 β)).symm
    exact (hL (chowGroupCast C p e2 (chowGroupCast C p e1 β))
      (hαβ.trans ((chowGroupCast_heq C p e2 (chowGroupCast C p e1 β)).trans
        (chowGroupCast_heq C p e1 β)).symm)).trans (h1.trans h2).symm

/-- **The bridge at a constant family**: the `n`-th power of one shift operator, read in degree
`n`, is the `n`-fold cap product of that operator. A product over a constant family is a power
(`List.ofFn_const` and `List.prod_replicate`), so this is the previous theorem at
`ℒ_i = ℒ`. -/
theorem evalChowGraded_firstChernShift_pow_eq_iteratedChernCapOnChow {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (deg : ℤ) (α : chowGroup C p deg) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hfacM : InvertibleChernCapDescends C p M) (n : ℕ)
    (β : chowGroup C p
      (deg - (n : ℤ) + ((List.ofFn fun _ : Fin n => invCap C p M).length : ℤ)))
    (hαβ : α ≍ β) :
    evalChowGraded C p deg α n (firstChernShift C p deg M hfacM ^ n) =
      iteratedChernCapOnChow C p (List.ofFn fun _ : Fin n => invCap C p M) (deg - (n : ℤ)) β := by
  have hprod : (List.ofFn fun _ : Fin n => firstChernShift C p deg M hfacM).prod =
      firstChernShift C p deg M hfacM ^ n := by
    rw [List.ofFn_const, List.prod_replicate]
  rw [← hprod]
  exact evalChowGraded_prod_ofFn_firstChernShift_eq_iteratedChernCapOnChow C p deg α
    (fun _ : Fin n => M) (fun _ => hfacM) β hαβ

/-! ### Stacks 0FDX in the shift-operator encoding -/

/-- **Stacks 0FDX, read on products of shift operators.** Let `X` be locally of finite type over
the base of chapter 42, Noetherian, carrying an ample invertible module and of topological
dimension at most `d`. For invertible `𝒪_X`-modules `ℒ_0, …, ℒ_d` and every test scheme
`u : T ⟶ X` locally of finite type, the product of the `d + 1` shift operators of the `u^*ℒ_i`,
read in degree `d + 1`, annihilates every Chow class of `T`. No bound is placed on the dimension
of `T`.

This is `Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le` through the
bridge. -/
theorem evalChowGraded_prod_ofFn_firstChernShift_eq_zero_of_topologicalKrullDim_le (d : ℕ)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (N : Fin (d + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hq : u ≫ sX = q) (deg : ℤ) (α : chowGroup C q deg)
    (hfac : ∀ i, InvertibleChernCapDescends C q ((Scheme.Modules.pullback u).obj (N i))) :
    evalChowGraded C q deg α (d + 1)
        (List.ofFn fun i => firstChernShift C q deg
          ((Scheme.Modules.pullback u).obj (N i)) (hfac i)).prod = 0 := by
  have hlen : deg = deg - ((d + 1 : ℕ) : ℤ) +
      ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) := by
    simp
  refine Eq.trans (evalChowGraded_prod_ofFn_firstChernShift_eq_iteratedChernCapOnChow C q deg α
    (fun i => (Scheme.Modules.pullback u).obj (N i)) hfac (chowGroupCast C q hlen α)
    (chowGroupCast_heq C q hlen α).symm) ?_
  exact iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le C d sX A hA hdim N u q hq _ _

/-- **The hypothesis `hzero` of the Voevodsky nilpotence hinge.** For `ℳ` invertible on a
Noetherian `X` of topological dimension at most `d` carrying an ample invertible module, for
every test scheme `u : T ⟶ X` locally of finite type and every `n ≥ d + 1`,

  `c₁(u^*ℳ)^n ∩ α = 0`   for every Chow class `α` of `T`,

read as the `n`-th power of the shift operator of `u^*ℳ` evaluated in degree `n`. No bound is
placed on the dimension of `T`.

This is the shape `hzero` of `Stacks.Chow.isOfFinAddOrder_evalChowGraded_listProd` consumes. In
Stacks 0FH9 it is step 7 transported along `π : Xⁿ ⟶ Sⁿ(X)`: the projective space bundle formula
writes `𝒩 = f^*ℳ` with `ℳ` on `Pic^n_{X/k}`, and `n > g = dim Pic^n_{X/k}`, so `d = g` and the
exponent exceeds `d` strictly rather than by exactly one — which is why the statement is at every
`n ≥ d + 1` and not only at `n = d + 1`. The extra `n - (d + 1)` factors act on a class the last
`d + 1` have already killed. -/
theorem evalChowGraded_firstChernShift_pow_eq_zero_of_topologicalKrullDim_le (d : ℕ)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hq : u ≫ sX = q) (deg : ℤ) (α : chowGroup C q deg) (n : ℕ) (hn : d + 1 ≤ n)
    (hfac : InvertibleChernCapDescends C q ((Scheme.Modules.pullback u).obj M)) :
    evalChowGraded C q deg α n
      (firstChernShift C q deg ((Scheme.Modules.pullback u).obj M) hfac ^ n) = 0 := by
  have hsplit : (List.ofFn fun _ : Fin n => invCap C q ((Scheme.Modules.pullback u).obj M)) =
      List.replicate (n - (d + 1)) (invCap C q ((Scheme.Modules.pullback u).obj M)) ++
        (List.ofFn fun _ : Fin (d + 1) =>
          invCap C q ((Scheme.Modules.pullback u).obj M)) := by
    rw [List.ofFn_const, List.ofFn_const, ← List.replicate_add, Nat.sub_add_cancel hn]
  have hlen : deg = deg - (n : ℤ) +
      ((List.ofFn fun _ : Fin n =>
        invCap C q ((Scheme.Modules.pullback u).obj M)).length : ℤ) := by simp
  have e3 : deg - (n : ℤ) +
        ((List.ofFn fun _ : Fin n =>
          invCap C q ((Scheme.Modules.pullback u).obj M)).length : ℤ) =
      deg - (n : ℤ) +
        ((List.replicate (n - (d + 1)) (invCap C q ((Scheme.Modules.pullback u).obj M)) ++
          (List.ofFn fun _ : Fin (d + 1) =>
            invCap C q ((Scheme.Modules.pullback u).obj M))).length : ℤ) := by
    simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  have e4 : deg - (n : ℤ) +
        ((List.replicate (n - (d + 1)) (invCap C q ((Scheme.Modules.pullback u).obj M)) ++
          (List.ofFn fun _ : Fin (d + 1) =>
            invCap C q ((Scheme.Modules.pullback u).obj M))).length : ℤ) =
      deg - (n : ℤ) +
        ((List.replicate (n - (d + 1))
          (invCap C q ((Scheme.Modules.pullback u).obj M))).length : ℤ) +
        ((List.ofFn fun _ : Fin (d + 1) =>
          invCap C q ((Scheme.Modules.pullback u).obj M)).length : ℤ) := by
    simp only [List.length_append, Nat.cast_add]
    ring
  rw [evalChowGraded_firstChernShift_pow_eq_iteratedChernCapOnChow C q deg α
    ((Scheme.Modules.pullback u).obj M) hfac n (chowGroupCast C q hlen α)
    (chowGroupCast_heq C q hlen α).symm]
  rw [show iteratedChernCapOnChow C q
        (List.ofFn fun _ : Fin n => invCap C q ((Scheme.Modules.pullback u).obj M))
        (deg - (n : ℤ)) (chowGroupCast C q hlen α) =
      iteratedChernCapOnChow C q
        (List.replicate (n - (d + 1)) (invCap C q ((Scheme.Modules.pullback u).obj M)) ++
          (List.ofFn fun _ : Fin (d + 1) =>
            invCap C q ((Scheme.Modules.pullback u).obj M)))
        (deg - (n : ℤ)) (chowGroupCast C q e3 (chowGroupCast C q hlen α)) from
    iteratedChernCapOnChow_eq_cast_of_eq C q hsplit _ e3 _]
  rw [iteratedChernCapOnChow_append C q _ _ (deg - (n : ℤ))
    (chowGroupCast C q e3 (chowGroupCast C q hlen α))
    (chowGroupCast C q e4 (chowGroupCast C q e3 (chowGroupCast C q hlen α)))
    (chowGroupCast_heq C q e4 _).symm]
  rw [iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le C d sX A hA hdim
    (fun _ : Fin (d + 1) => M) u q hq _ _, map_zero]

/-! ### The hinge with `hzero` discharged -/

/-- **The step of Stacks 0FH9 that makes the zero cycle torsion, with `hzero` supplied.** This is
`Stacks.Chow.isOfFinAddOrder_evalChowGraded_listProd` of the hinge, with its hypothesis `hzero`
replaced by the geometric input that produces it: the module `𝒩'` playing `π^*𝒩` is the pullback
along `v : T ⟶ Y` of an invertible module `ℳ` on a Noetherian `Y` of topological dimension at
most `d` carrying an ample invertible module, and the number `n` of factors exceeds `d`.

The remaining hypotheses are those of the hinge, unchanged: `hM` (Stacks 02SP, that the shift of
`𝒩'` is `m` times the sum of the shifts of the `ℒ_i`), `hsq` (Stacks 0FDX for each `ℒ_i`, which
for `ℒ_i` pulled back from a curve is
`Stacks.Chow.firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one`) and `hcomm`
(Stacks 02TJ for each pair). -/
theorem isOfFinAddOrder_evalChowGraded_listProd_of_topologicalKrullDim_le (d : ℕ)
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsNoetherian Y] (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] (hA : Stacks.Ample.IsAmple Y A)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (Mod : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property Mod]
    {T : Scheme.{u}} (v : T ⟶ Y) [LocallyOfFiniteType v] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hv : v ≫ sY = q) (deg : ℤ) (α : chowGroup C q deg) {n : ℕ} (hn : d + 1 ≤ n)
    (L : Fin n → T.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property (L i)]
    (hfac : ∀ i, InvertibleChernCapDescends C q (L i))
    (hfacM : InvertibleChernCapDescends C q ((Scheme.Modules.pullback v).obj Mod)) (m : ℕ)
    (hm : m ≠ 0)
    (hM : firstChernShift C q deg ((Scheme.Modules.pullback v).obj Mod) hfacM =
      m • ∑ i, firstChernShift C q deg (L i) (hfac i))
    (hsq : ∀ i, firstChernShift C q deg (L i) (hfac i) *
      firstChernShift C q deg (L i) (hfac i) = 0)
    (hcomm : ∀ i j, FirstChernCapStepsCommute C q deg (L i) (L j) (hfac i) (hfac j)) :
    IsOfFinAddOrder (evalChowGraded C q deg α n
      (List.ofFn fun i ↦ firstChernShift C q deg (L i) (hfac i)).prod) :=
  isOfFinAddOrder_evalChowGraded_listProd C q deg L hfac
    ((Scheme.Modules.pullback v).obj Mod) hfacM α m hm hM hsq hcomm
    (evalChowGraded_firstChernShift_pow_eq_zero_of_topologicalKrullDim_le C d sY A hA hdim Mod v q
      hv deg α n hn hfacM)

end Stacks.Chow

end
