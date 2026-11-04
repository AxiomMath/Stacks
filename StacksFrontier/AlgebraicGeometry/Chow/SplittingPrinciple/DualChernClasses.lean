module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of the dual of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ` be a finite locally free `𝒪_X`-module with dual `ℰ^∨`.
[Stacks, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5) is the sign rule

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`.

This file proves it **componentwise, as an identity between cap products on Chow groups**, in the
vocabulary of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity`: for every
`n`, every `n`-cycle `α` and every `i`,

  `c_i(ℰ^∨) ∩ α = (-1)^i • (c_i(ℰ) ∩ α)`  in  `A_{n-i}(X)`.

The cap product is `Stacks.Chow.chernClassCapExt`, the one Stacks 02UH and Stacks 02UJ are stated
with; there is no bivariant ring `A^*(X)` and therefore no total Chern class, so the statement is
made degree by degree against a fixed cycle.

## The proof, and where it starts

The source argues in two steps. First it chooses `π : P ⟶ X` as in Stacks 02UL, uses injectivity
of `π^*` to reduce to the case where `ℰ` carries a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,  `ℰ_i/ℰ_{i-1} ≅ ℒ_i`

with the `ℒ_i` invertible, and dualizes that filtration to one of `ℰ^∨` with successive quotients
`ℒ_i^{⊗ -1}`. Second, with `x_i = c₁(ℒ_i)` it reads Stacks 02UJ on both filtrations, uses Stacks
02SP to rewrite `c₁(ℒ_i^{⊗ -1}) = -x_i`, and finishes by "a formal computation which we omit".

**The second step is what is proved below, in every degree**; the first is a hypothesis, for the
reasons recorded in the `@[stacks 0FA5]` clause. The hypothesis is exactly the sentence "Thus we
may assume there exist invertible `𝒪_X`-modules `ℒ_i` and a filtration …" of the source proof.

## The dual, and why it appears as a tensor inverse

The dual filtration enters the source proof only through the isomorphisms
`ℰ_{i-1}^⊥/ℰ_i^⊥ ≅ ℒ_i^{⊗ -1}`, so what the computation needs of `ℰ^∨` is a filtration whose
successive quotients are **tensor inverses** of the `ℒ_i`; that is the hypothesis `hdual` below,
`ℒ_i ⊗_{𝒪_X} ℳ_i ≅ 𝒪_X`. This is not a weakening. By Stacks 0B8K a tensor inverse of an
invertible module exists and is unique up to isomorphism, it is the dual
(`Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf`, Stacks 01CT and 040A), and the first
Chern class cap product depends only on the isomorphism class of the module by
`Stacks.Chow.firstChernClassCapOfInvertible_congr`. Phrasing the quotients as tensor inverses
rather than as `Stacks.SheafOfModules.dualSheaf` keeps the statement inside the spelling
`AlgebraicGeometry.Scheme.Modules.tensorObj` of Stacks 02SP.

## The two pieces of content

* **The line-bundle case.** `Stacks.Chow.firstChernCapStep_eq_neg_of_tensorObj_iso_unit` is
  `c₁(ℒ^{⊗ -1}) ∩ - = -(c₁(ℒ) ∩ -)` as an identity of operations on Chow groups. It follows from
  the two clauses of Stacks 02SP, additivity `c₁(ℒ) ∩ α + c₁(ℳ) ∩ α = c₁(ℒ ⊗ ℳ) ∩ α` and the
  vanishing `c₁(𝒪_X) ∩ α = 0`, which together give `c₁(ℒ) ∩ α + c₁(ℒ^{⊗ -1}) ∩ α = 0`.

  This also identifies `Stacks.Chow.inverseFirstChernCapStep`, *defined* as the negative of
  `Stacks.Chow.firstChernCapStep`, with the operation `c₁(ℳ) ∩ -` it is named after, whenever a
  tensor inverse `ℳ` is exhibited.

* **The formal computation the source omits.**
  `Stacks.Chow.elemSymmChernCap_eq_zsmul_of_neg_steps` is
  `e_k(-x_1, …, -x_r) = (-1)^k e_k(x_1, …, x_r)` for the elementary symmetric functions of
  `Stacks.Chow.elemSymmChernCap`, proved by induction on the number of operations along the
  Pascal recursion those functions are defined by, simultaneously in every degree `k` and for
  every length `r`.

## Main results

* `Stacks.Chow.firstChernCapStep_eq_neg_of_tensorObj_iso_unit` — `c₁` of a tensor inverse is the
  negative of `c₁`, as operations on Chow groups.
* `Stacks.Chow.elemSymmChernCap_eq_zsmul_of_neg_steps` — negating the first Chern class
  operations multiplies the `k`-th elementary symmetric function by `(-1)^k`.
* `Stacks.Chow.chernClassCapExt_eq_zsmul_of_dualFiltration` — **Stacks 0FA5**, componentwise.

## References

* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Transport of a negation along an equality of degrees -/

/-- The transport of `Stacks.Chow.chowGroupDegreeCast` along an equality of degrees commutes with
negation. -/
theorem chowGroupDegreeCast_neg (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {k l m : ℤ} (h : k = l)
    (F : chowGroup C p l →+ chowGroup C p m) :
    chowGroupDegreeCast C p h (-F) = -chowGroupDegreeCast C p h F := by
  subst h
  rfl

/-! ### The first Chern class of a tensor inverse

This is the line-bundle case of Stacks 0FA5. -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **The first Chern class cap product of a tensor inverse is the negative.** If
`ℒ ⊗_{𝒪_X} ℳ ≅ 𝒪_X` — so that `ℳ` is the tensor inverse `ℒ^{⊗ -1}`, equivalently the dual `ℒ^∨`
by Stacks 0B8K — then `c₁(ℳ) ∩ α = -(c₁(ℒ) ∩ α)` in `A_k(X)` for every `α ∈ Z_{k+1}(X)`. -/
theorem firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit (k : ℤ) (L M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : Scheme.Modules.tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf)
    (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k M α = -firstChernClassCapOfInvertible C p k L α := by
  rw [eq_neg_iff_add_eq_zero, add_comm, firstChernClassCapOfInvertible_tensorObj C p k L M α,
    firstChernClassCapOfInvertible_congr C p k _ _ e α]
  exact firstChernClassCapOfInvertible_unit C p k α

/-- **Stacks 02TI for a tensor inverse.** The descended operation `c₁(ℒ^{⊗ -1}) ∩ -` on Chow
groups is the negative of `c₁(ℒ) ∩ -`. -/
theorem firstChernClassCapOnChow_eq_neg_of_tensorObj_iso_unit (k : ℤ) (L M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hL : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L))
    (hM : FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k M))
    (e : Scheme.Modules.tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf) :
    firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k M) hM =
      -firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k L) hL := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ ?_)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.neg_apply,
    firstChernClassCapOnChow_mk]
  exact firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit C p k L M e α

/-- **The line-bundle case of Stacks 0FA5.** As graded operations `A_{n-i}(X) ⟶ A_{n-i-1}(X)`,

  `c₁(ℒ^{⊗ -1}) ∩ - = -(c₁(ℒ) ∩ -)`,

for any tensor inverse `ℳ` of `ℒ`. -/
theorem firstChernCapStep_eq_neg_of_tensorObj_iso_unit (n : ℤ) (L M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hfacL : InvertibleChernCapDescends C p L) (hfacM : InvertibleChernCapDescends C p M)
    (e : Scheme.Modules.tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf) (i : ℕ) :
    firstChernCapStep C p n M hfacM i = -firstChernCapStep C p n L hfacL i := by
  have h := firstChernClassCapOnChow_eq_neg_of_tensorObj_iso_unit C p
    (n - ((i + 1 : ℕ) : ℤ)) L M (hfacL _) (hfacM _) e
  simp only [firstChernCapStep, h, chowGroupDegreeCast_neg]

/-! ### The formal computation the source omits

`e_k(-x_1, …, -x_r) = (-1)^k e_k(x_1, …, x_r)`, by induction along the Pascal recursion that
defines the elementary symmetric functions of `Stacks.Chow.elemSymmChernCap`. -/

variable (n : ℤ) {r : ℕ} (L M : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]
  (hfacL : ∀ j, InvertibleChernCapDescends C p (L j))
  (hfacM : ∀ j, InvertibleChernCapDescends C p (M j))

/-- In degree zero the elementary symmetric cap operation is the identity, hence does not depend
on the family of invertible modules at all. -/
theorem elemSymmChernCap_degree_zero_congr (m : ℕ) (hm : m ≤ r) :
    elemSymmChernCap C p n M hfacM m hm 0 = elemSymmChernCap C p n L hfacL m hm 0 :=
  QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [elemSymmChernCap_degree_zero_apply, elemSymmChernCap_degree_zero_apply])

/-- **Negating the first Chern class operations multiplies the `k`-th elementary symmetric
function by `(-1)^k`.** If `ℳ_j` has `c₁(ℳ_j) ∩ - = -(c₁(ℒ_j) ∩ -)` for every `j` — which by
`Stacks.Chow.firstChernCapStep_eq_neg_of_tensorObj_iso_unit` is the case when `ℳ_j` is a tensor
inverse of `ℒ_j` — then for every `m ≤ r` and every degree `k`

  `e_k(c₁(ℳ_0), …, c₁(ℳ_{m-1})) = (-1)^k e_k(c₁(ℒ_0), …, c₁(ℒ_{m-1}))`

as operations `A_n(X) ⟶ A_{n-k}(X)`. -/
theorem elemSymmChernCap_eq_zsmul_of_neg_steps
    (hstep : ∀ (j : Fin r) (i : ℕ),
      firstChernCapStep C p n (M j) (hfacM j) i = -firstChernCapStep C p n (L j) (hfacL j) i) :
    ∀ (m : ℕ) (hm : m ≤ r) (k : ℕ) (x : chowGroup C p n),
      elemSymmChernCap C p n M hfacM m hm k x =
        ((-1 : ℤ) ^ k) • elemSymmChernCap C p n L hfacL m hm k x := by
  intro m
  induction m <;> intro hm k x <;> cases k
  all_goals try (rw [elemSymmChernCap_degree_zero_congr C p n L M hfacL hfacM _ hm]; simp)
  · rw [elemSymmChernCap_zero_succ C p n M hfacM hm, elemSymmChernCap_zero_succ C p n L hfacL hm]
    simp
  · rename_i m ih s
    rw [elemSymmChernCap_succ C p n M hfacM m hm s, elemSymmChernCap_succ C p n L hfacL m hm s]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [ih (Nat.le_of_succ_le hm) (s + 1) x, ih (Nat.le_of_succ_le hm) s x, hstep ⟨m, hm⟩ s]
    have hpow : ((-1 : ℤ) ^ (s + 1)) = -((-1 : ℤ) ^ s) := by ring
    simp only [AddMonoidHom.neg_apply, AddMonoidHom.map_zsmul, hpow, neg_smul, smul_add, smul_neg]

/-! ### Stacks 0FA5 -/

/-- **Stacks 0FA5, componentwise on cap products.** Let `ℰ` be finite locally free of rank `r`
with a filtration whose successive quotients are the invertible modules `ℒ_0, …, ℒ_{r-1}`, and
let `ℰ^∨` be finite locally free of rank `r` with the dual filtration, whose successive quotients
`ℳ_j` are tensor inverses of the `ℒ_j`. Both filtrations are presented as the towers of short
exact sequences `0 ⟶ ℒ_j ⟶ ℰ_{j+1} ⟶ ℰ_j ⟶ 0` and `0 ⟶ ℳ_j ⟶ ℰ^∨_{j+1} ⟶ ℰ^∨_j ⟶ 0` that
Stacks 02UJ consumes. Then for every `n`-cycle `α` and every `i`

  `c_i(ℰ^∨) ∩ α = (-1)^i • (c_i(ℰ) ∩ α)`

in `A_{n-i}(X)`, which is the sign rule of the source read degree by degree against `α`. -/
@[stacks 0FA5 "CORRECTION OF FORM: the source states c_i(E^dual) = (-1)^i c_i(E) in the \
bivariant ring A^i(X). This development has no bivariant ring and no total Chern class, for the \
reason recorded in the Stacks 02UH clause of \
StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation, so -- exactly as for Stacks \
02UJ, which this result is read on top of -- the identity is stated degree by degree as cap \
products against a fixed cycle: for every n, every alpha in CycleGroup C p n and every i >= 0, \
c_i(E^dual) cap alpha = (-1)^i times (c_i(E) cap alpha) in A_{n-i}(X). It holds for EVERY i and \
EVERY rank r; no degree and no rank is special-cased. WHAT IS CARRIED: the reduction of the \
source's first paragraph, i.e. the two filtrations themselves, as the towers of short exact \
sequences that Stacks 02UJ consumes -- for E with invertible quotients L_j, and for E^dual with \
quotients M_j satisfying L_j tensor M_j iso O_X, which is the source's E_{i-1}^perp/E_i^perp iso \
L_i^{tensor -1}. The source gets these from Stacks 02UL and the injectivity of pi^*. That \
reduction CANNOT be performed in this repository, for two independent reasons: (1) Stacks 02UL \
is Stacks.Chow.exists_splittingMorphism and the filtration it delivers is \
Stacks.WeilCohomology.HasInvertibleFiltration, an inductive Prop, from which the tower of \
modules and maps that Stacks 02UJ needs -- which is data -- cannot be eliminated; (2) nothing in \
this repository states that the Chern class cap product commutes with flat pullback (the clause \
of Stacks 02U0 quoted as Stacks 02U1), so injectivity of pi^* has no identity on P to descend \
to X. ALSO CARRIED, each of them an input of Stacks 02UJ itself and carried there for the same \
reason: chern and chernDual, the Stacks 02U0 component data in every rank; hnorm and hnormDual, \
the Stacks 02U0 normalisation c_0 = 1 along each tower; hbinom and hbinomDual, the equality of \
binomial transforms that Stacks 02UD gives once Stacks 02UG is applied, neither of which is \
proved here; and hfacL, hfacM, Stacks 02TI for c_1 of each quotient. NOT CARRIED, i.e. proved \
here: the line-bundle case c_1(L^{tensor -1}) = -c_1(L), deduced from the two clauses of Stacks \
02SP as firstChernCapStep_eq_neg_of_tensorObj_iso_unit and absent from this repository before \
this file; and the formal computation the source omits, e_k(-x) = (-1)^k e_k(x), proved for \
every degree and every length as elemSymmChernCap_eq_zsmul_of_neg_steps. The dual is given as a \
tensor inverse rather than as Stacks.SheafOfModules.dualSheaf; by Stacks 0B8K the two agree up \
to isomorphism and c_1 depends only on the isomorphism class \
(firstChernClassCapOfInvertible_congr), so this is a change of spelling and not a weakening"]
theorem chernClassCapExt_eq_zsmul_of_dualFiltration
    (hdual : ∀ j, Scheme.Modules.tensorObj (L j) (M j) ≅ SheafOfModules.unit X.ringCatSheaf)
    (E EDual : ℕ → X.Modules)
    (sub : ∀ j : Fin r, L j ⟶ E ((j : ℕ) + 1)) (proj : ∀ j : Fin r, E ((j : ℕ) + 1) ⟶ E (j : ℕ))
    (hzero : ∀ j : Fin r, sub j ≫ proj j = 0)
    (hexact : ∀ j : Fin r, (ShortComplex.mk (sub j) (proj j) (hzero j)).ShortExact)
    (hrank : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (E m) m)
    (subDual : ∀ j : Fin r, M j ⟶ EDual ((j : ℕ) + 1))
    (projDual : ∀ j : Fin r, EDual ((j : ℕ) + 1) ⟶ EDual (j : ℕ))
    (hzeroDual : ∀ j : Fin r, subDual j ≫ projDual j = 0)
    (hexactDual : ∀ j : Fin r,
      (ShortComplex.mk (subDual j) (projDual j) (hzeroDual j)).ShortExact)
    (hrankDual : ∀ m : ℕ, m ≤ r → PullbackPreservesRank (EDual m) m)
    (chern chernDual : ∀ m : ℕ, ChernClassCycleRule C m) (α : CycleGroup C p n)
    (hnorm : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (E m) m (hrank m hm) (chern m) 0 α = cycleClassDegreeZero C p n α)
    (hnormDual : ∀ (m : ℕ) (hm : m ≤ r),
      chernClassCapExt C p n (EDual m) m (hrankDual m hm) (chernDual m) 0 α =
        cycleClassDegreeZero C p n α)
    (hbinom : ∀ j : Fin r, ∀ i ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (L j) (hfacL j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (E ((j : ℕ) + 1)) ((j : ℕ) + 1) (hrank ((j : ℕ) + 1) j.isLt)
            (chern ((j : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (L j) (hfacL j)) (j : ℕ)
          (chernCapFamily C p n (E (j : ℕ)) (j : ℕ) (hrank (j : ℕ) j.isLt.le)
            (chern (j : ℕ)) α) i)
    (hbinomDual : ∀ j : Fin r, ∀ i ≤ (j : ℕ) + 1,
      binomialTransform (inverseFirstChernCapStep C p n (M j) (hfacM j)) ((j : ℕ) + 1)
          (chernCapFamily C p n (EDual ((j : ℕ) + 1)) ((j : ℕ) + 1)
            (hrankDual ((j : ℕ) + 1) j.isLt) (chernDual ((j : ℕ) + 1)) α) i =
        binomialTransform (inverseFirstChernCapStep C p n (M j) (hfacM j)) (j : ℕ)
          (chernCapFamily C p n (EDual (j : ℕ)) (j : ℕ) (hrankDual (j : ℕ) j.isLt.le)
            (chernDual (j : ℕ)) α) i)
    (k : ℕ) :
    chernClassCapExt C p n (EDual r) r (hrankDual r le_rfl) (chernDual r) k α =
      ((-1 : ℤ) ^ k) • chernClassCapExt C p n (E r) r (hrank r le_rfl) (chern r) k α := by
  rw [chernClassCapExt_eq_elemSymmChernCap_of_tower C p n M hfacM EDual subDual projDual
      hzeroDual hexactDual hrankDual chernDual α hnormDual hbinomDual r le_rfl k,
    chernClassCapExt_eq_elemSymmChernCap_of_tower C p n L hfacL E sub proj hzero hexact hrank
      chern α hnorm hbinom r le_rfl k]
  exact elemSymmChernCap_eq_zsmul_of_neg_steps C p n L M hfacL hfacM
    (fun j i ↦ firstChernCapStep_eq_neg_of_tensorObj_iso_unit C p n (L j) (M j) (hfacL j)
      (hfacM j) (hdual j) i) r le_rfl k _

end Stacks.Chow

end
