module

public import StacksCore.RingTheory.TensorProduct.Finite
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u v w

/-!
# The tensor product of two Mittag-Leffler modules

Let `R` be a commutative ring and let `M` and `N` be Mittag-Leffler `R`-modules, in the intrinsic
form 059E (1): every map `f` from a finitely presented module into the module dominates and is
dominated by a map `g` into a finitely presented module, `g` dominating `f` meaning that
`Ker(f ⊗ id_T) ⊆ Ker(g ⊗ id_T)` for every test module `T`. Then `M ⊗[R] N` is Mittag-Leffler.

The source writes `M = colim_i M i` and `N = colim_j N j` as directed colimits of finitely
presented modules, notes that `M ⊗[R] N = colim_{(i,j)} M i ⊗[R] N j` with finitely presented
members (Lemma 05BS), and produces the factorizations of 059E (3) for the product system as the
tensor products `a ⊗ b` of the factorizations for the two systems separately. The route taken here
is that same idea read off the intrinsic form 059E (1), with the colimits replaced by the one place
they are used: a map `f` out of a finitely presented module `P` into `M ⊗[R] N` factors, after
precomposition with a surjection from a finite free module `F`, through `F₁ ⊗[R] F₁` for a finitely
presented `F₁` carrying maps `u : F₁ → M` and `v : F₁ → N`, because each of the finitely many
values of `f` on a basis of `F` is a finite sum of pure tensors. The two Mittag-Leffler hypotheses
applied to `u` and to `v` give `a : F₁ → A` and `b : F₁ → B` with `A` and `B` finitely presented
dominating and dominated by them, `A ⊗[R] B` is finitely presented (Lemma 05BS), and `a ⊗ b`
dominates and is dominated by `u ⊗ v`. Descending along the surjection `F → P` is the argument of
Lemma 05CP.

## Main results

* `Stacks.MittagLeffler.TensorProductStable.solution`: the tensor product of two Mittag-Leffler
  `R`-modules is Mittag-Leffler.

## Implementation notes

Domination is named here, `Dominated u a` for "`a` dominates `u`" (059B), and the mathematical
content of the lemma is that it is functorial: domination is preserved by precomposition
(`Dominated.comp`) and by tensoring with a fixed module on either side (`Dominated.rTensor` and
`Dominated.lTensor`, the second being the first read through the commutativity of the tensor
product), hence by tensor products of maps (`Dominated.map`), which is the tensor product `a ⊗ b`
of the source's proof. That last proof is the two factorizations
`u ⊗ v = (id_M ⊗ v) ∘ (u ⊗ id_G)` and `u ⊗ b = (u ⊗ id_B) ∘ (id_F ⊗ b)`, replacing `v` by `b`
while testing on `M ⊗[R] T` and then `u` by `a` while testing on `B ⊗[R] T`.

In particular no directed system, and hence no use of 059E itself, enters the proof: the
hypotheses and the conclusion are all instances of condition (1), which is intrinsic to the
module, so the equivalence 059E is never invoked as a theorem, only its condition (1) is used as
the definition it is (Definition 059F).

The two finite free modules, the `F` surjecting onto `P` and the `F₁` of the factorization, must
live in `Type v`, where the quantifiers of condition (1) sit, while a free module on a finite index
type in `Type v` is built over `R` and so lands in `Type (max u v)`. It is `Shrink`, available
because `R` is `v`-small, that moves them back, exactly as in 05CP and 05CQ; the same
`Shrink.{v} R` is the test module on which domination is read as a containment of the untensored
kernels (`Dominated.ker_le`), which is what the descent along `F → P` uses. The index type of `F₁`
is `Σ i, S i` where `S i` is a finite set of pairs representing the value of the map on the `i`-th
basis vector of `F`, so that `u` and `v` are defined on the same finite free module.

## References

* [StacksProject 05CN](https://stacks.math.columbia.edu/tag/05CN)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
* [StacksProject 05BS](https://stacks.math.columbia.edu/tag/05BS)
* [StacksProject 05CP](https://stacks.math.columbia.edu/tag/05CP)
-/

namespace Stacks.MittagLeffler.TensorProductStable



open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- `Dominated u a` says that the map `a` dominates the map `u` (059B): the kernel of `u ⊗ id_T` is
contained in the kernel of `a ⊗ id_T` for every test module `T`. -/
private abbrev Dominated {F M A : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M]
    [Module R M] [AddCommGroup A] [Module R A] (u : F →ₗ[R] M) (a : F →ₗ[R] A) : Prop :=
  ∀ (T : Type v) [AddCommGroup T] [Module R T],
    LinearMap.ker (u.rTensor T) ≤ LinearMap.ker (a.rTensor T)

/-- A commuting pair of squares whose vertical maps are additive isomorphisms carries a kernel
inclusion to a kernel inclusion. The two rows may be linear over different rings, which is what
lets a domination over one ring be read as one over another. -/
public theorem ker_le_ker_of_comm {S : Type w} [Semiring S]
    {X Y Z X' Y' Z' : Type*} [AddCommMonoid X] [Module S X] [AddCommMonoid Y] [Module S Y]
    [AddCommMonoid Z] [Module S Z] [AddCommMonoid X'] [Module R X'] [AddCommMonoid Y']
    [Module R Y'] [AddCommMonoid Z'] [Module R Z']
    {f : X →ₗ[S] Y} {g : X →ₗ[S] Z} {f' : X' →ₗ[R] Y'} {g' : X' →ₗ[R] Z'}
    (eX : X ≃+ X') (eY : Y ≃+ Y') (eZ : Z ≃+ Z')
    (hf : ∀ x, f' (eX x) = eY (f x)) (hg : ∀ x, g' (eX x) = eZ (g x))
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    LinearMap.ker f' ≤ LinearMap.ker g' := by
  intro x hx
  obtain ⟨y, rfl⟩ := eX.surjective x
  simp only [LinearMap.mem_ker, hf, hg, AddEquivClass.map_eq_zero_iff] at hx ⊢
  exact h hx

/-- The `R`-linear specialization used below: isomorphisms of the source and the two targets
transport a kernel containment backwards. -/
private theorem ker_le_ker_of_comm' {X X' Y Y' Z Z' : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R Y']
    [AddCommGroup Z] [Module R Z] [AddCommGroup Z'] [Module R Z']
    {p : X →ₗ[R] Y} {q : X →ₗ[R] Z} {p' : X' →ₗ[R] Y'} {q' : X' →ₗ[R] Z'}
    (eX : X ≃ₗ[R] X') (eY : Y ≃ₗ[R] Y') (eZ : Z ≃ₗ[R] Z')
    (hp : eY.toLinearMap ∘ₗ p = p' ∘ₗ eX.toLinearMap)
    (hq : eZ.toLinearMap ∘ₗ q = q' ∘ₗ eX.toLinearMap)
    (h : LinearMap.ker p' ≤ LinearMap.ker q') :
    LinearMap.ker p ≤ LinearMap.ker q :=
  ker_le_ker_of_comm (S := R) eX.symm.toAddEquiv eY.symm.toAddEquiv eZ.symm.toAddEquiv
    (fun x => (eY.eq_symm_apply).mpr (by simpa using congr($hp (eX.symm x))))
    (fun x => (eZ.eq_symm_apply).mpr (by simpa using congr($hq (eX.symm x)))) h


/-- Domination is preserved by precomposition with a common map. -/
private theorem Dominated.comp {W X Y Z : Type v} [AddCommGroup W] [Module R W] [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] {p : X →ₗ[R] Y}
    {q : X →ₗ[R] Z} (h : Dominated p q) (r : W →ₗ[R] X) : Dominated (p ∘ₗ r) (q ∘ₗ r) := by
  intro T _ _
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_comp]
  exact Submodule.comap_mono (h T)

/-- Domination is preserved by tensoring on the right with a module `C`: it is domination of the
same two maps, tested on `C ⊗[R] T` instead of on `T`. -/
private theorem Dominated.rTensor {F M A : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M]
    [Module R M] [AddCommGroup A] [Module R A] {u : F →ₗ[R] M} {a : F →ₗ[R] A} (h : Dominated u a)
    (C : Type v) [AddCommGroup C] [Module R C] : Dominated (u.rTensor C) (a.rTensor C) := by
  intro T _ _
  refine ker_le_ker_of_comm' (TensorProduct.assoc R F C T) (TensorProduct.assoc R M C T)
    (TensorProduct.assoc R A C T) ?_ ?_ (h (C ⊗[R] T)) <;> ext <;> simp

/-- Domination is preserved by tensoring on the left with a module `C`: this is the case of the
right-hand factor, read through the commutativity of the tensor product. -/
private theorem Dominated.lTensor {G N B : Type v} [AddCommGroup G] [Module R G] [AddCommGroup N]
    [Module R N] [AddCommGroup B] [Module R B] {v : G →ₗ[R] N} {b : G →ₗ[R] B} (h : Dominated v b)
    (C : Type v) [AddCommGroup C] [Module R C] : Dominated (v.lTensor C) (b.lTensor C) := by
  intro T _ _
  refine ker_le_ker_of_comm' (LinearEquiv.rTensor T (TensorProduct.comm R C G))
    (LinearEquiv.rTensor T (TensorProduct.comm R C N))
    (LinearEquiv.rTensor T (TensorProduct.comm R C B)) ?_ ?_ (h.rTensor C T) <;> ext <;> simp

/-- **Domination is stable under tensor products of maps:** if `a` dominates `u : F →ₗ[R] M` and
`b` dominates `v : G →ₗ[R] N`, then `a ⊗ b` dominates `u ⊗ v`. This is the tensor product `a ⊗ b`
of the source's proof, read off condition 059E (1) instead of the directed systems. -/
private theorem Dominated.map {F G M N A B : Type v} [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {u : F →ₗ[R] M} {a : F →ₗ[R] A}
    {v : G →ₗ[R] N} {b : G →ₗ[R] B} (hu : Dominated u a) (hv : Dominated v b) :
    Dominated (TensorProduct.map u v) (TensorProduct.map a b) := by
  -- `u ⊗ v = (id_M ⊗ v) ∘ (u ⊗ id_G)` and `u ⊗ b = (id_M ⊗ b) ∘ (u ⊗ id_G)`: replace `v` by `b`.
  have h₁ : Dominated (TensorProduct.map u v) (TensorProduct.map u b) := by
    simpa only [LinearMap.lTensor_comp_rTensor] using (hv.lTensor M).comp (u.rTensor G)
  -- `u ⊗ b = (u ⊗ id_B) ∘ (id_F ⊗ b)` and `a ⊗ b = (a ⊗ id_B) ∘ (id_F ⊗ b)`: replace `u` by `a`.
  have h₂ : Dominated (TensorProduct.map u b) (TensorProduct.map a b) := by
    simpa only [LinearMap.rTensor_comp_lTensor] using (hu.rTensor B).comp (b.lTensor F)
  exact fun T _ _ => (h₁ T).trans (h₂ T)

/-- Domination implies containment of the untensored kernels: test it on `Shrink.{v} R`, the copy
of `R` itself living in the universe of the test modules. -/
private theorem Dominated.ker_le [Small.{v} R] {X Y Z : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] {p : X →ₗ[R] Y} {q : X →ₗ[R] Z}
    (h : Dominated p q) : LinearMap.ker p ≤ LinearMap.ker q := by
  refine ker_le_ker_of_comm'
    ((TensorProduct.rid R X).symm.trans (LinearEquiv.lTensor X (Shrink.linearEquiv R R).symm))
    ((TensorProduct.rid R Y).symm.trans (LinearEquiv.lTensor Y (Shrink.linearEquiv R R).symm))
    ((TensorProduct.rid R Z).symm.trans (LinearEquiv.lTensor Z (Shrink.linearEquiv R R).symm))
    ?_ ?_ (h (Shrink.{v} R)) <;> ext <;> simp

/-- A finite module in `Type v` over a `v`-small ring is a quotient of a finite free module that
also lives in `Type v`, given with a basis indexed by `Fin n`. -/
public theorem exists_finite_free_surjective [Small.{v} R] (P : Type v) [AddCommGroup P]
    [Module R P] [Module.Finite R P] :
    ∃ (n : ℕ) (F : Type v) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Basis (Fin n) R F)
      (π : F →ₗ[R] P), Function.Surjective π := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  exact ⟨n, Shrink.{v} (Fin n → R), inferInstance, inferInstance,
    (Pi.basisFun R (Fin n)).map (Shrink.linearEquiv R (Fin n → R)).symm,
    π ∘ₗ (Shrink.linearEquiv R (Fin n → R)).toLinearMap,
    hπ.comp (Shrink.linearEquiv R (Fin n → R)).surjective⟩

/-- A map into `M ⊗[R] N` from a free module on a finite basis factors through `F₁ ⊗[R] F₁` for a
finitely presented `F₁` in `Type v` equipped with maps `u` to `M` and `v` to `N`: each of the
finitely many values on the basis is a finite sum of pure tensors, and the finitely many tensor
factors occurring are the images under `u` and `v` of the basis vectors of `F₁`. -/
private theorem exists_map_factorization [Small.{v} R] {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} {F : Type w} [AddCommGroup F] [Module R F]
    (bF : Module.Basis (Fin n) R F) (f : F →ₗ[R] M ⊗[R] N) :
    ∃ (F₁ : Type v) (_ : AddCommGroup F₁) (_ : Module R F₁)
      (_ : Module.FinitePresentation R F₁) (u : F₁ →ₗ[R] M) (v : F₁ →ₗ[R] N)
      (φ : F →ₗ[R] F₁ ⊗[R] F₁), f = TensorProduct.map u v ∘ₗ φ := by
  classical
  choose S hS using fun i : Fin n => TensorProduct.exists_finset (f (bF i))
  let J : Type v := Σ i : Fin n, {x // x ∈ S i}
  let e : Shrink.{v} (J → R) ≃ₗ[R] (J → R) := Shrink.linearEquiv R (J → R)
  let b : Module.Basis J R (Shrink.{v} (J → R)) := (Pi.basisFun R J).map e.symm
  have : Module.FinitePresentation R (Shrink.{v} (J → R)) :=
    (LinearEquiv.finitePresentation_iff e).mpr inferInstance
  refine ⟨Shrink.{v} (J → R), inferInstance, inferInstance, inferInstance,
    b.constr ℕ (fun j => ((j.2 : M × N).1 : M)), b.constr ℕ (fun j => ((j.2 : M × N).2 : N)),
    bF.constr ℕ (fun i => ∑ x : {x // x ∈ S i}, b ⟨i, x⟩ ⊗ₜ[R] b ⟨i, x⟩), bF.ext fun i => ?_⟩
  simp only [Module.Basis.constr_basis, LinearMap.coe_comp, Function.comp_apply, map_sum,
    TensorProduct.map_tmul]
  rw [hS i, ← Finset.sum_coe_sort (S i) (fun y => y.1 ⊗ₜ[R] y.2)]

/-- Stacks 05CN: if `M` and `N` are Mittag-Leffler `R`-modules, in the intrinsic form of condition
(1) of 059E, then so is `M ⊗[R] N`. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T))
    (hN : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M ⊗[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T) := by
  intro P _ _ _ f
  -- A surjection onto `P` from a finite free module in `Type v`, and a factorization of `f ∘ π`
  -- through `F₁ ⊗[R] F₁` with `F₁` finitely presented.
  obtain ⟨n, F, _, _, bF, π, hπ⟩ := exists_finite_free_surjective (R := R) P
  obtain ⟨F₁, _, _, _, u, v, φ, hfac⟩ := exists_map_factorization bF (f ∘ₗ π)
  -- The Mittag-Leffler conditions on `M` and on `N`, applied to `u` and to `v`.
  obtain ⟨A, _, _, _, a, ha⟩ := hM F₁ u
  obtain ⟨B, _, _, _, b, hb⟩ := hN F₁ v
  -- `u ⊗ v` and `a ⊗ b` dominate each other, hence so do `f ∘ π` and `(a ⊗ b) ∘ φ`.
  have h₁ : Dominated (f ∘ₗ π) (TensorProduct.map a b ∘ₗ φ) := by
    rw [hfac]
    exact (Dominated.map (fun S _ _ => (ha S).le) (fun S _ _ => (hb S).le)).comp φ
  have h₂ : Dominated (TensorProduct.map a b ∘ₗ φ) (f ∘ₗ π) := by
    rw [hfac]
    exact (Dominated.map (fun S _ _ => (ha S).ge) (fun S _ _ => (hb S).ge)).comp φ
  -- The kernel of `(a ⊗ b) ∘ φ` contains that of `f ∘ π`, hence that of `π`: descend along `π`.
  obtain ⟨g, hg⟩ := LinearMap.exists_comp_eq_of_ker_le hπ
    ((LinearMap.ker_le_ker_comp π f).trans h₁.ker_le)
  refine ⟨A ⊗[R] B, inferInstance, inferInstance, inferInstance, g, fun T _ _ => ?_⟩
  -- `π ⊗ id_T` is surjective, so the mutual domination of `f ∘ π` and `g ∘ π` is that of `f`, `g`.
  refine Submodule.comap_injective_of_surjective (LinearMap.rTensor_surjective T hπ) ?_
  rw [← LinearMap.ker_comp, ← LinearMap.ker_comp, ← LinearMap.rTensor_comp,
    ← LinearMap.rTensor_comp, hg]
  exact le_antisymm (h₁ T) (h₂ T)

end Stacks.MittagLeffler.TensorProductStable

/-!
# The tensor product of two Mittag-Leffler modules

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) when the equivalent conditions of
Proposition 059E hold for it. Only one of those five conditions is intrinsic to `M`, namely
condition (1), and it is the one used here: for every finitely presented `R`-module `P` and every
module map `f : P → M` there are a finitely presented `R`-module `Q` and a module map
`g : P → Q` such that `f` and `g` dominate each other, i.e. `Ker (f ⊗ id_T) = Ker (g ⊗ id_T)`
for every `R`-module `T`.

This file states Stacks 05CN: the Mittag-Leffler condition is stable under tensor product. The
source's proof writes `M = colim_{i ∈ I} M i` and `N = colim_{j ∈ J} N j` as directed colimits of
finitely presented modules; then `M i ⊗ N j` is finitely presented (Lemma 05BS) and
`M ⊗_R N = colim_{(i,j) ∈ I × J} M i ⊗_R N j`, so it suffices to produce the factorizations of
condition 059E (3) for the product system. Given `(i, j)`, choose `i' ≥ i` and `j' ≥ j` as in
059E (3) for the two systems separately; if `a : M i'' → M i'` and `b : N j'' → N j'` factor the
transition maps for `i'' ≥ i` and `j'' ≥ j`, then `a ⊗ b` factors the transition map of the product
system, which is 059E (3) for `M ⊗_R N`.

## Main results

* `Module.mittagLeffler_tensorProduct`: if `M` and `N` are Mittag-Leffler `R`-modules, then so is
  `M ⊗[R] N`.

## Implementation notes

Mathlib has no predicate for a Mittag-Leffler module — its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system* —
so the condition is spelled out inline, three times, in the intrinsic form 059E (1), exactly as in
05CQ (`Module.mittagLeffler_trans`). Mutual domination is spelled out as equality of the kernels of
the tensored maps, `f ⊗ id_T` being `f.rTensor T`, as in 059D
(`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`). The name mutates that of the Mathlib lemma
`Module.Finite.tensorProduct`.

The modules `M`, `N` and the quantified `P`, `Q`, `T` all live in one universe `Type v`, and `R` is
`v`-small, as in 059D and 05CQ; the tensor product `M ⊗[R] N` then lies in `Type v` too, so the
three occurrences of condition 059E (1) are literally the same predicate applied to three modules.
For a `v`-small `R` every finitely presented `R`-module is isomorphic to one in `Type v`, so the
displayed quantifiers are the source's quantifiers over all finitely presented modules and over all
test modules.

Faithfulness. (1) No hypothesis is dead: both Mittag-Leffler hypotheses are needed, and neither is
implied by the conclusion — over `R = ℤ` the module `M = ℤ` is Mittag-Leffler (finitely presented,
so `Q = P` and `g = f` serve) while `N = ℚ` is not (flat and countably generated but not
projective, Theorem 059Z) and `M ⊗_ℤ N ≅ ℚ` is not either, so `hN` cannot be dropped, nor `hM` by
the symmetry of the tensor product; and `Small.{v} R` is what makes the quantifiers over
`P, Q, T : Type v` the source's quantifiers over all modules. (2) The scalars and the base are the
source's: all three conditions are conditions over the one ring `R`, the tensor product is over
`R`, and the `R`-module structure on `M ⊗[R] N` is the canonical one, neither restricted nor
extended along any ring map. (3) The source names no canonical map: `Q` and `g` are existentially
quantified in 059E (1) itself, and what is canonical is pinned — the maps whose kernels are
compared are `f.rTensor T` and `g.rTensor T`, not arbitrary maps `P ⊗ T → M ⊗ T` and
`P ⊗ T → Q ⊗ T`. (4) The instantiation is not degenerate: for `R = ℤ` and `M = N = ⊕_{n : ℕ} ℤ`
both hypotheses hold (a free module is Mittag-Leffler, Example 059R (2)) and the conclusion
says something non-vacuous about the free module `M ⊗_ℤ N` of countable rank, while the
conclusion is not satisfied by every module, `ℚ` not being Mittag-Leffler over `ℤ`.

## References

* [StacksProject 05CN](https://stacks.math.columbia.edu/tag/05CN)
-/



@[expose] public section

open scoped TensorProduct

/-- **Stacks 05CN.** If `R` is a ring and `M`, `N` are Mittag-Leffler modules over `R`, then
`M ⊗_R N` is a Mittag-Leffler module. The Mittag-Leffler condition is spelled out in the
intrinsic form 059E (1): every map `f` from a finitely presented module into the module in
question dominates and is dominated by a map `g` into a finitely presented module, domination
meaning containment of the kernels of the maps `· ⊗ id_T`. -/
@[stacks 05CN "Mittag-Leffler is spelled out inline as condition (1) of 059E."]
public theorem Module.mittagLeffler_tensorProduct {R : Type u} [CommRing R] [Small.{v} R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T))
    (hN : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M ⊗[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T) :=
  Stacks.MittagLeffler.TensorProductStable.solution hM hN

end
