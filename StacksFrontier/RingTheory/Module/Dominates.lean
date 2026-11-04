module

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
public import Mathlib.RingTheory.PicardGroup
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
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Domination of maps of modules
-/

@[expose] public section


@[expose] public section

universe u v w w' t

/-!
# Domination of maps of modules

Let `R` be a commutative ring and let `f : M → N` and `g : M → M'` be maps of `R`-modules with
common source `M`. Then `g` *dominates* `f` if for every `R`-module `Q` the kernel of
`f ⊗_R id_Q` is contained in the kernel of `g ⊗_R id_Q`, as submodules of `M ⊗_R Q`.

Factorizations are the source of examples: if `g = h ∘ f` for some `h : N → M'`, then
`g ⊗ id_Q = (h ⊗ id_Q) ∘ (f ⊗ id_Q)`, so everything killed by `f ⊗ id_Q` is killed by
`g ⊗ id_Q` and `g` dominates `f`. The converse fails in general and holds as soon as `Coker(f)`
is of finite presentation (Lemma 059D), so domination is a weakening of factorization through `f`
which remembers only what happens to kernels. Domination is a preorder on the maps out of `M`:
every `g` dominates `f = id_M`, since `Ker(id_M ⊗ id_Q) = 0`; every `g` dominates itself; and a
map dominating a map which dominates `f` dominates `f`.

Taking `Q = R` and transporting along `M ⊗_R R ≅ M` shows that domination implies the plain
containment `Ker(f) ⊆ Ker(g)`, and it is strictly weaker than domination: for `R = ℤ`,
`M = N = M' = ℤ`, `f` multiplication by `2` and `g = id` one has `Ker(f) = 0 ⊆ Ker(g)`, yet `g`
does not dominate `f`, because at `Q = ℤ/2ℤ` the element `1 ⊗ 1` is killed by `f ⊗ id_Q` while
`g ⊗ id_Q` is the identity. In that same example `f` dominates `g`, so the relation is not
symmetric; mutual domination is the relation in which the Mittag-Leffler condition on a module is
phrased (Proposition 059E (1), Definition 059F).

It is enough to test the condition on finitely presented modules `Q` (Lemma 059C).

## Main definitions

* `LinearMap.Dominates`: `g.Dominates f` says that `g` dominates `f`, that is, that
  `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` for every test module `Q`.

## Implementation notes

`f ⊗_R id_Q` is `f.rTensor Q`, Mathlib's named combinator for tensoring a map with the identity
of `Q` on the right, and the source's containment of kernels is the containment
`ker (f.rTensor Q) ≤ ker (g.rTensor Q)` of two submodules of `M ⊗_R Q`. The arguments are ordered
so that dot notation reads as the source's sentence, `g.Dominates f` for "`g` dominates `f`",
where the source lists `f` first.

A `Prop` cannot quantify over every universe at once, so the test module `Q` has to be confined
to one universe, and the universe it is confined to is `Type u`, that of the **ring**, not that of
the source module `M`. This is unconditionally the source's condition on all `Q` whatsoever: a
finitely presented `R`-module is `Rⁿ` modulo a finitely generated submodule, hence isomorphic to
one in `Type u` for every `R`; an arbitrary module is a filtered colimit of finitely presented
ones; and the containment of kernels is invariant under isomorphism of test modules and passes to
a filtered colimit, since tensoring commutes with filtered colimits — which is the proof of
Lemma 059C. Confining `Q` instead to the universe of `M` would need `R` to be `Type v`-small to
mean the same thing, and would be vacuous without it: over a field `R` that is not `v`-small every
`R`-module in `Type v` is zero, so both kernels are everything and every `g` would "dominate"
every `f`. Quantifying test objects over the ring's universe is also Mathlib's convention for a
predicate of this shape; `Module.Flat.out` quantifies over `⦃P : Type u⦄`.

Nothing in the definition uses negatives or the multiplicative inverse-free part of a ring beyond
what the tensor product needs, so `R` is a commutative semiring and the modules are commutative
monoids, where the source has a commutative ring and abelian groups. The targets `N` and `M'` live
in their own universes, since the submodules being compared live in `M ⊗_R Q` and the two targets
never interact. Over a commutative ring the group-spelled condition, quantified over
`Q : Type u` carrying `[AddCommGroup Q] [Module R Q]`, is equivalent to this one, but not
definitionally so: the equivalence is proved by supplying `Module.addCommMonoidToAddCommGroup` in
one direction and forgetting it in the other, and `Iff.rfl` between the two fails.

Faithfulness. (1) No datum is idle: both maps occur in the conclusion, `f` through the kernel
being contained and `g` through the kernel containing it, and `Q` is quantified over, so nothing
is decoration. (2) The scalars and the base are the source's: `f` and `g` are `R`-linear for the
one base ring `R`, both tensor products are `⊗[R]` over that same `R`, and neither the maps nor
the test module is localized or base changed. (3) The maps whose kernels are compared are pinned,
not merely asserted to exist: they are `f.rTensor Q` and `g.rTensor Q`, the source's
`f ⊗_R id_Q` and `g ⊗_R id_Q`, and not arbitrary maps `M ⊗ Q → N ⊗ Q` and `M ⊗ Q → M' ⊗ Q`.
(4) The instantiation is not degenerate: the predicate is satisfiable, every `g` dominating
`f = id_M` since `Ker(id_M ⊗ id_Q) = 0`, and it is not always satisfied, `id_ℤ` failing to
dominate multiplication by `2` on `ℤ` at `Q = ℤ/2ℤ` as above.

## References

* [Stacks Project, Tag 059B](https://stacks.math.columbia.edu/tag/059B)
-/



namespace LinearMap

/-- **Stacks 059B.** Let `f : M → N` and `g : M → M'` be maps of `R`-modules with common source.
We say `g` *dominates* `f` if for every `R`-module `Q` we have
`Ker(f ⊗_R id_Q) ⊆ Ker(g ⊗_R id_Q)` as submodules of `M ⊗_R Q`. -/
@[stacks 059B "Domination is spelled out as containment of the kernels of the two maps
  tensored with the identity of the test module."]
public def Dominates {R : Type u} [CommSemiring R] {M : Type v} {N : Type w} {M' : Type w'}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid M']
    [Module R M'] (g : M →ₗ[R] M') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type u) [AddCommMonoid Q] [Module R Q],
    LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q)

end LinearMap


/-!
# Domination of maps of modules is tested on finitely presented modules

Let `f : M → N` and `g : M → M'` be maps of `R`-modules with common source. Then `g` dominates `f`
(Definition 059B) as soon as `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` holds for every *finitely presented*
test module `Q`.

The source writes an arbitrary test module `Q` as the colimit of a directed system of finitely
presented modules and appeals to the exactness of directed colimits and to their commutation with
the tensor product. The argument here is that colimit argument made elementwise: an element
`x ∈ M ⊗ Q` killed by `f ⊗ id_Q` is exhibited as the image of an element of `M ⊗ Q'` killed by
`f ⊗ id_{Q'}` for a single finitely presented `Q'` mapping to `Q`, which is what one stage of the
colimit provides, and the containment at `Q'` then pushes forward to `x`.

## Main results

* `Stacks.Modules.Domination.solution`: `g` dominates `f` if and only if
  `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` for every finitely presented `R`-module `Q`.
* `LinearMap.Dominates.ker_rTensor_le`: domination gives `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` for a
  test module `Q` in an arbitrary universe, not only for the test modules of `Type u` it
  quantifies over.

## Implementation notes

That stage is reached in two steps, both elementwise. The colimit step,
`exists_fg_lTensor_subtype_eq_of_rTensor_eq_zero`, moves `x` to a finitely generated submodule
`Q₁ ≤ Q` on which `f ⊗ id` still kills it: `M ⊗ Q` is the direct limit of the `M ⊗ Q'` over the
finitely generated submodules `Q'` of `Q`, so both the element and the vanishing of its image are
witnessed at a finite stage. It is `Submodule.FG.exists_rTensor_fg_inclusion_eq` conjugated by
`TensorProduct.comm`, the test module being the right tensor factor here and the left one there.
The presentation step, `exists_finitePresentation_lTensor_eq_of_rTensor_eq_zero`, then replaces a
finitely generated test module `A` by a finitely presented one: a presentation `Rⁿ ↠ A` lifts the
element to `M ⊗ Rⁿ`, where right exactness of the tensor product writes the obstruction
`(f ⊗ id)(y)` as coming from `N ⊗ Ker(Rⁿ → A)`, and the finitely many relations occurring in that
expression span a finitely generated `K ≤ Ker(Rⁿ → A)` by which `Rⁿ` may be divided: `Rⁿ / K` is
finitely presented, still maps onto `A`, and the obstruction dies in `N ⊗ Rⁿ / K`. That an element
coming from `N ⊗ L` needs only finitely many of the relations in `L` is
`exists_fg_le_lTensor_mkQ_eq_zero`.

The finitely presented module so produced lies in the universe of `R`, while the finitely presented
test modules of the right-hand side lie in the universe of `M`. It is finitely generated, hence
`v`-small by `Module.Finite.small`, so `Shrink` moves it into the universe of `M` — this is what
the hypothesis `Small.{v} R` is for — and `ker_rTensor_le_of_linearEquiv` says that the containment
of kernels does not distinguish isomorphic test modules. The same `Shrink` step runs in the other
direction: a finitely presented test module in `Type v` is `u`-small, `u` being the universe of `R`
that `LinearMap.Dominates` quantifies over, so the containment it provides there transports back.
`ker_rTensor_le_of_forall_finitePresentation` is therefore stated for a test module in an arbitrary
universe, since the test modules it is applied to come from both.

The same descent proves that domination itself is universe-insensitive, which is
`LinearMap.Dominates.ker_rTensor_le`: the finitely presented module it descends a given element to
is produced in the universe of `R`, which is the universe `LinearMap.Dominates` quantifies over, so
domination applies to it directly and the containment of kernels transports to a test module in any
universe — with no smallness hypothesis and no `Shrink` step. This is what lets
domination be tested at a module in the universe of `M`, as the proof of Proposition 059M does.

## References

* [StacksProject 059B](https://stacks.math.columbia.edu/tag/059B)
* [StacksProject 059C](https://stacks.math.columbia.edu/tag/059C)
-/

namespace Stacks.Modules.Domination



open TensorProduct LinearMap

section Helpers

variable {R : Type u} [CommRing R]

/-- Tensoring with a map on the left and tensoring with a map on the right commute. -/
private lemma rTensor_lTensor_apply {M M' N N' : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] [AddCommMonoid N']
    [Module R N'] (f : M →ₗ[R] M') (u : N →ₗ[R] N') (x : M ⊗[R] N) :
    f.rTensor N' (u.lTensor M x) = u.lTensor M' (f.rTensor N x) := by
  rw [← comp_apply, rTensor_comp_lTensor, ← comp_apply, lTensor_comp_rTensor]

/-- The containment `Ker(f ⊗ id) ⊆ Ker(g ⊗ id)` does not distinguish isomorphic test modules. -/
private lemma ker_rTensor_le_of_linearEquiv {M N M' Q Q' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Q'] [Module R Q'] (g : M →ₗ[R] M') (f : M →ₗ[R] N) (φ : Q ≃ₗ[R] Q')
    (h : ker (f.rTensor Q') ≤ ker (g.rTensor Q')) :
    ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  intro x hx
  have hfx : f.rTensor Q' ((φ : Q →ₗ[R] Q').lTensor M x) = 0 := by
    rw [rTensor_lTensor_apply, mem_ker.mp hx, map_zero]
  have hgx := mem_ker.mp (h (mem_ker.mpr hfx))
  rw [rTensor_lTensor_apply] at hgx
  exact (map_eq_zero_iff _ (LinearEquiv.lTensor M' φ).injective).mp hgx

/-- **The colimit step.** An element of `M ⊗ Q` killed by `f ⊗ id_Q` comes from an element of
`M ⊗ Q₁`, for a finitely generated submodule `Q₁ ≤ Q`, which is already killed by `f ⊗ id_{Q₁}`:
`M ⊗ Q` is the direct limit of the `M ⊗ Q'` over the finitely generated submodules `Q'` of `Q`, so
both the element and the vanishing of its image are witnessed at a finite stage. -/
private lemma exists_fg_lTensor_subtype_eq_of_rTensor_eq_zero {M N Q : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] (f : M →ₗ[R] N)
    {x : M ⊗[R] Q} (hx : f.rTensor Q x = 0) :
    ∃ (Q₁ : Submodule R Q) (_ : Module.Finite R Q₁) (x₁ : M ⊗[R] Q₁),
      Q₁.subtype.lTensor M x₁ = x ∧ f.rTensor Q₁ x₁ = 0 := by
  obtain ⟨Q₀, hQ₀, hmem⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨x₀, hx₀⟩ := hmem rfl
  -- the obstruction `(f ⊗ id)(x₀)` dies in `N ⊗ Q`, hence in `N ⊗ Q₁` for a larger `Q₁`
  obtain ⟨Q₁, hQ₁, hle, heq⟩ := (Module.Finite.iff_fg.mp hQ₀).exists_rTensor_fg_inclusion_eq
    (M := N) (x := TensorProduct.comm R N Q₀ (f.rTensor Q₀ x₀)) (y := 0)
    (by rw [rTensor_comm, ← rTensor_lTensor_apply, hx₀, hx, map_zero, map_zero])
  rw [map_zero, rTensor_comm] at heq
  refine ⟨Q₁, Module.Finite.iff_fg.mpr hQ₁, (Q₀.inclusion hle).lTensor M x₀, ?_, ?_⟩
  · rw [← lTensor_comp_apply, Submodule.subtype_comp_inclusion, hx₀]
  · rw [rTensor_lTensor_apply, (map_eq_zero_iff _ (TensorProduct.comm R N Q₁).injective).mp heq]

/-- **Finitely many relations suffice.** An element of `N ⊗ P` coming from `N ⊗ L`, for a submodule
`L ≤ P`, already dies in `N ⊗ P/K` for a *finitely generated* `K ≤ L`: only the finitely many
elements of `L` occurring in a representation of the element as a sum of tensors are needed. -/
private lemma exists_fg_le_lTensor_mkQ_eq_zero {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] {L : Submodule R P} (z : N ⊗[R] L) :
    ∃ K ≤ L, K.FG ∧ K.mkQ.lTensor N (L.subtype.lTensor N z) = 0 := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  set K := Submodule.span R ((fun p : N × L ↦ (p.2 : P)) '' S) with hK
  have hmem : ∀ p ∈ S, ((p : N × L).2 : P) ∈ K := fun p hp ↦ by
    rw [hK]; exact Submodule.subset_span ⟨p, hp, rfl⟩
  refine ⟨K, ?_, Submodule.fg_span (S.finite_toSet.image _), ?_⟩
  · rw [hK, Submodule.span_le]
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2
  · rw [← lTensor_comp_apply, hS, map_sum]
    exact Finset.sum_eq_zero fun p hp ↦ by
      simp [(Submodule.Quotient.mk_eq_zero _).mpr (hmem p hp)]

/-- **The presentation step.** An element of `M ⊗ A` killed by `f ⊗ id_A`, for a finitely generated
test module `A`, is the image of an element of `M ⊗ A'` killed by `f ⊗ id_{A'}`, for some finitely
presented `A'` mapping to `A`: a presentation `Rⁿ ↠ A` lifts the element to `M ⊗ Rⁿ`, where right
exactness of the tensor product writes its obstruction as coming from `N ⊗ Ker(Rⁿ → A)`, and
dividing `Rⁿ` by the finitely many relations that obstruction needs leaves a finitely presented
`A'` in which it has died. -/
private lemma exists_finitePresentation_lTensor_eq_of_rTensor_eq_zero {M N A : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup A] [Module R A]
    [Module.Finite R A] (f : M →ₗ[R] N) {x : M ⊗[R] A} (hx : f.rTensor A x = 0) :
    ∃ (A' : Type u) (_ : AddCommGroup A') (_ : Module R A')
      (_ : Module.FinitePresentation R A') (u : A' →ₗ[R] A) (y : M ⊗[R] A'),
      u.lTensor M y = x ∧ f.rTensor A' y = 0 := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R A
  obtain ⟨y, hy⟩ := lTensor_surjective M hπ x
  obtain ⟨z, hz⟩ := (lTensor_exact N (exact_subtype_ker_map π) hπ _).mp
    (show π.lTensor N (f.rTensor (Fin n → R) y) = 0 by rw [← rTensor_lTensor_apply, hy, hx])
  obtain ⟨K, hKle, hKfg, hKzero⟩ := exists_fg_le_lTensor_mkQ_eq_zero (L := ker π) z
  rw [hz] at hKzero
  refine ⟨(Fin n → R) ⧸ K, inferInstance, inferInstance,
    Module.finitePresentation_of_free_of_surjective K.mkQ K.mkQ_surjective
      (by rw [K.ker_mkQ]; exact hKfg),
    K.liftQ π hKle, K.mkQ.lTensor M y, ?_, ?_⟩
  · rw [← lTensor_comp_apply, K.liftQ_mkQ π hKle, hy]
  · rw [rTensor_lTensor_apply, hKzero]

/-- **The descent step.** The containment of kernels holds at every test module, in any universe,
as soon as it holds at every finitely presented test module in the universe of `R`. -/
private lemma ker_rTensor_le_of_forall_finitePresentation_type {M : Type v} {N : Type w}
    {M' : Type w'} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M']
    [Module R M'] (g : M →ₗ[R] M') (f : M →ₗ[R] N)
    (h : ∀ (A : Type u) [AddCommGroup A] [Module R A] [Module.FinitePresentation R A],
      ker (f.rTensor A) ≤ ker (g.rTensor A))
    (Q : Type t) [AddCommGroup Q] [Module R Q] :
    ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  intro x hx
  obtain ⟨Q₁, _, x₁, rfl, hx₁⟩ :=
    exists_fg_lTensor_subtype_eq_of_rTensor_eq_zero f (mem_ker.mp hx)
  obtain ⟨A, _, _, _, u, y, rfl, hy⟩ :=
    exists_finitePresentation_lTensor_eq_of_rTensor_eq_zero f hx₁
  rw [mem_ker, rTensor_lTensor_apply, rTensor_lTensor_apply, mem_ker.mp (h A hy), map_zero,
    map_zero]

/-- **The content of 059C.** If the containment of kernels holds for every finitely presented test
module, it holds for every test module: an element of `Ker(f ⊗ id_Q)` comes from an element of
`Ker(f ⊗ id_{A})` for a finitely presented `A` mapping to `Q`, which the hypothesis places in
`Ker(g ⊗ id_{A})`, and the element is the image of that one. -/
private lemma ker_rTensor_le_of_forall_finitePresentation [Small.{v} R] {M : Type v} {N : Type w}
    {M' : Type w'} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M']
    [Module R M'] (g : M →ₗ[R] M') (f : M →ₗ[R] N)
    (h : ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
      ker (f.rTensor Q) ≤ ker (g.rTensor Q))
    (Q : Type t) [AddCommGroup Q] [Module R Q] :
    ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  refine ker_rTensor_le_of_forall_finitePresentation_type g f (fun A _ _ _ ↦ ?_) Q
  have : Small.{v} A := Module.Finite.small R A
  have : Module.FinitePresentation R (Shrink.{v} A) :=
    Module.FinitePresentation.of_equiv (Shrink.linearEquiv R A).symm
  exact ker_rTensor_le_of_linearEquiv g f (Shrink.linearEquiv R A).symm (h (Shrink.{v} A))

/-- **Domination is not a condition on one universe of test modules.** `LinearMap.Dominates`
confines its test modules to `Type u`, that of the ring, a `Prop` being unable to quantify over
all universes at once; the containment of kernels it asserts there holds at a test module in an
arbitrary universe. The same descent as above: an element of `Ker(f ⊗ id_Q)` comes from an element
of `Ker(f ⊗ id_A)` for a finitely presented `A` mapping to `Q`, and that `A` is produced in the
universe of `R`, so domination applies to it with no smallness hypothesis and no `Shrink` step. -/
public theorem _root_.LinearMap.Dominates.ker_rTensor_le {M : Type v} {N : Type w} {M' : Type w'}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    {g : M →ₗ[R] M'} {f : M →ₗ[R] N} (hdom : g.Dominates f) (Q : Type t) [AddCommGroup Q]
    [Module R Q] :
    ker (f.rTensor Q) ≤ ker (g.rTensor Q) :=
  ker_rTensor_le_of_forall_finitePresentation_type g f (fun A _ _ _ ↦ hdom A) Q

end Helpers

/-- Stacks 059C: `g` dominates `f` if and only if `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` for every
finitely presented `R`-module `Q`. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R] {M : Type v} {N : Type w}
    {M' : Type w'} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M']
    [Module R M'] (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
        LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := by
  refine ⟨fun hdom Q _ _ _ ↦ ?_, fun h Q _ _ ↦ ?_⟩
  · -- A finitely presented test module `Q : Type v` is `u`-small, so `Shrink.{u} Q` is a test
    -- module in the universe `LinearMap.Dominates` quantifies over.
    have : Small.{u} Q := Module.Finite.small.{u} R Q
    exact ker_rTensor_le_of_linearEquiv g f (Shrink.linearEquiv R Q).symm (hdom (Shrink.{u} Q))
  · let _ : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R
    exact ker_rTensor_le_of_forall_finitePresentation g f h Q

end Stacks.Modules.Domination

/-!
# Domination of maps of modules is tested on finitely presented modules

Let `f : M → N` and `g : M → M'` be maps of `R`-modules with common source. Then `g` *dominates*
`f` if `Ker(f ⊗_R id_Q) ⊆ Ker(g ⊗_R id_Q)` for every `R`-module `Q` (Definition 059B,
`LinearMap.Dominates`). The condition is a quantifier over all test modules `Q`, but only the
finitely presented ones carry information: every `R`-module is the filtered colimit of a directed
system of finitely presented modules, tensoring commutes with filtered colimits and filtered
colimits of modules are exact, so the kernel of `f ⊗ id_Q` is the colimit of the kernels of the
`f ⊗ id_{Q_i}` and a containment holding at every stage holds in the colimit. This file records
that reduction.

It is what makes domination a usable condition: the finitely presented test modules form a set,
and each of them is a cokernel `R^n / Im(R^m → R^n)`, so the condition becomes a statement about
finitely many elements of `M` at a time. Its two standard uses are the equivalence of domination
with a factorization when `Coker(f)` is of finite presentation (Lemma 059D) and the Mittag-Leffler
condition on a module, where mutual domination is tested on finitely presented modules by
construction (Proposition 059E, Definition 059F).

## Main results

* `LinearMap.dominates_iff_forall_finitePresentation`: `g` dominates `f` if and only if
  `Ker(f ⊗ id_Q) ⊆ Ker(g ⊗ id_Q)` for every finitely presented `R`-module `Q`.

## Implementation notes

`f ⊗_R id_Q` is `f.rTensor Q`, and the source's containment of kernels is the containment
`ker (f.rTensor Q) ≤ ker (g.rTensor Q)` of submodules of `M ⊗_R Q`; finite presentation of the
test module is the typeclass hypothesis `Module.FinitePresentation R Q`. The left-hand side is the
project's named predicate `LinearMap.Dominates` rather than its unfolding, so that this lemma
rewrites the notion the source defines.

The finitely presented test modules `Q` of the right-hand side range over `Type v`, the universe of
the common source `M`, whereas `LinearMap.Dominates` quantifies its test modules over `Type u`, the
universe of the ring, a `Prop` being unable to quantify over all universes at once. The two are
compared by `Shrink`, which is available in both directions: a finitely presented module is
`u`-small because it is a quotient of some `Rⁿ`, and it is `v`-small under `Small.{v} R`. Under
`Small.{v} R` confining `Q` to `Type v` is therefore no restriction, since every
finitely presented `R`-module is a quotient of some `Rⁿ` and hence `v`-small, and an isomorphism
of test modules carries the kernel containment for one to the kernel containment for the other.
Smallness is automatic in the usual case where `R` and `M` lie in the same universe. The targets
`N` and `M'` are in their own universes, unconstrained, because the two submodules being compared
live in `M ⊗_R Q` and the targets never interact.

`LinearMap.Dominates` quantifies its test modules as additive commutative monoids, whereas the
finitely presented test modules here are quantified as additive commutative groups. Over the
source's commutative ring `R` these are the same test modules: an `R`-module which is an additive
commutative monoid is an additive commutative group, by `Module.addCommMonoidToAddCommGroup`,
since `(-1) • x` is an additive inverse of `x`.

Faithfulness. (1) No hypothesis is decoration: both maps occur in the conclusion, `f` through the
kernel contained and `g` through the kernel containing it, and `Small.{v} R`, while it does not
appear in the conclusion, is what the equivalence is false without — it makes the right-hand
quantifier the source's "for any finitely presented `R`-module `Q`", since without it the
finitely presented modules in `Type v` need not include the cokernels of maps `Rᵐ → Rⁿ` that the
colimit presentation of a test module produces, and the right-hand side stops controlling the
left. (2) The scalars and the base are the source's: `f` and `g` are `R`-linear for the single
base ring `R`, both tensor products are `⊗[R]` over that same `R`, and neither the maps nor the
test module is localized or base changed; `R` is the source's commutative ring and the modules are
abelian groups. (3) The maps whose kernels are compared are pinned, not merely asserted to exist:
they are `f.rTensor Q` and `g.rTensor Q`, the source's `f ⊗_R id_Q` and `g ⊗_R id_Q`, and not
arbitrary maps `M ⊗ Q → N ⊗ Q` and `M ⊗ Q → M' ⊗ Q`. (4) The instantiation is not degenerate:
both sides hold for `R = ℤ` and `f = g = id_ℤ`, since `Ker(id ⊗ id_Q) = 0`, so neither side is
vacuously false; and both fail for `R = ℤ`, `M = N = M' = ℤ`, `f` multiplication by `2` and
`g = id`, the left at the test module `Q = ℤ/2ℤ`, where `f ⊗ id_Q = 0` while `g ⊗ id_Q = id` on
`ℤ ⊗ ℤ/2ℤ ≅ ℤ/2ℤ ≠ 0`, and the right at the same `Q`, which is finitely presented — so neither
side is vacuously true, and the equivalence has content in both directions.

## References

* [StacksProject 059C](https://stacks.math.columbia.edu/tag/059C)
-/



@[expose] public section

/-- **Stacks 059C.** Let `f : M → N` and `g : M → M'` be maps of `R`-modules. Then `g` dominates
`f`, that is `Ker(f ⊗_R id_Q) ⊆ Ker(g ⊗_R id_Q)` for every `R`-module `Q`, if and only if
`Ker(f ⊗_R id_Q) ⊆ Ker(g ⊗_R id_Q)` for every finitely presented `R`-module `Q`. -/
@[stacks 059C "Domination is the project's `LinearMap.Dominates`; the containment of kernels is
  the containment of the kernels of the maps tensored with the identity of the test module."]
public theorem LinearMap.dominates_iff_forall_finitePresentation {R : Type u} [CommRing R]
    [Small.{v} R] {M : Type v} {N : Type w} {M' : Type w'} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] (g : M →ₗ[R] M')
    (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q],
        LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) :=
          by apply Stacks.Modules.Domination.solution

end

end
end

/-!
# Domination and the pushout of a span of module maps

Throughout, `R` is a fixed commutative ring and all modules are `R`-modules. For
an `R`-linear map `h : A → B` and an `R`-module `Q`, the induced map on tensor
products `h ⊗ id_Q : A ⊗[R] Q → B ⊗[R] Q` is `LinearMap.rTensor Q h`.

Given `R`-linear maps `f : M → N` and `g : M → M'`, the pushout of the span
`M' ←g— M —f→ N` is the `R`-module `N' = (M' × N) / K`, where
`K = { (g x, -f x) : x ∈ M }`, together with the maps
`f' : M' → N', m' ↦ ⟨(m', 0)⟩` and `g' : N → N', n ↦ ⟨(0, n)⟩`. These satisfy
`f' ∘ g = g' ∘ f`, and `(N', f', g')` is the categorical pushout.

Stacks Lemma 10.88.4 says that, for this pushout square, `g` dominates `f` — that
is, `Ker (f ⊗ id_Q) ⊆ Ker (g ⊗ id_Q)` inside `M ⊗[R] Q` for every `R`-module `Q` —
if and only if `f'` is universally injective, meaning `f' ⊗ id_Q` is injective for
every `Q`. The two input notions are `UniversallyInjective` (Stacks Definition
10.82.1) and `Dominates` (Stacks Definition 10.88.2).

## Main definitions

* `pushoutRel`: the submodule `K ⊆ M' × N`.
* `moduleMapPushout`: the pushout module `N'`.
* `pushoutInl`, `pushoutInr`: the two structural maps `f'` and `g'`.

## Main results

* `pushout_comm`: the pushout square commutes.
* `dominates_iff_pushoutInl_universallyInjective`: the lemma above.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

/-- The submodule `K = { (g x, -f x) : x ∈ M } ⊆ M' × N` defining the pushout. -/
@[ega "0 18.2.7" "special case"]
def pushoutRel {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') : Submodule R (M' × N) :=
  LinearMap.range (g.prod (-f))

/-- The pushout module `N' = (M' × N) / K`, formed from a span of module maps
`M' ←g— M —f→ N`. -/
@[ega "0 18.2.7" "special case", ega "0 18.2.8" "partial"]
abbrev moduleMapPushout {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') : Type u :=
  (M' × N) ⧸ pushoutRel f g

/-- The pushout map `f' : M' → N', m' ↦ ⟨(m', 0)⟩`. -/
@[ega "0 18.2.7" "canonical map j₁"]
def pushoutInl {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') : M' →ₗ[R] moduleMapPushout f g :=
  (pushoutRel f g).mkQ ∘ₗ LinearMap.inl R M' N

/-- The pushout map `g' : N → N', n ↦ ⟨(0, n)⟩`. -/
@[ega "0 18.2.7" "canonical map j₂"]
def pushoutInr {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') : N →ₗ[R] moduleMapPushout f g :=
  (pushoutRel f g).mkQ ∘ₗ LinearMap.inr R M' N

/-- The pushout square commutes: `f' ∘ g = g' ∘ f`. -/
theorem pushout_comm {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    (pushoutInl f g) ∘ₗ g = (pushoutInr f g) ∘ₗ f := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, pushoutInl, pushoutInr,
    LinearMap.inl_apply, LinearMap.inr_apply]
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, by simp⟩

/-- An element of `(M' × N) ⊗[R] Q` is determined by its two projections. -/
theorem rTensor_prod_ext {M' N Q : Type u} [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    {x y : TensorProduct R (M' × N) Q}
    (hfst : (LinearMap.fst R M' N).rTensor Q x = (LinearMap.fst R M' N).rTensor Q y)
    (hsnd : (LinearMap.snd R M' N).rTensor Q x = (LinearMap.snd R M' N).rTensor Q y) :
    x = y := by
  have hid : ((LinearMap.inl R M' N).rTensor Q).comp ((LinearMap.fst R M' N).rTensor Q)
      + ((LinearMap.inr R M' N).rTensor Q).comp ((LinearMap.snd R M' N).rTensor Q)
      = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add,
      ← LinearMap.rTensor_id Q (M' × N)]
    congr 1
    ext z <;> simp
  have hdec : ∀ w : TensorProduct R (M' × N) Q, w
      = (LinearMap.inl R M' N).rTensor Q ((LinearMap.fst R M' N).rTensor Q w)
      + (LinearMap.inr R M' N).rTensor Q ((LinearMap.snd R M' N).rTensor Q w) := fun w ↦ by
    simpa using (LinearMap.congr_fun hid w).symm
  rw [hdec x, hdec y, hfst, hsnd]

/-- Tensoring the exact sequence `M → M' × N → N'` defining the pushout with `Q` keeps
it exact. -/
theorem rTensor_pushoutRel_exact {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Exact ((g.prod (-f)).rTensor Q) ((pushoutRel f g).mkQ.rTensor Q) :=
  rTensor_exact Q (by rw [LinearMap.exact_iff, Submodule.ker_mkQ]; rfl)
    (pushoutRel f g).mkQ_surjective

/-- If `g` dominates `f`, then the pushout map `f'` is universally injective. -/
theorem pushoutInl_universallyInjective_of_dominates
    {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    {f : M →ₗ[R] N} {g : M →ₗ[R] M'} (hdom : Dominates.{u, u, u, u, u} f g) :
    UniversallyInjective (pushoutInl f g) := by
  intro Q _ _
  rw [injective_iff_map_eq_zero]
  intro u hu
  rw [pushoutInl, LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply] at hu
  obtain ⟨z, hz⟩ := (rTensor_pushoutRel_exact f g Q _).mp hu
  have hg : g.rTensor Q z = u := by
    have h1 := congrArg ((LinearMap.fst R M' N).rTensor Q) hz
    simpa only [← LinearMap.rTensor_comp_apply, LinearMap.fst_prod, LinearMap.fst_comp_inl,
      LinearMap.rTensor_id, LinearMap.id_coe, id_eq] using h1
  have hf : f.rTensor Q z = 0 := by
    have h1 := congrArg ((LinearMap.snd R M' N).rTensor Q) hz
    simpa only [← LinearMap.rTensor_comp_apply, LinearMap.snd_prod, LinearMap.snd_comp_inl,
      LinearMap.rTensor_zero, LinearMap.zero_apply, LinearMap.rTensor_neg,
      LinearMap.neg_apply, neg_eq_zero] using h1
  rw [← hg]
  exact hdom Q hf

/-- If the pushout map `f'` is universally injective, then `g` dominates `f`. -/
theorem dominates_of_pushoutInl_universallyInjective
    {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    {f : M →ₗ[R] N} {g : M →ₗ[R] M'} (huniv : UniversallyInjective (pushoutInl f g)) :
    Dominates.{u, u, u, u, u} f g := by
  intro Q _ _ z hzker
  rw [LinearMap.mem_ker] at hzker ⊢
  have hz : f.rTensor Q z = 0 := hzker
  change g.rTensor Q z = 0
  have hkey : (LinearMap.inl R M' N).rTensor Q (g.rTensor Q z) = (g.prod (-f)).rTensor Q z := by
    apply rTensor_prod_ext (R := R) (Q := Q)
    · simp only [← LinearMap.rTensor_comp_apply, ← LinearMap.comp_assoc,
        LinearMap.fst_comp_inl, LinearMap.fst_prod, LinearMap.id_comp]
    · simp only [← LinearMap.rTensor_comp_apply, ← LinearMap.comp_assoc,
        LinearMap.snd_comp_inl, LinearMap.snd_prod, LinearMap.zero_comp,
        LinearMap.rTensor_zero, LinearMap.zero_apply, LinearMap.rTensor_neg,
        LinearMap.neg_apply, hz, neg_zero]
  have h0 := (rTensor_pushoutRel_exact f g Q _).mpr ⟨z, hkey.symm⟩
  refine (injective_iff_map_eq_zero _).mp (huniv Q) _ ?_
  rw [pushoutInl, LinearMap.rTensor_comp]
  simpa using h0

/-- Let `f : M → N` and `g : M → M'` be maps of `R`-modules, and form the pushout
square `f' : M' → N'`, `g' : N → N'`. Then `g` dominates `f` if and only if `f'`
is universally injective. -/
@[stacks 0AUM]
theorem dominates_iff_pushoutInl_universallyInjective
    {M N M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    Dominates.{u, u, u, u, u} f g ↔ UniversallyInjective (pushoutInl f g) :=
  ⟨pushoutInl_universallyInjective_of_dominates, dominates_of_pushoutInl_universallyInjective⟩

end
