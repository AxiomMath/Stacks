module

public import StacksFrontier.RingTheory.Module.Dominates
public import StacksFrontier.Algebra.MittagLeffler.Criteria
public import StacksFrontier.RingTheory.Module.FinitePresentation.TensorProductPi
public import StacksFrontier.RingTheory.Module.FinitePresentation.Factorization

@[expose] public section

universe u v w t

/-!
# Mittag-Leffler modules as those for which tensor interchanges with direct products

Let `R` be a commutative ring and `M` an `R`-module. This file proves Stacks 059M: `M` is
Mittag-Leffler — every map `f : P → M` from a finitely presented module dominates and is dominated
by a map `g : P → Q` into a finitely presented module, which is condition (1) of Proposition 059E
— if and only if for every family `(Q α)` of `R`-modules the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective.

Both directions rest on Proposition 059K, that the comparison map is bijective for a finitely
presented module, and on the naturality of the comparison map in its left factor.

For the first direction, an element `x` of the kernel is written as the image of an element `y` of
`P ⊗[R] (∀ α, Q α)` for a finite free `P` mapping to `M` by `f`, `x` being a finite sum of pure
tensors. Mittag-Leffler gives a `g : P → Q'` into a finitely presented module with
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `N`. Componentwise, the `α`-th component of `y` lies in
`Ker(f ⊗ id_{Q α})`, hence in `Ker(g ⊗ id_{Q α})`; so `g ⊗ id` kills `y` after the comparison map
of `Q'`, which is injective by 059K, whence `y ∈ Ker(g ⊗ id) = Ker(f ⊗ id)` and `x = 0`.

For the converse, given `f : P → M` with `P` finitely presented, the family of test modules is
indexed by all triples `(n, m, c)` presenting a finitely presented module together with an element
of `Ker(f ⊗ id)` for it. The elements assemble to a single element of `P ⊗[R] (∀ α, Q α)`, the
comparison map of `P` being surjective by 059K, that element is killed in `M ⊗[R] (∀ α, Q α)` by
the assumed injectivity, and Lemma 059L produces a finitely presented `P'` with `f = g ∘ f'`
killing it; naturality reads the conclusion off componentwise. So
`Ker(f ⊗ id_Q) ⊆ Ker(f' ⊗ id_Q)` for every finitely presented `Q`, which is domination by Lemma
059C, and `f = g ∘ f'` gives the reverse containment for every `Q`.

## Main results

* `Stacks.MittagLeffler.TensorProductPi.solution`: Stacks 059M, the statement of
  `Module.mittagLeffler_iff_piRightHom_injective`.

## Implementation notes

The source takes for the index set a set of representatives of the isomorphism classes of finitely
presented `R`-modules. What the argument needs is only that every finitely presented module in
`Type v` be isomorphic to a member of the family, so no choice of representatives is made here:
the family runs over the *standard* presented modules `Shrink (Fin n → R) ⧸ span (range c)` for
`c : Fin m → Shrink (Fin n → R)`, one for each triple `(n, m, c)`, and these form a type in
`Type v` because `R` is `v`-small. Members of the family isomorphic to one another, and members
that are not needed, are harmless: injectivity is assumed for every family.

Two steps of the argument are facts about tensor products that Mathlib does not record and that
are proved here as private lemmas. `piRightHom_rTensor` is the naturality of the comparison map in
its left factor, and `exists_finitePresentation_rTensor_eq` is the statement that every element of
`M ⊗[R] N` comes from `P ⊗[R] N` for some finitely presented `P` over `M`, which is the "write `M`
as a colimit of finitely presented modules and descend `x` to a stage" step of the source's proof
in the only form it is used.

The main content of the converse is factored out as `exists_factorization_forall_rTensor_eq_zero`,
stated for an abstract family, so that the concrete family of standard presented modules is
elaborated once and the assembly argument is carried out in the abstract.

## References

* [StacksProject 059M](https://stacks.math.columbia.edu/tag/059M)
-/



namespace Stacks.MittagLeffler.TensorProductPi

open TensorProduct

variable {R : Type u} [CommRing R]

/-- Naturality of the comparison map `M ⊗ ∏ Q α → ∏ (M ⊗ Q α)` in the left tensor factor. -/
private lemma piRightHom_rTensor {M : Type v} {M' : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] {A : Type t} (Q : A → Type*)
    [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)] (f : M →ₗ[R] M')
    (x : M ⊗[R] (∀ α, Q α)) (α : A) :
    TensorProduct.piRightHom R R M' Q (f.rTensor _ x) α
      = f.rTensor (Q α) (TensorProduct.piRightHom R R M Q x α) := by
  induction x using TensorProduct.inductionOn with
  | tmul m q => simp
  | add x y hx hy => simp [hx, hy]

/-- The comparison map of `M'` kills `f.rTensor X` iff `f ⊗ id` kills each component of the
comparison map of `M` at `X`. -/
private lemma piRightHom_rTensor_eq_zero_iff {M : Type v} {M' : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] {A : Type t} (Q : A → Type*)
    [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)] (f : M →ₗ[R] M') (X : M ⊗[R] (∀ α, Q α)) :
    TensorProduct.piRightHom R R M' Q (f.rTensor _ X) = 0 ↔
      ∀ α, f.rTensor (Q α) (TensorProduct.piRightHom R R M Q X α) = 0 := by
  simp [funext_iff, piRightHom_rTensor]

/-- Tensoring with a map on the left and with a map on the right commute. -/
private lemma rTensor_lTensor_apply {M M' N N' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N] [AddCommGroup N']
    [Module R N'] (f : M →ₗ[R] M') (e : N →ₗ[R] N') (z : M ⊗[R] N) :
    f.rTensor N' (LinearMap.lTensor M e z) = LinearMap.lTensor M' e (f.rTensor N z) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor]

/-- Every element of `M ⊗[R] N` is the image of an element of `P ⊗[R] N` for some finitely
presented `R`-module `P` mapping to `M`: it is a finite sum of pure tensors, and a finite free
module on its left-hand factors will do. -/
private lemma exists_finitePresentation_rTensor_eq [Small.{v} R] {M : Type v} [AddCommGroup M]
    [Module R M] {N : Type w} [AddCommGroup N] [Module R N] (x : M ⊗[R] N) :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.FinitePresentation R P)
      (g : P →ₗ[R] M) (y : P ⊗[R] N), g.rTensor N y = x := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  set n := S.card
  set p : Fin n → M × N := fun i => (S.equivFin.symm i : M × N)
  set e := Shrink.linearEquiv R (Fin n → R)
  refine ⟨Shrink.{v} (Fin n → R), inferInstance, inferInstance,
    e.finitePresentation_iff.mpr inferInstance,
    Fintype.linearCombination R (fun i => (p i).1) ∘ₗ e.toLinearMap,
    ∑ i, e.symm (Pi.single i 1) ⊗ₜ[R] (p i).2, ?_⟩
  rw [hS]
  simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Fintype.linearCombination_apply_single,
    one_smul]
  rw [← Finset.sum_coe_sort S (fun q => (q.1 : M) ⊗ₜ[R] (q.2 : N))]
  exact Fintype.sum_equiv S.equivFin.symm _ _ fun i => rfl

/-- Stacks 059K in the form in which the argument uses it: for a finitely presented module the
comparison map `P ⊗ ∏ Q α → ∏ (P ⊗ Q α)` is bijective. -/
private lemma piRightHom_bijective (R : Type u) [CommRing R] [Small.{v} R] (P : Type v)
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P] (A : Type v) (Q : A → Type v)
    [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)] :
    Function.Bijective (TensorProduct.piRightHom R R P Q) := by
  have h : Module.FinitePresentation R P ↔
      ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
        Function.Bijective (TensorProduct.piRightHom R R P Q) :=
    (Module.FinitePresentation.tfae_piRightHom_bijective R P).out 1 2
  exact h.mp inferInstance A Q

/-- The standard finitely presented `R`-module in the universe `v` with `n` generators and the
`m` relations `c`: a quotient of the `v`-small copy `Shrink (Fin n → R)` of `Rⁿ`. -/
private abbrev stdFP (R : Type u) [CommRing R] [Small.{v} R] {n m : ℕ}
    (c : Fin m → Shrink.{v} (Fin n → R)) : Type v :=
  Shrink.{v} (Fin n → R) ⧸ Submodule.span R (Set.range c)

/-- Every finitely presented `R`-module in the universe `v` is one of the standard ones. -/
private lemma exists_linearEquiv_stdFP (R : Type u) [CommRing R] [Small.{v} R] (Q : Type v)
    [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q] :
    ∃ (n m : ℕ) (c : Fin m → Shrink.{v} (Fin n → R)), Nonempty (Q ≃ₗ[R] stdFP R c) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R Q
  set ε := (Shrink.linearEquiv.{v} R (Fin n → R)).symm
  obtain ⟨m, c, hc⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hK.map (ε : (Fin n → R) →ₗ[R] Shrink.{v} (Fin n → R)))
  exact ⟨n, m, c, ⟨e.trans (Submodule.Quotient.equiv K _ ε hc.symm)⟩⟩

/-- The index type of the test family used in the proof that (2) implies (1): all pairs `(Q, x)`
with `Q` a standard finitely presented module and `x ∈ Ker(f ⊗ id_Q)`. -/
private abbrev relIndex {P M : Type v} [Small.{v} R] [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] (f : P →ₗ[R] M) : Type v :=
  Σ (n m : ℕ) (c : Fin m → Shrink.{v} (Fin n → R)),
    ↥(LinearMap.ker (f.rTensor (stdFP R c)))

/-- The heart of the implication (2) ⟹ (1). Let `f : P → M` be a map from a finitely presented
module, let `(Q α)` be a family for which the comparison map of `M` is injective, and let
`(x α)` be a family of elements `x α ∈ Ker(f ⊗ id_{Q α})`. Then `f` factors through a finitely
presented module which kills every `x α`: the `x α` assemble to a single element of
`P ⊗ ∏ Q α`, the comparison map of `P` being bijective, that element dies in `M ⊗ ∏ Q α` by
injectivity, and Lemma 059L kills it at a finitely presented stage. -/
private lemma exists_factorization_forall_rTensor_eq_zero [Small.{v} R] {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P] [AddCommGroup M] [Module R M]
    {A : Type v} (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)]
    (hinj : Function.Injective (TensorProduct.piRightHom R R M Q)) (f : P →ₗ[R] M)
    (x : ∀ α, P ⊗[R] Q α) (hx : ∀ α, f.rTensor (Q α) (x α) = 0) :
    ∃ (P' : Type v) (_ : AddCommGroup P') (_ : Module R P')
      (_ : Module.FinitePresentation R P') (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
      f = g ∘ₗ f' ∧ ∀ α, f'.rTensor (Q α) (x α) = 0 := by
  obtain ⟨X, hX⟩ := (piRightHom_bijective R P A Q).surjective x
  have hMX : f.rTensor (∀ α, Q α) X = 0 := by
    refine hinj ?_
    rw [map_zero, piRightHom_rTensor_eq_zero_iff, hX]
    exact hx
  obtain ⟨P', _, _, _, f', g, hfg, hX'⟩ :=
    LinearMap.exists_finitePresentation_factorization_of_rTensor_apply_eq_zero f hMX
  refine ⟨P', inferInstance, inferInstance, inferInstance, f', g, hfg, fun α => ?_⟩
  have h0 := (piRightHom_rTensor_eq_zero_iff Q f' X).mp (by simp [hX'])
  rw [hX] at h0
  exact h0 α

/-- Stacks 059M: every map `f : P → M` from a finitely presented module has the same kernels after
`· ⊗ id_N`, for every `N`, as some map `g : P → Q` into a finitely presented module if and only if
the comparison map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective for every family `(Q α)`. -/
public theorem solution (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M]
    [Module R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
        Function.Injective (TensorProduct.piRightHom R R M Q) := by
  constructor
  · intro H A Q _ _
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨P, _, _, _, g, y, rfl⟩ := exists_finitePresentation_rTensor_eq x
    obtain ⟨Q', _, _, _, h, hker⟩ := H P g
    have h0 : TensorProduct.piRightHom R R Q' Q (h.rTensor _ y) = 0 := by
      rw [piRightHom_rTensor_eq_zero_iff]
      intro α
      rw [← LinearMap.mem_ker, ← hker (Q α), LinearMap.mem_ker]
      exact (piRightHom_rTensor_eq_zero_iff Q g y).mp hx α
    have hy : y ∈ LinearMap.ker (h.rTensor (∀ α, Q α)) :=
      LinearMap.mem_ker.mpr ((piRightHom_bijective R Q' A Q).injective (by rw [h0, map_zero]))
    rwa [← hker (∀ α, Q α), LinearMap.mem_ker] at hy
  · intro H P _ _ _ f
    obtain ⟨P', _, _, _, f', g, hfg, key⟩ :=
      exists_factorization_forall_rTensor_eq_zero (fun α : relIndex f => stdFP R α.2.2.1)
        (H (relIndex f) _) f (fun α => (α.2.2.2 : P ⊗[R] stdFP R α.2.2.1)) fun α => α.2.2.2.2
    have hdom : f'.Dominates f := by
      rw [LinearMap.dominates_iff_forall_finitePresentation]
      intro Q _ _ _ z hz
      obtain ⟨n, m, c, ⟨e⟩⟩ := exists_linearEquiv_stdFP R Q
      have hz' : LinearMap.lTensor P (e : Q →ₗ[R] stdFP R c) z
          ∈ LinearMap.ker (f.rTensor (stdFP R c)) := by
        rw [LinearMap.mem_ker, rTensor_lTensor_apply, LinearMap.mem_ker.mp hz, map_zero]
      have h2 : LinearMap.lTensor P' (e : Q →ₗ[R] stdFP R c) (f'.rTensor Q z) = 0 := by
        rw [← rTensor_lTensor_apply]
        exact key ⟨n, m, c, ⟨_, hz'⟩⟩
      have hinj : Function.Injective (LinearMap.lTensor P' (e : Q →ₗ[R] stdFP R c)) :=
        (LinearEquiv.lTensor P' e).injective
      exact LinearMap.mem_ker.mpr (hinj (by simpa using h2))
    -- `f'.Dominates f` quantifies its test modules over `Type u`, that of `R`, while the test
    -- module `N` here lives in `Type v`; `ker_rTensor_le` is domination at a test module in any
    -- universe.
    refine ⟨P', inferInstance, inferInstance, inferInstance, f', fun N _ _ => le_antisymm
      (hdom.ker_rTensor_le N) fun z hz => ?_⟩
    rw [LinearMap.mem_ker, hfg, LinearMap.rTensor_comp, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hz, map_zero]

end Stacks.MittagLeffler.TensorProductPi

/-!
# Mittag-Leffler modules as those for which tensor interchanges with direct products

Let `R` be a commutative ring, let `M` be an `R`-module and let `(Q α)` be a family of `R`-modules
indexed by a set `A`. The canonical map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α`, given on pure
tensors by `x ⊗ (q α) ↦ (x ⊗ q α)`, is surjective for all families exactly when `M` is finitely
generated (Proposition 059J) and bijective for all families exactly when `M` is finitely presented
(Proposition 059K). This file states the remaining case, and it is the reason the section exists:
the map is injective for all families exactly when `M` is Mittag-Leffler.

Suppose `M` is Mittag-Leffler and write it as a directed colimit `M = colim M i` of finitely
presented modules. An element of the kernel comes from some `M i ⊗[R] (∀ α, Q α)`, and it suffices
to kill it in `M j ⊗[R] (∀ α, Q α)` for some `j ≥ i`; choosing `j` so that `M i → M j` and
`M i → M` dominate each other, the two comparison maps at the finitely presented stages `i` and `j`
are isomorphisms by 059K, and domination says that the kernels of
`∏ (M i ⊗ Q α) → ∏ (M j ⊗ Q α)` and of `∏ (M i ⊗ Q α) → ∏ (M ⊗ Q α)` agree.
Conversely, given a map `f : P → M` out of a finitely presented module, apply injectivity to the
family indexed by all pairs `(Q, x)` with `Q` a finitely presented module and `x` an element of
`Ker(P ⊗ Q → M ⊗ Q)`: the element of `P ⊗[R] (∀ α, Q α)` assembled from the `x α` — the assembly
is possible because the comparison map for the finitely presented `P` is an isomorphism, again by
059K — is killed in `M ⊗[R] (∀ α, Q α)`, so by Lemma 059L the map `f` factors through a finitely
presented `P'` killing it, and unwinding gives
`Ker(P ⊗ Q → M ⊗ Q) ⊆ Ker(P ⊗ Q → P' ⊗ Q)` for every finitely presented `Q`, whence `f` and the
map `P → P'` dominate each other.

## Main results

* `Module.mittagLeffler_iff_piRightHom_injective`: an `R`-module `M` is Mittag-Leffler if and only
  if `TensorProduct.piRightHom` is injective for every family of `R`-modules.

## Implementation notes

Being Mittag-Leffler (Definition 059F) is defined by reference to the equivalent conditions of
Proposition 059E, which are conditions on a directed system of finitely presented modules with
colimit `M`. Only condition (1) of those is intrinsic to `M`, and it is the one written out here:
every map `f : P → M` from a finitely presented module dominates and is dominated by a map
`g : P → Q` into a finitely presented module, domination meaning that `f` and `g` have the same
kernel after applying `· ⊗ id_N` for every `R`-module `N`. Mathlib's Mittag-Leffler condition,
`CategoryTheory.Functor.IsMittagLeffler`, is the condition on an inverse system, that is condition
(4) of 059E for the system of duals, so it does not apply to `M` on its own; this is the same
inline spelling as in Lemma 05CQ, and it is the form Proposition 059E makes available.

The canonical map the source names is pinned to Mathlib's `TensorProduct.piRightHom R R M Q`, whose
value on `x ⊗ q` is `fun α ↦ x ⊗ q α`, so the statement asserts injectivity of that map and not the
existence of some injection; it is the same map as in 059J and 059K, and the assertion here is the
one word by which those two propositions differ from this one.

Unlike 059J and 059K, no weakening of the test family is stated, because the source states none:
the converse direction needs a family whose members run through all the finitely presented modules,
so the test family cannot be taken constant, and it is with the family of all such modules that
injectivity is applied.

The index types and the test modules range over `Type v`, the universe of `M`, as in 059J and
059K, and so do the finitely presented modules `P`, `Q` and the test module `N` of the
Mittag-Leffler condition, as in 059D, 059E and 05CQ. This is what `Small.{v} R` buys, and the
hypothesis is not decoration: it is needed to apply 059K, which carries it, and in the converse
direction it is what puts the finitely presented module produced by 059L, and the index set of
pairs `(Q, x)`, in `Type v`. It is automatic when `R` itself lives in `Type v`, by `small_self`.
A family of modules in a larger universe is reached by applying the statement to a `ULift` copy
of `M`.

Faithfulness. (1) No hypothesis is idle: the data are `R` and `M`, both used by each side, nothing
is assumed of `M`, and `Small.{v} R` is used as described above; the test data of both sides are
quantified inside them. (2) The scalars and the base are the source's: one commutative ring `R`
throughout, every tensor product is `⊗[R]`, every map is `R`-linear, and Mittag-Leffler is over
`R`; nothing is localized or base changed. (3) The canonical map is pinned to
`TensorProduct.piRightHom R R M Q`, and the maps of the Mittag-Leffler condition are pinned to
`LinearMap.rTensor N f` and `LinearMap.rTensor N g` with their kernels compared by equality.
(4) The instantiation is not degenerate and neither side is vacuous: for `R = ℤ` and `M = ℤ ⧸ 2ℤ`
both sides hold, being finitely presented, and for `R = ℤ` and `M = ℚ` both fail, the family
`Q n = ℤ ⧸ nℤ` of the source's Example 059I having `∏ n, (ℚ ⊗ Q n) = 0` while
`ℚ ⊗[ℤ] (∀ n, Q n) ≠ 0`. The statement is strictly weaker than 059K, hence not a restatement of
it: for `R = ℤ` and `M = ⨁ (_ : ℕ), ℤ` both sides hold, `M` being free, while `M` is not finitely
presented and the comparison map is not surjective.

## References

* [StacksProject 059M](https://stacks.math.columbia.edu/tag/059M)
-/



@[expose] public section

/-- **Stacks 059M.** Let `R` be a commutative ring and `M` an `R`-module. Then `M` is
Mittag-Leffler — every map `f : P → M` from a finitely presented `R`-module dominates and is
dominated by a map `g : P → Q` into a finitely presented `R`-module, that is
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`, which is condition (1) of
Proposition 059E — if and only if for every family `(Q α)` of `R`-modules the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective. -/
@[stacks 059M "Mittag-Leffler is spelled out inline as condition (1) of 059E; test data in the
universe of `M`, as in 059J and 059K, whence `Small.{v} R`. See the module docstring."]
public theorem Module.mittagLeffler_iff_piRightHom_injective (R : Type u) [CommRing R]
    [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (A : Type v) (Q : A → Type v) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
        Function.Injective (TensorProduct.piRightHom R R M Q) :=
  Stacks.MittagLeffler.TensorProductPi.solution R M

end
