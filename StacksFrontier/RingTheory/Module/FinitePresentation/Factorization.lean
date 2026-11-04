module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
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

universe u v w t

/-!
# Factoring a map through a finitely presented module after tensoring

Let `R` be a commutative ring, `P` a finitely presented `R`-module, `f : P → M` a map of
`R`-modules and `Q` an `R`-module, and let `x` be an element of `P ⊗ Q` killed by `f ⊗ id_Q`.
This file proves Stacks 059L: `f` factors as `P → P' → M` through a finitely presented
`R`-module `P'` in which `x` is killed already, that is with `x` in the kernel of
`P ⊗ Q → P' ⊗ Q`.

The source writes `M` as a directed colimit of finitely presented modules, factors `f` through a
finite stage `M_j` because `P` is finitely presented, and kills the image of `x` at a further
stage because `M ⊗ Q = colim (M_i ⊗ Q)`. The route taken here is the same argument with a
colimit presentation chosen once and for all, and in two stages. First the target is shrunk: `M`
is the directed union of its finitely generated submodules, so `M ⊗ Q` is the colimit of the
`M_i ⊗ Q`, and the element of `range f ⊗ Q` that `x` gives rise to already vanishes in `M₂ ⊗ Q`
for some finitely generated `M₂ ⊇ range f`. Then the target is presented: a finitely generated
module is a quotient `R^k / K`, the map `P → M₂` lifts along `R^k ↠ M₂` after choosing a
presentation `R^n ↠ P` of `P` (its source is free, hence projective), and `x` lifts to
`R^n ⊗ Q`. The relations of `P` and a witness for the vanishing of the lift of `x` in
`M₂ ⊗ Q` together involve only finitely many elements of `K`, so they lie in a finitely
generated `K₁ ≤ K`, and `P' = R^k / K₁` is finitely presented and does both jobs.

## Main results

* `Stacks.FinitePresentation.Factorization.solution`: Stacks 059L, the statement of
  `LinearMap.exists_finitePresentation_factorization_of_rTensor_apply_eq_zero`.

## Implementation notes

Two steps of the argument are general facts about tensor products that Mathlib does not record,
and are proved here as private lemmas. `exists_fg_ge_of_rTensor_subtype_eq_zero` is the colimit
statement in the form it is used: an element of `M₁ ⊗ Q`, for `M₁` a finitely generated submodule
of `M`, which dies in `M ⊗ Q` already dies in `M₂ ⊗ Q` for some finitely generated `M₂ ⊇ M₁`.
It is read off Mathlib's `Submodule.FG.rTensor.directLimit` through
`Module.DirectLimit.of.zero_exact`.
`exists_fg_le_of_mem_range_rTensor_subtype` is the companion for a single element: an element of
`F ⊗ Q` coming from `K ⊗ Q` comes from `K₀ ⊗ Q` for some finitely generated `K₀ ≤ K`; it comes
from `TensorProduct.exists_finite_submodule_left_of_setFinite` applied inside `K`.

The finitely presented module produced by the construction is `(Fin k → R) ⧸ K₁`, which lives in
the universe of `R`; `Shrink` moves it to the universe `v` of `P` and `M`, which is what the
hypothesis `Small.{v} R` of the statement is for.

## References

* [StacksProject 059L](https://stacks.math.columbia.edu/tag/059L)
-/



namespace Stacks.FinitePresentation.Factorization

open TensorProduct LinearMap

section Helpers

variable {R : Type u} [CommRing R] {Q : Type w} [AddCommGroup Q] [Module R Q]

/-- Tensoring the inclusion of submodules `A ≤ B` with `Q` is monotone on ranges. -/
private lemma range_rTensor_subtype_mono {F : Type*} [AddCommGroup F] [Module R F]
    {A B : Submodule R F} (h : A ≤ B) :
    range (A.subtype.rTensor Q) ≤ range (B.subtype.rTensor Q) := by
  rw [show A.subtype = B.subtype ∘ₗ Submodule.inclusion h from rfl, rTensor_comp]
  exact range_comp_le_range _ _

/-- An element of `F ⊗ Q` in the image of `K ⊗ Q` is in the image of `K₀ ⊗ Q` for some finitely
generated `K₀ ≤ K`: only finitely many elements of `K` are involved in it. -/
private lemma exists_fg_le_of_mem_range_rTensor_subtype {F : Type*} [AddCommGroup F] [Module R F]
    (K : Submodule R F) {v : F ⊗[R] Q} (hv : v ∈ range (K.subtype.rTensor Q)) :
    ∃ K₀ ≤ K, K₀.FG ∧ v ∈ range (K₀.subtype.rTensor Q) := by
  obtain ⟨w, rfl⟩ := hv
  obtain ⟨K', hK', hw⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {w} (Set.finite_singleton w)
  obtain ⟨w', hw'⟩ := hw rfl
  refine ⟨range (K.subtype ∘ₗ K'.subtype), ?_, ?_, ?_⟩
  · exact (range_comp_le_range _ _).trans_eq K.range_subtype
  · rw [range_comp, Submodule.range_subtype]
    exact (Module.Finite.iff_fg.mp hK').map _
  · rw [← rTensor_range]
    exact ⟨w', by rw [rTensor_comp, comp_apply, hw']⟩

/-- **The colimit step.** An element of `M₁ ⊗ Q`, for `M₁` a finitely generated submodule of `M`,
which is killed in `M ⊗ Q` is already killed in `M₂ ⊗ Q` for some finitely generated
`M₂` with `M₁ ≤ M₂`: this is the statement that `M ⊗ Q` is the direct limit of the `M' ⊗ Q`
over the finitely generated submodules `M'` of `M`. -/
private lemma exists_fg_ge_of_rTensor_subtype_eq_zero {M : Type v} [AddCommGroup M] [Module R M]
    {M₁ : Submodule R M} (h₁ : M₁.FG) (v : M₁ ⊗[R] Q)
    (hv : M₁.subtype.rTensor Q v = 0) :
    ∃ (M₂ : Submodule R M) (h : M₁ ≤ M₂), M₂.FG ∧ (Submodule.inclusion h).rTensor Q v = 0 := by
  classical
  have : IsDirectedOrder {N : Submodule R M // N.FG} :=
    ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, le_sup_left, le_sup_right⟩⟩
  have := Submodule.FG.rTensor.directedSystem R M Q
  have key : Module.DirectLimit.of R {N : Submodule R M // N.FG} (fun N ↦ N.val ⊗[R] Q)
      (fun ⦃_ _⦄ h ↦ (Submodule.inclusion h).rTensor Q) ⟨M₁, h₁⟩ v = 0 := by
    apply (Submodule.FG.rTensor.directLimit R M Q).injective
    rw [Submodule.FG.rTensor.directLimit_apply' R M Q h₁ v, hv, map_zero]
  obtain ⟨⟨M₂, h₂⟩, hle, hzero⟩ := Module.DirectLimit.of.zero_exact key
  exact ⟨M₂, hle, h₂, hzero⟩

/-- **Shrinking the target.** A map `f : P → M` out of a finitely generated module factors
through a finitely generated submodule `M₂` of `M`, and `M₂` can be chosen so that an element of
`P ⊗ Q` killed by `f ⊗ id_Q` is killed by the corestriction of `f` to `M₂` tensored with `Q`. -/
private lemma exists_fg_factorization_rTensor_eq_zero {P M : Type v} [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] [Module.Finite R P] (f : P →ₗ[R] M) {x : P ⊗[R] Q}
    (hx : f.rTensor Q x = 0) :
    ∃ (M₂ : Submodule R M) (_ : M₂.FG) (f₀ : P →ₗ[R] M₂),
      M₂.subtype ∘ₗ f₀ = f ∧ f₀.rTensor Q x = 0 := by
  have h₁ : (range f).FG := by
    rw [range_eq_map]
    exact (Module.Finite.iff_fg.mp inferInstance).map f
  have hv : (range f).subtype.rTensor Q (f.rangeRestrict.rTensor Q x) = 0 := by
    rw [← rTensor_comp_apply, show (range f).subtype ∘ₗ f.rangeRestrict = f from rfl, hx]
  obtain ⟨M₂, hle, h₂, hzero⟩ :=
    exists_fg_ge_of_rTensor_subtype_eq_zero h₁ (f.rangeRestrict.rTensor Q x) hv
  refine ⟨M₂, h₂, Submodule.inclusion hle ∘ₗ f.rangeRestrict, rfl, ?_⟩
  rw [rTensor_comp_apply, hzero]

/-- **The construction.** A map from a finitely presented module to a finitely generated module
factors through an explicit finite presentation `(Fin k → R) ⧸ K` in which a prescribed element of
the kernel of `f ⊗ id_Q` is killed. -/
private lemma exists_quotient_factorization_rTensor_eq_zero {P : Type v} {M : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [Module.FinitePresentation R P]
    [Module.Finite R M] (f : P →ₗ[R] M) {x : P ⊗[R] Q} (hx : f.rTensor Q x = 0) :
    ∃ (k : ℕ) (K : Submodule R (Fin k → R)) (_ : K.FG) (f' : P →ₗ[R] (Fin k → R) ⧸ K)
      (g : ((Fin k → R) ⧸ K) →ₗ[R] M), f = g ∘ₗ f' ∧ f'.rTensor Q x = 0 := by
  classical
  -- a presentation `R^n / KP ≃ P` of `P`, with `KP` finitely generated
  obtain ⟨n, KP, e, hKP⟩ := Module.FinitePresentation.exists_fin R P
  set p : (Fin n → R) →ₗ[R] P := e.symm ∘ₗ KP.mkQ with hp
  have hpsurj : Function.Surjective p := e.symm.surjective.comp KP.mkQ_surjective
  -- a presentation `R^k ↠ M` of `M`, and a lift `u` of `f ∘ p` along it
  obtain ⟨k, σ, hσ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨u, hu⟩ := Module.projective_lifting_property σ (f ∘ₗ p) hσ
  obtain ⟨z, hz⟩ := rTensor_surjective Q hpsurj x
  -- the relations of `P` land in `ker σ`
  have hrel : KP.map u ≤ ker σ := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    have hy' : p y = 0 := by
      rw [hp]
      simp [(Submodule.Quotient.mk_eq_zero _).2 hy]
    simp [← comp_apply, hu, hy']
  -- the lift of `x` is killed in `M ⊗ Q`, hence comes from `ker σ ⊗ Q`
  have hmem : u.rTensor Q z ∈ range ((ker σ).subtype.rTensor Q) := by
    rw [← (rTensor_exact Q (exact_subtype_ker_map σ) hσ).linearMap_ker_eq]
    rw [mem_ker, ← rTensor_comp_apply, hu, rTensor_comp_apply, hz, hx]
  obtain ⟨K₀, hK₀le, hK₀fg, hK₀mem⟩ := exists_fg_le_of_mem_range_rTensor_subtype _ hmem
  -- the finite presentation: relations of `P` together with the witness of the vanishing
  refine ⟨k, K₀ ⊔ KP.map u, hK₀fg.sup (hKP.map u), ?_⟩
  have hmem₁ : ∀ y ∈ KP, u y ∈ K₀ ⊔ KP.map u := fun y hy ↦
    Submodule.mem_sup_right (Submodule.mem_map_of_mem hy)
  set K₁ := K₀ ⊔ KP.map u
  have hK₁le : K₁ ≤ ker σ := sup_le hK₀le hrel
  have hdesc : KP ≤ ker (K₁.mkQ ∘ₗ u) := fun y hy ↦ by
    simpa using hmem₁ y hy
  have hf'p : (KP.liftQ (K₁.mkQ ∘ₗ u) hdesc ∘ₗ e.toLinearMap) ∘ₗ p = K₁.mkQ ∘ₗ u := by
    rw [hp]
    ext y
    simp
  refine ⟨KP.liftQ (K₁.mkQ ∘ₗ u) hdesc ∘ₗ e.toLinearMap,
    K₁.liftQ σ (fun y hy ↦ hK₁le hy), ?_, ?_⟩
  · have hmaps : (K₁.liftQ σ (fun y hy ↦ hK₁le hy) ∘ₗ
        (KP.liftQ (K₁.mkQ ∘ₗ u) hdesc ∘ₗ e.toLinearMap)) ∘ₗ p = f ∘ₗ p := by
      rw [comp_assoc, hf'p, ← comp_assoc, Submodule.liftQ_mkQ, hu]
    ext y
    obtain ⟨y, rfl⟩ := hpsurj y
    simpa using (congr($hmaps y)).symm
  · rw [← hz, ← rTensor_comp_apply, hf'p, rTensor_comp_apply, ← mem_ker, rTensor_mkQ]
    exact range_rTensor_subtype_mono le_sup_left hK₀mem

/-- **The universe step.** A factorization through a finitely presented module in any universe
gives one through a finitely presented module in the universe of `P` and `M`, as soon as the
former is small. -/
private lemma exists_shrink_factorization {P M : Type v} {P'' : Type t} [AddCommGroup P]
    [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup P''] [Module R P'']
    [Module.FinitePresentation R P''] [Small.{v} P''] {f : P →ₗ[R] M} {x : P ⊗[R] Q}
    (f' : P →ₗ[R] P'') (g : P'' →ₗ[R] M) (hfg : f = g ∘ₗ f') (hx : f'.rTensor Q x = 0) :
    ∃ (P' : Type v) (_ : AddCommGroup P') (_ : Module R P')
      (_ : Module.FinitePresentation R P') (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
      f = g ∘ₗ f' ∧ f'.rTensor Q x = 0 := by
  refine ⟨Shrink.{v} P'', inferInstance, inferInstance,
    Module.FinitePresentation.of_equiv (Shrink.linearEquiv R P'').symm,
    (Shrink.linearEquiv R P'').symm ∘ₗ f', g ∘ₗ (Shrink.linearEquiv R P'' : _ →ₗ[R] _), ?_, ?_⟩
  · rw [hfg]
    ext y
    simp
  · rw [rTensor_comp_apply, hx, map_zero]

end Helpers

/-- **Stacks 059L.** A map `f : P → M` out of a finitely presented module factors as
`f = g ∘ₗ f'` through a finitely presented module `P'` in the universe of `P` and `M`, with a
prescribed element `x` of the kernel of `f ⊗ id_Q` already killed by `f' ⊗ id_Q`. -/
public theorem solution
    {R : Type u} [CommRing R] [Small.{v} R] {P M : Type v} {Q : Type w} [AddCommGroup P]
    [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R P] (f : P →ₗ[R] M) {x : P ⊗[R] Q}
    (hx : f.rTensor Q x = 0) :
    ∃ (P' : Type v) (_ : AddCommGroup P') (_ : Module R P')
      (_ : Module.FinitePresentation R P') (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
      f = g ∘ₗ f' ∧ f'.rTensor Q x = 0 := by
  obtain ⟨M₂, h₂, f₀, hf₀, hx₀⟩ := exists_fg_factorization_rTensor_eq_zero f hx
  have : Module.Finite R M₂ := Module.Finite.iff_fg.mpr h₂
  obtain ⟨k, K, hK, f', g, hfg, hx'⟩ := exists_quotient_factorization_rTensor_eq_zero f₀ hx₀
  have : Module.FinitePresentation R ((Fin k → R) ⧸ K) :=
    Module.finitePresentation_of_free_of_surjective K.mkQ K.mkQ_surjective
      (by rwa [Submodule.ker_mkQ])
  have : Small.{v} ((Fin k → R) ⧸ K) := small_of_surjective K.mkQ_surjective
  refine exists_shrink_factorization f' (M₂.subtype ∘ₗ g) ?_ hx'
  rw [← hf₀, hfg, comp_assoc]

end Stacks.FinitePresentation.Factorization

/-!
# Factoring a map through a finitely presented module after tensoring

Let `R` be a commutative ring, let `P` be a finitely presented `R`-module, let `f : P → M` be a
map of `R`-modules and let `Q` be an `R`-module. If an element `x` of `P ⊗ Q` is killed by
`f ⊗ id_Q`, then `f` already factors as `P → P' → M` through a finitely presented `R`-module `P'`
in which `x` is killed too, that is with `x` in the kernel of `P ⊗ Q → P' ⊗ Q` (Stacks 059L).

This is the compactness of finitely presented modules, made visible after tensoring. Writing `M`
as a directed colimit `M = colim M_i` of finitely presented modules, the map `f` factors through
some `M_j → M` because `P` is finitely presented, and the image `y` of `x` in `M_j ⊗ Q`, being
killed in `M ⊗ Q = colim (M_i ⊗ Q)`, is already killed in `M_{j'} ⊗ Q` for some `j' ≥ j`; so
`P' = M_{j'}` and `f'` is the composite `P → M_j → M_{j'}` will do. Its use is to replace a kernel
condition over `M`, about which nothing is assumed, by one over a finitely presented module, which
is the form in which domination of maps is recognized (Definition 059B, Lemma 059D), and this is
how the Mittag-Leffler criterion by injectivity of `M ⊗ ∏ Q_α → ∏ (M ⊗ Q_α)` is proved
(Proposition 059M).

The two halves of the conclusion pull against each other, and neither is idle: the kernel
condition alone is met by `P' = 0`, the factorization alone by `P' = P` with `f' = id`, and the
content of the lemma is one `P'` doing both. In particular, taking `P' = 0` forces `f = 0`.

## Main results

* `LinearMap.exists_finitePresentation_factorization_of_rTensor_apply_eq_zero`: a map `f : P → M`
  out of a finitely presented module factors through a finitely presented module in which a
  prescribed element of `Ker(f ⊗ id_Q)` is already killed.

## Implementation notes

The map `f ⊗ id_Q : P ⊗ Q → M ⊗ Q` is `LinearMap.rTensor Q f`, and the source's `x ∈ Ker(f ⊗ id_Q)`
is written elementwise as `f.rTensor Q x = 0`, which is `LinearMap.mem_ker` away from the source's
wording and is how Mathlib phrases the same hypothesis in
`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`. "`f` factors through `f'`" is pinned
as the equation `f = g ∘ₗ f'` for an explicit `g : P' → M`, rather than left as a property of `f'`.

The existence of a module is stated by quantifying over a type together with its instances, which
is Mathlib's idiom for this shape (`Module.exists_finite_presentation`,
`Module.FinitePresentation.equiv_quotient`). The alternative of pinning a concrete presentation of
`P'`, as a cokernel of a map of finite free modules, would force every user to undo that choice.

The module `P'` is produced in `Type v`, the universe of `P` and `M`, which is what
`Small.{v} R` buys: a finitely presented module is a quotient of a finite free module on `R`, so
it lands in `Type v` only after shrinking `R`. The hypothesis is automatic in the usual case where
`R` itself lives in `Type v`, and it is the same hypothesis carried by Lemma 059D. The test module
`Q` is left in its own universe `w`, nothing in the statement tying it to `v`.

Faithfulness. (1) No hypothesis is idle: finite presentation of `P` is what makes `f` factor
through a finite stage of the colimit above, and it is what Lemma 059D needs of `Coker(f')` when
this lemma is applied; `f.rTensor Q x = 0` is live, since for `R = ℤ`, `P = M = Q = ℤ`, `f = id`
and `x = 1 ⊗ 1` any factorization `id = g ∘ f'` with `f'.rTensor ℤ x = 0` would give
`f' 1 = 0` and hence `id = 0`. (2) The scalars and the base are the source's: one commutative ring
`R` throughout, `f`, `f'` and `g` are `R`-linear, both tensor products are `⊗[R]`, and nothing is
localized or base changed. (3) The maps the source names are pinned: `P ⊗ Q → M ⊗ Q` is `f ⊗ id_Q`
and `P ⊗ Q → P' ⊗ Q` is `f' ⊗ id_Q`, the same construction applied to `f'`, and the factorization
is the equation `f = g ∘ₗ f'`. Existence is all that can be asked of `P'` itself, which in the
source is a member `M_{j'}` of a chosen colimit presentation of `M` and is canonical in no sense.
(4) The instantiation is not degenerate: for `R = ℤ`, `P = M = ℤ`, `f` multiplication by `2`,
`Q = ℤ/2ℤ` and `x` the generator of `P ⊗ Q = ℤ/2ℤ`, the hypothesis holds because `f ⊗ id_Q` is
multiplication by `2` on `ℤ/2ℤ`, and `P' = ℤ` with `f'` multiplication by `2` and `g = id`
witnesses the conclusion with `x ≠ 0` and `P' ≠ 0`.

## References

* [StacksProject 059L](https://stacks.math.columbia.edu/tag/059L)
-/



open TensorProduct

@[expose] public section

/-- **Stacks 059L.** Let `R` be a commutative ring, `P` a finitely presented `R`-module,
`f : P → M` a map of `R`-modules and `Q` an `R`-module, and let `x ∈ P ⊗ Q` be killed by
`f ⊗ id_Q`. Then there are a finitely presented `R`-module `P'` and maps `f' : P → P'`,
`g : P' → M` with `f = g ∘ f'` such that `x` is killed by `f' ⊗ id_Q`. -/
@[stacks 059L "The kernel conditions are elementwise, `x` being a single element; `f` factors
through `f'` by the pinned equation `f = g ∘ₗ f'`."]
public theorem LinearMap.exists_finitePresentation_factorization_of_rTensor_apply_eq_zero
    {R : Type u} [CommRing R] [Small.{v} R] {P M : Type v} {Q : Type w} [AddCommGroup P]
    [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R P] (f : P →ₗ[R] M) {x : P ⊗[R] Q}
    (hx : f.rTensor Q x = 0) :
    ∃ (P' : Type v) (_ : AddCommGroup P') (_ : Module R P')
      (_ : Module.FinitePresentation R P') (f' : P →ₗ[R] P') (g : P' →ₗ[R] M),
      f = g ∘ₗ f' ∧ f'.rTensor Q x = 0 :=
  Stacks.FinitePresentation.Factorization.solution f hx

end
