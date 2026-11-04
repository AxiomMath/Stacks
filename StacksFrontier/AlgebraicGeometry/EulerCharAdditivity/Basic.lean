module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic

/-!
# Additivity of the Euler characteristic along a short exact sequence

Tag 08AA says that for a proper scheme `X` over a field `k` and a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent modules on `X`,
`χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`. The proof in the source is two steps: the long exact sequence
of cohomology attached to the short exact sequence, and the rank-nullity theorem applied to it.
This file proves both steps, and reduces Tag 08AA to the two facts that make `χ` well defined in
the first place — finite dimensionality of each `Hⁱ(X, ℱ)` (Tag 02O6) and vanishing of all but
finitely many of them (Tag 01XJ) — carried as hypotheses.

## Main results

* `Module.finsum_alternating_finrank_add_of_exact`: the rank-nullity step, as a statement of
  linear algebra. For three `ℕ`-indexed families of finite-dimensional `k`-vector spaces laced
  into a long exact sequence `0 ⟶ A₀ ⟶ B₀ ⟶ C₀ ⟶ A₁ ⟶ B₁ ⟶ ⋯` all of whose terms vanish from
  some index on, `∑ᵢ (-1)ⁱ dim Bᵢ = ∑ᵢ (-1)ⁱ dim Aᵢ + ∑ᵢ (-1)ⁱ dim Cᵢ`.
* `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`: **the long exact sequence of
  cohomology over a field.** For any morphism `f : X ⟶ Spec k` and any short exact sequence of
  modules on `X` there are connecting maps `Hⁿ(X, ℱ₃) ⟶ Hⁿ⁺¹(X, ℱ₁)` making
  `0 ⟶ H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂) ⟶ H⁰(X, ℱ₃) ⟶ H¹(X, ℱ₁) ⟶ ⋯` exact.
* `AlgebraicGeometry.finsum_alternating_finrank_cohomologyOverField_add_of_shortExact`: the two
  steps combined — additivity of the alternating sum of dimensions of cohomology, given finite
  dimensionality in every degree and vanishing from some degree on.
* `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero`: the
  statement of Tag 08AA, with those same two facts as hypotheses.
* `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`: **degree-zero cohomology is global
  sections**, `H⁰(X, ℱ) ≃ Γ(ℱ, ⊤)`, together with
  `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap`, which says it
  intertwines `H⁰(X, φ)` with `φ.app ⊤`. These live here rather than in a consumer because the
  two functors `AlgebraicGeometry.cohomologyOverFieldMap` is built from are `private` to this
  file, so no other module can unfold it.

## Main definitions

* `AlgebraicGeometry.cohomologyOverFieldMap`: the map `Hⁿ(X, ℱ) ⟶ Hⁿ(X, 𝒢)` of `k`-vector
  spaces induced by a morphism `ℱ ⟶ 𝒢` of modules, i.e. functoriality of
  `AlgebraicGeometry.cohomologyOverField` in its module argument.

## Implementation notes

**What is proved and what is assumed.** Tag 08AA itself is **not** proved here and no
`@[stacks 08AA]` attribute is attached anywhere in this file. Both steps of the source's proof
are proved in full and unconditionally; what is assumed is the content of the two lemmas the
source cites for well-definedness of `χ`, both of which the library has elsewhere:

* finite dimensionality of `Hⁱ(X, ℱ)` over `k` for `ℱ` coherent and `f` proper, Tag 02O6
  (Cohomology of Schemes); and
* `Hⁱ(X, ℱ) = 0` for `i` large, Tag 01XJ (Cohomology of Schemes).

`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero` takes
exactly those two as hypotheses, for the three modules of the sequence, so Tag 08AA follows from
it by discharging six arguments and nothing else. The tag is proved, by the route through
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'`, on
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact` in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/AdditivityUnconditional.lean`. The properness
and coherence hypotheses of Tag 08AA are present in that statement only because `χ` is defined
under them, and are used nowhere in the proof.

**The long exact sequence.** `AlgebraicGeometry.cohomologyOverField` is the right derived functor
of evaluation at the whole space, with scalars restricted to `k` — Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, for which Mathlib has no long exact sequence. The sequence
comes instead from `AlgebraicGeometry.cohomologyDeltaFunctor`, the instance at global sections
of `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, which packages the
`ℕ`-indexed right derived functors of any additive functor out of a category with enough
injectives as a cohomological `δ`-functor (Tag 010Q), so the sequence is available with no
hypothesis on `f` or on the modules at all. The private `globalSections` below is
definitionally that functor, so the shared `δ`-functor is the one this file's proofs use.
Restriction of scalars changes neither the underlying types nor the underlying functions
(`ModuleCat.restrictScalars.map_apply` is `rfl`), so exactness transports to the `k`-linear maps
by `ModuleCat` exactness read as `Function.Exact`.

The exactness in `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence` is stated as
`Function.Exact` on the underlying maps rather than as `CategoryTheory.ShortComplex.Exact`, and
the connecting maps are existentially quantified rather than named. Both choices keep
`CategoryTheory.HasDerivedCategory` — which the construction of the connecting map needs, which
has no global instance, and which `AlgebraicGeometry.cohomologyOverField` does not mention — out
of the statement.

**The rank-nullity step.** Mathlib's `Module.sum_neg_one_pow_finrank_eq_zero_of_exact` is the
same computation for a sequence indexed by `Fin (n + 2)`. It is not used: the sequence here is
three `ℕ`-indexed families laced together and truncated where they vanish, and assembling that
into a single `Fin`-indexed family costs more than the telescoping induction does.

**Why `AlgebraicGeometry.cohomologyOverFieldMap` carries `@[expose]`.** Its functoriality
(`..._id`, `..._comp`) and the degree-zero identification are all a consumer needs as long as it
only *composes* cohomology maps. A consumer that has to compare one with a comparison of
cohomologies built from a natural transformation of derived functors — naturality of the
closed-immersion comparison of
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, say — has to unfold it
instead, and `@[expose]` is refused for a body mentioning a `private` declaration. The body is
therefore written in the vocabulary of `AlgebraicGeometry.cohomologyOverField` itself, with the
two abbreviations below used only in the proofs, where they are definitionally equal to it.

**Note.** Global sections of modules is taken from `AlgebraicGeometry.ModuleGlobalSections`;
the file of Tag 01XK introduces it as `moduleGlobalSections`; it is private and nameless to
the library precisely so that Tag 01XK keeps the name. It exists only because
`AlgebraicGeometry.Scheme.Modules` is a `def` wrapping `SheafOfModules`, with its own category
and abelian instances, so the instances that an unascribed `SheafOfModules.evaluation` carries
are not the ones a `CategoryTheory.ShortComplex X.Modules` is stated with, and instance search
for `Functor.Additive` fails across the two.

## References

* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

/-! ### The rank-nullity step -/

namespace Module

variable {k : Type*} [Field k]

/-- Telescoping of an alternating sum of consecutive pairs. -/
private lemma alternating_sum_consecutive (N : ℕ) (v : ℕ → ℤ) :
    (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (v i + v (i + 1))) =
      v 0 + (-1 : ℤ) ^ N * v (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hs : (-1 : ℤ) ^ (N + 1) = -((-1 : ℤ) ^ N) := by rw [pow_succ]; ring
    rw [hs]; ring

/-- An alternating sum over `ℕ` of a family vanishing from `N` on is a sum over a range. -/
private lemma finsum_alternating_eq_sum_range (N : ℕ) (v : ℕ → ℤ) (hv : ∀ i, N ≤ i → v i = 0) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * v i) = ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * v i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  by_contra hn
  have hni : N ≤ i := by
    by_contra h
    exact hn (Finset.mem_range.mpr (by omega))
  simp [hv i hni] at hi

/-- **Additivity of the alternating sum of dimensions along a long exact sequence.** Let
`0 ⟶ A₀ ⟶ B₀ ⟶ C₀ ⟶ A₁ ⟶ B₁ ⟶ C₁ ⟶ ⋯` be an exact sequence of finite-dimensional `k`-vector
spaces, laced from three `ℕ`-indexed families, in which every term with index at least `N`
vanishes. Then `∑ᵢ (-1)ⁱ dim Bᵢ = ∑ᵢ (-1)ⁱ dim Aᵢ + ∑ᵢ (-1)ⁱ dim Cᵢ`. -/
theorem finsum_alternating_finrank_add_of_exact {A B C : ℕ → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)]
    [∀ i, FiniteDimensional k (A i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, FiniteDimensional k (C i)]
    (a : ∀ i, A i →ₗ[k] B i) (b : ∀ i, B i →ₗ[k] C i) (d : ∀ i, C i →ₗ[k] A (i + 1))
    (hab : ∀ i, Function.Exact (a i) (b i)) (hbc : ∀ i, Function.Exact (b i) (d i))
    (hca : ∀ i, Function.Exact (d i) (a (i + 1))) (hinj : Function.Injective (a 0)) (N : ℕ)
    (hA : ∀ i, N ≤ i → finrank k (A i) = 0) (hB : ∀ i, N ≤ i → finrank k (B i) = 0)
    (hC : ∀ i, N ≤ i → finrank k (C i) = 0) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k (B i) : ℤ)) =
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k (A i) : ℤ)) +
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (finrank k (C i) : ℤ) := by
  have hker0 : finrank k (LinearMap.ker (a 0)) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
  have hkerN : finrank k (LinearMap.ker (a (N + 1))) = 0 := by
    have h := (a (N + 1)).finrank_range_add_finrank_ker
    have hv := hA (N + 1) (by omega)
    omega
  -- Rank-nullity at `Aᵢ ⟶ Bᵢ ⟶ Cᵢ ⟶ Aᵢ₊₁`, with the two kernels of `a` as the error terms.
  have hrel (i : ℕ) :
      (finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i) =
        (finrank k (LinearMap.ker (a i)) : ℤ) + finrank k (LinearMap.ker (a (i + 1))) := by
    have ha := (a i).finrank_range_add_finrank_ker
    have hb := (b i).finrank_range_add_finrank_ker
    have hc := (d i).finrank_range_add_finrank_ker
    have hab' := congrArg (fun p : Submodule k (B i) => finrank k p) (hab i).linearMap_ker_eq
    have hbc' := congrArg (fun p : Submodule k (C i) => finrank k p) (hbc i).linearMap_ker_eq
    have hca' :=
      congrArg (fun p : Submodule k (A (i + 1)) => finrank k p) (hca i).linearMap_ker_eq
    have hNat : finrank k (A i) + finrank k (C i) =
        finrank k (B i) + finrank k (LinearMap.ker (a i)) +
          finrank k (LinearMap.ker (a (i + 1))) := by
      rw [← ha, ← hc, ← hb, ← hca', ← hbc', ← hab']; omega
    have hCast : (finrank k (A i) : ℤ) + finrank k (C i) =
        finrank k (B i) + finrank k (LinearMap.ker (a i)) +
          finrank k (LinearMap.ker (a (i + 1))) := by exact_mod_cast hNat
    linarith
  rw [finsum_alternating_eq_sum_range N _ fun i hi => by simp [hB i hi],
    finsum_alternating_eq_sum_range N _ fun i hi => by simp [hA i hi],
    finsum_alternating_eq_sum_range N _ fun i hi => by simp [hC i hi]]
  have hsum :
      (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
          ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i))) =
        ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
          ((finrank k (LinearMap.ker (a i)) : ℤ) + finrank k (LinearMap.ker (a (i + 1)))) :=
    Finset.sum_congr rfl fun i _ => by rw [hrel]
  have hleft :
      (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
          ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i))) =
        (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (finrank k (A i) : ℤ)) -
          (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (finrank k (B i) : ℤ)) +
          ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (finrank k (C i) : ℤ) := by
    simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- The error terms telescope, and both ends of the telescope vanish.
  have hright :
      (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
          ((finrank k (LinearMap.ker (a i)) : ℤ) +
            finrank k (LinearMap.ker (a (i + 1))))) = 0 := by
    rw [alternating_sum_consecutive,
      show (finrank k (LinearMap.ker (a 0)) : ℤ) = 0 by exact_mod_cast hker0,
      show (finrank k (LinearMap.ker (a (N + 1))) : ℤ) = 0 by exact_mod_cast hkerN]
    simp
  linarith [hleft, hsum, hright]

end Module

/-! ### The long exact sequence of cohomology over a field -/

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Restriction of scalars along the structure morphism, the functor that gives cohomology on a
scheme over `k` its `k`-vector space structure. -/
private def restrictToBase : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- The map `Hⁿ(X, ℱ) ⟶ Hⁿ(X, 𝒢)` of `k`-vector spaces induced by a morphism `ℱ ⟶ 𝒢` of
modules on a scheme over `k`: functoriality of `AlgebraicGeometry.cohomologyOverField` in its
module argument.

The body is written in the vocabulary `AlgebraicGeometry.cohomologyOverField` itself uses, and
not with the `private` abbreviation `restrictToBase` of this file, so that
it can carry `@[expose]`: a consumer comparing this map with a comparison of cohomologies built
from a natural transformation of derived functors — the naturality of the closed-immersion
comparison, say — has to unfold it, and `@[expose]` is refused for a body that mentions a
`private` declaration. The two spellings are definitionally equal, so the proofs below may still
use the abbreviations. -/
@[expose] def cohomologyOverFieldMap {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    cohomologyOverField k f F n ⟶ cohomologyOverField k f G n :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
    (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map φ)

/-- **`AlgebraicGeometry.cohomologyOverFieldMap` takes the identity to the identity.** Both
functors it is built from are functors; the statement has to be proved here because the two of
them are `private` to this file, so no consumer can reach the body. -/
theorem cohomologyOverFieldMap_id (F : X.Modules) (n : ℕ) :
    cohomologyOverFieldMap k f (𝟙 F) n = 𝟙 (cohomologyOverField k f F n) :=
  (congrArg (restrictToBase k f).map (((moduleGlobalSections X).rightDerived n).map_id F)).trans
    ((restrictToBase k f).map_id _)

/-- **`AlgebraicGeometry.cohomologyOverFieldMap` takes a composite to the composite.** Both
functors it is built from are functors; the statement has to be proved here because the two of
them are `private` to this file, so no consumer can reach the body. -/
theorem cohomologyOverFieldMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    cohomologyOverFieldMap k f (φ ≫ ψ) n =
      cohomologyOverFieldMap k f φ n ≫ cohomologyOverFieldMap k f ψ n :=
  (congrArg (restrictToBase k f).map
      (((moduleGlobalSections X).rightDerived n).map_comp φ ψ)).trans
    ((restrictToBase k f).map_comp _ _)

section LongExactSequence

/-- Restriction of scalars changes neither the underlying types nor the underlying maps, so it
carries exactness of a short complex of `Γ(X, ⊤)`-modules to exactness of the pair of `k`-linear
maps. -/
private lemma function_exact_restrictToBase {S : ShortComplex (ModuleCat.{u} Γ(X, ⊤))}
    (h : S.Exact) :
    Function.Exact ((restrictToBase k f).map S.f) ((restrictToBase k f).map S.g) :=
  fun x => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h x

/-- Restriction of scalars does not change the underlying map, so it carries injectivity. -/
private lemma injective_restrictToBase {M N : ModuleCat.{u} Γ(X, ⊤)} (φ : M ⟶ N)
    (h : Function.Injective φ) : Function.Injective ((restrictToBase k f).map φ) :=
  fun _ _ hab => h hab

/-- **The long exact sequence of cohomology over a field**, Tag 010Q for the global sections of
modules on a scheme. For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme
`X` over `k` there are connecting maps `Hⁿ(X, ℱ₃) ⟶ Hⁿ⁺¹(X, ℱ₁)` of `k`-vector spaces for which
`0 ⟶ H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂) ⟶ H⁰(X, ℱ₃) ⟶ H¹(X, ℱ₁) ⟶ H¹(X, ℱ₂) ⟶ ⋯` is exact. There is no
hypothesis on `f` or on the modules. -/
theorem exists_cohomologyOverField_longExactSequence {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    ∃ d : ∀ n : ℕ, cohomologyOverField k f S.X₃ n ⟶ cohomologyOverField k f S.X₁ (n + 1),
      Function.Injective (cohomologyOverFieldMap k f S.f 0) ∧
        (∀ n, Function.Exact (cohomologyOverFieldMap k f S.f n)
          (cohomologyOverFieldMap k f S.g n)) ∧
        (∀ n, Function.Exact (cohomologyOverFieldMap k f S.g n) (d n)) ∧
        ∀ n, Function.Exact (d n) (cohomologyOverFieldMap k f S.f (n + 1)) := by
  -- The cohomological `δ`-functor of Tag 010Q formed by the global sections of modules on `X`.
  -- Spelled out rather than named: the same statement is already declared as
  -- `Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor`
  -- (StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerCohomologySequence.lean:80), and
  -- importing that module here would add 522 modules to this file's 51-module closure.
  let E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (moduleGlobalSections X)
  refine ⟨fun n => (restrictToBase k f).map (E.δ hS n), ?_, ?_, ?_, ?_⟩
  · have hmono : Mono ((E.functor 0).map S.f) := E.mono_map_f hS
    exact injective_restrictToBase k f _ ((ModuleCat.mono_iff_injective _).1 hmono)
  · exact fun n => function_exact_restrictToBase k f (E.exact_map hS n)
  · exact fun n => function_exact_restrictToBase k f (E.exact_δ₁ hS n)
  · exact fun n => function_exact_restrictToBase k f (E.exact_δ₂ hS n)

end LongExactSequence

/-! ### Additivity -/

/-- **Additivity of the alternating sum of dimensions of cohomology along a short exact
sequence**: the two steps of the proof of Tag 08AA, with the finite dimensionality of Tag 02O6
and the vanishing of Tag 01XJ as hypotheses. -/
theorem finsum_alternating_finrank_cohomologyOverField_add_of_shortExact
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hfin₁ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₂ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n))
    (hfin₃ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) (N : ℕ)
    (hvan₁ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₁ n))
    (hvan₂ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₂ n))
    (hvan₃ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₃ n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₂ n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₁ n) : ℤ)) +
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₃ n) : ℤ) := by
  obtain ⟨d, hinj, hab, hbc, hca⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have hzero {F : X.Modules} {n : ℕ} (h : IsZero (cohomologyOverField k f F n)) :
      Module.finrank k (cohomologyOverField k f F n) = 0 :=
    have := ModuleCat.subsingleton_of_isZero h
    Module.finrank_zero_of_subsingleton
  have := hfin₁
  have := hfin₂
  have := hfin₃
  exact Module.finsum_alternating_finrank_add_of_exact
    (fun n => (cohomologyOverFieldMap k f S.f n).hom)
    (fun n => (cohomologyOverFieldMap k f S.g n).hom) (fun n => (d n).hom) hab hbc hca hinj N
    (fun n hn => hzero (hvan₁ n hn)) (fun n hn => hzero (hvan₂ n hn))
    fun n hn => hzero (hvan₃ n hn)

/-- **Tag 08AA with its two cited inputs as hypotheses.** For a proper scheme over a field and a
short exact sequence of coherent modules, `χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`, given finite
dimensionality of each cohomology group (Tag 02O6) and vanishing of all but finitely many of
them (Tag 01XJ). Properness and coherence are hypotheses of
`AlgebraicGeometry.eulerCharacteristic` and are not used in the proof. -/
theorem eulerCharacteristic_add_of_shortExact_of_finiteDimensional_of_isZero [IsProper f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (hfin₁ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n))
    (hfin₂ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n))
    (hfin₃ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) (N : ℕ)
    (hvan₁ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₁ n))
    (hvan₂ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₂ n))
    (hvan₃ : ∀ n, N ≤ n → IsZero (cohomologyOverField k f S.X₃ n)) :
    eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  exact finsum_alternating_finrank_cohomologyOverField_add_of_shortExact k f hS hfin₁ hfin₂ hfin₃
    N hvan₁ hvan₂ hvan₃

/-! ### Degree-zero cohomology is global sections -/

section DegreeZero

/-- **`H⁰(X, ℱ)` is the module of global sections of `ℱ`.** Global sections are left exact, so
the zeroth right derived functor computing `H⁰` is the global sections functor itself. -/
private def cohomologyOverFieldZeroIso (F : X.Modules) :
    cohomologyOverField k f F 0 ≅ (restrictToBase k f).obj ((moduleGlobalSections X).obj F) :=
  (restrictToBase k f).mapIso ((moduleGlobalSections X).rightDerivedZeroIsoSelf.app F)

/-- Naturality of `cohomologyOverFieldZeroIso`, applied in term position: `rw` builds a motive,
and the motive is not type-correct, because the `AlgebraicGeometry.Scheme.Modules` spelling of
the global sections functor and the `SheafOfModules` one carry different `Category` instances. -/
private theorem cohomologyOverFieldZeroIso_naturality {F G : X.Modules} (φ : F ⟶ G) :
    cohomologyOverFieldMap k f φ 0 ≫ (cohomologyOverFieldZeroIso k f G).hom
      = (cohomologyOverFieldZeroIso k f F).hom ≫ (restrictToBase k f).map
        ((moduleGlobalSections X).map φ) :=
  ((restrictToBase k f).map_comp (((moduleGlobalSections X).rightDerived 0).map φ)
      ((moduleGlobalSections X).rightDerivedZeroIsoSelf.app G).hom).symm.trans
    ((congrArg (restrictToBase k f).map
        (NatTrans.naturality (moduleGlobalSections X).rightDerivedZeroIsoSelf.hom φ)).trans
      ((restrictToBase k f).map_comp _ _))

/-- **Degree-zero cohomology is global sections.** The bijection `H⁰(X, ℱ) ≃ Γ(ℱ, ⊤)` obtained
from left exactness of global sections, stated at the `Γ` spelling of sections.

It is an `Equiv` rather than a `k`-linear equivalence because `Γ(ℱ, ⊤)` carries no `Module k`
instance: its `k`-vector space structure is the one restriction of scalars along the structure
morphism puts on it, which is the structure `AlgebraicGeometry.cohomologyOverField` records and
which has no name outside this file. -/
def cohomologyOverFieldZeroEquivSections (F : X.Modules) :
    (cohomologyOverField k f F 0 : Type u) ≃ Γ(F, ⊤) where
  toFun a := (cohomologyOverFieldZeroIso k f F).hom a
  invFun b := (cohomologyOverFieldZeroIso k f F).inv b
  left_inv a := (cohomologyOverFieldZeroIso k f F).hom_inv_id_apply a
  right_inv b := (cohomologyOverFieldZeroIso k f F).inv_hom_id_apply b

/-- **`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` intertwines `H⁰(X, φ)` with
`φ.app ⊤`.** This is what makes the identification usable: a class in `H⁰(X, 𝒢)` lies in the
image of `H⁰(X, φ)` exactly when the corresponding global section lies in the image of `φ` on
sections. -/
theorem cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap {F G : X.Modules}
    (φ : F ⟶ G) (a : cohomologyOverField k f F 0) :
    cohomologyOverFieldZeroEquivSections k f G (cohomologyOverFieldMap k f φ 0 a)
      = φ.app ⊤ (cohomologyOverFieldZeroEquivSections k f F a) :=
  DFunLike.congr_fun
    (congrArg ConcreteCategory.hom (cohomologyOverFieldZeroIso_naturality k f φ)) a

/-- Sections over `⊤` in the `appLE ⊤ ⊤` spelling that `AlgebraicGeometry.cohomologyOverField`
uses are sections over `⊤` in the `appTop` spelling. -/
theorem appLE_top_top_eq_appTop {Z Y : Scheme.{u}} (t : Z ⟶ Y)
    (e : (⊤ : Z.Opens) ≤ t ⁻¹ᵁ ⊤) : t.appLE ⊤ ⊤ e = t.appTop :=
  have h : Z.presheaf.map (homOfLE e).op = 𝟙 Γ(Z, ⊤) :=
    Eq.trans (congrArg Z.presheaf.map
      (Subsingleton.elim (homOfLE e).op (𝟙 (op (⊤ : Z.Opens))))) (Z.presheaf.map_id _)
  Eq.trans (congrArg (fun c ↦ t.appTop ≫ c) h) (Category.comp_id t.appTop)

/-- **Degree-zero cohomology is global sections, `k`-linearly**, at the `appTop` spelling of the
`k`-module structure on sections: global sections are left exact, so the zeroth right derived
functor computing `H⁰` is the global sections functor itself.

`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` above is the same identification read as
a bare `Equiv` of types, along which no dimension travels; this is the `k`-linear form, and
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` is what it is
good for. -/
def cohomologyOverFieldZeroIsoSections (F : X.Modules) :
    cohomologyOverField k f F 0 ≅
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F) :=
  appLE_top_top_eq_appTop f (by simp) ▸ (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app F)

/-- **The dimension of degree-zero cohomology of the structure sheaf is the dimension of the ring
of global functions**, for the `k`-algebra structure the structure morphism induces.

The bridge is that the `Module k` structure `RingHom.toAlgebra` puts on `Γ(X, ⊤)` is the one
`ModuleCat.restrictScalars` puts on it — the same restriction of scalars along `k ⟶ Γ(X, ⊤)` in
both cases — so `AlgebraicGeometry.cohomologyOverFieldZeroIsoSections` is an isomorphism of
`k`-modules with carrier `Γ(X, ⊤)` and `LinearEquiv.finrank_eq` applies with no transport.

No properness and no finite dimensionality: both sides may be infinite, in which case both
`Module.finrank` are zero and the statement still holds, being an equality along an iso. -/
theorem finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) =
      Module.finrank k Γ(X, ⊤) :=
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  (cohomologyOverFieldZeroIsoSections k f
    (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv.finrank_eq

end DegreeZero

/-! `AlgebraicGeometry.cohomologyOverFieldMap` is `@[expose]`d but **irreducible**, and the
attribute is set here, after this file's own proofs, which use the definitional equality with the
two `private` abbreviations freely.

Exposure without irreducibility is not an option: the body is a right derived functor, so a
`whnf` that reaches it unfolds injective resolutions and does not come back. For instance, a
`Function.Injective (cohomologyOverFieldMap …)` goal in
`StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean` overruns the heartbeat limit as soon as
the body is visible there. A consumer that genuinely has to unfold it — the naturality of
the closed-immersion comparison, which must compare this map with a component of a natural
transformation of derived functors — asks for it explicitly with `with_unfolding_all`. -/
attribute [irreducible] cohomologyOverFieldMap

end AlgebraicGeometry
