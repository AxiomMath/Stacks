module

public import Mathlib.Data.Rat.Floor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialHighTwist
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialNumerical
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.CoherentTwistEventualVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FreeSheafTwistAcyclic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.Regularity

/-!
# A regularity bound for the kernels of quotients of a free sheaf, uniform in the quotient

Let `k` be a field, `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`. [Stacks, Tag 08AG] produces an integer `m`
depending only on `n`, `r` and `P` such that for every short exact sequence
`0 ⟶ 𝒦 ⟶ 𝒪^{⊕r} ⟶ ℱ ⟶ 0` of coherent sheaves on `ℙⁿ_k` with `ℱ` of Hilbert polynomial `P`,
the kernel `𝒦` is `m`-regular. This file proves it for a given base degree `b ≥ 0` and a given
chain of multiplications by a hyperplane section on the cohomology of the twists of `𝒦`, with
`m = b + ⌈P(b)⌉ + n` serving every field and every sequence.

## Main definitions

* `AlgebraicGeometry.KernelChainData`: maps `Hⁱ(ℙⁿ_k, 𝒦(b+j)) ⟶ Hⁱ(ℙⁿ_k, 𝒦(b+j+1))`, injective
  for `2 ≤ i ≤ n` and surjective for `i = 1`, with injectivity propagating along the chain in
  degree one.
* `AlgebraicGeometry.kernelRegularityBound`: the bound `b + ⌈P(b)⌉ + n`.

## Main results

* `AlgebraicGeometry.exists_shortExact_projectiveTwist`: the twist of a short exact sequence on
  `ℙⁿ_k` is short exact.
* `AlgebraicGeometry.finrank_cohomologyOverField_one_le_eulerCharacteristic_of_shortExact`: the
  bound `h¹(𝒦) ≤ χ(ℱ)` for a short exact sequence `0 ⟶ 𝒦 ⟶ ℰ ⟶ ℱ ⟶ 0` on a scheme proper over
  a field, with `ℰ` acyclic and `𝒦` acyclic above degree one.
* `AlgebraicGeometry.exists_isMRegular_kernel_free_of_kernelChainData`: [Stacks, Tag 08AG] at a
  given base degree `b` and chain, with `m = AlgebraicGeometry.kernelRegularityBound n P b`.

## References

* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 08AD](https://stacks.math.columbia.edu/tag/08AD)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-! ### Two chain arguments -/

/-- A function `ℕ → ℕ` bounded by `N` at `0`, never increasing, and strictly decreasing wherever
it is positive, is zero at `N`. -/
private theorem eq_zero_of_strict_drop (g : ℕ → ℕ) (N : ℕ) (h₀ : g 0 ≤ N)
    (hle : ∀ j, g (j + 1) ≤ g j) (hlt : ∀ j, 0 < g j → g (j + 1) < g j) : g N = 0 := by
  have key : ∀ j, j ≤ N → g j ≤ N - j := by
    intro j hj
    induction j with
    | zero => simpa using h₀
    | succ j ih =>
      have := ih (by omega)
      have := hle j
      rcases Nat.eq_zero_or_pos (g j) with hz | hp
      · omega
      · have := hlt j hp
        omega
  simpa using key N le_rfl

/-- A chain `H 0 ↣ H 1 ↣ ⋯` of injections of `k`-vector spaces that reaches a zero space at
index `N` starts at a zero space. -/
private theorem isZero_of_injective_chain (k : Type u) [Field k] :
    ∀ (N : ℕ) (H : ℕ → ModuleCat.{u} k) (φ : ∀ j, H j ⟶ H (j + 1)),
      (∀ j, Function.Injective (ConcreteCategory.hom (φ j))) → IsZero (H N) → IsZero (H 0) := by
  intro N
  induction N with
  | zero => exact fun _ _ _ h => h
  | succ N ih =>
    intro H φ hφ hN
    have h1 : IsZero (H 1) :=
      ih (fun j => H (j + 1)) (fun j => φ (j + 1)) (fun j => hφ (j + 1)) hN
    have : Subsingleton (H 1) := ModuleCat.subsingleton_of_isZero h1
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun _ _ => hφ 0 (Subsingleton.elim _ _)⟩

/-- Let `H 0 ↠ H 1 ↠ ⋯` be a chain of surjections of finite-dimensional `k`-vector spaces along
which injectivity propagates — if one map is injective, so is the next — and which is eventually
zero. Then `H B` is zero for every `B ≥ dim_k (H 0)`. -/
private theorem isZero_of_surjective_chain (k : Type u) [Field k] (H : ℕ → ModuleCat.{u} k)
    (hfd : ∀ j, FiniteDimensional k (H j)) (φ : ∀ j, H j ⟶ H (j + 1))
    (hsurj : ∀ j, Function.Surjective (ConcreteCategory.hom (φ j)))
    (hstep : ∀ j, Function.Injective (ConcreteCategory.hom (φ j)) →
      Function.Injective (ConcreteCategory.hom (φ (j + 1))))
    (N : ℕ) (hvan : ∀ j, N ≤ j → IsZero (H j))
    (B : ℕ) (hB : Module.finrank k (H 0) ≤ B) : IsZero (H B) := by
  have hzero : ∀ j, Function.Injective (ConcreteCategory.hom (φ j)) → IsZero (H j) := by
    intro j hj
    have hinj : ∀ l, Function.Injective (ConcreteCategory.hom (φ (j + l))) := by
      intro l
      induction l with
      | zero => simpa using hj
      | succ l ih => exact hstep (j + l) ih
    exact isZero_of_injective_chain k N (fun l => H (j + l)) (fun l => φ (j + l))
      (fun l => hinj l) (hvan (j + N) (by omega))
  have hle : ∀ j, Module.finrank k (H (j + 1)) ≤ Module.finrank k (H j) := by
    intro j
    have := hfd j
    exact LinearMap.finrank_le_finrank_of_surjective
      (f := ConcreteCategory.hom (φ j)) (hsurj j)
  have hlt : ∀ j, 0 < Module.finrank k (H j) →
      Module.finrank k (H (j + 1)) < Module.finrank k (H j) := by
    intro j hj
    have := hfd j
    have := hfd (j + 1)
    refine lt_of_le_of_ne (hle j) fun heq => ?_
    have := ModuleCat.subsingleton_of_isZero (hzero j
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).2 (hsurj j)))
    have hz : Module.finrank k (H j) = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hg := eq_zero_of_strict_drop (fun j => Module.finrank k (H j)) B hB hle hlt
  have := hfd B
  exact ModuleCat.isZero_iff_subsingleton.mpr (Module.finrank_zero_iff.mp hg)

/-! ### Twisting a short exact sequence, from [Stacks, Tag 0EGK] -/

/-- The `b`-th twist `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor` on
`ℙⁿ_k`, as an endofunctor of `AlgebraicGeometry.Scheme.Modules`. -/
public noncomputable def twistFunctorModules (k : Type u) [Field k] (n : ℕ) (b : ℤ) :
    (projectiveSpaceOverRing n (.of k)).Modules ⥤ (projectiveSpaceOverRing n (.of k)).Modules :=
  Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n b

/-- The twist, re-typed as in `AlgebraicGeometry.twistFunctorModules`, is an equivalence. -/
public noncomputable instance isEquivalence_twistFunctorModules (k : Type u) [Field k] (n : ℕ)
    (b : ℤ) : (twistFunctorModules k n b).IsEquivalence :=
  inferInstanceAs
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor (R := k) n b).IsEquivalence

/-- The twist, re-typed as in `AlgebraicGeometry.twistFunctorModules`, is additive. -/
public noncomputable instance additive_twistFunctorModules (k : Type u) [Field k] (n : ℕ)
    (b : ℤ) : (twistFunctorModules k n b).Additive :=
  inferInstanceAs
    (Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor (R := k) n b).Additive

/-- [Stacks, Tag 0EGK] on `ℙⁿ_k`: given a short exact `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of modules on `ℙⁿ_k`
and a degree `b`, there is a short exact sequence `0 ⟶ 𝒜(b) ⟶ ℬ(b) ⟶ 𝒞(b) ⟶ 0`. -/
public theorem exists_shortExact_projectiveTwist (k : Type u) [Field k] (n : ℕ) (b : ℤ)
    {A B C : (projectiveSpaceOverRing n (.of k)).Modules}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact) :
    ∃ (f' : projectiveTwist n A b ⟶ projectiveTwist n B b)
      (g' : projectiveTwist n B b ⟶ projectiveTwist n C b) (w' : f' ≫ g' = 0),
      (ShortComplex.mk f' g' w').ShortExact :=
  ⟨_, _, _, hS.map_of_exact (twistFunctorModules k n b)⟩

/-! ### The Euler-characteristic bound on `H¹` of a kernel -/

/-- The alternating sum of the dimensions of the cohomology of a module whose cohomology
vanishes in every degree at least two collapses to `h⁰ - h¹`. -/
public theorem finsum_alternating_finrank_cohomologyOverField_eq_sub (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)
    (hvan : ∀ i : ℕ, 2 ≤ i → IsZero (cohomologyOverField k f F i)) :
    (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k f F i) : ℤ)) =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f F 1) : ℤ) := by
  classical
  have hs : Function.support
      (fun i : ℕ => (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k f F i) : ℤ)) ⊆
      ({0, 1} : Finset ℕ) := by
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    by_contra h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at h
    have := ModuleCat.subsingleton_of_isZero (hvan i (by omega))
    exact hi (by simp [Module.finrank_zero_of_subsingleton])
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_insert (by simp),
    Finset.sum_singleton]
  ring

/-- Let `0 ⟶ 𝒦 ⟶ ℰ ⟶ ℱ ⟶ 0` be a short exact sequence of coherent modules on a scheme proper
over a field `k`. If the cohomology of `ℰ` vanishes in every positive degree and that of `𝒦` in
every degree at least two, then `dim_k H¹(X, 𝒦) ≤ χ(X, ℱ)`. -/
public theorem finrank_cohomologyOverField_one_le_eulerCharacteristic_of_shortExact
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (hker : ∀ i : ℕ, 2 ≤ i → IsZero (cohomologyOverField k f S.X₁ i))
    (hmid : ∀ i : ℕ, 1 ≤ i → IsZero (cohomologyOverField k f S.X₂ i)) :
    (Module.finrank k (cohomologyOverField k f S.X₁ 1) : ℤ) ≤ eulerCharacteristic k f S.X₃ := by
  have hfin := cohomologyFiniteDimensionalOverFieldOn k f
  have hadd : eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ :=
    eulerCharacteristic_add_of_shortExact_of_finiteDimensional' k f hS
      (fun i _ => hfin S.X₁ inferInstance i) fun i _ => hfin S.X₃ inferInstance i
  have hχ₁ : eulerCharacteristic k f S.X₁ =
      (Module.finrank k (cohomologyOverField k f S.X₁ 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f S.X₁ 1) : ℤ) := by
    rw [eulerCharacteristic_eq_finsum]
    exact finsum_alternating_finrank_cohomologyOverField_eq_sub k f S.X₁ hker
  have hχ₂ : eulerCharacteristic k f S.X₂ =
      (Module.finrank k (cohomologyOverField k f S.X₂ 0) : ℤ) := by
    rw [eulerCharacteristic_eq_finsum]
    exact finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k f S.X₂ hmid
  have hmono : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
    obtain ⟨_, hinj, _, _, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
    have := hfin S.X₂ inferInstance 0
    exact LinearMap.finrank_le_finrank_of_injective
      (f := ConcreteCategory.hom (cohomologyOverFieldMap k f S.f 0)) hinj
  omega

/-! ### The chain of multiplications by the hyperplane section -/

/-- The chain of multiplications by a hyperplane section on the cohomology of the twists of a
coherent sheaf `𝒦` on `ℙⁿ_k`, from a base degree `b`: for every cohomological degree `i` and every
step `j` a map `Hⁱ(ℙⁿ_k, 𝒦(b+j)) ⟶ Hⁱ(ℙⁿ_k, 𝒦(b+j+1))`, injective in the degrees `2 ≤ i ≤ n`,
surjective in degree one, and such that in degree one injectivity propagates from one step to
the next. -/
public structure KernelChainData (k : Type u) [Field k] (n : ℕ)
    (K : (projectiveSpaceOverRing n (.of k)).Modules) (b : ℤ) where
  /-- Multiplication by the hyperplane section, read on `Hⁱ(𝒦(b+j))`. -/
  step : ∀ i j : ℕ,
    cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n K (b + (j : ℤ))) i ⟶
      cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n K (b + ((j + 1 : ℕ) : ℤ))) i
  /-- In degrees at least two the chain maps are injective. -/
  injective_step : ∀ i : ℕ, 2 ≤ i → i ≤ n → ∀ j : ℕ,
    Function.Injective (ConcreteCategory.hom (step i j))
  /-- In degree one the chain maps are surjective. -/
  surjective_step : ∀ j : ℕ, Function.Surjective (ConcreteCategory.hom (step 1 j))
  /-- In degree one injectivity propagates along the chain. -/
  injective_step_succ : ∀ j : ℕ,
    Function.Injective (ConcreteCategory.hom (step 1 j)) →
      Function.Injective (ConcreteCategory.hom (step 1 (j + 1)))

/-! ### The bound, and Tag 08AG -/

/-- The regularity bound `b + ⌈P(b)⌉ + n` of [Stacks, Tag 08AG], for a base degree `b`. -/
public def kernelRegularityBound (n : ℕ) (P : Polynomial ℚ) (b : ℤ) : ℤ :=
  b + (⌈P.eval (b : ℚ)⌉₊ : ℤ) + n

/-- [Stacks, Tag 08AG] at a given base degree. Fix `n`, a rank `r ≥ 1`, a rational polynomial
`P` and a degree `b ≥ 0`. There is a single integer `m`, namely
`AlgebraicGeometry.kernelRegularityBound n P b`, such that for every field `k`, every coherent
sheaf `ℱ` on `ℙⁿ_k`, every epimorphism `q : 𝒪^{⊕r} ⟶ ℱ` and every chain data
`AlgebraicGeometry.KernelChainData` for `𝒦 = ker q` at `b`, if the Hilbert polynomial of `ℱ` is
`P` then `𝒦` is `m`-regular. -/
public theorem exists_isMRegular_kernel_free_of_kernelChainData
    (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ) (b : ℤ) (hb : 0 ≤ b) :
    ∃ m : ℤ, ∀ (k : Type u) [Field k]
      (Q : (projectiveSpaceOverRing n (.of k)).Modules) [Q.IsCoherent]
      (q : freeModules k n r ⟶ Q) [Epi q],
      KernelChainData k n (kernel q) b →
      (∀ d : ℤ, (hilbertPolynomial k n Q d : ℚ) = P.eval (d : ℚ)) →
      @IsMRegular k _ n (kernel q) (CoherentAbelian.isCoherent_kernel q) m := by
  refine ⟨kernelRegularityBound n P b, ?_⟩
  intro k _ Q _ q _ D hP
  have : (kernel q).IsCoherent := CoherentAbelian.isCoherent_kernel q
  obtain ⟨tf, tg, tw, hTwisted⟩ :=
    exists_shortExact_projectiveTwist k n b (kernel.ι q) q (kernel.condition q)
      ⟨ShortComplex.kernelSequence_exact q⟩
  obtain ⟨d₀, hd₀⟩ := exists_isZero_cohomologyOverField_projectiveTwist k n (kernel q)
  have hev : ∀ j : ℕ, (d₀ - b).toNat ≤ j → ∀ p : ℕ, 0 < p →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) (b + (j : ℤ))) p) := fun j hj p hp =>
    hd₀ (b + (j : ℤ)) (by omega) p hp
  have hhigh : ∀ i : ℕ, 2 ≤ i → ∀ j : ℕ,
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) (b + (j : ℤ))) i) := by
    intro i hi j
    rcases le_or_gt i n with hin | hin
    · exact isZero_of_injective_chain k (d₀ - b).toNat
        (fun l => cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
          (projectiveTwist n (kernel q) (b + ((j + l : ℕ) : ℤ))) i)
        (fun l => D.step i (j + l)) (fun l => D.injective_step i hi hin (j + l))
        (hev (j + (d₀ - b).toNat) (by omega) i (by omega))
    · refine (isZero_cohomologyOverField_iff_isZero_hgroup k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) (b + (j : ℤ))) i).mpr ?_
      have : (projectiveTwist n (kernel q) (b + (j : ℤ))).IsQuasicoherent :=
        isQuasicoherent_projectiveTwist_of_isCoherent n (kernel q) (b + (j : ℤ))
      exact Stacks.ProjectiveCohomology.isZero_Hgroup_of_lt n (.of k) _ i hin
  have hB : Module.finrank k
      (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) b) 1) ≤ ⌈P.eval (b : ℚ)⌉₊ := by
    have hineq : (Module.finrank k
          (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
            (projectiveTwist n (kernel q) b) 1) : ℤ)
        ≤ eulerCharacteristic k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
            (projectiveTwist n Q b) :=
      finrank_cohomologyOverField_one_le_eulerCharacteristic_of_shortExact k
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) hTwisted
        (fun i hi => by simpa using hhigh i hi 0) fun i hi =>
          (isZero_cohomologyOverField_iff_isZero_hgroup k
            (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
            (projectiveTwist n (freeModules k n r) b) i).mpr
            (isZero_Hgroup_projectiveTwist_freeModules k n r b hb i (by omega))
    rw [← hilbertPolynomial_eq_eulerCharacteristic k n Q b] at hineq
    have hceil : hilbertPolynomial k n Q b ≤ (⌈P.eval (b : ℚ)⌉₊ : ℤ) := by
      exact_mod_cast (hP b).trans_le (Nat.le_ceil _)
    omega
  have hone : 1 ≤ n → ∀ j : ℕ, ⌈P.eval (b : ℚ)⌉₊ ≤ j →
      IsZero (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) (b + (j : ℤ))) 1) := by
    intro hn j hj
    have hB0 : Module.finrank k
        (cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
          (projectiveTwist n (kernel q) (b + ((0 : ℕ) : ℤ))) 1) ≤ j := by
      rw [Nat.cast_zero, add_zero]
      exact hB.trans hj
    exact isZero_of_surjective_chain k
      (fun j => cohomologyOverField k (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
        (projectiveTwist n (kernel q) (b + (j : ℤ))) 1)
      (fun j => cohomologyFiniteDimensionalOverFieldOn k _ _
        (isCoherent_projectiveTwist n (kernel q) (b + (j : ℤ))) 1)
      (D.step 1) D.surjective_step D.injective_step_succ (d₀ - b).toNat
      (fun j hj => hev j hj 1 one_pos) _ hB0
  intro i hi hin
  refine (isZero_cohomologyOverField_iff_isZero_hgroup k
    (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))
    (projectiveTwist n (kernel q) (kernelRegularityBound n P b - (i : ℤ))) i).mp ?_
  have hdeg : kernelRegularityBound n P b - (i : ℤ)
      = b + ((⌈P.eval (b : ℚ)⌉₊ + (n - i) : ℕ) : ℤ) := by
    rw [kernelRegularityBound]
    omega
  rw [hdeg]
  rcases hi.eq_or_lt with h1 | h2
  · subst h1
    exact hone hin _ (by omega)
  · exact hhigh i (by omega) _

end AlgebraicGeometry

end
