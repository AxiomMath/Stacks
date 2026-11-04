module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFree
public import StacksFrontier.Examples.Completion.CompleteModuleCategory

/-!
# Finite freeness of `Ω` discharges the hypothesis `hlift` of [Stacks, Tag 07JH]

`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFree.lean` discharges the *injectivity*
hypothesis `hinj` of
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor` from a
basis of `Ω` over `D` with an **arbitrary** index type: `I`-adic Hausdorffness of `M ⊗_D Ω` is
checked one coordinate at a time, so the index type of the basis is unconstrained.

This module does the same for the remaining algebraic hypothesis `hlift` — that the connection of
every pair factors through the uncompleted tensor product `M ⊗_D Ω` — and the index type is
**not** unconstrained here.  The lemma
`Crystalline.exists_firstOrderConnection_of_bijective` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsToPairsEquivalence.lean` derives `hlift` from
*bijectivity* of the canonical map `M ⊗_D Ω → M ⊗̂_D Ω`, and that lemma had no consumer anywhere:
nothing in the library produced a bijectivity hypothesis to feed it.  This module produces one.

By `AdicCompletion.of_bijective_iff` bijectivity of that map is `IsAdicComplete` for the `p`-adic
ideal of `D` on `M ⊗_D Ω`, which is `hinj` plus *precompleteness*.  Precompleteness is where the
finiteness enters and it cannot be removed:

* For a **finite** basis, `M ⊗_D Ω ≅ (ι → M)` is a finite product of copies of `M`, and a finite
  product of `I`-adically complete modules is `I`-adically complete
  (`Crystalline.isAdicComplete_pi`).  The module `M` of a pair is `p`-adically complete by its
  field `Crystalline.Pair.isPAdicallyComplete`, which is item (07JB) of the tag, so nothing beyond
  the finite basis is carried.
* For an **infinite** basis the conclusion is false, and this is proved below rather than
  remarked on.  `Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero`: for a principal
  ideal `(a)` of a separated ring in which no power of `a` vanishes, the family
  `f n = (1, a, …, a^{n-1}, 0, 0, …)` in `ℕ →₀ R` is Cauchy and its only candidate limit
  `(1, a, a², …)` is not finitely supported.
  `Crystalline.not_isPrecomplete_finsupp_powerSeries` instantiates it at the `(X)`-adically
  complete ring `ℤ⟦X⟧`, so the counterexample is inhabited.  Hence
  `Crystalline.isAdicComplete_finsupp_of_finite` has no analogue with the index type arbitrary,
  and the contrast with `Crystalline.isHausdorff_finsupp`, which *is* stated for an arbitrary
  index type, is a genuine asymmetry between the two halves of completeness and not an artefact
  of the proof.

## Main results

* `Crystalline.isAdicComplete_pi` — a finite product of `I`-adically complete modules is
  `I`-adically complete, through `AdicCompletion.piEquivOfFintype` and
  `AdicCompletion.of_bijective_iff`.  Mathlib has the splitting of the completion over a finite
  product but not this corollary of it.
* `Crystalline.isAdicComplete_finsupp_of_finite` and
  `Crystalline.isAdicComplete_tensorProduct_of_finite_basis` — hence the tensor product of an
  `I`-adically complete module with a module free of finite rank is `I`-adically complete.
* `Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` and
  `Crystalline.not_isPrecomplete_finsupp_powerSeries` — **the two preceding results are false
  with the index type arbitrary**, so the finiteness below is a limit of the method rather than a
  hypothesis added for convenience.
* `Crystalline.bijective_toCompletedTensor_of_finite_basis` — hence the canonical map
  `M ⊗_D Ω → M ⊗̂_D Ω` is bijective, not merely injective, when `Ω` is free of finite rank and `M`
  is `p`-adically complete.
* `Crystalline.forall_exists_firstOrderConnection_of_finite_basis` — **the hypothesis `hlift` of
  `Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`,
  verbatim, from a finite basis of `Ω` alone.**  This is the first consumer of
  `Crystalline.exists_firstOrderConnection_of_bijective`.
* `Crystalline.equivalence07JH_of_isEquivalence_functor_of_finite_basis` — **with `Ω` free of
  finite rank, [Stacks, Tag 07JH] for a reduction datum reduces to the single hypothesis that the
  datum's functor is an equivalence.**  Both algebraic hypotheses of the reduction are gone.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Two things remain for this reduction, and neither is touched here.  [Stacks, Tag 07JH] itself is
`...SmallSite.crystalPairFunctor_isEquivalence` of `SmallSite/CrystalPairEquivalence.lean`, for
the functor `...SmallSite.crystalPairFunctor`, which does not go through a reduction datum.

* `Functor.IsEquivalence Rd.functor` — that the passage from a crystal in quasi-coherent
  `𝒪_{X/S}`-modules on `Cris(X/S)` to its first-order comparison datum over `D` is an equivalence.
  This is the geometric content of the tag, and nothing in the library discharges it for a
  reduction datum.
* The existence of any term of
  `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` whatever.  Every statement
  below is about a given one, and none has been constructed outright:
  `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG.ofWholeSpaceSystem` is never
  invoked, and the only `PreReduction07JG` in the library,
  `...SmallSite.preReduction07JGBot`, exists in order to *fail* the field `levelSystem_isLevel`.

**The finite-rank hypothesis is an added assumption and is not the source's own.**  The `Ω` of
[Stacks, Tag 07JH] is the module of divided power differentials of the `p`-adically completed
divided power envelope `D`, taken relative to a presentation `C = A[x_w : w ∈ W]/J`, and the
source allows `W` infinite.  For finite `W` — a finite-type presentation, which is the case the
source's examples are in — the hypothesis holds; see
`Crystalline.equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials_of_finite` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FreeDifferentials07JH.lean`, where it is discharged at
the divided power polynomial algebra with nothing carried.  For infinite `W` the route taken here
is unavailable, by `Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero`, and `hlift`
would have to be proved some other way.

## References

* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public section

open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### Completeness of a finite product -/

section Pi

variable {R : Type*} [CommRing R]

/-- **A finite product of `I`-adically complete modules is `I`-adically complete.**

`AdicCompletion.of_bijective_iff` turns `IsAdicComplete I N` into bijectivity of the canonical
map `N → N^∧`, and `AdicCompletion.piEquivOfFintype` identifies `(∏ i, N i)^∧` with
`∏ i, (N i)^∧` in a way compatible with those canonical maps, by `AdicCompletion.map_of`.  So the
canonical map of the product is the coordinatewise one up to that identification, and a
coordinatewise map is bijective as soon as each coordinate is.

Mathlib has the identification but not this corollary: it has no `IsAdicComplete` instance for a
product.  Finiteness of the index type is essential — see
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero`. -/
theorem isAdicComplete_pi (I : Ideal R) {ι : Type*} [Finite ι] (N : ι → Type*)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (h : ∀ i, IsAdicComplete I (N i)) :
    IsAdicComplete I (∀ i, N i) := by
  classical
  cases nonempty_fintype ι
  rw [← AdicCompletion.of_bijective_iff]
  have hcoord : Function.Bijective
      (fun (x : ∀ i, N i) (i : ι) ↦ AdicCompletion.of I (N i) (x i)) :=
    Function.Bijective.piMap fun i ↦
      (AdicCompletion.of_bijective_iff (I := I) (M := N i)).mpr (h i)
  have hkey : ∀ x : (∀ i, N i), AdicCompletion.piEquivOfFintype I N
      (AdicCompletion.of I (∀ i, N i) x) = fun i ↦ AdicCompletion.of I (N i) (x i) := by
    intro x
    funext i
    rw [AdicCompletion.piEquivOfFintype_apply]
    simp only [AdicCompletion.pi, LinearMap.pi_apply, AdicCompletion.map_of]
    rfl
  have heq : (AdicCompletion.piEquivOfFintype I N) ∘ (AdicCompletion.of I (∀ i, N i)) =
      fun (x : ∀ i, N i) (i : ι) ↦ AdicCompletion.of I (N i) (x i) := funext hkey
  have hcomp : Function.Bijective
      ((AdicCompletion.piEquivOfFintype I N) ∘ (AdicCompletion.of I (∀ i, N i))) := heq ▸ hcoord
  exact (Function.Bijective.of_comp_iff' (AdicCompletion.piEquivOfFintype I N).bijective _).mp
    hcomp

/-- **Finitely supported families over a finite index type in an `I`-adically complete module are
`I`-adically complete**, by `Crystalline.isAdicComplete_pi` along
`Finsupp.linearEquivFunOnFinite`.

Contrast `Crystalline.isHausdorff_finsupp`, which has no finiteness hypothesis on the index type.
Hausdorffness is coordinatewise and finite support is no obstruction to it; precompleteness is
not, because the limit of a coordinatewise convergent family need not be finitely supported.  See
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero`. -/
theorem isAdicComplete_finsupp_of_finite (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (hM : IsAdicComplete I M) : IsAdicComplete I (ι →₀ M) :=
  Stacks.Examples.isAdicComplete_of_linearEquiv (Finsupp.linearEquivFunOnFinite R M ι)
    (isAdicComplete_pi I (fun _ : ι ↦ M) fun _ ↦ hM)

/-- **The tensor product of an `I`-adically complete module with a module free of finite rank is
`I`-adically complete.**  A basis of `Ω` indexed by a finite `ι` identifies `M ⊗_R Ω` with
`ι →₀ M` through `TensorProduct.equivFinsuppOfBasisRight`, exactly as in
`Crystalline.isHausdorff_tensorProduct_of_basis`, and
`Crystalline.isAdicComplete_finsupp_of_finite` finishes.

The finiteness of `ι` is the only difference from the Hausdorff statement, and it is doing real
work: `Crystalline.not_isPrecomplete_finsupp_powerSeries` is a complete ring whose finitely
supported families over `ℕ` are not precomplete. -/
theorem isAdicComplete_tensorProduct_of_finite_basis {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] {Omega : Type*} [AddCommGroup Omega] [Module R Omega] (I : Ideal R)
    (b : Module.Basis ι R Omega) (hM : IsAdicComplete I M) : IsAdicComplete I (M ⊗[R] Omega) := by
  classical
  exact Stacks.Examples.isAdicComplete_of_linearEquiv
    (TensorProduct.equivFinsuppOfBasisRight b) (isAdicComplete_finsupp_of_finite I hM)

/-- **The finiteness of the index type cannot be dropped from
`Crystalline.isAdicComplete_finsupp_of_finite`.**  Let `I = (a)` be a principal ideal of an
`I`-adically separated ring `R` in which no power of `a` vanishes.  Then the finitely supported
families `ℕ →₀ R` are **not** `I`-adically precomplete, even though `R` itself may be
`I`-adically complete.

The Cauchy family is `f n = (1, a, a², …, a^{n-1}, 0, 0, …)`: consecutive terms differ by
`a^i e_i` with `i ≥ n`, which lies in `I^n • ⊤`.  A limit `L` would have to satisfy
`L i = a^i` in every coordinate, because `a^i - L i` lies in `I^k • ⊤` for every `k` — read off
the `i`-th coordinate of `f n - L` for `n` large, using
`Crystalline.map_mem_pow_smul_top_of_mem` on `Finsupp.lapply i` — and `R` is separated.  But
`L` is finitely supported, so `L i = 0` for some `i`, forcing `a^i = 0`.

This is what makes `Crystalline.isHausdorff_finsupp` and
`Crystalline.isAdicComplete_finsupp_of_finite` genuinely different statements rather than the
same statement proved twice, and so it is what makes the finite-rank hypothesis of
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis` a necessity of the method and
not a gratuitous weakening: that hypothesis is the one place where the two halves of
`IsAdicComplete` part company. -/
theorem not_isPrecomplete_finsupp_of_forall_pow_ne_zero (a : R)
    (hR : IsHausdorff (Ideal.span {a}) R) (ha : ∀ n : ℕ, a ^ n ≠ 0) :
    ¬ IsPrecomplete (Ideal.span {a}) (ℕ →₀ R) := by
  set I : Ideal R := Ideal.span {a} with hI
  set f : ℕ → (ℕ →₀ R) := fun n ↦ ∑ i ∈ Finset.range n, Finsupp.single i (a ^ i) with hfdef
  have hsingle : ∀ m i : ℕ, m ≤ i →
      Finsupp.single i (a ^ i) ∈ (I ^ m • ⊤ : Submodule R (ℕ →₀ R)) := by
    intro m i hmi
    have hsplit : a ^ i = a ^ m • a ^ (i - m) := by
      rw [smul_eq_mul, ← pow_add]
      congr 1
      omega
    rw [hsplit, ← Finsupp.smul_single]
    exact Submodule.smul_mem_smul
      (by rw [hI, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      Submodule.mem_top
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R (ℕ →₀ R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hsplit : f m + ∑ i ∈ Finset.Ico m n, Finsupp.single i (a ^ i) = f n :=
      Finset.sum_range_add_sum_Ico _ hmn
    have hneg : f m - f n = -∑ i ∈ Finset.Ico m n, Finsupp.single i (a ^ i) := by
      rw [← hsplit]; abel
    rw [hneg]
    exact neg_mem (Submodule.sum_mem _ fun i hi ↦ hsingle m i (Finset.mem_Ico.mp hi).1)
  intro hpre
  obtain ⟨L, hL⟩ := hpre.prec hcauchy
  have hcoord : ∀ i : ℕ, L i = a ^ i := by
    intro i
    refine (sub_eq_zero.mp (hR.haus (a ^ i - L i) fun k ↦ SModEq.zero.mpr ?_)).symm
    have hkn : k ≤ max k (i + 1) := le_max_left _ _
    have hin : i < max k (i + 1) := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)
    refine Submodule.pow_smul_top_le _ _ hkn ?_
    have hproj : (f (max k (i + 1)) - L) i ∈ (I ^ max k (i + 1) • ⊤ : Submodule R R) := by
      have hgen := map_mem_pow_smul_top_of_mem I (Finsupp.lapply (M := R) (R := R) i)
        (max k (i + 1)) (SModEq.sub_mem.mp (hL (max k (i + 1))))
      rwa [Finsupp.lapply_apply] at hgen
    have hfn : (f (max k (i + 1))) i = a ^ i := by
      rw [hfdef, Finsupp.finsetSum_apply,
        Finset.sum_eq_single_of_mem (f := fun j ↦ (Finsupp.single j (a ^ j) : ℕ →₀ R) i) i
          (Finset.mem_range.mpr hin) fun j _ hji ↦ Finsupp.single_eq_of_ne hji.symm]
      exact Finsupp.single_eq_same
    simpa [hfn] using hproj
  have hnot : L.support.sup id + 1 ∉ L.support := by
    intro hmem
    have hle := Finset.le_sup (f := id) hmem
    simp only [id] at hle
    omega
  exact ha _ ((hcoord _).symm.trans (Finsupp.notMem_support_iff.mp hnot))

/-- **The counterexample is inhabited, so the finiteness hypothesis is not vacuously
unremovable.**  The ring of power series `ℤ⟦X⟧` is `(X)`-adically complete — that is Mathlib's
instance for `PowerSeries` — and `X^n ≠ 0` in it, so by
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` the finitely supported families
`ℕ →₀ ℤ⟦X⟧` are not `(X)`-adically precomplete.

The two halves are stated together on purpose: either alone is uninteresting.  The pair is the
statement that `Crystalline.isAdicComplete_finsupp_of_finite` is false with the index type
arbitrary, and so that the finite rank in
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis` is a limit of the method and not
a hypothesis added for convenience. -/
theorem not_isPrecomplete_finsupp_powerSeries :
    IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) (PowerSeries ℤ) ∧
      ¬ IsPrecomplete (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) (ℕ →₀ PowerSeries ℤ) :=
  ⟨inferInstance, not_isPrecomplete_finsupp_of_forall_pow_ne_zero _
    IsAdicComplete.toIsHausdorff fun n ↦ pow_ne_zero n PowerSeries.X_ne_zero⟩

end Pi

/-! ### Bijectivity of the completion map under finite freeness -/

section Bijective

/-- **The canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is bijective when `Ω` is free of finite rank and `M`
is `p`-adically complete.**  Injectivity is `Crystalline.injective_toCompletedTensor_of_basis` and
does not need the finiteness; surjectivity is precompleteness of `M ⊗_D Ω`, and that is where the
finite rank is used.  Both halves at once are
`AdicCompletion.of_bijective_iff` applied to
`Crystalline.isAdicComplete_tensorProduct_of_finite_basis`.

This is the hypothesis `hbij` of `Crystalline.exists_firstOrderConnection_of_bijective`, which
before this module had no consumer. -/
theorem bijective_toCompletedTensor_of_finite_basis (p : ℕ) (D : Type u) [CommRing D]
    (Omega : Type u) [AddCommGroup Omega] [Module D Omega] (M : Type u) [AddCommGroup M]
    [Module D M] {ι : Type*} [Finite ι] (b : Module.Basis ι D Omega)
    (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (toCompletedTensor p D Omega M) :=
  (AdicCompletion.of_bijective_iff (I := DividedPowers.pAdicIdeal (A := D) p)
      (M := M ⊗[D] Omega)).mpr
    (isAdicComplete_tensorProduct_of_finite_basis _ b hM)

end Bijective

/-! ### The hypothesis `hlift` under finite freeness of `Ω` -/

section Hlift

variable (A : Type u) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D) (Omega : Type u)
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega) (p : ℕ) {ι : Type uI} (dx : ι → Omega)

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- **The connection of a single pair factors through `M ⊗_D Ω` when `Ω` is free of finite
rank.**  This is `Crystalline.exists_firstOrderConnection_of_bijective` fed
`Crystalline.bijective_toCompletedTensor_of_finite_basis`, with the `p`-adic completeness of the
module taken from the pair's own field `Crystalline.Pair.isPAdicallyComplete`, which is item
(07JB) of [Stacks, Tag 07JH].  Nothing is carried but the finite basis of `Ω`. -/
theorem exists_firstOrderConnection_of_finite_basis
    (P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d))
    {κ : Type*} [Finite κ] (b : Module.Basis κ (D : Type u) Omega) :
    ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
      ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
        (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m :=
  exists_firstOrderConnection_of_bijective A D g Omega d p dx P
    (bijective_toCompletedTensor_of_finite_basis p (D : Type u) Omega P.carrier b
      P.isPAdicallyComplete)

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- **The hypothesis `hlift` of
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`,
verbatim, from a finite basis of `Ω` alone.**

This is the counterpart of `Crystalline.forall_injective_toCompletedTensor_of_basis` for the other
algebraic hypothesis of that reduction, and it is the first consumer anywhere of
`Crystalline.exists_firstOrderConnection_of_bijective`.  Unlike the injectivity statement it needs
the index type of the basis to be finite;
`Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` shows the underlying completeness
statement is false without that. -/
theorem forall_exists_firstOrderConnection_of_finite_basis {κ : Type*} [Finite κ]
    (b : Module.Basis κ (D : Type u) Omega) :
    ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m :=
  fun P ↦ exists_firstOrderConnection_of_finite_basis A D g Omega d p dx P b

end Hlift

/-! ### What is left of [Stacks, Tag 07JH] once `Ω` is free of finite rank -/

section Reduction

open CategoryTheory AlgebraicGeometry GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega] [Module D Omega]
  [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  {ι : Type uI} {dx : ι → Omega} [IsAffine S.X] [IsAffine S.S.scheme]
  {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-- **With `Ω` free of finite rank, [Stacks, Tag 07JH] reduces to one open question rather than
three.**
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`
reduces the tag, for a given reduction datum, to three hypotheses: that the datum's functor is an
equivalence, the injectivity hypothesis `hinj`, and the factorisation `hlift`.  A basis of `Ω`
discharges `hinj` by `Crystalline.forall_injective_toCompletedTensor_of_basis`; a basis with a
*finite* index type discharges `hlift` as well, by
`Crystalline.forall_exists_firstOrderConnection_of_finite_basis`.  What is left is the geometric
half alone.

This is **not** a proof of [Stacks, Tag 07JH] and no `@[stacks 07JH]` attribute is placed on it.
Two things remain open.  The hypothesis `Functor.IsEquivalence Rd.functor` is the statement that
the passage from a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to its first-order
comparison datum over `D` is an equivalence, and nothing in the library discharges it; by
`Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff` its faithfulness half
is exactly the faithfulness half of the tag, so it is not a weak hypothesis.  And the statement is
conditional on a reduction datum, of which the library constructs none. -/
theorem equivalence07JH_of_isEquivalence_functor_of_finite_basis
    (Rd : Reduction07JG S A D g Omega d p dx hp) (hR : Functor.IsEquivalence Rd.functor)
    {κ : Type*} [Finite κ] (b : Module.Basis κ (D : Type u) Omega) :
    Equivalence07JH Rd :=
  equivalence07JH_of_isEquivalence_functor Rd hR
    (forall_injective_toCompletedTensor_of_basis p dx b)
    (forall_exists_firstOrderConnection_of_finite_basis A D g Omega d p dx b)

end Reduction

end Crystalline

end
