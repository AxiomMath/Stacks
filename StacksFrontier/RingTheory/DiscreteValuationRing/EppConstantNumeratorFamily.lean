module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFrobeniusCombination
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constant-numerator family: one shared Artin--Schreier extension of the base

This is O2's third disjunct — the genuinely-ramified, empty-wild-set branch of Tag 09F9 — at the
per-layer shape `Stacks.EppTheorem.FamilyPrimeDegreeSolvable` that
`Stacks.EppTheorem.familyTowerSolvable_of_forall_terminal` consumes.

## What the branch is

Off its wild set every Laurent coefficient of a member lies in the perfect core of that member's
residue field, and the shared residue absorption
(`exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`)
replaces those coefficients by elements of the *base*, at one depth `N` fixed before any member is
examined.  What a member then presents is an Artin--Schreier layer whose **pole part is a base
element** — a depth-`N` Frobenius numerator over `A` in one common uniformizer `π` — plus an
integral part of its own.  Since the pole parts all live in `K`, one finite extension of `K` in
which they all acquire Artin--Schreier roots serves the whole family at once, and that extension is
computed from the family's bounds before any member is examined.  That is the quantifier discipline
the route demands: `∃ K₂` outside `∀ i`, never a per-member extension combined afterwards.

## Where the presentation lands, which was the open question

The pole part is over the **base**: coefficients `α i j : A` and the uniformizer `π : A`, so the
Artin--Schreier class is an element of `K` and the extension that splits it is an extension of `K`.
The integral part is over the **member**, `b i : B i`; it is not, and cannot be, pushed down to
`A`, because the absorption controls the coefficients of the polar terms and says nothing about the
integral term.  Both halves matter: without the first there is no shared extension, and with the
first the second is harmless, since after the class is split what is left of the layer is an
Artin--Schreier parameter integral over the member's own ring.

`B i` and not `C i`, and this is soundness rather than taste.  A layer is Artin--Schreier over
`L i` only if its parameter lies in `L i`, and with `b i : C i` nothing in the statement forces
that — `z i ^ p - z i` would be an unconstrained element of `M i` and the branch would be claiming
something about extensions that are not Artin--Schreier at all.  Nothing is lost by the
restriction: `C i ∩ L i = B i`, since `B i` is integrally closed, so an integral part that makes
the parameter lie in `L i` is in `B i` already.

## What is settled about the shape, and what is not

The members are presented in the **bound** shape
`Ξ_N(n) = { π⁻¹ ^ n * (∑_{j < n} α j ^ (p ^ N) * π ^ j) + b }`, with `n` a pole **bound** and not a
pole order.  Adding `IsUnit (α 0)` or `¬ p ∣ n` would pin `n` to the pole order and make closure
under `𝔽_p`-combination false — the characteristic-`2` witness is in
`EppFrobeniusNumerator.lean`'s module docstring.  On the bound shape closure holds, at the same
depth and at the bound `max_i n_i`, which is
`Stacks.EppTheorem.exists_frobeniusNumerator_of_sum`.

The depth is one family-wide `N` with `∀ i, nBound i ≤ N`.  The intended discharge is
`N := Finset.univ.sup nBound`; taking `N` existentially with that bound is weaker, hence easier to
supply, and nothing below needs more.

## Main results

* `Stacks.EppTheorem.exists_artinSchreierSplitting_forall` — the shared extension, pure field
  theory: for
  a finite family of elements of a characteristic-`p` field there is one finite **separable**
  extension in which every member acquires an Artin--Schreier root.  Built by iterating the
  splitting field of `X ^ p - X - C c`, which is separable because its derivative is `-1`.
* `Stacks.EppTheorem.exists_terminal_of_combination` and
  `Stacks.EppTheorem.trivial_or_unramified_or_totallyRamified_of_combination` — the seminar's
    verdict
 wired to the family: every
  `𝔽_p`-combination of the members' base classes is again presented at the family-wide depth, so it
  reduces to a terminal representative and its Artin--Schreier extension of `K` is trivial,
  unramified with separable residue extension, or totally ramified.  **Never ferocious**, with no
  minimality hypothesis anywhere.
* `Stacks.EppTheorem.SplitConstantClassSolvable` — the one obligation this file does not discharge,
  named
  at the point it is needed.
* `Stacks.EppTheorem.familyPrimeDegreeSolvable_of_frobeniusPresentation` — the producer:
  `FamilyPrimeDegreeSolvable`'s telescope, plus `CharP K p` and the presentation, yields the shared
  `K₂`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

namespace Stacks.EppTheorem

open IsDiscreteValuationRing Polynomial

universe u

/-! ### The shared Artin--Schreier extension of the base

Pure field theory: no valuation, no ramification, no residue field.  What makes the construction
available is that the members' classes are elements of `K`, which is what the constant-numerator
presentation buys. -/

/-- **A field extension generated by the image of a separable extension is separable.**

If `E / L` is generated as an `L`-algebra by the image of an algebra map `ι : K₂ →ₐ[K] E` from a
separable extension `K₂ / K`, with `L` an intermediate field, then `E / L` is separable.

This is the hypothesis `[Algebra.IsSeparable K E]` of
`IsDiscreteValuationRing.exists_isWeakSolution_of_fieldFactor_ramification` at the **middle**
layer, where the base field is `L` rather than `K`: the conjugate factors of
`(L ⊗[K] K₂) ⧸ nilradical` are generated over `L` by the image of `K₂`, and that is exactly this
hypothesis.

Mathlib does not have it, and the near misses fail for a structural reason worth recording:
`Algebra.isSeparable_tower_top_of_isSeparable` wants a tower `F ⊆ L ⊆ E` with `E / F` separable,
which is what is being *concluded* here and not what is given; and
`IntermediateField.isSeparable_iSup` and `isSeparable_sup` want intermediate fields of a fixed
extension, whereas a conjugate factor is a quotient of a tensor product.  The proof instead goes
through `separableClosure L E` as an intermediate field: each `ι x` has the same minimal polynomial
over `K` as `x` (`minpoly.algHom_eq`, `ι` being injective into a field), hence is separable over
`K` and so over `L`, so the separable closure contains the generators and therefore everything. -/
@[ega "0 20.6.19" "(ii), case F/K algebraic"]
theorem isSeparable_of_adjoin_range_algHom {K L E K₂ : Type*}
    [Field K] [Field L] [Field E] [Field K₂]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [Algebra K K₂] [Algebra.IsSeparable K K₂]
    (ι : K₂ →ₐ[K] E) (hgen : Algebra.adjoin L (Set.range ι) = ⊤) :
    Algebra.IsSeparable L E := by
  have hsub : Set.range ι ⊆ (separableClosure L E : Set E) := by
    rintro _ ⟨x, rfl⟩
    have h1 : IsSeparable K (ι x) := by
      rw [IsSeparable, minpoly.algHom_eq ι ι.injective x]
      exact Algebra.IsSeparable.isSeparable K x
    exact mem_separableClosure_iff.mpr (IsSeparable.tower_top L h1)
  have htop : (⊤ : Subalgebra L E) ≤ (separableClosure L E).toSubalgebra := by
    rw [← hgen]
    exact Algebra.adjoin_le hsub
  rw [← separableClosure.eq_top_iff]
  exact top_le_iff.mp (fun x _ => htop (by trivial : x ∈ (⊤ : Subalgebra L E)))

section Splitting

/-- **The Artin--Schreier polynomial is separable.**

Its derivative is the unit `-1`, which is the whole proof.
`separable_C_mul_X_pow_add_C_mul_X_add_C'` packages that for `C a * X ^ n + C b * X + C c` with
`p ∣ n` and `b` a unit. -/
theorem separable_X_pow_sub_X_sub_C (K : Type*) [Field K] (p : ℕ) [CharP K p] (c : K) :
    (X ^ p - X - C c : K[X]).Separable := by
  have h : (X ^ p - X - C c : K[X]) = C 1 * X ^ p + C (-1) * X + C (-c) := by
    simp; ring
  rw [h]
  exact separable_C_mul_X_pow_add_C_mul_X_add_C' p p 1 (-1) (-c) dvd_rfl (IsUnit.neg isUnit_one)

/-- The Artin--Schreier polynomial has degree `p`: the subtracted `X + C c` has degree `1 < p`. -/
theorem degree_X_pow_sub_X_sub_C (K : Type*) [Field K] (p : ℕ) (hp : 1 < p) (c : K) :
    (X ^ p - X - C c : K[X]).degree = (p : WithBot ℕ) := by
  have hlt : (X + C c : K[X]).degree < (X ^ p : K[X]).degree := by
    rw [degree_X_pow, degree_X_add_C]
    exact_mod_cast Nat.one_lt_cast.mpr hp
  have he : (X ^ p - X - C c : K[X]) = X ^ p - (X + C c) := by ring
  rw [he, degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]

/-- **One Artin--Schreier class is split by a finite separable extension.**

The splitting field of `X ^ p - X - C c`.  It is finite by construction and separable because the
polynomial is (`Algebra.isSeparable_of_separable_splitting_field`), and it contains a root because
the polynomial splits there and has nonzero degree. -/
theorem exists_artinSchreierSplitting (K : Type u) [Field K] (p : ℕ) (hp : 1 < p) [CharP K p]
    (c : K) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E)
      (_ : Algebra.IsSeparable K E), ∃ w : E, w ^ p - w = algebraMap K E c := by
  classical
  have hsep : (X ^ p - X - C c : K[X]).Separable := separable_X_pow_sub_X_sub_C K p c
  have hdeg : (X ^ p - X - C c : K[X]).degree ≠ 0 := by
    rw [degree_X_pow_sub_X_sub_C K p hp c]
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  refine ⟨(X ^ p - X - C c : K[X]).SplittingField, inferInstance, inferInstance, inferInstance,
    Algebra.isSeparable_of_separable_splitting_field K _ hsep, ?_⟩
  have hsplits := IsSplittingField.splits (X ^ p - X - C c : K[X]).SplittingField
    (X ^ p - X - C c : K[X])
  obtain ⟨w, hw⟩ := hsplits.exists_eval_eq_zero (by rwa [degree_map])
  refine ⟨w, ?_⟩
  rw [eval_map] at hw
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at hw
  linear_combination hw

/-- The induction behind `exists_artinSchreierSplitting_forall`, on the length of the family.

The base field is quantified *inside* the induction because the step replaces it: the extension
produced for the last class becomes the base for the remaining ones.  Composing the two gives one
extension, finite and separable over the original base by transitivity, and the earlier roots are
transported up by its structure map. -/
private theorem exists_artinSchreierSplitting_fin (p : ℕ) (hp : 1 < p) :
    ∀ (n : ℕ) (K : Type u) (_ : Field K) (_ : CharP K p) (ξ : Fin n → K),
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E)
        (_ : Algebra.IsSeparable K E),
        ∀ i, ∃ w : E, w ^ p - w = algebraMap K E (ξ i) := by
  intro n
  induction n with
  | zero =>
    intro K _ _ ξ
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, fun i => absurd i.2
      (by omega)⟩
  | succ n ih =>
    intro K _ _ ξ
    obtain ⟨E, _, _, _, _, w₀, hw₀⟩ := exists_artinSchreierSplitting K p hp (ξ (Fin.last n))
    let : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
    obtain ⟨F, _, _, _, _, hF⟩ := ih E inferInstance inferInstance
      (fun i => algebraMap K E (ξ i.castSucc))
    let : Algebra K F := ((algebraMap E F).comp (algebraMap K E)).toAlgebra
    let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
    let : Module.Finite K F := Module.Finite.trans E F
    let : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K E F
    refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro i
    induction i using Fin.lastCases with
    | last =>
      refine ⟨algebraMap E F w₀, ?_⟩
      rw [← map_pow, ← map_sub, hw₀, ← IsScalarTower.algebraMap_apply]
    | cast j =>
      obtain ⟨w, hw⟩ := hF j
      exact ⟨w, by rw [hw, ← IsScalarTower.algebraMap_apply]⟩

/-- **The shared extension: one finite separable extension splitting every member's class.**

The existential sits outside `∀ i`, which is the point.  Nothing here is about valuations — the
classes are elements of `K`, so the extension is built from them alone, before any member of the
family is examined. -/
theorem exists_artinSchreierSplitting_forall (K : Type u) [Field K] (p : ℕ) (hp : 1 < p)
    [CharP K p] {ι : Type*} [Finite ι] (ξ : ι → K) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E)
      (_ : Algebra.IsSeparable K E),
      ∀ i, ∃ w : E, w ^ p - w = algebraMap K E (ξ i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨E, _, _, _, _, hE⟩ :=
    exists_artinSchreierSplitting_fin p hp n K inferInstance inferInstance (fun j => ξ (e.symm j))
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, fun i => ?_⟩
  simpa only [Equiv.symm_apply_apply] using hE (e i)

end Splitting

/-! ### Combinations of parameters, wired to the family

An `𝔽_p`-combination of parameters presented
at depth `N` with bounds `n i ≤ N` is again presented at depth `N` with bound `N`, so the reduction
and the ramification dichotomy apply to it with `n ≤ N` re-established by `le_rfl`.  Ferocity is
excluded and no minimality is needed. -/

section Combination

/-- The pole parts of a family in the bound shape combine into one numerator at depth `N`. -/
private theorem exists_frobeniusNumerator_of_combination
    {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [ExpChar A p] (π : A) (hπ : Irreducible π)
    {ι : Type*} (s : Finset ι) (c nBound : ι → ℕ) (N : ℕ) (hN : ∀ i ∈ s, nBound i ≤ N)
    (α : ι → ℕ → A) (b : ι → A) (ξ : ι → K)
    (hξ : ∀ i ∈ s, ξ i = (algebraMap A K π)⁻¹ ^ nBound i *
      algebraMap A K (∑ j ∈ Finset.range (nBound i), α i j ^ (p ^ N) * π ^ j)
      + algebraMap A K (b i)) :
    ∃ β : ℕ → A, ∑ i ∈ s, (c i : K) * ξ i = (algebraMap A K π)⁻¹ ^ N *
      algebraMap A K (∑ j ∈ Finset.range N, β j ^ (p ^ N) * π ^ j)
        + algebraMap A K (∑ i ∈ s, (c i : A) * b i) :=
  exists_frobeniusNumerator_of_sum p N π
    ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπ.ne_zero) s c nBound N hN α b ξ hξ

/-- **Every `𝔽_p`-combination of the family's base classes reduces to a terminal representative at
the family-wide depth.**

`exists_frobeniusNumerator_of_sum` puts the combination in the bound shape at depth `N` and bound
`N`, and `exists_terminal_of_frobeniusNumerator` then iterates the pole reduction on it — the
depth hypothesis `n ≤ N` is `le_rfl` at that bound, which is what the family-wide depth is for.
The translate generates the same subalgebra, so this is a better presentation of one extension and
never a different extension. -/
theorem exists_terminal_of_combination
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [ExpChar A p]
    (π : A) (hπ : Irreducible π)
    {ι : Type*} (s : Finset ι) (nBound : ι → ℕ) (N : ℕ) (hN : ∀ i ∈ s, nBound i ≤ N)
    (α : ι → ℕ → A) (b : ι → A) (ξ : ι → K)
    (hξ : ∀ i ∈ s, ξ i = (algebraMap A K π)⁻¹ ^ nBound i *
      algebraMap A K (∑ j ∈ Finset.range (nBound i), α i j ^ (p ^ N) * π ^ j)
      + algebraMap A K (b i))
    (c : ι → ℕ) (z : L) (hz : z ^ p - z = algebraMap K L (∑ i ∈ s, (c i : K) * ξ i)) :
    ∃ (z' : L) (ξ' : K), z' ^ p - z' = algebraMap K L ξ' ∧
      Algebra.adjoin K {z'} = Algebra.adjoin K {z} ∧
      ((∃ a : A, ξ' = algebraMap A K a)
        ∨ ∃ (N' n' : ℕ) (β : ℕ → A) (b' : A), 0 < n' ∧ n' ≤ N' ∧ IsUnit (β 0) ∧ ¬ p ∣ n' ∧
            ξ' = (algebraMap A K π)⁻¹ ^ n' *
              algebraMap A K (∑ j ∈ Finset.range n', β j ^ (p ^ N') * π ^ j)
              + algebraMap A K b') := by
  obtain ⟨β, hβ⟩ := exists_frobeniusNumerator_of_combination p π hπ s c nBound N hN α b ξ hξ
  exact exists_terminal_of_frobeniusNumerator p π hπ N N le_rfl β
    (∑ i ∈ s, (c i : A) * b i) _ z (by rw [hz, hβ]) hβ

/-- **No `𝔽_p`-combination of the family's base classes is ferociously ramified.**

The Artin--Schreier extension of `K` generated by a combination is trivial, unramified with
separable residue extension, or totally ramified.  The residually inseparable fourth case of Tag
09F0 is excluded, and there is **no minimality hypothesis** — which is the whole point, since pole
order is not stable under combination while the pole *bound* is.

This is what makes the shared extension of `exists_artinSchreierSplitting_forall` a *controlled*
extension of `A`: it is generated by Artin--Schreier roots of classes each of which falls in this
trichotomy, and the trichotomy is what a ramification computation over it consumes. -/
theorem trivial_or_unramified_or_totallyRamified_of_combination
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p] [ExpChar A p]
    (π : A) (hπ : Irreducible π)
    {ι : Type*} (s : Finset ι) (nBound : ι → ℕ) (N : ℕ) (hN : ∀ i ∈ s, nBound i ≤ N)
    (α : ι → ℕ → A) (b : ι → A) (ξ : ι → K)
    (hξ : ∀ i ∈ s, ξ i = (algebraMap A K π)⁻¹ ^ nBound i *
      algebraMap A K (∑ j ∈ Finset.range (nBound i), α i j ^ (p ^ N) * π ^ j)
      + algebraMap A K (b i))
    (c : ι → ℕ) (z : L) (hz : z ^ p - z = algebraMap K L (∑ i ∈ s, (c i : K) * ξ i))
    (hgen : Algebra.adjoin K {z} = ⊤) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      trivial ∨ unramified ∨ totallyRamified := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨β, hβ⟩ := exists_frobeniusNumerator_of_combination p π hπ s c nBound N hN α b ξ hξ
  exact trivial_or_unramified_or_totallyRamified_of_frobeniusNumerator p hp π hπ N N le_rfl β
    (∑ i ∈ s, (c i : A) * b i) _ z (by rw [hz, hβ]) hgen hβ

end Combination

/-! ### The middle layer: a split constant class leaves an integral parameter -/

section MiddleLayer

/-- **Transfer of a primitive generator across a base change.**

If `M / L` is generated by `z` and `F / M` is generated by the image of `E`, then `F / E` is
generated by the image of `z`.  Both generation statements are `Algebra.adjoin`, and the content is
the nested induction: an element of `F` is a polynomial over `M` in the image of `E`, and each
coefficient is a polynomial over `L` in `z`.

This is what supplies `Algebra.adjoin E {z} = ⊤` to
`IsDiscreteValuationRing.isWeaklyUnramified_of_artinSchreier_parameter_integral` at a conjugate
factor, where what the factor hands over is generation in the *other* direction. -/
theorem adjoin_singleton_eq_top_of_adjoin_range
    {L M E F : Type*} [Field L] [Field M] [Field E] [Field F]
    [Algebra L M] [Algebra L E] [Algebra M F] [Algebra E F] [Algebra L F]
    [IsScalarTower L M F] [IsScalarTower L E F]
    (z : M) (hz : Algebra.adjoin L {z} = ⊤)
    (hgen : Algebra.adjoin M (Set.range (algebraMap E F)) = ⊤) :
    Algebra.adjoin E {algebraMap M F z} = ⊤ := by
  set S : Subalgebra E F := Algebra.adjoin E {algebraMap M F z} with hS
  have hM : ∀ m : M, algebraMap M F m ∈ S := by
    intro m
    have hm : m ∈ Algebra.adjoin L {z} := by rw [hz]; trivial
    induction hm using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl : y = z := hy
      exact Algebra.subset_adjoin rfl
    | algebraMap l =>
      rw [← IsScalarTower.algebraMap_apply L M F, IsScalarTower.algebraMap_apply L E F]
      exact S.algebraMap_mem _
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using S.mul_mem hx hy
  have key : ∀ x : F, x ∈ S := by
    intro x
    have hx : x ∈ Algebra.adjoin M (Set.range (algebraMap E F)) := by rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨e, rfl⟩ := hy; exact S.algebraMap_mem e
    | algebraMap m => exact hM m
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
  exact top_unique fun x _ => key x

/-- **The middle layer of the split-class solver: a constant class split in the base change leaves
a parameter integral over the middle ring.**

`M = L(z)` is Artin--Schreier with parameter `ξ + b`, `ξ` coming from a base field whose extension
`E` contains a root `w` of `ξ`.  Then over each conjugate factor `F` of `M ⊗[L] E` the element
`z - w` satisfies `x ^ p - x = b`, which is integral in `integralClosure B E`, so that factor
contributes ramification index one and `B → C` base changed along `E` is a weak solution.

This is where the degree-`p` solver
`IsDiscreteValuationRing.isWeakSolution_of_constant_artinSchreier_parameter` cannot be used and
why: it computes `ramificationIndex A A₁` from `Algebra.adjoin K {w} = ⊤`, and over a compositum of
two or more independent Artin--Schreier classes that hypothesis is false.  Nothing replaces the
computation — it is not needed, because at this layer the parameter is *integral* and the
ramification is one for that reason alone, with no arithmetic in the degrees. -/
theorem isWeakSolution_of_split_constant_artinSchreier_parameter
    (B C L M E : Type u)
    [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field L] [Field M] [Field E]
    [Algebra B C] [IsExtension B C]
    [Algebra B L] [Algebra C M] [Algebra B M] [Algebra L M]
    [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Module.Finite L E] [Algebra.IsSeparable L E]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    (ξ : L) (b : B) (z : M) (w : E)
    (hz : z ^ p - z = algebraMap L M ξ + algebraMap B M b)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (hw : w ^ p - w = algebraMap L E ξ) :
    ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} B C L M E, D.IsWeakSolution := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP M p := charP_of_injective_algebraMap (algebraMap L M).injective p
  apply exists_isWeakSolution_of_fieldFactor_ramification B C L M E
  intro Q F
  intros
  rename_i ι hsquare hgenF
  let R := integralClosure B E
  let _ : IsDiscreteValuationRing R :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L E).1
  let _ : IsFractionRing R E :=
    Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure B L E
  let _ : Algebra E F := ι.toRingHom.toAlgebra
  let _ : IsScalarTower L E F :=
    IsScalarTower.of_algebraMap_eq fun l => (ι.commutes l).symm
  let _ : CharP E p := charP_of_injective_algebraMap (algebraMap L E).injective p
  let _ : IsScalarTower R Q F := IsScalarTower.of_algebraMap_eq fun a => (hsquare a).symm
  have hinj : Function.Injective (algebraMap R Q) := by
    intro x y h
    apply Subtype.ext
    apply ι.injective
    change ι (x : E) = ι (y : E)
    rw [← hsquare x, ← hsquare y, h]
  let _ : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).mpr hinj
  let _ : IsLocalHom (algebraMap B Q) := by
    rw [IsScalarTower.algebraMap_eq B C Q]
    infer_instance
  have hcontr : (IsLocalRing.maximalIdeal Q).under R = IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := B)
    change ((IsLocalRing.maximalIdeal Q).under R |>.under B).IsMaximal
    rw [Ideal.under_under, Ideal.under_def, IsLocalRing.maximalIdeal_comap]
    infer_instance
  let _ : IsLocalHom (algebraMap R Q) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R Q)).out 5 1).mp hcontr
  let _ : IsExtension R Q := {}
  -- the translated generator and its integral parameter
  have hgv : Algebra.adjoin E {algebraMap M F z - algebraMap E F w} = ⊤ := by
    rw [adjoin_singleton_sub_algebraMap]
    exact adjoin_singleton_eq_top_of_adjoin_range z hgen hgenF
  let _ : CharP F p := charP_of_injective_algebraMap (algebraMap M F).injective p
  have hbF : algebraMap M F (algebraMap B M b)
      = algebraMap E F (algebraMap R E (algebraMap B R b)) := by
    rw [IsScalarTower.algebraMap_apply B L M, ← IsScalarTower.algebraMap_apply L M F,
      ← IsScalarTower.algebraMap_apply B R E, IsScalarTower.algebraMap_apply B L E,
      ← IsScalarTower.algebraMap_apply L E F]
  have hξF : algebraMap M F (algebraMap L M ξ) = algebraMap E F (algebraMap L E ξ) := by
    rw [← IsScalarTower.algebraMap_apply L M F, ← IsScalarTower.algebraMap_apply L E F]
  have hv : (algebraMap M F z - algebraMap E F w) ^ p - (algebraMap M F z - algebraMap E F w)
      = algebraMap E F (algebraMap R E (algebraMap B R b)) := by
    have h1 := congrArg (algebraMap M F) hz
    have h2 := congrArg (algebraMap E F) hw
    simp only [map_sub, map_pow, map_add] at h1 h2
    rw [hξF, hbF] at h1
    rw [sub_pow_char]
    linear_combination h1 - h2
  have hweakRQ : IsWeaklyUnramified R Q :=
    isWeaklyUnramified_of_artinSchreier_parameter_integral R Q E F p hp
      (algebraMap R E (algebraMap B R b)) _ hv hgv ⟨algebraMap B R b, rfl⟩
  rw [← IsDiscreteValuationRing.ramificationIndex_eq_ramificationIdx R Q]
  exact hweakRQ

end MiddleLayer

/-! ### The producer -/

section Producer

/-- **The one obligation the constant-numerator branch leaves open, named at the point it is
needed.**

A member whose Artin--Schreier layer has a **constant** pole part `ξ ∈ K` and an integral part
`b : B`, that pole class acquiring a root in the **prescribed** finite separable `K₂ / K`, is
solved by `K₂`.

Three things about the shape, each deliberate.

*It is prescribed, not produced.*  `K₂` is a parameter and the conclusion speaks about that one
field, so nothing here combines two independently chosen extensions.  The production of `K₂` is
`exists_artinSchreierSplitting_forall`, above, and it happens once for the whole family; this
obligation is then checked at each member against that one field.  So naming this gap does not
re-introduce the amalgamation the route forbids.

*It is the constant-numerator solver freed of its degree-`p` hypothesis.*
`IsDiscreteValuationRing.isWeakSolution_of_constant_artinSchreier_parameter` proves the same
conclusion when `K₂ = K(w)` — it asks for `Algebra.adjoin K {w} = ⊤`, a unit numerator at a pole
order prime to `p`, total ramification of `K₂ / K` and `ramificationIndex A C = p`.  A family of
two or more independent classes cannot be served by a degree-`p` extension, so the compositum is
unavoidable and `Algebra.adjoin K {w} = ⊤` is exactly what fails for it.

*The route, which does not go through the compositum's ramification.*  That proof computes
`ramificationIndex A A₁` from the degree, and over a compositum that computation is not available.
It is also not needed, because the middle ring does the work instead: over each factor `E` of
`(L ⊗[K] K₂) ⧸ nilradical` the pole class is split, so the layer there is Artin--Schreier with
parameter `b`, which is *integral* in `integralClosure B E`, hence
`integralClosure B E → integralClosure C (M · E)` is weakly unramified; and
`integralClosure A K₂ → integralClosure B E` is weakly unramified because `A → B` is and `κ_A` is
perfect, `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` holding for **every**
finite base change.  Composing the two gives the weak solution, and
`isWeakSolution_of_prime_layer_of_forall_factor` is the composition.  What that needs and the tree
does not yet export is `ArtinSchreier.lean`'s
`exists_isWeakSolution_of_fieldFactor_ramification` and
`isWeaklyUnramified_of_artinSchreier_parameter_integral`, both currently `private`.

So `trivial_or_unramified_or_totallyRamified_of_combination` above is **not** an input to this gap.
It is the statement that the produced `K₂` is a controlled extension of `A` — needed by
whatever consumes `K₂` further up, but not by this obligation.

*`_hterminal` is untouched.*  This gap is taken as a hypothesis rather than closed by
narrowing the family's terminal alternative. -/
abbrev SplitConstantClassSolvable (p : ℕ) : Prop :=
  ∀ (A B C K L M K₂ : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₂]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [Algebra K K₂] [Algebra A K₂] [IsScalarTower A K K₂]
    [Module.Finite K K₂] [Algebra.IsSeparable K K₂]
    [CharP K p] [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M],
    IsWeaklyUnramified A B →
    ∀ (ξ : K) (b : B) (z : M) (w : K₂),
      z ^ p - z = algebraMap K M ξ + algebraMap B M b →
      Algebra.adjoin L {z} = ⊤ →
      w ^ p - w = algebraMap K K₂ ξ →
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂, D.IsWeakSolution

/-- The split constant class is solved by the prescribed separable base extension. -/
theorem splitConstantClassSolvable (p : ℕ) [Fact p.Prime] :
    SplitConstantClassSolvable.{u} p := by
  classical
  intro A B C K L M K₂
  intros
  rename_i hweak ξ b z w hz hgen hw
  let DAB := canonicalBaseChange A B K L K₂
  let DAC := canonicalBaseChange A C K M K₂
  have hDAB : DAB.IsWeakSolution :=
    isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField
      A B K L K₂ DAB hweak
  let _ : CharP L p :=
    charP_of_injective_algebraMap (algebraMap K L).injective p
  let := DAB.commRingL₁
  let := DAB.algebraKL₁
  let := DAB.algebraLL₁
  let := DAB.algebraK₁L₁
  let := DAB.isScalarTowerKLL₁
  let := DAB.isScalarTowerKK₁L₁
  obtain ⟨n, E, hE, hLE, hK₂E, hBE, hAE, hBLE, hABE, hAK₂E, hfinE,
      hsepE, hn, e, he⟩ := exists_finiteSeparableFieldFactors_of_package A B K L K₂ DAB
  let := hE
  let := hLE
  let := hK₂E
  let := hBE
  let := hAE
  let := hBLE
  let := hABE
  let := hAK₂E
  let := hfinE
  let := hsepE
  have hz' : z ^ p - z =
      algebraMap L M (algebraMap K L ξ) + algebraMap B M b := by
    rw [← IsScalarTower.algebraMap_apply K L M]
    exact hz
  have hwE : ∀ i, (algebraMap K₂ (E i) w) ^ p - algebraMap K₂ (E i) w =
      algebraMap L (E i) (algebraMap K L ξ) := by
    intro i
    rw [← map_pow, ← map_sub, hw]
    calc
      _ = e (algebraMap K₂ DAB.L₁ (algebraMap K K₂ ξ)) i :=
        (he i (algebraMap K K₂ ξ)).symm
      _ = e (algebraMap L DAB.L₁ (algebraMap K L ξ)) i :=
        congrArg (fun x => e x i) (by
          rw [← IsScalarTower.algebraMap_apply K K₂ DAB.L₁,
            ← IsScalarTower.algebraMap_apply K L DAB.L₁])
      _ = _ := congrArg (fun f => f i) (e.commutes (algebraMap K L ξ))
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M,
      IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]
  have hDBC : ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
      B C L M (E i), D.IsWeakSolution := fun i =>
    isWeakSolution_of_split_constant_artinSchreier_parameter
      B C L M (E i) p (Fact.out : p.Prime) (algebraMap K L ξ) b z
      (algebraMap K₂ (E i) w) hz' hgen (hwE i)
  choose DBC hDBC using hDBC
  exact ⟨DAC, isWeakSolution_of_prime_layer_of_forall_factor
    A B C K L M K₂ DAB DAC n E hn e DBC hDAB hDBC⟩

/-- **A finite family of base-field Artin--Schreier classes is solved over one extension.**

Each member has a parameter of the form `algebraMap K (L i) (ξ i) + algebraMap (B i) (M i)
(b i)`: its polar class comes from the common base field and its remaining term is integral in the
member.  One finite separable extension of `K` is chosen which contains an Artin--Schreier root of
every `ξ i`; `splitConstantClassSolvable` then checks every member against that same extension.

This is the direct consumer of the all-conjugate normalization in `EppSharedFactorSync`: unlike the
Frobenius-presentation wrapper below, it does not ask how the base parameters were constructed. -/
theorem exists_finite_extension_forall_isWeakSolution_of_base_parameter_add_integral
    (p : ℕ) [Fact p.Prime]
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP K p] [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (ξ : ι → K) (b : ∀ i, B i) (z : ∀ i, M i)
    (hz : ∀ i, z i ^ p - z i =
      algebraMap K (M i) (ξ i) + algebraMap (B i) (M i) (b i))
    (hgen : ∀ i, Algebra.adjoin (L i) {z i} = ⊤) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
        A (C i) K (M i) K₂, D.IsWeakSolution := by
  classical
  obtain ⟨K₂, hK₂, hKK₂, hfin, hsep, hroot⟩ :=
    exists_artinSchreierSplitting_forall K p (Fact.out : p.Prime).one_lt ξ
  let := hK₂
  let := hKK₂
  let := hfin
  let := hsep
  let : Algebra A K₂ := ((algebraMap K K₂).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K K₂ := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  obtain ⟨w, hw⟩ := hroot i
  exact splitConstantClassSolvable p A (B i) (C i) K (L i) (M i) K₂
    (hweak i) (ξ i) (b i) (z i) w (hz i) (hgen i) hw

/-- **The all-conjugate constant-Laurent endgame.**

Deep roots supplied by the shared residue absorption normalize every Laurent parameter to a sum of
a common-base parameter and an integral member parameter.  The preceding theorem then splits all
base parameters in one finite extension and solves every member over that same extension. -/
theorem exists_finite_extension_forall_isWeakSolution_of_constant_laurent
    (p : ℕ) [Fact p.Prime]
    (ι : Type u) [Finite ι]
    (A K : Type u) (F B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, Field (F i)]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP K p] [∀ i, CharP (B i) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (N : ℕ) (pi : A) (hpi : Irreducible pi)
    (f : ∀ i, F i →+* IsLocalRing.ResidueField (B i))
    (sigma : ∀ i, F i → B i)
    (hsigma : ∀ i x, IsLocalRing.residue (B i) (sigma i x) = f i x)
    (sq : ∀ i, F i →+* B i ⧸ (IsLocalRing.maximalIdeal (B i)) ^ N)
    (hsq : ∀ i x, Ideal.Quotient.mk _ (sigma i x) = sq i x)
    (coeff rootCoeff : ∀ i, ℕ → F i)
    (hrootCoeff : ∀ i k, k ∈ Finset.range N →
      rootCoeff i k ^ (p ^ N) = coeff i k)
    (rootBase : ι → ℕ → IsLocalRing.ResidueField A)
    (hrootBase : ∀ i k, k ∈ Finset.range N →
      algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (B i)) (rootBase i k) = f i (rootCoeff i k))
    (xi : ∀ i, L i) (b : ∀ i, B i)
    (hexp : ∀ i, xi i = (∑ k ∈ Finset.range N,
      algebraMap (B i) (L i) (sigma i (coeff i k)) *
        (algebraMap (B i) (L i) (algebraMap A (B i) pi))⁻¹ ^ (N - k)) +
          algebraMap (B i) (L i) (b i))
    (z : ∀ i, M i)
    (hz : ∀ i, z i ^ p - z i = algebraMap (L i) (M i) (xi i))
    (hgen : ∀ i, Algebra.adjoin (L i) {z i} = ⊤) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
        A (C i) K (M i) K₂, D.IsWeakSolution := by
  classical
  obtain ⟨xi0, b', hxi⟩ :=
    exists_forall_base_parameter_add_integral_of_constant_laurent
      (iota := ι) (R := A) (K := K) (F := F) (S := B) (L := L)
      p N pi hpi hweak f sigma hsigma sq hsq coeff rootCoeff hrootCoeff rootBase hrootBase
        xi b hexp
  refine exists_finite_extension_forall_isWeakSolution_of_base_parameter_add_integral
    p ι A K B C L M hweak xi0 b' z (fun i => ?_) hgen
  rw [hz i, hxi i, map_add, IsScalarTower.algebraMap_apply K (L i) (M i),
    IsScalarTower.algebraMap_apply (B i) (L i) (M i)]

/-- **The producer of `Stacks.EppTheorem.FamilyPrimeDegreeSolvable`, for a family presented in the
constant-numerator Frobenius bound shape.**

This is O2's third disjunct.  The telescope is `FamilyPrimeDegreeSolvable`'s verbatim — nothing
added to it and nothing removed, `_hterminal` in particular unnarrowed — plus two binders, which
are what this branch owes upstream:

* `hchar : CharP K p`.  The presentation is an Artin--Schreier presentation, so the branch lives in
  equal characteristic; `FamilyPrimeDegreeSolvable` carries only `CharP (ResidueField A) p` because
  its other branches do not.
* `hpresent`, the family-wide constant-numerator presentation: one uniformizer `π` of `A`, one
  depth `N`, per-member pole bounds `nBound i ≤ N`, base coefficients `α i j : A`, integral parts
  `b i : B i`, and an Artin--Schreier generator of each layer whose pole part is the depth-`N`
  Frobenius numerator over `A`.  The depth and the uniformizer are shared across the family and
  fixed before any member is examined, which is the same quantifier discipline as `∃ K₂` outside
  `∀ i`; a per-member depth would be the amalgamation in another costume.

The proof is three lines of mathematics.  The pole parts `ξ i` are elements of `K`, so
`exists_artinSchreierSplitting_forall` produces **one** finite separable `K₂ / K` in which all of
them acquire Artin--Schreier roots, computed from the family's data alone.  Each member is then
checked against that one `K₂` by `SplitConstantClassSolvable`.  No member's extension is ever
combined with another's.

The `nBound i ≤ N` form is weaker than fixing `N := Finset.univ.sup nBound`, which is the intended
discharge, and weaker is what a hypothesis should be. -/
theorem familyPrimeDegreeSolvable_of_frobeniusPresentation (p : ℕ) [Fact p.Prime]
    (hgap : SplitConstantClassSolvable.{u} p)
    (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_hterminal : ∀ i,
      IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime)
    (hchar : CharP K p)
    (hpresent : ∃ (π : A) (N : ℕ) (nBound : ι → ℕ) (α : ι → ℕ → A) (b : ∀ i, B i)
        (z : ∀ i, M i),
        Irreducible π ∧ (∀ i, nBound i ≤ N) ∧
        ∀ i, Algebra.adjoin (L i) {z i} = ⊤ ∧
          z i ^ p - z i = algebraMap K (M i)
              ((algebraMap A K π)⁻¹ ^ nBound i *
                algebraMap A K (∑ j ∈ Finset.range (nBound i),
                  α i j ^ (p ^ N) * π ^ j))
            + algebraMap (B i) (M i) (b i)) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution := by
  classical
  let := hchar
  obtain ⟨π, N, nBound, α, b, z, hπ, hN, hmem⟩ := hpresent
  set ξ : ι → K := fun i => (algebraMap A K π)⁻¹ ^ nBound i *
    algebraMap A K (∑ j ∈ Finset.range (nBound i), α i j ^ (p ^ N) * π ^ j) with hξ
  obtain ⟨K₂, _, _, _, _, hroot⟩ :=
    exists_artinSchreierSplitting_forall K p (Fact.out : p.Prime).one_lt ξ
  let : Algebra A K₂ := ((algebraMap K K₂).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K K₂ := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨K₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  obtain ⟨w, hw⟩ := hroot i
  exact hgap A (B i) (C i) K (L i) (M i) K₂ (_hweak i) (ξ i) (b i) (z i) w
    (hmem i).2 (hmem i).1 hw

/-- **The constant-numerator presentation, as one named Prop about the whole class of families.**

This is `hpresent` of `familyPrimeDegreeSolvable_of_frobeniusPresentation` and `hchar` alongside
it, universally quantified over the families `FamilyPrimeDegreeSolvable` quantifies over, so that
the producer below can conclude that abbrev *literally*.  It is what the wild branch's preparation
theorems owe the constant branch: their output is a Laurent presentation with the wild set empty,
and the residue absorption turns that into this. -/
abbrev FamilyFrobeniusPresentation (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_hterminal : ∀ i,
      IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime),
    CharP K p ∧
      ∃ (π : A) (N : ℕ) (nBound : ι → ℕ) (α : ι → ℕ → A) (b : ∀ i, B i) (z : ∀ i, M i),
        Irreducible π ∧ (∀ i, nBound i ≤ N) ∧
        ∀ i, Algebra.adjoin (L i) {z i} = ⊤ ∧
          z i ^ p - z i = algebraMap K (M i)
              ((algebraMap A K π)⁻¹ ^ nBound i *
                algebraMap A K (∑ j ∈ Finset.range (nBound i),
                  α i j ^ (p ^ N) * π ^ j))
            + algebraMap (B i) (M i) (b i)

/-- **`Stacks.EppTheorem.FamilyPrimeDegreeSolvable p` itself, from the two obligations this branch
  owes.**

O2's third disjunct, at the shape `familyTowerSolvable_of_forall_terminal` consumes, modulo exactly
two named hypotheses: the constant-numerator presentation, which the wild branch's preparation and
the residue absorption owe it, and `SplitConstantClassSolvable`, the ramification computation over
the compositum.  Nothing else is assumed and `_hterminal` is not narrowed.

This is the declaration that gives the abbrev a producer.  Until this commit it was consumed only
as a hypothesis, by `familyTowerSolvable_of_forall_terminal`, and produced nowhere. -/
theorem familyPrimeDegreeSolvable_of_forall_frobeniusPresentation (p : ℕ) [Fact p.Prime]
    (hgap : SplitConstantClassSolvable.{u} p)
    (hpresent : FamilyFrobeniusPresentation.{u} p) :
    FamilyPrimeDegreeSolvable.{u} p := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ hepp hterminal
  obtain ⟨hchar, hpres⟩ := hpresent ι A K B C L M hweak hepp hterminal
  exact familyPrimeDegreeSolvable_of_frobeniusPresentation p hgap ι A K B C L M hweak hepp
    hterminal hchar hpres

end Producer

end Stacks.EppTheorem

end
