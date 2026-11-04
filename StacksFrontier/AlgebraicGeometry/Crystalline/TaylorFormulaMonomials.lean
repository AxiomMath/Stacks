module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormula
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexed
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.PartialDerivative

/-!
# Taylor's formula in `B`, for the divided power polynomial algebra of [Stacks, Tag 07JH]

`Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorFormula.lean` reduces the corrected Taylor
comparison predicate `Crystalline.IsTwistedTaylorComparison` to one hypothesis, `htay`: **Taylor's
formula in `B`**,

`f(a) = ∑_J g(∂_J a) ξ^{[J]}`,

a statement about the two rings, the two divided power maps and the coordinate operators of `D`,
with no module and no connection in it.  **This module proves that hypothesis** for the divided
power polynomial algebra `D = A⟨x_i : i ∈ W⟩`, and so inhabits the predicate there.

Two things stood between the library and the formula, and neither was a missing idea.  The first
was the operators `∂_J : D → D`, which did not exist as declarations; they are now
`DividedPowers.dividedPowerPolynomialPartial` of
`StacksFrontier/RingTheory/DividedPowers/Polynomial/PartialDerivative.lean`, built on the divided
power monomial basis `DividedPowers.dividedPowerPolynomialMonomialBasis`.  The second was the
formula itself, whose content on a divided power monomial is the multi-index binomial formula
`DividedPowers.prod_dpow_add_support`, already proved:

`f(x^{[K]}) = ∏_i (ξ_i + g(x_i))^{[k_i]} = ∑_{J + J' = K} ξ^{[J]} g(x^{[J']})`,

and `x^{[J']} = x^{[K - J]} = ∂_J(x^{[K]})`.  From the monomials the formula passes to every `a`
by linearity over the coefficient ring, which is where the basis is used a second time.

## Main definitions

* `Crystalline.polynomialDelta` and `Crystalline.polynomialDeltaPow` — the operators `∂_i` and
  `∂_J` of the divided power polynomial algebra, with its divided power ring's own carrier as
  domain, which is the shape `Crystalline.IsThetaMonomialFamily` and
  `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` ask for.

## Main results

* `Crystalline.map_taylorMonomial_eq_sum` — **Taylor's formula on a divided power monomial**, for
  any two divided power maps `f, g : D → B` and any family `x` in the divided power ideal of `D`:

  `f(x^{[K]}) = ∑_{J + J' = K} ξ^{[J]} g(x^{[J']})`,   `ξ_i = f(x_i) - g(x_i)`.

  Nothing about polynomials enters; this is the multi-index binomial formula read through the two
  maps, and it holds in any divided power ring.
* `Crystalline.map_monomial_eq_sum_partial` — the same for the divided power polynomial algebra,
  with the second factor recognised as `∂_J(x^{[K]})` and the sum reindexed over the multi-indices
  `J ≤ K`, which is the shape the hypothesis `htay` has.
* `Crystalline.taylorFormula_polynomial` — **Taylor's formula in `B`**, for every `a` of the
  divided power polynomial algebra, with its sum finite.  This is `htay`, proved.
* `Crystalline.isThetaMonomialFamily_partial` — the operators `∂_J` are a composite coordinate
  operator family in the sense of `Crystalline.IsThetaMonomialFamily`, which is the hypothesis
  `hfamD` of the reduction, discharged.
* `Crystalline.exists_isTwistedTaylorComparison_dividedPowerPolynomial` — **the corrected Taylor
  comparison predicate of [Stacks, Tag 07JH] is inhabited for the divided power polynomial
  algebra**, at the coordinate family `ξ_i = f(x_i) - g(x_i)` of
  `Crystalline.SecondDividedPowerMap.diffFamily`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Nothing here is about crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`; the tag's
statement is `Crystalline.GlobalCrystallineSituation.SmallSite.Equivalence07JH`, still a
proposition, and `Crystalline.equivalence07JH_of_isEquivalence_functor` splits it into three open
things of which none is touched here.

**What is closed is `htay`**, the one hypothesis
`Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` was left carrying, and with it
`hfamD`.  What
`Crystalline.exists_isTwistedTaylorComparison_dividedPowerPolynomial` still carries is named in
its docstring and is in each case either the source's own or a property of the module `M`:

* `hfamM`, `hthAdd`, `hleib` — that the module's coordinate operators form a composite family, are
  additive, and satisfy the first-order Leibniz rule against `∂_i`.  These are discussed in
  `StacksFrontier/AlgebraicGeometry/Crystalline/TaylorFormula.lean`; `hleib` is the Leibniz rule of
  `Crystalline.CompletedConnection.leibniz` read in the coordinates, and it is now stated against
  a *concrete* operator rather than an abstract one, which it could not be before this module.
* `hg` — that the structure map `D → B` is the divided power map `g`.  Both maps of the source are
  divided power homomorphisms; the single `Algebra D B` instance of the predicate records only
  that `g` is a ring map, so the divided power structure on it has to be supplied.
* `hfg` — that `f` and `g` agree on the coefficient ring `A`.  This is the source's requirement
  that both are maps over the base, and it is strictly weaker than asking either to be an
  `A`-algebra map.  It is **not** a weakening of anything, and it is what the proof consumes: the
  two sides of the formula are computed from the monomial case by expanding `a` over the
  coefficient ring, and they differ by `∑_K (f - g)(c_K) · f(x^{[K]})`, which `hfg` is exactly
  what kills.
* `hpB` — nilpotence of `p` in `B`, part of the definition of a divided power thickening in
  [Stacks, Tag 07HM].
* `hfin` — the source's own "the sum is finite!", which
  `Crystalline.finite_thetaPow_notMem_pPowSmul` gives from the quasi-nilpotence condition (07JE).

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

open Finset.HasAntidiagonal

universe u uI w

namespace Crystalline

section Monomial

variable {D : DividedPowerRing.{u}} {B : DividedPowerRing.{u}} {ι : Type uI} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A divided power map carries a divided power monomial to the divided power monomial of the
images**: `f(x^{[K]}) = f(x)^{[K]}`, for a family `x` lying in the divided power ideal of the
source.  This is `DividedPowers.DPMorphism.dpow_comp` taken over the finitely many factors of
`Crystalline.taylorMonomial`. -/
theorem map_taylorMonomial (f : DividedPowers.DPMorphism D.dividedPowers B.dividedPowers)
    {x : ι → (D : Type u)} (hx : ∀ i, x i ∈ D.ideal) (K : ι →₀ ℕ) :
    f (taylorMonomial D x K) = taylorMonomial B (fun i ↦ f (x i)) K := by
  show f.toRingHom (taylorMonomial D x K) = _
  rw [taylorMonomial, taylorMonomial, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ (f.dpow_comp (x i) (hx i)).symm

/-- A divided power map carries the divided power ideal of its source into that of its target. -/
theorem map_mem_ideal (f : DividedPowers.DPMorphism D.dividedPowers B.dividedPowers)
    {a : (D : Type u)} (ha : a ∈ D.ideal) : f a ∈ B.ideal :=
  f.ideal_comp (Ideal.mem_map_of_mem _ ha)

/-- **Taylor's formula on a divided power monomial of [Stacks, Tag 07JH]**: for two divided power
maps `f, g : D → B` and a family `x` in the divided power ideal of `D`,

`f(x^{[K]}) = ∑_{J + J' = K} ξ^{[J]} g(x^{[J']})`,   where `ξ_i = f(x_i) - g(x_i)`.

Nothing about polynomials enters, and no hypothesis beyond `x` lying in the ideal: the identity is
the multi-index binomial formula `DividedPowers.prod_dpow_add_support` applied to the splitting
`f(x_i) = ξ_i + g(x_i)`, both summands lying in the divided power ideal of `B` because `f` and `g`
carry the ideal into it.  It is the whole mathematical content of Taylor's formula; what the rest
of this module adds is the identification of `g(x^{[J']})` with `g(∂_J x^{[K]})` and the passage
from the monomials to a general element. -/
theorem map_taylorMonomial_eq_sum
    (f g : DividedPowers.DPMorphism D.dividedPowers B.dividedPowers)
    {x : ι → (D : Type u)} (hx : ∀ i, x i ∈ D.ideal) (K : ι →₀ ℕ) :
    f (taylorMonomial D x K) =
      ∑ P ∈ antidiagonal K,
        taylorMonomial B (fun i ↦ f (x i) - g (x i)) P.1 * g (taylorMonomial D x P.2) := by
  have hgm : ∀ i, g (x i) ∈ B.ideal := fun i ↦ map_mem_ideal g (hx i)
  have hxi : ∀ i, f (x i) - g (x i) ∈ B.ideal := fun i ↦
    Ideal.sub_mem _ (map_mem_ideal f (hx i)) (hgm i)
  rw [map_taylorMonomial f hx K]
  have hfun : (fun i ↦ f (x i)) = fun i ↦ (f (x i) - g (x i)) + g (x i) :=
    funext fun i ↦ (sub_add_cancel _ _).symm
  rw [hfun, taylorMonomial, B.dividedPowers.prod_dpow_add_support hxi hgm K]
  exact Finset.sum_congr rfl fun P _ ↦ by
    rw [map_taylorMonomial g hx P.2, taylorMonomial, taylorMonomial]

end Monomial

section Polynomial

open DividedPowers

/-- **The divided power monomial of the variables is the divided power polynomial monomial.**
The divided powers induced on the divided power polynomial algebra send a variable to its divided
power monomial (`DividedPowers.setIndexedDividedPowerPolynomialDividedPowers_dpow_variable`), so
the product `Crystalline.taylorMonomial` takes over the support of `K` is
`DividedPowers.dividedPowerPolynomialMonomial`. -/
theorem taylorMonomial_variable (A : DividedPowerRing.{u}) {W : Type u} (K : W →₀ ℕ) :
    taylorMonomial (setIndexedDividedPowerPolynomialDividedPowerRing A W)
        (fun i ↦ dividedPowerPolynomialVariable A i) K =
      dividedPowerPolynomialMonomial A K := by
  show ∏ i ∈ K.support, _ = _
  rw [dividedPowerPolynomialMonomial, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simpa [setIndexedDividedPowerPolynomialDividedPowerRing,
    dividedPowerPolynomialVariableMonomial] using
    setIndexedDividedPowerPolynomialDividedPowers_dpow_variable A i (K i)

/-- A variable lies in the divided power ideal of the divided power polynomial ring, which is what
`Crystalline.map_taylorMonomial_eq_sum` requires of the coordinate family. -/
theorem variable_mem_ideal (A : DividedPowerRing.{u}) {W : Type u} (i : W) :
    dividedPowerPolynomialVariable A i ∈
      (setIndexedDividedPowerPolynomialDividedPowerRing A W).ideal :=
  variable_mem_polynomialIdeal A i

/-- **The first-order divided power partial derivative `∂_i` of the divided power polynomial
algebra**, with the divided power *ring*'s own carrier for its domain and codomain.  This is
`DividedPowers.dividedPowerPolynomialPartial` at the multi-index `Finsupp.single i 1`; the
repackaging is what lets it be the `delta` of `Crystalline.IsThetaMonomialFamily`, whose operators
act on the carrier. -/
noncomputable def polynomialDelta (A : DividedPowerRing.{u}) (W : Type u) [DecidableEq W] (i : W)
    (y : (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)) :
    (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) :=
  dividedPowerPolynomialPartial (A : Type u) W (Finsupp.single i 1) y

/-- **The iterated divided power partial derivative `∂_J` of the divided power polynomial
algebra**, with the divided power ring's own carrier for its domain and codomain; the `deltaPow`
of `Crystalline.IsThetaMonomialFamily`.  On the divided power monomials it is
`∂_J(x^{[K]}) = x^{[K - J]}` for `J ≤ K` and `0` otherwise. -/
noncomputable def polynomialDeltaPow (A : DividedPowerRing.{u}) (W : Type u) [DecidableEq W]
    (J : W →₀ ℕ) (y : (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)) :
    (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) :=
  dividedPowerPolynomialPartial (A : Type u) W J y

variable {A : DividedPowerRing.{u}} {W : Type u} [DecidableEq W] {B : DividedPowerRing.{u}}

/-- The first components of the antidiagonal of a multi-index `K` are exactly the multi-indices
below `K`.  This is the reindexing that turns the sum over `J + J' = K` of Taylor's formula into a
sum over `J ≤ K`, which is the shape with `∂_J` in it. -/
theorem mem_image_fst_antidiagonal_iff {J K : W →₀ ℕ} :
    J ∈ (antidiagonal K).image Prod.fst ↔ J ≤ K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦
    Finset.mem_image.mpr ⟨(J, K - J), mem_antidiagonal.mpr (add_tsub_cancel_of_le h), rfl⟩⟩
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp h
  exact le_of_le_of_eq le_self_add (mem_antidiagonal.mp hP)

omit [DecidableEq W] in
/-- **Taylor's formula on a divided power monomial, with the partial derivatives in it**:

`f(x^{[K]}) = ∑_{J ∈ t} g(∂_J x^{[K]}) ξ^{[J]}`

for any finite index set `t` containing the multi-indices below `K`.  This is
`Crystalline.map_taylorMonomial_eq_sum` with `x^{[K - J]}` recognised as `∂_J(x^{[K]})` by
`DividedPowers.dividedPowerPolynomialPartial_monomial_of_le`, reindexed along the first projection
of the antidiagonal, and extended to `t`: the extra multi-indices contribute nothing because `∂_J`
annihilates `x^{[K]}` when `J ≰ K`.  The freedom in `t` is what makes the formula addible over the
monomials of a general element. -/
theorem map_monomial_eq_sum_partial
    (f g : DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowerRing A W).dividedPowers B.dividedPowers)
    (K : W →₀ ℕ) (t : Finset (W →₀ ℕ)) (ht : ∀ J ≤ K, J ∈ t) :
    f (dividedPowerPolynomialMonomial A K) =
      ∑ J ∈ t, g (dividedPowerPolynomialPartial A W J (dividedPowerPolynomialMonomial A K)) *
        taylorMonomial B (fun i ↦ f (dividedPowerPolynomialVariable A i) -
          g (dividedPowerPolynomialVariable A i)) J := by
  classical
  set xi : W → (B : Type u) := fun i ↦ f (dividedPowerPolynomialVariable A i) -
    g (dividedPowerPolynomialVariable A i)
  set H : (W →₀ ℕ) → (B : Type u) := fun J ↦
    g (dividedPowerPolynomialPartial A W J (dividedPowerPolynomialMonomial A K)) *
      taylorMonomial B xi J with hH
  have hx : ∀ i : W, dividedPowerPolynomialVariable A i ∈
      (setIndexedDividedPowerPolynomialDividedPowerRing A W).ideal := variable_mem_ideal A
  have hstep := map_taylorMonomial_eq_sum f g hx K
  rw [taylorMonomial_variable A K] at hstep
  have hinj : ∀ P ∈ antidiagonal K, ∀ P' ∈ antidiagonal K,
      Prod.fst P = Prod.fst P' → P = P' := by
    intro P hP P' hP' hfst
    have h1 : P.1 + P.2 = K := mem_antidiagonal.mp hP
    have h2 : P'.1 + P'.2 = K := mem_antidiagonal.mp hP'
    refine Prod.ext hfst (add_right_injective P.1 ?_)
    show P.1 + P.2 = P.1 + P'.2
    rw [h1, hfst, h2]
  have hcongr : ∀ P ∈ antidiagonal K,
      taylorMonomial B xi P.1 *
          g (taylorMonomial (setIndexedDividedPowerPolynomialDividedPowerRing A W)
            (fun i ↦ dividedPowerPolynomialVariable A i) P.2) = H P.1 := by
    intro P hP
    have hsum : P.1 + P.2 = K := mem_antidiagonal.mp hP
    have hle : P.1 ≤ K := le_of_le_of_eq le_self_add hsum
    have h2 : P.2 = K - P.1 := by rw [← hsum, add_tsub_cancel_left]
    rw [hH, taylorMonomial_variable A P.2, h2,
      ← dividedPowerPolynomialPartial_monomial_of_le A W hle, mul_comm]
  have himg : ∑ J ∈ (antidiagonal K).image Prod.fst, H J = ∑ P ∈ antidiagonal K, H P.1 :=
    Finset.sum_image hinj
  have hext : ∑ J ∈ (antidiagonal K).image Prod.fst, H J = ∑ J ∈ t, H J := by
    refine Finset.sum_subset (fun J hJ ↦ ht J (mem_image_fst_antidiagonal_iff.mp hJ))
      fun J _ hJ ↦ ?_
    have hzero : @Eq (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)
        (dividedPowerPolynomialPartial A W J (dividedPowerPolynomialMonomial A K)) 0 :=
      dividedPowerPolynomialPartial_monomial_of_not_le A W
        (fun h ↦ hJ (mem_image_fst_antidiagonal_iff.mpr h))
    simp only [hH]
    rw [hzero, show g (0 : (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)) = 0
      from map_zero g.toRingHom, zero_mul]
  rw [hstep, Finset.sum_congr rfl hcongr, ← himg, hext]

omit [DecidableEq W] in
/-- **Taylor's formula in `B`, for the divided power polynomial algebra**: for two divided power
maps `f, g : A⟨x_i⟩ → B` agreeing on the coefficient ring `A` and every element `a`,

`f(a) = ∑_{J ∈ t} g(∂_J a) ξ^{[J]}`,   `ξ_i = f(x_i) - g(x_i)`,

with `t` finite and every term outside `t` zero.

This is the hypothesis `htay` of
`Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula`, proved.  The two ingredients are
the monomial case `Crystalline.map_monomial_eq_sum_partial` and the divided power monomial basis
`DividedPowers.dividedPowerPolynomialMonomialBasis`, over which both sides are additive and
`A`-homogeneous; the index set is the union over the monomials occurring in `a` of the
multi-indices below them, and `∂_J a = 0` outside it.

`hfg`, that `f` and `g` agree on `A`, is the source's requirement that both maps are over the
base.  It is not a convenience: the two sides of the formula differ by exactly
`∑_K (f - g)(c_K) f(x^{[K]})` without it. -/
theorem taylorFormula_polynomial
    (f g : DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowerRing A W).dividedPowers B.dividedPowers)
    (hfg : ∀ c : (A : Type u),
      f (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W) c) =
        g (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W) c))
    (a : setIndexedDividedPowerPolynomialAlgebra A W) :
    ∃ t : Finset (W →₀ ℕ),
      (f a = ∑ J ∈ t, g (dividedPowerPolynomialPartial A W J a) *
          taylorMonomial B (fun i ↦ f (dividedPowerPolynomialVariable A i) -
            g (dividedPowerPolynomialVariable A i)) J) ∧
        ∀ J ∉ t, g (dividedPowerPolynomialPartial A W J a) *
          taylorMonomial B (fun i ↦ f (dividedPowerPolynomialVariable A i) -
            g (dividedPowerPolynomialVariable A i)) J = 0 := by
  classical
  set bs := dividedPowerPolynomialMonomialBasis (A : Type u) W with hbs
  set s := (bs.repr a).support
  set t := s.biUnion fun K ↦ (antidiagonal K).image Prod.fst
  set xi : W → (B : Type u) := fun i ↦ f (dividedPowerPolynomialVariable A i) -
    g (dividedPowerPolynomialVariable A i)
  have hmem : ∀ K ∈ s, ∀ J ≤ K, J ∈ t := fun K hK J hJ ↦
    Finset.mem_biUnion.mpr ⟨K, hK, mem_image_fst_antidiagonal_iff.mpr hJ⟩
  have hbsapply : ∀ K : W →₀ ℕ, bs K = dividedPowerPolynomialMonomial (A : Type u) K := fun K ↦ by
    rw [hbs]
    exact dividedPowerPolynomialMonomialBasis_apply _ K
  have hrepr : ∑ K ∈ s, bs.repr a K • dividedPowerPolynomialMonomial (A : Type u) K = a := by
    conv_rhs => rw [← bs.linearCombination_repr a]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun K _ ↦ by rw [hbsapply]
  have hsmul : ∀ (h : DividedPowers.DPMorphism
        (setIndexedDividedPowerPolynomialDividedPowerRing A W).dividedPowers B.dividedPowers)
      (c : (A : Type u)) (y : setIndexedDividedPowerPolynomialAlgebra A W),
      h (c • y) =
        h (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W) c) * h y := by
    intro h c y
    rw [Algebra.smul_def]
    exact map_mul h.toRingHom _ _
  have hpartial : ∀ J : W →₀ ℕ, dividedPowerPolynomialPartial A W J a =
      ∑ K ∈ s, bs.repr a K • dividedPowerPolynomialPartial A W J
        (dividedPowerPolynomialMonomial (A : Type u) K) := by
    intro J
    conv_lhs => rw [← hrepr]
    rw [map_sum]
    exact Finset.sum_congr rfl fun K _ ↦ map_smul _ _ _
  have hkey : ∀ J : W →₀ ℕ,
      ∑ K ∈ s, g (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W)
            (bs.repr a K)) *
          g (dividedPowerPolynomialPartial A W J
            (dividedPowerPolynomialMonomial (A : Type u) K)) =
        g (dividedPowerPolynomialPartial A W J a) := by
    intro J
    refine Eq.trans ?_ (congrArg (fun y ↦ g y) (hpartial J)).symm
    refine Eq.trans ?_ (map_sum g.toRingHom
      (fun K ↦ bs.repr a K • dividedPowerPolynomialPartial A W J
        (dividedPowerPolynomialMonomial (A : Type u) K)) s).symm
    exact Finset.sum_congr rfl fun K _ ↦ (hsmul g _ _).symm
  refine ⟨t, ?_, fun J hJ ↦ ?_⟩
  · have hfa : f a = ∑ K ∈ s, f (bs.repr a K • dividedPowerPolynomialMonomial (A : Type u) K) := by
      conv_lhs => rw [← hrepr]
      exact map_sum f.toRingHom _ _
    rw [hfa]
    calc ∑ K ∈ s, f (bs.repr a K • dividedPowerPolynomialMonomial (A : Type u) K)
        = ∑ K ∈ s, ∑ J ∈ t,
            g (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W)
                (bs.repr a K)) *
              (g (dividedPowerPolynomialPartial A W J
                (dividedPowerPolynomialMonomial (A : Type u) K)) * taylorMonomial B xi J) := by
          refine Finset.sum_congr rfl fun K hK ↦ ?_
          rw [hsmul f, hfg, map_monomial_eq_sum_partial f g K t (hmem K hK), Finset.mul_sum]
      _ = ∑ J ∈ t, ∑ K ∈ s,
            g (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W)
                (bs.repr a K)) *
              (g (dividedPowerPolynomialPartial A W J
                (dividedPowerPolynomialMonomial (A : Type u) K)) * taylorMonomial B xi J) :=
          Finset.sum_comm
      _ = ∑ J ∈ t, g (dividedPowerPolynomialPartial A W J a) * taylorMonomial B xi J :=
          Finset.sum_congr rfl fun J _ ↦
            ((Finset.sum_congr rfl fun K _ ↦ (mul_assoc _ _ _).symm).trans
              (Finset.sum_mul _ _ _).symm).trans
                (congrArg (fun y ↦ y * taylorMonomial B xi J) (hkey J))
  · have hza : @Eq (setIndexedDividedPowerPolynomialAlgebra A W)
        (dividedPowerPolynomialPartial A W J a) 0 := by
      rw [hpartial J]
      refine Finset.sum_eq_zero fun K hK ↦ ?_
      rw [dividedPowerPolynomialPartial_monomial_of_not_le A W (fun h ↦ hJ (hmem K hK J h)),
        smul_zero]
    rw [hza, show g (0 : setIndexedDividedPowerPolynomialAlgebra A W) = 0
      from map_zero g.toRingHom, zero_mul]

/-- **The divided power partial derivatives are a composite coordinate operator family.**  This is
the hypothesis `hfamD` of `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula`,
discharged: `∂_0` is the identity and `∂_{K + e_i} = ∂_i ∘ ∂_K`, which are
`DividedPowers.dividedPowerPolynomialPartial_apply_zero` and
`DividedPowers.dividedPowerPolynomialPartial_succ`. -/
theorem isThetaMonomialFamily_partial :
    IsThetaMonomialFamily (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)
      (polynomialDelta A W) (polynomialDeltaPow A W) :=
  ⟨dividedPowerPolynomialPartial_apply_zero (A : Type u) W,
    fun i k ↦ dividedPowerPolynomialPartial_succ (A : Type u) W i k⟩

end Polynomial

section Comparison

open DividedPowers

variable {A : DividedPowerRing.{u}} {W : Type u} [DecidableEq W] {B : DividedPowerRing.{u}}
  [Algebra (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) (B : Type u)]
  {M : Type u} [AddCommGroup M]
  [Module (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) M]
  {theta : W → (M → M)} {thetaPow : (W →₀ ℕ) → (M → M)}

/-- **The corrected Taylor comparison predicate of [Stacks, Tag 07JH] is inhabited for the divided
power polynomial algebra.**  For `D = A⟨x_i : i ∈ W⟩`, a second divided power map
`f : D → B` and the coordinate differences `ξ_i = f(x_i) - g(x_i)` of
`Crystalline.SecondDividedPowerMap.diffFamily`, there is an `f`-semilinear map
`T : M →ₛₗ[f] B ⊗_D M` whose values are the sums of the Taylor series.

This is `Crystalline.exists_isTwistedTaylorComparison_of_taylorFormula` with its two ring-side
hypotheses discharged: `hfamD` by `Crystalline.isThetaMonomialFamily_partial` and `htay` — Taylor's
formula in `B`, the module's whole reason for existing — by
`Crystalline.taylorFormula_polynomial`.

What remains carried is named in the module docstring and is in each case the source's own or a
property of `M`: `hfamM`, `hthAdd` and `hleib` describe the module's coordinate operators and the
first-order Leibniz rule relating them to `∂_i`; `hg` says the structure map `D → B` is the
divided power map `g`; `hfg` says `f` and `g` agree on the coefficient ring, which is the source's
"both maps are over the base"; `hpB` is nilpotence of `p` in `B` from [Stacks, Tag 07HM]; and
`hfin` is the source's own "the sum is finite!", which
`Crystalline.finite_thetaPow_notMem_pPowSmul` gives from the quasi-nilpotence condition (07JE).

**This is not [Stacks, Tag 07JH]** and no attribute is placed: the tag is an equivalence of
categories, and this is the existence of one comparison map for one module. -/
theorem exists_isTwistedTaylorComparison_dividedPowerPolynomial (p : ℕ)
    (hfamM : IsThetaMonomialFamily M theta thetaPow)
    (hthAdd : ∀ (i : W) (x y : M), theta i (x + y) = theta i x + theta i y)
    (hleib : ∀ (i : W)
      (a : (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)) (m : M),
      theta i (a • m) = a • theta i m + polynomialDelta A W i a • m)
    (f : SecondDividedPowerMap (setIndexedDividedPowerPolynomialDividedPowerRing A W) B)
    (g : DividedPowers.DPMorphism
      (setIndexedDividedPowerPolynomialDividedPowerRing A W).dividedPowers B.dividedPowers)
    (hg : ∀ y, g y =
      algebraMap (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) (B : Type u) y)
    (hfg : ∀ c : (A : Type u),
      f.hom (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W) c) =
        g (algebraMap (A : Type u) (setIndexedDividedPowerPolynomialAlgebra A W) c))
    {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0)
    (hfin : ∀ m : M, {L : W →₀ ℕ | thetaPow L m ∉
      pPowSmul p (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) M N}.Finite) :
    ∃ T : M →ₛₗ[f.ringHom]
        ((B : Type u) ⊗[(setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u)] M),
      IsTwistedTaylorComparison p (setIndexedDividedPowerPolynomialDividedPowerRing A W) B M f
        thetaPow (f.diffFamily (fun i ↦ dividedPowerPolynomialVariable A i)) T := by
  classical
  have hxifun : f.diffFamily (fun i ↦ dividedPowerPolynomialVariable A i) =
      fun i ↦ f.hom (dividedPowerPolynomialVariable A i) -
        g (dividedPowerPolynomialVariable A i) :=
    funext fun i ↦ congrArg (fun y ↦ f.hom (dividedPowerPolynomialVariable A i) - y)
      (hg (dividedPowerPolynomialVariable A i)).symm
  refine exists_isTwistedTaylorComparison_of_taylorFormula p hfamM
    isThetaMonomialFamily_partial hthAdd hleib
    (fun i ↦ f.diffFamily_mem (fun i ↦ dividedPowerPolynomialVariable A i) i) hpB f
    (fun a ↦ ?_) hfin
  obtain ⟨t, h1, h2⟩ := taylorFormula_polynomial f.hom g hfg a
  have hterm : ∀ J : W →₀ ℕ,
      g (polynomialDeltaPow A W J a) *
          taylorMonomial B (fun i ↦ f.hom (dividedPowerPolynomialVariable A i) -
            g (dividedPowerPolynomialVariable A i)) J =
        algebraMap (setIndexedDividedPowerPolynomialDividedPowerRing A W : Type u) (B : Type u)
            (polynomialDeltaPow A W J a) *
          taylorMonomial B (f.diffFamily (fun i ↦ dividedPowerPolynomialVariable A i)) J :=
    fun J ↦ congrArg₂ (· * ·) (hg _)
      (congrArg (fun φ ↦ taylorMonomial B φ J) hxifun).symm
  exact ⟨t, h1.trans (Finset.sum_congr rfl fun J _ ↦ hterm J),
    fun J hJ ↦ (hterm J).symm.trans (h2 J hJ)⟩

end Comparison

end Crystalline

end
