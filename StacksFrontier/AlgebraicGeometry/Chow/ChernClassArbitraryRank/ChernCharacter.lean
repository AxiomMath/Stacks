module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic

/-!
# The full Chern character of a finite locally free module of arbitrary rank

Let `X` be a scheme locally of finite type over the base `S` of a Chow situation and let `E` be a
finite locally free `O_X`-module whose rank need not be constant. Write `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …`
for the decomposition of `X` into the loci where the rank of `E` is `r`. Given the power sums
`P_p(c_1(E|_{X_r}), …, c_p(E|_{X_r})) ∈ A^p(X_r)` of the constant-rank restrictions, as a family
`P`, they assemble into a single class on `X`, and dividing by `p!` gives the degree-`p` component
of the Chern character

  `ch_p(E) = P_p(c_1(E), …, c_p(E))/p! ∈ A^p(X) ⊗ 𝐐`.

The rank of `E` is unbounded in general, so the full Chern character

  `ch(E) = (ch_0(E), ch_1(E), ch_2(E), …)`

is an element of the product `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` and not of the direct sum
`A^*(X) ⊗ 𝐐 = ⊕_{p ≥ 0} (A^p(X) ⊗ 𝐐)`. If the dimension of `X` is at most `d`, then `ch_p(E)` caps
every rational Chow class of a test scheme of dimension at most `d` to zero for `p > d`, and once
the components vanish above `d` the full Chern character lies in `A^*(X) ⊗ 𝐐`.

## Main definitions

* `Stacks.Chow.rationalChowCohomologyComponent`, `Stacks.Chow.fullRationalChowCohomology`,
  `Stacks.Chow.gradedRationalChowCohomology`: the groups `A^p(X) ⊗ 𝐐`, `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`
  and `A^*(X) ⊗ 𝐐`.
* `Stacks.Chow.capAtHom`, `Stacks.Chow.rationalCap`: the cap operation of a Chow cohomology class
  on a fixed Chow class, as a homomorphism in the class, and its base change to rational
  coefficients.
* `Stacks.Chow.rankLocusRestrictionHom`, `Stacks.Chow.rationalRankLocusRestriction`: restriction to
  a rank locus as a homomorphism, and with rational coefficients.
* `Stacks.Chow.powerSumClassArbitraryRank`: the integral power sum `P_p(c_1(E), …, c_p(E))` of a
  module of not necessarily constant rank, assembled from the rank loci.
* `Stacks.Chow.chernCharacterComponent`: the component `ch_p(E) ∈ A^p(X) ⊗ 𝐐`.
* `Stacks.Chow.fullChernCharacter`: the full Chern character `ch(E)` as an element of
  `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`.
* `Stacks.Chow.gradedChernCharacter`: the truncation `⊕_{p ≤ d} ch_p(E)` in `A^*(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.rankLocusRestriction_powerSumClassArbitraryRank`,
  `Stacks.Chow.eq_powerSumClassArbitraryRank_of_rankLocusRestriction_eq`: the component of
  `P_p(c_•(E))` on `X_r` is the constant-rank power sum there, and that determines the class.
* `Stacks.Chow.rationalRankLocusRestriction_chernCharacterComponent`: the component of `ch_p(E)` on
  the rank locus `X_r` is `ch_p(E|_{X_r})`.
* `Stacks.Chow.rationalCap_chernCharacterComponent_eq_zero_of_topologicalKrullDim_le`,
  `Stacks.Chow.rationalCap_id_chernCharacterComponent_eq_zero_of_topologicalKrullDim_le`: for
  `p > d` the component `ch_p(E)` caps every rational Chow class of every test scheme of dimension
  at most `d` to zero, in particular on `X` itself.
* `Stacks.Chow.chernCharacterComponent_eq_zero_of_cap_eq_zero`: a component whose power sum caps to
  zero on every test scheme is zero.
* `Stacks.Chow.gradedChernCharacter_eq_fullChernCharacter`: if the components vanish above `d`,
  then the full Chern character is the image of the finite sum `⊕_{p ≤ d} ch_p(E)` under the
  inclusion of the direct sum into the product.

## References

* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Chow cohomology with rational coefficients -/

section Rational

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- The degree-`p` rational Chow cohomology `A^p(X) ⊗ 𝐐` of a scheme locally of finite type over
the base. -/
abbrev rationalChowCohomologyComponent (p : ℤ) : Type (u + 1) :=
  TensorProduct ℤ ℚ (chowCohomologyComponent C G sX p)

/-- The product `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` of the rational Chow cohomology groups in the
nonnegative degrees. -/
abbrev fullRationalChowCohomology : Type (u + 1) :=
  ∀ p : ℕ, rationalChowCohomologyComponent C G sX (p : ℤ)

/-- The rational Chow cohomology `A^*(X) ⊗ 𝐐 = ⊕_{p ≥ 0} (A^p(X) ⊗ 𝐐)` as a graded group: the
families of classes with only finitely many nonzero components. -/
abbrev gradedRationalChowCohomology : Type (u + 1) :=
  DirectSum ℕ fun p : ℕ ↦ rationalChowCohomologyComponent C G sX (p : ℤ)

/-- Capping a fixed Chow class of a test scheme with a Chow cohomology class of `X`, read as a
homomorphism in the cohomology class. -/
def capAtHom (p : ℤ) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    chowCohomologyComponent C G sX p →+ chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - p) :=
  AddMonoidHom.mk' (fun c ↦ c.cap g k α) fun _ _ ↦ rfl

/-- Capping with a fixed Chow class evaluates to the cap operation of the class. -/
@[simp]
theorem capAtHom_apply (p : ℤ) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) (c : chowCohomologyComponent C G sX p) :
    capAtHom C G sX p g k α c = c.cap g k α :=
  rfl

/-- The cap operation of a rational Chow cohomology class on a fixed Chow class of a test scheme,
with rational coefficients: the base change to `𝐐` of `Stacks.Chow.capAtHom`. -/
def rationalCap (p : ℤ) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k)
    (c : TensorProduct ℤ ℚ (chowCohomologyComponent C G sX p)) :
    TensorProduct ℤ ℚ (chowGroup C (pullback.fst (𝟙 X) g ≫ sX) (k - p)) :=
  TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) (capAtHom C G sX p g k α).toIntLinearMap c

/-- The rational cap operation on a class with rational coefficient `q` caps the integral class
and keeps the coefficient. -/
@[simp]
theorem rationalCap_tmul (p : ℤ) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) (q : ℚ) (c : chowCohomologyComponent C G sX p) :
    rationalCap C G sX p g k α (q ⊗ₜ[ℤ] c) = q ⊗ₜ[ℤ] c.cap g k α :=
  rfl

end Rational

/-! ### The power sums and the Chern character of a module of arbitrary rank -/

section ChernCharacter

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)
  (P : ∀ r p : ℕ, chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) (p : ℤ))

/-- Restriction of a Chow cohomology class of `X` to the rank-`r` locus of `E`, as a
homomorphism. -/
def rankLocusRestrictionHom (p : ℤ) (r : ℕ) :
    chowCohomologyComponent C G sX p →+
      chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p :=
  AddMonoidHom.mk' (fun c ↦ rankLocusRestriction C G sX E hgysO p c r)
    fun c d ↦ rankLocusRestriction_add C G sX E hgysO p c d r

/-- Restriction to a rank locus as a homomorphism evaluates to the restriction. -/
@[simp]
theorem rankLocusRestrictionHom_apply (p : ℤ) (r : ℕ)
    (c : chowCohomologyComponent C G sX p) :
    rankLocusRestrictionHom C G sX E hgysO p r c =
      rankLocusRestriction C G sX E hgysO p c r :=
  rfl

/-- Restriction to the rank-`r` locus of `E` with rational coefficients. -/
def rationalRankLocusRestriction (p : ℤ) (r : ℕ)
    (c : TensorProduct ℤ ℚ (chowCohomologyComponent C G sX p)) :
    TensorProduct ℤ ℚ (chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p) :=
  TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (rankLocusRestrictionHom C G sX E hgysO p r).toIntLinearMap c

/-- Rational restriction to a rank locus restricts the integral class and keeps the
coefficient. -/
@[simp]
theorem rationalRankLocusRestriction_tmul (p : ℤ) (r : ℕ) (q : ℚ)
    (c : chowCohomologyComponent C G sX p) :
    rationalRankLocusRestriction C G sX E hgysO p r (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] rankLocusRestriction C G sX E hgysO p c r :=
  rfl

/-- The integral power sum `P_p(c_1(E), …, c_p(E)) ∈ A^p(X)` of a finite locally free module of
not necessarily constant rank: the class whose component on the rank-`r` locus is the power sum
of the constant-rank restriction `E|_{X_r}`. -/
def powerSumClassArbitraryRank (p : ℕ) : chowCohomologyComponent C G sX (p : ℤ) :=
  rankLocusAssembly C G sX E hgysO hgysR hgysC (p : ℤ) fun r ↦ P r p

/-- The component of `P_p(c_1(E), …, c_p(E))` on the rank-`r` locus is the power sum of
`E|_{X_r}`. -/
theorem rankLocusRestriction_powerSumClassArbitraryRank (p r : ℕ) :
    rankLocusRestriction C G sX E hgysO (p : ℤ)
        (powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p) r = P r p :=
  rankLocusRestriction_rankLocusAssembly C G sX E hgysO hgysR hgysC (p : ℤ) _ r

/-- The power sum of a module of not necessarily constant rank is the only class with those
components on the rank loci. -/
theorem eq_powerSumClassArbitraryRank_of_rankLocusRestriction_eq (p : ℕ)
    {c : chowCohomologyComponent C G sX (p : ℤ)}
    (h : ∀ r : ℕ, rankLocusRestriction C G sX E hgysO (p : ℤ) c r = P r p) :
    c = powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p :=
  eq_of_rankLocusRestriction_eq C G sX E hgysO hgysR hgysC (p : ℤ) fun r ↦
    (h r).trans
      (rankLocusRestriction_powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC
        P p r).symm

/-- The degree-`p` component `ch_p(E) = P_p(c_1(E), …, c_p(E))/p! ∈ A^p(X) ⊗ 𝐐` of the Chern
character of a finite locally free module of not necessarily constant rank. -/
def chernCharacterComponent (p : ℕ) : rationalChowCohomologyComponent C G sX (p : ℤ) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
    powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p

/-- The Chern character component is the integral power sum divided by `p!`. -/
theorem chernCharacterComponent_eq (p : ℕ) :
    chernCharacterComponent C G sX E hgysO hgysR hgysC P p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
        powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p :=
  rfl

/-- The full Chern character `ch(E) = (ch_0(E), ch_1(E), ch_2(E), …)` of a finite locally free
module whose rank need not be constant, as an element of the product `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`. -/
@[stacks 0ESX "the full Chern character of a finite locally free module of not necessarily \
constant rank as an element of the product ∏_{p ≥ 0} (A^p(X) ⊗ 𝐐), assembled over the rank loci \
from the constant-rank power sums P_p(c_1(E|X_r), …, c_p(E|X_r)) that the remark recalls from \
Tags 0ESW, 0FA7 and 0F9C; those are carried as a quantified family, the multiplication of \
A^*(X) — composition of bivariant classes, Tag 0FE0 — not being constructed in this library"]
def fullChernCharacter : fullRationalChowCohomology C G sX :=
  fun p ↦ chernCharacterComponent C G sX E hgysO hgysR hgysC P p

/-- The degree-`p` entry of the full Chern character is the component `ch_p(E)`. -/
theorem fullChernCharacter_apply (p : ℕ) :
    fullChernCharacter C G sX E hgysO hgysR hgysC P p =
      chernCharacterComponent C G sX E hgysO hgysR hgysC P p :=
  rfl

/-- The component of `ch_p(E)` on the rank-`r` locus is `ch_p(E|_{X_r})`, the Chern character
component of the constant-rank restriction. -/
theorem rationalRankLocusRestriction_chernCharacterComponent (p r : ℕ) :
    rationalRankLocusRestriction C G sX E hgysO (p : ℤ) r
        (chernCharacterComponent C G sX E hgysO hgysR hgysC P p) =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] P r p := by
  rw [chernCharacterComponent_eq, rationalRankLocusRestriction_tmul,
    rankLocusRestriction_powerSumClassArbitraryRank]

/-! ### The Chern character in finite dimension -/

section FiniteDimension

variable [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)

include hδ in
/-- For `d < p` the class `ch_p(E)` caps every rational Chow class of a test scheme of dimension
at most `d` to zero. -/
@[stacks 0ESX "the vanishing of the components ch_p(E) for p above the dimension d of X, by \
Tag 0FDX, read on the test schemes of dimension at most d as the library's form of that tag \
allows; the splitting principle of the source is not needed, that form being a \
delta-dimension count, and neither is quasi-compactness of X"]
theorem rationalCap_chernCharacterComponent_eq_zero_of_topologicalKrullDim_le (d p : ℕ)
    (hp : d < p) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    rationalCap C G sX (p : ℤ) g k α
      (chernCharacterComponent C G sX E hgysO hgysR hgysC P p) = 0 := by
  rw [chernCharacterComponent_eq, rationalCap_tmul,
    BivariantClass.cap_eq_zero_of_topologicalKrullDim_le C hδ G sX sX (𝟙 X)
      (Category.id_comp sX) _ (by omega : (d : ℤ) + 1 ≤ (p : ℤ)) g hT k α,
    TensorProduct.tmul_zero]

include hδ in
/-- If the dimension of `X` is at most `d`, then for `d < p` the component `ch_p(E)` caps every
rational Chow class of `X` to zero. -/
theorem rationalCap_id_chernCharacterComponent_eq_zero_of_topologicalKrullDim_le (d p : ℕ)
    (hp : d < p) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (k : ℤ)
    (α : chowGroup C (𝟙 X ≫ sX) k) :
    rationalCap C G sX (p : ℤ) (𝟙 X) k α
      (chernCharacterComponent C G sX E hgysO hgysR hgysC P p) = 0 :=
  rationalCap_chernCharacterComponent_eq_zero_of_topologicalKrullDim_le C G sX E
    hgysO hgysR hgysC P hδ d p hp (𝟙 X) hdim k α

end FiniteDimension

/-- A component of the Chern character whose underlying power sum caps every Chow class of every
test scheme to zero is itself zero. -/
theorem chernCharacterComponent_eq_zero_of_cap_eq_zero (p : ℕ)
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k),
      (powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p).cap g k α = 0) :
    chernCharacterComponent C G sX E hgysO hgysR hgysC P p = 0 := by
  have hzero : powerSumClassArbitraryRank C G sX E hgysO hgysR hgysC P p = 0 := by
    apply BivariantClass.ext
    intro _ g _ k α
    rw [BivariantClass.zero_cap, h]
  rw [chernCharacterComponent_eq, hzero, TensorProduct.tmul_zero]

/-- The truncation `⊕_{p ≤ d} ch_p(E)` of the Chern character: the element of `A^*(X) ⊗ 𝐐` whose
component is `ch_p(E)` in the degrees at most `d` and zero above them. -/
def gradedChernCharacter (d : ℕ) : gradedRationalChowCohomology C G sX :=
  ∑ p ∈ Finset.range (d + 1), DirectSum.of _ p
    (chernCharacterComponent C G sX E hgysO hgysR hgysC P p)

/-- The truncation is the sum over the degrees at most `d` of the Chern character components,
each placed in its degree. -/
theorem gradedChernCharacter_eq (d : ℕ) :
    gradedChernCharacter C G sX E hgysO hgysR hgysC P d =
      ∑ p ∈ Finset.range (d + 1), DirectSum.of _ p
        (chernCharacterComponent C G sX E hgysO hgysR hgysC P p) :=
  rfl

/-- The degree-`p` entry of the truncation is `ch_p(E)` if `p ≤ d` and zero otherwise. -/
private theorem gradedChernCharacter_apply_eq_ite (d p : ℕ) :
    gradedChernCharacter C G sX E hgysO hgysR hgysC P d p =
      if p ≤ d then chernCharacterComponent C G sX E hgysO hgysR hgysC P p else 0 := by
  rw [gradedChernCharacter_eq, DirectSum.sum_apply]
  simp [DirectSum.of_apply]

/-- In the degrees at most `d` the truncation has the Chern character components. -/
theorem gradedChernCharacter_apply_of_le (d p : ℕ) (hp : p ≤ d) :
    gradedChernCharacter C G sX E hgysO hgysR hgysC P d p =
      chernCharacterComponent C G sX E hgysO hgysR hgysC P p := by
  simp [gradedChernCharacter_apply_eq_ite, hp]

/-- Above `d` the truncation vanishes. -/
theorem gradedChernCharacter_apply_of_lt (d p : ℕ) (hp : d < p) :
    gradedChernCharacter C G sX E hgysO hgysR hgysC P d p = 0 := by
  simp [gradedChernCharacter_apply_eq_ite, hp.not_ge]

/-- If the components of the Chern character vanish in the degrees above `d`, then the full
Chern character lies in `A^*(X) ⊗ 𝐐`: it is the image of the finite sum `⊕_{p ≤ d} ch_p(E)` under
the inclusion of the direct sum into the product `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`. -/
@[stacks 0ESX "the membership ch(E) ∈ A^*(X) ⊗ 𝐐 for X of dimension at most d: the full Chern \
character is the image of the finite sum ⊕_{p ≤ d} ch_p(E). The vanishing of the components \
above d is a hypothesis: the library's Tag 0FDX reaches only the test schemes of dimension at most \
d, and by Tag 02UC the remaining ones are what the equality ch_p(E) = 0 in A^p(X) ⊗ 𝐐 needs. \
Quasi-compactness of X is not assumed, being unused by the library's form of Tag 0FDX"]
theorem gradedChernCharacter_eq_fullChernCharacter (d : ℕ)
    (hvan : ∀ p : ℕ, d < p →
      chernCharacterComponent C G sX E hgysO hgysR hgysC P p = 0) :
    (fun p : ℕ ↦ gradedChernCharacter C G sX E hgysO hgysR hgysC P d p) =
      fullChernCharacter C G sX E hgysO hgysR hgysC P := by
  funext p
  rcases le_or_gt p d with hp | hp
  · exact gradedChernCharacter_apply_of_le C G sX E hgysO hgysR hgysC P d p hp
  · rw [gradedChernCharacter_apply_of_lt C G sX E hgysO hgysR hgysC P d p hp,
      fullChernCharacter_apply, hvan p hp]

end ChernCharacter

end Stacks.Chow

end
