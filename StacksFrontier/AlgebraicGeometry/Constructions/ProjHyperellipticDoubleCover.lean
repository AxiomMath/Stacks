module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjAmple.DegreeOneCover
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedQuotient
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjMorphismRatios
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.DualNumber

/-!
# The weighted double cover of the projective line: an ample sheaf with no small very ample twist

Over a field `k`, for `d ≥ 1` and scalars `λ₁, …, λ_{2d} ∈ k*`, let

`A_d = k[U, V, Z] / (Z² - ∏_{i=1}^{2d} (U - λᵢ V))`,  `deg U = deg V = 1`,  `deg Z = d`,

the weighted homogeneous presentation of the double cover of `𝐏¹_k` branched over the `2d`
points `λᵢ`. The algebra is graded by weighted degree, `X_d = Proj A_d` is covered by the two
standard opens `D₊(U)` and `D₊(V)` — because `Z²` is a product of the linear forms
`U - λᵢ V`, so `Z` vanishes wherever both `U` and `V` do — and therefore every twist
`𝒪_{X_d}(n)` is invertible, every multiplication map
`𝒪_{X_d}(n) ⊗ 𝒪_{X_d}(m) → 𝒪_{X_d}(n + m)` is an isomorphism, and `𝒪_{X_d}(1)` is ample.
For `d ≥ 2` the algebra `A_d` is not generated in degree one over `k`, so none of this is
available through the usual degree-one-generation hypothesis.

The example of [Stacks, Tag 01VP] is that, nevertheless, `𝒪_{X_d}(n)` is very ample only if
`n ≥ d`. The reason is that `Z` has degree `d`, so `Γ(X_d, 𝒪_{X_d}(n)) = k[U, V]_n` for `n < d`.
Concretely: `A_d` is the quadratic algebra `k[U, V][ω] / (ω² - f)` over the binary forms, with
`f = ∏ (U - λᵢ V)`, and an element of weighted degree `N` has a `Z`-coefficient of degree
`N - d`. A global section of `𝒪(n)` is a fraction `a / Vᴺ` on `D₊(V)` and `b / Uᴹ` on `D₊(U)`;
the two agree after a power of `U V`, and comparing `Z`-coefficients shows that the
`Z`-coefficient of `a` would be divisible by `Vᴺ` while having degree `N + n - d < N`, so it
vanishes. Comparing the other coefficients then exhibits the section as a binary form.

If `𝒪(n)` were very ample with `n < d`, there would be an immersion `α : X_d → 𝐏(E)` with
`𝒪(n) ≅ α^* 𝒪(1)`. At the branch point `(λ₁ : 1 : 0)` of `X_d → 𝐏¹` there are two `k[ε]`-points,
`Z ↦ ε` and `Z ↦ 0`, both with `U ↦ λ₁`, `V ↦ 1`; they are different, but they agree on every
element without a `Z`-part. The ratios of the sections of `𝒪(n)` pulled back from `𝐏(E)` are
such elements, and they determine the composites with `α`; so the two points have the same
image under the monomorphism `α`, which is absurd.

## Main definitions

* `Stacks.ProjHyperellipticDoubleCover.Vars` and
  `Stacks.ProjHyperellipticDoubleCover.weight`: the variables `U, V, Z` and their degrees
  `1, 1, d`.
* `Stacks.ProjHyperellipticDoubleCover.relation`: the relation `Z² - ∏ (U - λᵢ V)`.
* `Stacks.ProjHyperellipticDoubleCover.ring` and
  `Stacks.ProjHyperellipticDoubleCover.grading`: the algebra `A_d` and its grading by weighted
  degree.
* `Stacks.ProjHyperellipticDoubleCover.instGradedAlgebra`: the graded-algebra structure on
  `A_d`.
* `Stacks.ProjHyperellipticDoubleCover.uGen`,
  `Stacks.ProjHyperellipticDoubleCover.vGen` and
  `Stacks.ProjHyperellipticDoubleCover.zGen`: the classes of the variables.
* `Stacks.ProjHyperellipticDoubleCover.binaryForm`: the map `k[U, V] → A_d`.
* `Stacks.ProjHyperellipticDoubleCover.split` and
  `Stacks.ProjHyperellipticDoubleCover.unsplit`: the identification of `A_d` with the quadratic
  algebra `k[U, V][ω] / (ω² - f)`.
* `Stacks.ProjHyperellipticDoubleCover.branchPoint`: the branch point `(λ₁ : 1 : 0)` of `X_d`.
* `Stacks.ProjHyperellipticDoubleCover.tangent` and
  `Stacks.ProjHyperellipticDoubleCover.tangentZero`: the two `k[ε]`-points `Z ↦ ε` and
  `Z ↦ 0` at the branch point, as ring maps `A_d → k[ε]`, and
  `Stacks.ProjHyperellipticDoubleCover.stalkHom` the homomorphisms out of the stalk of `X_d` they
  induce.

## Main results

* `Stacks.ProjHyperellipticDoubleCover.zGen_sq_eq_prod`: the defining relation,
  `Z² = ∏ (U - λᵢ V)`.
* `Stacks.ProjHyperellipticDoubleCover.sup_basicOpen_eq_top`: **`X_d` is covered by `D₊(U)` and
  `D₊(V)`.**
* `Stacks.ProjHyperellipticDoubleCover.compactSpace_proj`: `X_d` is quasi-compact.
* `Stacks.ProjHyperellipticDoubleCover.isInvertible_twistingSheaf`: **every `𝒪_{X_d}(n)` is
  invertible**, and
  `Stacks.ProjHyperellipticDoubleCover.isIso_twistMultiplicationMap` identifies
  `𝒪_{X_d}(n) ⊗ 𝒪_{X_d}(m)` with `𝒪_{X_d}(n + m)`.
* `Stacks.ProjHyperellipticDoubleCover.isAmple_twistingModule_one`: **`𝒪_{X_d}(1)` is ample.**
* `Stacks.ProjHyperellipticDoubleCover.exists_twoChart_fraction`: for `n < d` a global section
  of `𝒪(n)` has no `Z`-part on either chart.
* `Stacks.ProjHyperellipticDoubleCover.bijective_degreeSection_binaryForm`:
  **`Γ(X_d, 𝒪_{X_d}(n)) = k[U, V]_n` for `n < d`.**
* `Stacks.ProjHyperellipticDoubleCover.tangent_ne_tangentZero`: the two `k[ε]`-points are
  different, and `Stacks.ProjHyperellipticDoubleCover.localHom_eq_of_smul_eq` that sections of
  `𝒪(n)` with `n < d` do not separate them.
* `Stacks.ProjHyperellipticDoubleCover.le_of_isRelativelyVeryAmple`: **if `𝒪_{X_d}(n)` is very
  ample, then `n ≥ d`.**

## Implementation notes

The scalars are taken as a family `λ : ℕ → kˣ` indexed from zero, with the product running over
`Finset.range (2 * d)`; neither distinctness nor infinitude of `k` is imposed, because neither is
used — the source notes that distinctness is "not strictly necessary" and that the construction
works with every `λᵢ = 1`. The degree `d` is an arbitrary natural number, and positivity of `d`
is assumed exactly where it is needed: for the two-chart cover, the inclusion
`D₊(Z) ⊆ D₊(U) ∪ D₊(V)` comes from a *nonempty* product of linear forms, and the branch point
`(λ₁ : 1 : 0)` exists because `f` has the factor `U - λ₁ V`.

Very ampleness is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` ([Stacks, Tag 01VM]) relative
to an arbitrary morphism from `X_d` to an affine scheme, which contains the structure morphism
`X_d → Spec k`. Over an affine base the projective bundle `𝐏(E)` is the homogeneous spectrum of
a graded ring generated in degree one
(`Stacks.VeryAmpleAffineBase.exists_immersion_proj_of_isRelativelyVeryAmple`), and
`Stacks.ProjMorphismRatios.spec_comp_eq_of_ratio` says that a morphism into such a `Proj` is
determined, on `k[ε]`-points, by the ratios of the pulled-back sections.

The argument is the source's with the tangent direction made explicit. When `char k ≠ 2` the two
points `(1 : 0 : ±1)` of `X_d` already have the same image; the vertical tangent vector at a
branch point is used instead because it works in every characteristic, including `2`, where
`X_d → 𝐏¹` is purely inseparable and injective on points.

The grading, the homogeneity of the relation ideal and the generation of `A_d` over `(A_d)₀` by
the variables all come from `Stacks.WeightedQuotient`, shared with the example of
[Stacks, Tag 01VO]. Invertibility and ampleness go through `Stacks.ProjDegreeOneCover`, whose
hypothesis is that every point lies in `D₊(g)` for some `g` of degree one.

## References

* [Stacks Project, Tag 01VP](https://stacks.math.columbia.edu/tag/01VP)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)

namespace Stacks.ProjHyperellipticDoubleCover

/-- The variables of the example: the two degree-one variables `U`, `V` and the variable `Z` of
degree `d`. -/
public inductive Vars : Type
  | u : Vars
  | v : Vars
  | z : Vars
  deriving DecidableEq

/-- The degrees of the variables: `U` and `V` have degree one, and `Z` has degree `d`. -/
public def weight (d : ℕ) : Vars → ℕ
  | .u => 1
  | .v => 1
  | .z => d

noncomputable section

universe u

variable (k : Type u) [Field k] (d : ℕ) (lam : ℕ → kˣ)

/-- The single relation `Z² - ∏_{i=1}^{2d} (U - λᵢ V)` of the example. -/
public def relation : Unit → MvPolynomial Vars k := fun _ =>
  X Vars.z ^ 2 - ∏ i ∈ Finset.range (2 * d), (X Vars.u - C (lam i : k) * X Vars.v)

/-- The weighted degree of the relation, namely `2d`. -/
public def relationDegree : Unit → ℕ := fun _ => 2 * d

/-- Each linear form `U - λᵢ V` is weighted homogeneous of degree one. -/
public theorem isWeightedHomogeneous_linearForm (i : ℕ) :
    (X Vars.u - C (lam i : k) * X Vars.v :
      MvPolynomial Vars k).IsWeightedHomogeneous (weight d) 1 := by
  have h1 : (X Vars.u : MvPolynomial Vars k).IsWeightedHomogeneous (weight d) 1 := by
    simpa [weight] using isWeightedHomogeneous_X k (weight d) Vars.u
  have h2 : (C (lam i : k) * X Vars.v :
      MvPolynomial Vars k).IsWeightedHomogeneous (weight d) 1 := by
    simpa [weight] using (isWeightedHomogeneous_X k (weight d) Vars.v).C_mul (lam i : k)
  exact h1.sub h2

/-- The relation is weighted homogeneous: `Z²` and a product of `2d` linear forms both have
weighted degree `2d`. -/
public theorem isWeightedHomogeneous_relation (j : Unit) :
    (relation k d lam j).IsWeightedHomogeneous (weight d) (relationDegree d j) := by
  have hz : (X Vars.z ^ 2 : MvPolynomial Vars k).IsWeightedHomogeneous (weight d)
      (relationDegree d j) := by
    simpa [weight, relationDegree, smul_eq_mul] using
      (isWeightedHomogeneous_X k (weight d) Vars.z).pow 2
  have hp : (∏ i ∈ Finset.range (2 * d), (X Vars.u - C (lam i : k) * X Vars.v) :
      MvPolynomial Vars k).IsWeightedHomogeneous (weight d) (relationDegree d j) := by
    have h := IsWeightedHomogeneous.prod (Finset.range (2 * d))
      (fun i => (X Vars.u - C (lam i : k) * X Vars.v : MvPolynomial Vars k)) (fun _ => 1)
      (w := weight d) fun i _ => isWeightedHomogeneous_linearForm k d lam i
    simpa [relationDegree, mul_comm] using h
  exact hz.sub hp

/-- The graded algebra `A_d = k[U, V, Z] / (Z² - ∏ (U - λᵢ V))` of the example. -/
public abbrev ring : Type u := Stacks.WeightedQuotient.ring (relation k d lam)

/-- The grading of `A_d` by weighted degree. -/
public abbrev grading : ℕ → Submodule k (ring k d lam) :=
  Stacks.WeightedQuotient.grading (weight d) (relation k d lam)

/-- **The graded-algebra structure on `A_d`.** It is constructed: the relation ideal is
homogeneous because the relation is weighted homogeneous, and the grading is the decomposition of
the quotient by a homogeneous ideal. -/
@[stacks 01VP "the graded algebra of the example"]
public instance instGradedAlgebra : _root_.GradedAlgebra (grading k d lam) :=
  Stacks.WeightedQuotient.gradedAlgebra (weight d) (relationDegree d) (relation k d lam)
    (isWeightedHomogeneous_relation k d lam)

/-- The class of `U` in `A_d`. -/
public def uGen : ring k d lam := Stacks.WeightedQuotient.gen (relation k d lam) Vars.u

/-- The class of `V` in `A_d`. -/
public def vGen : ring k d lam := Stacks.WeightedQuotient.gen (relation k d lam) Vars.v

/-- The class of `Z` in `A_d`. -/
public def zGen : ring k d lam := Stacks.WeightedQuotient.gen (relation k d lam) Vars.z

/-- `U` has degree one. -/
public theorem uGen_mem : uGen k d lam ∈ grading k d lam 1 :=
  Stacks.WeightedQuotient.gen_mem_grading (weight d) (relation k d lam) Vars.u

/-- `V` has degree one. -/
public theorem vGen_mem : vGen k d lam ∈ grading k d lam 1 :=
  Stacks.WeightedQuotient.gen_mem_grading (weight d) (relation k d lam) Vars.v

/-- `Z` has degree `d`. -/
public theorem zGen_mem : zGen k d lam ∈ grading k d lam d :=
  Stacks.WeightedQuotient.gen_mem_grading (weight d) (relation k d lam) Vars.z

/-- The defining relation in `A_d`: the degree-`d` element `Z` squares to the product of the
`2d` linear forms `U - λᵢ V`. -/
public theorem zGen_sq_eq_prod : zGen k d lam ^ 2 =
    ∏ i ∈ Finset.range (2 * d),
      (uGen k d lam - algebraMap k (ring k d lam) (lam i : k) * vGen k d lam) := by
  have h0 : Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k d lam))
      (relation k d lam ()) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(), rfl⟩)
  rw [relation, map_sub, sub_eq_zero] at h0
  simp only [map_pow, map_prod, map_sub, map_mul, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap] at h0
  exact h0

/-- **The standard open of `Z` is contained in the union of those of `U` and `V`**: a homogeneous
prime containing `U` and `V` contains every linear form `U - λᵢ V`, hence their product `Z²`,
hence `Z`. This needs `d ≥ 1`, so that the product has at least one factor. -/
public theorem basicOpen_zGen_le_sup (hd : 0 < d) :
    Proj.basicOpen (grading k d lam) (zGen k d lam) ≤
      Proj.basicOpen (grading k d lam) (uGen k d lam) ⊔
        Proj.basicOpen (grading k d lam) (vGen k d lam) := by
  intro x hx
  by_contra hcon
  rw [TopologicalSpace.Opens.mem_sup, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Proj.mem_basicOpen, not_not] at h1 h2
  have hfac (i : ℕ) : uGen k d lam -
      algebraMap k (ring k d lam) (lam i : k) * vGen k d lam ∈
        x.asHomogeneousIdeal.toIdeal :=
    sub_mem h1 (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i₀, hi₀⟩ : (Finset.range (2 * d)).Nonempty :=
    Finset.nonempty_range_iff.mpr (by omega)
  have hprod : ∏ i ∈ Finset.range (2 * d),
      (uGen k d lam - algebraMap k (ring k d lam) (lam i : k) * vGen k d lam) ∈
        x.asHomogeneousIdeal.toIdeal := by
    rw [← Finset.mul_prod_erase _ _ hi₀]
    exact Ideal.mul_mem_right _ _ (hfac i₀)
  exact hx (x.isPrime.mem_of_pow_mem 2 ((zGen_sq_eq_prod k d lam).symm ▸ hprod))

/-- **`X_d = Proj A_d` is covered by the two standard opens `D₊(U)` and `D₊(V)`.** The three
variables generate `A_d` over `(A_d)₀ = k`, so their standard opens cover, and `D₊(Z)` is
contained in the union of the other two. -/
@[stacks 01VP "the two-chart cover of the example"]
public theorem sup_basicOpen_eq_top (hd : 0 < d) :
    Proj.basicOpen (grading k d lam) (uGen k d lam) ⊔
      Proj.basicOpen (grading k d lam) (vGen k d lam) = ⊤ := by
  have hcover : (⨆ i : Vars, Proj.basicOpen (grading k d lam)
      (Stacks.WeightedQuotient.gen (relation k d lam) i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (grading k d lam)
      (Stacks.WeightedQuotient.gen (relation k d lam))
      (fun i => ⟨weight d i,
        Stacks.WeightedQuotient.gen_mem_grading (weight d) (relation k d lam) i⟩)
      (Stacks.WeightedQuotient.adjoin_range_gen_eq_top (weight d) (relation k d lam))
  refine top_unique (hcover.ge.trans (iSup_le fun i => ?_))
  cases i with
  | u => exact le_sup_left
  | v => exact le_sup_right
  | z => exact basicOpen_zGen_le_sup k d lam hd

/-- Every point of `X_d` lies in the standard open of a degree-one element, namely of `U` or of
`V`. -/
public theorem exists_mem_basicOpen_degreeOne (hd : 0 < d)
    (x : ProjectiveSpectrum.top (grading k d lam)) :
    ∃ g ∈ grading k d lam 1, x ∈ ProjectiveSpectrum.basicOpen (grading k d lam) g := by
  have hx : x ∈ Proj.basicOpen (grading k d lam) (uGen k d lam) ⊔
      Proj.basicOpen (grading k d lam) (vGen k d lam) := by
    rw [sup_basicOpen_eq_top k d lam hd]; trivial
  rcases hx with h | h
  · exact ⟨uGen k d lam, uGen_mem k d lam, h⟩
  · exact ⟨vGen k d lam, vGen_mem k d lam, h⟩

/-- **`X_d` is quasi-compact**: it is covered by the two affine opens `D₊(U)` and `D₊(V)`. -/
public theorem compactSpace_proj (hd : 0 < d) :
    CompactSpace (AlgebraicGeometry.Proj (grading k d lam)) :=
  Stacks.ProjDegreeOneCover.compactSpace_of_iSup_basicOpen_eq_top (grading k d lam)
    (fun b : Bool => cond b (uGen k d lam) (vGen k d lam))
    (fun b => by cases b with
      | false => exact vGen_mem k d lam
      | true => exact uGen_mem k d lam)
    (by rw [iSup_bool_eq]; exact sup_basicOpen_eq_top k d lam hd)

/-- **Every twist `𝒪_{X_d}(n)` is invertible.** For `d ≥ 2` the algebra `A_d` is not generated in
degree one, so this does not come from degree-one generation; the two-chart cover is what
supplies it. -/
@[stacks 01VP "invertibility of the twists on the example"]
public theorem isInvertible_twistingSheaf (hd : 0 < d) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (grading k d lam)).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj (grading k d lam)).toRingedSpace).property
      (twistingSheaf (grading k d lam) n) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
    (grading k d lam) (Stacks.ProjDegreeOneCover.degreeOneCover_of_forall_exists
      (grading k d lam) (exists_mem_basicOpen_degreeOne k d lam hd)) n

/-- **The multiplication `𝒪_{X_d}(n) ⊗ 𝒪_{X_d}(m) → 𝒪_{X_d}(n + m)` is an isomorphism**, so each
`𝒪_{X_d}(n)` is the `n`-th tensor power of `𝒪_{X_d}(1)`. -/
@[stacks 01VP "the twists are tensor powers of the first twist"]
public theorem isIso_twistMultiplicationMap (hd : 0 < d) (n m : ℤ) :
    IsIso (twistMultiplicationMap (grading k d lam) n m) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistMultiplicationMap
    (grading k d lam) (Stacks.ProjDegreeOneCover.degreeOneCover_of_forall_exists
      (grading k d lam) (exists_mem_basicOpen_degreeOne k d lam hd)) n m

/-- **`𝒪_{X_d}(1)` is an ample invertible sheaf on `X_d = Proj A_d`** — the positive assertion of
the example. `X_d` is quasi-compact and every point lies in the affine standard open of one of
the degree-one elements `U`, `V`. -/
@[stacks 01VP "the ample invertible sheaf on the example"]
public theorem isAmple_twistingModule_one (hd : 0 < d) :
    @AlgebraicGeometry.Scheme.Modules.IsAmple (AlgebraicGeometry.Proj (grading k d lam))
      (Stacks.ProjTwistSection.twistingModule (grading k d lam) 1)
      (isInvertible_twistingSheaf k d lam hd 1) :=
  Stacks.ProjDegreeOneCover.isAmple_twistingModule_one (grading k d lam)
    (compactSpace_proj k d lam hd) (exists_mem_basicOpen_degreeOne k d lam hd)

/-! ### The splitting of `A_d` over `k[U, V]`

The relation `Z² = f(U, V)` with `f = ∏ (U - λᵢ V)` says that `A_d` is the quadratic algebra
`k[U, V][ω] / (ω² - f)` over the ring of binary forms `k[U, V]`: the map `Z ↦ ω` is
`Stacks.ProjHyperellipticDoubleCover.split`, with inverse
`Stacks.ProjHyperellipticDoubleCover.unsplit`,
`p + q ω ↦ p + q Z`. The `ω`-coefficient of the image of an element is its `Z`-coefficient. An
element of weighted degree `N` has a `1`-coefficient of degree `N` and a `Z`-coefficient of
degree `N - d`, and no `Z`-coefficient at all when `N < d`. -/

/-- The ring map `k[U, V] → A_d` from binary forms. -/
public def binaryForm : MvPolynomial (Fin 2) k →ₐ[k] ring k d lam :=
  aeval ![uGen k d lam, vGen k d lam]

/-- The branch form `f = ∏_{i=1}^{2d} (U - λᵢ V)`, a binary form of degree `2d`. -/
public def branchForm : MvPolynomial (Fin 2) k :=
  ∏ i ∈ Finset.range (2 * d), (X 0 - C (lam i : k) * X 1)

/-- The quadratic algebra `k[U, V][ω] / (ω² - f)`. -/
public abbrev Splitting : Type u := QuadraticAlgebra (MvPolynomial (Fin 2) k) (branchForm k d lam) 0

/-- The images of the variables in `Splitting`: `U ↦ U`, `V ↦ V`, `Z ↦ ω`. -/
public def splitVar : Vars → Splitting k d lam
  | .u => algebraMap (MvPolynomial (Fin 2) k) _ (X 0)
  | .v => algebraMap (MvPolynomial (Fin 2) k) _ (X 1)
  | .z => (QuadraticAlgebra.omega : Splitting k d lam)

/-- The map `k[U, V, Z] → Splitting` sending `Z` to `ω`. -/
public def splitPoly : MvPolynomial Vars k →ₐ[k] Splitting k d lam := aeval (splitVar k d lam)

public theorem splitPoly_linearForm (c : k) :
    splitPoly k d lam (X Vars.u - C c * X Vars.v) =
      algebraMap _ _ (X 0 - C c * X 1 : MvPolynomial (Fin 2) k) := by
  simp [splitPoly, splitVar,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (Splitting k d lam)]

/-- The relation `Z² - f` is killed by `Z ↦ ω`. -/
public theorem splitPoly_relation (j : Unit) : splitPoly k d lam (relation k d lam j) = 0 := by
  have hz : splitPoly k d lam (X Vars.z ^ 2) = algebraMap _ _ (branchForm k d lam) := by
    rw [map_pow, splitPoly, aeval_X, splitVar, sq, QuadraticAlgebra.omega_mul_omega_eq_mk]
    ext <;> simp
  simp only [relation]
  rw [map_sub, hz, sub_eq_zero, map_prod]
  refine (map_prod (algebraMap (MvPolynomial (Fin 2) k) (Splitting k d lam))
    (fun i => (X 0 - C (lam i : k) * X 1 : MvPolynomial (Fin 2) k))
    (Finset.range (2 * d))).trans ?_
  exact Finset.prod_congr rfl fun i _ => (splitPoly_linearForm k d lam _).symm

/-- **The splitting `A_d → Splitting`**, `Z ↦ ω`. -/
public def split : ring k d lam →ₐ[k] Splitting k d lam :=
  Ideal.Quotient.liftₐ _ (splitPoly k d lam) (fun a ha => by
    have hle : Stacks.WeightedQuotient.relationIdeal (relation k d lam) ≤
        RingHom.ker (splitPoly k d lam) :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr fun j => splitPoly_relation k d lam j)
    exact hle ha)

public theorem split_mk (p : MvPolynomial Vars k) :
    split k d lam (Ideal.Quotient.mk _ p) = splitPoly k d lam p := rfl

public theorem split_uGen : split k d lam (uGen k d lam) =
    algebraMap (MvPolynomial (Fin 2) k) (Splitting k d lam) (X 0) := by
  simp [uGen, Stacks.WeightedQuotient.gen, split_mk, splitPoly, splitVar]

public theorem split_vGen : split k d lam (vGen k d lam) =
    algebraMap (MvPolynomial (Fin 2) k) (Splitting k d lam) (X 1) := by
  simp [vGen, Stacks.WeightedQuotient.gen, split_mk, splitPoly, splitVar]

public theorem split_zGen : split k d lam (zGen k d lam) = QuadraticAlgebra.omega := by
  simp [zGen, Stacks.WeightedQuotient.gen, split_mk, splitPoly, splitVar]

/-- The splitting is the identity on binary forms. -/
public theorem split_binaryForm (p : MvPolynomial (Fin 2) k) :
    split k d lam (binaryForm k d lam p) = algebraMap _ _ p := by
  have h : (split k d lam).comp (binaryForm k d lam) =
      IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (Splitting k d lam) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [binaryForm, split_uGen]
    · simp [binaryForm, split_vGen]
  exact congrArg (fun φ => φ p) h

/-- `Z² = f(U, V)` in `A_d`, with `f` read as a binary form. -/
public theorem zGen_mul_zGen :
    zGen k d lam * zGen k d lam = binaryForm k d lam (branchForm k d lam) := by
  rw [← sq, zGen_sq_eq_prod, branchForm, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [binaryForm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc]

/-- **The inverse of the splitting**, `p + q ω ↦ p + q Z`. -/
public def unsplit : Splitting k d lam →+* ring k d lam where
  toFun x := binaryForm k d lam x.re + binaryForm k d lam x.im * zGen k d lam
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_zero,
      zero_mul, add_zero]
    linear_combination (binaryForm k d lam x.im * binaryForm k d lam y.im) *
      (zGen_mul_zGen k d lam).symm
  map_zero' := by simp
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

/-- **Every element of `A_d` is `p + q Z`** with `p + q ω` its splitting. -/
public theorem unsplit_split (a : ring k d lam) : unsplit k d lam (split k d lam a) = a := by
  have h : (unsplit k d lam).comp (split k d lam).toRingHom = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [unsplit, RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, split_mk, splitPoly,
        aeval_C, RingHom.id_apply]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    · intro i
      cases i with
      | u => simp [unsplit, split_mk, splitPoly, splitVar, binaryForm, uGen,
          Stacks.WeightedQuotient.gen, QuadraticAlgebra.algebraMap_re,
          QuadraticAlgebra.algebraMap_im]
      | v => simp [unsplit, split_mk, splitPoly, splitVar, binaryForm, vGen,
          Stacks.WeightedQuotient.gen, QuadraticAlgebra.algebraMap_re,
          QuadraticAlgebra.algebraMap_im]
      | z => simp [unsplit, split_mk, splitPoly, splitVar, zGen,
          Stacks.WeightedQuotient.gen, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
  exact congrArg (fun φ => φ a) h

public theorem isHomogeneous_branchForm : (branchForm k d lam).IsHomogeneous (2 * d) := by
  have h := IsHomogeneous.prod (Finset.range (2 * d))
      (fun i => (X 0 - C (lam i : k) * X 1 : MvPolynomial (Fin 2) k)) (fun _ => 1)
      fun i _ => (isHomogeneous_X k 0).sub ((isHomogeneous_X k 1).C_mul _)
  simpa [branchForm, mul_comm] using h

/-- The binary forms a `Z`-coefficient of weighted degree `N` can be: those of degree `N - d` when
`d ≤ N`, and only `0` when `N < d`. -/
public def zCoeffSubmodule (N : ℕ) : Submodule k (MvPolynomial (Fin 2) k) :=
  if d ≤ N then homogeneousSubmodule (Fin 2) k (N - d) else ⊥

/-- An element of `Splitting` has weighted degree `N` when its `1`-coefficient is a binary form of
degree `N` and its `ω`-coefficient one of degree `N - d`. -/
public def IsSplitHomogeneous (N : ℕ) (x : Splitting k d lam) : Prop :=
  x.re ∈ homogeneousSubmodule (Fin 2) k N ∧ x.im ∈ zCoeffSubmodule k d N

variable {k d lam} in
public theorem mul_mem_zCoeffSubmodule {N M : ℕ} {p q : MvPolynomial (Fin 2) k}
    (hp : p ∈ homogeneousSubmodule (Fin 2) k N) (hq : q ∈ zCoeffSubmodule k d M) :
    p * q ∈ zCoeffSubmodule k d (N + M) := by
  unfold zCoeffSubmodule at hq ⊢
  split_ifs at hq with hM
  · rw [if_pos (by omega)]
    rw [mem_homogeneousSubmodule] at hp hq ⊢
    have := hp.mul hq
    rwa [show N + (M - d) = N + M - d by omega] at this
  · rw [Submodule.mem_bot] at hq
    rw [hq, mul_zero]
    exact Submodule.zero_mem _

variable {k d} in
public theorem branchForm_mul_mem {N M : ℕ} {p q : MvPolynomial (Fin 2) k}
    (hp : p ∈ zCoeffSubmodule k d N) (hq : q ∈ zCoeffSubmodule k d M) :
    branchForm k d lam * p * q ∈ homogeneousSubmodule (Fin 2) k (N + M) := by
  unfold zCoeffSubmodule at hp hq
  split_ifs at hp hq with hN hM
  · rw [mem_homogeneousSubmodule] at hp hq ⊢
    have := ((isHomogeneous_branchForm k d lam).mul hp).mul hq
    rwa [show 2 * d + (N - d) + (M - d) = N + M by omega] at this
  all_goals first
    | (rw [Submodule.mem_bot] at hq; rw [hq, mul_zero]; exact Submodule.zero_mem _)
    | (rw [Submodule.mem_bot] at hp; rw [hp, mul_zero, zero_mul]; exact Submodule.zero_mem _)

variable {k d lam} in
public theorem IsSplitHomogeneous.mul {N M : ℕ} {x y : Splitting k d lam}
    (hx : IsSplitHomogeneous k d lam N x) (hy : IsSplitHomogeneous k d lam M y) :
    IsSplitHomogeneous k d lam (N + M) (x * y) := by
  obtain ⟨hxr, hxi⟩ := hx
  obtain ⟨hyr, hyi⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_mul]
    refine Submodule.add_mem _ ?_ (branchForm_mul_mem lam hxi hyi)
    rw [mem_homogeneousSubmodule] at hxr hyr ⊢
    exact hxr.mul hyr
  · rw [QuadraticAlgebra.im_mul, zero_mul, zero_mul, add_zero]
    refine Submodule.add_mem _ (mul_mem_zCoeffSubmodule hxr hyi) ?_
    rw [mul_comm, add_comm]
    exact mul_mem_zCoeffSubmodule hyr hxi

variable {k d lam} in
public theorem IsSplitHomogeneous.add {N : ℕ} {x y : Splitting k d lam}
    (hx : IsSplitHomogeneous k d lam N x) (hy : IsSplitHomogeneous k d lam N y) :
    IsSplitHomogeneous k d lam N (x + y) :=
  ⟨by rw [QuadraticAlgebra.re_add]; exact Submodule.add_mem _ hx.1 hy.1,
    by rw [QuadraticAlgebra.im_add]; exact Submodule.add_mem _ hx.2 hy.2⟩

variable {k d lam} in
public theorem IsSplitHomogeneous.smul {N : ℕ} (c : k) {x : Splitting k d lam}
    (hx : IsSplitHomogeneous k d lam N x) : IsSplitHomogeneous k d lam N (c • x) := by
  refine ⟨?_, ?_⟩
  · simpa using Submodule.smul_mem _ c hx.1
  · simpa using Submodule.smul_mem _ c hx.2

public theorem isSplitHomogeneous_zero (N : ℕ) : IsSplitHomogeneous k d lam N 0 :=
  ⟨by simpa using Submodule.zero_mem _, by simpa using Submodule.zero_mem _⟩

public theorem isSplitHomogeneous_one : IsSplitHomogeneous k d lam 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_one, mem_homogeneousSubmodule]
    exact isHomogeneous_one (Fin 2) k
  · rw [QuadraticAlgebra.im_one]
    exact Submodule.zero_mem _

public theorem isSplitHomogeneous_splitVar (i : Vars) :
    IsSplitHomogeneous k d lam (weight d i) (splitVar k d lam i) := by
  cases i with
  | u => exact ⟨by simpa [splitVar, mem_homogeneousSubmodule, weight,
            QuadraticAlgebra.algebraMap_re] using isHomogeneous_X k (0 : Fin 2),
          by simpa [splitVar, QuadraticAlgebra.algebraMap_im] using Submodule.zero_mem _⟩
  | v => exact ⟨by simpa [splitVar, mem_homogeneousSubmodule, weight,
            QuadraticAlgebra.algebraMap_re] using isHomogeneous_X k (1 : Fin 2),
          by simpa [splitVar, QuadraticAlgebra.algebraMap_im] using Submodule.zero_mem _⟩
  | z =>
      refine ⟨by simpa [splitVar, QuadraticAlgebra.re_omega] using Submodule.zero_mem _, ?_⟩
      simp only [splitVar, QuadraticAlgebra.im_omega, zCoeffSubmodule, weight, le_refl,
        if_true, Nat.sub_self, mem_homogeneousSubmodule]
      exact isHomogeneous_one (Fin 2) k

/-- **The splitting respects degrees.** -/
public theorem isSplitHomogeneous_splitPoly {N : ℕ} {p : MvPolynomial Vars k}
    (hp : p.IsWeightedHomogeneous (weight d) N) :
    IsSplitHomogeneous k d lam N (splitPoly k d lam p) := by
  classical
  have hmono : ∀ s : Vars →₀ ℕ, IsSplitHomogeneous k d lam (Finsupp.weight (weight d) s)
      (s.prod fun i e => splitVar k d lam i ^ e) := by
    intro s
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    induction s.support using Finset.induction_on with
    | empty => simpa using isSplitHomogeneous_one k d lam
    | insert i t hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi]
        refine IsSplitHomogeneous.mul ?_ ih
        have hpow : ∀ e : ℕ, IsSplitHomogeneous k d lam (e • weight d i)
            (splitVar k d lam i ^ e) := by
          intro e
          induction e with
          | zero => simpa using isSplitHomogeneous_one k d lam
          | succ e ihe =>
              rw [pow_succ, succ_nsmul]
              exact ihe.mul (isSplitHomogeneous_splitVar k d lam i)
        exact hpow (s i)
  rw [p.as_sum, map_sum]
  refine Finset.sum_induction _ _ (fun x y hx hy => hx.add hy)
    (isSplitHomogeneous_zero k d lam N) ?_
  intro s hs
  rw [splitPoly, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hw : Finsupp.weight (weight d) s = N := hp (mem_support_iff.mp hs)
  rw [← hw]
  exact (hmono s).smul _

/-- **The splitting of an element of degree `N` of `A_d` has weighted degree `N`.** -/
public theorem isSplitHomogeneous_split {N : ℕ} {a : ring k d lam}
    (ha : a ∈ grading k d lam N) : IsSplitHomogeneous k d lam N (split k d lam a) := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  exact isSplitHomogeneous_splitPoly k d lam
    ((mem_weightedHomogeneousSubmodule k (weight d) N p).mp hp)

variable {k} in
/-- **A binary form divisible by a high power of one variable after multiplication by a power of
the other has too high a degree.** If `q` has degree `D` and `q Xᵢᴹ = q' Xⱼᴷ` with `i ≠ j` and
`D < K`, then `q = 0`: every monomial of `q Xᵢᴹ` carries `Xⱼ` to the power at least `K`. -/
public theorem eq_zero_of_mul_X_pow_eq {D K M : ℕ} {i j : Fin 2} (hij : i ≠ j)
    {q q' : MvPolynomial (Fin 2) k} (hq : q.IsHomogeneous D) (hDK : D < K)
    (h : q * X i ^ M = q' * X j ^ K) : q = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hne
  have h1 : coeff (s + Finsupp.single i M) (q * X i ^ M) = coeff s q := by
    rw [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
  have h2 : coeff (s + Finsupp.single i M) (q' * X j ^ K) ≠ 0 := by
    rw [← h, h1]
    exact hs
  rw [X_pow_eq_monomial, coeff_mul_monomial'] at h2
  split_ifs at h2 with hle
  swap
  · exact h2 rfl
  have hK : K ≤ s j := by
    have := hle j
    simpa [Finsupp.single_apply, hij, Ne.symm hij] using this
  have hw : Finsupp.weight 1 s = D := hq hs
  have hsj : s j ≤ Finsupp.weight 1 s := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    by_cases hj : s j = 0
    · rw [hj]; exact Nat.zero_le _
    · have hmem : j ∈ s.support := Finsupp.mem_support_iff.mpr hj
      calc s j = s j • (1 : Fin 2 → ℕ) j := by simp
        _ ≤ ∑ i ∈ s.support, s i • (1 : Fin 2 → ℕ) i :=
          Finset.single_le_sum (f := fun i => s i • (1 : Fin 2 → ℕ) i)
            (fun _ _ => Nat.zero_le _) hmem
  omega

variable {k} in
/-- A `Z`-coefficient of degree `N - d` with `N < K + d` that becomes divisible by `Xⱼᴷ` after
multiplication by a power of the other variable is zero. -/
public theorem eq_zero_of_mem_zCoeffSubmodule {N K M : ℕ} {i j : Fin 2} (hij : i ≠ j)
    {q q' : MvPolynomial (Fin 2) k} (hq : q ∈ zCoeffSubmodule k d N) (hNK : N < K + d)
    (h : q * X i ^ M = q' * X j ^ K) : q = 0 := by
  unfold zCoeffSubmodule at hq
  split_ifs at hq with hdN
  · exact eq_zero_of_mul_X_pow_eq hij ((mem_homogeneousSubmodule _ _).mp hq) (by omega) h
  · exact (Submodule.mem_bot k).mp hq

/-! ### Global sections of `𝒪(n)` for `n < d` carry no `Z`

A global section of `𝒪(n)` is a single fraction `a / Vᴺ` on `D₊(V)` and a single fraction
`b / Uᴹ` on `D₊(U)`, and the two agree after a power of `U V`. Reading that relation through the
splitting, `Uᴹ · (Z-part of a) = Vᴺ · (Z-part of b)`, and the `Z`-part of `a` has degree
`N + n - d < N`, too small to be divisible by `Vᴺ` unless it vanishes. This is the content of
`Γ(X_d, 𝒪(n)) = k[U, V]_n` for `n < d` that the example uses. -/

local instance (x : AlgebraicGeometry.Proj (grading k d lam)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime

attribute [local instance] ProjectiveSpectrum.isPrime

/-- **For `n < d`, a global section of `𝒪_{X_d}(n)` on the two charts.** On `D₊(V)` it is a
fraction `a / Vᴺ`, on `D₊(U)` a fraction `b / Uᴹ`; neither numerator has a `Z`-coefficient, and
their `1`-coefficients satisfy `p_a Uᴹ = p_b Vᴺ`. -/
public theorem exists_twoChart_fraction {n : ℤ} (hn : n < d)
    (t : Γ(Stacks.ProjTwistSection.twistingModule (grading k d lam) n, ⊤)) :
    ∃ (N M m m' : ℕ) (a b : ring k d lam), (m : ℤ) = N + n ∧ (m' : ℤ) = M + n ∧
      a ∈ grading k d lam m ∧ b ∈ grading k d lam m' ∧
      (split k d lam a).im = 0 ∧ (split k d lam b).im = 0 ∧
      (split k d lam a).re * X 0 ^ M = (split k d lam b).re * X 1 ^ N ∧
      (∀ (y : AlgebraicGeometry.Proj (grading k d lam))
        (hy : vGen k d lam ∉ y.asHomogeneousIdeal),
        t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
          ⟨vGen k d lam ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩) ∧
      (∀ (y : AlgebraicGeometry.Proj (grading k d lam))
        (hy : uGen k d lam ∉ y.asHomogeneousIdeal),
        t.1 ⟨y, trivial⟩ = LocalizedModule.mk b
          ⟨uGen k d lam ^ M, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy M⟩) := by
  obtain ⟨N, m, a, hm, ha, hva⟩ :=
    Stacks.ProjMorphismRatios.exists_eq_mk_of_mem_degreeOne (vGen_mem k d lam) t
  obtain ⟨M, m', b, hm', hb, hub⟩ :=
    Stacks.ProjMorphismRatios.exists_eq_mk_of_mem_degreeOne (uGen_mem k d lam) t
  obtain ⟨K, hK⟩ := Stacks.ProjMorphismRatios.exists_pow_mul_sub_eq_zero (vGen_mem k d lam)
    (uGen_mem k d lam) t hm hm' ha hb hva hub
  have hsplit := congrArg (split k d lam) hK
  simp only [map_mul, map_pow, map_sub, split_uGen, split_vGen, map_zero] at hsplit
  rw [← map_mul, ← map_pow, ← map_pow, ← map_pow] at hsplit
  have hne : (X 1 * X 0 : MvPolynomial (Fin 2) k) ^ K ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  have him := congrArg QuadraticAlgebra.im hsplit
  have hre := congrArg QuadraticAlgebra.re hsplit
  simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
    QuadraticAlgebra.im_zero, QuadraticAlgebra.re_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at him hre
  have him' := sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_left hne)
  have hre' := sub_eq_zero.mp ((mul_eq_zero.mp hre).resolve_left hne)
  have hoa : (split k d lam a).im = 0 :=
    eq_zero_of_mem_zCoeffSubmodule d (i := 0) (j := 1) (K := N) (M := M)
      (q' := (split k d lam b).im) (by decide)
      (isSplitHomogeneous_split k d lam ha).2 (by omega)
      (by linear_combination him')
  have hob : (split k d lam b).im = 0 :=
    eq_zero_of_mem_zCoeffSubmodule d (i := 1) (j := 0) (K := M) (M := N)
      (q' := (split k d lam a).im) (by decide)
      (isSplitHomogeneous_split k d lam hb).2 (by omega)
      (by linear_combination -him')
  exact ⟨N, M, m, m', a, b, hm, hm', ha, hb, hoa, hob, by linear_combination hre', hva, hub⟩

/-- **For `n < d` a global section of `𝒪_{X_d}(n)` has no `Z`-part on `D₊(V)`**: on `D₊(V)` it is a
single fraction `a / Vᴺ` whose numerator has vanishing `Z`-coefficient. -/
public theorem exists_eq_mk_split_im_eq_zero {n : ℤ} (hn : n < d)
    (t : Γ(Stacks.ProjTwistSection.twistingModule (grading k d lam) n, ⊤)) :
    ∃ (N m : ℕ) (a : ring k d lam), (m : ℤ) = N + n ∧ a ∈ grading k d lam m ∧
      (split k d lam a).im = 0 ∧
      ∀ (y : AlgebraicGeometry.Proj (grading k d lam))
        (hy : vGen k d lam ∉ y.asHomogeneousIdeal),
        t.1 ⟨y, trivial⟩ = LocalizedModule.mk a
          ⟨vGen k d lam ^ N, y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩ := by
  obtain ⟨N, -, m, -, a, -, hm, -, ha, -, hoa, -, -, hva, -⟩ :=
    exists_twoChart_fraction k d lam hn t
  exact ⟨N, m, a, hm, ha, hoa, hva⟩

/-! ### `Γ(X_d, 𝒪(n)) = k[U, V]_n` for `n < d` -/

/-- A binary form of degree `n` is an element of degree `n` of `A_d`. -/
public theorem binaryForm_mem {n : ℕ} {p : MvPolynomial (Fin 2) k} (hp : p.IsHomogeneous n) :
    binaryForm k d lam p ∈ grading k d lam n := by
  classical
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hw : Finsupp.weight 1 s = n := hp (mem_support_iff.mp hs)
  rw [binaryForm, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine Submodule.smul_mem _ _ ?_
  have hsum : s 0 + s 1 = n := by
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
  rw [← hsum]
  exact SetLike.mul_mem_graded (by simpa using SetLike.pow_mem_graded (s 0) (uGen_mem k d lam))
    (by simpa using SetLike.pow_mem_graded (s 1) (vGen_mem k d lam))

/-- In a localization, a fraction `c gᴺ / gᴺ` equals `c / 1`. -/
private theorem mk_mul_pow_eq_mk_one {R : Type*} [CommRing R] {P : Ideal R} [P.IsPrime] {g : R}
    (hg : g ∈ P.primeCompl) (c : R) (N : ℕ) :
    (LocalizedModule.mk (c * g ^ N) ⟨g ^ N, P.primeCompl.pow_mem hg N⟩ :
      LocalizedModule P.primeCompl R) = LocalizedModule.mk c 1 := by
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩

/-- **[Stacks, Tag 01VP]: `Γ(X_d, 𝒪_{X_d}(n)) = k[U, V]_n` for `0 ≤ n < d`.** The map sending a
binary form `p` of degree `n` to the global section `p / 1` of `𝒪_{X_d}(n)` is bijective. -/
@[stacks 01VP "the global sections of the twists of degree less than d"]
public theorem bijective_degreeSection_binaryForm (hd : 0 < d) {n : ℕ} (hn : n < d) :
    Function.Bijective fun p : homogeneousSubmodule (Fin 2) k n =>
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k d lam) n
        ⟨binaryForm k d lam p, binaryForm_mem k d lam ((mem_homogeneousSubmodule _ _).mp p.2)⟩ := by
  have hval : ∀ (p : homogeneousSubmodule (Fin 2) k n)
      (y : AlgebraicGeometry.Proj (grading k d lam)),
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (grading k d lam) n
        ⟨binaryForm k d lam p, binaryForm_mem k d lam
          ((mem_homogeneousSubmodule _ _).mp p.2)⟩).1 ⟨y, trivial⟩ =
        LocalizedModule.mk (binaryForm k d lam p) 1 := fun _ _ => rfl
  refine ⟨fun p p' hpp' => ?_, fun s => ?_⟩
  · -- injectivity: the difference is killed by a power of `V`
    have hδ : binaryForm k d lam p - binaryForm k d lam p' ∈ grading k d lam n :=
      sub_mem (binaryForm_mem k d lam ((mem_homogeneousSubmodule _ _).mp p.2))
        (binaryForm_mem k d lam ((mem_homogeneousSubmodule _ _).mp p'.2))
    obtain ⟨K, hK⟩ := ProjectiveSpectrum.exists_pow_mul_eq_zero_of_forall_mem_basicOpen
      one_pos (vGen_mem k d lam) hδ fun y hy => by
        have h : (LocalizedModule.mk (binaryForm k d lam p) 1 :
            LocalizedModule y.asHomogeneousIdeal.toIdeal.primeCompl (ring k d lam)) =
            LocalizedModule.mk (binaryForm k d lam p') 1 :=
          (hval p y).symm.trans ((congrArg (fun z => z.1 ⟨y, trivial⟩) hpp').trans (hval p' y))
        rw [LocalizedModule.mk_eq] at h
        obtain ⟨c, hc⟩ := h
        refine ⟨c, c.2, ?_⟩
        simp only [one_smul, Submonoid.smul_def, smul_eq_mul] at hc
        rw [mul_sub, hc, sub_self]
    have h := congrArg (fun z => (split k d lam z).re) hK
    rw [map_mul, map_pow, split_vGen, map_sub, split_binaryForm, split_binaryForm, ← map_pow,
      ← map_sub, ← map_mul, map_zero, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.re_zero] at h
    have h' := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (X_ne_zero _))
    exact Subtype.ext (sub_eq_zero.mp h')
  · -- surjectivity: the section is a binary form on both charts
    obtain ⟨N, M, m, m', a, b, hm, hm', ha, hb, hoa, hob, hrel, hva, hub⟩ :=
      exists_twoChart_fraction k d lam (by exact_mod_cast hn) s
    have hbin : ∀ x : ring k d lam, (split k d lam x).im = 0 →
        x = binaryForm k d lam (split k d lam x).re := fun x hx => by
      conv_lhs => rw [← unsplit_split k d lam x]
      simp [unsplit, hx]
    have ha' := hbin a hoa
    have hb' := hbin b hob
    have hX : ¬ (X 1 : MvPolynomial (Fin 2) k) ∣ X 0 ^ M := fun h =>
      absurd (X_dvd_X.mp (X_prime.dvd_of_dvd_pow h)) (by decide)
    obtain ⟨p, hp⟩ := (X_prime.pow_dvd_of_dvd_mul_right N hX
      ⟨_, hrel.trans (mul_comm _ _)⟩ : (X 1 : MvPolynomial (Fin 2) k) ^ N ∣
        (split k d lam a).re)
    have hmN : m = N + n := by omega
    have hpn : p.IsHomogeneous n := by
      intro s hs
      have hra := (isSplitHomogeneous_split k d lam ha).1
      rw [mem_homogeneousSubmodule, hp] at hra
      have hc : coeff (s + Finsupp.single 1 N) (X 1 ^ N * p) ≠ 0 := by
        rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]; exact hs
      have hws : ∀ s : Fin 2 →₀ ℕ, Finsupp.weight 1 s = s 0 + s 1 := fun s => by
        simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
      have := hra hc
      rw [hws] at this ⊢
      simp [Finsupp.single_apply] at this
      omega
    have hrb : (split k d lam b).re = p * X 0 ^ M := by
      apply mul_right_cancel₀ (pow_ne_zero N (X_ne_zero (1 : Fin 2)) :
        (X 1 : MvPolynomial (Fin 2) k) ^ N ≠ 0)
      rw [← hrel, hp]
      ring
    refine ⟨⟨p, (mem_homogeneousSubmodule _ _).mpr hpn⟩, ?_⟩
    apply Subtype.ext
    funext y
    have hy : y.1 ∈ Proj.basicOpen (grading k d lam) (uGen k d lam) ⊔
        Proj.basicOpen (grading k d lam) (vGen k d lam) := by
      rw [sup_basicOpen_eq_top k d lam hd]; trivial
    haveI := y.1.isPrime
    rcases hy with hy | hy
    · have h1 := hub y.1 hy
      have h2 : (LocalizedModule.mk b ⟨uGen k d lam ^ M,
          y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy M⟩ :
            LocalizedModule y.1.asHomogeneousIdeal.toIdeal.primeCompl (ring k d lam)) =
          LocalizedModule.mk (binaryForm k d lam p) 1 := by
        rw [hb', hrb, map_mul, map_pow, binaryForm, aeval_X]
        exact mk_mul_pow_eq_mk_one hy _ _
      exact h2.symm.trans h1.symm
    · have h1 := hva y.1 hy
      have h2 : (LocalizedModule.mk a ⟨vGen k d lam ^ N,
          y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hy N⟩ :
            LocalizedModule y.1.asHomogeneousIdeal.toIdeal.primeCompl (ring k d lam)) =
          LocalizedModule.mk (binaryForm k d lam p) 1 := by
        rw [ha', hp, map_mul, map_pow, binaryForm, aeval_X, mul_comm]
        exact mk_mul_pow_eq_mk_one hy _ _
      exact h2.symm.trans h1.symm

/-! ### The vertical tangent vector at a branch point

The point `(λ₁ : 1 : 0)` of `X_d` is a branch point of `X_d → 𝐏¹`: there `Z = 0` and
`f(λ₁, 1) = 0`. It carries the tangent vector `∂/∂Z`, the `k[ε]`-point
`U ↦ λ₁, V ↦ 1, Z ↦ ε` (a point because `ε² = 0 = f(λ₁, 1)`), besides the constant one
`Z ↦ 0`. The two agree on everything without a `Z`-part, so a morphism given by sections of
`𝒪(n)` with `n < d` cannot tell them apart. -/

/-- The coordinates `U = λ₁, V = 1` of the branch point. -/
public def branchValue : Fin 2 → k := ![(lam 0 : k), 1]

public theorem eval_branchForm (hd : 0 < d) :
    eval (branchValue k lam) (branchForm k d lam) = 0 := by
  rw [branchForm, map_prod]
  exact Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (by omega)) (by simp [branchValue])

/-- The evaluation `Splitting → k[ε]`, `x ↦ x₁(λ₁, 1, 0) + x_ω(λ₁, 1, 0) ε`; multiplicative
because `f(λ₁, 1) = 0` and `ε² = 0`. -/
public def tangentEval (hd : 0 < d) : Splitting k d lam →+* DualNumber k where
  toFun x := TrivSqZeroExt.inl (eval (branchValue k lam) x.re) +
    TrivSqZeroExt.inr (eval (branchValue k lam) x.im)
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    ext
    · simp [QuadraticAlgebra.re_mul, eval_branchForm k d lam hd]
    · simp [QuadraticAlgebra.im_mul]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

/-- **The vertical tangent vector at the branch point**, `A_d → k[ε]`, `U ↦ λ₁, V ↦ 1, Z ↦ ε`. -/
public def tangent (hd : 0 < d) : ring k d lam →+* DualNumber k :=
  (tangentEval k d lam hd).comp (split k d lam).toRingHom

/-- The branch point itself, `A_d → k`, `U ↦ λ₁, V ↦ 1, Z ↦ 0`. -/
public def branchEval (hd : 0 < d) : ring k d lam →+* k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom.comp (tangent k d lam hd)

/-- The constant tangent vector at the branch point, `A_d → k ⊆ k[ε]`. -/
public def tangentZero (hd : 0 < d) : ring k d lam →+* DualNumber k :=
  (TrivSqZeroExt.inlHom k k).comp (branchEval k d lam hd)

public theorem tangent_fst (hd : 0 < d) (a : ring k d lam) :
    (tangent k d lam hd a).fst = branchEval k d lam hd a := rfl

public theorem tangentZero_fst (hd : 0 < d) (a : ring k d lam) :
    (tangentZero k d lam hd a).fst = branchEval k d lam hd a := rfl

/-- **Without a `Z`-part the two tangent vectors agree.** -/
public theorem tangent_eq_inl (hd : 0 < d) {a : ring k d lam} (ha : (split k d lam a).im = 0) :
    tangent k d lam hd a = TrivSqZeroExt.inl (branchEval k d lam hd a) := by
  ext
  · rfl
  · change (TrivSqZeroExt.inl (eval (branchValue k lam) (split k d lam a).re) +
      TrivSqZeroExt.inr (eval (branchValue k lam) (split k d lam a).im) : DualNumber k).snd = _
    simp [ha]

public theorem tangent_vGen (hd : 0 < d) : tangent k d lam hd (vGen k d lam) = 1 := by
  change tangentEval k d lam hd (split k d lam (vGen k d lam)) = 1
  rw [split_vGen]
  ext <;> simp [tangentEval, branchValue, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im]

public theorem tangent_zGen (hd : 0 < d) :
    tangent k d lam hd (zGen k d lam) = DualNumber.eps := by
  change tangentEval k d lam hd (split k d lam (zGen k d lam)) = _
  rw [split_zGen]
  ext <;> simp [tangentEval, branchValue, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

public theorem branchEval_vGen (hd : 0 < d) : branchEval k d lam hd (vGen k d lam) = 1 := by
  rw [← tangent_fst, tangent_vGen]; rfl

public theorem branchEval_zGen (hd : 0 < d) : branchEval k d lam hd (zGen k d lam) = 0 := by
  rw [← tangent_fst, tangent_zGen]; rfl

public theorem tangentZero_vGen (hd : 0 < d) : tangentZero k d lam hd (vGen k d lam) = 1 := by
  simp [tangentZero, branchEval_vGen]

/-- **The branch point `(λ₁ : 1 : 0)` of `X_d`**: the homogeneous prime generated by the
homogeneous elements vanishing at `U = λ₁, V = 1, Z = 0`. -/
public def branchPoint (hd : 0 < d) : ProjectiveSpectrum (grading k d lam) where
  asHomogeneousIdeal :=
    Ideal.homogeneousCore (grading k d lam) (RingHom.ker (branchEval k d lam hd))
  isPrime := (RingHom.ker_isPrime _).homogeneousCore
  not_irrelevant_le := fun hle => by
    have hV : vGen k d lam ∈ HomogeneousIdeal.irrelevant (grading k d lam) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ (vGen_mem k d lam) one_ne_zero]
    have := Ideal.toIdeal_homogeneousCore_le _ _ (hle hV)
    rw [RingHom.mem_ker, branchEval_vGen] at this
    exact one_ne_zero this

/-- A homogeneous element lies outside the branch point exactly when it does not vanish there. -/
public theorem notMem_branchPoint_iff (hd : 0 < d) {a : ring k d lam} {i : ℕ}
    (ha : a ∈ grading k d lam i) :
    a ∉ (branchPoint k d lam hd).asHomogeneousIdeal ↔ branchEval k d lam hd a ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · exact Ideal.toIdeal_homogeneousCore_le _ _ h
  · exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨i, ha⟩ h

public theorem vGen_notMem_branchPoint (hd : 0 < d) :
    vGen k d lam ∉ (branchPoint k d lam hd).asHomogeneousIdeal :=
  (notMem_branchPoint_iff k d lam hd (vGen_mem k d lam)).mpr
    (by rw [branchEval_vGen]; exact one_ne_zero)

public theorem vGen_mem_primeCompl (hd : 0 < d) :
    vGen k d lam ∈ (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal.primeCompl :=
  vGen_notMem_branchPoint k d lam hd

/-! ### The two tangent vectors as `k[ε]`-points of `X_d`

A ring map `ρ : A_d → k[ε]` over the branch point with `ρ(V) = 1` induces a ring map out of the
degree-zero localization `(A_d)_{(V)}`, and from there, the stalk of `X_d` at the branch point
being a localization of `(A_d)_{(V)}`, a local homomorphism out of that stalk. -/

/-- A ring map to `k[ε]` over the branch point is a unit on a homogeneous element outside it. -/
private theorem isUnit_apply_of_notMem_branchPoint (hd : 0 < d) {ρ : ring k d lam →+* DualNumber k}
    (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a) {a : ring k d lam} {i : ℕ}
    (ha : a ∈ grading k d lam i) (h : a ∉ (branchPoint k d lam hd).asHomogeneousIdeal) :
    IsUnit (ρ a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hρ, isUnit_iff_ne_zero]
  exact (notMem_branchPoint_iff k d lam hd ha).mp h

open HomogeneousLocalization in
/-- The ring map `(A_d)_{(V)} → k[ε]`, `a / Vᵐ ↦ ρ(a)`, of a ring map `ρ` with `ρ(V) = 1`. -/
public def awayHom (ρ : ring k d lam →+* DualNumber k) (hρV : ρ (vGen k d lam) = 1) :
    Away (grading k d lam) (vGen k d lam) →+* DualNumber k :=
  (IsLocalization.Away.lift (S := Localization.Away (vGen k d lam)) (vGen k d lam) (g := ρ)
    (by rw [hρV]; exact isUnit_one)).comp
    (algebraMap (Away (grading k d lam) (vGen k d lam)) (Localization.Away (vGen k d lam)))

open HomogeneousLocalization in
public theorem awayHom_mk' (ρ : ring k d lam →+* DualNumber k) (hρV : ρ (vGen k d lam) = 1)
    (z : NumDenSameDeg (grading k d lam) (Submonoid.powers (vGen k d lam))) :
    awayHom k d lam ρ hρV (HomogeneousLocalization.mk z) = ρ z.num := by
  obtain ⟨i, hi⟩ := z.den_mem
  simp only [awayHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  change ρ z.num = ρ (z.den : ring k d lam) * ρ z.num
  rw [← hi, map_pow, hρV, one_pow, one_mul]

open HomogeneousLocalization in
public theorem awayHom_mk (ρ : ring k d lam →+* DualNumber k) (hρV : ρ (vGen k d lam) = 1)
    (m : ℕ) (a : ring k d lam) (ha : a ∈ grading k d lam (m • 1)) :
    awayHom k d lam ρ hρV (Away.mk (grading k d lam) (vGen_mem k d lam) m a ha) = ρ a :=
  awayHom_mk' k d lam ρ hρV _

open HomogeneousLocalization in
/-- Outside the prime of the branch point in `(A_d)_{(V)}`, `awayHom` takes unit values. -/
public theorem isUnit_awayHom (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a)
    (y : Away (grading k d lam) (vGen k d lam))
    (hy : y ∉ ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd, vGen_notMem_branchPoint k d lam hd⟩).asIdeal) :
    IsUnit (awayHom k d lam ρ hρV y) := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective y
  have hy' := (AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply _ _ z).not.mp hy
  rw [awayHom_mk']
  exact isUnit_apply_of_notMem_branchPoint k d lam hd hρ z.num.2 hy'

open HomogeneousLocalization in
/-- **The local homomorphism out of the homogeneous localization at the branch point** induced by
a ring map `ρ : A_d → k[ε]` over the branch point with `ρ(V) = 1`. -/
public def localHom (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a) :
    AtPrime (grading k d lam) (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal →+*
      DualNumber k :=
  haveI : ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd,
        vGen_notMem_branchPoint k d lam hd⟩).asIdeal.IsPrime :=
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd, vGen_notMem_branchPoint k d lam hd⟩).isPrime
  letI _inst : Algebra (Away (grading k d lam) (vGen k d lam))
      (AtPrime (grading k d lam) (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal) :=
    (HomogeneousLocalization.mapId (grading k d lam)
      (Submonoid.powers_le.mpr (vGen_mem_primeCompl k d lam hd))).toAlgebra
  haveI _hloc : @IsLocalization (Away (grading k d lam) (vGen k d lam)) _
      ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
        (vGen k d lam)).base ⟨branchPoint k d lam hd,
          vGen_notMem_branchPoint k d lam hd⟩).asIdeal.primeCompl
      (AtPrime (grading k d lam) (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal) _ _inst :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime (grading k d lam)
      (vGen k d lam) ⟨branchPoint k d lam hd, vGen_notMem_branchPoint k d lam hd⟩
      (vGen_mem k d lam) one_pos
  IsLocalization.lift (M := ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd,
        vGen_notMem_branchPoint k d lam hd⟩).asIdeal.primeCompl)
    (g := awayHom k d lam ρ hρV) fun y => isUnit_awayHom k d lam hd ρ hρV hρ y.1 y.2

open HomogeneousLocalization in
public theorem localHom_mapId (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a)
    (w : Away (grading k d lam) (vGen k d lam)) :
    localHom k d lam hd ρ hρV hρ (HomogeneousLocalization.mapId (grading k d lam)
      (Submonoid.powers_le.mpr (vGen_mem_primeCompl k d lam hd)) w) =
      awayHom k d lam ρ hρV w := by
  haveI : ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd,
        vGen_notMem_branchPoint k d lam hd⟩).asIdeal.IsPrime :=
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
      (vGen k d lam)).base ⟨branchPoint k d lam hd, vGen_notMem_branchPoint k d lam hd⟩).isPrime
  letI _inst : Algebra (Away (grading k d lam) (vGen k d lam))
      (AtPrime (grading k d lam) (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal) :=
    (HomogeneousLocalization.mapId (grading k d lam)
      (Submonoid.powers_le.mpr (vGen_mem_primeCompl k d lam hd))).toAlgebra
  haveI _hloc : @IsLocalization (Away (grading k d lam) (vGen k d lam)) _
      ((AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec (grading k d lam)
        (vGen k d lam)).base ⟨branchPoint k d lam hd,
          vGen_notMem_branchPoint k d lam hd⟩).asIdeal.primeCompl
      (AtPrime (grading k d lam) (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal) _ _inst :=
    AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime (grading k d lam)
      (vGen k d lam) ⟨branchPoint k d lam hd, vGen_notMem_branchPoint k d lam hd⟩
      (vGen_mem k d lam) one_pos
  exact IsLocalization.lift_eq _ w

open HomogeneousLocalization in
/-- On a fraction `c / e` of the homogeneous localization, `localHom ρ` solves
`localHom ρ (c / e) · ρ(e) = ρ(c)`. -/
public theorem localHom_mk_mul (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a)
    (z : NumDenSameDeg (grading k d lam)
      (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal.primeCompl) :
    localHom k d lam hd ρ hρV hρ (HomogeneousLocalization.mk z) * ρ z.den = ρ z.num := by
  have hc : (z.num : ring k d lam) ∈ grading k d lam (z.deg • 1) := by simpa using z.num.2
  have he : (z.den : ring k d lam) ∈ grading k d lam (z.deg • 1) := by simpa using z.den.2
  have hP := vGen_mem_primeCompl k d lam hd
  have key : HomogeneousLocalization.mk z * HomogeneousLocalization.mapId (grading k d lam)
      (Submonoid.powers_le.mpr hP)
        (Away.mk (grading k d lam) (vGen_mem k d lam) z.deg z.den he) =
      HomogeneousLocalization.mapId (grading k d lam) (Submonoid.powers_le.mpr hP)
        (Away.mk (grading k d lam) (vGen_mem k d lam) z.deg z.num hc) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul]
    change Localization.mk (z.num : ring k d lam) ⟨z.den, z.den_mem⟩ *
        Localization.mk (z.den : ring k d lam) ⟨vGen k d lam ^ z.deg, _⟩ =
      Localization.mk (z.num : ring k d lam) ⟨vGen k d lam ^ z.deg, _⟩
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩
  have h := congrArg (localHom k d lam hd ρ hρV hρ) key
  rw [map_mul, localHom_mapId, localHom_mapId, awayHom_mk, awayHom_mk] at h
  exact h

open HomogeneousLocalization in
public theorem isLocalHom_localHom (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a) :
    IsLocalHom (localHom k d lam hd ρ hρV hρ) := by
  refine ⟨fun r hr => ?_⟩
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective r
  have hc : IsUnit (ρ z.num) := by
    rw [← localHom_mk_mul k d lam hd ρ hρV hρ z]
    exact hr.mul (isUnit_apply_of_notMem_branchPoint k d lam hd hρ z.den.2 z.den_mem)
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hρ, isUnit_iff_ne_zero] at hc
  have hcP : (z.num : ring k d lam) ∈
      (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal.primeCompl :=
    (notMem_branchPoint_iff k d lam hd z.num.2).mpr hc
  refine ⟨⟨HomogeneousLocalization.mk z,
    HomogeneousLocalization.mk ⟨z.deg, z.den, z.num, hcP⟩, ?_, ?_⟩, rfl⟩
  all_goals
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_one, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

/-- **The homomorphism out of the stalk of `X_d` at the branch point** induced by `ρ`: the stalk
read as the homogeneous localization at the branch point, followed by `localHom ρ`. -/
public def stalkHom (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a) :
    (AlgebraicGeometry.Proj (grading k d lam)).presheaf.stalk (branchPoint k d lam hd) ⟶
      CommRingCat.of (DualNumber k) :=
  (AlgebraicGeometry.Proj.stalkIso (grading k d lam) (branchPoint k d lam hd)).hom ≫
    CommRingCat.ofHom (localHom k d lam hd ρ hρV hρ)

public theorem stalkHom_stalkIso'_symm (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a)
    (r : HomogeneousLocalization.AtPrime (grading k d lam)
      (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal) :
    stalkHom k d lam hd ρ hρV hρ
        ((AlgebraicGeometry.Proj.stalkIso' (grading k d lam) (branchPoint k d lam hd)).symm r) =
      localHom k d lam hd ρ hρV hρ r := by
  change ((AlgebraicGeometry.Proj.stalkIso (grading k d lam) (branchPoint k d lam hd)).inv ≫
    stalkHom k d lam hd ρ hρV hρ) r = _
  rw [stalkHom, Iso.inv_hom_id_assoc]
  rfl

/-- The homomorphism out of the stalk induced by `ρ` is local. -/
public instance isLocalHom_stalkHom (hd : 0 < d) (ρ : ring k d lam →+* DualNumber k)
    (hρV : ρ (vGen k d lam) = 1) (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a) :
    IsLocalHom (stalkHom k d lam hd ρ hρV hρ).hom := by
  haveI := isLocalHom_localHom k d lam hd ρ hρV hρ
  haveI := isLocalHom_of_iso (AlgebraicGeometry.Proj.stalkIso (grading k d lam)
    (branchPoint k d lam hd))
  exact CommRingCat.isLocalHom_comp _ _

/-- **The two tangent vectors are different `k[ε]`-points of `X_d`.** -/
public theorem tangent_ne_tangentZero (hd : 0 < d) :
    Spec.map (stalkHom k d lam hd (tangent k d lam hd) (tangent_vGen k d lam hd)
        (tangent_fst k d lam hd)) ≫
        (AlgebraicGeometry.Proj (grading k d lam)).fromSpecStalk (branchPoint k d lam hd) ≠
      Spec.map (stalkHom k d lam hd (tangentZero k d lam hd) (tangentZero_vGen k d lam hd)
        (tangentZero_fst k d lam hd)) ≫
        (AlgebraicGeometry.Proj (grading k d lam)).fromSpecStalk (branchPoint k d lam hd) := by
  intro h
  have h' := (SpecToEquivOfLocalRing (AlgebraicGeometry.Proj (grading k d lam))
    (CommRingCat.of (DualNumber k))).symm.injective
    (a₁ := ⟨branchPoint k d lam hd, stalkHom k d lam hd (tangent k d lam hd)
      (tangent_vGen k d lam hd) (tangent_fst k d lam hd), inferInstance⟩)
    (a₂ := ⟨branchPoint k d lam hd, stalkHom k d lam hd (tangentZero k d lam hd)
      (tangentZero_vGen k d lam hd) (tangentZero_fst k d lam hd), inferInstance⟩) h
  have hψ := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h').2)
  have hz : zGen k d lam ∈ grading k d lam (d • 1) := by simpa using zGen_mem k d lam
  have hval := congrArg (fun φ => φ ((AlgebraicGeometry.Proj.stalkIso' (grading k d lam)
      (branchPoint k d lam hd)).symm (HomogeneousLocalization.mapId (grading k d lam)
        (Submonoid.powers_le.mpr (vGen_mem_primeCompl k d lam hd))
        (HomogeneousLocalization.Away.mk (grading k d lam) (vGen_mem k d lam) d (zGen k d lam)
          hz)))) hψ
  have hval' := (stalkHom_stalkIso'_symm k d lam hd _ _ _ _).symm.trans
    (hval.trans (stalkHom_stalkIso'_symm k d lam hd _ _ _ _))
  rw [localHom_mapId, localHom_mapId, awayHom_mk, awayHom_mk, tangent_zGen] at hval'
  have := congrArg TrivSqZeroExt.snd hval'
  simp [tangentZero, branchEval_zGen] at this

/-- **Sections of `𝒪(n)` with `n < d` do not separate the two tangent vectors.** If `r` in the
homogeneous localization at the branch point solves `r · t = s` there, for global sections `s`,
`t` of `𝒪(n)` with `t` not vanishing at the branch point, then both tangent vectors take the
same value on `r`. -/
public theorem localHom_eq_of_smul_eq (hd : 0 < d) {n : ℤ} (hn : n < d)
    (s t : Γ(Stacks.ProjTwistSection.twistingModule (grading k d lam) n, ⊤))
    (ht : (branchPoint k d lam hd : AlgebraicGeometry.Proj (grading k d lam)) ∈
      Stacks.Ample.nonvanishingLocus (Stacks.ProjTwistSection.twistingModule (grading k d lam) n) t)
    (r : HomogeneousLocalization.AtPrime (grading k d lam)
      (branchPoint k d lam hd).asHomogeneousIdeal.toIdeal)
    (hr : r.val • t.1 ⟨branchPoint k d lam hd, trivial⟩ =
      s.1 ⟨branchPoint k d lam hd, trivial⟩) :
    localHom k d lam hd (tangent k d lam hd) (tangent_vGen k d lam hd) (tangent_fst k d lam hd) r =
      localHom k d lam hd (tangentZero k d lam hd) (tangentZero_vGen k d lam hd)
        (tangentZero_fst k d lam hd) r := by
  obtain ⟨Ns, ms, aS, hms, has, hos, hvs⟩ := exists_eq_mk_split_im_eq_zero k d lam hn s
  obtain ⟨Nt, mt, aT, hmt, hat, hot, hvt⟩ := exists_eq_mk_split_im_eq_zero k d lam hn t
  have hVP := vGen_notMem_branchPoint k d lam hd
  have hatP : aT ∉ (branchPoint k d lam hd).asHomogeneousIdeal :=
    Stacks.ProjMorphismRatios.notMem_of_mem_nonvanishingLocus (vGen_mem k d lam) t hmt hat hvt
      (branchPoint k d lam hd) hVP ht
  have hbt : branchEval k d lam hd aT ≠ 0 := (notMem_branchPoint_iff k d lam hd hat).mp hatP
  rw [hvs _ hVP, hvt _ hVP] at hr
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective r
  rw [HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hr
  obtain ⟨u, hu⟩ := hr
  simp only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul] at hu
  set δ : ring k d lam := vGen k d lam ^ Ns * z.num * aT - z.den * vGen k d lam ^ Nt * aS
    with hδ
  have hδmem : δ ∈ grading k d lam (Ns + z.deg + mt) := by
    have hV : ∀ N : ℕ, vGen k d lam ^ N ∈ grading k d lam N := fun N => by
      simpa using SetLike.pow_mem_graded N (vGen_mem k d lam)
    refine sub_mem (SetLike.mul_mem_graded (SetLike.mul_mem_graded (hV Ns) z.num.2) hat) ?_
    rw [show Ns + z.deg + mt = z.deg + Nt + ms by omega]
    exact SetLike.mul_mem_graded (SetLike.mul_mem_graded z.den.2 (hV Nt)) has
  have huδ : (u : ring k d lam) * δ = 0 := by
    rw [hδ]
    linear_combination hu
  obtain ⟨j, hj, hjδ⟩ := HomogeneousIdeal.exists_decompose_notMem_mul_eq_zero
    (branchPoint k d lam hd).asHomogeneousIdeal hδmem u.2 huδ
  have key : ∀ (ρ : ring k d lam →+* DualNumber k) (hρV : ρ (vGen k d lam) = 1)
      (hρ : ∀ a, (ρ a).fst = branchEval k d lam hd a)
      (_hρ0 : ∀ a, (split k d lam a).im = 0 → ρ a = TrivSqZeroExt.inl (branchEval k d lam hd a)),
      localHom k d lam hd ρ hρV hρ (HomogeneousLocalization.mk z) *
          TrivSqZeroExt.inl (branchEval k d lam hd aT) =
        TrivSqZeroExt.inl (branchEval k d lam hd aS) := by
    intro ρ hρV hρ hρ0
    have huj := isUnit_apply_of_notMem_branchPoint k d lam hd hρ
      (DirectSum.decompose (grading k d lam) (u : ring k d lam) j).2 hj
    have hρδ : ρ δ = 0 := by
      have := congrArg ρ hjδ
      rw [map_mul, map_zero] at this
      exact (huj.mul_right_eq_zero).mp this
    have hre : ρ z.num * ρ aT = ρ z.den * ρ aS := by
      rw [hδ] at hρδ
      simp only [map_sub, map_mul, map_pow, hρV, one_pow, one_mul, mul_one] at hρδ
      linear_combination hρδ
    have he := isUnit_apply_of_notMem_branchPoint k d lam hd hρ z.den.2 z.den_mem
    have hmul := localHom_mk_mul k d lam hd ρ hρV hρ z
    rw [hρ0 _ hot, hρ0 _ hos] at hre
    apply he.mul_left_cancel
    calc ρ z.den * (localHom k d lam hd ρ hρV hρ (HomogeneousLocalization.mk z) *
          TrivSqZeroExt.inl (branchEval k d lam hd aT))
        = (localHom k d lam hd ρ hρV hρ (HomogeneousLocalization.mk z) * ρ z.den) *
          TrivSqZeroExt.inl (branchEval k d lam hd aT) := by ring
      _ = ρ z.num * TrivSqZeroExt.inl (branchEval k d lam hd aT) := by rw [hmul]
      _ = ρ z.den * TrivSqZeroExt.inl (branchEval k d lam hd aS) := hre
  have h1 := key (tangent k d lam hd) (tangent_vGen k d lam hd) (tangent_fst k d lam hd)
    (fun a ha => tangent_eq_inl k d lam hd ha)
  have h2 := key (tangentZero k d lam hd) (tangentZero_vGen k d lam hd)
    (tangentZero_fst k d lam hd) (fun a _ => rfl)
  have hu : IsUnit (TrivSqZeroExt.inl (branchEval k d lam hd aT) : DualNumber k) := by
    rw [TrivSqZeroExt.isUnit_inl_iff, isUnit_iff_ne_zero]
    exact hbt
  exact hu.mul_right_cancel (h1.trans h2.symm)

/-- **[Stacks, Tag 01VP]: if `𝒪_{X_d}(n)` is very ample, then `n ≥ d`.** Here very ample is
relative to any morphism from `X_d` to an affine scheme, the case of the structure morphism
`X_d → Spec k` included.

The proof is the source's. Very ampleness gives an immersion `α : X_d → 𝐏(E)` with
`𝒪_{X_d}(n) ≅ α^* 𝒪(1)`, and over an affine base `𝐏(E)` is the `Proj` of a graded ring generated
in degree one. For `n < d` every global section of `𝒪(n)` is a form in `U`, `V` alone near the
branch point `(λ₁ : 1 : 0)` — this is `Γ(X_d, 𝒪(n)) = k[U, V]_n` — so the two `k[ε]`-points
`Z ↦ ε` and `Z ↦ 0` at the branch point, which agree on `U` and `V`, have the same image under
`α`. An immersion is a monomorphism, and the two points are different. -/
@[stacks 01VP "very ampleness of a twist forces its degree to be at least d"]
public theorem le_of_isRelativelyVeryAmple (hd : 0 < d) {S : Scheme.{u}} [IsAffine S]
    (f : AlgebraicGeometry.Proj (grading k d lam) ⟶ S) (n : ℤ)
    (h : @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple _ _ f
      (Stacks.ProjTwistSection.twistingModule (grading k d lam) n)
      (isInvertible_twistingSheaf k d lam hd n)) :
    (d : ℤ) ≤ n := by
  by_contra hn
  push Not at hn
  haveI := isInvertible_twistingSheaf k d lam hd n
  obtain ⟨E, hE, α, hα, -, ⟨e⟩⟩ :=
    Stacks.VeryAmpleAffineBase.exists_immersion_proj_of_isRelativelyVeryAmple
      (isAffineOpen_top S) f _ h
  have := hE
  have hgen := Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top E (⊤ : S.Opens)
    (isAffineOpen_top S)
  have hcomp := Stacks.ProjMorphismRatios.spec_comp_eq_of_ratio hgen e (branchPoint k d lam hd)
    (stalkHom k d lam hd (tangent k d lam hd) (tangent_vGen k d lam hd) (tangent_fst k d lam hd))
    (stalkHom k d lam hd (tangentZero k d lam hd) (tangentZero_vGen k d lam hd)
      (tangentZero_fst k d lam hd))
    (fun s t ht r hr => by
      rw [stalkHom_stalkIso'_symm, stalkHom_stalkIso'_symm]
      exact localHom_eq_of_smul_eq k d lam hd hn s t ht r hr)
  exact tangent_ne_tangentZero k d lam hd ((cancel_mono α).mp hcomp)

end

end Stacks.ProjHyperellipticDoubleCover

end
