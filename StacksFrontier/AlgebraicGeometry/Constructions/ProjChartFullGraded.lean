module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycle

/-!
# Charts of a graded map `A → Γ_*(T, L)` at a homogeneous element of arbitrary degree

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme and `L` an invertible `𝒪_T`-module. A
graded ring map `ψ : A → Γ_*(T, L)` assigns to a homogeneous element of degree `n` a global
section of `L ^⊗ n`. For a homogeneous `f ∈ A_e` with `e ≥ 1` the fractions `a / f ^ n`, with `a`
homogeneous of degree `n e`, are carried to the ratios `ψ(a) / ψ(f ^ n)` of two global sections of
the *same* tensor power `L ^⊗ (n e)`, so they define a ring map

`A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)`

and hence a chart `T_{ψ(f)} ⟶ D₊(f)`. The charts are indexed by homogeneous `f` of every
positive degree, they cover `U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`, and the charts of two
homogeneous elements agree on their overlap.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections` — **the graded map
  `ψ : A → Γ_*(T, L)`, degreewise**: for each `n` an additive map `𝒜 n →+ Γ(L ^⊗ n, ⊤)`,
  multiplicative across degrees. The unit axiom `ψ(1) = 1` is not required.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.nonvanishingOpenAt` — the open
  `T_{ψ(f)}` on which the section `ψ(f)` of `L ^⊗ e` does not vanish.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.coveringOpen` — **the open
  `U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`** of [Stacks, Tag 01NK].
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homogeneousRatios` — **the family
  of homogeneous ratios `a / f ^ n ↦ ψ(a) / ψ(f ^ n)` for `f` of arbitrary positive degree.**
  Through `Stacks.MorphismToProj.HomogeneousRatios.lift` this is the ring map
  `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.chart` and `chartToProj` — **the
  chart `T_{ψ(f)} ⟶ D₊(f)`**, and the same morphism read into `Proj 𝒜`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.ratioOf_mul` and
  `…ratioOf_mul_cancel` — the ratio of a product by a product is the product of the ratios, and
  the cancellation `ψ(x u) / ψ(t u) = ψ(x) / ψ(t)`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.le_nonvanishingOpen_pow` — **one
  open serves every power of the denominator at once**: wherever `ψ(f)` does not vanish, neither
  does `ψ(f ^ n)`, for every `n` including `n = 0`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.lift_mk` — the value of the ring
  map on the fraction `a / f ^ n`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.lift_comp_awayMap_left` and
  `…_right` — **the chart ring map of the product `f g` restricts to the chart ring maps of `f`
  and of `g`**, along `HomogeneousLocalization.awayMap`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.chartToProj_eq` — **the cocycle
  condition across different degrees**: on an open inside both `T_{ψ(f)}` and `T_{ψ(g)}` the chart
  of `f` and the chart of `g` are the same morphism into `Proj 𝒜`, even when `f` and `g` have
  different degrees.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop trivEquiv)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjChartCocycle
open Stacks.MorphismToProj (HomogeneousRatios)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The input datum -/

section Datum

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- **The graded map `ψ : A → Γ_*(T, L)` of [Stacks, Tag 01NK], degreewise.** For each `n` an
additive map from the degree-`n` part of `A` to the global sections of `L ^⊗ n`, multiplicative
across degrees.

The degree-`n` part of `Γ_*(T, L)` is `Γ(L ^⊗ n, ⊤)`, so this is the family of homogeneous
components of a graded ring map out of `A`. The unit axiom `ψ(1) = 1` is not required. -/
structure GradedSections (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} (L : T.Modules) where
  /-- The degree-`n` component, a map `𝒜 n →+ Γ(L ^⊗ n, ⊤)`. -/
  toFun : ∀ n : ℕ, 𝒜 n →+ Γ(natTensorPow L n, ⊤)
  /-- Multiplicativity across degrees. -/
  map_mul : ∀ (n m : ℕ) (a : 𝒜 n) (b : 𝒜 m) (ab : 𝒜 (n + m)),
    (ab : A) = (a : A) * (b : A) → toFun (n + m) ab = mulSections L (toFun n a) (toFun m b)

end Datum

namespace GradedSections

section Opens

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- **The open `T_{ψ(f)}`** on which the section `ψ(f)` of `L ^⊗ e` does not vanish, for `f`
homogeneous of degree `e`. -/
def nonvanishingOpenAt (e : ℕ) (f : 𝒜 e) : T.Opens :=
  nonvanishingOpen T (natTensorPow L e) (ψ.toFun e f)

/-- **The open `U(ψ) = ⋃_{f ∈ A_+ homogeneous} T_{ψ(f)}`** of [Stacks, Tag 01NK]: the union of
the nonvanishing opens of the sections `ψ(f)` attached to the homogeneous elements of positive
degree. The index `e + 1` runs over the positive degrees. -/
def coveringOpen : T.Opens :=
  ⨆ p : (e : ℕ) × 𝒜 (e + 1), ψ.nonvanishingOpenAt (p.1 + 1) p.2

/-- Each `T_{ψ(f)}` with `f` of positive degree lies in `U(ψ)`. -/
theorem nonvanishingOpenAt_le_coveringOpen (e : ℕ) (f : 𝒜 (e + 1)) :
    ψ.nonvanishingOpenAt (e + 1) f ≤ ψ.coveringOpen :=
  le_iSup (fun p : (e : ℕ) × 𝒜 (e + 1) => ψ.nonvanishingOpenAt (p.1 + 1) p.2) ⟨e, f⟩

/-- A point of `U(ψ)` lies in `T_{ψ(f)}` for some homogeneous `f` of positive degree. -/
theorem exists_mem_nonvanishingOpenAt_of_mem_coveringOpen {t : T}
    (ht : t ∈ ψ.coveringOpen) :
    ∃ (e : ℕ) (f : 𝒜 (e + 1)), t ∈ ψ.nonvanishingOpenAt (e + 1) f := by
  obtain ⟨p, hp⟩ := Opens.mem_iSup.mp ht
  exact ⟨p.1, p.2, hp⟩

end Opens

/-! ### Ratios of values of `ψ` -/

section Ratio

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {V : T.Opens}

/-- The ratio `ψ(x) / ψ(t)` is `1` when `x` and `t` are the same element of `A`. -/
theorem ratioOf_eq_one {k : ℕ} {t x : A} (ht : t ∈ 𝒜 k) (hx : x ∈ 𝒜 k)
    (hV : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩)) (h : x = t) :
    ratioOf L (ψ.toFun k ⟨t, ht⟩) hV (ψ.toFun k ⟨x, hx⟩) = 1 := by
  subst h
  exact ratioOf_self L _ hV

/-- **The ratio `ψ(x) / ψ(t)` depends only on the elements `t` and `x` of `A`, and not on the
index they are read at.** Two indices known to be equal give the same ratio. -/
theorem ratioOf_congr {k k' : ℕ} {t x t' x' : A}
    (ht : t ∈ 𝒜 k) (hx : x ∈ 𝒜 k) (ht' : t' ∈ 𝒜 k') (hx' : x' ∈ 𝒜 k')
    (hV : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L k') (ψ.toFun k' ⟨t', ht'⟩))
    (hk : k = k') (htt : t = t') (hxx : x = x') :
    ratioOf L (ψ.toFun k ⟨t, ht⟩) hV (ψ.toFun k ⟨x, hx⟩)
      = ratioOf L (ψ.toFun k' ⟨t', ht'⟩) hV' (ψ.toFun k' ⟨x', hx'⟩) := by
  subst hk htt hxx
  rfl

/-- **`T_{ψ(t u)} = T_{ψ(t)} ⊓ T_{ψ(u)}`**: a product of values of `ψ` is nonvanishing exactly
where both factors are. -/
theorem nonvanishingOpen_mul {k l : ℕ} {t u : A} (ht : t ∈ 𝒜 k) (hu : u ∈ 𝒜 l)
    (htu : t * u ∈ 𝒜 (k + l)) :
    nonvanishingOpen T (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩)
      = nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩)
        ⊓ nonvanishingOpen T (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩) := by
  rw [ψ.map_mul k l ⟨t, ht⟩ ⟨u, hu⟩ ⟨t * u, htu⟩ rfl, nonvanishingOpen_mulSections]

/-- **A product of values of `ψ` does not vanish where the factors do not.** -/
theorem le_nonvanishingOpen_mul {k l : ℕ} {t u : A} (ht : t ∈ 𝒜 k) (hu : u ∈ 𝒜 l)
    (htu : t * u ∈ 𝒜 (k + l))
    (hVt : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen T (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩)) :
    V ≤ nonvanishingOpen T (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩) := by
  rw [ψ.nonvanishingOpen_mul ht hu htu]
  exact le_inf hVt hVu

/-- **The nonvanishing open of a value of `ψ` depends only on the element and its index.** -/
theorem nonvanishingOpen_congr {k k' : ℕ} {x x' : A} (hx : x ∈ 𝒜 k) (hx' : x' ∈ 𝒜 k')
    (hk : k = k') (hxx : x = x') :
    nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨x, hx⟩)
      = nonvanishingOpen T (natTensorPow L k') (ψ.toFun k' ⟨x', hx'⟩) := by
  subst hk hxx
  rfl

/-- **The ratio of a product by a product is the product of the ratios.** -/
theorem ratioOf_mul {k l : ℕ} {t u x y : A}
    (ht : t ∈ 𝒜 k) (hu : u ∈ 𝒜 l) (hx : x ∈ 𝒜 k) (hy : y ∈ 𝒜 l)
    (htu : t * u ∈ 𝒜 (k + l)) (hxy : x * y ∈ 𝒜 (k + l))
    (hVt : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen T (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩))
    (hVtu : V ≤ nonvanishingOpen T (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩)) :
    ratioOf L (ψ.toFun (k + l) ⟨t * u, htu⟩) hVtu (ψ.toFun (k + l) ⟨x * y, hxy⟩)
      = ratioOf L (ψ.toFun k ⟨t, ht⟩) hVt (ψ.toFun k ⟨x, hx⟩)
        * ratioOf L (ψ.toFun l ⟨u, hu⟩) hVu (ψ.toFun l ⟨y, hy⟩) := by
  refine ratioOf_eq_of_resTop_eq L _ hVtu ?_
  rw [ψ.map_mul k l ⟨x, hx⟩ ⟨y, hy⟩ ⟨x * y, hxy⟩ rfl,
    ψ.map_mul k l ⟨t, ht⟩ ⟨u, hu⟩ ⟨t * u, htu⟩ rfl,
    resTop_mulSections_smul_right L (ψ.toFun k ⟨x, hx⟩)
      (resTop_eq_ratioOf_smul L (ψ.toFun l ⟨u, hu⟩) hVu (ψ.toFun l ⟨y, hy⟩)),
    resTop_mulSections_smul_left L (ψ.toFun l ⟨u, hu⟩)
      (resTop_eq_ratioOf_smul L (ψ.toFun k ⟨t, ht⟩) hVt (ψ.toFun k ⟨x, hx⟩)),
    smul_smul, mul_comm]

/-- **The cancellation `ψ(x u) / ψ(t u) = ψ(x) / ψ(t)`.** -/
theorem ratioOf_mul_cancel {k l : ℕ} {t u x : A}
    (ht : t ∈ 𝒜 k) (hu : u ∈ 𝒜 l) (hx : x ∈ 𝒜 k)
    (htu : t * u ∈ 𝒜 (k + l)) (hxu : x * u ∈ 𝒜 (k + l))
    (hVt : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen T (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩))
    (hVtu : V ≤ nonvanishingOpen T (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩)) :
    ratioOf L (ψ.toFun (k + l) ⟨t * u, htu⟩) hVtu (ψ.toFun (k + l) ⟨x * u, hxu⟩)
      = ratioOf L (ψ.toFun k ⟨t, ht⟩) hVt (ψ.toFun k ⟨x, hx⟩) := by
  rw [ψ.ratioOf_mul ht hu hx hu htu hxu hVt hVu hVtu,
    ψ.ratioOf_eq_one hu hu hVu rfl, mul_one]

end Ratio

/-! ### The charts -/

section Chart

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {e : ℕ} {f : A}
  {V : T.Opens}

variable (hf : f ∈ 𝒜 e)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))

include hV

/-- **One open serves every power of the denominator at once**: wherever `ψ(f)` does not vanish,
neither does `ψ(f ^ n)`, for every `n`, including `n = 0`. -/
theorem le_nonvanishingOpen_pow (n : ℕ) :
    V ≤ nonvanishingOpen T (natTensorPow L (n * e))
      (ψ.toFun (n * e) ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩) := by
  induction n with
  | zero =>
      have h1 : (1 : A) ∈ 𝒜 (0 * e) := by
        simpa [Nat.zero_mul] using SetLike.one_mem_graded 𝒜
      have h1f : (1 : A) * f ∈ 𝒜 (0 * e + e) := by
        simpa [Nat.zero_mul, one_mul] using hf
      have h := ψ.nonvanishingOpen_mul h1 hf h1f
      rw [ψ.nonvanishingOpen_congr h1f hf (by simp) (one_mul f)] at h
      refine le_trans ((hV.trans h.le).trans inf_le_left) (le_of_eq ?_)
      exact ψ.nonvanishingOpen_congr h1 (HomogeneousRatios.pow_mem hf 0) rfl (pow_zero f).symm
  | succ n ih =>
      have hfn : (f : A) ^ n ∈ 𝒜 (n * e) := HomogeneousRatios.pow_mem hf n
      have hstep : (f : A) ^ n * f ∈ 𝒜 (n * e + e) := SetLike.mul_mem_graded hfn hf
      refine le_trans (ψ.le_nonvanishingOpen_mul hfn hf hstep ih hV) (le_of_eq ?_)
      refine ψ.nonvanishingOpen_congr hstep (HomogeneousRatios.pow_mem hf (n + 1))
        (Nat.succ_mul n e).symm ?_
      rw [pow_succ]

/-- **The family of homogeneous ratios `a / f ^ n ↦ ψ(a) / ψ(f ^ n)`, for `f` homogeneous of
arbitrary degree `e`.** Through `Stacks.MorphismToProj.HomogeneousRatios.lift` this is the ring
map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)`, and through `Stacks.MorphismToProj.HomogeneousRatios.chart` the
chart `T_{ψ(f)} ⟶ D₊(f)`. Numerator and denominator are read at the same index `n * e`. -/
def homogeneousRatios : HomogeneousRatios 𝒜 hf ↥Γ(T, V) where
  toFun n :=
    (ratioOfHom L (ψ.toFun (n * e) ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩)
      (ψ.le_nonvanishingOpen_pow hf hV n)).comp (ψ.toFun (n * e))
  map_one a ha :=
    ψ.ratioOf_eq_one (HomogeneousRatios.pow_mem hf 0) a.2
      (ψ.le_nonvanishingOpen_pow hf hV 0) (ha.trans (pow_zero f).symm)
  map_den a ha :=
    ψ.ratioOf_eq_one (HomogeneousRatios.pow_mem hf 1) a.2
      (ψ.le_nonvanishingOpen_pow hf hV 1) (ha.trans (pow_one f).symm)
  map_mul n m a b ab hab := by
    have hfn : (f : A) ^ n ∈ 𝒜 (n * e) := HomogeneousRatios.pow_mem hf n
    have hfm : (f : A) ^ m ∈ 𝒜 (m * e) := HomogeneousRatios.pow_mem hf m
    have hfnm : (f : A) ^ n * f ^ m ∈ 𝒜 (n * e + m * e) := SetLike.mul_mem_graded hfn hfm
    have hab' : (a : A) * (b : A) ∈ 𝒜 (n * e + m * e) := SetLike.mul_mem_graded a.2 b.2
    refine Eq.trans (ψ.ratioOf_congr (HomogeneousRatios.pow_mem hf (n + m)) ab.2 hfnm hab'
      (ψ.le_nonvanishingOpen_pow hf hV (n + m))
      (ψ.le_nonvanishingOpen_mul hfn hfm hfnm (ψ.le_nonvanishingOpen_pow hf hV n)
        (ψ.le_nonvanishingOpen_pow hf hV m))
      (Nat.add_mul n m e) (pow_add f n m) hab) ?_
    exact ψ.ratioOf_mul hfn hfm a.2 b.2 hfnm hab'
      (ψ.le_nonvanishingOpen_pow hf hV n) (ψ.le_nonvanishingOpen_pow hf hV m)
      (ψ.le_nonvanishingOpen_mul hfn hfm hfnm (ψ.le_nonvanishingOpen_pow hf hV n)
        (ψ.le_nonvanishingOpen_pow hf hV m))

/-- The component of `homogeneousRatios` in degree `n` sends `a` to the ratio
`ψ(a) / ψ(f ^ n)`. -/
@[simp] theorem homogeneousRatios_toFun (n : ℕ) (a : 𝒜 (n * e)) :
    (ψ.homogeneousRatios hf hV).toFun n a
      = ratioOf L (ψ.toFun (n * e) ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩)
          (ψ.le_nonvanishingOpen_pow hf hV n) (ψ.toFun (n * e) a) := rfl

/-- **The value of the ring map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` on the fraction `a / f ^ n`**: it is
the ratio `ψ(a) / ψ(f ^ n)` of two global sections of `L ^⊗ (n e)`. -/
theorem lift_mk (he : 0 < e) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • e)) (a : 𝒜 (n * e))
    (ha : (a : A) = x) :
    (ψ.homogeneousRatios hf hV).lift he (HomogeneousLocalization.Away.mk 𝒜 hf n x hx)
      = ratioOf L (ψ.toFun (n * e) ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩)
          (ψ.le_nonvanishingOpen_pow hf hV n) (ψ.toFun (n * e) a) :=
  (ψ.homogeneousRatios hf hV).lift_mk he n x hx a ha

/-- **The chart `T_{ψ(f)} ⟶ D₊(f)`** attached to a homogeneous element `f` of positive degree.
This is `Stacks.MorphismToProj.HomogeneousRatios.chart` of the family of ratios. -/
def chart (he : 0 < e) : V.toScheme ⟶ (AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme :=
  (ψ.homogeneousRatios hf hV).chart he

/-- **The chart read into `Proj 𝒜`.** -/
def chartToProj (he : 0 < e) : V.toScheme ⟶ Proj 𝒜 :=
  (ψ.homogeneousRatios hf hV).chartToProj he

/-- The chart followed by the inclusion `D₊(f) ⟶ Proj 𝒜` is `chartToProj`. -/
@[reassoc] theorem chart_ι (he : 0 < e) :
    ψ.chart hf hV he ≫ (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι = ψ.chartToProj hf hV he :=
  (ψ.homogeneousRatios hf hV).chart_ι he

/-- **The image of the chart lies in `D₊(f)`.** -/
theorem chartToProj_base_mem (he : 0 < e) (t : V.toScheme) :
    (ψ.chartToProj hf hV he).base t ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 f :=
  (ψ.homogeneousRatios hf hV).chartToProj_base_mem he t

end Chart

/-! ### The overlap of two charts of different degrees -/

section Overlap

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {e e' : ℕ} {f g : A}
  {V : T.Opens}

/-- **`AlgebraicGeometry.Proj.awayι` does not depend on the degree index.** Two memberships of
the same element at indices known to be equal give the same morphism `Spec A_{(x)} ⟶ Proj 𝒜`. -/
private theorem awayι_congr_degree {m m' : ℕ} {x : A} (h : x ∈ 𝒜 m) (h' : x ∈ 𝒜 m')
    (hm : 0 < m) (hm' : 0 < m') (hmm : m = m') :
    AlgebraicGeometry.Proj.awayι 𝒜 x h hm = AlgebraicGeometry.Proj.awayι 𝒜 x h' hm' := by
  subst hmm
  rfl

/-- **A fraction of `A_{(t)}` does not depend on the degree index of its denominator.** -/
private theorem away_mk_congr_degree {m m' : ℕ} {t : A} (h : t ∈ 𝒜 m) (h' : t ∈ 𝒜 m')
    (n : ℕ) (p : A) (hp : p ∈ 𝒜 (n • m)) (hp' : p ∈ 𝒜 (n • m')) (hmm : m = m') :
    HomogeneousLocalization.Away.mk 𝒜 h n p hp
      = HomogeneousLocalization.Away.mk 𝒜 h' n p hp' := by
  subst hmm
  rfl

variable (hf : f ∈ 𝒜 e) (hg : g ∈ 𝒜 e')
  (hVf : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
  (hVg : V ≤ nonvanishingOpen T (natTensorPow L e') (ψ.toFun e' ⟨g, hg⟩))

include hVf hVg

/-- **The product `ψ(f g)` does not vanish where both `ψ(f)` and `ψ(g)` do not.** -/
theorem le_nonvanishingOpen_mul_elem :
    V ≤ nonvanishingOpen T (natTensorPow L (e + e'))
      (ψ.toFun (e + e') ⟨f * g, SetLike.mul_mem_graded hf hg⟩) :=
  ψ.le_nonvanishingOpen_mul hf hg (SetLike.mul_mem_graded hf hg) hVf hVg

/-- The chart ring map of `f g` sends the fraction `x b ^ n / (f g) ^ n` to the value of the chart
ring map of `a` on `x / a ^ n`, when `a b = f g` and the degrees add up. -/
private theorem lift_mk_mul_pow {a b : A} {d d' : ℕ} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d')
    (hVa : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨a, ha⟩))
    (hVb : V ≤ nonvanishingOpen T (natTensorPow L d') (ψ.toFun d' ⟨b, hb⟩))
    (hd : d + d' = e + e') (hab : a * b = f * g) (hd0 : 0 < d) (hE : 0 < e + e') (n : ℕ)
    (x : A) (hx : x ∈ 𝒜 (n • d)) (hy : x * b ^ n ∈ 𝒜 (n • (e + e'))) :
    (ψ.homogeneousRatios (SetLike.mul_mem_graded hf hg)
        (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg)).lift hE
      (HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (x * b ^ n) hy)
      = (ψ.homogeneousRatios ha hVa).lift hd0 (HomogeneousLocalization.Away.mk 𝒜 ha n x hx) := by
  have hxe : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  have hpa : a ^ n ∈ 𝒜 (n * d) := HomogeneousRatios.pow_mem ha n
  have hpb : b ^ n ∈ 𝒜 (n * d') := HomogeneousRatios.pow_mem hb n
  have httn : a ^ n * b ^ n ∈ 𝒜 (n * d + n * d') := SetLike.mul_mem_graded hpa hpb
  have hxb : x * b ^ n ∈ 𝒜 (n * d + n * d') := SetLike.mul_mem_graded hxe hpb
  have hmem : x * b ^ n ∈ 𝒜 (n * (e + e')) := by simpa [smul_eq_mul] using hy
  have hVan := ψ.le_nonvanishingOpen_pow ha hVa n
  have hVbn := ψ.le_nonvanishingOpen_pow hb hVb n
  have hVtu := ψ.le_nonvanishingOpen_mul hpa hpb httn hVan hVbn
  rw [ψ.lift_mk (SetLike.mul_mem_graded hf hg)
      (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg) hE n (x * b ^ n) hy
      ⟨x * b ^ n, hmem⟩ rfl,
    ψ.lift_mk ha hVa hd0 n x hx ⟨x, hxe⟩ rfl]
  refine Eq.trans (ψ.ratioOf_congr
    (HomogeneousRatios.pow_mem (SetLike.mul_mem_graded hf hg) n) hmem httn hxb _ hVtu
    (by rw [← hd, Nat.mul_add]) (by rw [← hab, mul_pow]) rfl) ?_
  exact ψ.ratioOf_mul_cancel hpa hpb hxe httn hxb hVan hVbn hVtu

/-- **The chart ring map of the product `f g` restricts to the chart ring map of `f`** along
`HomogeneousLocalization.awayMap`, which sends `a / f ^ n` to `a g ^ n / (f g) ^ n`. -/
theorem lift_comp_awayMap_left (he : 0 < e) (hE : 0 < e + e') :
    ((ψ.homogeneousRatios (SetLike.mul_mem_graded hf hg)
          (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg)).lift hE).comp
        (HomogeneousLocalization.awayMap 𝒜 hg (rfl : f * g = f * g))
      = (ψ.homogeneousRatios hf hVf).lift he := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx => ?_
  have hmem : x * g ^ n ∈ 𝒜 (n • (e + e')) := by
    simpa [smul_eq_mul, Nat.mul_add] using SetLike.mul_mem_graded
      (by simpa [smul_eq_mul] using hx : x ∈ 𝒜 (n * e)) (HomogeneousRatios.pow_mem hg n)
  have key : HomogeneousLocalization.awayMap 𝒜 hg (rfl : f * g = f * g)
        (HomogeneousLocalization.Away.mk 𝒜 hf n x hx)
      = HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (x * g ^ n) hmem := by
    rw [HomogeneousLocalization.awayMap_mk]
  change (ψ.homogeneousRatios (SetLike.mul_mem_graded hf hg)
    (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg)).lift hE
      (HomogeneousLocalization.awayMap 𝒜 hg rfl
        (HomogeneousLocalization.Away.mk 𝒜 hf n x hx)) = _
  rw [key]
  exact ψ.lift_mk_mul_pow hf hg hVf hVg hf hg hVf hVg rfl rfl he hE n x hx hmem

/-- **The chart ring map of the product `f g` restricts to the chart ring map of `g`** along
`HomogeneousLocalization.awayMap`, which sends `a / g ^ n` to `a f ^ n / (f g) ^ n`. -/
theorem lift_comp_awayMap_right (he' : 0 < e') (hE : 0 < e + e') :
    ((ψ.homogeneousRatios (SetLike.mul_mem_graded hf hg)
          (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg)).lift hE).comp
        (HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g))
      = (ψ.homogeneousRatios hg hVg).lift he' := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hg fun n x hx => ?_
  have hmem : x * f ^ n ∈ 𝒜 (n • (e + e')) := by
    simpa [smul_eq_mul, Nat.mul_add, add_comm] using SetLike.mul_mem_graded
      (by simpa [smul_eq_mul] using hx : x ∈ 𝒜 (n * e')) (HomogeneousRatios.pow_mem hf n)
  have key : HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
        (HomogeneousLocalization.Away.mk 𝒜 hg n x hx)
      = HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (x * f ^ n) hmem := by
    rw [HomogeneousLocalization.awayMap_mk]
    exact away_mk_congr_degree _ _ n (x * f ^ n) _ hmem (Nat.add_comm e' e)
  change (ψ.homogeneousRatios (SetLike.mul_mem_graded hf hg)
    (ψ.le_nonvanishingOpen_mul_elem hf hg hVf hVg)).lift hE
      (HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g)
        (HomogeneousLocalization.Away.mk 𝒜 hg n x hx)) = _
  rw [key]
  exact ψ.lift_mk_mul_pow hf hg hVf hVg hg hf hVg hVf (Nat.add_comm e' e) (mul_comm g f)
    he' hE n x hx hmem

/-- **The cocycle condition at the level of `Spec Γ(T, V)`:** the morphisms
`Spec Γ(T, V) ⟶ Proj 𝒜` induced by the chart ring maps of `f` and of `g` through `Spec A_{(f)}`
and `Spec A_{(g)}` coincide. -/
theorem specMap_lift_awayι_eq (he : 0 < e) (he' : 0 < e') (hE : 0 < e + e') :
    Spec.map (CommRingCat.ofHom ((ψ.homogeneousRatios hf hVf).lift he))
        ≫ AlgebraicGeometry.Proj.awayι 𝒜 f hf he
      = Spec.map (CommRingCat.ofHom ((ψ.homogeneousRatios hg hVg).lift he'))
        ≫ AlgebraicGeometry.Proj.awayι 𝒜 g hg he' := by
  rw [← ψ.lift_comp_awayMap_left hf hg hVf hVg he hE,
    ← ψ.lift_comp_awayMap_right hf hg hVf hVg he' hE,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, AlgebraicGeometry.Proj.SpecMap_awayMap_awayι,
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι]
  exact congrArg _ (awayι_congr_degree _ _ _ _ (Nat.add_comm e e'))

/-- **The cocycle condition for the charts into `Proj 𝒜`, across different degrees.** On an open
inside both `T_{ψ(f)}` and `T_{ψ(g)}` the chart of `f` and the chart of `g` are one and the same
morphism, even when `f` and `g` are homogeneous of different degrees. -/
theorem chartToProj_eq (he : 0 < e) (he' : 0 < e') (hE : 0 < e + e') :
    ψ.chartToProj hf hVf he = ψ.chartToProj hg hVg he' := by
  unfold chartToProj HomogeneousRatios.chartToProj HomogeneousRatios.toSpecAway
  rw [Category.assoc, Category.assoc, ψ.specMap_lift_awayι_eq hf hg hVf hVg he he' hE]

end Overlap

end GradedSections

end Stacks.AlgebraicGeometry.ProjChartFullGraded

end
