module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGluing

/-!
# The cocycle condition for the charts into `Proj`, and the glued morphism

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, `d > 0`, and let
`U_d = ⋃_{f ∈ 𝒜 d} D₊(f) ⊆ X`. Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module and
`ψ : A^{(d)} → Γ_*(Y, L)` a graded map, given as
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`. For `f ∈ 𝒜 d` and an open
`W ≤ Y_{ψ(f)}` there is a chart `W ⟶ D₊(f) ⊆ U_d`. This file proves that the charts of two
elements agree on the overlap, and glues the charts over a family of opens covering `Y` into a
morphism `φ : Y ⟶ U_d`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf`: the ratio `x / t` of a global section of
  an invertible module by a global section that does not vanish on the open in question.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.prodPow`: the global section `ψ((f g)^n)` of
  `L ^⊗ (n + n)`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.prodRatios`: the family of homogeneous ratios for
  `f g`, i.e. the ring map `A_{(f g)} → Γ(Y, V)` sending `x / (f g)^n` to `ψ(x) / ψ((f g)^n)`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.opensCover`: a family of opens covering `Y`, as an
  `AlgebraicGeometry.Scheme.OpenCover`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.glued`: the morphism `φ : Y ⟶ U_d` glued from the
  charts over a family of opens `W g ≤ Y_{ψ(g)}` covering `Y`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf_psi_mul` and
  `Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf_psi_mul_cancel`: the ratio of a product by a
  product is the product of the ratios, and hence `ψ(x u) / ψ(t u) = ψ(x) / ψ(t)`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.lift_prodRatios_comp_awayMap_left` and
  `Stacks.AlgebraicGeometry.ProjChartCocycle.lift_prodRatios_comp_awayMap_right`: the ring map on
  `A_{(f g)}` restricts along `HomogeneousLocalization.awayMap` to the chart ring maps of `f` and
  of `g`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.toDegreeOpen_eq`: on an open inside
  `Y_{ψ(f)} ⊓ Y_{ψ(g)}` the chart of `f` and the chart of `g` are the same morphism into `U_d`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.comp_toDegreeOpen_eq`: the same, after composing
  with two morphisms into the two opens that agree over `Y`.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.ι_glued`: `φ` restricts to the chart on each member
  of the cover.
* `Stacks.AlgebraicGeometry.ProjChartCocycle.preimage_basicOpen_glued`: the preimage of `D₊(e)`
  under `φ` is `Y_{ψ(e)}`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop trivEquiv)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.MorphismToProj (HomogeneousRatios)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartCocycle

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The ratio by an arbitrary nonvanishing section -/

section Ratio

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- The ratio `x / t` of a global section `x` of an invertible module by a global section `t`
that does not vanish on the open `V`: the unique `c ∈ Γ(Y, V)` with `x|_V = c · t|_V`. -/
def ratioOf {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) (x : Γ(natTensorPow L n, ⊤)) : Γ(Y, V) :=
  (trivEquiv (natTensorPow L n) t hV).symm (resTop (natTensorPow L n) x V)

/-- The ratio by a fixed denominator, as an additive map in the numerator. -/
def ratioOfHom {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) :
    Γ(natTensorPow L n, ⊤) →+ Γ(Y, V) :=
  ((trivEquiv (natTensorPow L n) t hV).symm.toAddMonoidHom).comp (resTopHom (natTensorPow L n) V)

/-- `ratioOfHom L t hV` sends `x` to the ratio `x / t`. -/
@[simp] theorem ratioOfHom_apply {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) (x : Γ(natTensorPow L n, ⊤)) :
    ratioOfHom L t hV x = ratioOf L t hV x := rfl

/-- The ratio satisfies `x|_V = (x / t) · t|_V`. -/
theorem resTop_eq_ratioOf_smul {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) (x : Γ(natTensorPow L n, ⊤)) :
    resTop (natTensorPow L n) x V = ratioOf L t hV x • resTop (natTensorPow L n) t V :=
  (Stacks.TensorPowerTrivialize.trivEquiv_symm_smul (natTensorPow L n) t hV
    (resTop (natTensorPow L n) x V)).symm

/-- If `x|_V = c · t|_V`, then the ratio `x / t` is `c`. -/
theorem ratioOf_eq_of_resTop_eq {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) {x : Γ(natTensorPow L n, ⊤)}
    {c : Γ(Y, V)} (h : resTop (natTensorPow L n) x V = c • resTop (natTensorPow L n) t V) :
    ratioOf L t hV x = c := by
  rw [ratioOf, h]
  exact (trivEquiv (natTensorPow L n) t hV).symm_apply_apply c

/-- The ratio of a section by itself is `1`. -/
@[simp] theorem ratioOf_self {n : ℕ} {V : Y.Opens} (t : Γ(natTensorPow L n, ⊤))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L n) t) : ratioOf L t hV t = 1 :=
  ratioOf_eq_of_resTop_eq L t hV (by rw [one_smul])

end Ratio

/-! ### Reading a graded piece at an equal index -/

section Cast

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- The graded piece `𝒜 k` read at an equal index `k'`, as an additive map that does not change
the underlying element of `A`. -/
def degreeCast (𝒜 : ℕ → σ) {k k' : ℕ} (h : k = k') : (𝒜 k) →+ (𝒜 k') where
  toFun a := ⟨(a : A), h ▸ a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `degreeCast` does not change the underlying element of `A`. -/
@[simp] theorem degreeCast_coe (𝒜 : ℕ → σ) {k k' : ℕ} (h : k = k') (a : 𝒜 k) :
    ((degreeCast 𝒜 h a : 𝒜 k') : A) = (a : A) := rfl

end Cast

/-! ### Ratios of values of `ψ` -/

section Psi

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] (ψ : VeroneseSections 𝒜 d L) {V : Y.Opens}

/-- The ratio `ψ(x) / ψ(t)` is `1` when `x` and `t` are the same element of `A`. -/
theorem ratioOf_psi_self {k : ℕ} {t x : A} (ht : t ∈ 𝒜 (k * d)) (hx : x ∈ 𝒜 (k * d))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩)) (h : x = t) :
    ratioOf L (ψ.toFun k ⟨t, ht⟩) hV (ψ.toFun k ⟨x, hx⟩) = 1 := by
  subst h
  exact ratioOf_self L _ hV

/-- The ratio `ψ(x) / ψ(t)` depends only on the elements `t` and `x` of `A`, and not on the
index they are read at. -/
theorem ratioOf_psi_congr {k k' : ℕ} {t x t' x' : A}
    (ht : t ∈ 𝒜 (k * d)) (hx : x ∈ 𝒜 (k * d)) (ht' : t' ∈ 𝒜 (k' * d)) (hx' : x' ∈ 𝒜 (k' * d))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hV' : V ≤ nonvanishingOpen Y (natTensorPow L k') (ψ.toFun k' ⟨t', ht'⟩))
    (hk : k = k') (htt : t = t') (hxx : x = x') :
    ratioOf L (ψ.toFun k ⟨t, ht⟩) hV (ψ.toFun k ⟨x, hx⟩)
      = ratioOf L (ψ.toFun k' ⟨t', ht'⟩) hV' (ψ.toFun k' ⟨x', hx'⟩) := by
  subst hk htt hxx
  rfl

/-- A product of values of `ψ` does not vanish where the factors do not. -/
theorem le_nonvanishingOpen_psi_mul {k l : ℕ} {t u : A} (ht : t ∈ 𝒜 (k * d)) (hu : u ∈ 𝒜 (l * d))
    (htu : t * u ∈ 𝒜 ((k + l) * d))
    (hVt : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen Y (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩)) :
    V ≤ nonvanishingOpen Y (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩) := by
  rw [ψ.map_mul k l ⟨t, ht⟩ ⟨u, hu⟩ ⟨t * u, htu⟩ rfl, nonvanishingOpen_mulSections]
  exact le_inf hVt hVu

/-- The ratio of a product by a product is the product of the ratios:
`ψ(x y) / ψ(t u) = (ψ(x) / ψ(t)) · (ψ(y) / ψ(u))`. -/
theorem ratioOf_psi_mul {k l : ℕ} {t u x y : A}
    (ht : t ∈ 𝒜 (k * d)) (hu : u ∈ 𝒜 (l * d)) (hx : x ∈ 𝒜 (k * d)) (hy : y ∈ 𝒜 (l * d))
    (htu : t * u ∈ 𝒜 ((k + l) * d)) (hxy : x * y ∈ 𝒜 ((k + l) * d))
    (hVt : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen Y (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩))
    (hVtu : V ≤ nonvanishingOpen Y (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩)) :
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

/-- The cancellation `ψ(x u) / ψ(t u) = ψ(x) / ψ(t)`. -/
theorem ratioOf_psi_mul_cancel {k l : ℕ} {t u x : A}
    (ht : t ∈ 𝒜 (k * d)) (hu : u ∈ 𝒜 (l * d)) (hx : x ∈ 𝒜 (k * d))
    (htu : t * u ∈ 𝒜 ((k + l) * d)) (hxu : x * u ∈ 𝒜 ((k + l) * d))
    (hVt : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen Y (natTensorPow L l) (ψ.toFun l ⟨u, hu⟩))
    (hVtu : V ≤ nonvanishingOpen Y (natTensorPow L (k + l)) (ψ.toFun (k + l) ⟨t * u, htu⟩)) :
    ratioOf L (ψ.toFun (k + l) ⟨t * u, htu⟩) hVtu (ψ.toFun (k + l) ⟨x * u, hxu⟩)
      = ratioOf L (ψ.toFun k ⟨t, ht⟩) hVt (ψ.toFun k ⟨x, hx⟩) := by
  rw [ratioOf_psi_mul ψ ht hu hx hu htu hxu hVt hVu hVtu,
    ratioOf_psi_self ψ hu hu hVu rfl, mul_one]

end Psi

/-! ### The overlap datum for `f g` -/

section Prod

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] (ψ : VeroneseSections 𝒜 d L) {f g : A}

/-- A power of `f g` is homogeneous of Veronese degree `n + n`. -/
theorem prodPow_mem (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (n : ℕ) :
    (f * g) ^ n ∈ 𝒜 ((n + n) * d) :=
  (show n * (d + d) = (n + n) * d by ring) ▸
    HomogeneousRatios.pow_mem (SetLike.mul_mem_graded hf hg) n

/-- The global section `ψ((f g)^n)` of `L ^⊗ (n + n)`. -/
def prodPow (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (n : ℕ) : Γ(natTensorPow L (n + n), ⊤) :=
  ψ.toFun (n + n) ⟨(f * g) ^ n, prodPow_mem hf hg n⟩

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The section `ψ((f g)^n)` is the product of `ψ(f^n)` and `ψ(g^n)`. -/
theorem prodPow_eq (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (n : ℕ) :
    prodPow ψ hf hg n = mulSections L (ψ.pow hf n) (ψ.pow hg n) :=
  ψ.map_mul n n ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩ ⟨g ^ n, HomogeneousRatios.pow_mem hg n⟩
    ⟨(f * g) ^ n, prodPow_mem hf hg n⟩ (mul_pow f g n)

variable {V : Y.Opens}

/-- The section `ψ((f g)^n)` does not vanish on an open inside both `Y_{ψ(f)}` and
`Y_{ψ(g)}`. -/
theorem le_nonvanishingOpen_prodPow (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d)
    (hVf : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))
    (hVg : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hg 1)) (n : ℕ) :
    V ≤ nonvanishingOpen Y (natTensorPow L (n + n)) (prodPow ψ hf hg n) := by
  rw [prodPow_eq, nonvanishingOpen_mulSections]
  exact le_inf (ψ.le_nonvanishingOpen hf hVf n) (ψ.le_nonvanishingOpen hg hVg n)

variable (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d)
  (hVf : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))
  (hVg : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hg 1))

include hVf hVg

/-- The degreewise datum of the ring map on `A_{(f g)}`: `a ∈ 𝒜 (n * (d + d))` goes to the ratio
`ψ(a) / ψ((f g)^n)`, with `a` read in degree `(n + n) * d`. -/
def prodFun (n : ℕ) : (𝒜 (n * (d + d))) →+ ↥Γ(Y, V) :=
  (ratioOfHom L (prodPow ψ hf hg n) (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg n)).comp
    ((ψ.toFun (n + n)).comp (degreeCast 𝒜 (show n * (d + d) = (n + n) * d by ring)))

/-- The value of `prodFun` at `a` is the ratio `ψ(a) / ψ((f g)^n)` read at any index `k` with
`k = n + n`. -/
theorem prodFun_eq (n : ℕ) (a : 𝒜 (n * (d + d))) {k : ℕ} {t x : A}
    (ht : t ∈ 𝒜 (k * d)) (hx : x ∈ 𝒜 (k * d))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hk : k = n + n) (hte : t = (f * g) ^ n) (hxe : x = (a : A)) :
    prodFun ψ hf hg hVf hVg n a = ratioOf L (ψ.toFun k ⟨t, ht⟩) hV (ψ.toFun k ⟨x, hx⟩) := by
  subst hte hxe hk
  rfl

/-- The family of homogeneous ratios for `f g`, i.e. the ring map `A_{(f g)} → Γ(Y, V)` sending
`x / (f g)^n` to `ψ(x) / ψ((f g)^n)`. -/
def prodRatios : HomogeneousRatios 𝒜 (SetLike.mul_mem_graded hf hg) ↥Γ(Y, V) where
  toFun := prodFun ψ hf hg hVf hVg
  map_one a ha := by
    have hx : (a : A) ∈ 𝒜 ((0 + 0) * d) := (show 0 * (d + d) = (0 + 0) * d by ring) ▸ a.2
    rw [prodFun_eq ψ hf hg hVf hVg 0 a (prodPow_mem hf hg 0) hx
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg 0) rfl rfl rfl]
    exact ratioOf_psi_self ψ (prodPow_mem hf hg 0) hx _ (by rw [ha, pow_zero])
  map_den a ha := by
    have hx : (a : A) ∈ 𝒜 ((1 + 1) * d) := (show 1 * (d + d) = (1 + 1) * d by ring) ▸ a.2
    rw [prodFun_eq ψ hf hg hVf hVg 1 a (prodPow_mem hf hg 1) hx
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg 1) rfl rfl rfl]
    exact ratioOf_psi_self ψ (prodPow_mem hf hg 1) hx _ (by rw [ha, pow_one])
  map_mul n m a b ab hab := by
    have ha' : (a : A) ∈ 𝒜 ((n + n) * d) := (show n * (d + d) = (n + n) * d by ring) ▸ a.2
    have hb' : (b : A) ∈ 𝒜 ((m + m) * d) := (show m * (d + d) = (m + m) * d by ring) ▸ b.2
    have hmemt : (f * g) ^ n * (f * g) ^ m ∈ 𝒜 ((n + n + (m + m)) * d) :=
      Nat.add_mul _ _ d ▸ SetLike.mul_mem_graded (prodPow_mem hf hg n) (prodPow_mem hf hg m)
    have hmemx : (a : A) * (b : A) ∈ 𝒜 ((n + n + (m + m)) * d) :=
      Nat.add_mul _ _ d ▸ SetLike.mul_mem_graded ha' hb'
    have hVbig := le_nonvanishingOpen_psi_mul ψ (prodPow_mem hf hg n) (prodPow_mem hf hg m) hmemt
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg n)
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg m)
    rw [prodFun_eq ψ hf hg hVf hVg (n + m) ab hmemt hmemx hVbig (by ring)
        (pow_add (f * g) n m).symm hab.symm,
      prodFun_eq ψ hf hg hVf hVg n a (prodPow_mem hf hg n) ha'
        (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg n) rfl rfl rfl,
      prodFun_eq ψ hf hg hVf hVg m b (prodPow_mem hf hg m) hb'
        (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg m) rfl rfl rfl]
    exact ratioOf_psi_mul ψ (prodPow_mem hf hg n) (prodPow_mem hf hg m) ha' hb' hmemt hmemx
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg n)
      (le_nonvanishingOpen_prodPow ψ hf hg hVf hVg m) hVbig

/-- The value of `prodFun` at `x u`, where `t u = (f g)^n`, is the ratio `ψ(x) / ψ(t)`. -/
private theorem prodFun_mul_eq_ratioOf (n : ℕ) {t u x : A} (ht : t ∈ 𝒜 (n * d))
    (hu : u ∈ 𝒜 (n * d)) (hx : x ∈ 𝒜 (n * d)) (hxu : x * u ∈ 𝒜 (n * (d + d)))
    (htu : t * u = (f * g) ^ n)
    (hVt : V ≤ nonvanishingOpen Y (natTensorPow L n) (ψ.toFun n ⟨t, ht⟩))
    (hVu : V ≤ nonvanishingOpen Y (natTensorPow L n) (ψ.toFun n ⟨u, hu⟩)) :
    prodFun ψ hf hg hVf hVg n ⟨x * u, hxu⟩
      = ratioOf L (ψ.toFun n ⟨t, ht⟩) hVt (ψ.toFun n ⟨x, hx⟩) := by
  have hmem : ∀ {a b : A}, a ∈ 𝒜 (n * d) → b ∈ 𝒜 (n * d) → a * b ∈ 𝒜 ((n + n) * d) :=
    fun ha hb ↦ Nat.add_mul n n d ▸ SetLike.mul_mem_graded ha hb
  rw [prodFun_eq ψ hf hg hVf hVg n ⟨x * u, hxu⟩ (htu ▸ hmem ht hu) (hmem hx hu)
    (le_nonvanishingOpen_psi_mul ψ ht hu (hmem ht hu) hVt hVu) rfl htu rfl]
  exact ratioOf_psi_mul_cancel ψ ht hu hx (hmem ht hu) (hmem hx hu) hVt hVu _

omit hVg in
/-- The degreewise datum of the chart of `f` is the ratio by `ψ(f ^ n)`. -/
theorem homogeneousRatios_toFun_eq (n : ℕ) (a : 𝒜 (n * d)) :
    (ψ.homogeneousRatios hf hVf).toFun n a
      = ratioOf L (ψ.toFun n ⟨f ^ n, HomogeneousRatios.pow_mem hf n⟩)
          (ψ.le_nonvanishingOpen hf hVf n) (ψ.toFun n a) := rfl

/-! ### The overlap ring map restricts to the two chart ring maps -/

/-- The ring map on `A_{(f g)}` restricts to the chart ring map of `f` along
`HomogeneousLocalization.awayMap`, the map `A_{(f)} → A_{(f g)}` sending `a / f^n` to
`a g^n / (f g)^n`. -/
theorem lift_prodRatios_comp_awayMap_left (hd : 0 < d) (hD : 0 < d + d) :
    ((prodRatios ψ hf hg hVf hVg).lift hD).comp (awayMap 𝒜 hg (rfl : f * g = f * g))
      = (ψ.homogeneousRatios hf hVf).lift hd := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx ↦ ?_
  have hxd : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  have hmem2 : x * g ^ n ∈ 𝒜 (n * (d + d)) :=
    (show (n + n) * d = n * (d + d) by ring) ▸ Nat.add_mul n n d ▸
      SetLike.mul_mem_graded hxd (HomogeneousRatios.pow_mem hg n)
  have hmem : x * g ^ n ∈ 𝒜 (n • (d + d)) := by simpa [smul_eq_mul] using hmem2
  change (prodRatios ψ hf hg hVf hVg).lift hD (awayMap 𝒜 hg rfl (Away.mk 𝒜 hf n x hx)) = _
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousRatios.lift_mk _ hD n (x * g ^ n) hmem ⟨x * g ^ n, hmem2⟩ rfl,
    HomogeneousRatios.lift_mk _ hd n x hx ⟨x, hxd⟩ rfl, homogeneousRatios_toFun_eq]
  exact prodFun_mul_eq_ratioOf ψ hf hg hVf hVg n (HomogeneousRatios.pow_mem hf n)
    (HomogeneousRatios.pow_mem hg n) hxd hmem2 (mul_pow f g n).symm
    (ψ.le_nonvanishingOpen hf hVf n) (ψ.le_nonvanishingOpen hg hVg n)

/-- The ring map on `A_{(f g)}` restricts to the chart ring map of `g` along
`HomogeneousLocalization.awayMap`, the map `A_{(g)} → A_{(f g)}` sending `a / g^n` to
`a f^n / (f g)^n`. -/
theorem lift_prodRatios_comp_awayMap_right (hd : 0 < d) (hD : 0 < d + d) :
    ((prodRatios ψ hf hg hVf hVg).lift hD).comp (awayMap 𝒜 hf (mul_comm f g))
      = (ψ.homogeneousRatios hg hVg).lift hd := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hg fun n x hx ↦ ?_
  have hxd : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  have hmem2 : x * f ^ n ∈ 𝒜 (n * (d + d)) :=
    (show (n + n) * d = n * (d + d) by ring) ▸ Nat.add_mul n n d ▸
      SetLike.mul_mem_graded hxd (HomogeneousRatios.pow_mem hf n)
  have hmem : x * f ^ n ∈ 𝒜 (n • (d + d)) := by simpa [smul_eq_mul] using hmem2
  change (prodRatios ψ hf hg hVf hVg).lift hD (awayMap 𝒜 hf (mul_comm f g)
    (Away.mk 𝒜 hg n x hx)) = _
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousRatios.lift_mk _ hD n (x * f ^ n) hmem ⟨x * f ^ n, hmem2⟩ rfl,
    HomogeneousRatios.lift_mk _ hd n x hx ⟨x, hxd⟩ rfl, homogeneousRatios_toFun_eq]
  exact prodFun_mul_eq_ratioOf ψ hf hg hVf hVg n (HomogeneousRatios.pow_mem hg n)
    (HomogeneousRatios.pow_mem hf n) hxd hmem2 (by ring)
    (ψ.le_nonvanishingOpen hg hVg n) (ψ.le_nonvanishingOpen hf hVf n)

/-! ### The cocycle -/

/-- The morphisms `Spec Γ(Y, V) ⟶ D₊(f) ⟶ Proj 𝒜` and `Spec Γ(Y, V) ⟶ D₊(g) ⟶ Proj 𝒜` induced
by the chart ring maps of `f` and of `g` coincide. -/
theorem specMap_lift_awayι_eq (hd : 0 < d) (hD : 0 < d + d) :
    Spec.map (CommRingCat.ofHom ((ψ.homogeneousRatios hf hVf).lift hd))
        ≫ AlgebraicGeometry.Proj.awayι 𝒜 f hf hd
      = Spec.map (CommRingCat.ofHom ((ψ.homogeneousRatios hg hVg).lift hd))
        ≫ AlgebraicGeometry.Proj.awayι 𝒜 g hg hd := by
  rw [← lift_prodRatios_comp_awayMap_left ψ hf hg hVf hVg hd hD,
    ← lift_prodRatios_comp_awayMap_right ψ hf hg hVf hVg hd hD,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, AlgebraicGeometry.Proj.SpecMap_awayMap_awayι,
    AlgebraicGeometry.Proj.SpecMap_awayMap_awayι]

/-- On an open inside both `Y_{ψ(f)}` and `Y_{ψ(g)}` the chart of `f` and the chart of `g` are
the same morphism into `Proj 𝒜`. -/
theorem chartToProj_eq (hd : 0 < d) (hD : 0 < d + d) :
    (ψ.homogeneousRatios hf hVf).chartToProj hd
      = (ψ.homogeneousRatios hg hVg).chartToProj hd := by
  unfold HomogeneousRatios.chartToProj HomogeneousRatios.toSpecAway
  rw [Category.assoc, Category.assoc, specMap_lift_awayι_eq ψ hf hg hVf hVg hd hD]

/-- On an open inside both `Y_{ψ(f)}` and `Y_{ψ(g)}` the chart of `f` and the chart of `g` are
the same morphism into `U_d`. -/
theorem toDegreeOpen_eq (hd : 0 < d) (hD : 0 < d + d) :
    ψ.toDegreeOpen hf hVf hd = ψ.toDegreeOpen hg hVg hd := by
  have h : ∀ (e : A) (he : e ∈ 𝒜 d) (V' : Y.Opens)
      (hV : V' ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow he 1)),
      ψ.toDegreeOpen he hV hd ≫ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).ι
        = (ψ.homogeneousRatios he hV).chartToProj hd :=
    fun _ he _ hV ↦ HomogeneousRatios.toProj_toDegreeOpen (ψ.homogeneousRatios he hV) hd
  rw [← cancel_mono (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).ι, h f hf V hVf,
    h g hg V hVg]
  exact chartToProj_eq ψ hf hg hVf hVg hd hD

end Prod

/-! ### The glued morphism -/

section Glue

open Stacks.AlgebraicGeometry.MorphismsIntoProj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- If a scheme `T` maps to `V` and to `V'` compatibly over `Y`, then the chart of `f` over `V`
and the chart of `g` over `V'` agree after composing with those two morphisms. -/
theorem comp_toDegreeOpen_eq {ψ : VeroneseSections 𝒜 d L} {f g : A} (hf : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 d) {V V' : Y.Opens}
    (hVf : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))
    (hV'g : V' ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hg 1)) (hd : 0 < d)
    (hD : 0 < d + d) {T : Scheme.{u}} (a : T ⟶ V.toScheme) (b : T ⟶ V'.toScheme)
    (hab : a ≫ V.ι = b ≫ V'.ι) :
    a ≫ ψ.toDegreeOpen hf hVf hd = b ≫ ψ.toDegreeOpen hg hV'g hd := by
  have hrange : Set.range (a ≫ V.ι).base ⊆ Set.range (V ⊓ V' : Y.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨t, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_base]
      exact (Scheme.Opens.range_ι V) ▸ Set.mem_range_self (a.base t)
    · rw [hab, Scheme.Hom.comp_base]
      exact (Scheme.Opens.range_ι V') ▸ Set.mem_range_self (b.base t)
  have hc := IsOpenImmersion.lift_fac (V ⊓ V' : Y.Opens).ι (a ≫ V.ι) hrange
  have ha : a = IsOpenImmersion.lift (V ⊓ V' : Y.Opens).ι (a ≫ V.ι) hrange
      ≫ Y.homOfLE (inf_le_left : V ⊓ V' ≤ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hc]
  have hb : b = IsOpenImmersion.lift (V ⊓ V' : Y.Opens).ι (a ≫ V.ι) hrange
      ≫ Y.homOfLE (inf_le_right : V ⊓ V' ≤ V') := by
    rw [← cancel_mono V'.ι, Category.assoc, Scheme.homOfLE_ι, hc, hab]
  rw [ha, hb, Category.assoc, Category.assoc,
    ψ.homOfLE_toDegreeOpen hf hVf hd (inf_le_left : V ⊓ V' ≤ V),
    ψ.homOfLE_toDegreeOpen hg hV'g hd (inf_le_right : V ⊓ V' ≤ V'),
    toDegreeOpen_eq ψ hf hg (le_trans inf_le_left hVf) (le_trans inf_le_right hV'g) hd hD]

/-- A family of opens covering `Y`, as an open cover. -/
def opensCover {W : 𝒜 d → Y.Opens} (hcover : ⨆ g : 𝒜 d, W g = ⊤) : Y.OpenCover :=
  Scheme.Cover.mkOfCovers (𝒜 d) (fun g ↦ (W g).toScheme) (fun g ↦ (W g).ι) fun y ↦ by
    obtain ⟨g, hy⟩ := Opens.mem_iSup.mp (hcover ▸ (Opens.mem_top y : y ∈ (⊤ : Y.Opens)))
    exact ⟨g, ⟨y, hy⟩, rfl⟩

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The member of `opensCover` at `g` is the inclusion of `W g`. -/
@[simp] theorem opensCover_f {W : 𝒜 d → Y.Opens} (hcover : ⨆ g : 𝒜 d, W g = ⊤) (g : 𝒜 d) :
    (opensCover 𝒜 hcover).f g = (W g).ι := rfl

/-- The morphism `φ : Y ⟶ U_d` glued from the charts over a family of opens `W g ≤ Y_{ψ(g)}`,
one for each `g ∈ 𝒜 d`, covering `Y`. -/
def glued (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d) {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤) : Y ⟶ (degreeOpen 𝒜 d).toScheme :=
  (opensCover 𝒜 hcover).glueMorphisms (fun g ↦ ψ.toDegreeOpen g.2 (hWle g) hd)
    fun i j ↦ comp_toDegreeOpen_eq 𝒜 i.2 j.2 (hWle i) (hWle j) hd
      (hd.trans_le (Nat.le_add_right d d)) (Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
      Limits.pullback.condition

/-- The glued morphism restricts to the chart on each member of the cover. -/
theorem ι_glued (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d) {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤) (g : 𝒜 d) :
    (W g).ι ≫ glued 𝒜 ψ hd hWle hcover = ψ.toDegreeOpen g.2 (hWle g) hd :=
  Scheme.Cover.ι_glueMorphisms (opensCover 𝒜 hcover) _ _ g

/-- The preimage of the standard open `D₊(e)` under the glued morphism `φ` is the nonvanishing
open `Y_{ψ(e)}`. -/
theorem preimage_basicOpen_glued (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d)
    {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤) (e : 𝒜 d) :
    toProj 𝒜 (glued 𝒜 ψ hd hWle hcover) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (e : A) =
      nonvanishingOpen Y (natTensorPow L 1) (ψ.pow e.2 1) :=
  ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen 𝒜 hd ψ hWle hcover
    (ι_glued 𝒜 ψ hd hWle hcover) e

end Glue

end Stacks.AlgebraicGeometry.ProjChartCocycle

end
