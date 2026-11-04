module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGradedPieces
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic

/-!
# The chart sections of the comparison `θ` of Stacks Tag 01NK

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` homogeneous, `n ≥ 0`
and an open `V ⊆ T_{ψ(f)}`, this file constructs the map

`(A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`,

from the degree-`n` part of the localization `A_f` to the sections of `L ^⊗ n` over `V`. It is
additive, and semilinear over the degree-zero subring `A_{(f)}` along the dehomogenisation ring
map `Stacks.MorphismToProj.HomogeneousRatios.lift`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSectionOf`: the section `x / f ^ j` of
  `L ^⊗ n` over `V`, on a representative.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection` and
  `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSectionHom`: the map
  `(A_f)_n ⟶ Γ(L ^⊗ n, V)`, as a function and as an additive map.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSectionOf_mul_pow`: the cancellation
  `(f ^ m x) / f ^ (m + j) = x / f ^ j`.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSectionOf_eq_of_mk_eq`: the quotient
  depends only on the fraction.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_mk`: the value of the map on
  any representative of a fraction.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_add`: the map is additive.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_smul`: the map is semilinear
  over `A_{(f)}`, along the dehomogenisation ring map `A_{(f)} ⟶ Γ(V, 𝒪_T)`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading integerGrading_natCast
  mem_homogeneousSubmodule)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf resTop_eq_ratioOf_smul)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (powCongr_app_toFun)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections nonvanishingOpen_mulSections
  resTop_mulSections_smul_left)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.GradedLocalization (gradedPiece mem_gradedPiece_iff smul_mem_gradedPiece)
open Stacks.GradedSections (powCongr)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (divTop divOf_add divOf_smul divTop_mulSections_cancel)
open Stacks.TensorPowerTrivialize (resTop resTop_app)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedDivision

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Transport and linearity for the quotient across degrees -/

section Transport

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] {W : T.Opens}

/-- Two equal denominators of the same degree and two equal numerators give the same quotient
`Stacks.TensorPowerDivision.divTop`. -/
theorem divTop_congr_sections {k : ℕ} {t t' : Γ(natTensorPow L k, ⊤)} (htt : t = t')
    {n : ℕ} {a a' : Γ(natTensorPow L (k + n), ⊤)} (haa : a = a')
    (hW : W ≤ nonvanishingOpen T (natTensorPow L k) t)
    (hW' : W ≤ nonvanishingOpen T (natTensorPow L k) t') :
    divTop L t hW n a = divTop L t' hW' n a' := by
  subst htt haa; rfl

/-- The quotient `Stacks.TensorPowerDivision.divTop` is additive in the global numerator. -/
theorem divTop_add {k : ℕ} (t : Γ(natTensorPow L k, ⊤))
    (hW : W ≤ nonvanishingOpen T (natTensorPow L k) t) (n : ℕ)
    (a b : Γ(natTensorPow L (k + n), ⊤)) :
    divTop L t hW n (a + b) = divTop L t hW n a + divTop L t hW n b := by
  unfold divTop
  rw [show resTop (natTensorPow L (k + n)) (a + b) W
      = resTop (natTensorPow L (k + n)) a W + resTop (natTensorPow L (k + n)) b W by
        simp [resTop], divOf_add]

/-- If the restriction to `W` of the numerator `a` is `r` times that of `b`, then the quotient
of `a` by `t` is `r` times the quotient of `b` by `t`. -/
theorem divTop_smul_of_resTop_eq {k : ℕ} (t : Γ(natTensorPow L k, ⊤))
    (hW : W ≤ nonvanishingOpen T (natTensorPow L k) t) (n : ℕ)
    {a b : Γ(natTensorPow L (k + n), ⊤)} {r : Γ(T, W)}
    (h : resTop (natTensorPow L (k + n)) a W
      = r • resTop (natTensorPow L (k + n)) b W) :
    divTop L t hW n a = r • divTop L t hW n b := by
  unfold divTop
  rw [h, divOf_smul]

variable (ψ : GradedSections 𝒜 L)

/-- The quotient of two values of `ψ` depends only on the two elements of `A`, not on the
indices they are read at. -/
theorem divTop_toFun_congr {k k' : ℕ} {p p' : A} (hp : p ∈ 𝒜 k) (hp' : p' ∈ 𝒜 k') (n : ℕ)
    {q q' : A} (hq : q ∈ 𝒜 (k + n)) (hq' : q' ∈ 𝒜 (k' + n))
    (hW : W ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨p, hp⟩))
    (hW' : W ≤ nonvanishingOpen T (natTensorPow L k') (ψ.toFun k' ⟨p', hp'⟩))
    (hkk : k = k') (hpp : p = p') (hqq : q = q') :
    divTop L (ψ.toFun k ⟨p, hp⟩) hW n (ψ.toFun (k + n) ⟨q, hq⟩)
      = divTop L (ψ.toFun k' ⟨p', hp'⟩) hW' n (ψ.toFun (k' + n) ⟨q', hq'⟩) := by
  subst hkk hpp hqq; rfl

end Transport

/-! ### The section attached to a fraction `x / f ^ j` -/

section Chart

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- The section `ψ(x) / ψ(f ^ j)` of `L ^⊗ n` over `V`, for `x` homogeneous of degree
`j d + n`. -/
def chartSectionOf (n j : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n)) : Γ(natTensorPow L n, V) :=
  divTop L (ψ.toFun (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩)
    (ψ.le_nonvanishingOpen_pow hf hV j) n (ψ.toFun (j * d + n) ⟨x, hx⟩)

/-- The section depends only on the exponent of the denominator and on the numerator, the
membership being a proposition. -/
theorem chartSectionOf_congr (n : ℕ) {j j' : ℕ} {x x' : A}
    (hx : x ∈ 𝒜 (j * d + n)) (hx' : x' ∈ 𝒜 (j' * d + n)) (hj : j = j') (hxx : x = x') :
    chartSectionOf ψ hf hV n j hx = chartSectionOf ψ hf hV n j' hx' := by
  subst hj hxx; rfl

/-- The section `chartSectionOf` is additive in the numerator, at a fixed denominator. -/
theorem chartSectionOf_add (n j : ℕ) {x x' : A} (hx : x ∈ 𝒜 (j * d + n))
    (hx' : x' ∈ 𝒜 (j * d + n)) (hs : x + x' ∈ 𝒜 (j * d + n)) :
    chartSectionOf ψ hf hV n j hs
      = chartSectionOf ψ hf hV n j hx + chartSectionOf ψ hf hV n j hx' := by
  unfold chartSectionOf
  rw [show (ψ.toFun (j * d + n)) ⟨x + x', hs⟩
      = (ψ.toFun (j * d + n)) ⟨x, hx⟩ + (ψ.toFun (j * d + n)) ⟨x', hx'⟩ from
        (ψ.toFun (j * d + n)).map_add ⟨x, hx⟩ ⟨x', hx'⟩, divTop_add]

/-- A product of homogeneous elements of degrees `k d` and `j d + n` lies in degree `m d + n`
when `k + j = m`. -/
private theorem mul_mem_graded_add {p x : A} {k j n m : ℕ} (hp : p ∈ 𝒜 (k * d))
    (hx : x ∈ 𝒜 (j * d + n)) (h : k + j = m) : p * x ∈ 𝒜 (m * d + n) :=
  mem_graded_of_eq 𝒜 (by subst h; ring) (SetLike.mul_mem_graded hp hx)

/-- The section `chartSectionOf` of a product `p x`, with `p` of degree `i d`, is the quotient of
`ψ(p) ψ(x)` by `ψ(f ^ i) ψ(f ^ j)`. -/
private theorem chartSectionOf_mul_eq_divTop (n i j : ℕ) {p x : A} (hp : p ∈ 𝒜 (i * d))
    (hx : x ∈ 𝒜 (j * d + n)) (hpx : p * x ∈ 𝒜 ((i + j) * d + n)) :
    chartSectionOf ψ hf hV n (i + j) hpx
      = divTop L (mulSections L (ψ.toFun (i * d) ⟨f ^ i, HomogeneousRatios.pow_mem hf i⟩)
            (ψ.toFun (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩))
          ((le_inf (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.le_nonvanishingOpen_pow hf hV j)).trans_eq
            (nonvanishingOpen_mulSections L _ _).symm) n
          ((powCongr L (Nat.add_assoc (i * d) (j * d) n).symm).app ⊤
            (mulSections L (ψ.toFun (i * d) ⟨p, hp⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩))) := by
  have hfi : f ^ i ∈ 𝒜 (i * d) := HomogeneousRatios.pow_mem hf i
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hprod : f ^ i * f ^ j ∈ 𝒜 (i * d + j * d) := SetLike.mul_mem_graded hfi hfj
  have hpx1 : p * x ∈ 𝒜 (i * d + (j * d + n)) := SetLike.mul_mem_graded hp hx
  have hpx2 : p * x ∈ 𝒜 (i * d + j * d + n) :=
    mem_graded_of_eq 𝒜 (Nat.add_assoc (i * d) (j * d) n).symm hpx1
  have hmid : V ≤ nonvanishingOpen T (natTensorPow L (i * d + j * d))
      (ψ.toFun (i * d + j * d) ⟨f ^ i * f ^ j, hprod⟩) :=
    ψ.le_nonvanishingOpen_mul hfi hfj hprod (ψ.le_nonvanishingOpen_pow hf hV i)
      (ψ.le_nonvanishingOpen_pow hf hV j)
  have hmul : V ≤ nonvanishingOpen T (natTensorPow L (i * d + j * d))
      (mulSections L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩) (ψ.toFun (j * d) ⟨f ^ j, hfj⟩)) :=
    (le_inf (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.le_nonvanishingOpen_pow hf hV j)).trans_eq
      (nonvanishingOpen_mulSections L _ _).symm
  have hnum : (powCongr L (Nat.add_assoc (i * d) (j * d) n).symm).app ⊤
      (mulSections L (ψ.toFun (i * d) ⟨p, hp⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩))
      = ψ.toFun (i * d + j * d + n) ⟨p * x, hpx2⟩ := by
    rw [← ψ.map_mul (i * d) (j * d + n) ⟨p, hp⟩ ⟨x, hx⟩ ⟨p * x, hpx1⟩ rfl]
    exact powCongr_app_toFun 𝒜 ψ (Nat.add_assoc (i * d) (j * d) n).symm (p * x) hpx1 hpx2
  unfold chartSectionOf
  rw [(divTop_toFun_congr ψ hprod (HomogeneousRatios.pow_mem hf (i + j)) n hpx2 hpx hmid
      (ψ.le_nonvanishingOpen_pow hf hV (i + j)) (Nat.add_mul i j d).symm (pow_add f i j).symm
      rfl).symm,
    divTop_congr_sections
      (ψ.map_mul (i * d) (j * d) ⟨f ^ i, hfi⟩ ⟨f ^ j, hfj⟩ ⟨f ^ i * f ^ j, hprod⟩ rfl)
      hnum.symm hmid hmul]

/-- The cancellation `(f ^ m x) / f ^ (m + j) = x / f ^ j`. -/
theorem chartSectionOf_mul_pow (n j m : ℕ) {x : A} (hx : x ∈ 𝒜 (j * d + n))
    (hmx : f ^ m * x ∈ 𝒜 ((m + j) * d + n)) :
    chartSectionOf ψ hf hV n (m + j) hmx = chartSectionOf ψ hf hV n j hx := by
  rw [chartSectionOf_mul_eq_divTop ψ hf hV n m j (HomogeneousRatios.pow_mem hf m) hx hmx]
  unfold chartSectionOf
  rw [divTop_mulSections_cancel]
  exact ψ.le_nonvanishingOpen_pow hf hV m

/-- The section `chartSectionOf` depends only on the fraction `x / f ^ j` of `A_f`, not on the
representative. -/
theorem chartSectionOf_eq_of_mk_eq (n : ℕ) {j j' : ℕ} {x x' : A}
    (hx : x ∈ 𝒜 (j * d + n)) (hx' : x' ∈ 𝒜 (j' * d + n))
    (h : LocalizedModule.mk (M := A) x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)
      = LocalizedModule.mk (M := A) x' (⟨f ^ j', ⟨j', rfl⟩⟩ : Submonoid.powers f)) :
    chartSectionOf ψ hf hV n j hx = chartSectionOf ψ hf hV n j' hx' := by
  obtain ⟨⟨_, c, rfl⟩, hu⟩ := LocalizedModule.mk_eq.1 h
  simp only [Submonoid.smul_def, smul_eq_mul] at hu
  have key : f ^ (c + j') * x = f ^ (c + j) * x' := by
    rwa [pow_add, pow_add, mul_assoc, mul_assoc]
  have h1 : f ^ (c + j') * x ∈ 𝒜 ((c + j' + j) * d + n) :=
    mul_mem_graded_add (HomogeneousRatios.pow_mem hf (c + j')) hx rfl
  have h2 : f ^ (c + j) * x' ∈ 𝒜 ((c + j + j') * d + n) :=
    mul_mem_graded_add (HomogeneousRatios.pow_mem hf (c + j)) hx' rfl
  rw [← chartSectionOf_mul_pow ψ hf hV n j (c + j') hx h1,
    ← chartSectionOf_mul_pow ψ hf hV n j' (c + j) hx' h2]
  exact chartSectionOf_congr ψ hf hV n h1 h2 (by lia) key

/-- For `p` homogeneous of degree `i d`, the quotient of `p x` by `f ^ (i + j)` is the ratio
`ψ(p) / ψ(f ^ i)`, a section of `𝒪_T` over `V`, times the quotient of `x` by `f ^ j`. -/
theorem chartSectionOf_mul_homogeneous (n j i : ℕ) {p x : A} (hp : p ∈ 𝒜 (i * d))
    (hx : x ∈ 𝒜 (j * d + n)) (hpx : p * x ∈ 𝒜 ((i + j) * d + n)) :
    chartSectionOf ψ hf hV n (i + j) hpx
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, HomogeneousRatios.pow_mem hf i⟩)
            (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.toFun (i * d) ⟨p, hp⟩)
          • chartSectionOf ψ hf hV n j hx := by
  have hfi : f ^ i ∈ 𝒜 (i * d) := HomogeneousRatios.pow_mem hf i
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hfi : f ^ i ∈ 𝒜 (i * d) := HomogeneousRatios.pow_mem hf i
  have hres : resTop (natTensorPow L (i * d + (j * d + n)))
        (mulSections L (ψ.toFun (i * d) ⟨p, hp⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩)) V
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩) (ψ.le_nonvanishingOpen_pow hf hV i)
            (ψ.toFun (i * d) ⟨p, hp⟩)
          • resTop (natTensorPow L (i * d + (j * d + n)))
              (mulSections L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩)) V :=
    resTop_mulSections_smul_left L (ψ.toFun (j * d + n) ⟨x, hx⟩)
      (resTop_eq_ratioOf_smul L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩)
        (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.toFun (i * d) ⟨p, hp⟩))
  have hres' : resTop (natTensorPow L (i * d + j * d + n))
        ((powCongr L (Nat.add_assoc (i * d) (j * d) n).symm).app ⊤
          (mulSections L (ψ.toFun (i * d) ⟨p, hp⟩) (ψ.toFun (j * d + n) ⟨x, hx⟩))) V
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩) (ψ.le_nonvanishingOpen_pow hf hV i)
            (ψ.toFun (i * d) ⟨p, hp⟩)
          • resTop (natTensorPow L (i * d + j * d + n))
              ((powCongr L (Nat.add_assoc (i * d) (j * d) n).symm).app ⊤
                (mulSections L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩)
                  (ψ.toFun (j * d + n) ⟨x, hx⟩))) V := by
    rw [resTop_app, resTop_app, hres, Scheme.Modules.Hom.app_smul]
  rw [chartSectionOf_mul_eq_divTop ψ hf hV n i j hp hx hpx]
  unfold chartSectionOf
  rw [divTop_smul_of_resTop_eq _ _ n hres', divTop_mulSections_cancel]
  exact ψ.le_nonvanishingOpen_pow hf hV i

end Chart

/-! ### The map out of the degree-`n` part of `A_f` -/

section Piece

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- The graded ring `𝒜` acts on its integer-extended grading
`AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading 𝒜`. -/
instance gradedSMulIntegerGrading : SetLike.GradedSMul 𝒜 (integerGrading (S := A) 𝒜) :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading_zero (S := A) 𝒜 ▸
    AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGradingGradedSMul (S := A) 𝒜 0

omit [GradedRing 𝒜] in
/-- An element of `A` lies in the integer grading at `n + j d` if and only if it lies in
`𝒜 (j d + n)`. -/
theorem mem_integerGrading_iff {n j : ℕ} (x : A) :
    x ∈ integerGrading (S := A) 𝒜 ((n : ℤ) + j • (d : ℤ)) ↔ x ∈ 𝒜 (j * d + n) := by
  rw [show ((n : ℤ) + j • (d : ℤ)) = ((j * d + n : ℕ) : ℤ) by push_cast; ring,
    integerGrading_natCast, mem_homogeneousSubmodule]

/-- Every element of the degree-`n` part of `A_f` is a fraction `x / f ^ j` with `x`
homogeneous of degree `j d + n`. -/
theorem exists_rep (n : ℕ) (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (hf' : f ∈ 𝒜 d) :
    ∃ (j : ℕ) (x : A) (_ : x ∈ 𝒜 (j * d + n)),
      (y : LocalizedModule.Away f A)
        = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) := by
  obtain ⟨j₀, x₀, hx₀, hy₀⟩ := (mem_gradedPiece_iff 𝒜 _ hf' (n : ℤ) _).1 y.2
  exact ⟨j₀, x₀, (mem_integerGrading_iff (𝒜 := 𝒜) (d := d) x₀).1 hx₀, hy₀⟩

/-- There is a section of `L ^⊗ n` over `V` that every representative of a given element of the
degree-`n` part of `A_f` computes by `chartSectionOf`. -/
theorem exists_chartSection (n : ℕ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    ∃ s : Γ(natTensorPow L n, V), ∀ (j : ℕ) (x : A) (hx : x ∈ 𝒜 (j * d + n)),
      (y : LocalizedModule.Away f A)
          = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) →
        s = chartSectionOf ψ hf hV n j hx := by
  obtain ⟨j₀, x₀, hx₀, hy₀⟩ := exists_rep n y hf
  exact ⟨chartSectionOf ψ hf hV n j₀ hx₀,
    fun j x hx hrep => chartSectionOf_eq_of_mk_eq ψ hf hV n hx₀ hx (hy₀.symm.trans hrep)⟩

/-- The map `(A_f)_n ⟶ Γ(L ^⊗ n, V)` sending the fraction `x / f ^ j` of `A_f`-degree `n` to the
quotient `ψ(x) / ψ(f ^ j)`, a section of `L ^⊗ n` over an open `V` on which `ψ(f)` does not
vanish. -/
def chartSection (n : ℕ) (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    Γ(natTensorPow L n, V) :=
  Classical.choose (exists_chartSection ψ hf hV n y)

/-- The value of `chartSection` on a fraction `x / f ^ j` is `chartSectionOf` of `x` and `j`. -/
theorem chartSection_mk (n : ℕ) (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ))
    (j : ℕ) (x : A) (hx : x ∈ 𝒜 (j * d + n))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)) :
    chartSection ψ hf hV n y = chartSectionOf ψ hf hV n j hx :=
  Classical.choose_spec (exists_chartSection ψ hf hV n y) j x hx hrep

/-- The map `chartSection` is additive. -/
theorem chartSection_add (n : ℕ)
    (y z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    chartSection ψ hf hV n (y + z)
      = chartSection ψ hf hV n y + chartSection ψ hf hV n z := by
  obtain ⟨j, x, hx, hy⟩ := exists_rep n y hf
  obtain ⟨i, w, hw, hz⟩ := exists_rep n z hf
  have hxw : f ^ i * x ∈ 𝒜 ((j + i) * d + n) :=
    mul_mem_graded_add (HomogeneousRatios.pow_mem hf i) hx (Nat.add_comm i j)
  have hwx : f ^ j * w ∈ 𝒜 ((j + i) * d + n) :=
    mul_mem_graded_add (HomogeneousRatios.pow_mem hf j) hw rfl
  have hsum : f ^ i * x + f ^ j * w ∈ 𝒜 ((j + i) * d + n) := add_mem hxw hwx
  have hden : (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) * (⟨f ^ i, ⟨i, rfl⟩⟩ : Submonoid.powers f)
      = (⟨f ^ (j + i), ⟨j + i, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext (by simp [pow_add])
  have hrep : ((y + z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
        LocalizedModule.Away f A)
      = LocalizedModule.mk (f ^ i * x + f ^ j * w)
          (⟨f ^ (j + i), ⟨j + i, rfl⟩⟩ : Submonoid.powers f) := by
    rw [AddSubgroup.coe_add, hy, hz, LocalizedModule.mk_add_mk, hden]
    simp [Submonoid.smul_def, smul_eq_mul]
  have hij : f ^ i * x ∈ 𝒜 ((i + j) * d + n) :=
    mul_mem_graded_add (HomogeneousRatios.pow_mem hf i) hx rfl
  have e1 : chartSectionOf ψ hf hV n (j + i) hxw = chartSectionOf ψ hf hV n j hx :=
    (chartSectionOf_congr ψ hf hV n hxw hij (by lia) rfl).trans
      (chartSectionOf_mul_pow ψ hf hV n j i hx hij)
  have e2 : chartSectionOf ψ hf hV n (j + i) hwx = chartSectionOf ψ hf hV n i hw :=
    chartSectionOf_mul_pow ψ hf hV n i j hw hwx
  rw [chartSection_mk ψ hf hV n _ (j + i) _ hsum hrep,
    chartSection_mk ψ hf hV n y j x hx hy, chartSection_mk ψ hf hV n z i w hw hz,
    chartSectionOf_add ψ hf hV n (j + i) hxw hwx hsum, e1, e2]

/-- The map `(A_f)_n ⟶ Γ(L ^⊗ n, V)` of `chartSection`, as an additive map. -/
def chartSectionHom (n : ℕ) :
    gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ) →+ Γ(natTensorPow L n, V) :=
  AddMonoidHom.mk' (chartSection ψ hf hV n) (chartSection_add ψ hf hV n)

/-- `chartSectionHom` applied to `y` is `chartSection` of `y`. -/
@[simp] theorem chartSectionHom_apply (n : ℕ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    chartSectionHom ψ hf hV n y = chartSection ψ hf hV n y := rfl

/-- The map `chartSection` is semilinear over the degree-zero subring `A_{(f)}`, along the
dehomogenisation ring map `A_{(f)} ⟶ Γ(V, 𝒪_T)`. -/
theorem chartSection_smul (hd : 0 < d) (n : ℕ) (a : HomogeneousLocalization.Away 𝒜 f)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n : ℤ)) :
    chartSection ψ hf hV n ⟨HomogeneousLocalization.val a • (y : LocalizedModule.Away f A),
        smul_mem_gradedPiece 𝒜 _ hf (n : ℤ) a y.2⟩
      = (ψ.homogeneousRatios hf hV).lift hd a • chartSection ψ hf hV n y := by
  obtain ⟨i, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf a
  obtain ⟨j, x, hx, hy⟩ := exists_rep n y hf
  have hp' : p ∈ 𝒜 (i * d) := mem_graded_of_eq 𝒜 (smul_eq_mul i d) hp
  have hpx : p * x ∈ 𝒜 ((i + j) * d + n) :=
    mul_mem_graded_add hp' hx rfl
  have hden : (⟨f ^ i, ⟨i, rfl⟩⟩ : Submonoid.powers f) * (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)
      = (⟨f ^ (i + j), ⟨i + j, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext (by simp [pow_add])
  have hrep : HomogeneousLocalization.val (HomogeneousLocalization.Away.mk 𝒜 hf i p hp)
        • (y : LocalizedModule.Away f A)
      = LocalizedModule.mk (p * x) (⟨f ^ (i + j), ⟨i + j, rfl⟩⟩ : Submonoid.powers f) := by
    rw [HomogeneousLocalization.Away.val_mk, hy, LocalizedModule.mk_smul_mk, hden]
    simp [smul_eq_mul]
  rw [chartSection_mk ψ hf hV n _ (i + j) _ hpx hrep,
    chartSection_mk ψ hf hV n y j x hx hy,
    chartSectionOf_mul_homogeneous ψ hf hV n j i hp' hx hpx,
    ψ.lift_mk hf hV hd i p hp ⟨p, hp'⟩ rfl]

end Piece

end Stacks.AlgebraicGeometry.ProjChartGradedDivision

end
