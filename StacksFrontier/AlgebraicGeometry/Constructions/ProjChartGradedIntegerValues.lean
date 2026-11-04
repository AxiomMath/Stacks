module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedDivision
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.IntegerLaurent

/-!
# The chart sections of `θ` in an arbitrary integer degree

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map, given as
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` homogeneous and `V`
an open on which `ψ(f)` does not vanish, this file constructs, for every `n : ℤ`, the map

`(A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`

of the comparison `θ` of [Stacks, Tag 01NK], with values in the tensor powers
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` of [Stacks, Tag 01CU].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intValue`: the value `ψ(p)` read as a global
  section of `L ^⊗ k` in the family of [Stacks, Tag 01CU].
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf`: the section
  `ψ(x) / ψ(f ^ j)` of `L ^⊗ n` over `V`, on a representative, for `n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` and
  `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionHom`: the map
  `(A_f)_n ⟶ Γ(L ^⊗ n, V)`, as a function and as an additive map.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.nonvanishingOpen_intValue`: `intValue` does
  not change the nonvanishing open.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intMulSections_intValue`: `intValue` is
  multiplicative for `Stacks.TensorPowerDivision.intMulSections`.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf_mul_pow`: the cancellation
  `(f ^ m x) / f ^ (m + j) = x / f ^ j`.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf_eq_of_mk_eq`: the quotient
  depends only on the fraction.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.exists_int_rep`: for `0 < d`, every element of
  `(A_f)_n` is a fraction with numerator in a nonnegative degree.
* `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_mk` and
  `Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_add`: the value of the map on
  any representative, and its additivity.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading integerGrading_natCast
  mem_homogeneousSubmodule)
open Stacks.GradedLocalization (gradedPiece mem_gradedPiece_iff)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare hStruct mulBilinear_mulSections)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (intMulSections intMulSections_eq_mulBilinear)
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

section Values

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-- The value `ψ(p)`, read as a global section of the `k`-th tensor power
`Stacks.AmpleProjectiveImmersion.tensorPowerModule T L k` through the comparison
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`. -/
def intValue (k : ℕ) (p : 𝒜 k) : Γ(tensorPowerModule T L (k : ℤ), ⊤) :=
  (powCompare L k).hom.app ⊤ (ψ.toFun k p)

/-- The nonvanishing open of `intValue ψ k p` is that of `ψ(p)`. -/
theorem nonvanishingOpen_intValue (k : ℕ) (p : 𝒜 k) :
    nonvanishingOpen T (tensorPowerModule T L (k : ℤ)) (intValue ψ k p)
      = nonvanishingOpen T (natTensorPow L k) (ψ.toFun k p) :=
  TopologicalSpace.Opens.ext (Stacks.Ample.nonvanishingLocus_congr (powCompare L k) (ψ.toFun k p))

/-- Two equal indices and two equal elements give the same value of `intValue`, up to the
reindexing of the tensor powers. -/
theorem intValue_reindex {k k' : ℕ} {p p' : A} (hp : p ∈ 𝒜 k) (hp' : p' ∈ 𝒜 k')
    (hkk : k = k') (hpp : p = p') :
    (Stacks.TensorPowerDivision.intPowReindex L
          (show ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) from by rw [hkk])).hom.app ⊤
        (intValue ψ k ⟨p, hp⟩)
      = intValue ψ k' ⟨p', hp'⟩ := by
  subst hkk; subst hpp; rfl

/-- `intValue` is multiplicative for `Stacks.TensorPowerDivision.intMulSections`: the product of
the values of `ψ` on two homogeneous elements is its value on their product. -/
theorem intMulSections_intValue (k m : ℕ) (a : 𝒜 k) (b : 𝒜 m) (ab : 𝒜 (k + m))
    (hab : (ab : A) = (a : A) * (b : A)) :
    intMulSections L (intValue ψ k a) (intValue ψ m b) = intValue ψ (k + m) ab :=
  (intMulSections_eq_mulBilinear L (intValue ψ k a) (intValue ψ m b)).trans
    ((mulBilinear_mulSections L k m (ψ.toFun k a) (ψ.toFun m b)).trans
      (congrArg (fun z => (powCompare L (k + m)).hom.app ⊤ z)
        (ψ.map_mul k m a b ab hab).symm))

variable {V : T.Opens}

/-- If `ψ(p)` does not vanish on `V`, then neither does `intValue ψ k p`. -/
theorem le_nonvanishingOpen_intValue {k : ℕ} {p : A} (hp : p ∈ 𝒜 k)
    (hV : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨p, hp⟩)) :
    V ≤ nonvanishingOpen T (tensorPowerModule T L (k : ℤ)) (intValue ψ k ⟨p, hp⟩) :=
  hV.trans (nonvanishingOpen_intValue ψ k ⟨p, hp⟩).ge

/-- If `ψ(f)` does not vanish on `V`, then neither does `intValue ψ (j * d) (f ^ j)`. -/
theorem le_nonvanishingOpen_intValue_pow {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩)) (j : ℕ) :
    V ≤ nonvanishingOpen T (tensorPowerModule T L ((j * d : ℕ) : ℤ))
      (intValue ψ (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩) :=
  le_nonvanishingOpen_intValue ψ _ (ψ.le_nonvanishingOpen_pow hf hV j)

/-- If `ψ(p)` and `ψ(q)` do not vanish on `V`, then neither does the product
`Stacks.TensorPowerDivision.intMulSections` of `intValue ψ k p` and `intValue ψ m q`. -/
theorem le_nonvanishingOpen_intMulSections {k m : ℕ} {p q : A} (hp : p ∈ 𝒜 k) (hq : q ∈ 𝒜 m)
    (hpq : p * q ∈ 𝒜 (k + m))
    (hVp : V ≤ nonvanishingOpen T (natTensorPow L k) (ψ.toFun k ⟨p, hp⟩))
    (hVq : V ≤ nonvanishingOpen T (natTensorPow L m) (ψ.toFun m ⟨q, hq⟩)) :
    V ≤ nonvanishingOpen T (tensorPowerModule T L ((k : ℤ) + (m : ℤ)))
      (intMulSections L (intValue ψ k ⟨p, hp⟩) (intValue ψ m ⟨q, hq⟩)) :=
  (le_nonvanishingOpen_intValue ψ hpq
        (ψ.le_nonvanishingOpen_mul hp hq hpq hVp hVq)).trans
    (congrArg (fun z => nonvanishingOpen T (tensorPowerModule T L ((k : ℤ) + (m : ℤ))) z)
      (intMulSections_intValue ψ k m ⟨p, hp⟩ ⟨q, hq⟩ ⟨p * q, hpq⟩ rfl)).ge

end Values

/-! ### The section attached to a fraction `x / f ^ j` in an arbitrary integer degree -/

section IntChart

open Stacks.TensorPowerDivision (intDivTop intDivOf_eq_of_mul_eq intPowReindex
  intPowReindex_trans intMulSections_intPowReindex intDivTop_intMulSections_cancel)

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- The section `ψ(x) / ψ(f ^ j)` of `L ^⊗ n` over `V`, for `n : ℤ` and `x` homogeneous of
degree `e` with `j d + n = e`. -/
def intChartSectionOf (n : ℤ) (j e : ℕ) (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    {x : A} (hx : x ∈ 𝒜 e) : Γ(tensorPowerModule T L n, V) :=
  intDivTop L (intValue ψ (j * d) ⟨f ^ j, HomogeneousRatios.pow_mem hf j⟩)
    (le_nonvanishingOpen_intValue_pow ψ hf hV j) n
    ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩))

/-- The quotient `intValue ψ q / intValue ψ p` depends only on the index of the denominator and on
the elements `p` and `q`. -/
theorem intDivTop_intValue_congr (n : ℤ) {k k' e e' : ℕ} {p p' q q' : A}
    (hp : p ∈ 𝒜 k) (hp' : p' ∈ 𝒜 k') (hq : q ∈ 𝒜 e) (hq' : q' ∈ 𝒜 e')
    (he : ((k : ℕ) : ℤ) + n = (e : ℕ)) (he' : ((k' : ℕ) : ℤ) + n = (e' : ℕ))
    (hVk : V ≤ nonvanishingOpen T (tensorPowerModule T L ((k : ℕ) : ℤ))
      (intValue ψ k ⟨p, hp⟩))
    (hVk' : V ≤ nonvanishingOpen T (tensorPowerModule T L ((k' : ℕ) : ℤ))
      (intValue ψ k' ⟨p', hp'⟩))
    (hkk : k = k') (hpp : p = p') (hqq : q = q') :
    intDivTop L (intValue ψ k ⟨p, hp⟩) hVk n
        ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨q, hq⟩))
      = intDivTop L (intValue ψ k' ⟨p', hp'⟩) hVk' n
          ((intPowReindex L he'.symm).hom.app ⊤ (intValue ψ e' ⟨q', hq'⟩)) := by
  subst hkk; subst hpp; subst hqq
  obtain rfl : e = e' := Nat.cast_injective (he.symm.trans he')
  rfl

/-- The quotient `Stacks.TensorPowerDivision.intDivTop` depends only on the denominator and the
numerator as sections. -/
theorem intDivTop_congr_sections {k : ℤ} {t t' : Γ(tensorPowerModule T L k, ⊤)} (htt : t = t')
    (n : ℤ) {a a' : Γ(tensorPowerModule T L (k + n), ⊤)} (haa : a = a')
    (hVt : V ≤ nonvanishingOpen T (tensorPowerModule T L k) t)
    (hVt' : V ≤ nonvanishingOpen T (tensorPowerModule T L k) t') :
    intDivTop L t hVt n a = intDivTop L t' hVt' n a' := by
  subst htt; subst haa; rfl

/-- Multiplying a numerator by `f ^ m` shifts the exponent of the denominator by `m`. -/
private theorem cast_add_mul_add_eq {n : ℤ} {j e : ℕ} (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    (m : ℕ) : (((m + j) * d : ℕ) : ℤ) + n = ((m * d + e : ℕ) : ℤ) := by
  rw [Nat.cast_add, ← he]; push_cast; ring

/-- Multiplying a homogeneous element by a power of `f` adds the degrees. -/
private theorem pow_mul_mem_graded {k : ℕ} {g : A} (hg : g ∈ 𝒜 k) (m : ℕ) {e : ℕ} {x : A}
    (hx : x ∈ 𝒜 e) : g ^ m * x ∈ 𝒜 (m * k + e) :=
  SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hg m) hx

/-- The numerator's index is determined by the exponent of the denominator and the degree. -/
theorem numerator_index_eq {n : ℤ} {j e : ℕ} (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    {m e' : ℕ} (he' : (((m + j) * d : ℕ) : ℤ) + n = (e' : ℕ)) : e' = m * d + e :=
  Nat.cast_injective (he'.symm.trans (cast_add_mul_add_eq he m))

/-- `intChartSectionOf` depends only on the exponent of the denominator and on the numerator. -/
theorem intChartSectionOf_congr (n : ℤ) {j j' e e' : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he' : ((j' * d : ℕ) : ℤ) + n = (e' : ℕ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e') (hj : j = j') (hxx : x = x') :
    intChartSectionOf ψ hf hV n j e he hx = intChartSectionOf ψ hf hV n j' e' he' hx' := by
  subst hj
  obtain rfl : e = e' := Nat.cast_injective (he.symm.trans he')
  subst hxx
  rfl

/-- The cancellation `(f ^ m x) / f ^ (m + j) = x / f ^ j` for `intChartSectionOf`. -/
theorem intChartSectionOf_mul_pow (n : ℤ) (j m e e' : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    (he' : (((m + j) * d : ℕ) : ℤ) + n = (e' : ℕ))
    {x : A} (hx : x ∈ 𝒜 e) (hmx : f ^ m * x ∈ 𝒜 e') :
    intChartSectionOf ψ hf hV n (m + j) e' he' hmx
      = intChartSectionOf ψ hf hV n j e he hx := by
  obtain rfl : e' = m * d + e := numerator_index_eq he he'
  have hfm : f ^ m ∈ 𝒜 (m * d) := HomogeneousRatios.pow_mem hf m
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hprod : f ^ m * f ^ j ∈ 𝒜 (m * d + j * d) := pow_mul_mem_graded hf m hfj
  have hmid : ((m * d + j * d : ℕ) : ℤ) + n = ((m * d + e : ℕ) : ℤ) :=
    (congrArg (fun k : ℕ => (k : ℤ) + n) (Nat.add_mul m j d).symm).trans
      (cast_add_mul_add_eq he m)
  have hVm := ψ.le_nonvanishingOpen_pow hf hV m
  have hVj := ψ.le_nonvanishingOpen_pow hf hV j
  have hVmid : V ≤ nonvanishingOpen T (tensorPowerModule T L ((m * d + j * d : ℕ) : ℤ))
      (intValue ψ (m * d + j * d) ⟨f ^ m * f ^ j, hprod⟩) :=
    le_nonvanishingOpen_intValue ψ hprod
      (ψ.le_nonvanishingOpen_mul hfm hfj hprod hVm hVj)
  have hVprod : V ≤ nonvanishingOpen T
        (tensorPowerModule T L (((m * d : ℕ) : ℤ) + ((j * d : ℕ) : ℤ)))
      (intMulSections L (intValue ψ (m * d) ⟨f ^ m, hfm⟩)
        (intValue ψ (j * d) ⟨f ^ j, hfj⟩)) :=
    le_nonvanishingOpen_intMulSections ψ hfm hfj hprod hVm hVj
  have hnum : (intPowReindex L hmid.symm).hom.app ⊤
        (intValue ψ (m * d + e) ⟨f ^ m * x, hmx⟩)
      = (intPowReindex L
            (Int.add_assoc ((m * d : ℕ) : ℤ) ((j * d : ℕ) : ℤ) n).symm).hom.app ⊤
          (intMulSections L (intValue ψ (m * d) ⟨f ^ m, hfm⟩)
            ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩))) := by
    rw [intMulSections_intPowReindex, intPowReindex_trans,
      intMulSections_intValue ψ (m * d) e ⟨f ^ m, hfm⟩ ⟨x, hx⟩ ⟨f ^ m * x, hmx⟩ rfl]
  calc intChartSectionOf ψ hf hV n (m + j) (m * d + e) he' hmx
      = intDivTop L (intValue ψ (m * d + j * d) ⟨f ^ m * f ^ j, hprod⟩) hVmid n
          ((intPowReindex L hmid.symm).hom.app ⊤
            (intValue ψ (m * d + e) ⟨f ^ m * x, hmx⟩)) :=
        intDivTop_intValue_congr ψ n (HomogeneousRatios.pow_mem hf (m + j)) hprod hmx hmx
          he' hmid _ hVmid (Nat.add_mul m j d) (pow_add f m j) rfl
    _ = intDivTop L (intMulSections L (intValue ψ (m * d) ⟨f ^ m, hfm⟩)
            (intValue ψ (j * d) ⟨f ^ j, hfj⟩)) hVprod n
          ((intPowReindex L
                (Int.add_assoc ((m * d : ℕ) : ℤ) ((j * d : ℕ) : ℤ) n).symm).hom.app ⊤
            (intMulSections L (intValue ψ (m * d) ⟨f ^ m, hfm⟩)
              ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩)))) :=
        intDivTop_congr_sections
          (intMulSections_intValue ψ (m * d) (j * d) ⟨f ^ m, hfm⟩ ⟨f ^ j, hfj⟩
            ⟨f ^ m * f ^ j, hprod⟩ rfl).symm n hnum hVmid hVprod
    _ = intChartSectionOf ψ hf hV n j e he hx :=
        intDivTop_intMulSections_cancel L (intValue ψ (j * d) ⟨f ^ j, hfj⟩)
          (le_nonvanishingOpen_intValue_pow ψ hf hV j)
          (intValue ψ (m * d) ⟨f ^ m, hfm⟩) hVprod n _


/-- `intChartSectionOf` depends only on the fraction `x / f ^ j` of `A_f`, not on the
representative. -/
theorem intChartSectionOf_eq_of_mk_eq (n : ℤ) {j j' e e' : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he' : ((j' * d : ℕ) : ℤ) + n = (e' : ℕ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e')
    (h : LocalizedModule.mk (M := A) x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)
      = LocalizedModule.mk (M := A) x' (⟨f ^ j', ⟨j', rfl⟩⟩ : Submonoid.powers f)) :
    intChartSectionOf ψ hf hV n j e he hx = intChartSectionOf ψ hf hV n j' e' he' hx' := by
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h
  obtain ⟨c, hc⟩ := u.2
  simp only [Submonoid.smul_def, smul_eq_mul] at hu
  rw [← hc] at hu
  have key : f ^ (c + j') * x = f ^ (c + j) * x' := by
    rwa [pow_add, pow_add, mul_assoc, mul_assoc]
  have h1 := pow_mul_mem_graded hf (c + j') hx
  have h2 := pow_mul_mem_graded hf (c + j) hx'
  have h1' := cast_add_mul_add_eq he (c + j')
  have h2' := cast_add_mul_add_eq he' (c + j)
  rw [← intChartSectionOf_mul_pow ψ hf hV n j (c + j') e _ he h1' hx h1,
    ← intChartSectionOf_mul_pow ψ hf hV n j' (c + j) e' _ he' h2' hx' h2]
  exact intChartSectionOf_congr ψ hf hV n h1' h2' h1 h2 (by omega) key


/-! ### The map out of the degree-`n` part of `A_f`, for an arbitrary integer `n` -/

omit [GradedRing 𝒜] in
/-- A homogeneous element of a nonnegative integer degree is homogeneous of that degree as a
natural number. -/
theorem mem_graded_toNat {k : ℤ} (hk : 0 ≤ k) {x : A}
    (hx : x ∈ integerGrading (S := A) 𝒜 k) : x ∈ 𝒜 k.toNat := by
  rwa [← Int.toNat_of_nonneg hk, integerGrading_natCast, mem_homogeneousSubmodule] at hx

include hf in
/-- If `0 < d`, every element of the degree-`n` part of `A_f`, for any `n : ℤ`, is a fraction
`x / f ^ j` with `x` homogeneous of a nonnegative degree. -/
theorem exists_int_rep (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    ∃ (j e : ℕ) (_ : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (x : A) (_ : x ∈ 𝒜 e),
      (y : LocalizedModule.Away f A)
        = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) := by
  obtain ⟨j₀, x₀, hx₀, hy₀⟩ := (mem_gradedPiece_iff 𝒜 _ hf n _).1 y.2
  rcases le_or_gt 0 (n + j₀ • (d : ℤ)) with hk | hk
  · refine ⟨j₀, (n + j₀ • (d : ℤ)).toNat, ?_, x₀, mem_graded_toNat hk hx₀, hy₀⟩
    rw [Int.toNat_of_nonneg hk]
    push_cast
    ring
  · have hx0 : x₀ = 0 := by
      rwa [AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_neg _ _ hk,
        Submodule.mem_bot] at hx₀
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have ht : (0 : ℤ) ≤ (((-n).toNat : ℕ) : ℤ) := Int.ofNat_nonneg _
    have hn : -n ≤ (((-n).toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have hmul : (((-n).toNat : ℕ) : ℤ) * 1 ≤ (((-n).toNat : ℕ) : ℤ) * (d : ℤ) :=
      mul_le_mul_of_nonneg_left hd1 ht
    have hj : 0 ≤ (((-n).toNat * d : ℕ) : ℤ) + n := by push_cast; linarith
    refine ⟨(-n).toNat, ((((-n).toNat * d : ℕ) : ℤ) + n).toNat,
      (Int.toNat_of_nonneg hj).symm, 0, zero_mem _, ?_⟩
    rw [hy₀, hx0]
    simp

/-- There is a section of `L ^⊗ n` over `V` that `intChartSectionOf` computes on every
representative of a given element of the degree-`n` part of `A_f`. -/
theorem exists_intChartSection (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    ∃ s : Γ(tensorPowerModule T L n, V), ∀ (j e : ℕ)
      (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (x : A) (hx : x ∈ 𝒜 e),
        (y : LocalizedModule.Away f A)
            = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) →
          s = intChartSectionOf ψ hf hV n j e he hx := by
  obtain ⟨j₀, e₀, he₀, x₀, hx₀, hy₀⟩ := exists_int_rep hf hd n y
  exact ⟨intChartSectionOf ψ hf hV n j₀ e₀ he₀ hx₀,
    fun j e he x hx hrep =>
      intChartSectionOf_eq_of_mk_eq ψ hf hV n he₀ he hx₀ hx (hy₀.symm.trans hrep)⟩

/-- The map `(A_f)_n ⟶ Γ(L ^⊗ n, V)`, for `n : ℤ`, sending the fraction `x / f ^ j` of
`A_f`-degree `n` to the quotient `ψ(x) / ψ(f ^ j)`. -/
def intChartSection (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) : Γ(tensorPowerModule T L n, V) :=
  Classical.choose (exists_intChartSection ψ hf hV hd n y)

/-- The value of `intChartSection` on a fraction `x / f ^ j` is `intChartSectionOf` at that
representative. -/
theorem intChartSection_mk (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) (j e : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (x : A) (hx : x ∈ 𝒜 e)
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)) :
    intChartSection ψ hf hV hd n y = intChartSectionOf ψ hf hV n j e he hx :=
  Classical.choose_spec (exists_intChartSection ψ hf hV hd n y) j e he x hx hrep


/-! ### Additivity -/

/-- The quotient `Stacks.TensorPowerDivision.intDivTop` is additive in the numerator. -/
theorem intDivTop_add {k : ℤ} (t : Γ(tensorPowerModule T L k, ⊤))
    (hVt : V ≤ nonvanishingOpen T (tensorPowerModule T L k) t) (n : ℤ)
    (a a' : Γ(tensorPowerModule T L (k + n), ⊤)) :
    intDivTop L t hVt n (a + a') = intDivTop L t hVt n a + intDivTop L t hVt n a' := by
  unfold Stacks.TensorPowerDivision.intDivTop
  rw [show resTop (tensorPowerModule T L (k + n)) (a + a') V
      = resTop (tensorPowerModule T L (k + n)) a V
        + resTop (tensorPowerModule T L (k + n)) a' V by simp [resTop],
    Stacks.TensorPowerDivision.intDivOf_add]

/-- `intValue` is additive. -/
theorem intValue_add (e : ℕ) {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e)
    (hs : x + x' ∈ 𝒜 e) :
    intValue ψ e ⟨x + x', hs⟩ = intValue ψ e ⟨x, hx⟩ + intValue ψ e ⟨x', hx'⟩ :=
  (congrArg ((powCompare L e).hom.app ⊤) ((ψ.toFun e).map_add ⟨x, hx⟩ ⟨x', hx'⟩)).trans
    (map_add _ _ _)

/-- `intChartSectionOf` is additive in the numerator, at a fixed denominator. -/
theorem intChartSectionOf_add (n : ℤ) (j e : ℕ) (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e) (hs : x + x' ∈ 𝒜 e) :
    intChartSectionOf ψ hf hV n j e he hs
      = intChartSectionOf ψ hf hV n j e he hx + intChartSectionOf ψ hf hV n j e he hx' := by
  unfold intChartSectionOf
  rw [intValue_add ψ e hx hx' hs, map_add, intDivTop_add]

/-- `intChartSection` is additive. -/
theorem intChartSection_add (hd : 0 < d) (n : ℤ)
    (y z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    intChartSection ψ hf hV hd n (y + z)
      = intChartSection ψ hf hV hd n y + intChartSection ψ hf hV hd n z := by
  obtain ⟨j, e, he, x, hx, hy⟩ := exists_int_rep hf hd n y
  obtain ⟨i, e₂, hi, w, hw, hz⟩ := exists_int_rep hf hd n z
  have hE1 := cast_add_mul_add_eq he i
  have hE2 := cast_add_mul_add_eq hi j
  have hE : (((j + i) * d : ℕ) : ℤ) + n = ((i * d + e : ℕ) : ℤ) := by rwa [Nat.add_comm]
  have hji : j * d + e₂ = i * d + e :=
    Nat.cast_injective (show ((j * d + e₂ : ℕ) : ℤ) = ((i * d + e : ℕ) : ℤ) from
      hE2.symm.trans hE)
  have hxw := pow_mul_mem_graded hf i hx
  have hwx' := pow_mul_mem_graded hf j hw
  have hwx : f ^ j * w ∈ 𝒜 (i * d + e) := mem_graded_of_eq 𝒜 hji hwx'
  have hsum : f ^ i * x + f ^ j * w ∈ 𝒜 (i * d + e) := add_mem hxw hwx
  have hden : (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) * (⟨f ^ i, ⟨i, rfl⟩⟩ : Submonoid.powers f)
      = (⟨f ^ (j + i), ⟨j + i, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext (by simp [pow_add])
  have hrep : ((y + z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
        LocalizedModule.Away f A)
      = LocalizedModule.mk (f ^ i * x + f ^ j * w)
          (⟨f ^ (j + i), ⟨j + i, rfl⟩⟩ : Submonoid.powers f) := by
    rw [AddSubgroup.coe_add, hy, hz, LocalizedModule.mk_add_mk, hden]
    simp [Submonoid.smul_def, smul_eq_mul]
  have e1 : intChartSectionOf ψ hf hV n (j + i) (i * d + e) hE hxw
      = intChartSectionOf ψ hf hV n j e he hx :=
    (intChartSectionOf_congr ψ hf hV n hE hE1 hxw hxw (Nat.add_comm j i) rfl).trans
      (intChartSectionOf_mul_pow ψ hf hV n j i e (i * d + e) he hE1 hx hxw)
  have e2 : intChartSectionOf ψ hf hV n (j + i) (i * d + e) hE hwx
      = intChartSectionOf ψ hf hV n i e₂ hi hw :=
    (intChartSectionOf_congr ψ hf hV n hE hE2 hwx hwx' rfl rfl).trans
      (intChartSectionOf_mul_pow ψ hf hV n i j e₂ (j * d + e₂) hi hE2 hw hwx')
  rw [intChartSection_mk ψ hf hV hd n _ (j + i) (i * d + e) hE _ hsum hrep,
    intChartSection_mk ψ hf hV hd n y j e he x hx hy,
    intChartSection_mk ψ hf hV hd n z i e₂ hi w hw hz,
    intChartSectionOf_add ψ hf hV n (j + i) (i * d + e) hE hxw hwx hsum, e1, e2]

/-- The map `(A_f)_n ⟶ Γ(L ^⊗ n, V)`, for `n : ℤ`, as an additive map. -/
def intChartSectionHom (hd : 0 < d) (n : ℤ) :
    gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n →+ Γ(tensorPowerModule T L n, V) :=
  AddMonoidHom.mk' (intChartSection ψ hf hV hd n) (intChartSection_add ψ hf hV hd n)

/-- `intChartSectionHom` is `intChartSection` as a function. -/
@[simp] theorem intChartSectionHom_apply (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    intChartSectionHom ψ hf hV hd n y = intChartSection ψ hf hV hd n y := rfl

end IntChart

end Stacks.AlgebraicGeometry.ProjChartGradedDivision

end
