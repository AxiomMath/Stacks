module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerSemilinear
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.LocalProduct

/-!
# The chart comparison of `θ` is multiplicative

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` of positive degree,
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` is the chart-level comparison

`θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`,

of [Stacks, Tag 01NK] in every integer degree `n`. It is already known to be additive, semilinear
over `A_{(f)}`, and compatible with shrinking `V`. This file proves it **multiplicative**:

`θ_f(y z) = θ_f(y) · θ_f(z)`,

where the product on the right is the product of two sections of tensor powers over the one open
`V`, `Stacks.TensorPowerDivision.localMul`. That is what makes `θ_f` a map of graded *algebras*
rather than of graded modules.

## The route

A fraction of `A_f`-degree `n` is `x / f ^ j` and one of degree `m` is `x' / f ^ {j'}`, so their
product is `x x' / f ^ {j + j'}`; `θ_f` of it is the quotient of the value `ψ(x x')` by the value
`ψ(f ^ {j + j'})`. The whole content is therefore that **the product of two quotients is the
quotient of the products**, which is
`Stacks.TensorPowerDivision.localMul_intDivTop`, and the multiplicativity of `ψ` in [Stacks, Tag
01CU]'s family, which is
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intMulSections_intValue`.

Both the numerator and the denominator of a fraction of `A_f`-degree `n` lie in **nonnegative**
degrees, however negative `n` is, so the multiplicativity of `ψ` is needed only in nonnegative
bidegrees, where it is available; no product of sections in a negative degree is ever formed from
`ψ` directly.

## Main results

* `…intChartSectionOf_mul` — **multiplicativity on representatives**: the quotient of `x x'` by
  `f ^ {j + j'}` is the product of the quotient of `x` by `f ^ j` with the quotient of `x'` by
  `f ^ {j'}`.
* `…intChartSection_mul` — **the comparison `θ_f` is multiplicative**, in every pair of integer
  degrees.

## Implementation notes

**The degree bookkeeping is where the work is, and it is all reindexing.** A fraction of degree
`n` over `f ^ j` has its numerator at the natural-number index `e` determined by
`(j d : ℤ) + n = e`; the product's numerator sits at `e + e'` and its denominator at
`(j + j') d`, while `localMul_intDivTop` produces them at `(j d + j' d)` and in the grouping
`(j d + n) + (j' d + m)`. The first is
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intDivTop_intValue_congr` — the same step the
cancellation `intChartSectionOf_mul_pow` takes — and the second is
`Stacks.TensorPowerDivision.intPowReindex`, collapsed by
`Stacks.TensorPowerDivision.intPowReindex_trans` after the two factors' reindexings have been
pulled out of the product by `Stacks.TensorPowerDivision.localMul_intPowReindex_left` and
`…_right`. Two reindexings between the same two degrees are the same morphism, the equality of
degrees being a proposition, so the chain closes by `rfl`.

**Nothing here needs a new product.** The product of two local sections of tensor powers over one
open is the multiplication of the Laurent algebra of [Stacks, Tag 01CU],
`Stacks.SheafOfModules.TensorPower.mulBilinear`, which exists in every pair of integer degrees;
`Stacks.TensorPowerDivision.localMul` only names it at the scheme spelling.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (intDivTop intMulSections intPowReindex intPowReindex_trans
  localMul localMul_intDivTop localMul_intPowReindex_left localMul_intPowReindex_right
  localMul_top_eq_intMulSections)
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

section Multiplicative

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- Adding degree identities `a + n = e` and `a' + m = e'` gives `(a + a') + (n + m) = e + e'`. -/
private theorem cast_add_add_eq {a a' e e' : ℕ} {n m : ℤ} (he : (a : ℤ) + n = e)
    (he' : (a' : ℤ) + m = e') : ((a + a' : ℕ) : ℤ) + (n + m) = ((e + e' : ℕ) : ℤ) := by
  push_cast; linarith

/-- **Multiplicativity of the chart comparison on representatives**: the quotient of `x x'` by
`f ^ {j + j'}` is the product, over the one open `V`, of the quotient of `x` by `f ^ j` with the
quotient of `x'` by `f ^ {j'}`.

The denominator is moved from the index `(j + j') d` to `j d + j' d`, where the multiplicativity
`intMulSections_intValue` of `ψ` splits it into `ψ(f ^ j) ψ(f ^ {j'})`, and then the product of the
two quotients is the quotient of the products by
`Stacks.TensorPowerDivision.localMul_intDivTop`. -/
theorem intChartSectionOf_mul (n m : ℤ) (j j' e e' : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he' : ((j' * d : ℕ) : ℤ) + m = (e' : ℕ))
    (hE : (((j + j') * d : ℕ) : ℤ) + (n + m) = ((e + e' : ℕ) : ℤ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e') (hxx : x * x' ∈ 𝒜 (e + e')) :
    intChartSectionOf ψ hf hV (n + m) (j + j') (e + e') hE hxx
      = localMul L (intChartSectionOf ψ hf hV n j e he hx)
          (intChartSectionOf ψ hf hV m j' e' he' hx') := by
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hfj' : f ^ j' ∈ 𝒜 (j' * d) := HomogeneousRatios.pow_mem hf j'
  have hprod : f ^ j * f ^ j' ∈ 𝒜 (j * d + j' * d) := SetLike.mul_mem_graded hfj hfj'
  have hVj := ψ.le_nonvanishingOpen_pow hf hV j
  have hVj' := ψ.le_nonvanishingOpen_pow hf hV j'
  have hmid := cast_add_add_eq he he'
  have hVmid : V ≤ nonvanishingOpen T (tensorPowerModule T L ((j * d + j' * d : ℕ) : ℤ))
      (intValue ψ (j * d + j' * d) ⟨f ^ j * f ^ j', hprod⟩) :=
    le_nonvanishingOpen_intValue ψ hprod
      (ψ.le_nonvanishingOpen_mul hfj hfj' hprod hVj hVj')
  have hVts : V ≤ nonvanishingOpen T
        (tensorPowerModule T L (((j * d : ℕ) : ℤ) + ((j' * d : ℕ) : ℤ)))
      (intMulSections L (intValue ψ (j * d) ⟨f ^ j, hfj⟩)
        (intValue ψ (j' * d) ⟨f ^ j', hfj'⟩)) :=
    le_nonvanishingOpen_intMulSections ψ hfj hfj' hprod hVj hVj'
  have hnum : (intPowReindex L hmid.symm).hom.app ⊤
        (intValue ψ (e + e') ⟨x * x', hxx⟩)
      = (intPowReindex L
            (show (((j * d : ℕ) : ℤ) + n) + (((j' * d : ℕ) : ℤ) + m)
              = (((j * d : ℕ) : ℤ) + ((j' * d : ℕ) : ℤ)) + (n + m) by ring)).hom.app ⊤
          (intMulSections L ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩))
            ((intPowReindex L he'.symm).hom.app ⊤ (intValue ψ e' ⟨x', hx'⟩))) := by
    rw [← localMul_top_eq_intMulSections, localMul_intPowReindex_left,
      localMul_intPowReindex_right, intPowReindex_trans, intPowReindex_trans,
      localMul_top_eq_intMulSections,
      intMulSections_intValue ψ e e' ⟨x, hx⟩ ⟨x', hx'⟩ ⟨x * x', hxx⟩ rfl]
  unfold intChartSectionOf
  rw [intDivTop_intValue_congr ψ (n + m) (HomogeneousRatios.pow_mem hf (j + j')) hprod hxx hxx
      hE hmid (le_nonvanishingOpen_intValue_pow ψ hf hV (j + j')) hVmid
      (Nat.add_mul j j' d) (pow_add f j j') rfl,
    intDivTop_congr_sections
      (intMulSections_intValue ψ (j * d) (j' * d) ⟨f ^ j, hfj⟩ ⟨f ^ j', hfj'⟩
        ⟨f ^ j * f ^ j', hprod⟩ rfl).symm (n + m) hnum hVmid hVts]
  exact (localMul_intDivTop L (intValue ψ (j * d) ⟨f ^ j, hfj⟩)
    (le_nonvanishingOpen_intValue_pow ψ hf hV j) (intValue ψ (j' * d) ⟨f ^ j', hfj'⟩)
    (le_nonvanishingOpen_intValue_pow ψ hf hV j') hVts n m _ _).symm

/-- **The chart-level comparison `θ_f` of [Stacks, Tag 01NK] is multiplicative**, in every pair of
integer degrees: the value on a product of two elements of `A_f` is the product, over the one open
`V`, of the two values. With the additivity
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection_add` and the semilinearity
`…intChartSection_smul` this makes `θ_f` a map of graded algebras rather than of graded modules.

The product of the two elements is given as a third element together with the identity it
satisfies in `A_f`, so that no grading instance on the localization is needed. Representatives
multiply to a representative of the product, and `intChartSectionOf_mul` computes there. -/
theorem intChartSection_mul (hd : 0 < d) (n m : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n)
    (z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f m)
    (w : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (n + m))
    (hw : (w : LocalizedModule.Away f A)
      = (y : LocalizedModule.Away f A) * (z : LocalizedModule.Away f A)) :
    intChartSection ψ hf hV hd (n + m) w
      = localMul L (intChartSection ψ hf hV hd n y) (intChartSection ψ hf hV hd m z) := by
  obtain ⟨j, e, he, x, hx, hy⟩ := exists_int_rep hf hd n y
  obtain ⟨j', e', he', x', hx', hz⟩ := exists_int_rep hf hd m z
  have hxx : x * x' ∈ 𝒜 (e + e') := SetLike.mul_mem_graded hx hx'
  have hE : (((j + j') * d : ℕ) : ℤ) + (n + m) = ((e + e' : ℕ) : ℤ) := by
    rw [Nat.add_mul]; exact cast_add_add_eq he he'
  have hden : (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f) * (⟨f ^ j', ⟨j', rfl⟩⟩ : Submonoid.powers f)
      = (⟨f ^ (j + j'), ⟨j + j', rfl⟩⟩ : Submonoid.powers f) := Subtype.ext (by simp [pow_add])
  have hfac : (y : LocalizedModule.Away f A) * (z : LocalizedModule.Away f A)
      = LocalizedModule.mk (M := A) x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)
        * LocalizedModule.mk (M := A) x' (⟨f ^ j', ⟨j', rfl⟩⟩ : Submonoid.powers f) := by
    rw [hy, hz]
  have hrep : (w : LocalizedModule.Away f A)
      = LocalizedModule.mk (x * x') (⟨f ^ (j + j'), ⟨j + j', rfl⟩⟩ : Submonoid.powers f) :=
    hw.trans (hfac.trans (LocalizedModule.mk_mul_mk.trans
      (congrArg (fun u : Submonoid.powers f => LocalizedModule.mk (M := A) (x * x') u) hden)))
  rw [intChartSection_mk ψ hf hV hd (n + m) w (j + j') (e + e') hE (x * x') hxx hrep,
    intChartSection_mk ψ hf hV hd n y j e he x hx hy,
    intChartSection_mk ψ hf hV hd m z j' e' he' x' hx' hz,
    intChartSectionOf_mul ψ hf hV n m j j' e e' he he' hE hx hx' hxx]

end Multiplicative

end Stacks.AlgebraicGeometry.ProjChartGradedDivision

end
