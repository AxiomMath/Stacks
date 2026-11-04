module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerValues

/-!
# Two chart comparisons agree on the overlap, in every integer degree

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` of positive degree,
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` is the chart-level comparison
`θ_f` of [Stacks, Tag 01NK] in an arbitrary **integer** degree.

`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedOverlap` proves that `θ_f` and
`θ_g` agree on the overlap `T_{ψ(f)} ⊓ T_{ψ(g)}` of their charts, for the comparison in a
**natural-number** degree, over the iterated tensor products `Stacks.TensorPowers.natTensorPow`.
This file proves the same for every integer degree, over [Stacks, Tag 01CU]'s family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`. The `θ` of [Stacks, Tag 01NK] is a map of
`ℤ`-graded algebras, so it is the integer-degree statement that is the compatibility of the family
`(θ_f)_f` across the cover `U(ψ) = ⋃_f T_{ψ(f)}`; the natural-number one covers only the
nonnegative half of the grading.

## Main results

* `…intChartSectionOf_mul_left` — **multiplying numerator and denominator by a nonvanishing
  `ψ(u)` does not change a chart value**, in every integer degree. This is the integer-degree
  analogue of `…ProjChartGradedOverlap.chartSectionOf_mul_left`, and it is
  `…ProjChartGradedDivision.intChartSectionOf_mul_pow` with the factor `f ^ m` replaced by an
  arbitrary homogeneous `u` whose value does not vanish.
* `…intChartSectionOf_eq_of_cross` — **`θ_f` and `θ_g` agree on two cross-multiplying
  representatives**, in every integer degree.
* `…intChartSectionOf_eq_of_cross_mul_pow` — the same under the hypothesis carrying a factor
  `(f g) ^ c`, which is what equality of the two fractions in `A_{f g}` gives.
* `…intChartSection_eq_of_mk_eq_away` — **the chart-level comparisons of two homogeneous elements
  agree on the overlap of their charts, in every integer degree.**

## Implementation notes

Every proof is the one its natural-number counterpart uses, with the three inputs replaced by
their integer-degree analogues: the cancellation
`Stacks.TensorPowerDivision.intDivTop_intMulSections_cancel`, the multiplicativity of `ψ` in
[Stacks, Tag 01CU]'s family
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intMulSections_intValue`, and the two congruence
lemmas `…intDivTop_intValue_congr` and `…intDivTop_congr_sections`. The one difference is the
numerator's index: a fraction of degree `n` over `f ^ j` has its numerator at the natural number
`e` determined by `(j d : ℤ) + n = e`, so each statement carries that equation and the single
reindexing `Stacks.TensorPowerDivision.intPowReindex` that it forces, exactly as
`…intChartSectionOf` does by construction.

No product of sections in a negative degree is formed: the numerator and the denominator of a
fraction of `A_f`-degree `n` both sit in nonnegative degrees however negative `n` is.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intValue intChartSection
  intChartSectionOf intChartSectionOf_mul_pow intChartSection_mk intDivTop_congr_sections
  intDivTop_intValue_congr intMulSections_intValue le_nonvanishingOpen_intMulSections
  le_nonvanishingOpen_intValue_pow)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (intDivTop intMulSections intPowReindex intPowReindex_trans
  intMulSections_intPowReindex intDivTop_intMulSections_cancel)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedOverlap

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)

/-! ### A chart value read over a larger denominator -/

section Common

variable {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-- **Multiplying numerator and denominator of a chart value by a nonvanishing `ψ(u)` does not
change it**, in an arbitrary integer degree: for `u` homogeneous of degree `m` whose value does not
vanish on `V`, the quotient `ψ(u x) / ψ(u f ^ j)` over `V` is `θ_f(x / f ^ j)`.

This is the form in which two chart values over *different* denominators are compared: taking
`u = g ^ k` on one side and `u = f ^ j` on the other puts both over the one denominator
`ψ(g ^ k f ^ j)`. It is
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf_mul_pow` with the factor
`f ^ m` replaced by an arbitrary homogeneous element whose value is nonvanishing. -/
theorem intChartSectionOf_mul_left (n : ℤ) (j : ℕ) {m e : ℕ} {u : A} (hu : u ∈ 𝒜 m)
    (hVu : V ≤ nonvanishingOpen T (natTensorPow L m) (ψ.toFun m ⟨u, hu⟩))
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    (hme : ((m + j * d : ℕ) : ℤ) + n = ((m + e : ℕ) : ℤ))
    {x : A} (hx : x ∈ 𝒜 e) (hprod : u * f ^ j ∈ 𝒜 (m + j * d))
    (hux : u * x ∈ 𝒜 (m + e))
    (hmid : V ≤ nonvanishingOpen T (tensorPowerModule T L ((m + j * d : ℕ) : ℤ))
      (intValue ψ (m + j * d) ⟨u * f ^ j, hprod⟩)) :
    intDivTop L (intValue ψ (m + j * d) ⟨u * f ^ j, hprod⟩) hmid n
        ((intPowReindex L hme.symm).hom.app ⊤ (intValue ψ (m + e) ⟨u * x, hux⟩))
      = intChartSectionOf ψ hf hV n j e he hx := by
  have hfj : f ^ j ∈ 𝒜 (j * d) := HomogeneousRatios.pow_mem hf j
  have hVmul : V ≤ nonvanishingOpen T
        (tensorPowerModule T L (((m : ℕ) : ℤ) + ((j * d : ℕ) : ℤ)))
      (intMulSections L (intValue ψ m ⟨u, hu⟩) (intValue ψ (j * d) ⟨f ^ j, hfj⟩)) :=
    le_nonvanishingOpen_intMulSections ψ hu hfj hprod hVu
      (ψ.le_nonvanishingOpen_pow hf hV j)
  have hnum : (intPowReindex L hme.symm).hom.app ⊤ (intValue ψ (m + e) ⟨u * x, hux⟩)
      = (intPowReindex L
            (Int.add_assoc ((m : ℕ) : ℤ) ((j * d : ℕ) : ℤ) n).symm).hom.app ⊤
          (intMulSections L (intValue ψ m ⟨u, hu⟩)
            ((intPowReindex L he.symm).hom.app ⊤ (intValue ψ e ⟨x, hx⟩))) := by
    rw [intMulSections_intPowReindex, intPowReindex_trans,
      intMulSections_intValue ψ m e ⟨u, hu⟩ ⟨x, hx⟩ ⟨u * x, hux⟩ rfl]
  unfold intChartSectionOf
  rw [intDivTop_congr_sections
      (intMulSections_intValue ψ m (j * d) ⟨u, hu⟩ ⟨f ^ j, hfj⟩ ⟨u * f ^ j, hprod⟩ rfl).symm
      n hnum hmid hVmul]
  exact intDivTop_intMulSections_cancel L (intValue ψ (j * d) ⟨f ^ j, hfj⟩)
    (le_nonvanishingOpen_intValue_pow ψ hf hV j) (intValue ψ m ⟨u, hu⟩) hVmul n _

/-- A chart value is unchanged by multiplying numerator and denominator by `f ^ c`. -/
private theorem intChartSectionOf_eq_pow_mul (n : ℤ) (j c : ℕ) {e : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) {x : A} (hx : x ∈ 𝒜 e)
    (hE : (((c + j) * d : ℕ) : ℤ) + n = ((c * d + e : ℕ) : ℤ) := by
      push_cast at *; linarith) :
    intChartSectionOf ψ hf hV n j e he hx = intChartSectionOf ψ hf hV n (c + j) (c * d + e) hE
      (SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hf c) hx) :=
  (intChartSectionOf_mul_pow ψ hf hV n j c e (c * d + e) he hE hx _).symm

end Common

/-! ### The two comparisons agree on the overlap -/

section Overlap

variable {d d' : ℕ} {f g : A} {V : T.Opens} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d')
  (hVf : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
  (hVg : V ≤ nonvanishingOpen T (natTensorPow L d') (ψ.toFun d' ⟨g, hg⟩))

/-- Reading a chart value over the denominator `ψ(g ^ k f ^ j)`, as in `intChartSectionOf_mul_left`
with `u = g ^ k`. -/
private theorem intChartSectionOf_eq_intDivTop_mul (n : ℤ) (j k : ℕ) {e : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) {x : A} (hx : x ∈ 𝒜 e)
    (hp : g ^ k * f ^ j ∈ 𝒜 (k * d' + j * d)) (hn : g ^ k * x ∈ 𝒜 (k * d' + e))
    (h' : ((k * d' + j * d : ℕ) : ℤ) + n = ((k * d' + e : ℕ) : ℤ) := by
      push_cast at *; linarith) :
    intChartSectionOf ψ hf hVf n j e he hx
      = intDivTop L (intValue ψ (k * d' + j * d) ⟨g ^ k * f ^ j, hp⟩)
        (Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue ψ hp
          (ψ.le_nonvanishingOpen_mul
            (HomogeneousRatios.pow_mem hg k) (HomogeneousRatios.pow_mem hf j) hp
            (ψ.le_nonvanishingOpen_pow hg hVg k) (ψ.le_nonvanishingOpen_pow hf hVf j))) n
        ((intPowReindex L h'.symm).hom.app ⊤ (intValue ψ (k * d' + e) ⟨g ^ k * x, hn⟩)) :=
  (intChartSectionOf_mul_left ψ hf hVf n j (HomogeneousRatios.pow_mem hg k)
    (ψ.le_nonvanishingOpen_pow hg hVg k) he h' hx hp hn _).symm

/-- **`θ_f` and `θ_g` agree on two cross-multiplying representatives**, in every integer degree.
If `x` is homogeneous of the degree `e` forced by `j` and `n`, `x'` of the degree `e₂` forced by
`k` and `n`, and `x g ^ k = x' f ^ j`, then the quotients `ψ(x) / ψ(f ^ j)` and
`ψ(x') / ψ(g ^ k)` are the same section of `L ^⊗ n` over an open where neither `ψ(f)` nor `ψ(g)`
vanishes.

Both sides are brought over the common denominator `ψ(g ^ k f ^ j)` by
`intChartSectionOf_mul_left`, after which the two quotients differ only by the transports
`k d' + j d = j d + k d'`, `g ^ k f ^ j = f ^ j g ^ k` and the hypothesis `g ^ k x = f ^ j x'`,
all three of which
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intDivTop_intValue_congr` takes. -/
theorem intChartSectionOf_eq_of_cross (n : ℤ) (j k : ℕ) {e e₂ : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he₂ : ((k * d' : ℕ) : ℤ) + n = (e₂ : ℕ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e₂) (hcross : x * g ^ k = x' * f ^ j) :
    intChartSectionOf ψ hf hVf n j e he hx = intChartSectionOf ψ hg hVg n k e₂ he₂ hx' := by
  have hp1 : g ^ k * f ^ j ∈ 𝒜 (k * d' + j * d) :=
    SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hg k) (HomogeneousRatios.pow_mem hf j)
  have hp2 : f ^ j * g ^ k ∈ 𝒜 (j * d + k * d') :=
    SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hf j) (HomogeneousRatios.pow_mem hg k)
  have hn1 : g ^ k * x ∈ 𝒜 (k * d' + e) :=
    SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hg k) hx
  have hn2 : f ^ j * x' ∈ 𝒜 (j * d + e₂) :=
    SetLike.mul_mem_graded (HomogeneousRatios.pow_mem hf j) hx'
  rw [intChartSectionOf_eq_intDivTop_mul ψ hf hg hVf hVg n j k he hx hp1 hn1,
    intChartSectionOf_eq_intDivTop_mul ψ hg hf hVg hVf n k j he₂ hx' hp2 hn2]
  exact intDivTop_intValue_congr ψ n hp1 hp2 hn1 hn2
    (by push_cast at *; linarith) (by push_cast at *; linarith) _ _
    (Nat.add_comm _ _) (mul_comm _ _) (by rw [mul_comm (g ^ k) x, hcross, mul_comm])

/-- **The same agreement under the hypothesis with a factor `(f g) ^ c`**, in every integer degree.
This is equality of the two fractions `x / f ^ j` and `x' / g ^ k` in the localization of `A` at
`f g`, written out: the cross-multiplication of `intChartSectionOf_eq_of_cross` is the case
`c = 0`.

Replacing the representatives by `f ^ c x / f ^ {c + j}` and `g ^ c x' / g ^ {c + k}` — which
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionOf_mul_pow` does not change the
value of — turns the hypothesis into a cross-multiplication of the new numerators. -/
theorem intChartSectionOf_eq_of_cross_mul_pow (n : ℤ) (j k c : ℕ) {e e₂ : ℕ}
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he₂ : ((k * d' : ℕ) : ℤ) + n = (e₂ : ℕ))
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e₂)
    (hcross : f ^ c * g ^ c * (x * g ^ k) = f ^ c * g ^ c * (x' * f ^ j)) :
    intChartSectionOf ψ hf hVf n j e he hx = intChartSectionOf ψ hg hVg n k e₂ he₂ hx' := by
  rw [intChartSectionOf_eq_pow_mul ψ hf hVf n j c he hx,
    intChartSectionOf_eq_pow_mul ψ hg hVg n k c he₂ hx']
  refine intChartSectionOf_eq_of_cross ψ hf hg hVf hVg n (c + j) (c + k) _ _ _ _ ?_
  calc f ^ c * x * g ^ (c + k) = f ^ c * g ^ c * (x * g ^ k) := by rw [pow_add]; ring
    _ = f ^ c * g ^ c * (x' * f ^ j) := hcross
    _ = g ^ c * x' * f ^ (c + j) := by rw [pow_add]; ring

/-- **The chart-level comparisons of two homogeneous elements agree on the overlap of their
charts, in every integer degree.** For `y` in the degree-`n` part of `A_f` and `z` in the
degree-`n` part of `A_g` whose representatives `x / f ^ j` and `x' / g ^ k` become equal in the
localization of `A` at `f g`, the sections `θ_f(y)` and `θ_g(z)` of [Stacks, Tag 01CU]'s
`L ^⊗ n` over `V ≤ T_{ψ(f)} ⊓ T_{ψ(g)}` coincide.

With `Stacks.AlgebraicGeometry.ProjChartGradedDivision.map_intChartSection`, which says each
`θ_f` commutes with restriction inside its own chart, this is the compatibility of the family
`(θ_f)_{f ∈ A_+}` across the cover `U(ψ) = ⋃_f T_{ψ(f)}` in every integer degree.
`Stacks.AlgebraicGeometry.ProjChartGradedOverlap.chartSection_eq_of_mk_eq_away` is the same
statement in a natural-number degree, over the iterated tensor products.

The hypothesis is stated as an equality of the cross-multiplied numerators in the localization of
`A` at `f g`, which `LocalizedModule.mk_eq` turns into the factor `(f g) ^ c` that
`intChartSectionOf_eq_of_cross_mul_pow` takes. -/
theorem intChartSection_eq_of_mk_eq_away (hd : 0 < d) (hd' : 0 < d') (n : ℤ) (j k : ℕ)
    {e e₂ : ℕ} (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ))
    (he₂ : ((k * d' : ℕ) : ℤ) + n = (e₂ : ℕ))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n)
    (z : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) g n)
    {x x' : A} (hx : x ∈ 𝒜 e) (hx' : x' ∈ 𝒜 e₂)
    (hy : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk x (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f))
    (hz : (z : LocalizedModule.Away g A)
      = LocalizedModule.mk x' (⟨g ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers g))
    (hmk : LocalizedModule.mk (M := A) (x * g ^ k) (1 : Submonoid.powers (f * g))
      = LocalizedModule.mk (x' * f ^ j) (1 : Submonoid.powers (f * g))) :
    intChartSection ψ hf hVf hd n y = intChartSection ψ hg hVg hd' n z := by
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hmk
  obtain ⟨c, hc⟩ := u.2
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul] at hu
  rw [← hc] at hu
  rw [intChartSection_mk ψ hf hVf hd n y j e he x hx hy,
    intChartSection_mk ψ hg hVg hd' n z k e₂ he₂ x' hx' hz]
  refine intChartSectionOf_eq_of_cross_mul_pow ψ hf hg hVf hVg n j k c he he₂ hx hx' ?_
  rw [← mul_pow]
  exact hu

end Overlap

end Stacks.AlgebraicGeometry.ProjChartGradedOverlap

end
