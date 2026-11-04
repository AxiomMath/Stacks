module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerValues

/-!
# The chart comparison of `θ` is semilinear in every integer degree

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. For `f ∈ 𝒜 d` of positive degree,
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` is the chart-level comparison

  `θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`,

of [Stacks, Tag 01NK] in an arbitrary integer degree `n`, with values in the family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` of [Stacks, Tag 01CU]. It is semilinear over
the degree-zero subring `A_{(f)}`, along the dehomogenisation ring map `A_{(f)} ⟶ Γ(V, 𝒪_T)` of
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.lift_mk`, and it commutes with
restriction to a smaller open of the chart.

## Main results

* `intDivTop_smul_of_resTop_eq`: the integer-degree quotient is `Γ(T, V)`-linear in the
  numerator, for a global numerator whose restriction is a multiple of another's.
* `resTop_intValue_smul_left`: the identity `ψ(p x)|_V = (ψ(p) / ψ(f ^ i)) · ψ(f ^ i x)|_V` in the
  family `tensorPowerModule`.
* `intChartSectionOf_mul_homogeneous`: dividing `p x` by `f ^ {i + j}` is the ratio
  `ψ(p) / ψ(f ^ i)` times the quotient of `x` by `f ^ j`.
* `intChartSection_smul`: the comparison is semilinear over `A_{(f)}`.
* `map_intChartSection`: the comparison commutes with restriction to a smaller open of the chart.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf resTop_eq_ratioOf_smul)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections resTop_mulSections_smul_left)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (mem_graded_of_eq)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.GradedLocalization (gradedPiece smul_mem_gradedPiece)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerDivision (intDivTop intDivOf_smul intPowReindex map_intDivTop)
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

section IntSemilinear

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  {d : ℕ} {f : A} {V : T.Opens} (hf : f ∈ 𝒜 d)
  (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))

/-! ### Linearity of the integer-degree quotient in the numerator -/

omit hf hV in
/-- If the restriction to `V` of a global section `a` of `L ^⊗ (k + n)` is `r` times that of `b`,
then the quotient of `a` by `t` in degree `n` is `r` times the quotient of `b` by `t`. -/
theorem intDivTop_smul_of_resTop_eq {k : ℤ} (t : Γ(tensorPowerModule T L k, ⊤))
    (hVt : V ≤ nonvanishingOpen T (tensorPowerModule T L k) t) (n : ℤ)
    {a b : Γ(tensorPowerModule T L (k + n), ⊤)} {r : Γ(T, V)}
    (h : resTop (tensorPowerModule T L (k + n)) a V
      = r • resTop (tensorPowerModule T L (k + n)) b V) :
    intDivTop L t hVt n a = r • intDivTop L t hVt n b := by
  rw [intDivTop, intDivTop, h, intDivOf_smul]

/-! ### Values of `ψ` restricted to `V` -/

omit hf hV in
/-- The restriction to `V` of the value `intValue ψ k q` is the image under
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` of the restriction of `ψ q`. -/
theorem resTop_intValue (k : ℕ) (q : 𝒜 k) :
    resTop (tensorPowerModule T L (k : ℤ)) (intValue ψ k q) V
      = (powCompare L k).hom.app V (resTop (natTensorPow L k) (ψ.toFun k q) V) :=
  resTop_app _ _ _

/-- For `p` homogeneous of degree `i d` and `x` homogeneous of degree `e`, in the family
`Stacks.AmpleProjectiveImmersion.tensorPowerModule`,
`ψ(p x)|_V = (ψ(p) / ψ(f ^ i)) · ψ(f ^ i x)|_V`. -/
theorem resTop_intValue_smul_left (i e : ℕ) {p x : A} (hp : p ∈ 𝒜 (i * d)) (hx : x ∈ 𝒜 e)
    (hpx : p * x ∈ 𝒜 (i * d + e)) (hfix : f ^ i * x ∈ 𝒜 (i * d + e)) :
    resTop (tensorPowerModule T L ((i * d + e : ℕ) : ℤ))
        (intValue ψ (i * d + e) ⟨p * x, hpx⟩) V
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, HomogeneousRatios.pow_mem hf i⟩)
            (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.toFun (i * d) ⟨p, hp⟩)
          • resTop (tensorPowerModule T L ((i * d + e : ℕ) : ℤ))
              (intValue ψ (i * d + e) ⟨f ^ i * x, hfix⟩) V := by
  have hfi : f ^ i ∈ 𝒜 (i * d) := HomogeneousRatios.pow_mem hf i
  have hnat : resTop (natTensorPow L (i * d + e)) (ψ.toFun (i * d + e) ⟨p * x, hpx⟩) V
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩) (ψ.le_nonvanishingOpen_pow hf hV i)
            (ψ.toFun (i * d) ⟨p, hp⟩)
          • resTop (natTensorPow L (i * d + e)) (ψ.toFun (i * d + e) ⟨f ^ i * x, hfix⟩) V := by
    rw [ψ.map_mul (i * d) e ⟨p, hp⟩ ⟨x, hx⟩ ⟨p * x, hpx⟩ rfl,
      ψ.map_mul (i * d) e ⟨f ^ i, hfi⟩ ⟨x, hx⟩ ⟨f ^ i * x, hfix⟩ rfl]
    exact resTop_mulSections_smul_left L (ψ.toFun e ⟨x, hx⟩)
      (resTop_eq_ratioOf_smul L (ψ.toFun (i * d) ⟨f ^ i, hfi⟩)
        (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.toFun (i * d) ⟨p, hp⟩))
  rw [resTop_intValue ψ (i * d + e) ⟨p * x, hpx⟩, resTop_intValue ψ (i * d + e) ⟨f ^ i * x, hfix⟩,
    hnat]
  exact Scheme.Modules.Hom.app_smul _ _ _

/-! ### The semilinearity -/

/-- In an arbitrary integer degree, dividing `p x` by `f ^ {i + j}`, for `p` homogeneous of
degree `i d`, is the ratio `ψ(p) / ψ(f ^ i)`, a section of `𝒪_T` over `V`, times the quotient of
`x` by `f ^ j`. -/
theorem intChartSectionOf_mul_homogeneous (n : ℤ) (j i e e' : ℕ)
    (he : ((j * d : ℕ) : ℤ) + n = (e : ℕ)) (he' : (((i + j) * d : ℕ) : ℤ) + n = (e' : ℕ))
    {p x : A} (hp : p ∈ 𝒜 (i * d)) (hx : x ∈ 𝒜 e) (hpx : p * x ∈ 𝒜 e') :
    intChartSectionOf ψ hf hV n (i + j) e' he' hpx
      = ratioOf L (ψ.toFun (i * d) ⟨f ^ i, HomogeneousRatios.pow_mem hf i⟩)
            (ψ.le_nonvanishingOpen_pow hf hV i) (ψ.toFun (i * d) ⟨p, hp⟩)
          • intChartSectionOf ψ hf hV n j e he hx := by
  obtain rfl : e' = i * d + e := numerator_index_eq he he'
  have hfi : f ^ i ∈ 𝒜 (i * d) := HomogeneousRatios.pow_mem hf i
  have hfix : f ^ i * x ∈ 𝒜 (i * d + e) := SetLike.mul_mem_graded hfi hx
  rw [← intChartSectionOf_mul_pow ψ hf hV n j i e (i * d + e) he he' hx hfix]
  unfold intChartSectionOf
  refine intDivTop_smul_of_resTop_eq (V := V) _ _ n ?_
  rw [resTop_app, resTop_app, resTop_intValue_smul_left ψ hf hV i e hp hx hpx hfix]
  exact Scheme.Modules.Hom.app_smul _ _ _

/-- In every integer degree, the comparison is semilinear over the degree-zero subring `A_{(f)}`,
along the dehomogenisation ring map `A_{(f)} ⟶ Γ(V, 𝒪_T)` of
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.lift_mk`. -/
theorem intChartSection_smul (hd : 0 < d) (n : ℤ) (a : HomogeneousLocalization.Away 𝒜 f)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) :
    intChartSection ψ hf hV hd n
        ⟨HomogeneousLocalization.val a • (y : LocalizedModule.Away f A),
          smul_mem_gradedPiece 𝒜 _ hf n a y.2⟩
      = (ψ.homogeneousRatios hf hV).lift hd a • intChartSection ψ hf hV hd n y := by
  obtain ⟨i, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf a
  obtain ⟨j, e, he, x, hx, hy⟩ := exists_int_rep hf hd n y
  have hp' : p ∈ 𝒜 (i * d) := mem_graded_of_eq 𝒜 (smul_eq_mul i d) hp
  have hpx : p * x ∈ 𝒜 (i * d + e) := SetLike.mul_mem_graded hp' hx
  have he' : (((i + j) * d : ℕ) : ℤ) + n = ((i * d + e : ℕ) : ℤ) := by
    rw [Nat.cast_add, ← he]; push_cast; ring
  have hden : (⟨f ^ i, ⟨i, rfl⟩⟩ : Submonoid.powers f) * (⟨f ^ j, ⟨j, rfl⟩⟩ : Submonoid.powers f)
      = (⟨f ^ (i + j), ⟨i + j, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext (by simp [pow_add])
  have hrep : HomogeneousLocalization.val (HomogeneousLocalization.Away.mk 𝒜 hf i p hp)
        • (y : LocalizedModule.Away f A)
      = LocalizedModule.mk (p * x) (⟨f ^ (i + j), ⟨i + j, rfl⟩⟩ : Submonoid.powers f) := by
    rw [HomogeneousLocalization.Away.val_mk, hy, LocalizedModule.mk_smul_mk, hden]
    simp [smul_eq_mul]
  rw [intChartSection_mk ψ hf hV hd n _ (i + j) (i * d + e) he' _ hpx hrep,
    intChartSection_mk ψ hf hV hd n y j e he x hx hy,
    intChartSectionOf_mul_homogeneous ψ hf hV n j i e (i * d + e) he he' hp' hx hpx,
    ψ.lift_mk hf hV hd i p hp ⟨p, hp'⟩ rfl]

/-! ### Restriction to a smaller open -/

/-- In every integer degree, the comparison commutes with restriction to a smaller open of the
chart. -/
theorem map_intChartSection (hd : 0 < d) (n : ℤ)
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n) {V' : T.Opens} (i : V' ⟶ V) :
    (tensorPowerModule T L n).presheaf.map i.op (intChartSection ψ hf hV hd n y)
      = intChartSection ψ hf (i.le.trans hV) hd n y := by
  obtain ⟨j, e, he, x, hx, hy⟩ := exists_int_rep hf hd n y
  rw [intChartSection_mk ψ hf hV hd n y j e he x hx hy,
    intChartSection_mk ψ hf (i.le.trans hV) hd n y j e he x hx hy]
  unfold intChartSectionOf
  rw [map_intDivTop]
  rfl

end IntSemilinear

end Stacks.AlgebraicGeometry.ProjChartGradedDivision

end
