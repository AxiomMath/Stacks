module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletion
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalSectionRing
public import StacksFrontier.AlgebraicGeometry.RelativeProj.PolynomialAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic

/-!
# The exceptional divisor of the blowup at infinity is `Proj_Z(𝒞_{Z/X,*}[S])`

Let `i : Z ⟶ X` be a closed immersion, `b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in the centre `∞(Z)`
and `E ⊆ W` its exceptional divisor. This file proves assertion (5) of [Stacks, Tag 0FBG]:

  `E = Proj_Z(𝒞_{Z/X,*}[S])`,

with `S` a variable placed in degree one: `E` is isomorphic over `Z` to the relative `Proj` of the
quasi-coherent graded `𝒪_Z`-algebra `𝒞_{Z/X,*}[S]`
(`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.polynomial` of the conormal algebra).

## The route

This is the proof of the source. Over an affine open `U = Spec A` of `X`, with `I` the ideal of
`Z ∩ U`, the part of `E` over `U` is `Proj B_U` with `B_U = A/I ⊗_{A[s]} A[s][J t]`,
`J = (I, s)` (`Stacks.Chow.exceptionalProjChart`, from Stacks 0804 and 01N2), and

  `B_U = Gr_J(A[s]) = Gr_I(A)[T] = Γ(Z ∩ U, 𝒞_{Z/X,*})[S]`

(`Stacks.Chow.centreChartToGradedEquiv`, from the description of the powers of `J`, and
`Stacks.Conormal.gradedSectionRingEquiv`, Divisors Lemma 0633). This file checks that these ring
isomorphisms are graded, compatible with the structure maps and with restriction to a smaller
affine open, and glues them (Stacks 01LH) along the gluing problem of `E` over the affine opens of
`X` (`Stacks.Chow.exceptionalBasisGluingData`).

## Main definitions

* `Stacks.Chow.conormalPolynomialAlgebra`: `𝒞_{Z/X,*}[S]`.
* `Stacks.Chow.conormalPolynomialProj`: `Proj_Z(𝒞_{Z/X,*}[S])`, with its projection
  `Stacks.Chow.conormalPolynomialProjToBase` to `Z`.
* `Stacks.Chow.exceptionalDivisorIsoConormalPolynomialProj`: **assertion (5)**,
  `E ≅ Proj_Z(𝒞_{Z/X,*}[S])`.

## Main results

* `Stacks.Chow.exceptionalDivisorIsoConormalPolynomialProj_hom_toBase`: the isomorphism lies
  over `Z`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AssociatedGraded

universe u

namespace Stacks.Chow

/-! ### Degrees in `Gr_J(A[s]) = Gr_I(A)[T]` -/

section Algebra

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The inverse of `Gr_I(A)[T] ≅ Gr_J(A[s])` is `infinityChartGradedInv`. -/
theorem infinityChartGradedEquiv_symm_apply (x : gradedRing (infinityChartIdeal I)) :
    (infinityChartGradedEquiv I).symm x = infinityChartGradedInv I x :=
  (RingEquiv.symm_apply_eq _).2 (infinityChartGradedMap_comp_inv I x).symm

/-- The class of `a ∈ Iⁿ` is homogeneous of degree `n`. -/
theorem classOfPow_mem_grading (n : ℕ) (a : ↥(I ^ n)) :
    classOfPow I n a ∈ AssociatedGraded.grading I n :=
  AssociatedGraded.of_mem_grading I _

/-- **`Gr_J(A[s]) ⟶ Gr_I(A)[T]` preserves degrees**, `T` in degree one: the class of `f ∈ Jⁿ` goes
to `∑_{j ≤ n} (class of the coefficient of sʲ in degree n - j) Tʲ`. -/
theorem infinityChartGradedInv_classOfPow_mem (n : ℕ) (f : ↥(infinityChartIdeal I ^ n)) :
    infinityChartGradedInv I (classOfPow _ n f) ∈
      Stacks.PolynomialGrading.grading (AssociatedGraded.grading I) n := by
  rw [infinityChartGradedInv_classOfPow, infinityChartGradedInvRep_apply]
  refine sum_mem fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h := Stacks.PolynomialGrading.monomial_mem_grading (j := j)
    (classOfPow_mem_grading I (n - j) ⟨(f : Polynomial A).coeff j, coeff_mem_pow_sub I f.2 j⟩)
  rwa [Nat.sub_add_cancel hjn] at h

end Algebra

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### The graded algebra `𝒞_{Z/X,*}[S]` and its relative `Proj` -/

/-- **The graded algebra `𝒞_{Z/X,*}[S]`** on `Z`: the conormal algebra of `Z` in `X` with a
variable `S` adjoined in degree one. -/
abbrev conormalPolynomialAlgebra : Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra Z :=
  (Stacks.Conormal.conormalSiteAlgebra i).polynomial

/-- **`Proj_Z(𝒞_{Z/X,*}[S])`**, the relative `Proj` over `Z` of `𝒞_{Z/X,*}[S]`. -/
abbrev conormalPolynomialProj : Scheme.{u} :=
  Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj (conormalPolynomialAlgebra i)

/-- The projection `Proj_Z(𝒞_{Z/X,*}[S]) ⟶ Z`. -/
abbrev conormalPolynomialProjToBase : conormalPolynomialProj i ⟶ Z :=
  Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase (conormalPolynomialAlgebra i)

variable (U : X.affineOpens)

/-- The affine open `Z ∩ U` of `Z`. -/
abbrev centreSite : Z.AffineZariskiSite := ⟨i ⁻¹ᵁ U.1, isAffineOpen_centrePreimage i U⟩

/-! ### The graded ring of the chart of `E` over `U` -/

section Chart

/-- `Gr_𝒥(Γ(V)) ≅ Gr_I(A)[T]` preserves degrees. -/
theorem centreGradedTransport_mem (n : ℕ)
    (f : ↥((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n)) :
    centreGradedTransport i U (classOfPow _ n f) ∈
      Stacks.PolynomialGrading.grading
        (AssociatedGraded.grading (Stacks.Conormal.chartIdeal i U)) n := by
  rw [centreGradedTransport, RingHom.comp_apply, gradedRingMapOfRingHom_classOfPow]
  change (infinityChartGradedEquiv _).symm _ ∈ _
  rw [infinityChartGradedEquiv_symm_apply]
  exact infinityChartGradedInv_classOfPow_mem _ n _

/-- **`B_U ≅ Gr_I(A)[T]` preserves degrees.** -/
theorem centreChartToGraded_mem {n : ℕ} {x : centreChartRing i U}
    (hx : x ∈ centreChartGrading i U n) :
    centreChartToGraded i U x ∈
      Stacks.PolynomialGrading.grading
        (AssociatedGraded.grading (Stacks.Conormal.chartIdeal i U)) n := by
  change x ∈ (centreReesGrading i U n).baseChange Γ(Z, i ⁻¹ᵁ U.1) at hx
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    rw [TensorProduct.mk_apply, centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_tmul,
      map_one, map_one, one_mul, Stacks.Blowup.reesToGraded_of_mem _ hr]
    exact centreGradedTransport_mem i U n _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx =>
    obtain ⟨r, rfl⟩ := Scheme.Hom.app_surjective i U.1 U.2 s
    rw [Algebra.smul_def, map_mul, centreChartToGraded_algebraMap]
    have h := SetLike.mul_mem_graded (Stacks.PolynomialGrading.C_mem_grading
      (show Stacks.Blowup.gradeZeroRingHom _ r ∈
        AssociatedGraded.grading (Stacks.Conormal.chartIdeal i U) 0 from
        AssociatedGraded.of_mem_grading _ _)) hx
    rwa [zero_add] at h

/-- `B_U ⟶ Gr_I(A)[T]` as a homomorphism of graded rings. -/
def centreChartGradedToGraded :
    centreChartGrading i U →+*ᵍ
      Stacks.PolynomialGrading.grading
        (AssociatedGraded.grading (Stacks.Conormal.chartIdeal i U)) where
  toRingHom := centreChartToGraded i U
  map_mem hx := centreChartToGraded_mem i U hx

/-- **The ring isomorphism `B_U ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})[S]`**: `B_U ≅ Gr_I(A)[T]` followed by
`Gr_I(A) ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})` on coefficients. -/
def polynomialChartRingEquiv :
    centreChartRing i U ≃+*
      Polynomial ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1)) :=
  (centreChartToGradedEquiv i U).trans
    (Polynomial.mapEquiv (Stacks.Conormal.gradedSectionRingEquiv i U inferInstance))

/-- `B_U ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` as a homomorphism of graded rings. -/
def polynomialChartGradedInv :
    centreChartGrading i U →+*ᵍ (conormalPolynomialAlgebra i).grading (centreSite i U) :=
  (Stacks.PolynomialGrading.map
    (Stacks.Conormal.gradedSectionRingGradedHom i U inferInstance)).comp
    (centreChartGradedToGraded i U)

theorem polynomialChartRingEquiv_apply (x : centreChartRing i U) :
    polynomialChartRingEquiv i U x = (centreChartToGraded i U x).map
      (Stacks.Conormal.gradedSectionRingHom i U inferInstance) := by
  rw [polynomialChartRingEquiv, RingEquiv.trans_apply, Polynomial.mapEquiv_apply]
  rfl

theorem polynomialChartGradedInv_apply (x : centreChartRing i U) :
    polynomialChartGradedInv i U x = polynomialChartRingEquiv i U x :=
  (polynomialChartRingEquiv_apply i U x).symm

/-- `Γ(Z ∩ U, 𝒞_{Z/X,*})[S] ⟶ B_U` as a homomorphism of graded rings. -/
def polynomialChartGradedHom :
    (conormalPolynomialAlgebra i).grading (centreSite i U) →+*ᵍ centreChartGrading i U where
  toRingHom := (polynomialChartRingEquiv i U).symm.toRingHom
  map_mem hx := Stacks.GradedTransport.symm_mem (centreChartGrading i U)
    ((conormalPolynomialAlgebra i).grading (centreSite i U)) (polynomialChartRingEquiv i U)
    (fun _ x h => polynomialChartGradedInv_apply i U x ▸ (polynomialChartGradedInv i U).map_mem h)
    hx

theorem polynomialChartGradedHom_apply (p) :
    polynomialChartGradedHom i U p = (polynomialChartRingEquiv i U).symm p := rfl

theorem polynomialChartGradedHom_comp_inv :
    (polynomialChartGradedHom i U).comp (polynomialChartGradedInv i U) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => by
    change (polynomialChartRingEquiv i U).symm (polynomialChartGradedInv i U x) = x
    rw [polynomialChartGradedInv_apply, RingEquiv.symm_apply_apply]

theorem polynomialChartGradedInv_comp_hom :
    (polynomialChartGradedInv i U).comp (polynomialChartGradedHom i U) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => by
    change polynomialChartGradedInv i U ((polynomialChartRingEquiv i U).symm x) = x
    rw [polynomialChartGradedInv_apply, RingEquiv.apply_symm_apply]

/-- **`Proj B_U ≅ Proj Γ(Z ∩ U, 𝒞_{Z/X,*})[S]`.** -/
def polynomialChartProjInv :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶
      (conormalPolynomialAlgebra i).projOver (centreSite i U) :=
  Proj.map (polynomialChartGradedHom i U)
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _
      (polynomialChartGradedHom_comp_inv i U))

instance isIso_polynomialChartProjInv : IsIso (polynomialChartProjInv i U) :=
  AlgebraicGeometry.Proj.isIso_map _
    (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _
      (polynomialChartGradedInv_comp_hom i U))
    (polynomialChartGradedInv_comp_hom i U) (polynomialChartGradedHom_comp_inv i U)

/-- The identification of the charts on scalars: `s ↦ s` in degree zero. -/
theorem polynomialChartRingEquiv_algebraMap (s : Γ(Z, i ⁻¹ᵁ U.1)) :
    polynomialChartRingEquiv i U (algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) s) =
      Polynomial.C ((Stacks.Conormal.conormalSheafGradedAlgebra i).strHom (i ⁻¹ᵁ U.1) s) := by
  obtain ⟨r, rfl⟩ := Scheme.Hom.app_surjective i U.1 U.2 s
  rw [polynomialChartRingEquiv_apply, centreChartToGraded_algebraMap, Polynomial.map_C]
  exact congrArg Polynomial.C (Stacks.Conormal.gradedSectionRingHom_gradeZero i U _ r)

/-- **`Proj B_U ≅ Proj Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` lies over `Z ∩ U`.** -/
theorem polynomialChartProjInv_toSpecZero :
    polynomialChartProjInv i U ≫ Proj.toSpecZero
        ((conormalPolynomialAlgebra i).grading (centreSite i U)) ≫
      Spec.map ((conormalPolynomialAlgebra i).strZero (centreSite i U)) =
      centreChartToSpec i U :=
  AlgebraicGeometry.Proj.map_toSpecZero_specMap _ _ _ _
    (GradedRingHom.comp_gradedZeroRingHom_eq _ _ _ fun s =>
      (congrArg (polynomialChartGradedHom i U)
        (Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply _ _ s)).trans
        ((RingEquiv.symm_apply_eq _).2 (polynomialChartRingEquiv_algebraMap i U s).symm))

end Chart

/-! ### `Proj_Z(𝒞_{Z/X,*}[S])` as a solution of the gluing problem of `E` -/

section Gluing

/-- The chart of `Proj_Z(𝒞_{Z/X,*}[S])` over `Z ∩ U`, with source the chart `Proj B_U` of `E`. -/
def polynomialGluingChart :
    AlgebraicGeometry.Proj (centreChartGrading i U) ⟶ conormalPolynomialProj i :=
  polynomialChartProjInv i U ≫
    Stacks.AlgebraicGeometry.RelativeProjGlue.chart (conormalPolynomialAlgebra i) (centreSite i U)

/-- `Proj B_U ≅ Proj Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` lies over `U`. -/
theorem polynomialChartProjInv_toOpen :
    polynomialChartProjInv i U ≫ (conormalPolynomialAlgebra i).toOpen (centreSite i U) ≫
        (i ∣_ U.1) = exceptionalProjChartToOpen i U := by
  change polynomialChartProjInv i U ≫ (Proj.toSpecZero _ ≫
      Spec.map ((conormalPolynomialAlgebra i).strZero (centreSite i U)) ≫
        (isAffineOpen_centrePreimage i U).isoSpec.inv) ≫ (i ∣_ U.1) =
    centreChartToSpec i U ≫ (isAffineOpen_centrePreimage i U).isoSpec.inv ≫ (i ∣_ U.1)
  rw [← polynomialChartProjInv_toSpecZero i U]
  simp only [Category.assoc]

/-- **The chart of `Proj_Z(𝒞_{Z/X,*}[S])` over `Z ∩ U` is the part of it over `U`**, with source
the chart `Proj B_U` of `E`. -/
theorem isPullback_polynomialGluingChart :
    IsPullback (exceptionalProjChartToOpen i U) (polynomialGluingChart i U) U.1.ι
      (conormalPolynomialProjToBase i ≫ i) := by
  have h1 := (Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_chart
    (conormalPolynomialAlgebra i) (centreSite i U)).paste_horiz (isPullback_morphismRestrict i U.1)
  refine IsPullback.of_iso h1 (asIso (polynomialChartProjInv i U)).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact polynomialChartProjInv_toOpen i U
  · simp only [Iso.refl_hom, Iso.symm_hom, asIso_inv, polynomialGluingChart]
    exact (Category.comp_id _).trans (IsIso.inv_hom_id_assoc _ _).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

variable {U} {V : X.affineOpens}

/-- `Γ(X, U)[s] ≅ Γ(𝐏¹_X, V)` carries `x ∈ Iⁿ` into `𝒥ⁿ`. -/
theorem infinityChartSectionsEquiv_C_mem_pow {n : ℕ} {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U ^ n) :
    infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n := by
  rw [ideal_infinityCentreIdeal_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (C_mem_pow_infinityChartIdeal hx)

/-- `B_U ⟶ Gr_I(A)[T]` on `1 ⊗ x tⁿ`, `x ∈ Iⁿ`. -/
theorem centreChartToGraded_tmul_C_pow (n : ℕ) {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U ^ n) :
    centreChartToGraded i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        (⟨Polynomial.monomial n (infinityChartSectionsEquiv U (Polynomial.C x)),
          reesAlgebra.monomial_mem.mpr (infinityChartSectionsEquiv_C_mem_pow i hx)⟩ :
          reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)))) =
      Polynomial.C (classOfPow _ n ⟨x, hx⟩) := by
  rw [centreChartToGraded, Stacks.Blowup.baseChangeReesToGraded_tmul, map_one, map_one, one_mul,
    Stacks.Blowup.reesToGraded_monomial _ n ⟨_, infinityChartSectionsEquiv_C_mem_pow i hx⟩]
  exact centreGradedTransport_classOfPow_C i U n hx _

/-- `B_U ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` on `1 ⊗ x tⁿ`, `x ∈ Iⁿ`: it is the constant polynomial on
the homogeneous section of degree `n` that `x` names. -/
theorem polynomialChartRingEquiv_tmul_C_pow (n : ℕ) {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U ^ n) :
    polynomialChartRingEquiv i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        (⟨Polynomial.monomial n (infinityChartSectionsEquiv U (Polynomial.C x)),
          reesAlgebra.monomial_mem.mpr (infinityChartSectionsEquiv_C_mem_pow i hx)⟩ :
          reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)))) =
      Polynomial.C (Stacks.Conormal.gradedSectionRingHom i U inferInstance
        (classOfPow _ n ⟨x, hx⟩)) := by
  rw [polynomialChartRingEquiv_apply, centreChartToGraded_tmul_C_pow, Polynomial.map_C]

/-- `B_U ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` on `1 ⊗ s t`: it is the variable `S`. -/
theorem polynomialChartRingEquiv_tmul_X :
    polynomialChartRingEquiv i U ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U)) = Polynomial.X := by
  rw [polynomialChartRingEquiv_apply, centreChartToGraded_tmul_X, Polynomial.map_X]

omit [IsClosedImmersion i] in
/-- The restriction of the graded rings of the charts of `E` on `1 ⊗ j tⁿ`. -/
theorem centreChartRestrict_tmul_monomial (h : V.1 ≤ U.1) (n : ℕ)
    {j : Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)}
    {j' : Γ(relativeProjectiveLine X, (infinityChartAffineOpen V).1)}
    (hj : j ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n)
    (hj' : j' ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen V) ^ n)
    (hjj : (lineChartRestrict h).hom j = j') :
    centreChartRestrict i h ((1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        (⟨Polynomial.monomial n j, reesAlgebra.monomial_mem.mpr hj⟩ :
          reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U)))) =
      (1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ
        (⟨Polynomial.monomial n j', reesAlgebra.monomial_mem.mpr hj'⟩ :
          reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen V))) := by
  change centreChartRestrictRingHom i h _ = _
  rw [centreChartRestrictRingHom_tmul, map_one]
  congr 1
  refine Subtype.ext ?_
  rw [Stacks.Blowup.coe_reesRestrict]
  change Polynomial.map _ (Polynomial.monomial n j) = Polynomial.monomial n j'
  rw [Polynomial.map_monomial]
  exact congrArg _ hjj

/-- The identification of the charts is compatible with restriction, on the constants
`C x`, `x ∈ Iⁿ`. -/
theorem centreChartRestrict_polynomialChartGradedHom_C (h : V.1 ≤ U.1) (n : ℕ) {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U ^ n) :
    centreChartRestrict i h (polynomialChartGradedHom i U (Polynomial.C
        (Stacks.Conormal.gradedSectionRingHom i U inferInstance (classOfPow _ n ⟨x, hx⟩)))) =
      polynomialChartGradedHom i V ((conormalPolynomialAlgebra i).res (U := centreSite i V)
          (V := centreSite i U) (i.preimage_mono h)
        (Polynomial.C (Stacks.Conormal.gradedSectionRingHom i U inferInstance
          (classOfPow _ n ⟨x, hx⟩)))) := by
  have hb := Stacks.Conormal.map_mem_chartIdeal_pow i h n hx
  have hres : (conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
          (i.preimage_mono h)
      (Polynomial.C (Stacks.Conormal.gradedSectionRingHom i U inferInstance
        (classOfPow _ n ⟨x, hx⟩))) =
      Polynomial.C (Stacks.Conormal.gradedSectionRingHom i V inferInstance
        (classOfPow _ n ⟨_, hb⟩)) := by
    rw [Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.polynomial_res_apply, Polynomial.map_C]
    exact congrArg Polynomial.C
      (Stacks.Conormal.gradedSectionRingHom_restrict_classOfPow i U _ V _ h n ⟨x, hx⟩)
  rw [hres, polynomialChartGradedHom_apply, polynomialChartGradedHom_apply,
    (RingEquiv.symm_apply_eq _).2 (polynomialChartRingEquiv_tmul_C_pow i n hx).symm,
    (RingEquiv.symm_apply_eq _).2 (polynomialChartRingEquiv_tmul_C_pow i n hb).symm]
  exact centreChartRestrict_tmul_monomial i h n (infinityChartSectionsEquiv_C_mem_pow i hx)
    (infinityChartSectionsEquiv_C_mem_pow i hb)
    ((lineChartRestrict_infinityChartSectionsEquiv U h _).trans (by rw [Polynomial.map_C]))

/-- The identification of the charts is compatible with restriction, on the variable `S`. -/
theorem centreChartRestrict_polynomialChartGradedHom_X (h : V.1 ≤ U.1) :
    centreChartRestrict i h (polynomialChartGradedHom i U (Polynomial.X :
        Polynomial ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1)))) =
      polynomialChartGradedHom i V ((conormalPolynomialAlgebra i).res (U := centreSite i V)
          (V := centreSite i U) (i.preimage_mono h)
        (Polynomial.X : Polynomial
          ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1)))) := by
  have h1 : (polynomialChartRingEquiv i U).symm Polynomial.X =
      (1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U) :=
    (RingEquiv.symm_apply_eq _).2 (polynomialChartRingEquiv_tmul_X i (U := U)).symm
  have h2 : (polynomialChartRingEquiv i V).symm Polynomial.X =
      (1 : Γ(Z, i ⁻¹ᵁ V.1)) ⊗ₜ
        Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i V) :=
    (RingEquiv.symm_apply_eq _).2 (polynomialChartRingEquiv_tmul_X i (U := V)).symm
  have h3 : (conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
      (i.preimage_mono h) (Polynomial.X :
        Polynomial ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1))) =
      Polynomial.X :=
    Polynomial.map_X _
  rw [h3, polynomialChartGradedHom_apply, polynomialChartGradedHom_apply, h1, h2]
  exact centreChartRestrict_tmul_reesDegOne i U h _ _
    ((lineChartRestrict_infinityChartSectionsEquiv U h _).trans (by rw [Polynomial.map_X]))

/-- **The identification of the charts is compatible with restriction.** -/
theorem centreChartRestrict_comp_polynomialChartGradedHom (h : V.1 ≤ U.1) :
    (centreChartRestrict i h).comp (polynomialChartGradedHom i U) =
      (polynomialChartGradedHom i V).comp
        ((conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
          (i.preimage_mono h)) := by
  let f : Polynomial ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1)) →+*
      centreChartRing i V :=
    (centreChartRestrict i h).toRingHom.comp (polynomialChartGradedHom i U).toRingHom
  let g : Polynomial ((Stacks.Conormal.conormalSheafGradedAlgebra i).sectionRing (i ⁻¹ᵁ U.1)) →+*
      centreChartRing i V :=
    (polynomialChartGradedHom i V).toRingHom.comp
      ((conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
          (i.preimage_mono h)).toRingHom
  have key : f = g := by
    refine Polynomial.ringHom_ext (fun a => ?_) (centreChartRestrict_polynomialChartGradedHom_X i h)
    obtain ⟨z, rfl⟩ := (Stacks.Conormal.bijective_gradedSectionRingHom i U inferInstance).2 a
    induction z using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ a =>
        exact centreChartRestrict_polynomialChartGradedHom_C i h n (x := (a : Γ(X, U.1)))
          (by simpa using a.2)
  exact GradedRingHom.ext fun p => RingHom.congr_fun key p

/-- The irrelevant-ideal hypothesis of `Proj.map` for the restriction maps of
`𝒞_{Z/X,*}[S]`. -/
theorem irrelevant_le_map_conormalPolynomialAlgebra_res (h : V.1 ≤ U.1) :
    HomogeneousIdeal.irrelevant ((conormalPolynomialAlgebra i).grading (centreSite i V)) ≤
      (HomogeneousIdeal.irrelevant
        ((conormalPolynomialAlgebra i).grading (centreSite i U))).map
        ((conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
          (i.preimage_mono h)) :=
  Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
    (conormalPolynomialAlgebra i) (U := centreSite i V) (V := centreSite i U)
    (i.preimage_mono h)

/-- The identifications `Proj B_U ≅ Proj Γ(Z ∩ U, 𝒞_{Z/X,*})[S]` are compatible with
restriction. -/
theorem exceptionalProjChartRestrict_polynomialChartProjInv (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ polynomialChartProjInv i U =
      polynomialChartProjInv i V ≫
        Proj.map ((conormalPolynomialAlgebra i).res (U := centreSite i V) (V := centreSite i U)
          (i.preimage_mono h))
          (irrelevant_le_map_conormalPolynomialAlgebra_res i h) :=
  AlgebraicGeometry.Proj.map_comp_map_eq _ _ _ _ _ _ _ _
    (centreChartRestrict_comp_polynomialChartGradedHom i h)

/-- The charts of `Proj_Z(𝒞_{Z/X,*}[S])` with sources the charts of `E` are compatible with
restriction. -/
theorem exceptionalProjChartRestrict_polynomialGluingChart (h : V.1 ≤ U.1) :
    exceptionalProjChartRestrict i h ≫ polynomialGluingChart i U = polynomialGluingChart i V := by
  have hdom := Stacks.AlgebraicGeometry.RelativeProjGeneral.mapDomain_res_eq_top_of_le_opens
    (conormalPolynomialAlgebra i) (U := centreSite i V) (V := centreSite i U) (i.preimage_mono h)
  have e2 := Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_chart_of_le_opens
    (conormalPolynomialAlgebra i) (U := centreSite i V) (V := centreSite i U) (i.preimage_mono h)
    hdom
  rw [Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens] at e2
  rw [polynomialGluingChart, ← Category.assoc, exceptionalProjChartRestrict_polynomialChartProjInv,
    Category.assoc]
  exact congrArg (polynomialChartProjInv i V ≫ ·) e2

/-- `Proj_Z(𝒞_{Z/X,*}[S])` as a solution of the gluing problem of `E`. -/
abbrev polynomialGluing : (exceptionalBasisGluingData i).Gluing where
  base := conormalPolynomialProj i
  toBase := conormalPolynomialProjToBase i ≫ i
  chart := polynomialGluingChart i
  isPullback_chart := isPullback_polynomialGluingChart i
  res_comp_chart h := exceptionalProjChartRestrict_polynomialGluingChart i h

end Gluing

/-! ### Assertion (5) -/

/-- **Stacks 0FBG, assertion (5).** `E = Proj_Z(𝒞_{Z/X,*}[S])`, with `S` a variable placed in
degree one: the exceptional divisor of the blowup of `𝐏¹_X` in `∞(Z)` is the relative `Proj` over
`Z` of the conormal algebra of `Z` in `X` with a degree-one variable adjoined. -/
@[stacks 0FBG "(5): E = Proj_Z(C_{Z/X,*}[S]), S a variable of degree one"]
def exceptionalDivisorIsoConormalPolynomialProj :
    (exceptionalIdealAtInfinity i.ker).subscheme ≅ conormalPolynomialProj i :=
  (exceptionalGluing i).isoOfGluing X.isBasis_affineOpens (polynomialGluing i)

/-- On the chart `Proj B_U` of `E`, the isomorphism `E ≅ Proj_Z(𝒞_{Z/X,*}[S])` is the chart of
`Proj_Z(𝒞_{Z/X,*}[S])` over `Z ∩ U`. -/
@[reassoc]
theorem exceptionalProjChart_exceptionalDivisorIsoConormalPolynomialProj_hom (U : X.affineOpens) :
    exceptionalProjChart i U ≫ (exceptionalDivisorIsoConormalPolynomialProj i).hom =
      polynomialGluingChart i U :=
  (exceptionalGluing i).chart_comp_desc X.isBasis_affineOpens (polynomialGluing i) U

/-- **Stacks 0FBG, assertion (5), over `Z`.** The isomorphism `E ≅ Proj_Z(𝒞_{Z/X,*}[S])` carries
the projection `E ⟶ Z` to the projection of the relative `Proj`. -/
@[stacks 0FBG "(5): the identification E = Proj_Z(C_{Z/X,*}[S]) is over Z"]
theorem exceptionalDivisorIsoConormalPolynomialProj_hom_toBase :
    (exceptionalDivisorIsoConormalPolynomialProj i).hom ≫ conormalPolynomialProjToBase i =
      exceptionalDivisorToCentre i := by
  rw [← cancel_mono i, Category.assoc]
  exact (exceptionalGluing i).desc_comp_toBase X.isBasis_affineOpens (polynomialGluing i)

end Stacks.Chow

end
