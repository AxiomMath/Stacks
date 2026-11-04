module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistStandardOpenSum

/-!
# Multiplying twists over a standard open

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `f ∈ 𝒜 d` be homogeneous of
positive degree. Over the standard open `D₊(f)` a section of the twisting sheaf `𝒪_P(i)` is a
single fraction `a / fⁿ` with `a` homogeneous of degree `n d + i`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`. This file
shows that the product of twists `Stacks.AlgebraicGeometry.ProjConeTwist.twistMulSection`
multiplies those fractions, and that the local degreewise inclusion
`Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L)` of `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp`
is multiplicative.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.natTwistMulSection`: the product of a local section of
  `𝒪_P(i)` and one of `𝒪_P(j)`, for natural numbers `i` and `j`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleToFiber_mul`: for the regular module the
  comparison `A[1/f] → A_x` with a fibre is multiplicative.
* `Stacks.AlgebraicGeometry.ProjConeTwist.mul_mem_degreeZeroLocalization_twistGrading`: the
  product of a degree-zero fraction of `A(i)` and one of `A(j)` is one of `A(i + j)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coe_associatedModuleSheafStandardOpenEquiv_twistMul`:
  the standard-open identification carries the product of two twists to the product of their
  fractions.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coe_sectionsTwistEquivAwayGrading_mul`: the same for
  `Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistAwayHom_mul` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_mul`: the local degreewise inclusion is
  multiplicative, in `(B[1/ψ f])₀` and on sections respectively.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- For the regular module, the comparison `moduleToFiber` of `A[1/f]` with the fibre at a point
of `D₊(f)` is multiplicative. -/
theorem moduleToFiber_mul (f : S) (x : ProjectiveSpectrum.basicOpen 𝒜 f)
    (a b : LocalizedModule.Away (R := S) f S) :
    moduleToFiber (M := S) 𝒜 f x (a * b) =
      moduleToFiber (M := S) 𝒜 f x a * moduleToFiber (M := S) 𝒜 f x b := by
  induction a using LocalizedModule.induction_on with
  | _ a s =>
    induction b using LocalizedModule.induction_on with
    | _ b t =>
      have hmul : (LocalizedModule.mk a s * LocalizedModule.mk b t :
            LocalizedModule.Away (R := S) f S) =
          LocalizedModule.mk (a * b) (s * t) := LocalizedModule.mk_mul_mk
      have hfib : moduleToFiber (M := S) 𝒜 f x (LocalizedModule.mk a s) *
            moduleToFiber (M := S) 𝒜 f x (LocalizedModule.mk b t) =
          LocalizedModule.mk (a * b)
            ((⟨(s : S), (Submonoid.powers_le.mpr x.2) s.2⟩ *
                ⟨(t : S), (Submonoid.powers_le.mpr x.2) t.2⟩ :
              x.1.asHomogeneousIdeal.toIdeal.primeCompl)) := by
        rw [moduleToFiber_mk, moduleToFiber_mk]
        exact LocalizedModule.mk_mul_mk
      rw [hmul, moduleToFiber_mk]
      exact hfib.symm

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

section General

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-! ### The product of two degree-zero fractions -/

/-- The product of a homogeneous element of degree `e` of the grading shifted by `i` and one of
degree `e'` of the grading shifted by `j` is homogeneous of degree `e + e'` of the grading
shifted by `i + j`. -/
theorem mul_mem_twistGrading {i j e e' : ℤ} {a b : A}
    (ha : a ∈ twistGrading (S := A) 𝒜 i e) (hb : b ∈ twistGrading (S := A) 𝒜 j e') :
    a * b ∈ twistGrading (S := A) 𝒜 (i + j) (e + e') := by
  by_cases hi : 0 ≤ e + i
  · by_cases hj : 0 ≤ e' + j
    · exact mem_twistGrading_of_mem 𝒜 (d := (e + i).toNat + (e' + j).toNat) (by omega)
        (SetLike.mul_mem_graded (mem_of_mem_twistGrading 𝒜 hi ha)
          (mem_of_mem_twistGrading 𝒜 hj hb))
    · rw [eq_zero_of_mem_twistGrading 𝒜 (by omega) hb, mul_zero]
      exact zero_mem _
  · rw [eq_zero_of_mem_twistGrading 𝒜 (by omega) ha, zero_mul]
    exact zero_mem _

/-- The product of a degree-zero fraction of the shifted module `A(i)` and one of `A(j)` is a
degree-zero fraction of `A(i + j)`. -/
theorem mul_mem_degreeZeroLocalization_twistGrading {d : ℕ} (hf : f ∈ 𝒜 d) (i j : ℤ)
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 i) f)
    (w : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 j) f) :
    ((z : LocalizedModule.Away f A) * (w : LocalizedModule.Away f A)) ∈
      GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 (i + j)) f := by
  obtain ⟨n, x, hx, hz⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒜
      (twistGrading (S := A) 𝒜 i) hf z
  obtain ⟨m, y, hy, hw⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒜
      (twistGrading (S := A) 𝒜 j) hf w
  have hden : (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) * ⟨f ^ m, ⟨m, rfl⟩⟩ =
      ⟨f ^ (n + m), ⟨n + m, rfl⟩⟩ := Subtype.ext (pow_add f n m).symm
  have hdeg : ((((n + m) * d : ℕ)) : ℤ) = (((n * d : ℕ)) : ℤ) + (((m * d : ℕ)) : ℤ) := by
    push_cast
    ring
  have hgoal : (z : LocalizedModule.Away f A) * (w : LocalizedModule.Away f A) =
      LocalizedModule.mk (x * y) (⟨f ^ (n + m), ⟨n + m, rfl⟩⟩ : Submonoid.powers f) := by
    rw [hz, hw]
    exact LocalizedModule.mk_mul_mk.trans (congrArg (LocalizedModule.mk (x * y)) hden)
  rw [hgoal]
  refine Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒜
    (twistGrading (S := A) 𝒜 (i + j)) hf (n + m) (x * y) ?_
  rw [hdeg]
  exact mul_mem_twistGrading 𝒜 hx hy

/-! ### The standard-open identification is multiplicative -/

/-- The standard-open identification `Γ(D₊(f), 𝒪_P(i)) = (A[1/f])_i` carries the product of two
twists to the product of their fractions. -/
@[stacks 0EKG "the standard-open identification of the sections of a twisting sheaf with the \
degree-zero fractions carries the product of two twists to the product of the fractions"]
theorem coe_associatedModuleSheafStandardOpenEquiv_twistMul {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 (i + j)) hf hd
          (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) :
        LocalizedModule.Away f A)) =
      (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 i) hf hd x :
          LocalizedModule.Away f A) *
        (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 j) hf hd y :
          LocalizedModule.Away f A) := by
  set a := associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 i) hf hd x
  set b := associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 j) hf hd y
  have hfib (k : ℤ) (z : (twistingSheaf 𝒜 k).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
      (p : ProjectiveSpectrum.basicOpen 𝒜 f) :
      moduleToFiber (M := A) 𝒜 f p
          (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 k) hf hd z :
            LocalizedModule.Away f A) = z.1 p :=
    congrArg (fun s : (twistingSheaf 𝒜 k).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) =>
        s.1 p)
      (degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜
        (twistGrading (S := A) 𝒜 k) hf hd z)
  have hmem := mul_mem_degreeZeroLocalization_twistGrading 𝒜 hf i j a b
  have key : degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 (i + j)) f
        ⟨(a : LocalizedModule.Away f A) * (b : LocalizedModule.Away f A), hmem⟩ =
      twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y := by
    refine twistSection_ext 𝒜 fun p => ?_
    show moduleToFiber (M := A) 𝒜 f p
        ((a : LocalizedModule.Away f A) * (b : LocalizedModule.Away f A)) = x.1 p * y.1 p
    rw [← hfib i x p, ← hfib j y p]
    exact moduleToFiber_mul 𝒜 f p _ _
  have hinj : associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 (i + j)) hf hd
        (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) =
      ⟨(a : LocalizedModule.Away f A) * (b : LocalizedModule.Away f A), hmem⟩ :=
    degreeZeroToSection_injective 𝒜 (twistGrading (S := A) 𝒜 (i + j)) hf hd
      ((degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜
        (twistGrading (S := A) 𝒜 (i + j)) hf hd _).trans key.symm)
  exact congrArg Subtype.val hinj

/-- The identification of the sections of `𝒪_P(i)` over `D₊(f)` with the degree-`i` part of
`A[1/f]` is multiplicative. -/
@[stacks 0EKG "the identification of the sections of a twisting sheaf over a standard open with \
a homogeneous part of the localization is multiplicative"]
theorem coe_sectionsTwistEquivAwayGrading_mul {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (i + j)
          (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) :
        LocalizedModule.Away f A)) =
      (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd i x :
          LocalizedModule.Away f A) *
        (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd j y :
          LocalizedModule.Away f A) :=
  coe_associatedModuleSheafStandardOpenEquiv_twistMul 𝒜 hf hd i j x y

/-! ### The product of two twists in natural-number degrees -/

/-- The product `Stacks.AlgebraicGeometry.ProjConeTwist.twistMulSection` of a local section of
`𝒪_P(i)` and one of `𝒪_P(j)` for `i` and `j` natural numbers, as a local section of
`𝒪_P(i + j)` with the degree again a natural number. -/
def natTwistMulSection (i j : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 (i : ℤ)).val.obj U)
    (b : (twistingSheaf 𝒜 (j : ℤ)).val.obj U) :
    (twistingSheaf 𝒜 ((i + j : ℕ) : ℤ)).val.obj U :=
  twistMulSection 𝒜 (i : ℤ) (j : ℤ) U a b

/-- The value of `natTwistMulSection 𝒜 i j U a b` at a point is the product of the values of `a`
and `b`. -/
@[simp] theorem natTwistMulSection_val (i j : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 (i : ℤ)).val.obj U)
    (b : (twistingSheaf 𝒜 (j : ℤ)).val.obj U) (x : U.unop) :
    (natTwistMulSection 𝒜 i j U a b).1 x = a.1 x * b.1 x := rfl

/-- The identification of the sections of a twisting sheaf over a standard open with a
homogeneous part of `A[1/f]` is multiplicative, in natural-number degrees. -/
theorem coe_sectionsTwistEquivAwayGrading_natMul {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℕ)
    (x : (twistingSheaf 𝒜 (i : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 (j : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd ((i + j : ℕ) : ℤ)
          (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) :
        LocalizedModule.Away f A)) =
      (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (i : ℤ) x :
          LocalizedModule.Away f A) *
        (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (j : ℤ) y :
          LocalizedModule.Away f A) :=
  coe_sectionsTwistEquivAwayGrading_mul 𝒜 hf hd (i : ℤ) (j : ℤ) x y

end General

section Cone

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-! ### The local degreewise inclusion is multiplicative -/

/-- The degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/ψ f])₀` is multiplicative: the product
of a section of `𝒪_P(i)` and one of `𝒪_P(j)` goes to the product of their images. -/
@[stacks 0EKG "the degreewise inclusion of the sections of the twisting sheaves over D+(f) into \
the degree-zero localization of the truncation algebra is multiplicative"]
theorem coneTwistAwayHom_mul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℕ)
    (x : (twistingSheaf 𝒜 (i : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 (j : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    coneTwistAwayHom 𝒜 (i + j) d hf hd
        (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) =
      coneTwistAwayHom 𝒜 i d hf hd x * coneTwistAwayHom 𝒜 j d hf hd y := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  have h1 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd (i + j)
    (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)
  have h2 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd i x
  have h3 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd j y
  have h4 := coe_sectionsTwistEquivAwayGrading_natMul 𝒜 hf hd i j x y
  exact (h1.trans (h4.trans (congrArg₂ (· * ·) h2.symm h3.symm))).trans (map_mul _ _ _).symm

/-- The local degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L)` is
multiplicative. -/
@[stacks 0EKG "the local degreewise inclusion of the sections of O_P(m) into the functions on \
the cone over D+(f) is multiplicative, for the truncation cone"]
theorem coneTwistApp_mul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℕ)
    (x : (twistingSheaf 𝒜 (i : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 (j : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (show (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj
          (op (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) from
        (coneTwistApp 𝒜 (i + j) d hf hd).hom
          (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)) =
      (show (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj
            (op (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) from
          (coneTwistApp 𝒜 i d hf hd).hom x) *
        (show (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj
            (op (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) from
          (coneTwistApp 𝒜 j d hf hd).hom y) := by
  have h0 := coneTwistApp_apply 𝒜 (i + j) d hf hd
    (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)
  have h1 := coneTwistApp_apply 𝒜 i d hf hd x
  have h2 := coneTwistApp_apply 𝒜 j d hf hd y
  have h3 := coneTwistAwayHom_mul 𝒜 d hf hd i j x y
  rw [h0, h1, h2, h3, map_mul, map_mul]

end Cone

end Stacks.AlgebraicGeometry.ProjConeTwist

end
