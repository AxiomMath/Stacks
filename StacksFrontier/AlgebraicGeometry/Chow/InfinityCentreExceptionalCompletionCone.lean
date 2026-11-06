module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletion
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapClosedImmersionOfSurjection

/-!
# The normal cone inside the projective completion of the normal bundle

Let `i : Z ⟶ X` be a regular closed immersion, `b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in the centre
`∞(Z)` and `E ⊆ W` its exceptional divisor. Write `𝒩` for the normal bundle of `i` and
`𝒞 = 𝒩^∨` for the conormal sheaf, so that `N = 𝐕(𝒞)` is the total space of `𝒩` and
`P = 𝐏(𝒞 ⊕ 𝒪_Z)` its projective completion. Two embeddings of the normal cone `C_ZX` are in
play in the proof of Stacks 0FEG:

* the open immersion `C_ZX ⟶ E` of Stacks 0FBH, followed by the isomorphism `E ≅ P`;
* the closed immersion `C_ZX ⟶ N` of the normal bundle, followed by the open immersion `N ⟶ P`
  of the vector bundle into its projective completion.

This file proves that they agree. Over an affine open `U = Spec A` of `X`, with `I` the ideal of
`Z ∩ U` and `J = (I, s) ⊆ A[s]`, both are computed on the chart `D₊(S) = Spec A[s][J/s]` of `W`:
the first is `Spec` of the quotient `A[s][J/s] ⟶ A[s][J/s]/(s) = Gr_I(A)`, the second sends the
generator `x/s`, `x ∈ I`, of the chart of `P` at `T` to the class of `x` in `I/I²`. Both send `x/s`
to the class of `x` and `a ∈ A` to its class in `A/I`, so they agree.

## Main results

* `Stacks.Chow.normalConeToExceptionalDivisor_comp_exceptionalDivisorIsoProjectiveCompletion_hom`:
  **`C_ZX ⟶ E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`.**
* `Stacks.Chow.blowupAtInfinityChartS_eq_awayι`: the chart `D₊(S) = Spec A[s][J/s]` of `W` is the
  standard open `D₊(s t)` of the Rees chart `Proj Γ(V)[𝒥(V) t]` of `W` over the chart at infinity
  `V` of `𝐏¹_X`.
* `Stacks.RelativeSpec.chart_relativeSpectrumMapOfAlgebraHom`: on the chart over an affine open,
  the morphism of relative spectra induced by a map of algebras is `Spec` of that map on sections.
* `Stacks.Blowup.reesAway_ringHom_ext`: ring maps out of the chart `(R[It])_{(a⁽¹⁾)} = R[I/a]` are
  determined on `R` and on the fractions `x / a`, `x ∈ I`.

## Implementation notes

Both morphisms are compared after composing with the closed immersion `E ⟶ W` (through
`E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`), chart by chart of `C_ZX` over the affine opens `U` of `X`. On each chart both
factor through the open immersion `D₊(s t) ⟶ Proj Γ(V)[𝒥(V) t] ⟶ W`, so the comparison is one of
two ring maps `Γ(V)[𝒥(V) t]_{(s t)} ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})`, which is checked on the generators
`a / (s t)⁰` and `x t / s t` of `Γ(V)[𝒥(V) t]_{(s t)} = A[s][J/s]`. The chart `D₊(S)` of
`Stacks.Chow.normalConeToExceptionalDivisor` is identified with `D₊(s t)` by the universal property
of the blowup.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AssociatedGraded Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SymmetricAway
open scoped Stacks.ProjectiveCompletion

universe u

/-! ### Morphisms of relative spectra on charts -/

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B)

/-- **On the chart over an affine open `U` of the base, the morphism of relative spectra induced
by `ψ` is the spectrum of `ψ` on the sections over `U`.** -/
@[reassoc]
theorem chart_relativeSpectrumMapOfAlgebraHom (U : s.base.affineOpens) :
    (gluedSpectrum (s.withAlgebra B hB)).chart U ≫ relativeSpectrumMapOfAlgebraHom s B hB ψ =
      Spec.map (ψ.right.hom.app (op U.1)) ≫ (gluedSpectrum s).chart U := by
  have h1 := ι_relativeSpectrumMapOfAlgebraHom s B hB ψ U
  have hinv : ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map ((universalAlgebraMap (s.withAlgebra B hB)).right.app (.op U.1)) =
      ((gluedSpectrum (s.withAlgebra B hB)).chartIsoPreimage U).inv :=
    toSpecΓ_specMap_eq _ _ _ (universalAlgebraMap_app_comp_topIso_inv (s.withAlgebra B hB) U)
  rw [← (gluedSpectrum (s.withAlgebra B hB)).chartIsoPreimage_hom_ι U, Category.assoc, h1,
    Spec.map_comp, Category.assoc, reassoc_of% hinv, Iso.hom_inv_id_assoc]

end Stacks.RelativeSpec

/-! ### Ring maps out of the standard chart of `Proj` of a Rees algebra -/

namespace Stacks.Blowup

open HomogeneousLocalization

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) (ha : a ∈ I)

/-- The fraction `r / aⁿ` of the chart, read in `R_a` through `1/a`. -/
theorem reesAwayToAway_reesAwayMk_eq (n : ℕ) (r : (I ^ n : Ideal R)) :
    reesAwayToAway I a ha (reesAwayMk I a ha n r) =
      algebraMap R (Localization.Away a) r * IsLocalization.Away.invSelf a ^ n := by
  rw [reesAwayToAway_reesAwayMk, mk_eq_algebraMap_mul_invSelf_pow]

/-- **A degree-one fraction `j / a` with `j = x + y a` splits as `x / a + y`.** -/
theorem reesAwayMk_one_eq_add {j x y : R} (hj : j ∈ I ^ 1) (hx : x ∈ I ^ 1)
    (h : j = x + y * a) :
    reesAwayMk I a ha 1 ⟨j, hj⟩ =
      reesAwayMk I a ha 1 ⟨x, hx⟩ + reesAwayMk I a ha 0 ⟨y, by simp⟩ := by
  refine reesAwayToAway_injective I a ha ?_
  rw [map_add, reesAwayToAway_reesAwayMk_eq, reesAwayToAway_reesAwayMk_eq,
    reesAwayToAway_reesAwayMk_eq]
  have hu := IsLocalization.Away.mul_invSelf (S := Localization.Away a) a
  simp only [h, map_add, map_mul, pow_one, pow_zero, mul_one]
  linear_combination (algebraMap R (Localization.Away a) y) * hu

/-- A fraction `r / a⁰` of the chart is the image of `r` in degree zero. -/
theorem reesAwayMk_zero_eq_fromZeroRingHom (r : R) (hr : r ∈ I ^ 0) :
    reesAwayMk I a ha 0 ⟨r, hr⟩ =
      fromZeroRingHom (reesGrading I) (Submonoid.powers (reesDegOne I ha))
        (algebraMap R (reesGrading I 0) r) := by
  rw [fromZeroRingHom_eq_reesAwayMk]
  congr 2
  simp [SetLike.GradeZero.coe_algebraMap]

/-- `(j / a) · (a / a⁰) = j / a⁰` in the chart. -/
theorem reesAwayMk_one_mul_self (j : (I ^ 1 : Ideal R)) :
    reesAwayMk I a ha 1 j * reesAwayMk I a ha 0 ⟨a, by simp⟩ =
      reesAwayMk I a ha 0 ⟨j, by simp⟩ := by
  refine reesAwayToAway_injective I a ha ?_
  rw [map_mul, reesAwayToAway_reesAwayMk_eq, reesAwayToAway_reesAwayMk_eq,
    reesAwayToAway_reesAwayMk_eq]
  have hu := IsLocalization.Away.mul_invSelf (S := Localization.Away a) a
  simp only [pow_one, pow_zero, mul_one]
  linear_combination (algebraMap R (Localization.Away a) j) * hu

/-- **Ring maps out of the chart `(R[It])_{(a⁽¹⁾)}` are determined by the fractions `r / a⁰`,
`r ∈ R`, and `x / a`, `x ∈ I`**: the chart is the affine blowup algebra `R[I/a]`, which is
generated over `R` by the fractions `x / a`. -/
theorem reesAway_ringHom_ext {T : Type*} [CommRing T]
    {f g : Away (reesGrading I) (reesDegOne I ha) →+* T}
    (h0 : ∀ r : (I ^ 0 : Ideal R), f (reesAwayMk I a ha 0 r) = g (reesAwayMk I a ha 0 r))
    (h1 : ∀ r : (I ^ 1 : Ideal R), f (reesAwayMk I a ha 1 r) = g (reesAwayMk I a ha 1 r)) :
    f = g := by
  set E := reesAwayEquivAffineBlowup I a ha
  suffices key : ∀ w : affineBlowup I a, f (E.symm w) = g (E.symm w) by
    ext z
    simpa using key (E z)
  rintro ⟨w, hw⟩
  change w ∈ Algebra.adjoin R (affineBlowupGenSet I a) at hw
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y ∈ I ^ 1 := by simpa using hy
    have e : E.symm ⟨_, Algebra.subset_adjoin ⟨y, hy, rfl⟩⟩ = reesAwayMk I a ha 1 ⟨y, hy1⟩ := by
      refine E.symm_apply_eq.2 (Subtype.ext ?_)
      refine Eq.trans ?_ (coe_reesAwayEquivAffineBlowup_reesAwayMk I a ha 1 ⟨y, hy1⟩).symm
      exact congrArg (Localization.mk y) (Subtype.ext (pow_one a).symm)
    rw [e]
    exact h1 _
  | algebraMap r =>
    have e : E.symm ⟨_, Subalgebra.algebraMap_mem _ r⟩ = reesAwayMk I a ha 0 ⟨r, by simp⟩ := by
      refine E.symm_apply_eq.2 (Subtype.ext ?_)
      refine Eq.trans ?_ (coe_reesAwayEquivAffineBlowup_reesAwayMk I a ha 0 ⟨r, by simp⟩).symm
      show algebraMap R (Localization.Away a) r =
        Localization.mk r (⟨a ^ 0, 0, rfl⟩ : Submonoid.powers a)
      rw [← Localization.mk_one_eq_algebraMap]
      exact congrArg (Localization.mk r) (Subtype.ext (pow_zero a).symm)
    rw [e]
    exact h0 _
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, add_mem hx hy⟩ : affineBlowup I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, mul_mem hx hy⟩ : affineBlowup I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, ihx, ihy]

end Stacks.Blowup

namespace Stacks.Chow

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

attribute [local instance] VirtualNormalBundle.isFiniteLocallyFree_dualSheaf

/-! ### The chart `D₊(S)` of `W` as a Rees chart -/

section ReesChartS

variable (U : X.affineOpens)

/-- The degree-one element `s t` of the Rees algebra `Γ(V)[𝒥(V) t]` of the centre over the chart
at infinity `V` over `U`. -/
abbrev infinityReesCoordinate : reesAlgebra ((infinityCentreIdeal i.ker).ideal
    (infinityChartAffineOpen U)) :=
  Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_X_mem i U)

/-- `s t` has degree one. -/
theorem infinityReesCoordinate_mem : infinityReesCoordinate i U ∈ centreReesGrading i U 1 :=
  Stacks.Blowup.reesDegOne_mem_reesGrading _ _

/-- The degree-one element `1 ⊗ s t` of `B = Γ(Z ∩ U) ⊗_{Γ(V)} Γ(V)[𝒥(V) t]`. -/
abbrev centreChartCoordinate : centreChartRing i U :=
  (1 : Γ(Z, i ⁻¹ᵁ U.1)) ⊗ₜ infinityReesCoordinate i U

/-- `1 ⊗ s t` has degree one. -/
theorem centreChartCoordinate_mem : centreChartCoordinate i U ∈ centreChartGrading i U 1 :=
  Submodule.tmul_mem_baseChange_of_mem _ (infinityReesCoordinate_mem i U)

/-- `1 ⊗ s t` is the image of `s t` in `B`. -/
theorem includeRight_infinityReesCoordinate :
    Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)
      (infinityReesCoordinate i U) = centreChartCoordinate i U :=
  rfl

/-- **The chart `Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s]`**: the standard open `D₊(s t)` of `Proj` of the
Rees algebra of the centre over the chart at infinity is the affine blowup algebra `A[s][J/s]`,
`J = (I, s)` (Stacks 0804). -/
def infinityReesAwayEquiv :
    HomogeneousLocalization.Away (centreReesGrading i U) (infinityReesCoordinate i U) ≃+*
      infinityChartAlgebra (i.ker.ideal U) :=
  (Stacks.Blowup.reesAwayEquivAffineBlowup _ _ (infinityChartSectionsEquiv_X_mem i U)).trans
    ((Subalgebra.equivOfEq _ _ (affineBlowup_eq_affineBlowupAlgebra _ _)).toRingEquiv.trans
      (infinityChartRingEquiv i.ker U Polynomial.X (X_mem_infinityChartIdeal _)).symm)

/-- `Γ(X, U)[s] ≅ Γ(𝐏¹_X, V) ⟶ Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s]` is the structure map. -/
theorem infinityReesAwayEquiv_structure :
    (infinityChartSectionsIso U).hom ≫ CommRingCat.ofHom (algebraMap
        Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) ↥(centreReesGrading i U 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (centreReesGrading i U)
        (Submonoid.powers (infinityReesCoordinate i U))) ≫
      CommRingCat.ofHom (infinityReesAwayEquiv i U).toRingHom =
    CommRingCat.ofHom
      (algebraMap (Polynomial Γ(X, U.1)) (infinityChartAlgebra (i.ker.ideal U))) := by
  have h := Stacks.Blowup.reesBase_fromZeroRingHom_reesAwayEquivAffineBlowup
    (infinityCentreIdeal i.ker) (infinityChartAffineOpen U) (infinityChartSectionsEquiv_X_mem i U)
  refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
  have hp := congrArg (fun φ => CommRingCat.Hom.hom φ (infinityChartSectionsEquiv U p)) h
  show (infinityChartRingEquiv i.ker U Polynomial.X (X_mem_infinityChartIdeal _)).symm
    (Subalgebra.equivOfEq _ _ (affineBlowup_eq_affineBlowupAlgebra _ _)
      (Stacks.Blowup.reesAwayEquivAffineBlowup _ _ (infinityChartSectionsEquiv_X_mem i U)
        (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap _ _
          (infinityChartSectionsEquiv U p))))) = _
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hp
  rw [show Stacks.Blowup.reesAwayEquivAffineBlowup _ _ (infinityChartSectionsEquiv_X_mem i U)
      (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap _ _
        (infinityChartSectionsEquiv U p))) = algebraMap _ _ (infinityChartSectionsEquiv U p)
    from hp]
  have h2 : Subalgebra.equivOfEq _ _ (affineBlowup_eq_affineBlowupAlgebra _ _)
      (algebraMap _ _ (infinityChartSectionsEquiv U p)) =
      algebraMap _ (blowUpAffineChartRing (infinityCentreIdeal i.ker) (infinityChartAffineOpen U)
        ⟨infinityChartSectionsEquiv U Polynomial.X,
          infinityChartSectionsEquiv_mem i.ker U _ (X_mem_infinityChartIdeal _)⟩)
        (infinityChartSectionsEquiv U p) := rfl
  rw [h2, infinityChartRingEquiv_symm_algebraMap, RingEquiv.symm_apply_apply]
  rfl

/-- `Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s]` on the image of `e(p)`, for the identification
`e : A[s] ≅ Γ(V)` of the chart at infinity: it is `p`. -/
theorem infinityReesAwayEquiv_fromZeroRingHom (p : Polynomial Γ(X, U.1)) :
    infinityReesAwayEquiv i U (HomogeneousLocalization.fromZeroRingHom (centreReesGrading i U)
        (Submonoid.powers (infinityReesCoordinate i U))
        (algebraMap _ _ (infinityChartSectionsEquiv U p))) =
      algebraMap _ (infinityChartAlgebra (i.ker.ideal U)) p := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ p) (infinityReesAwayEquiv_structure i U)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h

/-- `Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s]` on a fraction `e(p) / (s t)⁰`: it is `p`. -/
theorem infinityReesAwayEquiv_reesAwayMk_zero (p : Polynomial Γ(X, U.1))
    (hp : infinityChartSectionsEquiv U p ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 0) :
    infinityReesAwayEquiv i U (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U)
        0 ⟨_, hp⟩) = algebraMap _ (infinityChartAlgebra (i.ker.ideal U)) p := by
  rw [Stacks.Blowup.reesAwayMk_zero_eq_fromZeroRingHom, infinityReesAwayEquiv_fromZeroRingHom]

/-- **`Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s]` on a degree-one generator**: `e(x) t / s t` goes to
`x / s`, for `x ∈ I`. -/
theorem infinityReesAwayEquiv_reesAwayMk_one_C {x : Γ(X, U.1)} (hx : x ∈ i.ker.ideal U)
    (h : infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 1) :
    infinityReesAwayEquiv i U (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U)
        1 ⟨_, h⟩) = infinityChartMk (i.ker.ideal U) 1 (Polynomial.C x)
          (C_mem_pow_infinityChartIdeal (by simpa using hx)) := by
  have hz := congrArg (infinityReesAwayEquiv i U)
    (Stacks.Blowup.reesAwayMk_one_mul_self _ _ (infinityChartSectionsEquiv_X_mem i U) ⟨_, h⟩)
  rw [map_mul, infinityReesAwayEquiv_reesAwayMk_zero, infinityReesAwayEquiv_reesAwayMk_zero]
    at hz
  refine Subtype.ext ?_
  rw [infinityChartMk_val, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  have hz' := congrArg Subtype.val hz
  simp only [pow_one, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at hz' ⊢
  exact hz'

/-- **The chart `D₊(S)` of `W` over `U` is the standard open `D₊(s t)` of the Rees chart of `W`
over the chart at infinity.** Both lie over the chart at infinity of `𝐏¹_X` by the structure map
of `A[s][J/s]`, and the centre pulls back to an effective Cartier divisor along them, so they agree
by the universal property of the blowup. -/
theorem blowupAtInfinityChartS_eq_awayι :
    blowupAtInfinityChartS i.ker U =
      Spec.map (CommRingCat.ofHom (infinityReesAwayEquiv i U).toRingHom) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos ≫ infinityReesChart i U := by
  have hg : Stacks.Blowup.IsCartierOver (infinityCentreIdeal i.ker)
      (Over.mk (blowupAtInfinityChartS i.ker U ≫ blowupAtInfinityToLine i.ker)) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor
      ((infinityCentreIdeal i.ker).comap
        (blowupAtInfinityChartS i.ker U ≫ blowupAtInfinityToLine i.ker))
    rw [Scheme.IdealSheafData.comap_comp]
    exact isEffectiveCartierDivisor_comap_blowupAtInfinityChartS i.ker U
  have h1 : (Spec.map (CommRingCat.ofHom (infinityReesAwayEquiv i U).toRingHom) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos ≫ infinityReesChart i U) ≫
      blowUpToBase (infinityCentreIdeal i.ker) =
      blowupAtInfinityChartS i.ker U ≫ blowupAtInfinityToLine i.ker := by
    show _ ≫ blowupAtInfinityToLine i.ker = _
    rw [blowupAtInfinityChartS, blowupAtInfinityPolyChart_comp, Category.assoc, Category.assoc,
      (isPullback_infinityReesChart i U).w, ← Category.assoc (Proj.awayι _ _ _ _),
      Proj.awayι_toSpecZero_assoc, ← specMap_infinityChartSectionsIso_infinityChartOver]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      infinityReesAwayEquiv_structure i U]
  exact (blowUpLift_unique _ _ hg _ rfl).trans (blowUpLift_unique _ _ hg _ h1).symm

end ReesChartS

/-! ### The isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` on the chart at `T` -/

section CompletionChart

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

variable (U : X.affineOpens)

/-- **`Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ B` sends `T` to `1 ⊗ s t`**: the section `(0, 1)` of
`𝒞 ⊕ 𝒪_Z` is the class of the coordinate `s` of the chart at infinity. -/
theorem exceptionalChartRingEquiv_infinitySection :
    exceptionalChartRingEquiv i U hi (Stacks.ProjectiveCompletion.infinitySection
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)) =
      centreChartCoordinate i U := by
  set S' := Stacks.ProjectiveCompletion.sectionsSplitting
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)
  have hκ : conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ (S'.p S'.t₀)) =
      classOfPow _ 1 ⟨0, by simp⟩ := by
    rw [S'.p_t₀, map_zero, map_zero]
    exact (map_zero (classOfPow (Stacks.Conormal.chartIdeal i U) 1)).symm
  show exceptionalChartSymEquiv i U hi (Stacks.ProjectiveCompletion.sectionRingEquiv
    (isAffineOpen_centrePreimage i U) (Stacks.ProjectiveCompletion.infinitySection _ _)) = _
  rw [Stacks.ProjectiveCompletion.sectionRingEquiv_infinitySection,
    exceptionalChartSymEquiv_ι_of i U hi _ (zero_mem _) hκ, S'.q_t₀, map_one, one_mul]
  have h0 : Stacks.Blowup.reesDegOne _ (infinityChartSectionsEquiv_C_mem i U
      (zero_mem (Stacks.Conormal.chartIdeal i U))) = 0 :=
    Subtype.ext (by simp [Stacks.Blowup.coe_reesDegOne])
  rw [h0, TensorProduct.tmul_zero, zero_add]

/-- `B ≅ Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` sends `1 ⊗ s t` to `T`. -/
theorem exceptionalChartGradedInv_centreChartCoordinate :
    exceptionalChartGradedInv i U hi (centreChartCoordinate i U) =
      Stacks.ProjectiveCompletion.infinitySection
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1) :=
  (RingEquiv.symm_apply_eq _).2 (exceptionalChartRingEquiv_infinitySection i hi U).symm

/-- `Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ⟶ Proj B ⟶ Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))` is the identity. -/
theorem exceptionalChartProjMap_comp_exceptionalChartProjInv :
    exceptionalChartProjMap i U hi ≫ exceptionalChartProjInv i U hi = 𝟙 _ := by
  rw [exceptionalChartProjMap, exceptionalChartProjInv, ← Proj.map_comp, ← Proj.map_id]
  exact Proj.map_congr (exceptionalChartGradedInv_comp_hom i U hi) _ _

/-- **The chart of `𝐏(𝒞 ⊕ 𝒪_Z)` over `Z ∩ U`, followed by `𝐏(𝒞 ⊕ 𝒪_Z) ≅ E`, is the chart of `E`
over `U`** after `Proj Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z)) ≅ Proj B`. -/
theorem completionChart_exceptionalDivisorIsoProjectiveCompletion_inv :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (completionAlgebra (dualSheaf
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).chart (i ⁻¹ᵁ U.1)
        (isAffineOpen_centrePreimage i U) ≫ (exceptionalDivisorIsoProjectiveCompletion i hi).inv =
      exceptionalChartProjMap i U hi ≫ exceptionalProjChart i U := by
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (exceptionalChartProjMap i U hi ≫ ·)
    (exceptionalProjChart_exceptionalDivisorIsoProjectiveCompletion_hom i hi U)).symm
  exact ((Category.id_comp _).symm.trans (congrArg (· ≫ _)
    (exceptionalChartProjMap_comp_exceptionalChartProjInv i hi U).symm)).trans
    (Category.assoc _ _ _)

end CompletionChart

/-! ### The embedding `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` on charts -/

section NormalBundleSide

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- The ring map `Γ(Z ∩ U, Sym(𝒞)) ⟶ Γ(Z ∩ U, Sym(𝒞_{Z/X})) ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})` of the
embedding `C_ZX ⟶ N` over an affine open `U` of `X`. -/
abbrev normalConeEmbeddingRingHom (U : X.affineOpens) :
    (Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).right.obj.obj
        (op (i ⁻¹ᵁ U.1)) ⟶
      (Stacks.Conormal.conormalAlgebraSheaf i).right.obj.obj (op (i ⁻¹ᵁ U.1)) :=
  (Scheme.Modules.symmetricAlgebraSheafMap Z
      (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection).right.hom.app
      (op (i ⁻¹ᵁ U.1)) ≫
    (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i).right.hom.app (op (i ⁻¹ᵁ U.1))

/-- **`C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` on the chart of `C_ZX` over an affine open `U` of `X`**: it is
`Spec` of `Γ(Z ∩ U, Sym(𝒞)) ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})` followed by the chart of `𝐏(𝒞 ⊕ 𝒪_Z)` at
`T` over `Z ∩ U`. -/
theorem normalConeChart_normalConeEmbedding_toCompletion (U : X.affineOpens) :
    normalConeChart i U ≫ (VirtualNormalBundle.ofIsRegularImmersion i hi).normalConeEmbedding ≫
        Stacks.ProjectiveCompletion.toCompletion
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) =
      Spec.map (normalConeEmbeddingRingHom i hi U) ≫
        Stacks.ProjectiveCompletion.chartToCompletion
          (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
          (isAffineOpen_centrePreimage i U) := by
  have e1 := Stacks.RelativeSpec.chart_relativeSpectrumMapOfAlgebraHom
    (Stacks.Conormal.normalBundleSituation i) (Stacks.Conormal.conormalAlgebraSheaf i)
    (Stacks.Conormal.isQuasicoherent_conormalAlgebraSheaf i)
    (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i) (subschemeAffineOpen i U)
  have e2 := Stacks.RelativeSpec.chart_relativeSpectrumMapOfAlgebraHom
    ⟨Z, Scheme.Modules.symmetricAlgebraSheaf Z
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)⟩
    (Stacks.Conormal.normalBundleAlgebra i) inferInstance
    (Scheme.Modules.symmetricAlgebraSheafMap Z
      (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection)
    (subschemeAffineOpen i U)
  rw [Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq] at e2
  have e2' : (Stacks.RelativeSpec.gluedSpectrum (Stacks.Conormal.normalBundleSituation i)).chart
        (subschemeAffineOpen i U) ≫ (Scheme.Modules.vectorBundleMap Z
          (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection).left =
      Spec.map ((Scheme.Modules.symmetricAlgebraSheafMap Z
          (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection).right.hom.app
          (op (i ⁻¹ᵁ U.1))) ≫
        (Stacks.RelativeSpec.gluedSpectrum ⟨Z, Scheme.Modules.symmetricAlgebraSheaf Z
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)⟩).chart
          (subschemeAffineOpen i U) :=
    (congrArg (fun f => _ ≫ Over.Hom.left f)
      (Scheme.Modules.vectorBundleMap_eq_relativeSpecMapOfAlgebraHom (X := Z)
        (f := (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection))).trans
      e2
  have e1' : normalConeChart i U ≫ Stacks.Conormal.normalConeToNormalBundle i =
      Spec.map ((Stacks.Conormal.conormalSymmetricAlgebraSheafHom i).right.hom.app
        (op (i ⁻¹ᵁ U.1))) ≫
        (Stacks.RelativeSpec.gluedSpectrum (Stacks.Conormal.normalBundleSituation i)).chart
          (subschemeAffineOpen i U) := e1
  have e3 := Stacks.ProjectiveCompletion.ι_toCompletion
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (subschemeAffineOpen i U)
  rw [VirtualNormalBundle.normalConeEmbedding, VirtualNormalBundle.normalBundleEmbedding]
  refine (congrArg (normalConeChart i U ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _ ≫ _) e1').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Spec.map _ ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e2'))).trans ?_
  refine (congrArg (Spec.map _ ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (Spec.map _ ≫ ·) e3))).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Spec.map_comp _ _).symm)

end NormalBundleSide

/-! ### The two ring maps out of `Γ(V)[𝒥(V) t]_{(s t)}` -/

section RingIdentity

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

variable (U : X.affineOpens)

/-- The sections of `C_ZX ⟶ N` over `Z ∩ U` composed with the identification of the symmetric
algebra of the sections are `Sym(Γ(𝒞)) ≅ Gr_I(A) ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})`. -/
theorem normalConeEmbeddingRingHom_symSectionsRingEquiv
    (z : SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.1)
      Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1)) :
    (normalConeEmbeddingRingHom i hi U).hom
        (Stacks.SymAlgSections.symSectionsRingEquiv _ (isAffineOpen_centrePreimage i U) z) =
      Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (conormalSymmetricSectionsEquiv i U hi z) := by
  have := isIso_symmetricAlgebraSheafMap_conormalDegreeOneSurjection i hi
  have := isIso_conormalSymmetricAlgebraSheafHom_of_isRegularImmersion i hi
  show _ = Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
    ((Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance).symm _)
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- Every class `x mod I²`, `x ∈ I`, is the image of a degree-one generator of `Sym(Γ(𝒞))`: the
surjection `𝒞 ⟶ 𝒞_{Z/X}` of the normal bundle is an isomorphism for a regular immersion. -/
theorem exists_conormalSymmetricSectionsEquiv_ι_eq_classOfPow {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U) :
    ∃ m : Γ(dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle, i ⁻¹ᵁ U.1),
      conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _ m) =
        classOfPow _ 1 ⟨x, by simpa using hx⟩ := by
  have := isIso_conormalDegreeOneSurjection_ofIsRegularImmersion i hi
  set σ := (VirtualNormalBundle.ofIsRegularImmersion i hi).conormalDegreeOneSurjection
  set y := (affineSectionsEquiv i U inferInstance).equiv 1
    (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) 1
      ⟨x, by simpa [AssociatedGraded.ring_power_eq] using hx⟩)
  refine ⟨(inv σ).app (i ⁻¹ᵁ U.1) y, ?_⟩
  have hσ : σ.app (i ⁻¹ᵁ U.1) ((inv σ).app (i ⁻¹ᵁ U.1) y) = y := by
    have h := congrArg (fun f => Scheme.Modules.Hom.app f (i ⁻¹ᵁ U.1) y) (IsIso.inv_hom_id σ)
    exact h
  rw [conormalSymmetricSectionsEquiv_ι, hσ, AddEquiv.symm_apply_apply]
  rfl

/-- **The ring map of `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z) ≅ E ⟶ W` on the chart `D₊(s t)`**:
`Γ(V)[𝒥(V) t]_{(s t)} ⟶ B_{(1 ⊗ s t)} ≅ Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))_{(T)} ≅ Γ(Z ∩ U, Sym(𝒞)) ⟶
Γ(Z ∩ U, 𝒞_{Z/X,*})`. -/
def completionChartRingHom :
    HomogeneousLocalization.Away (centreReesGrading i U) (infinityReesCoordinate i U) →+*
      (Stacks.Conormal.conormalAlgebraSheaf i).right.obj.obj (op (i ⁻¹ᵁ U.1)) :=
  (normalConeEmbeddingRingHom i hi U).hom.comp
    ((Stacks.ProjectiveCompletion.chartRingEquiv
      (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
      (isAffineOpen_centrePreimage i U)).symm.toRingHom.comp
    ((HomogeneousLocalization.map (exceptionalChartGradedInv i U hi)
        (Stacks.ProjectiveCompletion.powers_le_comap_powers _
          (exceptionalChartGradedInv_centreChartCoordinate i hi U))).comp
      (HomogeneousLocalization.map (Stacks.ProjBaseChange.includeRight (centreReesGrading i U)
          Γ(Z, i ⁻¹ᵁ U.1))
        (Stacks.ProjectiveCompletion.powers_le_comap_powers _
          (includeRight_infinityReesCoordinate i U)))))

/-- `completionChartRingHom` written out. -/
theorem completionChartRingHom_apply
    (z : HomogeneousLocalization.Away (centreReesGrading i U) (infinityReesCoordinate i U)) :
    completionChartRingHom i hi U z = (normalConeEmbeddingRingHom i hi U).hom
      ((Stacks.ProjectiveCompletion.chartRingEquiv
        (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
        (isAffineOpen_centrePreimage i U)).symm
        (HomogeneousLocalization.map (exceptionalChartGradedInv i U hi)
          (Stacks.ProjectiveCompletion.powers_le_comap_powers _
            (exceptionalChartGradedInv_centreChartCoordinate i hi U))
          (HomogeneousLocalization.map
            (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1))
            (Stacks.ProjectiveCompletion.powers_le_comap_powers _
              (includeRight_infinityReesCoordinate i U)) z))) :=
  rfl

/-- `completionChartRingHom` on a fraction `r tⁿ / (s t)ⁿ`: the dehomogenization of the image of
`1 ⊗ r tⁿ` in `Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))`. -/
theorem completionChartRingHom_reesAwayMk (n : ℕ)
    (r : ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ n : Ideal _)) :
    completionChartRingHom i hi U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) n r) =
      (normalConeEmbeddingRingHom i hi U).hom
        (Stacks.ProjectiveCompletion.sectionsDehomogenize (isAffineOpen_centrePreimage i U)
          (exceptionalChartGradedInv i U hi
            (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)
              (Stacks.Blowup.reesMonomial _ n r : reesAlgebra _)))) := by
  have hmem : (Stacks.Blowup.reesMonomial _ n r : reesAlgebra _) ∈
      centreReesGrading i U (n • 1) := by
    rw [smul_eq_mul, mul_one]; exact (Stacks.Blowup.reesMonomial _ n r).2
  have e0 : Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) n r =
      HomogeneousLocalization.Away.mk (centreReesGrading i U) (infinityReesCoordinate_mem i U) n
        (Stacks.Blowup.reesMonomial _ n r : reesAlgebra _) hmem := by
    unfold Stacks.Blowup.reesAwayMk
    rfl
  have e1 := Stacks.ProjectiveCompletion.map_away_mk
    (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1))
    (includeRight_infinityReesCoordinate i U) (infinityReesCoordinate_mem i U)
    (centreChartCoordinate_mem i U) n _ hmem
  have hmem' := GradedFunLike.map_mem
    (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)) hmem
  have e2 := Stacks.ProjectiveCompletion.map_away_mk (exceptionalChartGradedInv i U hi)
    (exceptionalChartGradedInv_centreChartCoordinate i hi U) (centreChartCoordinate_mem i U)
    (Stacks.ProjectiveCompletion.infinitySection_mem _ _) n _ hmem'
  have e3 := Stacks.ProjectiveCompletion.chartRingEquiv_symm_mk
    (isAffineOpen_centrePreimage i U) n _
    (GradedFunLike.map_mem (exceptionalChartGradedInv i U hi) hmem')
  rw [e0, completionChartRingHom_apply]
  refine congrArg (normalConeEmbeddingRingHom i hi U).hom ?_
  refine (congrArg (fun z => (Stacks.ProjectiveCompletion.chartRingEquiv
    (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
    (isAffineOpen_centrePreimage i U)).symm (HomogeneousLocalization.map
      (exceptionalChartGradedInv i U hi) (Stacks.ProjectiveCompletion.powers_le_comap_powers _
        (exceptionalChartGradedInv_centreChartCoordinate i hi U)) z)) e1).trans ?_
  refine (congrArg (fun z => (Stacks.ProjectiveCompletion.chartRingEquiv
    (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
    (isAffineOpen_centrePreimage i U)).symm z) e2).trans ?_
  exact e3

omit [IsClosedImmersion i] [IsLocallyNoetherian Z] in
/-- `1 ⊗ r t⁰ = r̄ ⊗ 1` in `B`, for `r ∈ Γ(V)` with image `r̄ ∈ Γ(Z ∩ U)`. -/
theorem includeRight_reesMonomial_zero
    (r : Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1))
    (hr : r ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 0) :
    Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)
        (Stacks.Blowup.reesMonomial _ 0 ⟨r, hr⟩ : reesAlgebra _) =
      algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) ((centreChartRingHom i U).hom r) := by
  have hx : ((Stacks.Blowup.reesMonomial ((infinityCentreIdeal i.ker).ideal
      (infinityChartAffineOpen U)) 0 ⟨r, hr⟩ : Stacks.Blowup.reesGrading _ 0) :
        reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))) =
      algebraMap _
        (reesAlgebra ((infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U))) r :=
    Subtype.ext (by simp [Polynomial.monomial_zero_left])
  rw [Stacks.ProjBaseChange.includeRight_apply, hx, ← Algebra.TensorProduct.algebraMap_apply',
    Algebra.TensorProduct.algebraMap_apply]
  rfl

/-- **`completionChartRingHom` on scalars**: `r / (s t)⁰` goes to the image of `r` in
`Γ(Z ∩ U, 𝒞_{Z/X,*})`. -/
theorem completionChartRingHom_reesAwayMk_zero
    (r : Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1))
    (hr : r ∈ (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 0) :
    completionChartRingHom i hi U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 0 ⟨r, hr⟩) =
      ((Stacks.Conormal.conormalAlgebraSheaf i).hom.hom.app (op (i ⁻¹ᵁ U.1))).hom
        ((centreChartRingHom i U).hom r) := by
  set s := (centreChartRingHom i U).hom r
  have h2 : exceptionalChartGradedInv i U hi (algebraMap Γ(Z, i ⁻¹ᵁ U.1) (centreChartRing i U) s) =
      (completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).strHom (i ⁻¹ᵁ U.1) s :=
    (RingEquiv.symm_apply_eq _).2 (exceptionalChartRingEquiv_strHom i U hi s).symm
  have h3 := Stacks.ProjectiveCompletion.sectionsDehomogenize_strHom
    (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
    (isAffineOpen_centrePreimage i U) s
  have h4 : (normalConeEmbeddingRingHom i hi U).hom
      (((Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).hom.hom.app
          (op (i ⁻¹ᵁ U.1))).hom s) =
      ((Stacks.Conormal.conormalAlgebraSheaf i).hom.hom.app (op (i ⁻¹ᵁ U.1))).hom s :=
    (congrArg ((Stacks.Conormal.conormalSymmetricAlgebraSheafHom i).right.hom.app
      (op (i ⁻¹ᵁ U.1))).hom (algebraSheaf_app_structure _ _ s)).trans
      (algebraSheaf_app_structure _ _ s)
  rw [completionChartRingHom_reesAwayMk, includeRight_reesMonomial_zero i U r hr, h2, h3]
  exact h4

/-- **`completionChartRingHom` on a degree-one generator**: `e(x) t / s t` goes to the class of
`x ∈ I` in `I/I²`. -/
theorem completionChartRingHom_reesAwayMk_one {x : Γ(X, U.1)}
    (hx : x ∈ Stacks.Conormal.chartIdeal i U)
    (hr : infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 1) :
    completionChartRingHom i hi U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 1 ⟨_, hr⟩) =
      Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (classOfPow _ 1 ⟨x, by simpa using hx⟩) := by
  obtain ⟨m, hm⟩ := exists_conormalSymmetricSectionsEquiv_ι_eq_classOfPow i hi U hx
  have hκ : conormalSymmetricSectionsEquiv i U hi (SymmetricAlgebra.ι _ _
      ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).p
        ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).j m))) =
      classOfPow _ 1 ⟨x, by simpa using hx⟩ := by
    rw [LineSplitting.p_j _]
    exact hm
  have h1 : exceptionalChartGradedInv i U hi
      (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1)
        (Stacks.Blowup.reesMonomial _ 1 ⟨_, hr⟩ : reesAlgebra _)) =
      (Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).symm
        (SymmetricAlgebra.ι _ _ ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).j m)) := by
    refine (RingEquiv.symm_apply_eq _).2 ?_
    show _ = exceptionalChartSymEquiv i U hi
      ((Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U))
        ((Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).symm
          (SymmetricAlgebra.ι _ _ ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).j m))))
    rw [RingEquiv.apply_symm_apply, exceptionalChartSymEquiv_ι_of i U hi _ hx hκ,
      LineSplitting.q_j _, map_zero, zero_mul, add_zero]
    rfl
  have h2 : Stacks.ProjectiveCompletion.sectionsDehomogenize (isAffineOpen_centrePreimage i U)
      ((Stacks.ProjectiveCompletion.sectionRingEquiv (isAffineOpen_centrePreimage i U)).symm
        (SymmetricAlgebra.ι _ _ ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).j m))) =
      Stacks.SymAlgSections.symSectionsRingEquiv _ (isAffineOpen_centrePreimage i U)
        (SymmetricAlgebra.ι _ _ m) := by
    have h5 : (Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).dehomogenize
        (SymmetricAlgebra.ι _ _ ((Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).j m)) =
        SymmetricAlgebra.ι _ _ m := by
      rw [LineSplitting.dehomogenize_ι, LineSplitting.p_j _, LineSplitting.q_j _, map_zero,
        add_zero]
    exact (Stacks.ProjectiveCompletion.sectionsDehomogenize_apply _ _).trans
      (congrArg (Stacks.SymAlgSections.symSectionsRingEquiv _ _)
        ((congrArg (Stacks.ProjectiveCompletion.sectionsSplitting
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) (i ⁻¹ᵁ U.1)).dehomogenize
          (RingEquiv.apply_symm_apply _ _)).trans h5))
  refine (completionChartRingHom_reesAwayMk i hi U 1 ⟨_, hr⟩).trans ?_
  refine (congrArg (fun y => (normalConeEmbeddingRingHom i hi U).hom
    (Stacks.ProjectiveCompletion.sectionsDehomogenize (isAffineOpen_centrePreimage i U) y))
      h1).trans ?_
  refine (congrArg (normalConeEmbeddingRingHom i hi U).hom h2).trans ?_
  refine (normalConeEmbeddingRingHom_symSectionsRingEquiv i hi U _).trans ?_
  exact congrArg _ hm

omit [IsLocallyNoetherian Z] in
/-- **The ring map of `C_ZX ⟶ E ⟶ W` on the chart `D₊(s t)`, on scalars**: `e(p) / (s t)⁰` goes to
the image of `p(0)` in `Γ(Z ∩ U, 𝒞_{Z/X,*})`. -/
theorem exceptionalChartSectionsEquiv_infinityReesAwayEquiv_zero (p : Polynomial Γ(X, U.1))
    (hr : infinityChartSectionsEquiv U p ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 0) :
    exceptionalChartSectionsEquiv i U (Ideal.Quotient.mk _ (infinityReesAwayEquiv i U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 0 ⟨_, hr⟩))) =
      ((Stacks.Conormal.conormalAlgebraSheaf i).hom.hom.app (op (i ⁻¹ᵁ U.1))).hom
        ((i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (p.coeff 0)) := by
  have hq : Ideal.Quotient.mk (infinityChartFibreIdeal (i.ker.ideal U))
      (algebraMap _ (infinityChartAlgebra (i.ker.ideal U)) p) =
      Ideal.Quotient.mk _ (algebraMap _ _ (Polynomial.C (p.coeff 0))) := by
    rw [Ideal.Quotient.eq, ← map_sub]
    have hp : p - Polynomial.C (p.coeff 0) = Polynomial.divX p * Polynomial.X := by
      rw [sub_eq_iff_eq_add]
      exact (Polynomial.divX_mul_X_add p).symm
    rw [hp, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  rw [infinityReesAwayEquiv_reesAwayMk_zero, hq]
  exact ConcreteCategory.congr_hom (exceptionalChartSectionsEquiv_structure i U) (p.coeff 0)

omit [IsLocallyNoetherian Z] in
/-- **The ring map of `C_ZX ⟶ E ⟶ W` on the chart `D₊(s t)`, on a degree-one generator**:
`e(x) t / s t` goes to the class of `x ∈ I` in `I/I²`. -/
theorem exceptionalChartSectionsEquiv_infinityReesAwayEquiv_one {x : Γ(X, U.1)}
    (hx : x ∈ i.ker.ideal U)
    (hr : infinityChartSectionsEquiv U (Polynomial.C x) ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 1) :
    exceptionalChartSectionsEquiv i U (Ideal.Quotient.mk _ (infinityReesAwayEquiv i U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 1 ⟨_, hr⟩))) =
      Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (classOfPow (Stacks.Conormal.chartIdeal i U) 1
          ⟨x, by rw [chartIdeal_eq_ker_ideal, pow_one]; exact hx⟩) := by
  have hc : Ideal.Quotient.mk (infinityChartFibreIdeal (i.ker.ideal U))
      (infinityChartMk (i.ker.ideal U) 1 (Polynomial.C x)
        (C_mem_pow_infinityChartIdeal (by rw [pow_one]; exact hx))) =
      conormalEquivInfinityChartFibre (i.ker.ideal U)
        (classOfPow (i.ker.ideal U) 1 ⟨x, by rw [pow_one]; exact hx⟩) := by
    have hxp : x ∈ AssociatedGraded.power (M := Γ(X, U.1)) (i.ker.ideal U) 1 := by
      rw [AssociatedGraded.ring_power_eq]; simpa using hx
    rw [conormalEquivInfinityChartFibre_apply']
    exact ((conormalToInfinityChartFibre_of (i.ker.ideal U) 1
      (AssociatedGraded.mk (i.ker.ideal U) 1 ⟨x, hxp⟩)).trans
      (conormalPieceToInfinityChartFibre_mk (i.ker.ideal U) 1 ⟨x, hxp⟩)).symm
  rw [infinityReesAwayEquiv_reesAwayMk_one_C i U hx hr, hc,
    exceptionalChartSectionsEquiv_conormalEquiv]
  exact congrArg (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance)
    (gradedRingMapOfRingHom_classOfPow _ _ _ 1 _)

/-- **The two ring maps out of `Γ(V)[𝒥(V) t]_{(s t)}` agree**: the ring map of
`C_ZX ⟶ E ⟶ W`, through `Γ(V)[𝒥(V) t]_{(s t)} ≅ A[s][J/s] ⟶ A[s][J/s]/(s) ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})`,
is the ring map of `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z) ≅ E ⟶ W`. Both send `a / (s t)⁰` to the class of `a(0)`
and `x t / s t`, `x ∈ I`, to the class of `x` in `I/I²`, and these generate. -/
theorem infinityReesAwayEquiv_comp_exceptionalChartSectionsIso :
    CommRingCat.ofHom (infinityReesAwayEquiv i U).toRingHom ≫ exceptionalChartQuotient i.ker U ≫
        (exceptionalChartSectionsIso i U).hom =
      CommRingCat.ofHom (completionChartRingHom i hi U) := by
  have h0 : ∀ (p : Polynomial Γ(X, U.1)) (hr : infinityChartSectionsEquiv U p ∈
      (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 0),
      exceptionalChartSectionsEquiv i U (Ideal.Quotient.mk _ (infinityReesAwayEquiv i U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 0 ⟨_, hr⟩))) =
      completionChartRingHom i hi U
        (Stacks.Blowup.reesAwayMk _ _ (infinityChartSectionsEquiv_X_mem i U) 0 ⟨_, hr⟩) := by
    intro p hr
    refine (exceptionalChartSectionsEquiv_infinityReesAwayEquiv_zero i U p hr).trans ?_
    refine Eq.trans ?_ (completionChartRingHom_reesAwayMk_zero i hi U _ hr).symm
    rw [centreChartRingHom_infinityChartSectionsEquiv, Scheme.Hom.appLE_eq_app,
      Polynomial.coeff_zero_eq_eval_zero]
  refine CommRingCat.hom_ext (Stacks.Blowup.reesAway_ringHom_ext _ _
    (infinityChartSectionsEquiv_X_mem i U) ?_ ?_)
  · rintro ⟨r, hr⟩
    obtain ⟨p, rfl⟩ := (infinityChartSectionsEquiv U).surjective r
    exact h0 p hr
  · rintro ⟨j, hj⟩
    obtain ⟨p, rfl⟩ := (infinityChartSectionsEquiv U).surjective j
    have hp : p ∈ infinityChartIdeal (i.ker.ideal U) := by
      rw [pow_one, ideal_infinityCentreIdeal_infinityChartAffineOpen] at hj
      obtain ⟨q, hq, hqp⟩ := (Ideal.mem_map_of_equiv _ _).1 hj
      rwa [(infinityChartSectionsEquiv U).injective hqp] at hq
    have hp0 : p.coeff 0 ∈ i.ker.ideal U := by
      have h := mem_pow_infinityChartIdeal_iff.1 (show p ∈ infinityChartIdeal (i.ker.ideal U) ^ 1
        by rwa [pow_one]) 0
      simpa using h
    have hp0' : p.coeff 0 ∈ Stacks.Conormal.chartIdeal i U := by
      rwa [chartIdeal_eq_ker_ideal]
    have hC : infinityChartSectionsEquiv U (Polynomial.C (p.coeff 0)) ∈
        (infinityCentreIdeal i.ker).ideal (infinityChartAffineOpen U) ^ 1 := by
      rw [pow_one]; exact infinityChartSectionsEquiv_C_mem i U hp0'
    have hsplit := Stacks.Blowup.reesAwayMk_one_eq_add _ _ (infinityChartSectionsEquiv_X_mem i U)
      hj hC (y := infinityChartSectionsEquiv U (Polynomial.divX p)) (by
        rw [← map_mul, ← map_add]
        exact congrArg _ ((Polynomial.divX_mul_X_add p).symm.trans (add_comm _ _)))
    rw [hsplit, map_add, map_add]
    exact congrArg₂ (· + ·)
      ((exceptionalChartSectionsEquiv_infinityReesAwayEquiv_one i U hp0 hC).trans
        (completionChartRingHom_reesAwayMk_one i hi U hp0' hC).symm)
      (h0 _ _)

end RingIdentity

/-! ### The compatibility -/

section Compatibility

variable [IsLocallyNoetherian Z]
  (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) (U : X.affineOpens)

omit [IsLocallyNoetherian Z] in
/-- `C_ZX ⟶ E ⟶ W` on the chart of `C_ZX` over `U`, through the standard open `D₊(s t)` of the
Rees chart of `W`. -/
theorem normalConeChart_normalConeToExceptionalDivisor_subschemeι :
    normalConeChart i U ≫ normalConeToExceptionalDivisor i ≫
        (exceptionalIdealAtInfinity i.ker).subschemeι =
      Spec.map (CommRingCat.ofHom (infinityReesAwayEquiv i U).toRingHom ≫
          exceptionalChartQuotient i.ker U ≫ (exceptionalChartSectionsIso i U).hom) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos ≫ infinityReesChart i U := by
  rw [normalConeToExceptionalDivisor, Category.assoc,
    normalConeChart_normalConeIsoExceptionalCompl_hom_assoc, exceptionalComplChartT,
    Category.assoc, exceptionalComplChart_ι_assoc, exceptionalChartS_subschemeι,
    blowupAtInfinityChartS_eq_awayι]
  simp only [Spec.map_comp, Category.assoc]

/-- The ring map `Γ(V)[𝒥(V) t]_{(s t)} ⟶ B_{(1 ⊗ s t)} ≅ Γ(Z ∩ U, Sym(𝒞 ⊕ 𝒪_Z))_{(T)} ≅
Γ(Z ∩ U, Sym(𝒞))` of the chart of `𝐏(𝒞 ⊕ 𝒪_Z)` at `T` inside the Rees chart of `W`. -/
abbrev completionChartAwayHom :
    CommRingCat.of (HomogeneousLocalization.Away (centreReesGrading i U)
        (infinityReesCoordinate i U)) ⟶
      (Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).right.obj.obj
        (op (i ⁻¹ᵁ U.1)) :=
  CommRingCat.ofHom (HomogeneousLocalization.map
      (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1))
      (Stacks.ProjectiveCompletion.powers_le_comap_powers _
        (includeRight_infinityReesCoordinate i U))) ≫
    CommRingCat.ofHom (HomogeneousLocalization.map (exceptionalChartGradedInv i U hi)
      (Stacks.ProjectiveCompletion.powers_le_comap_powers _
        (exceptionalChartGradedInv_centreChartCoordinate i hi U))) ≫
    CommRingCat.ofHom
      (R := HomogeneousLocalization.Away ((completionAlgebra (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).grading (i ⁻¹ᵁ U.1))
        (Stacks.ProjectiveCompletion.infinitySection _ (i ⁻¹ᵁ U.1)))
      (S := ((Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)).right.obj.obj
          (op (i ⁻¹ᵁ U.1)) : CommRingCat))
      (Stacks.ProjectiveCompletion.chartRingEquiv
        (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
        (isAffineOpen_centrePreimage i U)).symm.toRingHom

/-- The chart of `𝐏(𝒞 ⊕ 𝒪_Z)` at `T` over `Z ∩ U` passes through the chart of `E` over `U`. -/
theorem chartToCompletion_eq_exceptionalProjChart :
    Stacks.ProjectiveCompletion.chartToCompletion
        (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
        (isAffineOpen_centrePreimage i U) =
      Stacks.ProjectiveCompletion.chartAway _ ⟨i ⁻¹ᵁ U.1, isAffineOpen_centrePreimage i U⟩ ≫
        exceptionalChartProjMap i U hi ≫ exceptionalProjChart i U ≫
          (exceptionalDivisorIsoProjectiveCompletion i hi).hom := by
  have h := (Iso.comp_inv_eq _).1
    (completionChart_exceptionalDivisorIsoProjectiveCompletion_inv i hi U)
  exact (Stacks.ProjectiveCompletion.chartToCompletion_eq _
    ⟨i ⁻¹ᵁ U.1, isAffineOpen_centrePreimage i U⟩).trans
    (congrArg (Stacks.ProjectiveCompletion.chartAway _
      ⟨i ⁻¹ᵁ U.1, isAffineOpen_centrePreimage i U⟩ ≫ ·) (h.trans (Category.assoc _ _ _)))

/-- **The chart of `𝐏(𝒞 ⊕ 𝒪_Z)` at `T` over `Z ∩ U`, followed by `𝐏(𝒞 ⊕ 𝒪_Z) ≅ E ⟶ W`, is a
standard open of the Rees chart of `W`.** -/
theorem chartToCompletion_exceptionalDivisorIsoProjectiveCompletion_inv_subschemeι :
    Stacks.ProjectiveCompletion.chartToCompletion
        (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)
        (isAffineOpen_centrePreimage i U) ≫
        (exceptionalDivisorIsoProjectiveCompletion i hi).inv ≫
          (exceptionalIdealAtInfinity i.ker).subschemeι =
      Spec.map (completionChartAwayHom i hi U) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos ≫ infinityReesChart i U := by
  have h1 := Stacks.ProjectiveCompletion.awayι_comp_map_of_eq (exceptionalChartGradedInv i U hi)
    (exceptionalChartGradedInv_centreChartCoordinate i hi U)
    (irrelevant_le_map_exceptionalChartGradedInv i U hi) one_pos (centreChartCoordinate_mem i U)
    (Stacks.ProjectiveCompletion.infinitySection_mem _ _)
  have h2 := Stacks.ProjectiveCompletion.awayι_comp_map_of_eq
    (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1))
    (includeRight_infinityReesCoordinate i U)
    (Stacks.ProjBaseChange.irrelevant_le_map _ _) one_pos (infinityReesCoordinate_mem i U)
    (centreChartCoordinate_mem i U)
  have h2' : Proj.awayι (centreChartGrading i U) (centreChartCoordinate i U)
      (centreChartCoordinate_mem i U) one_pos ≫
        Stacks.ProjBaseChange.map (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map
        (Stacks.ProjBaseChange.includeRight (centreReesGrading i U) Γ(Z, i ⁻¹ᵁ U.1))
        (Stacks.ProjectiveCompletion.powers_le_comap_powers _
          (includeRight_infinityReesCoordinate i U)))) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos := h2
  rw [chartToCompletion_eq_exceptionalProjChart]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [exceptionalProjChart_subschemeι, exceptionalChartProjMap, reassoc_of% h1]
  refine (congrArg (fun f => Spec.map _ ≫ Spec.map _ ≫ f) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ infinityReesChart i U) h2').trans (Category.assoc _ _ _)))).trans ?_
  simp only [completionChartAwayHom, Spec.map_comp, Category.assoc]

/-- `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z) ≅ E ⟶ W` on the chart of `C_ZX` over `U`, through the standard open
`D₊(s t)` of the Rees chart of `W`. -/
theorem normalConeChart_normalConeEmbedding_toCompletion_subschemeι :
    normalConeChart i U ≫ (VirtualNormalBundle.ofIsRegularImmersion i hi).normalConeEmbedding ≫
        Stacks.ProjectiveCompletion.toCompletion
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) ≫
        (exceptionalDivisorIsoProjectiveCompletion i hi).inv ≫
          (exceptionalIdealAtInfinity i.ker).subschemeι =
      Spec.map (CommRingCat.ofHom (completionChartRingHom i hi U)) ≫
        Proj.awayι (centreReesGrading i U) (infinityReesCoordinate i U)
          (infinityReesCoordinate_mem i U) one_pos ≫ infinityReesChart i U := by
  have hring : CommRingCat.ofHom (completionChartRingHom i hi U) =
      completionChartAwayHom i hi U ≫ normalConeEmbeddingRingHom i hi U := rfl
  refine (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (exceptionalDivisorIsoProjectiveCompletion i hi).inv ≫
      (exceptionalIdealAtInfinity i.ker).subschemeι)
      ((Category.assoc _ _ _).trans
        (normalConeChart_normalConeEmbedding_toCompletion i hi U)))) |>.trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Spec.map (normalConeEmbeddingRingHom i hi U) ≫ ·)
    (chartToCompletion_exceptionalDivisorIsoProjectiveCompletion_inv_subschemeι i hi U)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hring]
  simp only [Spec.map_comp, Category.assoc]

/-- **The isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` is compatible with the normal cone**: the open immersion
`C_ZX ⟶ E` of Stacks 0FBH followed by `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` is the closed immersion `C_ZX ⟶ N` of the
normal cone into the normal bundle followed by the open immersion `N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
theorem normalConeToExceptionalDivisor_comp_exceptionalDivisorIsoProjectiveCompletion_hom :
    normalConeToExceptionalDivisor i ≫ (exceptionalDivisorIsoProjectiveCompletion i hi).hom =
      (VirtualNormalBundle.ofIsRegularImmersion i hi).normalConeEmbedding ≫
        Stacks.ProjectiveCompletion.toCompletion
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) := by
  rw [← cancel_mono ((exceptionalDivisorIsoProjectiveCompletion i hi).inv ≫
    (exceptionalIdealAtInfinity i.ker).subschemeι), Category.assoc, Iso.hom_inv_id_assoc]
  refine normalCone_hom_ext i fun U => ?_
  refine (normalConeChart_normalConeToExceptionalDivisor_subschemeι i U).trans ?_
  refine Eq.trans ?_ (congrArg (normalConeChart i U ≫ ·) (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (normalConeChart_normalConeEmbedding_toCompletion_subschemeι i hi U).symm
  rw [infinityReesAwayEquiv_comp_exceptionalChartSectionsIso i hi U]
  rfl

end Compatibility

end Stacks.Chow

end
