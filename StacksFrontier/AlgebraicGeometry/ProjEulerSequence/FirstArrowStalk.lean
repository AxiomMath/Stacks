module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.BiproductStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization

/-!
# The first arrow of the Euler sequence on the chart differentials

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = P^n_R` for
`Proj R[T]`. Fix a point `x` of `X` and a coordinate `Tᵢ` outside its homogeneous prime, so that
`x` lies on the standard chart `D₊(Tᵢ)` and the ratios `Tⱼ/Tᵢ` are regular functions there. This
file computes the first arrow of the Euler sequence on the germ at `x` of `d(Tⱼ/Tᵢ)`.

The answer is the expected one: in the basis `e₀, …, eₙ` of `𝒪_X(-1)^{⊕ (n+1)}` the germ of
`d(Tⱼ/Tᵢ)` is sent to `eⱼ - (Tⱼ/Tᵢ) eᵢ`, so its `k`-th component is `δ_{kj} - δ_{ki} Tⱼ/Tᵢ`
once the stalk of `𝒪_X(-1)` at `x` is identified with the local ring by multiplication by `Tᵢ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.chartFracSection`: the regular function `Tⱼ/Tᵢ`
  on the standard chart `D₊(Tᵢ)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.chartDiffGerm`: the germ at `x` of the
  differential `d(Tⱼ/Tᵢ)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.chartFracSection_val`: the value of `Tⱼ/Tᵢ` at a
  point of `D₊(Tᵢ)` is the fraction `Tⱼ/Tᵢ` of the local ring there.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.val_tw_stalkMap_π_eulerFirstArrow`: the `k`-th
  component of the image of the germ of `d(Tⱼ/Tᵢ)` under the first arrow is
  `δ_{kj} - δ_{ki} Tⱼ/Tᵢ`.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

local instance (x : ProjectiveSpectrum.top (polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

variable (x : ProjectiveSpectrum.top (polyGrading R n)) (i : Fin (n + 1))

/-- **The regular function `Tⱼ/Tᵢ` on the standard chart `D₊(Tᵢ)`**: at every point of the chart
it is the degree-zero homogeneous fraction with numerator `Tⱼ` and denominator `Tᵢ`. -/
def chartFracSection (j : Fin (n + 1)) :
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj.obj
      (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))) :=
  ⟨fun y => HomogeneousLocalization.mk
      ⟨1, ⟨MvPolynomial.X j, X_mem_one R n j⟩, ⟨MvPolynomial.X i, X_mem_one R n i⟩, y.2⟩,
    fun y => ⟨ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i), y.2, 𝟙 _, 1,
      ⟨MvPolynomial.X j, X_mem_one R n j⟩, ⟨MvPolynomial.X i, X_mem_one R n i⟩,
      fun z => z.2, fun _ => rfl⟩⟩

/-- The value of `Tⱼ/Tᵢ` in the local ring at a point of `D₊(Tᵢ)` is the fraction `Tⱼ/Tᵢ`. -/
theorem chartFracSection_val (j : Fin (n + 1))
    (y : ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) :
    HomogeneousLocalization.val ((chartFracSection R n i j).1 y) =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
        ⟨MvPolynomial.X i, y.2⟩ :=
  HomogeneousLocalization.val_mk _

variable (hxb : x ∈ ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))

/-- **The germ at `x` of the differential `d(Tⱼ/Tᵢ)`**, for `x` a point of the standard chart
`D₊(Tᵢ)`: the universal relative derivation of `P^n_R` over `Spec R` applied to `Tⱼ/Tᵢ`, read in
the stalk of the sheaf of relative differentials. -/
def chartDiffGerm (j : Fin (n + 1)) :
    ↥(AlgebraicGeometry.SheafOfModules.stalkObj (projRingSheaf (polyGrading R n)) x
      (projDifferentials R n)) :=
  (TopCat.Presheaf.germ (projDifferentials R n).val.presheaf
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom
    ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d
      (chartFracSection R n i j))

/-- The first arrow carries the germ of `d(Tⱼ/Tᵢ)` to the germ of the value of the Euler
derivation on `Tⱼ/Tᵢ`. -/
private theorem stalkMap_eulerFirstArrow_chartDiffGerm (j : Fin (n + 1)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (eulerFirstArrow R n)).hom (chartDiffGerm R n x i hxb j) =
      (TopCat.Presheaf.germ (twistMinusOneSum R n).val.presheaf
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom
        ((eulerDerivation R n).d (chartFracSection R n i j)) := by
  rw [chartDiffGerm, AlgebraicGeometry.SheafOfModules.stalkMap_germ]
  exact congrArg _ (PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalRelativeDerivation_postcomp_eulerFirstArrow R n) _)

/-- The `k`-th component of the germ of the value of the Euler derivation on a section is the
germ of its derivative `∂ₖ`. -/
private theorem stalkMap_π_germ_eulerDerivation_d (j k : Fin (n + 1)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (biproduct.π (twistMinusOneFamily R n) k)).hom
        ((TopCat.Presheaf.germ (twistMinusOneSum R n).val.presheaf
            (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom
          ((eulerDerivation R n).d (chartFracSection R n i j))) =
      (TopCat.Presheaf.germ (twistMinusOneFamily R n k).val.presheaf
          (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom
        (pderivApp R n k (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
          (chartFracSection R n i j)) := by
  classical
  refine (congrArg (fun z => (AlgebraicGeometry.SheafOfModules.stalkMap
      (projRingSheaf (polyGrading R n)) x (biproduct.π (twistMinusOneFamily R n) k)).hom
    ((TopCat.Presheaf.germ (twistMinusOneSum R n).val.presheaf
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) x hxb).hom z))
    (eulerDerivation_d R n (chartFracSection R n i j))).trans ?_
  refine (congrArg _ (map_sum _ _ _)).trans ?_
  refine (congrArg _ (Finset.sum_congr rfl fun l _ =>
    (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ _
      (biproduct.ι (twistMinusOneFamily R n) l) _ hxb _).symm)).trans ?_
  refine (map_sum _ _ _).trans ?_
  refine (Finset.sum_eq_single_of_mem k (Finset.mem_univ k) fun l _ hlk =>
    AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_ne _ _ _ hlk _).trans ?_
  exact AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_self _ _ _ _ _

/-- The germ of a section of a summand of `𝒪_X(-1)^{⊕ (n+1)}` is the germ taken in the
description of the stalk of the sheaf associated to a graded module. -/
private theorem germ_eq_associatedModuleSheafGerm (k : Fin (n + 1))
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n))) (hxU : x ∈ U)
    (a : (twistMinusOneFamily R n k).val.obj (op U)) :
    (TopCat.Presheaf.germ (twistMinusOneFamily R n k).val.presheaf U x hxU).hom a =
      associatedModuleSheafGerm (polyGrading R n) (twistGrading (polyGrading R n) (-1)) x
        U hxU a :=
  rfl

/-- In the local ring at `x`, the fraction `Tᵢ (Tᵢ ∂ₖTⱼ - Tⱼ ∂ₖTᵢ) / Tᵢ²` is
`δ_{kj} - δ_{ki} Tⱼ/Tᵢ`. -/
private theorem mk_pderiv_X_eq (j k : Fin (n + 1))
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal) :
    Localization.mk ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) *
          ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) *
              MvPolynomial.pderiv k (MvPolynomial.X j) -
            (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
              MvPolynomial.pderiv k (MvPolynomial.X i)))
        (⟨MvPolynomial.X i * MvPolynomial.X i,
          x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hx hx⟩ :
            x.asHomogeneousIdeal.toIdeal.primeCompl) =
      (if k = j then (1 : Localization x.asHomogeneousIdeal.toIdeal.primeCompl) else 0)
        - (if k = i then 1 else 0) *
          Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
            ⟨MvPolynomial.X i, hx⟩ := by
  classical
  have hcancel : ∀ m : MvPolynomial (Fin (n + 1)) R,
      Localization.mk ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * m)
          (⟨MvPolynomial.X i * MvPolynomial.X i,
            x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hx hx⟩ :
              x.asHomogeneousIdeal.toIdeal.primeCompl) =
        Localization.mk m (⟨MvPolynomial.X i, hx⟩ :
          x.asHomogeneousIdeal.toIdeal.primeCompl) := fun m =>
    Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq
      (show (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * (MvPolynomial.X i * m) =
          MvPolynomial.X i * MvPolynomial.X i * m from by ring))
  have hself : Localization.mk (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)
      (⟨MvPolynomial.X i, hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) = 1 :=
    Localization.mk_self (⟨MvPolynomial.X i, hx⟩ :
      x.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [hcancel]
  by_cases hkj : k = j <;> by_cases hki : k = i
  · subst hkj hki
    simp [hself, Localization.mk_zero]
  · subst hkj
    simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hki), hki, hself]
  · subst hki
    simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hkj), hkj, ← Localization.neg_mk]
  · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hkj), MvPolynomial.pderiv_X_of_ne (Ne.symm hki),
      hkj, hki, Localization.mk_zero]

/-- **The first arrow of the Euler sequence on the germ of `d(Tⱼ/Tᵢ)`.** Its `k`-th component,
read through the trivialization of `𝒪_X(-1)` at `x` by the coordinate `Tᵢ`, is
`δ_{kj} - δ_{ki} Tⱼ/Tᵢ`. -/
theorem val_tw_stalkMap_π_eulerFirstArrow
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal)
    (j k : Fin (n + 1)) :
    HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
        (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx
          ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
                (biproduct.π (twistMinusOneFamily R n) k)).hom
            ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
                (eulerFirstArrow R n)).hom (chartDiffGerm R n x i hxb j)))))
      = (if k = j then (1 : Localization x.asHomogeneousIdeal.toIdeal.primeCompl) else 0)
          - (if k = i then 1 else 0) *
            Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)
              ⟨MvPolynomial.X i, hx⟩ := by
  classical
  have hstep : (AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
          (biproduct.π (twistMinusOneFamily R n) k)).hom
        ((AlgebraicGeometry.SheafOfModules.stalkMap (projRingSheaf (polyGrading R n)) x
            (eulerFirstArrow R n)).hom (chartDiffGerm R n x i hxb j)) =
      associatedModuleSheafGerm (polyGrading R n) (twistGrading (polyGrading R n) (-1)) x
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hxb
        (pderivApp R n k (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
          (chartFracSection R n i j)) :=
    ((congrArg (fun z => (AlgebraicGeometry.SheafOfModules.stalkMap
            (projRingSheaf (polyGrading R n)) x
            (biproduct.π (twistMinusOneFamily R n) k)).hom z)
        (stalkMap_eulerFirstArrow_chartDiffGerm R n x i hxb j)).trans
      (stalkMap_π_germ_eulerDerivation_d R n x i hxb j k)).trans
      (germ_eq_associatedModuleSheafGerm R n x k _ hxb _)
  have hpd : (pderivApp R n k
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
        (chartFracSection R n i j)).1 ⟨x, hxb⟩ =
      Localization.mk ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) *
            MvPolynomial.pderiv k (MvPolynomial.X j) -
          (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
            MvPolynomial.pderiv k (MvPolynomial.X i))
        ⟨MvPolynomial.X i * MvPolynomial.X i,
          x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hx hx⟩ :=
    pderivApp_apply_of_val_eq_mk R n k
      (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i))
      (chartFracSection R n i j) ⟨x, hxb⟩ hx (chartFracSection_val R n i j ⟨x, hxb⟩)
  exact ((congrArg (fun z => HomogeneousLocalization.val (Proj.stalkIso' (polyGrading R n) x
        (twistingSheafMinusOneStalkEquiv (polyGrading R n) (X_mem_one R n i) hx z))) hstep).trans
      (val_twistingSheafMinusOneStalkEquiv_germ (polyGrading R n) (X_mem_one R n i) hx
        (ProjectiveSpectrum.basicOpen (polyGrading R n) (MvPolynomial.X i)) hxb _ hpd)).trans
    (mk_pderiv_X_eq R n x i j k hx)

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
