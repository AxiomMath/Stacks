module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityJacobianTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Main
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowRank
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# Tag 03RQ from the degree-zero Picard scheme

The theorem `etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_rank`
proves the eight clauses of [Stacks, Tag 03RQ] from a Jacobian `H` of the curve and the rank of
multiplication by the primes dividing `n` on it. This file instantiates `H` with `Pic⁰_{X/k}`
(`Stacks.PicardFunctor.picardDegreeZeroSubgroup`), whose rational points are `Pic⁰(X)`, and derives
the rank from [Stacks, Tag 0BFG], whose only input beyond an ample module is the theorem of the
cube (`Stacks.Cube.hasTheoremOfTheCube`).

## Main results

* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_picardScheme`: the
  eight clauses of [Stacks, Tag 03RQ], with the Picard functor representable, clause (1) of
  [Stacks, Tag 0BA0] for the degree-zero component and the quasi-projectivity of `Pic⁰_{X/k}` as
  inputs.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

open Stacks.PicardFunctor

section PicardScheme

variable (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
  (B : BigFppfSite.{u}) {X : Scheme.{u}} (hXb : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (fb : B.obj hXb ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map fb = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map fb)] [IsProjectiveVariety k (B.inclusion.map fb)]
  [Smooth (B.inclusion.map fb)] [GeometricallyIrreducible (B.inclusion.map fb)]
  [(picardFunctor B hXb hk fb).IsRepresentable]
  (E : BigEtaleSite.{u}) (hX : E.Contains X)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

/-- **The eight clauses of [Stacks, Tag 03RQ] from the degree-zero Picard scheme.** -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_picardScheme (hn : IsUnit (n : k))
    (hproper : IsProper (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom))
    (hsmooth : Smooth (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom))
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).left))
    (hdim : Stacks.Groupoids.abelianVarietyDimension
        (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X = genus (B.inclusion.map fb))
    (hq : IsQuasiProjective (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X.hom) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX (B.inclusion.map fb) n) ∧
      Function.Bijective
        (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X (B.inclusion.map fb) E hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale E X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X (B.inclusion.map fb) E hX n hn x) =
          picardDegreeZMod k X (B.inclusion.map fb) n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 1 ≃+
        (Fin (2 * genus (B.inclusion.map fb)) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) q) := by
  have := isAbelianVariety_picardDegreeZero B hXb hk fb σ hσ hproper hsmooth hint
  have hcube := Stacks.Cube.hasTheoremOfTheCube
    (A := (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X)
  have : LocallyOfFiniteType (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X.hom :=
    inferInstance
  obtain ⟨L, hL, hamp⟩ := (isQuasiProjective_groupScheme_iff_exists_isAmple
    (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier).mp hq
  exact etaleCohomology_rootsOfUnity_smoothProjectiveCurve_allDegrees_of_jacobian_of_rank k X
    (B.inclusion.map fb) n E hX hn (picardDegreeZeroSubgroup B hXb hk fb σ hσ)
    (isProper_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hproper)
    (smooth_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hsmooth)
    (connectedSpace_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hint) hdim
    (fun p _ hpn => Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_isAmple
      (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X hcube p
      (isUnit_of_dvd_unit (Nat.cast_dvd_cast hpn) hn) L hamp)
    (picardDegreeZeroPoints B hXb hk fb σ hσ) (picardDegreeZeroPoints_mul B hXb hk fb σ hσ)
    (bijective_picardDegreeZeroPoints B hXb hk fb σ hσ)

end PicardScheme

section Assembly

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] (n : ℕ)
  (E : BigEtaleSite.{u}) (hX : E.Contains X)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

/-- **[Stacks, Tag 03RQ] over the remaining inputs about the Picard scheme.** The statement of
record, a smooth projective curve over an algebraically closed field and `n` invertible in it,
with the facts about the Picard scheme of `X` that are not yet available collected in `hinp`: for
every big fppf site carrying `X ⟶ Spec k` and every rational point, the Picard functor is
representable, its degree-zero component is smooth, proper, integral and of dimension the genus
(clause (1) of [Stacks, Tag 0BA0]). Quasi-projectivity of `Pic⁰_{X/k}` is [Stacks, Tag 0BF7] and
the theorem of the cube is `Stacks.Cube.hasTheoremOfTheCube`. -/
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_picardInputs (hn : IsUnit (n : k))
    (hinp : ∀ (B : BigFppfSite.{u}) (hXb : B.Contains X) (hk : B.Contains (Spec (.of k)))
      (fb : B.obj hXb ⟶ B.obj hk) (σ : Spec (.of k) ⟶ X)
      (hσ : σ ≫ B.inclusion.map fb = 𝟙 (Spec (.of k))) [IsCurve k (B.inclusion.map fb)]
      [IsProjectiveVariety k (B.inclusion.map fb)] [Smooth (B.inclusion.map fb)]
      [GeometricallyIrreducible (B.inclusion.map fb)],
      ∃ _ : (picardFunctor B hXb hk fb).IsRepresentable,
        IsProper (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom) ∧
        Smooth (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom) ∧
        IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).left) ∧
        Stacks.Groupoids.abelianVarietyDimension
          (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X = genus (B.inclusion.map fb)) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX f n) ∧
      Function.Bijective (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f E hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale E X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f E hX n hn x) = picardDegreeZMod k X f n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) q) := by
  obtain ⟨B, hXb, hk, fb, hfb, ⟨σ, hσ⟩, hgi⟩ := exists_bigFppfSite_picardData f
  subst hfb
  obtain ⟨hrep, hproper, hsmooth, hint, hdim⟩ := hinp B hXb hk fb σ hσ
  have hq : IsQuasiProjective (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X.hom := by
    have := smooth_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hsmooth
    have := isProper_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hproper
    exact isQuasiProjective_of_groupScheme_over_field _
  exact etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_picardScheme k n B hXb hk fb σ hσ
    E hX hn hproper hsmooth hint hdim hq

end Assembly

end AlgebraicGeometry

end
