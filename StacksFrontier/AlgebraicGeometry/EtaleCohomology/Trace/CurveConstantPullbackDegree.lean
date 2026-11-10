module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantSecondCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePullbackDegree

/-!
# Pullback of `H²` with constant coefficients along a morphism of curves

Let `π : B ⟶ A` be a nonconstant morphism of smooth proper curves over an algebraically closed
field `K`, `n` invertible in `K` and `ζ` a primitive `n`-th root of unity.  The pullback of the
fundamental class `[A] ∈ H²(A, ℤ/n)` is `deg(B/A) · [B]`, and for a finite abelian group `E`
killed by `n` the pullback `π^* : H²(A, E) → H²(B, E)` is zero as soon as `n ∣ deg(B/A)`.

## Main results

* `Stacks.EtaleCohomology.etaleConstantCohomologyPullback_sheafHMap`: the pullback on constant
  coefficients is natural in the coefficient group.
* `Stacks.EtaleCohomology.etaleConstantCohomologyPullback_curveFundamentalClass`:
  `π^*[A] = deg(B/A) · [B]`.
* `Stacks.EtaleCohomology.etaleConstantCohomologyPullback_two_eq_zero_of_dvd`: `π^*` kills
  `H²(A, E)` when `n ∣ deg(B/A)`.

## References

* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Naturality

variable {X Y : Scheme.{u}} [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The pullback on constant coefficients is natural in the coefficient group.** -/
theorem etaleConstantCohomologyPullback_sheafHMap (π : X ⟶ Y) {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (φ : A →+ B) (q : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y A) q) :
    etaleConstantCohomologyPullback π B q (Sheaf.H.map (etaleConstantSheafMap Y φ) q x) =
      Sheaf.H.map (etaleConstantSheafMap X φ) q (etaleConstantCohomologyPullback π A q x) := by
  simp only [etaleConstantCohomologyPullback, etaleCohomologyMapTo, AddMonoidHom.comp_apply]
  rw [Stacks.Kummer.etaleCohomologyRestrictionMap_sheafHMap, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]
  congr 2
  exact (etaleAbelianInverseImageConstantIso.{u, 0} π).hom.naturality _

end Naturality

section Degree

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Scheme.{u}} (qA : A ⟶ Spec (.of K))
  (qB : B ⟶ Spec (.of K)) [IsCurve K qA] [Smooth qA] [IsProper qA] [IsCurve K qB] [Smooth qB]
  [IsProper qB] (π : B ⟶ A) (w : π ≫ qA = qB) (hnc : ¬ ∃ a : A, ∀ b : B, π.base b = a)
  {n : ℕ} (hn : IsUnit (n : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ n)

include w in
/-- **`π^*[A] = deg(B/A) · [B]`** for a nonconstant morphism `π : B ⟶ A` of smooth proper curves
over an algebraically closed field. -/
theorem etaleConstantCohomologyPullback_curveFundamentalClass :
    etaleConstantCohomologyPullback π (ZMod n) 2 (curveFundamentalClass qA hn hζ) =
      (@degreeOver B A π inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp K qB qA π w)
          (isDominant_of_not_constant K qB qA π hnc)) • curveFundamentalClass qB hn hζ := by
  have hn0 := Stacks.Kummer.neZero_of_isUnit hn
  have hdimA : topologicalKrullDim A ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := qA)).le
  have hdimB : topologicalKrullDim B ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := qB)).le
  have key : curveConstantTrace qB hn hζ
      (etaleConstantCohomologyPullback π (ZMod n) 2 (curveFundamentalClass qA hn hζ)) =
      ((@degreeOver B A π inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp K qB qA π w)
          (isDominant_of_not_constant K qB qA π hnc) : ℕ) : ℤ) •
        curveConstantTrace qA hn hζ (curveFundamentalClass qA hn hζ) := by
    change Stacks.Kummer.smoothProperCurveTrace qB hn
        (sheafHRootsOfUnityConstantAddEquiv qB hζ hn0 2
          (etaleConstantCohomologyPullback π (ZMod n) 2 (curveFundamentalClass qA hn hζ))) =
      _ • Stacks.Kummer.smoothProperCurveTrace qA hn
        (sheafHRootsOfUnityConstantAddEquiv qA hζ hn0 2 (curveFundamentalClass qA hn hζ))
    rw [sheafHRootsOfUnityConstantAddEquiv_apply, sheafHRootsOfUnityConstantAddEquiv_apply,
      sheafHMap_rootsOfUnityConstantHom_etaleCohomologyMapTo qB qA π w hζ hn0]
    exact Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap qB qA hn hn π _
      (fun L => Stacks.Picard.picardDegree_schemePullbackClassHom qB qA hdimB hdimA π w hnc L) _
  apply (curveConstantTrace qB hn hζ).injective
  rw [key, map_nsmul, curveConstantTrace_curveFundamentalClass,
    curveConstantTrace_curveFundamentalClass]
  simp

include w hnc hn in
/-- **`π^* : H²(A, E) → H²(B, E)` vanishes when `n ∣ deg(B/A)`**, for a finite abelian group `E`
killed by `n` and `π : B ⟶ A` a nonconstant morphism of smooth proper curves over an
algebraically closed field in which `n` is invertible. -/
theorem etaleConstantCohomologyPullback_two_eq_zero_of_dvd {E : Type} [AddCommGroup E] [Finite E]
    (hE : ∀ a : E, n • a = 0)
    (hd : n ∣ @degreeOver B A π inferInstance inferInstance
      (locallyOfFiniteType_of_isCurve_comp K qB qA π w)
      (isDominant_of_not_constant K qB qA π hnc))
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} A E) 2) :
    etaleConstantCohomologyPullback π E 2 x = 0 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  obtain ⟨φ, rfl⟩ := surjective_curveConstantClass qA hn hζ hE x
  change etaleConstantCohomologyPullback π E 2
    (Sheaf.H.map (etaleConstantSheafMap A φ) 2 (curveFundamentalClass qA hn hζ)) = 0
  rw [etaleConstantCohomologyPullback_sheafHMap,
    etaleConstantCohomologyPullback_curveFundamentalClass qA qB π w hnc hn hζ]
  obtain ⟨c, hc⟩ := hd
  rw [hc, mul_comm, ← smul_smul, nsmul_sheafH_etaleConstantSheaf_eq_zero, smul_zero, map_zero]

end Degree

end Stacks.EtaleCohomology

end
