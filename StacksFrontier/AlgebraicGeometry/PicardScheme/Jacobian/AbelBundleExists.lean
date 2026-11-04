module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.ProjectiveJacobian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelMorphism
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerAbelBundle

/-!
# The existence of Abel projective bundles, from the claim of Stacks 0B9X

`Stacks.Chow.AbelBundleExists` asks, for a smooth proper geometrically irreducible curve `X` over
an algebraically closed field with a rational point, for a morphism `Hilb^n ⟶ P` which is
Zariski-locally on `P` the projective space `ℙ^{n-g}`, for every large `n`. In the source this is
the Abel map `γ_n : Hilb^n_{X/k} ⟶ Pic^n_{X/k}` of [Stacks, Tag 0BA0] for `n ≥ 2g - 1`.

## Main results

* `Stacks.RigidifiedPicard.abelBundleExists_of_claim`: `Stacks.Chow.AbelBundleExists`, granted
  the claim in the proof of [Stacks, Tag 0B9X] (existence and uniqueness halves) and the
  projective bundle structure of the Abel morphism for `n ≥ 2g - 1`.
* `Stacks.RigidifiedPicard.abelBundleExists_of_isLocallyProjectiveSpace`: the same with the claim
  of [Stacks, Tag 0B9X] discharged, so only the projective bundle structure is carried.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

/-- **The Abel morphism of degree `d ≥ 2g - 1` is a projective bundle of rank `d - g`**, for a
smooth proper curve over an algebraically closed field: the clause of [Stacks, Tag 0BA0] (5)
that `γ_d` is, Zariski locally on `Pic⁰`, the projective space `ℙ^{d-g}`. -/
def AbelMorphismIsLocallyProjectiveSpace : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f]
    [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
    [LocallyOfFiniteType f] [GeometricallyIntegral f] [IsCurve k f]
    (hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ f = 𝟙 _) (θ : Stacks.Picard.ofScheme X) {d : ℕ}
    (hθ : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = d) {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
    [LocallyOfFiniteType A.X.hom], 2 * genus f ≤ d + 1 →
      Stacks.ProjectiveBundle.IsLocallyProjectiveSpace
        (abelMorphism f hdim σ hσ θ hθ hH A e).left (d - genus f)

/-- **Abel projective bundles exist**, granted the claim in the proof of [Stacks, Tag 0B9X] and
the projective bundle structure of the Abel morphism. For a smooth proper geometrically
irreducible curve `X` over an algebraically closed field `k` with a rational point `x` and every
`n ≥ 2g + 1`, the Abel morphism `Hilb^n_{X/k} ⟶ Pic⁰_{X/k,x}`, translated by `n[x]`, is a
projective bundle of rank `n - g` over the group scheme representing `Pic⁰_{X/k,x}`. -/
theorem abelBundleExists_of_claim
    (hex : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Stacks.WeilCohomology.CohomologyLocusDivisorExistence K)
    (hun : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness K)
    (hbun : AbelMorphismIsLocallyProjectiveSpace.{u}) :
    Stacks.Chow.AbelBundleExists.{u} := by
  intro k _ _ X _ _ _ hproj H hH x hx
  set f := X.hom
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve k f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one f
  have hdimX : topologicalKrullDim X.left ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdimF : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s ↦ by
    rwa [topologicalKrullDim_fiber_spec f s]
  have : GeometricallyIntegral f := geometricallyIntegral_of_smooth f
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections k f
  have := GenusOne.isEffectiveCartierDivisor f h0 x hx
  set θ₀ : Stacks.Picard.ofScheme X.left := genus f • Stacks.Divisors.picardClass
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point x}, GenusOne.isClosed_point f x hx⟩ : TopologicalSpace.Closeds X.left))
  have hθ₀ : invertibleCurveDegreeHom k f hdimX θ₀ = genus f := by
    rw [map_nsmul, invertibleCurveDegreeHom_divisorPicardClass_point k f hdimX h0 x hx,
      nsmul_eq_mul, mul_one]
  obtain ⟨A, ⟨e⟩, hA⟩ := exists_smooth_grp_iso_functorZero f hdimX hdimF x hx θ₀ hθ₀ H hH
    (fun T c ↦ hex k f T c) (fun T Z Z' ↦ hun k f T Z Z')
    (fun L _ _ c hc ↦
      Stacks.WeilCohomology.prescribedCohomologyTranslate_of_isSepClosed k f L c _ hc θ₀ hθ₀)
  refine ⟨genus f, 2 * genus f + 1, fun n hn ↦ ⟨by omega, A.X.left, A.X.hom, inferInstance, ?_⟩⟩
  obtain ⟨θ, hθ⟩ := exists_degree_eq f hdimX hdimF x hx n
  exact ⟨(abelMorphism f hdimF x hx θ hθ (hH n) A e).left, Over.w _,
    hbun f hdimF x hx θ hθ (hH n) A e (by omega)⟩

/-- **Abel projective bundles exist, granted only the projective bundle structure of the Abel
morphism.** -/
theorem abelBundleExists_of_isLocallyProjectiveSpace
    (hbun : AbelMorphismIsLocallyProjectiveSpace.{u}) : Stacks.Chow.AbelBundleExists.{u} :=
  abelBundleExists_of_claim (fun K _ _ ↦ Stacks.WeilCohomology.cohomologyLocusDivisorExistence K)
    (fun K _ _ ↦ Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness K) hbun

end Stacks.RigidifiedPicard
