module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.JacobianOfPicardZero
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardZeroCurve
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineFibresRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSymmetricPower
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsProjectiveJacobian
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension

/-!
# The Jacobian input of Stacks 0FH7 from `Pic⁰`

Over an algebraically closed field `K`, every projective smooth geometrically irreducible curve
`X` has a rational point `σ`, Hilbert schemes of points, and a class of degree `g`; so
`Stacks.RigidifiedPicard.exists_smooth_grp_iso_functorZero` gives a smooth group scheme
representing `Pic⁰_{X/K,σ}`, and `Stacks.WeilCohomology.jacobianParametrization_of_iso_functorZero`
turns it into the Jacobian input `Stacks.WeilCohomology.JacobianParametrization` of
[Stacks, Tag 0FH7]. This file assembles that, given the claim of [Stacks, Tag 0B9X] and
[Stacks, Tag 0B9Y] as hypotheses quantified over all curves.

## Main results

* `Stacks.WeilCohomology.hasProjectiveJacobianParametrizations_of` — the Jacobian input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.WeilCohomology

/-- **The claim in the proof of [Stacks, Tag 0B9X], existence half**, for every proper smooth
geometrically irreducible curve over `K`. -/
def CohomologyLocusDivisorExistence (K : Type u) [Field K] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIrreducible f] (T : Over (Spec (.of K)))
    (c : Stacks.Picard.ofScheme (Stacks.RigidifiedPicard.bc f T)),
    Stacks.RigidifiedPicard.HasInvertibleDirectImage f T c →
      ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
        (n : Stacks.Picard.ofScheme T.left),
        Stacks.RigidifiedPicard.abelClass f Z =
          c + Stacks.Picard.schemePullbackClass (Stacks.RigidifiedPicard.bcProj f T) n

/-- **The claim in the proof of [Stacks, Tag 0B9X], uniqueness half.** -/
def CohomologyLocusDivisorUniqueness (K : Type u) [Field K] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIrreducible f] (T : Over (Spec (.of K)))
    (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)),
    Stacks.RigidifiedPicard.HasInvertibleDirectImage f T (Stacks.RigidifiedPicard.abelClass f Z) →
      (∃ n : Stacks.Picard.ofScheme T.left,
        Stacks.RigidifiedPicard.abelClass f Z' = Stacks.RigidifiedPicard.abelClass f Z +
          Stacks.Picard.schemePullbackClass (Stacks.RigidifiedPicard.bcProj f T) n) → Z = Z'

/-- **[Stacks, Tag 0B9Y] in the degree-zero/degree-`g` form**, for every proper smooth curve over
`K`. -/
def PrescribedCohomologyTranslate (K : Type u) [Field K] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    (L : Type u) [Field L] [Algebra K L]
    (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (hdimL : topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≤ 1),
    invertibleCurveDegreeHom L (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      hdimL c = 0 →
    ∀ θ : Stacks.Picard.ofScheme X,
      invertibleCurveDegreeHom K f (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le θ =
        genus f →
      ∃ c₀ : Stacks.Picard.ofScheme X,
        invertibleCurveDegreeHom K f (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le
          c₀ = 0 ∧
        Module.finrank L (cohomologyOverField L
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) θ)).obj 0) = 1 ∧
        IsZero (cohomologyOverField L
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) θ)).obj 1)

/-- **[Stacks, Tag 0B9Y] in the degree-zero/degree-`g` form holds over every separably closed
field**: over a separably closed field `K`, `PrescribedCohomologyTranslate K` holds. -/
theorem prescribedCohomologyTranslate_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K] :
    PrescribedCohomologyTranslate K :=
  fun f _ _ _ L _ _ c _ hc θ hθ =>
    exists_invertibleCurveDegreeHom_eq_zero_finrank_cohomologyOverField_eq_one K L f c hc θ hθ

/-- **The Jacobian input of [Stacks, Tag 0FH7] over an algebraically closed field**, from the
claim of [Stacks, Tag 0B9X] and from [Stacks, Tag 0B9Y]. -/
theorem hasProjectiveJacobianParametrizations_of (K : Type u) [Field K] [IsAlgClosed K] (n : ℤ)
    (hex : CohomologyLocusDivisorExistence K) (hun : CohomologyLocusDivisorUniqueness K)
    (h0B9Y : PrescribedCohomologyTranslate K) :
    HasProjectiveJacobianParametrizations K n := by
  intro X f _ _ _ hproj hdim
  have : SmoothOfRelativeDimension 1 f :=
    Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one K f
      (by exact_mod_cast hdim)
  have hdimX : topologicalKrullDim X ≤ 1 := hdim.le
  have hdimF : ∀ s : Spec (.of K), topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s => by
    rw [Stacks.RigidifiedPicard.topologicalKrullDim_fiber_spec f s]; exact hdimX
  have : IsIntegral X := Stacks.RigidifiedPicard.isIntegral_of_smooth_geometricallyIrreducible f
  have : IsVariety K f := ⟨⟩
  have : IsCurve K f := ⟨hdim⟩
  have : Subsingleton (Spec (CommRingCat.of K)) := by
    change Subsingleton (PrimeSpectrum K); infer_instance
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have : Nonempty (Over.mk f).left := (inferInstance : Nonempty X)
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := ‹SmoothOfRelativeDimension 1 f›
  obtain ⟨s, -, -⟩ := Stacks.Scheme.exists_ne_sections_of_isAlgClosed (Over.mk f)
  have hσ : s.left ≫ f = 𝟙 _ := by simpa using Over.w s
  have H : ∀ d : ℕ, Σ H : Over (Spec (.of K)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d := fun d =>
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk f) hproj d).some
  have h0 := curveHasOneDimensionalSections K f
  have := GenusOne.isEffectiveCartierDivisor f h0 s.left hσ
  set θ : Stacks.Picard.ofScheme X := genus f • Stacks.Divisors.picardClass
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point s.left}, GenusOne.isClosed_point f s.left hσ⟩ : TopologicalSpace.Closeds X))
  have hθ : invertibleCurveDegreeHom K f hdimX θ = genus f := by
    rw [map_nsmul, invertibleCurveDegreeHom_divisorPicardClass_point K f hdimX h0 s.left hσ,
      nsmul_eq_mul, mul_one]
  obtain ⟨A, ⟨e⟩, hA⟩ := Stacks.RigidifiedPicard.exists_smooth_grp_iso_functorZero f hdimX hdimF
    s.left hσ θ hθ (fun d => (H d).1) (fun d => (H d).2) (fun T c => hex f T c)
    (fun T Z Z' => hun f T Z Z')
    (fun L _ _ c hc => h0B9Y f L c _ hc θ hθ)
  have := hA
  exact jacobianParametrization_of_iso_functorZero f hdimX hdimF s.left hσ A e n

end Stacks.WeilCohomology

end
