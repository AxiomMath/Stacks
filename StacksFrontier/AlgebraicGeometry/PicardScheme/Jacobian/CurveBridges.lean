module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardZeroRepresentable
public import
  StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Picard.CurveChowZeroDivisor
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian

/-!
# The hypotheses of the Picard construction for a curve over a field

This file supplies, for a proper integral scheme `X` over a field `k` with a rational point,
the inputs of `Stacks.RigidifiedPicard.exists_grp_iso_functorZero` which concern only `X`:

* `𝒪_T ⟶ (X_T ⟶ T)_*𝒪_{X_T}` is an isomorphism for every `k`-scheme `T`
  (`Stacks.RigidifiedPicard.isIso_bcProj_c`, [Stacks, Tag 0B9U] at the hypotheses its proof uses);
* the fibre of `X ⟶ Spec k` at the point has the dimension of `X`
  (`Stacks.RigidifiedPicard.topologicalKrullDim_fiber_spec_le`);
* the degree on that fibre is the degree on `X`
  (`Stacks.RigidifiedPicard.relativeInvertibleDegreeHomAt_spec`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **[Stacks, Tag 0B9U], at the hypotheses its proof uses**: for `X` integral and universally
closed over `k` with a `k`-rational point, `𝒪_T ⟶ (X_T ⟶ T)_*𝒪_{X_T}` is an isomorphism for every
`k`-scheme `T`. -/
theorem isIso_bcProj_c [IsIntegral X] [UniversallyClosed f] [QuasiSeparated f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (T : Over (Spec (.of k))) :
    IsIso (bcProj f T).toLRSHom.toHom.c := by
  have hf : IsIso (Scheme.Modules.unitToPushforwardUnit f) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      f).1 (isIso_c_of_section_of_universallyClosed f σ hσ)
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
    (pullback.snd f T.hom)).2
    (Stacks.AlgebraicGeometry.AffinePushforward.isIso_unitToPushforwardUnit_of_isPullback
      (IsPullback.of_hasPullback f T.hom) hf)

/-- The residue field of a point of `Spec k`, as a field extension of `k`. -/
abbrev specResidueAlgebra (s : Spec (.of k)) : Algebra k ((Spec (.of k)).residueField s) :=
  (Spec.preimage ((Spec (.of k)).fromSpecResidueField s)).hom.toAlgebra

/-- For a point `s` of `Spec k`, the morphism `Spec κ(s) ⟶ Spec k` induced by the structure map
`k → κ(s)` is the canonical morphism from the spectrum of the residue field. -/
theorem spec_map_specResidueAlgebra (s : Spec (.of k)) :
    letI := specResidueAlgebra s
    Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField s))) =
      (Spec (.of k)).fromSpecResidueField s := by
  conv_rhs => rw [← Spec.map_preimage ((Spec (.of k)).fromSpecResidueField s)]
  rfl

/-- The fibre of `X ⟶ Spec k` at the point has the dimension of `X`. -/
theorem topologicalKrullDim_fiber_spec [LocallyOfFiniteType f] (s : Spec (.of k)) :
    topologicalKrullDim ↥(f.fiber s) = topologicalKrullDim X := by
  let := specResidueAlgebra s
  have h := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField s))))
  have e := topologicalKrullDim_baseChange k ((Spec (.of k)).residueField s) _ _ f h
  rw [spec_map_specResidueAlgebra] at e
  exact e

/-- The degree of a Picard class on the fibre of `X ⟶ Spec k` at the point is its degree. -/
theorem relativeInvertibleDegreeHomAt_spec [IsProper f] [LocallyOfFiniteType f]
    (hdimX : topologicalKrullDim X ≤ 1)
    (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (s : Spec (.of k)) (θ : Stacks.Picard.ofScheme X) :
    relativeInvertibleDegreeHomAt f hdim s θ = invertibleCurveDegreeHom k f hdimX θ := by
  let := specResidueAlgebra s
  have key : ∀ (ι : Spec ((Spec (.of k)).residueField s) ⟶ Spec (.of k))
      (hι : ι = Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField s))))
      (hd : topologicalKrullDim ↥(pullback f ι) ≤ 1) [IsProper (pullback.snd f ι)],
      invertibleCurveDegreeHom ((Spec (.of k)).residueField s) (pullback.snd f ι) hd
        (Stacks.Picard.schemePullbackClass (pullback.fst f ι) θ) =
        invertibleCurveDegreeHom k f hdimX θ := by
    intro ι hι hd _
    subst hι
    exact invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k
      ((Spec (.of k)).residueField s) (IsPullback.of_hasPullback _ _) hdimX hd θ
  rw [relativeInvertibleDegreeHomAt_apply]
  exact key _ (spec_map_specResidueAlgebra s).symm (hdim s)

/-- A proper smooth geometrically irreducible scheme over a field is integral. -/
theorem isIntegral_of_smooth_geometricallyIrreducible [Smooth f] [GeometricallyIrreducible f] :
    IsIntegral X := by
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have : Subsingleton (Spec (CommRingCat.of k)) := by
    change Subsingleton (PrimeSpectrum k); infer_instance
  exact GeometricallyIntegral.isIntegral_of_subsingleton (f := f)

/-- **A rigidified class of degree `g` on every fibre**: `g` times the class of the rational
point. -/
theorem exists_degree_eq [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [SmoothOfRelativeDimension 1 f] (hdimX : topologicalKrullDim X ≤ 1)
    (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (g : ℕ) :
    ∃ θ : Stacks.Picard.ofScheme X, ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = g := by
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections k f
  have := GenusOne.isEffectiveCartierDivisor f h0 σ hσ
  refine ⟨g • Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal
    (⟨{GenusOne.point σ}, GenusOne.isClosed_point f σ hσ⟩ : TopologicalSpace.Closeds X)),
    fun s => ?_⟩
  rw [relativeInvertibleDegreeHomAt_spec f hdimX hdim s, map_nsmul,
    invertibleCurveDegreeHom_divisorPicardClass_point k f hdimX h0 σ hσ, nsmul_eq_mul, mul_one]

/-- The Hilbert schemes of points of a smooth separated relative curve are smooth. -/
theorem smooth_of_represents [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d) (d : ℕ) :
    Smooth (H d).hom :=
  have : IsSeparated (Over.mk f).hom := ‹IsSeparated f›
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom := ‹SmoothOfRelativeDimension 1 f›
  (Stacks.Hilbert.smoothOfRelativeDimension_of_represents H hH d).smooth

end Stacks.RigidifiedPicard

end
