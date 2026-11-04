module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.Immersion
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonPerfectProper
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.Assembly
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Rigidity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth

/-!
# The relative dualizing complex of a smooth proper morphism

For `S` Noetherian and `f : X ⟶ S` smooth and proper of relative dimension `d`, the relative
dualizing complex `a(𝒪_S)` is `∧^d Ω_{X/S}[d]`: [Stacks, Tag 0BRT]. The proof runs through the
diagonal `Δ`, a Koszul-regular immersion: rigidity `c(Lpr₁^*a(𝒪_S)) ≅ 𝒪_X`
([Stacks, Tag 0E2P]), the comparison `LΔ^*K ⊗ᴸ c(𝒪) ≅ c(K)` ([Stacks, Tag 0A9U]) and
`c(𝒪) ≅ ∧^d 𝒩_Δ[-d]` ([Stacks, Tag 0BR0]).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **[Stacks, Tag 0BRT].** Let `S` be a Noetherian scheme and `f : X ⟶ S` a smooth proper
morphism of relative dimension `d`, and let `a` be the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` ([Stacks, Tag 0A9E]). Then there is an isomorphism
`∧^d Ω_{X/S}[d] ≅ a(𝒪_S)` in `D(𝒪_X)`. -/
@[stacks 0BRT]
def singleFunctorExteriorPowerIsoRelativeDualizingComplex {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    (DerivedCategory.singleFunctor X.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) ≅
      (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf S)).obj :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  haveI : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Smooth (pullback.fst f f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
  haveI : IsNoetherian X := isNoetherian_of_isProper f
  haveI : IsNoetherian (pullback f f : Scheme.{u}) := isNoetherian_of_isProper (pullback.fst f f)
  haveI : Smooth (pullback.diagonal f ≫ pullback.fst f f ≫ f) := by
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]; infer_instance
  have hK :
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion (pullback.diagonal f) :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isRegularImmersion _
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth (pullback.diagonal f)
        (pullback.fst f f ≫ f))
  haveI : Perfect (pullback.diagonal f) := perfect_of_isKoszulRegularImmersion _ hK
  haveI := isFiniteLocallyFreeOfRank_conormalSheaf_diagonal f d
  let hΔ := isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)
  let ω := (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    (DerivedPushforward.derivedStructureSheaf S)
  haveI := isIso_twistedInverseImageCompareWithPullback_of_perfect_of_isProper
    (pullback.diagonal f) ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj ω)
  (isoSingleFunctorExteriorPowerOfDiagonal f d _ hΔ (relativeDualizingComplexRigidity f).1.1.symm
    (asIso (twistedInverseImageCompareWithPullback (pullback.diagonal f)
      hΔ
      (quasiCoherentDerivedPullbackTensorIso (pullback.diagonal f)).hom
      (quasiCoherentDerivedTensorRightUnitor (pullback f f))
      ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj ω)))
    (KoszulRegular.twistedInverseImageIsoOfIsKoszulRegularImmersion (pullback.diagonal f) hΔ hK
      d).symm).symm

end Stacks.Duality
