module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartExistence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeGlue
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectComposite
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeStalkTensorBoundProof
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalRelativeTorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of relative dualizing complexes

Let `f : Y ⟶ X` and `g : X ⟶ S` be flat and locally of finite presentation, and let `(K, ξ)` and
`(M, η)` be relative dualizing complexes for `g` and `f` (Stacks 0E2T). Then
`E = M ⊗ᴸ_{𝒪_Y} Lf^*K` is the first component of a relative dualizing complex `(E, ζ)` for
`f ≫ g` (Stacks 0E30), on the diagonal open `W' ⊆ Y ×_S Y` built from those of `g` and `f` in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal`.

## The proof

* `E` is `S`-perfect:
  `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_derivedTensor_of_stalkBound` together with
  the pointwise bound `AlgebraicGeometry.Scheme.Hom.relativeStalkTensorBound` (the stalk of
  `M ⊗ᴸ Lf^*K` is `M_y ⊗ᴸ_{𝒪_{X,x}} K_x`, and Stacks 0B66).
* `R ℰom(𝒪_V, L pr₁^*E|_{W'}) ≅ L pr₁^*M|_V`
  (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_compExactSupport_iso_of_isIso_diagonal`),
  from the invertibility of the diagonal of Stacks 0BYS at
  `(L pr₁^*M|_{W'}, L(f × f)^* L pr₁^*K|_W, δ_*𝒪_V)`. That diagonal is invertible by the relative
  form of Stacks 0ATN (3)
  (`isIso_derivedTensorHomDiagonal_derivedPullback_of_locallyHasRelativeTorAmplitudeGE` in
  `Stacks.Cohomology.DerivedInternalHomPullback`), because `L pr₁^*M|_{W'}` has locally bounded Tor
  amplitude over `𝒪_W` along `f × f`
  (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_hasTorAmplitudeOver_compProd`).
* Then `R ℰom(𝒪_Y, L pr₁^*E|_{W'}) ≅ 𝒪_Y[0]` by Stacks 0E2I and `η`
  (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_comp_diagonalExactSupport_iso`), and such
  an isomorphism is induced by a map `ζ : Δ_*𝒪_Y ⟶ L pr₁^*E|_{W'}`
  (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_isIso_diagonalAction`).

## A gap in the source's proof

The source applies Stacks 0E2N on `Y ×_S Y` with tensor factor `Lq^*M`. Stacks 0E2N asks the
tensor factor to have Tor amplitude bounded below over `𝒪_{Y ×_S Y}`, and `Lq^*M` need not:
for `X = S = Spec k` and `Y = Spec B` with `B` Artinian and not Gorenstein, `M = ω_B`, the module
`ω_B ⊗_k B` has infinite Tor dimension over `B ⊗_k B`, since `ω_B` has infinite projective
dimension over `B`. What is true, and what the proof here uses, is that `Lq^*M` has Tor amplitude
bounded below relative to `f × f`, over `𝒪_{X ×_S X}`; with that hypothesis the diagonal of
Stacks 0BYS is still invertible. This is the sheaf-level form of the argument of the algebraic
version, Stacks 0E2H, run over `A ⊗_R A` (see
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.comp`: Stacks 0E30.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- `L pr₁^*M|_{W'}` has Tor amplitude bounded below relative to `f × f : W' ⟶ W`, locally on
`W'`, for `M` `X`-perfect. -/
theorem DiagonalOpen.locallyHasRelativeTorAmplitudeGE_compProd {X Y S : Scheme.{u}}
    {g : X ⟶ S} {f : Y ⟶ X} [Flat f] [LocallyOfFinitePresentation f] (Dg : DiagonalOpen g)
    (Df : DiagonalOpen f) (M : DerivedCategory Y.Modules)
    (hM : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) M) :
    Stacks.Cohomology.DerivedInternalHomPullback.LocallyHasRelativeTorAmplitudeGE
      (Dg.compProd Df).toLRSHom.toShHom ((Dg.comp Df).derivedPullbackProj M) :=
  Dg.exists_isGE_restrict_tensor_derivedPullbackProj Df M hM

/-- **Stacks 0E30.** Let `f : Y ⟶ X` and `g : X ⟶ S` be flat and locally of finite
presentation, and let `(K, ξ)` and `(M, η)` be relative dualizing complexes for `g` and `f`.
Then `(M ⊗ᴸ Lf^*K, ζ)` is a relative dualizing complex for `f ≫ g`, for a suitable `ζ`, on the
diagonal open `W' = Dg.comp Df` of the source's proof.

The source's proof applies Stacks 0E2N with tensor factor `Lq^*M` over `𝒪_{Y ×_S Y}`, which
needs Tor amplitude of `Lq^*M` over `𝒪_{Y ×_S Y}`; this fails for `X = S = Spec k`,
`Y = Spec B`, `B` Artinian non-Gorenstein, `M = ω_B`. The proof here uses instead the Tor
amplitude of `Lq^*M` relative to `f × f`, as the algebraic version 0E2H does over `A ⊗_R A`. -/
@[stacks 0E30]
theorem IsRelativeDualizingComplex.comp {X Y S : Scheme.{u}} (g : X ⟶ S) (f : Y ⟶ X)
    [Flat g] [LocallyOfFinitePresentation g] [Flat f] [LocallyOfFinitePresentation f]
    {Dg : DiagonalOpen g} {K : DerivedCategory X.Modules}
    {ξ : Dg.diagonalObject ⟶ Dg.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex g (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      Dg K ξ)
    {Df : DiagonalOpen f} {M : DerivedCategory Y.Modules}
    {η : Df.diagonalObject ⟶ Df.derivedPullbackProj M}
    (hM : IsRelativeDualizingComplex f (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      Df M η) :
    ∃ ζ, IsRelativeDualizingComplex (f ≫ g)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (Dg.comp Df)
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        Y.toRingedSpace.sheaf).obj M).obj
        ((derivedPullback f.toLRSHom.toShHom).obj K)) ζ := by
  have hE := isPerfectRelativeTo_comp_derivedTensor_of_stalkBound g f
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.toRingedSpace.sheaf)
    (relativeStalkTensorBound f g _) K M hK.isPerfectRelativeTo hM.isPerfectRelativeTo
  have := Dg.flat_compProd Df
  have hdiag0 :=
    open Stacks.Cohomology.DerivedInternalHomPullback in
    isIso_derivedTensorHomDiagonal_derivedPullback_of_locallyHasRelativeTorAmplitudeGE
      (Dg.compProd Df).toLRSHom.toShHom (fun w => Flat.stalkMap (Dg.compProd Df) w)
      (Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf Dg.diagQuotient)
      (Scheme.isPseudoCoherent_pushforward_derivedStructureSheaf Dg.diag Dg.pseudoCoherent_diag)
      (Dg.derivedPullbackProj K)
      (Dg.isLocallyBoundedBelow_derivedPullbackProj K hK.isPerfectRelativeTo)
      ((Dg.comp Df).derivedPullbackProj M)
      (Dg.locallyHasRelativeTorAmplitudeGE_compProd Df M hM.isPerfectRelativeTo)
  have hdiag := RingedSite.isIso_derivedTensorHomDiagonal_of_iso_hom _ _ _
    (Dg.compPushforwardStructureSheafIso Df).symm hdiag0
  obtain ⟨es⟩ := Dg.nonempty_compExactSupport_iso_of_isIso_diagonal Df M K
    hK.isPerfectRelativeTo ξ hK.isIso_diagonalAction hdiag
  have h2 := Dg.nonempty_comp_diagonalExactSupport_iso Df _ M η hM.isIso_diagonalAction ⟨es⟩
  obtain ⟨ζ, hζ⟩ := (Dg.comp Df).exists_isIso_diagonalAction _ h2
  refine ⟨ζ, ?_⟩
  constructor
  · exact hE
  · exact hζ

end AlgebraicGeometry.Scheme.Hom

end
