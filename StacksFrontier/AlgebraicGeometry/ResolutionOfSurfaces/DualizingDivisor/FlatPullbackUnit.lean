module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowupChainTwistedInverseImage
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Flat derived pullback of the structure sheaf and of cohomology sheaves

For a flat morphism of schemes `g : X ⟶ Y` the derived pullback `Lg^*` is degreewise pullback, so
`Lg^*(𝒪_Y[0]) ≅ 𝒪_X[0]` and `H^i(Lg^*K) ≅ g^*H^i(K)`. For an isomorphism `e`, the twisted inverse
image `e^×` is `Le^*` (both are quasi-inverse to `Re_*`), so `e` has trivial twisted inverse
image.

## Main results

* `AlgebraicGeometry.DualizingDivisor.quasiCoherentDerivedPullbackUnitIso`:
  `Lg^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.
* `AlgebraicGeometry.DualizingDivisor.homologyQuasiCoherentDerivedPullbackIso`:
  `H^i(Lg^*K) ≅ g^*H^i(K)`.
* `AlgebraicGeometry.DualizingDivisor.twistedInverseImageIsoPullbackOfIsIso`: `e^× ≅ Le^*` for an
  isomorphism `e`.
* `AlgebraicGeometry.DualizingDivisor.hasTrivialTwistedInverseImage_of_isIso`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Stacks.Duality

universe u

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat

namespace AlgebraicGeometry.DualizingDivisor

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g]

/-- **`Lg^*(𝒪_Y[0]) ≅ 𝒪_X[0]` for a flat morphism `g`**: derived pullback along a flat morphism is
degreewise pullback, and `g^*𝒪_Y = 𝒪_X`. -/
noncomputable def quasiCoherentDerivedPullbackUnitIso :
    (quasiCoherentDerivedPullback' g).obj (unitQC Y) ≅ unitQC X :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((derivedPullbackMapDerivedIso g).app _ ≪≫
      ((Scheme.Modules.pullback g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor X.Modules 0).mapIso (Scheme.Modules.pullbackUnitIso g))

/-- **Flat derived pullback commutes with cohomology sheaves**: `H^i(Lg^*K) ≅ g^*H^i(K)`. -/
noncomputable def homologyQuasiCoherentDerivedPullbackIso (K : quasiCoherentDerivedCategory Y)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).obj
        ((quasiCoherentDerivedPullback' g).obj K).obj ≅
      (Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor Y.Modules i).obj K.obj) :=
  (DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((derivedPullbackMapDerivedIso g).app K.obj) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback g) i).app K.obj

section Iso

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] [CompactSpace Y]

/-- Derived direct image along an isomorphism, as an equivalence `D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_Y)`
(`Stacks.Duality.quasiCoherentDerivedPushforwardEquivalenceOfIsIso`). -/
noncomputable abbrev pushforwardEquivalenceOfIsIso :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e
    quasiCoherentDerivedCategory X ≌ quasiCoherentDerivedCategory Y :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e
  quasiCoherentDerivedPushforwardEquivalenceOfIsIso e
    (isQuasicoherent_homology_derivedPushforward_of_qcqs e)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv e))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 X))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Y))

/-- **The twisted inverse image of an isomorphism is its derived pullback**: both are
quasi-inverse to the equivalence `Re_*`, as its right and its left adjoint. -/
noncomputable def twistedInverseImageIsoPullbackOfIsIso :
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward e
    twistedInverseImage e (isQuasicoherent_homology_derivedPushforward_of_qcqs e) ≅
      quasiCoherentDerivedPullback' e :=
  letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward e
  Adjunction.rightAdjointUniq (twistedInverseImageAdjunction e _)
      (pushforwardEquivalenceOfIsIso e).toAdjunction ≪≫
    (Adjunction.leftAdjointUniq (quasiCoherentDerivedAdjunction e
      (isQuasicoherent_homology_derivedPullback' e)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs e))
        (pushforwardEquivalenceOfIsIso e).symm.toAdjunction).symm

/-- **An isomorphism has trivial twisted inverse image**:
`e^×(𝒪_Y[0]) ≅ Le^*(𝒪_Y[0]) ≅ 𝒪_X[0]`. -/
theorem hasTrivialTwistedInverseImage_of_isIso : HasTrivialTwistedInverseImage e :=
  ⟨(twistedInverseImageIsoPullbackOfIsIso e).app _ ≪≫ quasiCoherentDerivedPullbackUnitIso e⟩

/-- **An object whose derived pullback along an isomorphism is trivial is trivial**: if
`Le^*M ≅ 𝒪_X[0]` then `M ≅ Re_*Le^*M ≅ Re_*Le^*𝒪_Y[0] ≅ 𝒪_Y[0]`, `Le^*` being quasi-inverse to
the equivalence `Re_*`. -/
theorem nonempty_iso_unitQC_of_pullback_of_isIso (M : quasiCoherentDerivedCategory Y)
    (h : (quasiCoherentDerivedPullback' e).obj M ≅ unitQC X) : Nonempty (M ≅ unitQC Y) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e
  let E := pushforwardEquivalenceOfIsIso e
  let i : quasiCoherentDerivedPullback' e ≅ E.inverse :=
    Adjunction.leftAdjointUniq (quasiCoherentDerivedAdjunction e
      (isQuasicoherent_homology_derivedPullback' e)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs e)) E.symm.toAdjunction
  exact ⟨E.counitIso.symm.app M ≪≫ E.functor.mapIso ((i.symm.app M) ≪≫ h ≪≫
    (quasiCoherentDerivedPullbackUnitIso e).symm ≪≫ i.app _) ≪≫ E.counitIso.app _⟩

end Iso

end AlgebraicGeometry.DualizingDivisor

end
