module

public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.DiagonalDeterminant
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# Assembly of the computation of `a(𝒪_S)` for a smooth proper morphism

The chain of isomorphisms in the proof of [Stacks, Tag 0BRT], read from the rigidity isomorphism
`c(Lpr^*ω) ≅ 𝒪_X` on: `c` is the right adjoint of `RΔ_*` for the diagonal `Δ` of `f`, and
`c(K) ≅ LΔ^*K ⊗ᴸ c(𝒪)` with `c(𝒪) ≅ ∧^d 𝒩_Δ[-d]`; since `pr ∘ Δ = id`, this gives
`ω ⊗ᴸ ∧^d 𝒩_Δ[-d] ≅ 𝒪_X`, hence `ω ≅ ∧^d Ω_{X/S}[d]`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `LΔ^* Lpr₂^* ≅ id` on `D(𝒪_X)`, for `Δ` the diagonal of `f` and `pr₂` the second projection
of `X ×_S X`: the composite `Δ ≫ pr₂` is the identity. -/
def derivedPullbackDiagonalSndIso :
    derivedPullback (pullback.snd f f) ⋙ derivedPullback (pullback.diagonal f) ≅
      𝟭 (DerivedCategory X.Modules) :=
  derivedPullbackCompIso (pullback.diagonal f) (pullback.snd f f) ≪≫
    eqToIso (congrArg derivedPullback (pullback.diagonal_snd f)) ≪≫ derivedPullbackIdIso X

/-- `LΔ^* Lpr₁^* ≅ id` on `D(𝒪_X)`, for the first projection. -/
def derivedPullbackDiagonalFstIso :
    derivedPullback (pullback.fst f f) ⋙ derivedPullback (pullback.diagonal f) ≅
      𝟭 (DerivedCategory X.Modules) :=
  derivedPullbackCompIso (pullback.diagonal f) (pullback.fst f f) ≪≫
    eqToIso (congrArg derivedPullback (pullback.diagonal_fst f)) ≪≫ derivedPullbackIdIso X

section Assembly

variable (d : ℕ) [SmoothOfRelativeDimension d f]
  (hf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hΔ : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (pullback f f).Modules i).obj
      ((derivedPushforward (pullback.diagonal f)).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (pullback.diagonal f) hΔ).IsLeftAdjoint]

/-- **The chain of isomorphisms of [Stacks, Tag 0BRT].** Write `ω = a(𝒪_S)` and let `c` be the
right adjoint of `RΔ_*`. Given the rigidity isomorphism `c(Lpr₁^*ω) ≅ 𝒪_X`, the comparison
`LΔ^*(Lpr₁^*ω) ⊗ᴸ c(𝒪) ≅ c(Lpr₁^*ω)` and `c(𝒪) ≅ ∧^d 𝒩_Δ[-d]`, one has
`ω ≅ ∧^d Ω_{X/S}[d]`. -/
def isoSingleFunctorExteriorPowerOfDiagonal
    (eR : (twistedInverseImage (pullback.diagonal f) hΔ).obj
        ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
          ((twistedInverseImage f hf).obj (DerivedPushforward.derivedStructureSheaf S))) ≅
      DerivedPushforward.derivedStructureSheaf X)
    (eU : ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' (pullback.diagonal f)).obj
          ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
            ((twistedInverseImage f hf).obj (DerivedPushforward.derivedStructureSheaf S))))).obj
        ((twistedInverseImage (pullback.diagonal f) hΔ).obj
          (DerivedPushforward.derivedStructureSheaf (pullback f f))) ≅
      (twistedInverseImage (pullback.diagonal f) hΔ).obj
        ((quasiCoherentDerivedPullback' (pullback.fst f f)).obj
          ((twistedInverseImage f hf).obj (DerivedPushforward.derivedStructureSheaf S))))
    (eK : ((twistedInverseImage (pullback.diagonal f) hΔ).obj
        (DerivedPushforward.derivedStructureSheaf (pullback f f))).obj ≅
      (DerivedCategory.singleFunctor X.Modules d).obj
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf (pullback.diagonal f)) d)) :
    ((twistedInverseImage f hf).obj (DerivedPushforward.derivedStructureSheaf S)).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-d)).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) :=
  let ω := (twistedInverseImage f hf).obj (DerivedPushforward.derivedStructureSheaf S)
  isoSingleFunctorExteriorPowerOfDerivedTensorIso f d ω.obj
    (((derivedTensor X).mapIso ((derivedPullbackDiagonalFstIso f).app ω.obj).symm).app _ ≪≫
      ((derivedTensor X).obj _).mapIso eK.symm ≪≫
      (ObjectProperty.ι _).mapIso eU ≪≫ (ObjectProperty.ι _).mapIso eR)

end Assembly

end Stacks.Duality
