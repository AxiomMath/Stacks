module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedComparison
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage

/-!
# The twist comparison of [Stacks, Tag 0897] part (2)

[Stacks, Tag 0897] part (2) is read off the base change `X' = Spec_X(𝓑)` of the source's proof:
one vanishing statement upstairs, for the single module `F'` twisted by `(π^* L)^{⊗d}`, accounts
for the vanishing of *every* `Hᵖ(X, Fₙ ⊗ L^{⊗d})` downstairs. **This file supplies that
implication**, which is the hypothesis `hcmp` of
`Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology`.

## The chain

Write `π : X' ⟶ X` for the affine structure morphism of the relative spectrum and
`G = L^{⊗d}`. Then

* a module whose restriction of scalars is a zero object is a zero object, restriction of
  scalars being faithful and additive;
* `Hᵖ(X', F' ⊗ (π^*L)^{⊗d}) = 0` gives `Hᵖ(X, π_*(F' ⊗ (π^*L)^{⊗d})) = 0`, by
  [Stacks, Tag 089W] for the affine `π`
  (`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`);
* `(π^*L)^{⊗d} ≅ π^*(L^{⊗d})` (`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`) and the
  projection formula ([Stacks, Tag 0FZE],
  `Stacks.ProjectionFormula.pushforwardTensorRightNatIso`) identify
  `π_*(F' ⊗ (π^*L)^{⊗d})` with `(π_* F') ⊗ G`;
* `π_* F' ≅ ∐_{n : ℤ} Fₙ` is the defining property of `F'`
  (`GradedQcohAlgebra.coprodPushforwardIso`), so the vanishing is that of
  `Hᵖ(X, (∐ₙ Fₙ) ⊗ G)`;
* and `Fₙ ⊗ G ⟶ (∐ₙ Fₙ) ⊗ G` is a split mono — the degree-`n` injection into a coproduct is,
  and every functor preserves split monos — so `Hᵖ(X, Fₙ ⊗ G)` is a retract of a zero object.

The last step is why no comparison `Hᵖ(X, ∐ₙ −) ≅ ⨁ₙ Hᵖ(X, −)` is needed: only the vanishing of
the summands is wanted, and a retract of a zero object vanishes.

## Main results

* `GradedQcohAlgebra.isZero_pieceTwist_of_isZero_baseChangeTwist`: **the implication**, for an
  arbitrary sheaf of graded algebras and an arbitrary morphism out of `X'` whose restriction of
  scalars the hypothesis is phrased with.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **A module whose restriction of scalars is a zero object is a zero object**: restriction of
scalars is faithful and additive, so it reflects the vanishing of the identity. -/
theorem isZero_of_isZero_restrictScalars {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (Z : ModuleCat.{u} S) (hz : IsZero ((ModuleCat.restrictScalars φ).obj Z)) : IsZero Z := by
  rw [Limits.IsZero.iff_id_eq_zero]
  refine (ModuleCat.restrictScalars φ).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (Limits.IsZero.iff_id_eq_zero _).1 hz

namespace GradedQcohAlgebra

variable {X : Scheme.{u}} (D : GradedQcohAlgebra X)
  (M : _root_.SheafOfModules.GradedModule.{u, u, u} D.alg)
  (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
  (L : X.Modules) [IsInvertibleModule X L]

/-- **The degree-`n` injection into the coproduct of the homogeneous pieces is a split mono**,
retracted by the projection onto the degree-`n` summand. -/
def splitMonoSigmaι (n : ℤ) : SplitMono (Limits.Sigma.ι (fun m : ℤ => M.piece m) n) where
  retraction := Limits.Sigma.desc (Pi.single n (𝟙 (M.piece n)))
  id := by simp

/-- **The twist comparison of [Stacks, Tag 0897] part (2).** If the cohomology of the twist of
`F'` by `(π^* L)^{⊗d}` vanishes in degree `p`, then so does the cohomology of every twist
`Fₙ ⊗ L^{⊗d}` of a homogeneous piece.

The morphism `f'` is arbitrary: it enters only through the restriction of scalars the hypothesis
is phrased with, which is discarded in the first step. -/
theorem isZero_pieceTwist_of_isZero_baseChangeTwist {Y : Scheme.{u}}
    (f' : D.relSpec.left ⟶ Y) (p d : ℕ)
    (hz : IsZero ((ModuleCat.restrictScalars f'.appTop.hom).obj
        (cohomologyOf D.relSpec.left p
          (tensorModules D.relSpec.left (D.baseChangeModule M hqc)
            (tensorPowModule D.relSpec.left
              (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ)))))) :
    ∀ n : ℤ, IsZero (cohomologyOf X p (pieceTwist M L n (d : ℤ))) := by
  have : IsInvertibleModule X (tensorPowModule X L (d : ℤ)) :=
    isInvertibleModule_tensorPowModule X L (d : ℤ)
  have : IsInvertibleModule D.relSpec.left
      (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) :=
    Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf D.relSpec.hom L
  have : IsInvertibleModule D.relSpec.left
      (tensorPowModule D.relSpec.left
        (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ)) :=
    isInvertibleModule_tensorPowModule _ _ (d : ℤ)
  -- the twist upstairs
  have hpowqc : (tensorPowModule D.relSpec.left
      (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have hTqc : (tensorModules D.relSpec.left (D.baseChangeModule M hqc)
      (tensorPowModule D.relSpec.left
        (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ))).IsQuasicoherent :=
    Stacks.AmpleFiniteSurjective.isQuasicoherent_tensorModules _ _
  -- (1) drop the restriction of scalars
  have h1 : IsZero (cohomologyOf D.relSpec.left p
      (tensorModules D.relSpec.left (D.baseChangeModule M hqc)
        (tensorPowModule D.relSpec.left
          (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ)))) :=
    isZero_of_isZero_restrictScalars f'.appTop.hom _ hz
  -- (2) [Stacks, Tag 089W] along the affine `π`
  have h2 : IsZero (cohomologyOf X p
      ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
        (tensorModules D.relSpec.left (D.baseChangeModule M hqc)
          (tensorPowModule D.relSpec.left
            (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ))))) :=
    ((ModuleCat.restrictScalars D.relSpec.hom.appTop.hom).map_isZero h1).of_iso
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward D.relSpec.hom _ p).symm
  -- (3) the projection formula, and `(π^*L)^{⊗d} ≅ π^*(L^{⊗d})`
  have e2 : tensorModules D.relSpec.left (D.baseChangeModule M hqc)
        ((_root_.AlgebraicGeometry.Scheme.Modules.pullback D.relSpec.hom).obj
          (tensorPowModule X L (d : ℤ))) ≅
      tensorModules D.relSpec.left (D.baseChangeModule M hqc)
        (tensorPowModule D.relSpec.left
          (Stacks.AmpleLocallyClosed.pullbackModule D.relSpec.hom L) (d : ℤ)) :=
    tensorModulesMapIso D.relSpec.left (Iso.refl _)
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso D.relSpec.hom L d)
  have e1 := (Stacks.ProjectionFormula.pushforwardTensorRightNatIso D.relSpec.hom
    (tensorPowModule X L (d : ℤ))).app (D.baseChangeModule M hqc)
  -- (4) `π_* F' ≅ ∐ₙ Fₙ`
  have e3 : tensorModules X
        ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).obj
          (D.baseChangeModule M hqc)) (tensorPowModule X L (d : ℤ)) ≅
      tensorModules X (∐ fun n : ℤ => M.piece n) (tensorPowModule X L (d : ℤ)) :=
    tensorModulesMapIso X (D.coprodPushforwardIso M hqc).symm (Iso.refl _)
  have h3 : IsZero (cohomologyOf X p
      (tensorModules X (∐ fun n : ℤ => M.piece n) (tensorPowModule X L (d : ℤ)))) :=
    h2.of_iso ((((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).mapIso
      ((_root_.AlgebraicGeometry.Scheme.Modules.pushforward D.relSpec.hom).mapIso e2.symm ≪≫
        e1 ≪≫ e3))).symm
  -- (5) each summand's twist is a retract of the twist of the coproduct
  intro n
  have key : ∀ Tw : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤),
      IsZero (Tw.obj (∐ fun m : ℤ => M.piece m)) → IsZero (Tw.obj (M.piece n)) := by
    intro Tw hTw
    have hsplit : IsSplitMono (Tw.map (Limits.Sigma.ι (fun m : ℤ => M.piece m) n)) :=
      IsSplitMono.mk'
        ⟨Tw.map (splitMonoSigmaι D M n).retraction,
          ((Tw.map_comp _ _).symm.trans
            (congrArg (fun φ : M.piece n ⟶ M.piece n => Tw.map φ)
              (splitMonoSigmaι D M n).id)).trans (Tw.map_id _)⟩
    exact IsZero.of_mono_eq_zero (Tw.map (Limits.Sigma.ι (fun m : ℤ => M.piece m) n))
      (hTw.eq_zero_of_tgt _)
  exact key (Stacks.ProjectionFormula.tensorRightInvertible X (tensorPowModule X L (d : ℤ)) ⋙
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) h3

end GradedQcohAlgebra

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
