module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentLocalCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCokernelDerivation

/-!
# Stacks 0D0X: `ε^*coker(d₀) ⟶ coker(d)` and the restriction of derivations

This file compares the degree `0` cohomology sheaves in the proof of Stacks 0D0X.  Let
`κ₀ : coker d₀ ⟶ ε_*(coker d)` be the map induced by `β : NL_{X₀/Y₀} ⟶ ε_*NL_{X/Y}` on the
cokernels of the differentials (`AlgebraicGeometry.Space.representedEpsilonCokernelHom`).  Its
adjunct `ε^*coker d₀ ⟶ coker d` is an isomorphism exactly when `h ↦ κ₀ ≫ ε_*h` is bijective on
morphisms out of `coker d`; both cokernels corepresent derivations
(`Stacks.SheafOfModules.existsUnique_naiveCotangentCokernelDerivation`), and through these
identifications `h ↦ κ₀ ≫ ε_*h` is the restriction `D ↦ D ∘ ε^♯` of `f^{-1}𝒪_Y`-derivations of
`𝒪_X` to `f_0^{-1}𝒪_{Y₀}`-derivations of `𝒪_{X₀}` with values in `ε_*`.  So the isomorphism is
the statement that this restriction of derivations is bijective.

## Main definitions

* `AlgebraicGeometry.Space.representedEpsilonDerivationRestriction`: the restriction
  `D ↦ D ∘ ε^♯` of derivations along `ε`.  By
  `Stacks.SheafOfModules.bijective_comp_pushforward_map_iff`, `h ↦ κ₀ ≫ ε_*h` is bijective on
  morphisms out of `coker d` into `T` exactly when this restriction is bijective at `T`.

## Main results

* `AlgebraicGeometry.Space.isIso_representedEpsilonCokernelHom_adjunct_iff`: the adjunct of `κ₀`
  is an isomorphism if and only if, for every sheaf of `𝒪_X`-modules `T`, restricting
  derivations of `𝒪_X` with values in `T` along `ε` is bijective.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_representedToZariskiRingedToposSiteHom_u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- **The restriction of derivations along `ε`**: a `f^{-1}𝒪_Y`-derivation `D` of `𝒪_X` with
values in a sheaf of `𝒪_X`-modules `T` gives the `f_0^{-1}𝒪_{Y₀}`-derivation `D ∘ ε^♯` of
`𝒪_{X₀}` with values in `ε_*T`. -/
def representedEpsilonDerivationRestriction
    (T : _root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O))
    (D : PresheafOfModulesOfCommRing.Derivation' T.val
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage.hom) :
    PresheafOfModulesOfCommRing.Derivation'
        ((representedEpsilonModulePushforward B S hS U).obj T).val
      (representedZariskiSchemeHom B S hS φ).fSharpInverseImage.hom :=
  Stacks.SheafOfModules.derivationPushforwardOfSquare.{u, u, u, u + 1, u, u} _ _ _ _ _
    (representedToZariskiRingedToposSiteHom B S hS U).u _ _ _ _ _
    (representedEpsilonPushforwardSquare_commutes B S hS φ) D

/-- `β : NL_{X₀/Y₀} ⟶ ε_*NL_{X/Y}` is the chain map of the square through the site functor of
`ε`, in the spelling of `Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap`. -/
theorem representedEpsilonNaiveCotangentPushforwardMap_eq :
    representedEpsilonNaiveCotangentPushforwardMap B S hS φ =
      Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap.{u, u, u, u + 1, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
        (representedToZariskiRingedToposSiteHom B S hS U).u _ _ _ _ _ _ _ _
        (representedEpsilonPushforwardSquare_commutes B S hS φ) :=
  rfl

/-- `ε_*` on modules is the pushforward along the ring map of the square, in the spelling of
`Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap`. -/
theorem representedEpsilonModulePushforward_eq :
    representedEpsilonModulePushforward B S hS U =
      SheafOfModules.pushforward.{u + 1} (Stacks.SheafOfModules.pushforwardRingHomOfSquare.{u, u, u,
        u + 1, u} ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
        (representedToZariskiRingedToposSiteHom B S hS U).u
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
        (representedToZariskiRingedToposSiteHom B S hS U).fSharp) :=
  rfl

/-- **The adjunct `ε^*coker d₀ ⟶ coker d` of `κ₀` is an isomorphism if and only if restricting
derivations along `ε` is bijective** for every sheaf of `𝒪_X`-modules. -/
theorem isIso_representedEpsilonCokernelHom_adjunct_iff :
    IsIso (((representedEpsilonModuleAdjunction B S hS U).homEquiv _ _).symm
      (representedEpsilonCokernelHom B S hS φ)) ↔
      ∀ T : _root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O),
        Function.Bijective (representedEpsilonDerivationRestriction B S hS φ T) := by
  rw [Adjunction.isIso_homEquiv_symm_iff_bijective]
  refine forall_congr' fun T => ?_
  exact Stacks.SheafOfModules.bijective_comp_map_iff_of_eq.{u, u, u, u + 1, u, u} _ _ _ _ _
    (representedToZariskiRingedToposSiteHom B S hS U).u _ _ _ _ _
    (representedEpsilonPushforwardSquare_commutes B S hS φ) rfl rfl
    (representedEpsilonModulePushforward_eq B S hS (U := U))
    (representedEpsilonNaiveCotangentPushforwardMap B S hS φ)
    (heq_of_eq (representedEpsilonNaiveCotangentPushforwardMap_eq B S hS φ)) T
    (representedEpsilonCokernelHom B S hS φ) (π_comp_representedEpsilonCokernelHom B S hS φ)

end AlgebraicGeometry.Space

end
