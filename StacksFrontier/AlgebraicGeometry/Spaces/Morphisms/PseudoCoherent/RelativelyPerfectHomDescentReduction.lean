module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The reduction of Stacks 0DKV to an affine situation

In Situation 0DKU fix `K₀, L₀ ∈ D(𝒪_{X₀})`.  Combining the two inductions
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_of_affine` with the comparison
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_extendRestrict_of_restrict`,
the conclusion of Stacks 0DKV for `(K₀, L₀)`, at every shift of `K₀`, follows from two inputs:

* the base change maps for extension by zero along the projections of the situation restricted
  along an étale `u : U₀ ⟶ X₀` are invertible, and
* the conclusion of the tag holds for `(Lu^*K₀, Lu^*L₀)` in the situation restricted along every
  étale `u : U₀ ⟶ X₀` with `U₀` affine whose composite `U₀ ⟶ Y₀` factors through an étale
  morphism from an affine algebraic space.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isFlat_of_isEtale_affine` and
  `isFinitePresentation_of_isEtale_affine`: an étale morphism from an affine algebraic space to
  `X₀` is flat and of finite presentation, so the situation can be restricted along it.
* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_of_restrict_affine`: the
  reduction.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

namespace RelativeDescentSituation

/- The conclusion of Stacks 0DKV,
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent`, and the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` it is built from are stated for the
standard model of the derived category, so the declarations below are stated at it too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I) (P : DerivedPullbackComposition B S hS)

/-- The space `X₀` of the situation is quasi-separated: it is of finite presentation over the
quasi-separated `Y₀`. -/
theorem initial_isAbsolutelyQuasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ D.X₀ :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ D.initial_isAlgebraicSpace
    (D.stage_isQuasiSeparated D.i₀) D.initial_isFinitePresentation.2.2

/-- An étale morphism into `X₀` is flat. -/
theorem isFlat_of_isEtale_affine {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : U₀ ⟶ D.X₀}
    (hg : IsEtale B S hS g) : IsFlat B S hS g :=
  isFlat_of_isEtale B S hS hg

/-- An étale morphism from an affine algebraic space into `X₀` is of finite presentation. -/
theorem isFinitePresentation_of_isEtale_affine {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAffineSpace B S hS U₀) {g : U₀ ⟶ D.X₀} (hg : IsEtale B S hS g) :
    IsFinitePresentation B S hS g :=
  ⟨isLocallyOfFinitePresentation_of_isEtale B S hS hg,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ D.initial_isAlgebraicSpace
      D.initial_isAbsolutelyQuasiSeparated hU₀.isQuasiCompactSpace g,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hU₀.isAlgebraicSpace
      (hU₀.isAbsolutelyQuasiSeparated B S hS hZ) g⟩

/-- **The reduction of Stacks 0DKV to an affine situation.**  Suppose that for every étale
`u : U₀ ⟶ X₀` with `U₀` affine whose composite `U₀ ⟶ Y₀` factors through an étale morphism from
an affine algebraic space, the base change maps for extension by zero along the projections of
the situation restricted along `u` are invertible, and the conclusion of the tag holds for
`(Lu^*K₀, Lu^*L₀)` in that restricted situation, at every shift.  Then the conclusion of the tag
holds for `(K₀, L₀)` at every shift. -/
theorem shiftedHomDescent_of_restrict_affine (K₀ L₀ : D.InitialDerived)
    (hleaf : ∀ {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAffineSpace B S hS U₀)
      (g : U₀ ⟶ D.X₀) (hg : IsEtale B S hS g)
      {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1),
        IsAffineSpace B S hS V.1 → IsEtale B S hS w.hom → t ≫ w.hom = g ≫ D.p₀ →
        (∀ (i : D.LaterIndex) (A : (D.restrict hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg)).InitialDerived),
          IsIso ((D.stageExtensionByZeroBaseChange P hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg) (D.isFinitePresentation_of_isEtale_affine hU₀ hg)
            hg i).app A)) ∧
        (∀ A : (D.restrict hU₀.isAlgebraicSpace g (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg)).InitialDerived,
          IsIso ((D.limitExtensionByZeroBaseChange P hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg) (D.isFinitePresentation_of_isEtale_affine hU₀ hg)
            hg).app A)) ∧
        (D.restrict hU₀.isAlgebraicSpace g (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg)).ShiftedHomDescent P
          ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj K₀)
          ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
            (D.isFlat_of_isEtale_affine hg)
            (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj L₀)) :
    D.ShiftedHomDescent P K₀ L₀ := by
  refine D.shiftedHomDescent_of_affine P K₀ L₀ fun {U} u hu hU {V} w t hV hw ht ↦ ?_
  obtain ⟨hβ, hβ', hE⟩ := hleaf hU u.hom hu w t hV hw ht
  exact D.shiftedHomDescent_extendRestrict_of_restrict P hU.isAlgebraicSpace u.hom
    (D.isFlat_of_isEtale_affine hu) (D.isFinitePresentation_of_isEtale_affine hU hu) hu K₀ L₀
    hβ hβ' hE

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
