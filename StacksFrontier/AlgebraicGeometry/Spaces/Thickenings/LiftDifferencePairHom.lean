module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseVanishingPair

/-!
# The difference of two morphisms agreeing on a thickening, as a map on differentials

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `W₀ ⊆ W` be a
closed subspace with inclusion `j`, let `e₀ : Z ⟶ W₀`, and let `c, c' : X ⟶ W` restrict on `Z`
to one and the same `e₀ ≫ j` and agree over a morphism `qb : W ⟶ Bas`.  This file produces the

`θ : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}`

by which they differ — the direction of [Stacks Project, Tag 0618] together with Equation
[Stacks Project, Tag 0619] which goes *from a pair of morphisms to a linear map*, and the one
simple transitivity of [Stacks Project, Tag 061C] needs on top of the direction that goes from a
linear map to a second morphism.

## Main definitions

* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom`: **the `θ` of the pair `(c, c')`.**

## Main results

* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_eq`: the defining equation of `θ`, so
  that a consumer rewrites with it instead of making unification delta-reduce the composite.
* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_self`: **a morphism does not differ from
  itself**, `θ(c, c) = 0`.  This is the field `equiv_self` of
  `AlgebraicGeometry.Space.LiftDerivationAction` read at this difference.
* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_add`: **the cocycle identity**,
  `θ(c₁, c₂) + θ(c₂, c₃) = θ(c₁, c₃)`.  This is the field `equiv_add_equiv` of
  `AlgebraicGeometry.Space.LiftDerivationAction` read at this difference.

## Implementation notes

The base datum of the descent is the composite `j ≫ qb : W₀ ⟶ Bas`, not a morphism
`b : W₀ ⟶ Bas₀` fitting a square `j ≫ qb = b ≫ iB`.  Taking the composite is what makes the
hypothesis `hz` of the descent available: it is
`AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero`,
and nothing has to be transported across a square.  A consumer which has a square can read `θ`
at `b` by the comparison of [Stacks Project, Tag 03G8],
`AlgebraicGeometry.Space.app_structureSharpInverseImage_square`.

Both hypotheses of the descent are passed **bare**, never eta-expanded: `hker` as the datum asks
for it and the `hz` lemma applied to its arguments.  Writing either as `fun V s ↦ …` causes a
`whnf` timeout in this area.

**Nothing is left to unification that an equation can carry instead.**  The two comorphisms of
the datum are read off by the `rfl` equations
`AlgebraicGeometry.Space.restrictedLiftDifferenceData_f` and
`AlgebraicGeometry.Space.restrictedLiftDifferenceData_g`, and the composite itself by
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom_eq`; the two identities below rewrite with
the latter before applying the descent lemma, so that the goal is already the lemma's statement
and the match is syntactic.  This matters for the cocycle identity, whose two sides carry an
addition on a hom-set of sheaves of modules: `exact` against an unrewritten goal leaves that
addition's instance to be compared across two elaborations and reports
`(deterministic) timeout at isDefEq`, whereas after the rewrite the comparison is between one
and the same term.  No compiler option is set and no budget is raised.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the equation presenting
  it as a map on differentials.
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C), the action this serves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W Bas : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (qb : W ⟶ Bas)

/-- **The linear map `θ : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}` by which two morphisms agreeing on the
thickening and over `qb` differ.**  This is
[Stacks Project, Tag 0618] together with Equation [Stacks Project, Tag 0619], in the direction
from a pair of morphisms to a linear map.

The pair of comorphisms is `AlgebraicGeometry.Space.restrictedLiftDifferenceData` and the descent
is `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom`; its two hypotheses are the datum's
own `hker` and
`AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero`.
-/
@[stacks 0619 "the linear map attached to the derivation by which the two comorphisms differ"]
abbrev restrictedLiftDifferenceHom (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
    (hcc : c ≫ qb = c' ≫ qb) :
    (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
      conormalModule B S hS X Z :=
  liftDifferenceDifferentialsHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb) e₀
    (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c c' h h' hker qb hcc)

/-- The defining equation of `AlgebraicGeometry.Space.restrictedLiftDifferenceHom`, so that
consumers rewrite with it rather than make unification delta-reduce the composite inside a
sum. -/
theorem restrictedLiftDifferenceHom_eq (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
    (hcc : c ≫ qb = c' ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hker hcc =
      liftDifferenceDifferentialsHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb) e₀
        (conormalModule B S hS X Z)
        (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker)
        (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
          B S hS Z W₀ hZ e₀ c c' h h' hker qb hcc) :=
  rfl

/-- The first comorphism of `AlgebraicGeometry.Space.restrictedLiftDifferenceData`, as an
equation. -/
theorem restrictedLiftDifferenceData_f (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x) :
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).f =
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ h :=
  rfl

/-- The second comorphism of `AlgebraicGeometry.Space.restrictedLiftDifferenceData`, as an
equation. -/
theorem restrictedLiftDifferenceData_g (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x) :
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).g =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' :=
  rfl

/-- **A morphism does not differ from itself:** the linear map of the pair `(c, c)` is zero.

The two maps of `AlgebraicGeometry.Space.restrictedLiftDifferenceData` at that pair are the same
transported comorphism, so `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_eq_zero`
applies.

This is the field `equiv_self` of `AlgebraicGeometry.Space.LiftDerivationAction` read at this
difference. -/
theorem restrictedLiftDifferenceHom_self (c : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
    (hcc : c ≫ qb = c ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c h h hker hcc = 0 := by
  rw [restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c c h h hker hcc]
  exact liftDifferenceDifferentialsHom_eq_zero B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c h h hker)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c c h h hker qb hcc)
    ((restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c c h h hker).trans
      (restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c c h h hker).symm)

/-- **The cocycle identity:** the linear maps of three morphisms add along the chain,
`θ(c₁, c₂) + θ(c₂, c₃) = θ(c₁, c₃)`.

The three pairs of transported comorphisms are `(f₁, f₂)`, `(f₂, f₃)` and `(f₁, f₃)` inside one
and the same square-zero ideal, so
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_add` applies with all three of its
index equations holding by `AlgebraicGeometry.Space.restrictedLiftDifferenceData_f` and
`AlgebraicGeometry.Space.restrictedLiftDifferenceData_g`.

This is the field `equiv_add_equiv` of `AlgebraicGeometry.Space.LiftDerivationAction` read at
this difference. -/
theorem restrictedLiftDifferenceHom_add (c₁ c₂ c₃ : X ⟶ W)
    (h₁ : subspaceInclusion B S hS X Z ≫ c₁ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₂ : subspaceInclusion B S hS X Z ≫ c₂ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₃ : subspaceInclusion B S hS X Z ≫ c₃ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker₁₂ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₁ e₀ h₁).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c₂ e₀ h₂).hom.app V x)
    (hker₂₃ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₂ e₀ h₂).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c₃ e₀ h₃).hom.app V x)
    (hker₁₃ : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₁ e₀ h₁).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c₃ e₀ h₃).hom.app V x)
    (hcc₁₂ : c₁ ≫ qb = c₂ ≫ qb) (hcc₂₃ : c₂ ≫ qb = c₃ ≫ qb)
    (hcc₁₃ : c₁ ≫ qb = c₃ ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₁ c₂ h₁ h₂ hker₁₂ hcc₁₂ +
        restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₂ c₃ h₂ h₃ hker₂₃ hcc₂₃ =
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₁ c₃ h₁ h₃ hker₁₃ hcc₁₃ := by
  rw [restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₁ c₂ h₁ h₂ hker₁₂ hcc₁₂,
    restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₂ c₃ h₂ h₃ hker₂₃ hcc₂₃,
    restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₁ c₃ h₁ h₃ hker₁₃ hcc₁₃]
  exact liftDifferenceDifferentialsHom_add B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c₁ c₂ h₁ h₂ hker₁₂)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c₂ c₃ h₂ h₃ hker₂₃)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c₁ c₃ h₁ h₃ hker₁₃)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c₁ c₂ h₁ h₂ hker₁₂ qb hcc₁₂)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c₂ c₃ h₂ h₃ hker₂₃ qb hcc₂₃)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c₁ c₃ h₁ h₃ hker₁₃ qb hcc₁₃)
    ((restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c₁ c₂ h₁ h₂ hker₁₂).trans
      (restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c₂ c₃ h₂ h₃ hker₂₃).symm)
    ((restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c₁ c₂ h₁ h₂ hker₁₂).trans
      (restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c₁ c₃ h₁ h₃ hker₁₃).symm)
    ((restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c₂ c₃ h₂ h₃ hker₂₃).trans
      (restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c₁ c₃ h₁ h₃ hker₁₃).symm)

end AlgebraicGeometry.Space

end
