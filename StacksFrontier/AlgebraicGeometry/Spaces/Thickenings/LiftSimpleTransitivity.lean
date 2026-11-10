module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferencePairHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningLiftMovedSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpFaithful

/-!
# The lifts of a morphism over a thickening are simply transitive under the linear maps

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `W₀ ⊆ W` be a
closed subspace with inclusion `j`, let `e₀ : Z ⟶ W₀`, and let `qb : W ⟶ Bas`.  For a morphism
`c₀ : X ⟶ W` restricting on `Z` to `e₀ ≫ j` the companions of `c₀` are the morphisms
`c : X ⟶ W` which restrict on `Z` to the same `e₀ ≫ j`, agree with `c₀` over `Bas`, and induce
the same map of conormal modules as `c₀` does — hypotheses (1) and (2) of
[Stacks Project, Tag 0618].  Each such `c` has a difference

`θ(c₀, c) : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}`,

`AlgebraicGeometry.Space.restrictedLiftDifferenceHom`.  **This file proves that `c ↦ θ(c₀, c)`
is a bijection**, which is [Stacks Project, Tag 04D0] and the simple transitivity of
[Stacks Project, Tag 061C] read at one object of the étale site.

## Main results

* `AlgebraicGeometry.Space.eq_of_restrictedLiftDifferenceHom_eq`: **the difference determines
  the companion.**  Two companions of `c₀` with the same difference from `c₀` are equal.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_movedThickeningLift`:
  hypothesis (2) of [Stacks Project, Tag 0618] for a morphism realizing the moved solution.
* `AlgebraicGeometry.Space.restrictedLiftDifferenceHom_eq_of_movedThickeningLift`: the
  difference of `c₀` and such a morphism is the linear map the solution was moved by.
* `AlgebraicGeometry.Space.exists_hom_restrictedLiftDifferenceHom_eq`: **every linear map is a
  difference.**  For every `θ` there is a companion of `c₀` whose difference from `c₀` is `θ`.
* `AlgebraicGeometry.Space.existsUnique_hom_restrictedLiftDifferenceHom_eq`: **Stacks 04D0**,
  the two together: for every `θ` there is exactly one companion of `c₀` whose difference from
  `c₀` is `θ`.

## Implementation notes

**This is the unconditional form of [Stacks Project, Tag 04D0].**  The tag is also registered
in `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/MorphismFromStructureMap.lean`, on the
route through `AlgebraicGeometry.Space.existsUnique_hom_of_derivationModification`, which
carries two hypotheses of its own: `AlgebraicGeometry.Space.DerivationModification`, and that
the canonical morphism `S ⟶ Spec Γ(S, ⊤)` of the base scheme is a monomorphism — an affine or
quasi-affine base — which is what makes
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` — [Stacks Project, Tag 04KL] over a base —
a theorem there (`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_mono_toSpecΓ`); over a
base scheme outside that class that route has nothing to say.  The route taken here carries
neither
and needs no hypothesis on the base; the recovery of a morphism from its comorphism is replaced
by the chart-level argument of
`AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf` for existence and by
`AlgebraicGeometry.Space.eq_of_structureSharpThroughThickeningAt_eq` for uniqueness.

**Uniqueness** is the cocycle identity followed by two injectivity statements.  From
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom_add` and
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom_self` the difference of the two companions
is `θ(c, c₀) + θ(c₀, c') = θ(c, c₀) + θ(c₀, c) = θ(c, c) = 0`; a pair of lifts with zero
descended difference has equal comorphisms by
`AlgebraicGeometry.Space.eq_of_liftDifferenceDifferentialsHom_eq_zero`, and two morphisms
agreeing on a first order thickening with equal transported comorphisms are equal by
`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`.  Neither step needs
[Stacks Project, Tag 04KL] nor the identification of the small étale topoi of the thickening.

**Existence** is the morphism realizing the moved solution,
`AlgebraicGeometry.Space.exists_hom_of_movedThickeningLift`, together with the identification
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_eq_movedThickeningLift_g` of its
transported comorphism.  Two things then come for free.  Hypothesis (2) of
[Stacks Project, Tag 0618] for the pair `(c₀, ε)` is the field `app_eq_of_app_eq_zero` of the
moved solution, which `Stacks.Sites.derivationActionData` discharges with no generating family:
the correction term is read off `j^♯`, and an additive map kills the zero section.  And the
difference `θ(c₀, ε)` is `θ` by the additivity
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_add` of the descent, applied to the
three pairs `(c₀^♯, ε^♯)`, `(ε^♯, ε^♯)` and `(c₀^♯, ε^♯)` — the first read as the moved
solution, whose descended difference is `θ` by
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`, and the
second as a pair of equal maps, whose descended difference is zero.  So no congruence of the
descent along an equality of pairs is needed, and none is stated.

**The ambient base of the moved solution is not thickened.**  The results about the moved
solution are stated for a square `j ≫ qb = b ≫ iB` with `b : W₀ ⟶ Bas₀` over a second base;
here `b` is taken to be `j ≫ qb` itself and `iB` the identity, which is the situation of
[Stacks Project, Tag 04D0]: the base `B` of the source carries no thickening, and the sheaf of
differentials in play is `Ω_{W₀/Bas}`.  So no transport along [Stacks Project, Tag 03G8] is
needed, and the `θ` of this file is the `θ` of
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom` with no comparison in between.

## Scope: what this is *not*

This is not [Stacks Project, Tag 061C].  That tag asks for an action of the *sheaf*
`Hom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` on the *sheaf* (061B) of
[Stacks Project, Tag 061A], simply transitive over every object of the étale site carrying a
section.  What is proved here is the bijection at one object, with the data of the thickening
and of the lifting problem given outright; the acting group is the group of global
`𝒪`-linear maps and not the sections of the acting sheaf
`AlgebraicGeometry.Space.liftActionSheaf`.

**Two of the three bridges this section used to call missing are not owed at all, and the third
is now built.**  The three were stated for relativisation to an object `V` of the *small* étale
site of `X`.  But the sheaf of lifts of [Stacks Project, Tag 061A] lives on the *spaces-étale*
site, and over that site the first two are free.  An object of
`AlgebraicGeometry.Space.SpacesEtale` already *is* an algebraic space together with an étale
morphism to the ambient space — that category is a full subcategory of `Over X'` — so no chart
has to be turned into a space and `AlgebraicGeometry.Space.chartSpace` is not needed; and
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`, [Stacks Project, Tag 09ZX], holds
along an arbitrary morphism of algebraic spaces, so it applies to the structure morphism of such
an object directly.  The third — the identification of the preimage subspace with the
categorical base change that `AlgebraicGeometry.Space.liftSubfunctor` is defined through — is
`AlgebraicGeometry.Space.thickeningPreimageIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftActionSheaf.lean`, and the sheaf statement
of [Stacks Project, Tag 061C] is carried out there and in
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftActionNaturality.lean`, unconditionally:
`AlgebraicGeometry.Space.conormalLiftSheafAddAction_bijective` and
`AlgebraicGeometry.Space.conormalLiftAction_map`.

The compatibility of the action with étale localization is [Stacks Project, Tag 0CK8]; for
algebraic spaces it is `AlgebraicGeometry.Space.restrictedLiftAction_comp_etaleLocalization` of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftEtaleLocalizationAction.lean`, the
algebraic-space form of [Stacks Project, Tag 04BY].

Of the chart reading of the differentials **both halves are stocked**, and only the assembly
across the slice is not: the
conormal half is `AlgebraicGeometry.Space.isIso_conormalMap_of_isEtale` together with
`AlgebraicGeometry.Space.conormalMap_comp`, and the differentials half — recorded here until
now as not stated, which was wrong — is the comparison of inverse images along a composite,
[Stacks Project, Tag 03LU], read at the sheaf of differentials:
`(AlgebraicGeometry.Space.modulePullbackCompIso B S hS p e₀).app`
`(AlgebraicGeometry.Space.sheafOfDifferentials B S hS (j ≫ qb))` is
`p^*(e₀^*Ω_{W₀/Bas}) ≅ (p ≫ e₀)^*Ω_{W₀/Bas}`, whose right-hand side is already the domain of
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom` at the chart.  Being a pullback of a
module on the undeformed target, `e₀^*Ω_{W₀/Bas}` needs no étaleness of the projection `p` for
this, which is why this half is a bare instance of Tag 03LU while the conormal half is not; and
for that reason no declaration is added for it, a specialization being only a second name for
Tag 03LU's comparison.

In the one case where the target is not deformed — Remark [Stacks Project, Tag 061D], `W₀` the
top closed subspace — hypothesis (2) of [Stacks Project, Tag 0618] needs no reference morphism
at all: it is `AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_top`, which
is already in the tree and is written in exactly the curried shape the hypothesis asks for.
The results below are not specialised to that case, because the general target is what
[Stacks Project, Tag 04D0] and [Stacks Project, Tag 061C] are stated at.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), the tag proved here.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts, and the two hypotheses that cut out the companions of `c₀`.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the equation
  presenting that difference as a map on differentials.
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A), the sheaf of lifts the
  pseudo-torsor acts on.
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C), the pseudo-torsor this
  serves; see "Scope" above for what is still owed.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the case of an
  undeformed target.
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL), which this route does
  not use.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the differentials half
  of the chart reading named in "Scope".
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

/-- **The difference determines the companion:** two morphisms which restrict on the thickening
to the same morphism, agree with `c₀` over `Bas`, induce the same map of conormal modules as
`c₀` does, and have the same difference from `c₀`, are equal.

This is the uniqueness clause of [Stacks Project, Tag 04D0], and it is unconditional: the
cocycle identity makes the difference of the two zero, a pair of lifts with zero descended
difference has equal comorphisms by
`AlgebraicGeometry.Space.eq_of_liftDifferenceDifferentialsHom_eq_zero`, and
`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq` recovers the equality of
the two morphisms from that. -/
@[stacks 04D0 "the uniqueness clause: a companion of the given morphism of thickenings is \
determined by its difference"]
theorem eq_of_restrictedLiftDifferenceHom_eq (c₀ c c' : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
    (hker' : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
    (hcc : c₀ ≫ qb = c ≫ qb) (hcc' : c₀ ≫ qb = c' ≫ qb)
    (heq : restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ c h₀ h hker hcc =
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ c' h₀ h' hker' hcc') :
    c = c' := by
  have hkerD : ∀ (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x :=
    fun V x hx => (hker V x hx).symm.trans (hker' V x hx)
  -- The chain `c, c₀, c'` gives `θ(c, c₀) + θ(c₀, c') = θ(c, c')`, and the chain `c, c₀, c`
  -- gives `θ(c, c₀) + θ(c₀, c) = 0`.  With `heq` the two left-hand sides agree.
  have hzero : restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c c' h h' hkerD
      (hcc.symm.trans hcc') = 0 := by
    rw [← restrictedLiftDifferenceHom_add B S hS Z W₀ hZ e₀ qb c c₀ c' h h₀ h'
      (fun V x hx => (hker V x hx).symm) hker' hkerD hcc.symm hcc' (hcc.symm.trans hcc'), ← heq,
      restrictedLiftDifferenceHom_add B S hS Z W₀ hZ e₀ qb c c₀ c h h₀ h
        (fun V x hx => (hker V x hx).symm) hker (fun _ _ _ => rfl) hcc.symm hcc rfl]
    exact restrictedLiftDifferenceHom_self B S hS Z W₀ hZ e₀ qb c h (fun _ _ _ => rfl) rfl
  rw [restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c c' h h' hkerD
    (hcc.symm.trans hcc')] at hzero
  refine eq_of_restrictedSharpThroughThickening_eq B S hS Z hZ W₀ c c' e₀ h h' ?_
  refine Eq.trans ?_ (restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c c' h h' hkerD)
  refine Eq.trans (restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c c' h h' hkerD).symm ?_
  exact eq_of_liftDifferenceDifferentialsHom_eq_zero B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hkerD)
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c c' h h' hkerD qb (hcc.symm.trans hcc')) hzero

/-- **Hypothesis (2) of [Stacks Project, Tag 0618] for a morphism realizing the moved
solution.**  If the transported comorphism of `ε` is the solution that the transported
comorphism of `c₀` is moved to by `θ`, then the two transported comorphisms agree on every
section killed by `j^♯`.

Nothing has to be proved: this is the field `app_eq_of_app_eq_zero` of
`AlgebraicGeometry.Space.movedThickeningLift`, which
`Stacks.Sites.derivationActionData` discharges with no generating family — the correction term
is read off `j^♯`, and an additive map kills the zero section. -/
theorem restrictedSharpThroughThickening_app_eq_of_movedThickeningLift (c₀ ε : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hres : subspaceInclusion B S hS X Z ≫ ε = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
      conormalModule B S hS X Z)
    (hgid : restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres =
      (movedThickeningLift B S hS Z W₀ hZ c₀ e₀ h₀
        (subspaceInclusion B S hS W W₀ ≫ qb) θ).g)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
      (restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres).hom.app V x := by
  rw [hgid]
  exact (movedThickeningLift B S hS Z W₀ hZ c₀ e₀ h₀
    (subspaceInclusion B S hS W W₀ ≫ qb) θ).app_eq_of_app_eq_zero x hx

/-- **The difference of `c₀` and a morphism realizing the moved solution is `θ`.**

The additivity `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_add` of the descent is
applied to the three pairs of transported comorphisms `(c₀^♯, ε^♯)`, `(ε^♯, ε^♯)` and
`(c₀^♯, ε^♯)`, the first read as `AlgebraicGeometry.Space.movedThickeningLift` — whose
descended difference is `θ` by
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom` — and the
second as a pair of equal maps, whose descended difference is zero.  So the descent is never
transported along an equality of pairs, and no congruence for it is needed. -/
theorem restrictedLiftDifferenceHom_eq_of_movedThickeningLift (c₀ ε : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hres : subspaceInclusion B S hS X Z ≫ ε = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
      conormalModule B S hS X Z)
    (hgid : restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres =
      (movedThickeningLift B S hS Z W₀ hZ c₀ e₀ h₀
        (subspaceInclusion B S hS W W₀ ≫ qb) θ).g)
    (hcc : c₀ ≫ qb = ε ≫ qb) :
    restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ ε h₀ hres
        (restrictedSharpThroughThickening_app_eq_of_movedThickeningLift
          B S hS Z W₀ hZ e₀ qb c₀ ε h₀ hres θ hgid) hcc = θ := by
  have hε := restrictedSharpThroughThickening_app_eq_of_movedThickeningLift
    B S hS Z W₀ hZ e₀ qb c₀ ε h₀ hres θ hgid
  have hrfl : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres).hom.app V x =
          (restrictedSharpThroughThickening B S hS Z W₀ ε e₀ hres).hom.app V x :=
    fun _ _ _ => rfl
  have hD := descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
    B S hS Z W₀ hZ e₀ ε ε hres hres hrfl qb rfl
  have hfε := restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ ε ε hres hres hrfl
  have hgε := restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ ε ε hres hres hrfl
  have hf := restrictedLiftDifferenceData_f B S hS Z W₀ hZ e₀ c₀ ε h₀ hres hε
  have hg := restrictedLiftDifferenceData_g B S hS Z W₀ hZ e₀ c₀ ε h₀ hres hε
  have hL₁ := liftDifferenceDifferentialsHom_liftDifferenceDataOfHom B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c₀ h₀ x m) θ
  have hL₂ := liftDifferenceDifferentialsHom_eq_zero B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ ε ε hres hres hrfl) hD (hfε.trans hgε.symm)
  have hadd := liftDifferenceDifferentialsHom_add B S hS
    (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
    (liftDifferenceDataOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ qb) e₀
      (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c₀ h₀ x m) θ)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ ε ε hres hres hrfl)
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c₀ ε h₀ hres hε)
    (liftDifferenceDataOfHom_descend_eq_zero B S hS
      (subspaceInclusion B S hS W W₀ ≫ qb) e₀ (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c₀ h₀ x m) θ) hD
    (descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c₀ ε h₀ hres hε qb hcc)
    (hgid.symm.trans hfε.symm) hf.symm (hgε.trans hg.symm)
  refine (restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₀ ε h₀ hres hε hcc).trans ?_
  rw [← hadd, hL₁, hL₂, add_zero]

/-- **Every linear map is a difference.**  For an `𝒪_Z`-linear map
`θ : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}` there is a morphism `c : X ⟶ W` restricting on the thickening
to `e₀ ≫ j`, agreeing with `c₀` over `Bas`, inducing the same map of conormal modules as `c₀`
does, and whose difference from `c₀` is `θ`.

This is the existence clause of [Stacks Project, Tag 04D0], and it is unconditional:
`AlgebraicGeometry.Space.exists_hom_of_movedThickeningLift` produces the morphism and
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_eq_movedThickeningLift_g` identifies
its transported comorphism with the moved solution. -/
@[stacks 04D0 "the existence clause: every linear map out of the pulled back differentials is \
the difference of the given morphism of thickenings and a second one"]
theorem exists_hom_restrictedLiftDifferenceHom_eq (c₀ : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
      conormalModule B S hS X Z) :
    ∃ (c : X ⟶ W)
      (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
      (hker : ∀ (V : (SmallEtale B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
          (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
      (hcc : c₀ ≫ qb = c ≫ qb),
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ c h₀ h hker hcc = θ := by
  obtain ⟨ε, hεq, hεZ, hεchart⟩ := exists_hom_of_movedThickeningLift B S hS Z W₀ hZ c₀ e₀ h₀
    (subspaceInclusion B S hS W W₀ ≫ qb) θ qb (𝟙 Bas) (Category.comp_id _).symm (c₀ ≫ qb) rfl
  have hres : subspaceInclusion B S hS X Z ≫ (ObjectProperty.homMk ε : X ⟶ W) =
      e₀ ≫ subspaceInclusion B S hS W W₀ :=
    ObjectProperty.hom_ext _ (hεZ.trans (congrArg (fun k :
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W => k.hom) h₀))
  have hgid : restrictedSharpThroughThickening B S hS Z W₀
        (ObjectProperty.homMk ε : X ⟶ W) e₀ hres =
      (movedThickeningLift B S hS Z W₀ hZ c₀ e₀ h₀
        (subspaceInclusion B S hS W W₀ ≫ qb) θ).g :=
    restrictedSharpThroughThickening_eq_movedThickeningLift_g B S hS Z W₀ hZ c₀ e₀ h₀
      (subspaceInclusion B S hS W W₀ ≫ qb) θ qb (𝟙 Bas) (Category.comp_id _).symm
      (ObjectProperty.homMk ε) hres fun Q hQ jj ψ hψ => @hεchart Q hQ jj ψ hψ
  exact ⟨ObjectProperty.homMk ε, hres,
    restrictedSharpThroughThickening_app_eq_of_movedThickeningLift
      B S hS Z W₀ hZ e₀ qb c₀ (ObjectProperty.homMk ε) h₀ hres θ hgid,
    (ObjectProperty.hom_ext _ hεq).symm,
    restrictedLiftDifferenceHom_eq_of_movedThickeningLift B S hS Z W₀ hZ e₀ qb c₀
      (ObjectProperty.homMk ε) h₀ hres θ hgid (ObjectProperty.hom_ext _ hεq).symm⟩

/-- **Stacks 04D0.**  For a morphism `c₀ : X ⟶ W` restricting on the first order thickening
`Z ⊂ X` to `e₀` read through the inclusion of the closed subspace `W₀ ⊆ W`, and for an
`𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}`, there is **exactly one** morphism
`c : X ⟶ W` which restricts on `Z` to the same morphism, agrees with `c₀` over `Bas` and
induces the same map of conormal modules as `c₀` does — hypotheses (1) and (2) of
[Stacks Project, Tag 0618] — and whose difference from `c₀` is `θ`.

This is the whole of [Stacks Project, Tag 04D0], unconditionally: the existence clause is
`AlgebraicGeometry.Space.exists_hom_restrictedLiftDifferenceHom_eq` and the uniqueness clause
is `AlgebraicGeometry.Space.eq_of_restrictedLiftDifferenceHom_eq`.  It is also the simple
transitivity of [Stacks Project, Tag 061C] read at one object of the étale site, with the
acting group the global `𝒪_Z`-linear maps; see the "Scope" section of the module doc for the
relativisation that is still owed. -/
@[stacks 04D0 "the unique second morphism of thickenings with a prescribed difference, with no \
stand-in: the existence of the moved solution and the faithfulness of the transported \
comorphism replace the recovery of a morphism from its comorphism"]
theorem existsUnique_hom_restrictedLiftDifferenceHom_eq (c₀ : X ⟶ W)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e₀ ≫ subspaceInclusion B S hS W W₀)
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ qb)) ⟶
      conormalModule B S hS X Z) :
    ∃! c : X ⟶ W, ∃ (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
      (hker : ∀ (V : (SmallEtale B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
          (restrictedSharpThroughThickening B S hS Z W₀ c₀ e₀ h₀).hom.app V x =
            (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x)
      (hcc : c₀ ≫ qb = c ≫ qb),
      restrictedLiftDifferenceHom B S hS Z W₀ hZ e₀ qb c₀ c h₀ h hker hcc = θ := by
  obtain ⟨c, h, hker, hcc, hθ⟩ :=
    exists_hom_restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₀ h₀ θ
  refine ⟨c, ⟨h, hker, hcc, hθ⟩, ?_⟩
  rintro c' ⟨h', hker', hcc', hθ'⟩
  exact eq_of_restrictedLiftDifferenceHom_eq B S hS Z W₀ hZ e₀ qb c₀ c' c h₀ h' h hker' hker
    hcc' hcc (hθ'.trans hθ.symm)

end AlgebraicGeometry.Space

end
