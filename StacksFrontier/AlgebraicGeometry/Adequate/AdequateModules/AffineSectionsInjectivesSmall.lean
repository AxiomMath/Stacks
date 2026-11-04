module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSubsiteInjectives
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModulesExtensions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful

/-!
# The affine-section functor of a big site preserves injective objects

Let `U = Spec A` be affine and let `B` be a chosen big `τ`-site over `U`. The affine-section
functor `Stacks.Adequate.affineSectionsFunctor`, the functor `j` of the proof of
[Stacks, Tag 06ZS], carries injective sheaves of modules on the site to injective presheaves of
modules on the `A`-algebras of the site, at every module universe `max u m` above the universe
`u` of the site. This is the
injectives step of the proof of [Stacks, Tag 06ZU], which the source gets from
[Stacks, Tag 03FB].

## Main results

* `Stacks.DenseSubsiteModules.isEquivalence_pushforward` — restriction of sheaves of modules to a
  dense subsite followed by restriction of scalars along an isomorphism is an equivalence.
* `Stacks.Adequate.isEquivalence_pushforward_affineRingSheafMap` — restriction of sheaves of
  modules to the affine subsite along the scalar identification is an equivalence.
* `Stacks.Adequate.preservesInjectiveObjects_affineSectionsFunctor` — the affine-section functor
  preserves injective objects.

## References

* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 03FB](https://stacks.math.columbia.edu/tag/03FB)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u m w r u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
  (φ : S ⟶ (v.sheafPushforwardContinuous RingCat.{r} J K).obj R)

/-- **The Comparison Lemma for sheaves of modules along a dense subsite and a scalar
isomorphism.** Restriction of sections along `v` followed by restriction of scalars along an
isomorphism `φ` is an equivalence, given the Comparison Lemma for sheaves of abelian groups. The
universe `w` of the module sections is independent of the universe `r` of the sheaves of
rings. -/
public theorem isEquivalence_pushforward [IsIso φ]
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (SheafOfModules.pushforward.{w} φ).IsEquivalence := by
  have : (SheafOfModules.restrictScalars.{w} φ).IsEquivalence :=
    Stacks.SheafOfModules.RestrictScalars.isEquivalence φ
  have : (SheafOfModules.pushforward.{w} φ).EssSurj :=
    Functor.essSurj_comp (moduleRestriction' J K v R : SheafOfModules.{w} R ⥤ _)
      (SheafOfModules.restrictScalars.{w} φ)
  exact Functor.IsEquivalence.mk

end Pushforward

end Stacks.DenseSubsiteModules

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- Restriction of sheaves of modules to the affine subsite of a chosen big site, along the scalar
identification, is an equivalence, at every module universe `max u m` above the universe `u`
of the site. -/
public theorem isEquivalence_pushforward_affineRingSheafMap :
    (SheafOfModules.pushforward.{max u m} (affineRingSheafMap B)).IsEquivalence :=
  have := isEquivalence_affineSheafPushforwardContinuous.{u, m} B
  Stacks.DenseSubsiteModules.isEquivalence_pushforward (affineSubsiteTopology B) B.topology
    (affineSpecOver B A (𝟙 (Spec A))) (affineRingSheafMap B)

/-- **The affine-section functor of a chosen big site over an affine base preserves injective
objects**: it carries an injective sheaf of modules on the site to an injective presheaf of
modules on the `A`-algebras of the site, at every module universe `max u m` above the universe
`u` of the site. -/
public theorem preservesInjectiveObjects_affineSectionsFunctor :
    (affineSectionsFunctor.{u, max u m} B A (𝟙 (Spec A))).PreservesInjectiveObjects := by
  have := isEquivalence_pushforward_affineRingSheafMap.{u, m} B
  have := preservesInjectiveObjects_forget_affineAlgebraRingSheaf.{u, m} B
  exact inferInstanceAs (SheafOfModules.pushforward.{max u m} (affineRingSheafMap B) ⋙
    SheafOfModules.forget (affineAlgebraRingSheaf B)).PreservesInjectiveObjects

end Stacks.Adequate

end
