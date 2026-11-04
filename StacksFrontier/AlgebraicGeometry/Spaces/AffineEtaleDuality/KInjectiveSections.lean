module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Sections
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Sections over an étale object preserve K-injectivity

For an object `V` of the small étale site of `Spec A`, the functor of sections over `V`, valued in
`A`-modules, carries K-injective complexes of `𝒪_étale`-modules to K-injective complexes of
`A`-modules.

Read through the slice adjunction, sections over `V` are the composite of restriction to the
slice over `V`, of the pushforward along `Over.star V`, and of global sections. Restriction to a
slice preserves K-injectivity over the essentially small étale site (Stacks 08FI at large
objects, `Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`); the other two
functors are right adjoints of exact functors — restriction to the slice, and `ε^*T` — so they
preserve K-injectivity by the adjoint criterion of Stacks 08BJ.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.isKInjective_secA`: sections over an object of the small
  étale site carry K-injective complexes to K-injective complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The functor `M ↦ ε^* M̃` from `A`-modules to `𝒪_étale`-modules preserves finite limits. -/
instance epsT_preservesFiniteLimits : PreservesFiniteLimits (epsT A B hX) := by
  have : PreservesFiniteLimits (tilde.functor A) := AlgebraicGeometry.tilde.preservesFiniteLimits A
  have : PreservesFiniteLimits (SmallEtale.associatedModule B (Spec A) hX) :=
    SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf B (Spec A) hX
  exact comp_preservesFiniteLimits (tilde.functor A) (SmallEtale.associatedModule B (Spec A) hX)

/-- The functor `M ↦ ε^* M̃` from `A`-modules to `𝒪_étale`-modules preserves finite colimits. -/
instance epsT_preservesFiniteColimits : PreservesFiniteColimits (epsT A B hX) := by
  have : PreservesFiniteColimits (tilde.functor A) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor A
  have : PreservesColimitsOfSize.{0, 0} (SmallEtale.associatedModule B (Spec A) hX) :=
    (SmallEtale.associatedModuleAdjunction B (Spec A) hX).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (SmallEtale.associatedModule B (Spec A) hX) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact comp_preservesFiniteColimits (tilde.functor A) (SmallEtale.associatedModule B (Spec A) hX)

/-- The functor `M ↦ ε^* M̃` from `A`-modules to `𝒪_étale`-modules is additive. -/
instance epsT_additive : (epsT A B hX).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The global sections functor from `𝒪_étale`-modules to `A`-modules is additive. -/
instance gammaTop_additive : (gammaTop A B hX).Additive :=
  (epsTAdj A B hX).right_adjoint_additive

/-- **Sections over an object of the small étale site preserve K-injectivity.** -/
theorem isKInjective_secA (V : Site A B hX)
    (J : CochainComplex (Mod A B hX) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
  let F₁ := SheafOfModules.overFunctor (O A B hX) V
  let F₂ := SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver
    (R := O A B hX) V)
  have : F₁.Additive :=
    Stacks.Cohomology.Localization.additive_overFunctor_of_essentiallySmall _ _ V
  have : F₂.Additive := (SheafOfModules.overPushforwardOverAdj V).right_adjoint_additive
  have h₁ : CochainComplex.IsKInjective ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall _ _ V J
  have : PreservesFiniteLimits F₁ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesColimitsOfSize.{0, 0} F₁ :=
    (SheafOfModules.overPushforwardOverAdj (R := O A B hX) V).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F₁ := PreservesColimitsOfSize.preservesFiniteColimits _
  have h₂ : CochainComplex.IsKInjective ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact F₂ F₁
      (SheafOfModules.overPushforwardOverAdj V) _
  have h₃ : CochainComplex.IsKInjective (((gammaTop A B hX).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact (gammaTop A B hX) (epsT A B hX)
      (epsTAdj A B hX) _
  have e : ((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J ≅
      ((gammaTop A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
    ((NatIso.mapHomologicalComplex (secVIso A B hX V) (ComplexShape.up ℤ)).app J).symm ≪≫
      HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact CochainComplex.isKInjective_of_iso e.symm

end AlgebraicGeometry.AffineEtaleDuality

end
