module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalkMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero of abelian sheaves along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Extension by zero
`f_!` of abelian sheaves on the small étale sites is a left adjoint, so it is additive and right
exact; it is also left exact, hence exact.

## Main results

* `AlgebraicGeometry.Space.EtaleShriekStalk.mono_sheafFiber_extensionByZero_map`: the stalk of
  an extension by zero of a monomorphism is a monomorphism.
* `AlgebraicGeometry.Space.preservesMonomorphisms_abelianEtaleExtensionByZero`: extension by
  zero preserves monomorphisms.
* `AlgebraicGeometry.Space.preservesFiniteLimits_abelianEtaleExtensionByZero`: extension by zero
  of abelian sheaves along an étale morphism of algebraic spaces is left exact.
* `AlgebraicGeometry.Space.abelianEtaleExtensionByZero_exact`: it is exact.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace EtaleShriekStalk

/-- A coproduct of monomorphisms of abelian groups is a monomorphism. -/
theorem mono_sigmaFunctor_map {α : Type u} {K K' : α → AddCommGrpCat.{u}}
    [HasCoproductsOfShape α AddCommGrpCat.{u}] (p : K ⟶ K')
    (hp : ∀ a, Mono (p a)) : Mono ((Sigma.functor α).map p) :=
  inferInstanceAs (Mono (CategoryTheory.Limits.Sigma.map p))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (x : GeometricPoint B S hS Y.1)

/-- If a morphism of abelian sheaves on `X` has monomorphic stalks at every lift of a geometric
point `x` of `Y`, then the stalk at `x` of its extension by zero is a monomorphism. -/
@[stacks 08GU "the stalk of an extension by zero of a monomorphism"]
theorem mono_sheafFiber_extensionByZero_map
    {G H : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (ψ : G ⟶ H)
    (hψ : ∀ t : GeometricPointLift B S hS f.hom x,
      Mono ((liftSitePoint B S hS f t).sheafFiber.map ψ)) :
    Mono ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZero B S hS f hf).map ψ)) :=
  @mono_of_mono_fac _ _ _ _ _ _ _ _
    (mono_comp' (inferInstance : Mono (stalkExtensionByZeroIso B S hS f hf x G).hom)
      (mono_sigmaFunctor_map ((stalkFamily B S hS f x).map ψ) hψ))
    (stalkExtensionByZeroIso_naturality B S hS f hf x ψ)

end EtaleShriekStalk

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- Restriction of abelian étale sheaves along an étale morphism of algebraic spaces is
additive. -/
instance abelianEtaleRestriction_additive :
    (abelianEtaleRestriction B S hS f hf).Additive :=
  ⟨by intros; rfl⟩

/-- Extension by zero of abelian étale sheaves is additive. -/
instance abelianEtaleExtensionByZero_additive :
    (abelianEtaleExtensionByZero B S hS f hf).Additive :=
  (abelianEtaleExtensionByZeroAdjunction B S hS f hf).left_adjoint_additive

/-- Extension by zero of abelian étale sheaves preserves monomorphisms. -/
instance preservesMonomorphisms_abelianEtaleExtensionByZero :
    (abelianEtaleExtensionByZero B S hS f hf).PreservesMonomorphisms where
  preserves {G H} ψ hψ := by
    refine (((isConservativeFamilyOfPoints_etaleSitePoint B S hS Y.1
      Y.2).jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono_iff _).2 fun Φ => ?_
    obtain ⟨Φ, hΦ⟩ := Φ
    obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
    exact EtaleShriekStalk.mono_sheafFiber_extensionByZero_map B S hS f hf x ψ fun _ =>
      inferInstance

/-- Extension by zero of abelian sheaves along an étale morphism of algebraic spaces is left
exact. -/
@[stacks 03DJ "left exactness for abelian sheaves along an étale morphism of algebraic spaces"]
instance preservesFiniteLimits_abelianEtaleExtensionByZero :
    PreservesFiniteLimits (abelianEtaleExtensionByZero B S hS f hf) := by
  have : PreservesColimitsOfSize.{0, 0} (abelianEtaleExtensionByZero B S hS f hf) :=
    (abelianEtaleExtensionByZeroAdjunction B S hS f hf).leftAdjoint_preservesColimits
  have : (abelianEtaleExtensionByZero B S hS f hf).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

/-- Extension by zero of abelian sheaves along an étale morphism of algebraic spaces is
exact. -/
@[stacks 03DJ "exactness for abelian sheaves along an étale morphism of algebraic spaces"]
theorem abelianEtaleExtensionByZero_exact :
    exactFunctor _ _ (abelianEtaleExtensionByZero B S hS f hf) := by
  have : PreservesColimitsOfSize.{0, 0} (abelianEtaleExtensionByZero B S hS f hf) :=
    (abelianEtaleExtensionByZeroAdjunction B S hS f hf).leftAdjoint_preservesColimits
  rw [exactFunctor_iff]
  exact ⟨inferInstance, PreservesColimitsOfSize.preservesFiniteColimits _⟩

end AlgebraicGeometry.Space

end
