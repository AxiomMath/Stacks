module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback

/-!
# Extension by zero of modules along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. Restriction of modules along `f` is `AlgebraicGeometry.Space.etaleModulePullback`,
restriction along postcomposition of étale charts. This file constructs its left adjoint,
*extension by zero* `f_!`, the lower shriek of the morphism of ringed topoi attached to `f`, with
the module sections in the universe `u` of the schemes.

## Main definitions

* `AlgebraicGeometry.Space.etaleModuleLowerShriek` is `f_! : Mod(𝒪_X) ⥤ Mod(𝒪_Y)`.
* `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction` is the adjunction `f_! ⊣ f^*`.

## Main results

* `AlgebraicGeometry.Space.isRightAdjoint_etaleModulePullback`: restriction of modules along an
  étale morphism of algebraic spaces has a left adjoint.
* `AlgebraicGeometry.Space.etaleModuleLowerShriek_additive` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_etaleModuleLowerShriek`: extension by zero is
  additive and preserves finite colimits.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Restriction of modules along an étale morphism of algebraic spaces has a left adjoint, with
the module sections in the universe `u` of the schemes. -/
theorem isRightAdjoint_etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).IsRightAdjoint := by
  have h₁ : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS X.1))
  have h₂ : LocallySmall.{u} (smallEtaleRingedSite B S hS Y.1 Y.2).C :=
    inferInstanceAs (LocallySmall.{u} (SmallEtale B S hS Y.1))
  have h₃ : HasWeakSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})
  have h₄ : (smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS Y.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  unfold etaleModulePullback
  exact @SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall.{u, u, u, u + 1, u + 1}
    _ _ _ _ h₁ h₂ (smallEtaleRingedSite B S hS X.1 X.2).J
    (smallEtaleRingedSite B S hS Y.1 Y.2).J (smallEtalePostcomp B S hS f hf)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf) _ _ _ h₃ h₄

/-- Restriction of modules along an étale morphism of algebraic spaces has a left adjoint. -/
instance instIsRightAdjointEtaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).IsRightAdjoint :=
  isRightAdjoint_etaleModulePullback B S hS f hf

/-- Extension by zero along an étale morphism `f : X ⟶ Y` of algebraic spaces: the lower
shriek `f_! : Mod(𝒪_X) ⥤ Mod(𝒪_Y)`, the left adjoint of restriction of modules along `f`. -/
def etaleModuleLowerShriek (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  (etaleModulePullback.{u, u} B S hS f hf).leftAdjoint

/-- Extension by zero is left adjoint to restriction of modules along an étale morphism of
algebraic spaces: `f_! ⊣ f^*`, with unit `M ⟶ (f_! M)|_X` and counit `f_!(N|_X) ⟶ N`. -/
def etaleModuleLowerShriekAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    etaleModuleLowerShriek B S hS f hf ⊣ etaleModulePullback.{u, u} B S hS f hf :=
  Adjunction.ofIsRightAdjoint (etaleModulePullback.{u, u} B S hS f hf)

/-- Extension by zero along an étale morphism of algebraic spaces is a left adjoint. -/
instance isLeftAdjoint_etaleModuleLowerShriek (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModuleLowerShriek B S hS f hf).IsLeftAdjoint :=
  (etaleModuleLowerShriekAdjunction B S hS f hf).isLeftAdjoint

/-- Extension by zero along an étale morphism of algebraic spaces is additive. -/
instance etaleModuleLowerShriek_additive (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModuleLowerShriek B S hS f hf).Additive :=
  letI : (etaleModulePullback.{u, u} B S hS f hf).Additive := { map_add := rfl }
  (etaleModuleLowerShriekAdjunction B S hS f hf).left_adjoint_additive

/-- Extension by zero along an étale morphism of algebraic spaces preserves finite colimits. -/
instance preservesFiniteColimits_etaleModuleLowerShriek (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    PreservesFiniteColimits (etaleModuleLowerShriek B S hS f hf) :=
  letI : PreservesColimitsOfSize.{0, 0} (etaleModuleLowerShriek B S hS f hf) :=
    (etaleModuleLowerShriekAdjunction B S hS f hf).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

end AlgebraicGeometry.Space

end
