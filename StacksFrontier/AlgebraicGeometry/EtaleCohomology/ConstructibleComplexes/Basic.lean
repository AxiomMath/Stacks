module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Complexes of étale sheaves with constructible cohomology

For a scheme `X` and a Noetherian coefficient ring `Λ`, the constructible derived
category consists of complexes of étale sheaves of `Λ`-modules whose cohomology
sheaves are constructible.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructible` is the cohomological constructibility property
  on the unbounded derived category.
* `Stacks.EtaleCohomology.ConstructibleDerivedCategory` is the full subcategory on those
  objects.

## Implementation notes

The small étale site and constructibility of module sheaves are those of Tags 021B and
03RW. The coefficient sheaves are `ModuleCat`-valued sheaves. The full subcategory
retains the canonical inclusion into the unbounded derived category, while its defining
property lets clients test membership degree by degree. The standard localization
supplies the derived category; sheafification is assumed to obtain the abelian category
of module sheaves.

## References

* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- An object of the unbounded derived category of small-étale `Λ`-module
sheaves has constructible cohomology in every degree. -/
public abbrev IsConstructible (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r)
    [Ring Λ]
    [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{w} Λ)]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{w} Λ)]
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{w} Λ))) : Prop :=
  ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ
    ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{w} Λ)) i).obj K)

/-- The full subcategory of the unbounded derived category of small-étale
`Λ`-module sheaves with constructible cohomology sheaves. -/
@[stacks 095W, sga "5 I App.1.1" "constant Λ coefficients", sga "5 IIIB 6.1" "D_c(-)"]
public abbrev ConstructibleDerivedCategory (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ]
    [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{w} Λ)]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{w} Λ)] :=
  ObjectProperty.FullSubcategory (IsConstructible B X Λ)

end Stacks.EtaleCohomology
