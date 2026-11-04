module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on the small étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`. The derived
tensor product `⊗^L_{𝒪_X}` on `D(𝒪_X)` is the canonical derived tensor product of Stacks 06YU on
the small étale ringed site of `X`, `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which
is available there because that construction lets the objects of the site live one universe
above its morphisms and rings.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`: the canonical
  `Stacks.SheafOfModules.DerivedTensorProduct` on the small étale ringed site of `X`, with its
  K-flat comparisons and exactness in each variable.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensor`: its bifunctor
  `D(𝒪_X) ⥤ D(𝒪_X) ⥤ D(𝒪_X)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso`: **Stacks 07A4** for a morphism
  `f : X ⟶ Y` of algebraic spaces, `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L`, for the morphism of small
  étale ringed topoi of Stacks 03G8.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_hom_app_model`: on a pair of
  K-flat complexes with flat terms the isomorphism of Stacks 07A4 is the composite of the K-flat
  comparisons, the computation of `Lf^*` of Stacks 06YY and the comparison of Stacks 03EL.

## Implementation notes

The category of modules of `AlgebraicGeometry.Space.smallEtaleRingedSite` and the one the derived
pullback of algebraic spaces is stated over,
`SheafOfModules (AlgebraicGeometry.Space.ringedToposStructureRingSheaf B S hS X)`, are the same
category by `rfl`: both are sheaves of modules over the structure sheaf with commutativity
forgotten. The bifunctor is stated in the second spelling, so that it composes with
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` without transport.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The total tensor complexes of sheaves of `𝒪_X`-modules on the small étale site exist, read
at the universe of the site's modules; instance search otherwise reaches them through an
assignment of the coefficient universes that the kernel rejects. -/
local instance hasMapBifunctor_sheafTensor_smallEtale (X : AlgebraicSpaces B S hS)
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} _ K₁ K₂

/-- The total tensor complexes of sheaves of `𝒪_X`-modules on the small étale ringed topos of
`X` exist, read at the universes of the site. Not a global instance; files whose instance search
does not reach these complexes in time make it a local one. -/
theorem hasMapBifunctor_sheafTensor_smallEtaleRingedTopos (X : AlgebraicSpaces B S hS)
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} _ K₁ K₂

/-- **The derived tensor product on an algebraic space**, Stacks 06YU on the small étale ringed
site of `X`: the canonical derived tensor product with its K-flat comparisons, its natural map to
the ordinary total tensor complex, and exactness in each variable. -/
abbrev smallEtaleDerivedTensorProduct (X : AlgebraicSpaces B S hS) :
    Stacks.SheafOfModules.DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2) :=
  Stacks.SheafOfModules.canonicalDerivedTensorProduct _

/-- The derived tensor bifunctor `- ⊗^L_{𝒪_X} -` on `D(𝒪_X)` for an algebraic space `X`. -/
abbrev smallEtaleDerivedTensor (X : AlgebraicSpaces B S hS) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (smallEtaleDerivedTensorProduct B S hS X).tensor

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 07A4 for a morphism of algebraic spaces.** For `f : X ⟶ Y` there is a canonical
bifunctorial isomorphism `Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L` for `K, L ∈ D(𝒪_Y)`,
stated between the two uncurried bifunctors on `D(𝒪_Y) × D(𝒪_Y)`. -/
def smallEtaleDerivedPullbackTensorIso (f : X ⟶ Y) :
    Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y) ⋙
        smallEtaleDerivedModulePullback B S hS f ≅
      (smallEtaleDerivedModulePullback B S hS f).prod
          (smallEtaleDerivedModulePullback B S hS f) ⋙
        Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso
    (smallEtaleRingedToposHom B S hS f) (smallEtaleDerivedTensorProduct B S hS X)
    (smallEtaleDerivedTensorProduct B S hS Y)

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms** is the
composite of the K-flat comparisons of Stacks 06YU, the computation of `Lf^*` of Stacks 06YY and
the comparison of total tensor complexes of Stacks 03EL. -/
theorem smallEtaleDerivedPullbackTensorIso_hom_app_model (f : X ⟶ Y)
    (P N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ _).obj P))
    (hN : smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ _).obj N)) :
    (smallEtaleDerivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelIso
        (smallEtaleRingedToposHom B S hS f) (smallEtaleDerivedTensorProduct B S hS X)
        (smallEtaleDerivedTensorProduct B S hS Y) P N hP.1 hN.1 hP.2 hN.2).hom :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_model
    (smallEtaleRingedToposHom B S hS f) (smallEtaleDerivedTensorProduct B S hS X)
    (smallEtaleDerivedTensorProduct B S hS Y) P N hP.1 hN.1 hP.2 hN.2

end AlgebraicGeometry.Space

end
