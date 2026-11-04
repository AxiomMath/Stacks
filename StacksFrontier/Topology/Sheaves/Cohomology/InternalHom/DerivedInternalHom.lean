module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# Internal hom in the derived category of a ringed space

Let `(X, O_X)` be a ringed space. For objects `L`, `M` of `D(O_X)` the derived internal hom
`RSheafHom(L, M)` is the object of `D(O_X)` represented by the internal Hom complex of a complex
representing `L` into a K-injective complex representing `M`, and it is characterised by the
tensor–internal-hom formula

`Hom_{D(O_X)}(K, RSheafHom(L, M)) = Hom_{D(O_X)}(K ⊗^L_{O_X} L, M)`

of Stacks 08DI, which pins it down up to isomorphism by Yoneda.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site derived internal hom of Stacks 08J7 and
its tensor–hom bijection of Stacks 08J8 apply verbatim. The declarations below read those off
along `Stacks.SheafOfModules.ringedSite`, in the vocabulary of
`Stacks.SheafOfModules.StructureSheafModules`.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHom`: `RSheafHom_{O_X}(-, -)`, the derived internal hom
  bifunctor on `D(O_X)`.
* `Stacks.SheafOfModules.derivedTensor`: `- ⊗^L_{O_X} -`, the derived tensor product on `D(O_X)`.
* `Stacks.SheafOfModules.derivedSheafHomComparison`: for a K-injective complex `I`, the
  identification of `RSheafHom(A, I)` with the internal Hom complex `SheafHom^•(A, I)`.
* `Stacks.SheafOfModules.derivedInternalHom`: the derived internal hom together with its
  comparison on K-injective representatives, as the datum the evaluation and composition
  morphisms of Stacks 0A8U and 0A8V are built from.
* `Stacks.SheafOfModules.derivedSheafHomMap` and `Stacks.SheafOfModules.derivedTensorMap`: the
  maps induced on derived internal homs and on derived tensor products in both variables at
  once.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv` (Stacks 08DI): the tensor–internal-hom
  bijection of morphism groups.

## Implementation notes

`ringedSite` is an abbreviation, so `(ringedSite Rc).ringSheaf` is `structureSheaf Rc` and
`SheafOfModules (ringedSite Rc).ringSheaf` is `StructureSheafModules Rc`. Hence each declaration
below is the site-level term, type-checked against the space-level statement, with no comparison
layer between the two settings.

The bijection of Stacks 08DI is the one induced on degree-zero derived global sections by the
currying isomorphism `RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_{O_X} L, M)`, as in
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`.

`derivedInternalHom` is built from `RingedSite.derivedSheafHomBifunctor`, the bifunctor obtained
by localizing the internal Hom complex at the quasi-isomorphisms, rather than from
`RingedSite.canonicalDerivedInternalHom`, which is a choice of inhabitant of the same structure.

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- `RSheafHom_{O_X}(-, -)`, the derived internal hom of modules on a ringed space: the
bifunctor on `D(O_X)`, contravariant in its first argument, obtained by localizing the internal
Hom complex into a K-injective resolution at the quasi-isomorphisms. -/
abbrev derivedSheafHom :
    (DerivedCategory (StructureSheafModules Rc))ᵒᵖ ⥤
      DerivedCategory (StructureSheafModules Rc) ⥤
        DerivedCategory (StructureSheafModules Rc) :=
  RingedSite.derivedSheafHomBifunctor (ringedSite Rc)

/-- `- ⊗^L_{O_X} -`, the derived tensor product of modules on a ringed space, computed by the
total tensor complex on K-flat representatives. -/
abbrev derivedTensor :
    DerivedCategory (StructureSheafModules Rc) ⥤
      DerivedCategory (StructureSheafModules Rc) ⥤
        DerivedCategory (StructureSheafModules Rc) :=
  derivedTensorProductFunctor (ringedSite Rc)

/-- A K-injective target computes the derived internal hom: `RSheafHom(A, I)` is the class of
the internal Hom complex `SheafHom^•(A, I)`. -/
def derivedSheafHomComparison (A I : CochainComplex (StructureSheafModules Rc) ℤ)
    [hI : I.IsKInjective] :
    ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj A))).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (sheafHomComplex Rc A I).obj :=
  @RingedSite.derivedSheafHomComparison (ringedSite Rc) _ A I hI

/-- The derived internal hom of a ringed space, together with its comparison on K-injective
representatives and the naturality of that comparison in both arguments. -/
def derivedInternalHom : RingedSite.DerivedInternalHom (ringedSite Rc) where
  hom := derivedSheafHom Rc
  homComparison A I hI :=
    @RingedSite.derivedSheafHomComparison (ringedSite Rc) _ A I hI
  homComparison_natural f g :=
    RingedSite.derivedSheafHomComparison_naturality (ringedSite Rc) f g

/-- The map of derived internal homs `RSheafHom(A, B) ⟶ RSheafHom(A', B')` induced
contravariantly by `a : A' ⟶ A` and covariantly by `b : B ⟶ B'`. -/
abbrev derivedSheafHomMap {A A' B B' : DerivedCategory (StructureSheafModules Rc)}
    (a : A' ⟶ A) (b : B ⟶ B') :
    ((derivedSheafHom Rc).obj (op A)).obj B ⟶ ((derivedSheafHom Rc).obj (op A')).obj B' :=
  RingedSite.derivedSheafHomMap (ringedSite Rc) (derivedInternalHom Rc) a b

/-- The map of derived tensor products `A ⊗^L_{O_X} B ⟶ A' ⊗^L_{O_X} B'` induced by
`a : A ⟶ A'` and `b : B ⟶ B'`. -/
abbrev derivedTensorMap {A A' B B' : DerivedCategory (StructureSheafModules Rc)}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((derivedTensor Rc).obj A).obj B ⟶ ((derivedTensor Rc).obj A').obj B' :=
  RingedSite.derivedTensorMap (ringedSite Rc) (canonicalDerivedTensorProduct (ringedSite Rc)) a b

/-- **Stacks 08DI.** For objects `K`, `L`, `M` of `D(O_X)` on a ringed space, morphisms into the
derived internal hom are canonically identified with morphisms out of the derived tensor
product,

`Hom_{D(O_X)}(K, RSheafHom(L, M)) = Hom_{D(O_X)}(K ⊗^L_{O_X} L, M)`,

as an isomorphism of abelian groups. -/
@[stacks 08DI]
def derivedSheafHomTensorEquiv (K L M : DerivedCategory (StructureSheafModules Rc)) :
    (K ⟶ ((derivedSheafHom Rc).obj (op L)).obj M) ≃+
      (((derivedTensor Rc).obj K).obj L ⟶ M) :=
  RingedSite.derivedCurryHomEquiv (ringedSite Rc) K L M

end Stacks.SheafOfModules

end
