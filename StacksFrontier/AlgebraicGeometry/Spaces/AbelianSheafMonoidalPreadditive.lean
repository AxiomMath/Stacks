module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxTotal
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Preadditive
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits

/-!
# The tensor product of abelian sheaves is bilinear on morphisms

`StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafMonoidal` puts a monoidal structure on the
abelian sheaves of a topological space and makes global sections lax monoidal, and then names
`CategoryTheory.MonoidalPreadditive (Stacks.Cohomology.Leray.AbelianSheaf X)` as the instance
without which no *complex* of abelian sheaves can be tensored. This file supplies it, in the
three steps that file lays out, and then forms the total complex it was wanted for.

The three steps are an instance of one transport, applied twice:
`CategoryTheory.monoidalPreadditive_of_additiveSection`
(`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Preadditive.lean`), which carries bilinearity
along an additive monoidal functor that has an additive section. An equivalence of categories is
such a functor, and so is sheafification.

* Abelian groups. `AddCommGrpCat.uliftIntEquivalence` presents them as the modules over a copy of
  the integers in their own universe, and `Mathlib` has bilinearity for modules. The functor of
  that equivalence is additive — on morphisms it is the identity — so its inverse is too, and the
  transport applies to the counit isomorphism.
* Presheaves. Nothing to do: the objectwise structure on a functor category is already known to
  be bilinear, in `CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive`
  (`StacksFrontier/CategoryTheory/Monoidal/FunctorCategoryTensorColimits.lean`). Only the import was
  missing.
* Sheaves. The monoidal structure on `Sheaf J A` is the localization of the objectwise one along
  sheafification, so sheafification is monoidal; it is additive because the sheaf category is
  abelian; and the inclusion of sheaves into presheaves is an additive section of it, the counit
  of the sheafification adjunction being an isomorphism. The transport applies again.

## Main definitions

* `AddCommGrpCat.monoidalPreadditive`: **the tensor product of abelian groups is bilinear on
  morphisms**, for the transported monoidal structure of
  `StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor`.
* `Stacks.Cohomology.Leray.abelianSheafMonoidalPreadditive`: **the tensor product of abelian
  sheaves on a topological space is bilinear on morphisms.**

## Main results

* `Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero`: **the tensor product of two
  bounded-below complexes of abelian sheaves has a total complex.** This is what the instance was
  named for, and it is the first step of the passage from `Γ` to `RΓ`.

## What this does and does not settle for Cohomology, Section 0FKU

The module docstrings of
`StacksFrontier/AlgebraicGeometry/DeRham/FirstChernClass/FilteredChernCupProduct.lean` and
`StacksFrontier/AlgebraicGeometry/DeRham/HodgeFiltration/BrutalPresentations.lean` list three things
missing from the passage `Γ ⟶ RΓ` that the cup product of Section 0FKU would be built from. This
file closes the first of the three and nothing else. Still missing, and still blocking a
*construction* of that cup product:

* the instantiation at abelian sheaves of `CochainComplex.KFlatMonoidal.derivedMonoidal`
  (`StacksFrontier/Homology/DerivedCategory/Monoidal/KFlatLocalization.lean`), whose hypothesis
  `hres` — every complex of abelian sheaves receives a quasi-isomorphism from a K-flat one — is
  carried, not an instance, and is not proved for abelian sheaves anywhere in this library. What
  *is* available is the transport of that hypothesis along an equivalence carrying one tensor
  product to the other,
  `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence`
  (`StacksFrontier/Homology/KFlat/BifunctorTransportEquivalence.lean`), and an equivalence to
  transport along: `Stacks.Cohomology.Leray.abelianSheafIntModulesEquivalence`
  (`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafAsIntModules.lean`) presents
  `AbelianSheaf X`
  as the modules over the constant sheaf of rings `ℤ` on the site of opens, which is a ringed
  site, and K-flat resolutions *are* available there, unconditionally, by [Stacks, Tag 06YS]. One
  gap stops that from closing: the equivalence is not known to carry the tensor product of
  `Stacks.SheafOfModules.Tensor.sheafTensor` to the tensor product of abelian sheaves. The route
  through `CategoryTheory.Sheaf.coefficientEquivalence` applied to
  `AddCommGrpCat.uliftIntEquivalence`, which presents `AbelianSheaf X` instead as
  `Sheaf (Opens.grothendieckTopology X) (ModuleCat (ULift ℤ))`, is *not* the one to take: no
  K-flat resolution theorem here is about a category of sheaves *valued* in modules;
* a monoidal structure on `DerivedCategory.Plus`, of which there is none anywhere, and which is
  the category the hypercohomology of abelian sheaves is actually computed in.

So the derived-level machinery that this instance unblocks —
`CategoryTheory.Functor.constMapDerivedCategoryMonoidal`
(`StacksFrontier/Homology/ConstMapDerivedCategoryMonoidal.lean`), which hypothesizes
`MonoidalPreadditive` and lifts a monoidal structure along `Functor.const` to the derived
category — is reachable but not reached here, and no cup product on the hypercohomology of
abelian sheaves is constructed below.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0722](https://stacks.math.columbia.edu/tag/0722)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe u v

namespace AddCommGrpCat

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal

/-- **The equivalence presenting abelian groups as modules over a universe-lifted copy of the
integers is additive.** On morphisms it changes nothing: a morphism of modules over
`AddCommGrpCat.ULiftInt` is an additive map, and restricting the scalars along
`ULift.ringEquiv.symm` and then forgetting them leaves that map alone. So addition of morphisms
is preserved by definition. -/
instance uliftIntEquivalenceFunctorAdditive :
    (AddCommGrpCat.uliftIntEquivalence.{v}).functor.Additive where
  map_add := by intros; rfl

/-- **The tensor product of abelian groups is bilinear on morphisms.**

Transported from the modules over a universe-lifted copy of the integers, where bilinearity of
the tensor product is already known, along the monoidal equivalence
`AddCommGrpCat.uliftIntEquivalence` that the monoidal structure itself was transported along. The
transport is `CategoryTheory.monoidalPreadditive_of_additiveSection`, whose additive section is
the inverse of the equivalence and whose isomorphism is its counit. -/
instance monoidalPreadditive : MonoidalPreadditive AddCommGrpCat.{v} :=
  monoidalPreadditive_of_additiveSection
    (AddCommGrpCat.uliftIntEquivalence.{v}).functor
    (AddCommGrpCat.uliftIntEquivalence.{v}).inverse
    inferInstance
    (AddCommGrpCat.uliftIntEquivalence.{v}).counitIso

end AddCommGrpCat

namespace Stacks.Cohomology.Leray

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal AddCommGrpCat.braidedCategory
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf
  abelianSheafMonoidalCategory

/-- **The tensor product of abelian sheaves on a topological space is bilinear on morphisms.**

The monoidal structure of `Stacks.Cohomology.Leray.abelianSheafMonoidalCategory` is the
localization along sheafification of the objectwise structure on presheaves, so sheafification is
a monoidal functor for it; it is additive, the category of abelian sheaves being abelian; and the
inclusion of sheaves into presheaves is an additive section of it, because the counit of the
sheafification adjunction is an isomorphism. Bilinearity on presheaves is objectwise, so it is
`CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive` applied to
`AddCommGrpCat.monoidalPreadditive`, and
`CategoryTheory.monoidalPreadditive_of_additiveSection` carries it across.

This is the instance that the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianSheafMonoidal.lean` names as the blocker on
tensoring *complexes* of abelian sheaves. What it unblocks immediately is
`Stacks.Cohomology.Leray.hasMapBifunctor_curriedTensor_of_isZero` below. -/
instance abelianSheafMonoidalPreadditive (X : TopCat.{u}) :
    MonoidalPreadditive (AbelianSheaf X) :=
  monoidalPreadditive_of_additiveSection
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    inferInstance
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit)

/-- **The tensor product of two bounded-below complexes of abelian sheaves has a total
complex**, so a tensor product of complexes of abelian sheaves can be formed.

The general criterion is `HomologicalComplex.hasMapBifunctor_up_ℤ_of_isZero`: a bifunctor that
preserves zero morphisms in each variable, into a category with finite coproducts, has a total
complex on a pair of bounded-below `ℤ`-indexed cochain complexes, because then only finitely many
summands contribute in each total degree. For the tensor product both hypotheses on the bifunctor
are `Stacks.Cohomology.Leray.abelianSheafMonoidalPreadditive`, which makes tensoring additive in
each variable. -/
theorem hasMapBifunctor_curriedTensor_of_isZero (X : TopCat.{u})
    (K L : CochainComplex (AbelianSheaf X) ℤ) (n₁ n₂ : ℤ)
    (hK : ∀ p, p < n₁ → IsZero (K.X p)) (hL : ∀ q, q < n₂ → IsZero (L.X q)) :
    HomologicalComplex.HasMapBifunctor K L (MonoidalCategory.curriedTensor (AbelianSheaf X))
      (ComplexShape.up ℤ) :=
  HomologicalComplex.hasMapBifunctor_up_ℤ_of_isZero K L _ n₁ n₂ hK hL

end Stacks.Cohomology.Leray

end
