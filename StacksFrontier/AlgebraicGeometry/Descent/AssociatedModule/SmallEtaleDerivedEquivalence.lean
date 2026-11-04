module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforwardQcoh
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
import StacksCore.Tactic.StacksAttribute

/-!
# `ε^* : D_QCoh(𝒪_S) ⟶ D_QCoh(𝒪_étale)` is an equivalence

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of Stacks 08H7/070R.  Its inverse image on modules is the associated-module functor
`ε^* = (𝓕 ↦ 𝓕^a)` of Stacks 03DU (4) at `τ = étale`, spelled
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, and it is exact (Stacks 08H8,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf`).  Stacks 071Q
asserts that the induced functor on the derived categories with quasi-coherent cohomology,

`ε^* : D_QCoh(𝒪_S) ⟶ D_QCoh(S_étale, 𝒪)`,

is an equivalence.  That is `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`
below, for every scheme `S`.

## The proof of Stacks 071Q

It is the source's.  The quasi-inverse is the derived direct image
`Rε_* : D(S_étale, 𝒪) ⥤ D(𝒪_S)`, built from K-injective resolutions in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedPushforward.lean`, where
`ε^* ⊣ Rε_*` is `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction` and where
`H^q(Rε_* E) = ε_* H^q(E)` is proved for `E` with quasi-coherent cohomology, from Stacks 03DW and
01XB on the affine objects of the small étale site and Stacks 0BKZ.  The unit and the counit of
`ε^* ⊣ Rε_*` are then isomorphisms on the complexes with quasi-coherent cohomology
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedPushforwardQcoh.lean`),
because `ε^*` and `ε_*` are mutually inverse on quasi-coherent modules (Stacks 03DX).  So the
adjunction restricts to an adjoint equivalence between the two `D_QCoh`'s,
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleQcohAdjunction`.

## The route through `D(QCoh)`

The first part of the file compares `ε^*` on `D_QCoh` with the derived functor of the abelian
equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` of Stacks 03DX (2), through the comparison functors
`D(QCoh) ⥤ D_QCoh` of Stacks 06VT on the two sides.  It deduces the equivalence,
`AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule`, from those two comparisons
being equivalences.  That is a weaker statement than Stacks 071Q: the comparison
`D(QCoh(𝒪_S)) ⥤ D_QCoh(𝒪_S)` is an equivalence for quasi-compact schemes with affine diagonal
(Stacks 08DB), not for every scheme.  It is kept for the comparison square
`AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare`, which identifies the two
derived functors induced by `ε^*`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.qcohOnSite`: quasi-coherence of `𝒪`-modules on `S_étale`, the
  object property cutting out `QCoh(S_étale, 𝒪)` and, through
  `DerivedCategoryB.derivedCategoryB`, also `D_QCoh(S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModule`: `ε^*` as a functor
  `D_QCoh(𝒪_S) ⥤ D_QCoh(S_étale, 𝒪)`, the functor of Stacks 071Q.
* `AlgebraicGeometry.SmallEtale.derivedRestrictModuleQcoh`: `Rε_*` as a functor
  `D_QCoh(S_étale, 𝒪) ⥤ D_QCoh(𝒪_S)`.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleQcohAdjunction`: `ε^* ⊣ Rε_*` between the
  two `D_QCoh`'s.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleEquivalenceQcoh`: the equivalence
  `D_QCoh(𝒪_S) ≌ D_QCoh(S_étale, 𝒪)` of Stacks 071Q, bundled.
* `AlgebraicGeometry.SmallEtale.derivedQcohOnSiteComparison`: the comparison functor
  `D(QCoh(S_étale, 𝒪)) ⥤ D_QCoh(S_étale, 𝒪)`, the small étale counterpart of
  `Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison`.
* `AlgebraicGeometry.SmallEtale.associatedModuleQcohOnSiteEquivalence`: the abelian equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` of Stacks 03DX (2) at `τ = étale`, for an essential
  surjectivity witness.
* `AlgebraicGeometry.SmallEtale.associatedModuleDerivedQcoh`: the functor
  `D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))` induced by `ε^*`.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`: **Stacks 071Q**.
* `AlgebraicGeometry.SmallEtale.isWeakSerreClass_qcohOnSite`: quasi-coherence on `S_étale` is a
  weak Serre class, from Stacks 06VE (5) and (10) at `τ = étale`.
* `AlgebraicGeometry.SmallEtale.isTriangulated_derivedQcohOnSite`: `D_QCoh(S_étale, 𝒪)` is a
  strictly full saturated triangulated subcategory of `D(S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_mem`: `ε^*` carries a complex with
  quasi-coherent cohomology to a complex with quasi-coherent cohomology, which is what makes the
  functor of 071Q exist.
* `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleDerivedQcoh`: `ε^*` induces an
  equivalence `D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))`.
* `AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare`: the comparison functors
  intertwine the two derived functors induced by `ε^*`.
* `AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule`: the equivalence of
  071Q deduced through `D(QCoh)`, from the two comparisons of Stacks 06VT being equivalences.

## Implementation notes

The ambient `HasDerivedCategory` instances are left free, as in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/WeakSerre/DerivedComparison.lean`: pinning
`CategoryTheory.HasDerivedCategory.standard` would put the morphisms of `D(𝒪_S)` one universe
above its objects and make the statement unusable for the direct-sum statements about
`D_QCoh(𝒪_S)`.  At `CategoryTheory.HasDerivedCategory.standard` the subcategory of the source is
`AlgebraicGeometry.QuasicoherentDerivedCategory S`, and the target is the small étale
counterpart of `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X.

`ε^*` is spelled `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, the retyping of
`AlgebraicGeometry.SmallEtale.associatedModule` with source `SheafOfModules.{u} S.ringCatSheaf`
rather than `AlgebraicGeometry.Scheme.Modules`; the two are definitionally equal but carry
separately declared `CategoryTheory.Category` and `CategoryTheory.Abelian` instances, and the
former is the spelling in which `AlgebraicGeometry.SmallEtale.associatedModuleQcoh`, hence the
abelian equivalence, is stated.

The comparison of two derived functors used for the square, `mapDerivedCategoryCompIso` below,
duplicates (and generalizes from an objectwise isomorphism to a natural one) the private helpers
of the same name in `StacksFrontier/Homology/PseudoCoherent/Relative/Localization.lean` and
`StacksFrontier/Homology/PseudoCoherent/Relative/Tower.lean`; Mathlib records no such comparison.

No `@[stacks 06VT]` attribute is attached to `derivedQcohOnSiteComparison`: 06VT is about
`QCoh(𝒪_X)` for a scheme, and the small étale analogue is the situation of Stacks 08F1, which
`AlgebraicGeometry.Space.quasicoherentDerivedComparison` leaves untagged as well.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

/-! ### The derived functor of a composite of exact functors -/

namespace Stacks.DerivedQCoh

section Generic

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- For exact functors `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₃` and an exact `H : C₁ ⥤ C₃` identified
with `F ⋙ G`, the derived functor of `H` is the composite of the derived functors of `F` and `G`.

A duplicate, generalized from an objectwise to a natural isomorphism, of the private helpers
`mapDerivedCategoryCompIso` of `StacksFrontier/Homology/PseudoCoherent/Relative/Localization.lean`
and `StacksFrontier/Homology/PseudoCoherent/Relative/Tower.lean`. -/
def mapDerivedCategoryCompIso
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃) (e : F ⋙ G ≅ H)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q)

end Generic

end Stacks.DerivedQCoh

namespace AlgebraicGeometry.SmallEtale

open Stacks.DerivedQCoh

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-coherence of `𝒪`-modules on the small étale site of `S`, at the module universe of the
structure sheaf: the object property cutting out `QCoh(S_étale, 𝒪)`, and through
`DerivedCategoryB.derivedCategoryB` also `D_QCoh(S_étale, 𝒪)`. -/
abbrev qcohOnSite : ObjectProperty (SheafOfModules.{u} (structureSheaf B S hS)) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)

/-! ### `QCoh(S_étale, 𝒪)` as a weak Serre subcategory -/

section WeakSerre

/-- **Stacks 06VE (5) and (10) at `τ = étale`, as a weak Serre class.**  Quasi-coherence of
`𝒪`-modules on the small étale site of `S` is a weak Serre class in the sense of Stacks 0754: it
is closed under kernels, cokernels and extensions. -/
instance isWeakSerreClass_qcohOnSite : (qcohOnSite B S hS).IsWeakSerreClass where

/-- The inclusion `QCoh(S_étale, 𝒪) ⥤ Mod(S_étale, 𝒪)` is left exact. -/
instance preservesFiniteLimits_ι_qcohOnSite :
    PreservesFiniteLimits (qcohOnSite B S hS).ι :=
  preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion `QCoh(S_étale, 𝒪) ⥤ Mod(S_étale, 𝒪)` is right exact. -/
instance preservesFiniteColimits_ι_qcohOnSite :
    PreservesFiniteColimits (qcohOnSite B S hS).ι :=
  preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- The five-term formulation of `isWeakSerreClass_qcohOnSite`, the form in which Stacks 06UP
consumes it: in an exact sequence of five `𝒪`-modules on `S_étale` whose four outer terms are
quasi-coherent, the middle term is quasi-coherent. -/
theorem isWeakSerre_qcohOnSite : WeakSerre.IsWeakSerre (qcohOnSite B S hS) := by
  refine ⟨inferInstance, (qcohOnSite B S hS).exists_prop_of_isWeakSerreClass,
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact prop_mid_of_exact₄ ((qcohOnSite B S hS).prop_obj₂_of_exact)
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

end WeakSerre

/-! ### `D_QCoh(S_étale, 𝒪)` and its comparison with `D(QCoh(S_étale, 𝒪))` -/

section Comparison

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- `D_QCoh(S_étale, 𝒪)` is a strictly full saturated triangulated subcategory of
`D(S_étale, 𝒪)`, by Stacks 06UP applied to the weak Serre subcategory of quasi-coherent
`𝒪`-modules on `S_étale`. -/
instance isTriangulated_derivedQcohOnSite :
    (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_qcohOnSite B S hS)

variable [HasDerivedCategory.{w} (qcohOnSite B S hS).FullSubcategory]

/-- The derived functor of the inclusion of the quasi-coherent `𝒪`-modules of `S_étale` has
quasi-coherent cohomology in every degree: the inclusion is exact, so it commutes with
cohomology. -/
theorem derivedQcohOnSiteComparison_mem
    (K : DerivedCategory (qcohOnSite B S hS).FullSubcategory) :
    DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)
      ((qcohOnSite B S hS).ι.mapDerivedCategory.obj K) := fun n =>
  (qcohOnSite B S hS).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (qcohOnSite B S hS).ι n).app K).symm
    ((DerivedCategory.homologyFunctor _ n).obj K).property

/-- The comparison functor `D(QCoh(S_étale, 𝒪)) ⥤ D_QCoh(S_étale, 𝒪)`: the derived functor of
the exact inclusion of the quasi-coherent `𝒪`-modules of `S_étale`, factored through the
complexes with quasi-coherent cohomology.

No `@[stacks]` attribute: this is the small étale analogue of Stacks 06VT, i.e. the situation of
Stacks 08F1 for the small étale site of a scheme rather than of an algebraic space, the same
reason `AlgebraicGeometry.Space.quasicoherentDerivedComparison` is untagged. -/
def derivedQcohOnSiteComparison :
    DerivedCategory (qcohOnSite B S hS).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).lift
    (qcohOnSite B S hS).ι.mapDerivedCategory (derivedQcohOnSiteComparison_mem B S hS)

end Comparison

/-! ### The abelian equivalence of Stacks 03DX (2) at `τ = étale`, and its derived category -/

section Abelian

/-- The corestricted functor `ε^* : QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` is additive, with no
hypothesis: composed with the additive and faithful inclusion of `QCoh(S_étale, 𝒪)` it is
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh`, which is additive because `ε^*` and the
inclusion of `QCoh(𝒪_S)` are. -/
instance additive_associatedModuleQcohOnSite :
    (associatedModuleQcohOnSite B S hS).Additive :=
  have h : (associatedModuleQcoh B S hS).Additive := inferInstance
  have : (associatedModuleQcohOnSite B S hS ⋙ (qcohOnSite B S hS).ι).Additive := h
  Functor.additive_of_comp_faithful _ (qcohOnSite B S hS).ι

variable (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)

/-- **Stacks 03DX (2) at `τ = étale`, bundled.**  Over essential surjectivity, `𝓕 ↦ 𝓕^a` is an
equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`. -/
def associatedModuleQcohOnSiteEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (qcohOnSite B S hS).FullSubcategory :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS hsurj
  (associatedModuleQcohOnSite B S hS).asEquivalence

include hsurj in
/-- The corestricted functor `ε^* : QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` is left exact: being an
equivalence it preserves all limits. -/
theorem preservesFiniteLimits_associatedModuleQcohOnSite :
    PreservesFiniteLimits (associatedModuleQcohOnSite B S hS) :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS hsurj
  inferInstance

include hsurj in
/-- The corestricted functor `ε^* : QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` is right exact: being an
equivalence it preserves all colimits. -/
theorem preservesFiniteColimits_associatedModuleQcohOnSite :
    PreservesFiniteColimits (associatedModuleQcohOnSite B S hS) :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS hsurj
  inferInstance

variable [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (qcohOnSite B S hS).FullSubcategory]

/-- The functor `D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))` induced by the exact corestricted `ε^*`. -/
def associatedModuleDerivedQcoh :
    DerivedCategory (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      DerivedCategory (qcohOnSite B S hS).FullSubcategory :=
  have := preservesFiniteLimits_associatedModuleQcohOnSite B S hS hsurj
  have := preservesFiniteColimits_associatedModuleQcohOnSite B S hS hsurj
  (associatedModuleQcohOnSite B S hS).mapDerivedCategory

include hsurj in
/-- **Stacks 03DX (2) at `τ = étale`, derived.**  `ε^*` induces an equivalence of the derived
categories of the abelian categories of quasi-coherent modules,
`D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))`.

The only input beyond the functor and its full faithfulness is the essential surjectivity
witness `hsurj`, which `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
supplies; an equivalence of abelian categories is automatically exact. -/
theorem isEquivalence_associatedModuleDerivedQcoh :
    (associatedModuleDerivedQcoh.{w} B S hS hsurj).IsEquivalence := by
  have hL := preservesFiniteLimits_associatedModuleQcohOnSite B S hS hsurj
  have hC := preservesFiniteColimits_associatedModuleQcohOnSite B S hS hsurj
  have : (associatedModuleQcohOnSiteEquivalence B S hS hsurj).functor.Additive :=
    additive_associatedModuleQcohOnSite B S hS
  have : PreservesFiniteLimits
    (associatedModuleQcohOnSiteEquivalence B S hS hsurj).functor := hL
  have : PreservesFiniteColimits
    (associatedModuleQcohOnSiteEquivalence B S hS hsurj).functor := hC
  exact Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory
    (associatedModuleQcohOnSiteEquivalence B S hS hsurj)

end Abelian

/-! ### `ε^*` on the derived categories with quasi-coherent cohomology -/

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Stacks 03DV (2) at `τ = étale`, derived.**  `ε^*` carries a complex of `𝒪_S`-modules with
quasi-coherent cohomology to a complex of `𝒪`-modules on `S_étale` with quasi-coherent
cohomology: `ε^*` is exact, so `Hⁿ(ε^* K) ≅ ε^*(Hⁿ K)`, and `ε^*` preserves quasi-coherence. -/
theorem derivedAssociatedModule_mem
    (K : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory) :
    DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj K.obj) := fun n =>
  (qcohOnSite B S hS).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (associatedModuleOfSheaf B S hS) n).app K.obj).symm
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} S.ringCatSheaf) n).obj K.obj) (K.property n))

/-- **The functor of Stacks 071Q**: `ε^* : D_QCoh(𝒪_S) ⥤ D_QCoh(S_étale, 𝒪)`, the derived
functor of the exact `ε^*` corestricted to the complexes with quasi-coherent cohomology on both
sides. -/
def derivedAssociatedModule :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).lift
    ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).ι ⋙
      (associatedModuleOfSheaf B S hS).mapDerivedCategory)
    (derivedAssociatedModule_mem B S hS)

end Derived

/-! ### Stacks 071Q -/

section Equivalence

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (qcohOnSite B S hS).FullSubcategory]
  (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)

/-- The two derived functors induced by `ε^*` are intertwined by the comparison functors of
Stacks 06VT: the square whose rows are the derived functors of `ε^*` on `D(QCoh)` and on
`D_QCoh`, and whose columns are the two comparisons, commutes up to a natural isomorphism.

The inclusion of `D_QCoh(S_étale, 𝒪)` is fully faithful, so it is enough to check the square
after composing with it; there both sides are the derived functor of
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh`. -/
def derivedQuasicoherentComparisonSquare :
    Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{w} S ⋙
        derivedAssociatedModule.{w} B S hS ≅
      associatedModuleDerivedQcoh.{w} B S hS hsurj ⋙ derivedQcohOnSiteComparison.{w} B S hS :=
  have : PreservesFiniteLimits (associatedModuleQcohOnSite B S hS) :=
    preservesFiniteLimits_associatedModuleQcohOnSite B S hS hsurj
  have : PreservesFiniteColimits (associatedModuleQcohOnSite B S hS) :=
    preservesFiniteColimits_associatedModuleQcohOnSite B S hS hsurj
  Functor.fullyFaithfulCancelRight
    (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι
    (mapDerivedCategoryCompIso (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
        (associatedModuleOfSheaf B S hS) (associatedModuleQcoh B S hS) (Iso.refl _) ≪≫
      (mapDerivedCategoryCompIso (associatedModuleQcohOnSite B S hS) (qcohOnSite B S hS).ι
        (associatedModuleQcoh B S hS) (Iso.refl _)).symm)

variable
  [(Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{w}
    S).IsEquivalence]
  [(derivedQcohOnSiteComparison.{w} B S hS).IsEquivalence]

include hsurj in
/-- **The equivalence of Stacks 071Q, through `D(QCoh)`.**  If the comparison functors
`D(QCoh) ⥤ D_QCoh` of Stacks 06VT are equivalences on both sides, then
`ε^* : D_QCoh(𝒪_S) ⟶ D_QCoh(S_étale, 𝒪)` is an equivalence, being identified by
`derivedQuasicoherentComparisonSquare` with the derived functor of the abelian equivalence
`QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`.

This is weaker than Stacks 071Q, whose statement for every scheme is
`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`. -/
theorem isEquivalence_derivedAssociatedModule :
    (derivedAssociatedModule.{w} B S hS).IsEquivalence := by
  have := isEquivalence_associatedModuleDerivedQcoh.{w} B S hS hsurj
  have : (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{w} S ⋙
      derivedAssociatedModule.{w} B S hS).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (derivedQuasicoherentComparisonSquare.{w} B S hS hsurj).symm
  exact Functor.isEquivalence_of_comp_left
    (Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison.{w} S)
    (derivedAssociatedModule.{w} B S hS)

/-- The equivalence of `isEquivalence_derivedAssociatedModule`, bundled, with functor `ε^*`.  The
bundled equivalence of Stacks 071Q for every scheme is
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleEquivalenceQcoh`. -/
def derivedAssociatedModuleEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory :=
  have := isEquivalence_derivedAssociatedModule.{w} B S hS hsurj
  (derivedAssociatedModule.{w} B S hS).asEquivalence

end Equivalence

/-! ### Stacks 071Q -/

section Unconditional

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- `Rε_* : D_QCoh(S_étale, 𝒪) ⥤ D_QCoh(𝒪_S)`: the derived direct image along `ε`, corestricted
to the complexes with quasi-coherent cohomology on both sides.  It lands there because
`H^q(Rε_* E) = ε_* H^q(E)` is quasi-coherent for `E` with quasi-coherent cohomology. -/
def derivedRestrictModuleQcoh :
    (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)).lift
    ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι ⋙ derivedRestrictModule B S hS)
    (fun E n => isQuasicoherent_homology_derivedRestrictModule B S hS
      E.obj E.property n)

/-- `ε^* ⊣ Rε_*` on the derived categories with quasi-coherent cohomology: the restriction of
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction` to the two full subcategories. -/
def derivedAssociatedModuleQcohAdjunction :
    derivedAssociatedModule.{w} B S hS ⊣ derivedRestrictModuleQcoh.{w} B S hS :=
  (derivedAssociatedModuleAdjunction B S hS).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- The unit of `ε^* ⊣ Rε_*` on `D_QCoh(𝒪_S)` is an isomorphism. -/
instance isIso_derivedAssociatedModuleQcohAdjunction_unit_app
    (X : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory) :
    IsIso ((derivedAssociatedModuleQcohAdjunction.{w} B S hS).unit.app X) := by
  have : IsIso ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)).ι.map
        ((derivedAssociatedModuleQcohAdjunction.{w} B S hS).unit.app X)) := by
    refine (congrArg (fun f => IsIso f) (Adjunction.map_restrictFullyFaithful_unit_app
      (derivedAssociatedModuleAdjunction B S hS) (ObjectProperty.fullyFaithfulι _)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm X)).mpr ?_
    refine IsIso.comp_isIso' (isIso_derivedAssociatedModuleAdjunction_unit_app B S hS X.obj
      X.property) (IsIso.comp_isIso' ?_ ?_)
    · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom (Iso.app
        ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).liftCompιIso
        ((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)).ι ⋙
          (associatedModuleOfSheaf B S hS).mapDerivedCategory)
          (derivedAssociatedModule_mem B S hS)).symm X))
    · exact Iso.isIso_hom (Iso.app
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent S.ringCatSheaf)).liftCompιIso
        ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι ⋙ derivedRestrictModule B S hS)
        (fun E n =>
          isQuasicoherent_homology_derivedRestrictModule B S hS E.obj E.property n)).symm _)
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

/-- The counit of `ε^* ⊣ Rε_*` on `D_QCoh(S_étale, 𝒪)` is an isomorphism. -/
instance isIso_derivedAssociatedModuleQcohAdjunction_counit_app
    (E : (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory) :
    IsIso ((derivedAssociatedModuleQcohAdjunction.{w} B S hS).counit.app E) := by
  have : IsIso ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι.map
      ((derivedAssociatedModuleQcohAdjunction.{w} B S hS).counit.app E)) := by
    refine (congrArg (fun f => IsIso f) (Adjunction.map_restrictFullyFaithful_counit_app
      (derivedAssociatedModuleAdjunction B S hS) (ObjectProperty.fullyFaithfulι _)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm E)).mpr ?_
    refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_
      (isIso_derivedAssociatedModuleAdjunction_counit_app B S hS E.obj E.property))
    · exact Iso.isIso_inv (Iso.app
        ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).liftCompιIso
        ((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)).ι ⋙
          (associatedModuleOfSheaf B S hS).mapDerivedCategory)
          (derivedAssociatedModule_mem B S hS)).symm _)
    · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_inv (Iso.app
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent S.ringCatSheaf)).liftCompιIso
        ((DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι ⋙ derivedRestrictModule B S hS)
        (fun E n =>
          isQuasicoherent_homology_derivedRestrictModule B S hS E.obj E.property n)).symm E))
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

/-- **Stacks 071Q.**  For a scheme `S`, the functor `ε^* : D_QCoh(𝒪_S) ⟶ D_QCoh(S_étale, 𝒪)`
induced by the exact functor `ε^*` of Stacks 08H8 is an equivalence.

The quasi-inverse is `Rε_*`, `AlgebraicGeometry.SmallEtale.derivedRestrictModuleQcoh`, as in the
source: the adjunction `ε^* ⊣ Rε_*` restricts to the two derived categories with quasi-coherent
cohomology, where its unit and counit are isomorphisms because `H^q(Rε_* E) = ε_* H^q(E)` for
`E` with quasi-coherent cohomology (Stacks 03DW, 01XB and 0BKZ) and `ε^*` and `ε_*` are mutually
inverse on quasi-coherent modules (Stacks 03DX). -/
@[stacks 071Q]
theorem derivedAssociatedModule_isEquivalence :
    (derivedAssociatedModule.{w} B S hS).IsEquivalence :=
  (derivedAssociatedModuleQcohAdjunction.{w} B S hS).toEquivalence.isEquivalence_functor

/-- **Stacks 071Q**, bundled: the equivalence `D_QCoh(𝒪_S) ≌ D_QCoh(S_étale, 𝒪)` with functor
`ε^*` and quasi-inverse `Rε_*`. -/
def derivedAssociatedModuleEquivalenceQcoh :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory :=
  (derivedAssociatedModuleQcohAdjunction.{w} B S hS).toEquivalence

/-- The functor of `derivedAssociatedModuleEquivalenceQcoh` is `ε^*`. -/
@[simp]
lemma derivedAssociatedModuleEquivalenceQcoh_functor :
    (derivedAssociatedModuleEquivalenceQcoh.{w} B S hS).functor =
      derivedAssociatedModule.{w} B S hS :=
  rfl

/-- The inverse of `derivedAssociatedModuleEquivalenceQcoh` is `Rε_*`. -/
@[simp]
lemma derivedAssociatedModuleEquivalenceQcoh_inverse :
    (derivedAssociatedModuleEquivalenceQcoh.{w} B S hS).inverse =
      derivedRestrictModuleQcoh.{w} B S hS :=
  rfl

end Unconditional

end AlgebraicGeometry.SmallEtale

end
