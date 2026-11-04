module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.UnitalGlobalCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# A one-point comparison and a unital global cup product exist

`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S` is the input of the global cup
product of Cohomology, Section 0FKU: a functor `L : D(A) ⥤ D(𝒪_S)` for `A = Γ(S, 𝒪_S)`, an
adjunction `L ⊣ RΓ(S, -)`, and a comparison of bifunctors
`L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`.  `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct` is
the predicate pinning a global cup product down by a unit.  Neither was known to be inhabited,
and a predicate with no witness makes every statement carrying it as a hypothesis vacuous.

This file inhabits both, over the one-point ringed space whose ring is the zero ring.  There
`D(A)` has only zero objects, so `RΓ(S, -)` is the zero functor; the constant functor at `0` is
left adjoint to it, every morphism out of it is the unique one, and the resulting global cup
product satisfies the two unit laws and the commutativity law because their common target
vanishes.  Conversely the unit laws force that vanishing on the zero morphism of bifunctors, so
`IsGlobalCupProduct (0 : GlobalCupProduct S)` holds **exactly** when `RΓ(S, -)` kills every
object of `D(𝒪_S)`; this sharpens
`Stacks.Cohomology.GlobalKunneth.not_isGlobalCupProduct_zero` to an equivalence.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.onePointComparisonOfIsZero` — **a one-point
  comparison** on a ringed space whose derived category of `A`-modules has only zero objects:
  the constant functor at `0`, the unique adjunction, and the unique comparison.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.isZero_of_forall_isZero` — if every object of an
  abelian category is zero then so is every object of its derived category.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_of_isZero_baseSections` — if
  `RΓ(S, -)` kills every object of `D(𝒪_S)` then every global cup product on `S` is unital.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_zero_iff` — the zero morphism of
  bifunctors is a unital global cup product if and only if `RΓ(S, -)` kills every object of
  `D(𝒪_S)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isUnitalWith_onePointComparisonOfIsZero` — the
  comparison constructed here is unital in the sense of
  `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.IsUnitalWith`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.exists_isGlobalCupProduct_globalCupProduct` —
  **there are a ringed space and a one-point comparison on it whose global cup product is a
  unital global cup product.**  So `IsGlobalCupProduct` and `IsUnitalWith` are not vacuous.

## Implementation notes

*Which ringed space.*  `Stacks.AssociatedSheaf.coefficientPoint R` is the one-point ringed space
with structure sheaf the skyscraper at `R`, and its global sections are `R` by
`Stacks.AssociatedSheaf.coefficientPointSectionsIso`.  Taking `R` with `Subsingleton R` makes
`A = Γ(S, 𝒪_S)` the zero ring, over which every module and hence every object of `D(A)` is zero.
Nothing is assumed about sheaves of modules on the point.

*What the witness does and does not show.*  It shows that the predicate has a model, so a
theorem carrying `IsGlobalCupProduct κ` as a hypothesis is not vacuously true and the
construction `globalCupProduct` is not a construction out of an empty type.  It does not produce
a cup product on a ringed space with nonzero cohomology: the adjunction there is the derived
one-point identification `D({*}, A) ≃ D(A)` of Cohomology, Section 0FKU, whose abelian half is
`Stacks.AssociatedSheaf.onePointEquivalence` in this repository and whose promotion to derived
categories, compatibly with the two derived tensor products, is not.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ZeroObject
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-! ### Derived categories of a category with only zero objects -/

section IsZero

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If every object of an abelian category is zero then so is every object of its derived
category, since every such object is the image of a complex with zero terms. -/
theorem isZero_of_forall_isZero (h : ∀ X : C, IsZero X) (Y : DerivedCategory C) : IsZero Y := by
  have h₁ : IsZero (DerivedCategory.Q.objPreimage Y) := by
    rw [IsZero.iff_id_eq_zero]
    ext i
    exact (h _).eq_of_src _ _
  have h₂ : IsZero (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage Y)) := by
    rw [IsZero.iff_id_eq_zero, ← DerivedCategory.Q.map_id, h₁.eq_of_src (𝟙 _) 0,
      DerivedCategory.Q.map_zero]
  exact h₂.of_iso (DerivedCategory.Q.objObjPreimageIso Y).symm

end IsZero

/-! ### Global cup products on a space with vanishing derived global sections -/

variable {S : RingedSpace.{u, u}}

/-- If derived global sections kill every object of `D(𝒪_S)` then every morphism of bifunctors
is a global cup product with any unit: the three laws are equalities of morphisms into a zero
object. -/
theorem isGlobalCupProductWithUnit_of_isZero_baseSections
    (h : ∀ U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      IsZero ((baseSections S).obj U))
    (κ : GlobalCupProduct S) (η : unitBase S ⟶ (baseSections S).obj (unitSheaf S)) :
    IsGlobalCupProductWithUnit κ η where
  right_unit U := (h U).eq_of_tgt _ _
  left_unit U := (h U).eq_of_tgt _ _
  braided _ _ := (h _).eq_of_tgt _ _

/-- If derived global sections kill every object of `D(𝒪_S)` then every morphism of bifunctors is
a unital global cup product. -/
theorem isGlobalCupProduct_of_isZero_baseSections
    (h : ∀ U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      IsZero ((baseSections S).obj U))
    (κ : GlobalCupProduct S) : IsGlobalCupProduct κ :=
  ⟨0, isGlobalCupProductWithUnit_of_isZero_baseSections h κ 0⟩

/-- **The zero morphism of bifunctors is a unital global cup product exactly when derived global
sections vanish identically**, the converse of
`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.isZero_baseSections`. -/
theorem isGlobalCupProduct_zero_iff :
    IsGlobalCupProduct (0 : GlobalCupProduct S) ↔
      ∀ U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
        IsZero ((baseSections S).obj U) :=
  ⟨fun hκ U => hκ.isZero_baseSections U, fun h => isGlobalCupProduct_of_isZero_baseSections h 0⟩

/-! ### A one-point comparison on a space with vanishing derived global sections -/

section Degenerate

variable (S) (h : ∀ x : DerivedCategory (ModuleCat.{u} (baseRing S)), IsZero x)

include h

/-- **The adjunction `0 ⊣ RΓ(S, -)`** on a ringed space whose derived category of
`A = Γ(S, 𝒪_S)`-modules has only zero objects: the constant functor at the zero object of
`D(𝒪_S)` is left adjoint to derived global sections, and the unit, the counit and the two
triangle identities are the unique morphisms and equalities available. -/
def zeroPullbackAdjunction :
    (Functor.const (DerivedCategory (ModuleCat.{u} (baseRing S)))).obj
        (0 : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) ⊣ baseSections S where
  unit :=
    { app := fun x => (h x).to_ _
      naturality := fun _ _ _ => (h _).eq_of_src _ _ }
  counit :=
    { app := fun Y =>
        (isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))).to_ Y
      naturality := fun _ _ _ =>
        (isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))).eq_of_src _ _ }
  left_triangle_components _ :=
    (isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))).eq_of_tgt _ _
  right_triangle_components _ := (h _).eq_of_src _ _

/-- **A one-point comparison** on a ringed space whose derived category of
`A = Γ(S, 𝒪_S)`-modules has only zero objects: the constant functor at `0` with the adjunction
`zeroPullbackAdjunction` and the unique comparison of bifunctors out of it. -/
def onePointComparisonOfIsZero : OnePointComparison S where
  pullback := (Functor.const (DerivedCategory (ModuleCat.{u} (baseRing S)))).obj 0
  adjunction := zeroPullbackAdjunction S h
  tensorComparison :=
    { app := fun _ =>
        (isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))).to_ _
      naturality := fun _ _ _ =>
        (isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))).eq_of_src _ _ }

/-- The one-point comparison of `onePointComparisonOfIsZero` is unital, with unit map the unique
morphism `0 ⟶ 𝒪_S`: both laws are equalities of morphisms out of a zero object. -/
theorem isUnitalWith_onePointComparisonOfIsZero :
    (onePointComparisonOfIsZero S h).IsUnitalWith 0 := by
  have hz := isZero_zero (DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
  exact ⟨fun _ => hz.eq_of_src _ _, fun _ _ => hz.eq_of_src _ _⟩

/-- **The global cup product of `onePointComparisonOfIsZero` is a unital global cup product.** -/
theorem isGlobalCupProduct_globalCupProduct_onePointComparisonOfIsZero :
    IsGlobalCupProduct (globalCupProduct (onePointComparisonOfIsZero S h)) :=
  isGlobalCupProduct_of_isZero_baseSections (fun _ => h _) _

end Degenerate

/-! ### The one-point ringed space with the zero ring -/

section Point

variable (R : CommRingCat.{u}) (hR : Subsingleton R)

include hR

/-- The global sections of the structure sheaf of the one-point ringed space with ring `R` form a
ring isomorphic to `R`, hence are trivial when `R` is. -/
theorem subsingleton_baseRing_coefficientPoint :
    Subsingleton (baseRing (coefficientPoint R)) := by
  have := hR
  exact (((forget CommRingCat.{u}).mapIso
    (coefficientPointSectionsIso R)).toEquiv).symm.subsingleton

/-- Over the zero ring every module is zero, hence so is every object of the derived category. -/
theorem isZero_derivedCategory_coefficientPoint
    (x : DerivedCategory (ModuleCat.{u} (baseRing (coefficientPoint R)))) : IsZero x := by
  have := subsingleton_baseRing_coefficientPoint R hR
  refine isZero_of_forall_isZero (fun M => ?_) x
  have : Subsingleton M :=
    Module.subsingleton (baseRing (coefficientPoint R) : Type u) (M : Type u)
  rw [IsZero.iff_id_eq_zero]
  ext m
  exact Subsingleton.elim _ _

/-- **A one-point comparison on the one-point ringed space with the zero ring.** -/
def onePointComparisonZeroRing : OnePointComparison (coefficientPoint R) :=
  onePointComparisonOfIsZero _ (isZero_derivedCategory_coefficientPoint R hR)

/-- **Its global cup product is a unital global cup product**, so
`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct` has a model. -/
theorem isGlobalCupProduct_globalCupProduct_onePointComparisonZeroRing :
    IsGlobalCupProduct (globalCupProduct (onePointComparisonZeroRing R hR)) :=
  isGlobalCupProduct_globalCupProduct_onePointComparisonOfIsZero _ _

end Point

/-- **A one-point comparison exists, and the global cup product it produces is a unital global
cup product.**  So `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison` is inhabited
and `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct` is not vacuous. -/
theorem exists_isGlobalCupProduct_globalCupProduct :
    ∃ (S : RingedSpace.{u, u}) (c : OnePointComparison S),
      IsGlobalCupProduct (globalCupProduct c) :=
  ⟨coefficientPoint (CommRingCat.of PUnit.{u + 1}),
    onePointComparisonZeroRing _ inferInstance,
    isGlobalCupProduct_globalCupProduct_onePointComparisonZeroRing _ _⟩

/-- A unital global cup product exists. -/
theorem exists_isGlobalCupProduct :
    ∃ (S : RingedSpace.{u, u}) (κ : GlobalCupProduct S), IsGlobalCupProduct κ :=
  let ⟨S, c, hc⟩ := exists_isGlobalCupProduct_globalCupProduct.{u}
  ⟨S, globalCupProduct c, hc⟩

end Stacks.Cohomology.DerivedGlobalCupProduct

end
