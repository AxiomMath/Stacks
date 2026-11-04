module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Unitality of the global cup product

Let `(S, 𝒪_S)` be a ringed space and set `A = Γ(S, 𝒪_S)`.  A morphism of bifunctors

`κ : RΓ(S, U) ⊗^𝐋_A RΓ(S, V) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} V)`

is a `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct`, the datum the global Künneth maps of
Tags 0G7V and 0G49 take as input.  Being a morphism of bifunctors is naturality and nothing
more, and the zero morphism of bifunctors is such a datum; so no property of those Künneth maps
that fails for the zero morphism can be stated against an unrestricted `κ`.

This file imposes on `κ` the part of the symmetric monoidal structure of `RΓ(S, -)` that the
cup product of Cohomology, Section 0FKU carries: a unit `η : A ⟶ RΓ(S, 𝒪_S)` in `D(A)` and the
two unit laws and the commutativity law relating `κ` to the unit and commutativity constraints
of `⊗^𝐋_A` and of `⊗^𝐋_{𝒪_S}`.  The unit laws alone already have the consequence that the
component of `κ` at `(U, 𝒪_S)` is a **split epimorphism**, with an explicit section built from
`η` and the two unit constraints.  In particular the zero morphism satisfies the unit laws only
when `RΓ(S, -)` kills every object of `D(𝒪_S)`.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.unitBase` and `Stacks.Cohomology.GlobalKunneth.unitSheaf` —
  the units `A` of `⊗^𝐋_A` and `𝒪_S` of `⊗^𝐋_{𝒪_S}`, in degree zero.
* `Stacks.Cohomology.GlobalKunneth.baseRightUnitor`,
  `Stacks.Cohomology.GlobalKunneth.baseLeftUnitor`,
  `Stacks.Cohomology.GlobalKunneth.baseComm`,
  `Stacks.Cohomology.GlobalKunneth.sheafRightUnitor`,
  `Stacks.Cohomology.GlobalKunneth.sheafLeftUnitor` and
  `Stacks.Cohomology.GlobalKunneth.sheafComm` — the unit and commutativity constraints of the
  two derived tensor products.
* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit` — the two unit laws and the
  commutativity law for `κ` with respect to a given unit `η`.
* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct` — `κ` admits such a unit.
* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit.splitEpiAppUnit` — the canonical
  section of `κ` at `(U, 𝒪_S)`.

## Main results

* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit.comp_app_unit` — the unit law
  solved for `κ`: tensoring with `η` and then applying `κ` at `(U, 𝒪_S)` is the composite of
  the two unit constraints, hence an isomorphism.
* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit.comp_app_unit_eq` — two cup
  products with a common unit agree at `(U, 𝒪_S)` after tensoring with that unit.
* `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit.isZero_of_app_unit_eq_zero`,
  `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero` and
  `Stacks.Cohomology.GlobalKunneth.not_isGlobalCupProduct_zero` — **the unit laws exclude the
  zero morphism**: if the component of a unital `κ` at `(U, 𝒪_S)` vanishes then `RΓ(S, U) = 0`,
  so a unital `κ` is nonzero as soon as `RΓ(S, -)` is nonzero at a single object, and the zero
  morphism of bifunctors is not unital.

## Implementation notes

*Why a unit and not an identification with the construction.*  Cohomology, Section 0FKU defines
the global cup product as the relative cup product of Tag 0B68 for the morphism from `S` to the
one-point space with ring `A`.  Identifying `κ` with that construction does not by itself
exclude the zero morphism: the construction is the adjoint transpose of a comparison of
bifunctors `L(x ⊗^𝐋_A y) ⟶ Lx ⊗^𝐋_{𝒪_S} Ly`, and that comparison may be zero, in which case
the resulting cup product is zero.  The unit laws are what distinguish the cup product from an
arbitrary natural transformation, and they are stated here against the repository's own unit
constraints, so they can be checked.

*What is and is not imposed.*  The constraints used are those of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` on `D(𝒪_S)` and of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` on `D(A)`, both at a pair of
objects.  The associativity law is **not** imposed: the associativity constraint of `⊗^𝐋_{𝒪_S}`
is not available in this repository, only the unit and commutativity constraints are, so the
associativity law cannot be written down here.  The three laws that are imposed are exactly the
ones that hold for the cup product because `RΓ(S, -)` is lax symmetric monoidal.

*The force of the unit laws.*  The right unit law says that the composite

`RΓ(S, U) ⊗^𝐋_A A ⟶ RΓ(S, U) ⊗^𝐋_A RΓ(S, 𝒪_S) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} 𝒪_S) ⟶ RΓ(S, U)`

is the unit constraint of `⊗^𝐋_A`, which is invertible.  Reading the equation as a factorization
of the identity of `RΓ(S, U ⊗^𝐋_{𝒪_S} 𝒪_S)` exhibits an explicit section of the middle arrow,
`splitEpiAppUnit`; no choice is involved and the section is written out.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### The units and the constraints of the two derived tensor products -/

variable (S : RingedSpace.{u, u})

/-- The ringed space `S` read as a ringed site, the form in which the constraints of the derived
tensor product of Tag 06YU on `D(𝒪_S)` are available. -/
abbrev baseSite : RingedSite.{u, u, u} := AlgebraicGeometry.RingedSpace.ringedSite S

/-- The structure sheaf `𝒪_S` in degree zero: the unit of `⊗^𝐋_{𝒪_S}`. -/
abbrev unitSheaf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  unitObject (baseSite S)

/-- The base ring `A = Γ(S, 𝒪_S)` in degree zero: the unit of `⊗^𝐋_A`. -/
abbrev unitBase : DerivedCategory (ModuleCat.{u} (baseRing S)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} (baseRing S)) 0).obj (ModuleCat.of _ (baseRing S))

/-- The unit constraint `K ⊗^𝐋_A A ≅ K` of the derived tensor product of Tag 064M. -/
abbrev baseRightUnitor (K : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    ((tensorBase S).obj K).obj (unitBase S) ≅ K :=
  CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso K

/-- The commutativity constraint `K ⊗^𝐋_A L ≅ L ⊗^𝐋_A K` of the derived tensor product of
Tag 064M, with the Koszul signs. -/
abbrev baseComm (K L : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    ((tensorBase S).obj K).obj L ≅ ((tensorBase S).obj L).obj K :=
  CochainComplex.DerivedTensor.derivedTensorProductCommIso K L

/-- The unit constraint `A ⊗^𝐋_A K ≅ K`, obtained from the right one by commutativity. -/
abbrev baseLeftUnitor (K : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    ((tensorBase S).obj (unitBase S)).obj K ≅ K :=
  baseComm S (unitBase S) K ≪≫ baseRightUnitor S K

/-- The unit constraint `U ⊗^𝐋_{𝒪_S} 𝒪_S ≅ U` of the derived tensor product of Tag 06YU. -/
abbrev sheafRightUnitor (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((derivedTensorProductFunctor S.sheaf).obj U).obj (unitSheaf S) ≅ U :=
  (canonicalDerivedTensorProduct S.sheaf).rightUnitIso (baseSite S) U

/-- The unit constraint `𝒪_S ⊗^𝐋_{𝒪_S} U ≅ U` of the derived tensor product of Tag 06YU. -/
abbrev sheafLeftUnitor (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((derivedTensorProductFunctor S.sheaf).obj (unitSheaf S)).obj U ≅ U :=
  (canonicalDerivedTensorProduct S.sheaf).leftUnitIso (baseSite S) U

/-- The commutativity constraint `U ⊗^𝐋_{𝒪_S} V ≅ V ⊗^𝐋_{𝒪_S} U` of Tag 0FPT. -/
abbrev sheafComm (U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((derivedTensorProductFunctor S.sheaf).obj U).obj V ≅
      ((derivedTensorProductFunctor S.sheaf).obj V).obj U :=
  (canonicalDerivedTensorProduct S.sheaf).braidingIso (baseSite S) U V

/-! ### Unital global cup products -/

variable {S}

/-- **A global cup product with a unit.**  A `GlobalCupProduct S` together with a unit
`η : A ⟶ RΓ(S, 𝒪_S)` satisfying the two unit laws and the commutativity law of a lax symmetric
monoidal structure on `RΓ(S, -)`: this is what the cup product of Cohomology, Section 0FKU
satisfies and what a bare morphism of bifunctors — the zero morphism, for instance — does
not. -/
structure IsGlobalCupProductWithUnit (κ : GlobalCupProduct S)
    (η : unitBase S ⟶ (baseSections S).obj (unitSheaf S)) : Prop where
  /-- Tensoring with the unit on the right, cupping, and cancelling `𝒪_S` is the unit constraint
  of `⊗^𝐋_A`. -/
  right_unit (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((tensorBase S).obj ((baseSections S).obj U)).map η ≫
        κ.app (U, unitSheaf S) ≫ (baseSections S).map (sheafRightUnitor S U).hom =
      (baseRightUnitor S ((baseSections S).obj U)).hom
  /-- Tensoring with the unit on the left, cupping, and cancelling `𝒪_S` is the unit constraint
  of `⊗^𝐋_A`. -/
  left_unit (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((tensorBase S).map η).app ((baseSections S).obj U) ≫
        κ.app (unitSheaf S, U) ≫ (baseSections S).map (sheafLeftUnitor S U).hom =
      (baseLeftUnitor S ((baseSections S).obj U)).hom
  /-- The cup product commutes with the commutativity constraints of the two derived tensor
  products. -/
  braided (U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    κ.app (U, V) ≫ (baseSections S).map (sheafComm S U V).hom =
      (baseComm S ((baseSections S).obj U) ((baseSections S).obj V)).hom ≫ κ.app (V, U)

/-- **A unital global cup product**: a `GlobalCupProduct S` admitting a unit for which the two
unit laws and the commutativity law hold. -/
def IsGlobalCupProduct (κ : GlobalCupProduct S) : Prop :=
  ∃ η, IsGlobalCupProductWithUnit κ η

/-! ### Three identities of a two-sided factorization of an isomorphism

The three statements below are the content of the right unit law, isolated in an arbitrary
category so that they can be applied to the concrete constraints without rewriting under the
functor `RΓ(S, -)`.  In each of them `ρ` is the unit constraint of `⊗^𝐋_A`, `e` is `RΓ(S, -)`
of the unit constraint of `⊗^𝐋_{𝒪_S}`, and `k` is the component of the cup product. -/

section Factorization

variable {C : Type*} [Category C] {T A B P : C}

/-- A composite factoring an isomorphism, read as a formula for the middle arrow. -/
theorem comp_eq_comp_inv (gη : T ⟶ A) (k : A ⟶ B) (ρ : T ≅ P) (e : B ≅ P)
    (hyp : gη ≫ k ≫ e.hom = ρ.hom) : gη ≫ k = ρ.hom ≫ e.inv := by
  rw [← hyp]
  simp

/-- A composite factoring an isomorphism exhibits a section of the middle arrow. -/
theorem section_comp_eq_id (gη : T ⟶ A) (k : A ⟶ B) (ρ : T ≅ P) (e : B ≅ P)
    (hyp : gη ≫ k ≫ e.hom = ρ.hom) : (e.hom ≫ ρ.inv ≫ gη) ≫ k = 𝟙 B := by
  rw [Category.assoc, Category.assoc, comp_eq_comp_inv gη k ρ e hyp, Iso.inv_hom_id_assoc,
    e.hom_inv_id]

/-- If the middle arrow of such a factorization vanishes, the isomorphism's target is zero. -/
theorem isZero_of_mid_eq_zero [Limits.HasZeroMorphisms C] (gη : T ⟶ A) (k : A ⟶ B)
    (ρ : T ≅ P) (e : B ≅ P) (hyp : gη ≫ k ≫ e.hom = ρ.hom) (hz : k = 0) : IsZero P := by
  have h0 : ρ.hom = 0 := by
    rw [← hyp, hz]
    simp
  rw [IsZero.iff_id_eq_zero, ← ρ.inv_hom_id, h0, Limits.comp_zero]

end Factorization

namespace IsGlobalCupProductWithUnit

variable {κ κ' : GlobalCupProduct S} {η : unitBase S ⟶ (baseSections S).obj (unitSheaf S)}

/-- The right unit law solved for the cup product: tensoring with the unit and then cupping at
`(U, 𝒪_S)` is the composite of the two unit constraints, hence invertible. -/
theorem comp_app_unit (h : IsGlobalCupProductWithUnit κ η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((tensorBase S).obj ((baseSections S).obj U)).map η ≫ κ.app (U, unitSheaf S) =
      (baseRightUnitor S ((baseSections S).obj U)).hom ≫
        (baseSections S).map (sheafRightUnitor S U).inv :=
  comp_eq_comp_inv _ _ (baseRightUnitor S ((baseSections S).obj U))
    ((baseSections S).mapIso (sheafRightUnitor S U)) (h.right_unit U)

/-- Two global cup products with a common unit agree at `(U, 𝒪_S)` after tensoring with that
unit: the unit law determines the cup product there. -/
theorem comp_app_unit_eq (h : IsGlobalCupProductWithUnit κ η)
    (h' : IsGlobalCupProductWithUnit κ' η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((tensorBase S).obj ((baseSections S).obj U)).map η ≫ κ.app (U, unitSheaf S) =
      ((tensorBase S).obj ((baseSections S).obj U)).map η ≫ κ'.app (U, unitSheaf S) := by
  rw [h.comp_app_unit U, h'.comp_app_unit U]

/-- **The canonical section of a unital cup product at `(U, 𝒪_S)`.**  It is the unit constraint
of `⊗^𝐋_{𝒪_S}`, the inverse unit constraint of `⊗^𝐋_A`, and tensoring with the unit; that this
is a section is the right unit law. -/
def splitEpiAppUnit (h : IsGlobalCupProductWithUnit κ η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    SplitEpi (κ.app (U, unitSheaf S)) where
  section_ := (baseSections S).map (sheafRightUnitor S U).hom ≫
    (baseRightUnitor S ((baseSections S).obj U)).inv ≫
      ((tensorBase S).obj ((baseSections S).obj U)).map η
  id :=
    section_comp_eq_id _ _ (baseRightUnitor S ((baseSections S).obj U))
      ((baseSections S).mapIso (sheafRightUnitor S U)) (h.right_unit U)

/-- The component of a unital cup product at `(U, 𝒪_S)` is a split epimorphism. -/
theorem isSplitEpi_app_unit (h : IsGlobalCupProductWithUnit κ η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    IsSplitEpi (κ.app (U, unitSheaf S)) :=
  IsSplitEpi.mk' (h.splitEpiAppUnit U)

/-- **The unit laws exclude the zero morphism.**  If the component of a unital cup product at
`(U, 𝒪_S)` vanishes then `RΓ(S, U)` is the zero object. -/
theorem isZero_of_app_unit_eq_zero (h : IsGlobalCupProductWithUnit κ η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (hz : κ.app (U, unitSheaf S) = 0) : IsZero ((baseSections S).obj U) :=
  isZero_of_mid_eq_zero _ _ (baseRightUnitor S ((baseSections S).obj U))
    ((baseSections S).mapIso (sheafRightUnitor S U)) (h.right_unit U) hz

/-- A unital cup product is nonzero at `(U, 𝒪_S)` whenever `RΓ(S, U)` is nonzero. -/
theorem app_unit_ne_zero (h : IsGlobalCupProductWithUnit κ η)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (hU : ¬ IsZero ((baseSections S).obj U)) : κ.app (U, unitSheaf S) ≠ 0 :=
  fun hz => hU (h.isZero_of_app_unit_eq_zero U hz)

end IsGlobalCupProductWithUnit

/-- A unital global cup product which is the zero morphism of bifunctors forces `RΓ(S, -)` to
kill every object of `D(𝒪_S)`. -/
theorem IsGlobalCupProduct.isZero_baseSections
    (h : IsGlobalCupProduct (0 : GlobalCupProduct S))
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    IsZero ((baseSections S).obj U) := by
  obtain ⟨η, hη⟩ := h
  refine hη.isZero_of_app_unit_eq_zero U ?_
  simp

/-- **The zero morphism of bifunctors is not a unital global cup product**, as soon as derived
global sections are nonzero at a single object of `D(𝒪_S)`. -/
theorem not_isGlobalCupProduct_zero
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (hU : ¬ IsZero ((baseSections S).obj U)) :
    ¬ IsGlobalCupProduct (0 : GlobalCupProduct S) :=
  fun h => hU (h.isZero_baseSections U)

/-- A unital global cup product is nonzero whenever derived global sections are nonzero at a
single object of `D(𝒪_S)`. -/
theorem IsGlobalCupProduct.ne_zero {κ : GlobalCupProduct S} (h : IsGlobalCupProduct κ)
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (hU : ¬ IsZero ((baseSections S).obj U)) : κ ≠ 0 := by
  obtain ⟨η, hη⟩ := h
  intro hκ
  refine hη.app_unit_ne_zero U hU ?_
  rw [hκ]
  simp

end Stacks.Cohomology.GlobalKunneth

end
