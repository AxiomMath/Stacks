module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductUnitality
import StacksCore.Tactic.StacksAttribute

/-!
# The global cup product of a unital one-point comparison is unital

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, and let `c` be an
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S`: a functor
`L : D(A) ⥤ D(𝒪_S)`, an adjunction `L ⊣ RΓ(S, -)` and a comparison of bifunctors
`α : L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`.  The global cup product of Cohomology,
Section 0FKU is the adjoint transpose of `α` followed by the counit in both tensor factors.

`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct` asks of a global cup product `κ` that it
carry a unit `η : A ⟶ RΓ(S, 𝒪_S)` satisfying the two unit laws and the commutativity law.  The
comparison `α` is an unrestricted morphism of bifunctors, so `α = 0` gives a global cup product
that is zero and the laws cannot hold for every `c`.  This file identifies the hypothesis on `c`
that makes them hold: `α` and a map `u : L A ⟶ 𝒪_S` must satisfy the right unit law and the
commutativity law of an **oplax symmetric monoidal structure** on `L`, which is what the
one-point identification supplies for `L = Lf^*`.  The unit is then the transpose `η` of `u`,
and the left unit law is automatic.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.IsUnitalWith` — the oplax
  right unit law and the oplax commutativity law for the comparison of `c` against a map
  `u : L A ⟶ 𝒪_S`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.unitOfComparison` — the unit
  `η : A ⟶ RΓ(S, 𝒪_S)` of the global cup product, the adjoint transpose of `u`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.AreNaturalTensorConstraints` — naturality of the
  unit and commutativity constraints of `⊗^𝐋_{𝒪_S}`, the part of Tag 0FPT that
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` supplies one pair of objects at a time
  and not as a transformation.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProductWithUnit_globalCupProduct` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_globalCupProduct` — **the global
  cup product of a unital one-point comparison is a unital global cup product**, with unit the
  transpose of `u`.  In particular it is not the zero morphism as soon as `RΓ(S, -)` is nonzero
  at a single object, by `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.adjunctionBitensorMap_right_unit`,
  `Stacks.Cohomology.DerivedGlobalCupProduct.adjunctionBitensorMap_left_unit` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.adjunctionBitensorMap_braided` — the three laws for
  the abstract construction of Tag 0B68, in an arbitrary pair of categories with bifunctors,
  units and constraints.  This is the whole computation; the concrete statements are these at
  the adjunction of `c`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.oplaxLeftUnit_of_braided` — the oplax **left** unit
  law follows from the oplax right unit law and the oplax commutativity law, because both left
  unit constraints are the right ones transported along the commutativity constraints.

## Implementation notes

*Why a hypothesis on `c` is unavoidable.*  `OnePointComparison.tensorComparison` is a morphism
of bifunctors and nothing else, so it may be zero; then the global cup product is zero and
`Stacks.Cohomology.GlobalKunneth.not_isGlobalCupProduct_zero` forbids the conclusion whenever
`RΓ(S, -)` is nonzero somewhere.  `IsUnitalWith` is the minimal such hypothesis: it mentions
only `c`, the map `u`, and the constraints of the two derived tensor products, and it is the
restriction to the unit and the braiding of the oplax monoidal structure that the derived
pullback along `S ⟶ ({*}, A)` carries.

*Two laws, not three.*  `IsUnitalWith` has no left unit field.  Both left unit constraints in
use are *defined* as the right ones conjugated by the commutativity constraints — for `⊗^𝐋_A`
by `Stacks.Cohomology.GlobalKunneth.baseLeftUnitor` and for `⊗^𝐋_{𝒪_S}` by
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_eq` — so the oplax left unit
law is a consequence, `oplaxLeftUnit_of_braided`, and so is the naturality of the left unit
constraint.

*What the naturality hypothesis is.*  The constraints of `⊗^𝐋_{𝒪_S}` are built in
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` by replacing an object by a chosen K-flat
model, which is not functorial; accordingly that file supplies them as isomorphisms at a pair of
objects and states that the symmetric monoidal structure of Tag 0FPT is not assembled.  Their
naturality is part of that unassembled structure, is used twice in the computation below — once
to move the counit across the unit constraint and once across the braiding — and is therefore
carried here as `AreNaturalTensorConstraints`.  The corresponding constraints of `⊗^𝐋_A` are
transformations already (`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` has
`rightUnitor` as a natural transformation and the Koszul braiding as a natural isomorphism of
bifunctors), so nothing is assumed on the base side.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-! ### The three laws of the abstract relative cup product

The computation is carried out once, for an adjunction `L ⊣ G` between arbitrary categories
carrying bifunctors `TC` and `TD`, units `oneC` and `oneD`, and a comparison
`α : TC ⋙ L ⟶ (L × L) ⋙ TD`.  Throughout, `ρC`, `ρD` are unit constraints at an object, `bC`,
`bD` are commutativity constraints at a pair of objects, `u : L oneC ⟶ oneD` and `η` is a
transpose of `u`. -/

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
  (TC : C × C ⥤ C) (TD : D × D ⥤ D) (α : TC ⋙ L ⟶ L.prod L ⋙ TD)
  {oneC : C} {oneD : D} (u : L.obj oneC ⟶ oneD) {η : oneC ⟶ G.obj oneD}

/-- **The right unit law of the abstract relative cup product of Tag 0B68.**  If `α` satisfies
the oplax right unit law against `u`, and the unit constraint of `TD` is natural, then tensoring
with the transpose of `u`, cupping, and cancelling `oneD` is the unit constraint of `TC`. -/
theorem adjunctionBitensorMap_right_unit (hη : L.map η ≫ adj.counit.app oneD = u)
    (ρC : ∀ x : C, TC.obj (x, oneC) ≅ x) (ρD : ∀ y : D, TD.obj (y, oneD) ≅ y)
    (hρD : ∀ {Y Y' : D} (f : Y ⟶ Y'),
      TD.map (f ×ₘ 𝟙 oneD) ≫ (ρD Y').hom = (ρD Y).hom ≫ f)
    (hα : ∀ x : C, α.app (x, oneC) ≫ TD.map (𝟙 (L.obj x) ×ₘ u) ≫ (ρD (L.obj x)).hom =
      L.map (ρC x).hom)
    (K : D) :
    TC.map (𝟙 (G.obj K) ×ₘ η) ≫
        adjunctionBitensorMap adj TC TD α K oneD ≫ G.map (ρD K).hom =
      (ρC (G.obj K)).hom := by
  have hα' : (α.app (G.obj K, oneC) ≫ TD.map (𝟙 (L.obj (G.obj K)) ×ₘ u)) ≫
      (ρD (L.obj (G.obj K))).hom = L.map (ρC (G.obj K)).hom := by
    rw [Category.assoc]; exact hα (G.obj K)
  have hcomp : (L.map (𝟙 (G.obj K)) ×ₘ L.map η) ≫
      (adj.counit.app K ×ₘ adj.counit.app oneD) =
      (𝟙 (L.obj (G.obj K)) ×ₘ u) ≫ (adj.counit.app K ×ₘ 𝟙 oneD) := by
    apply Prod.hom_ext <;> simp [hη]
  have hstep : TD.map (L.map (𝟙 (G.obj K)) ×ₘ L.map η) ≫
        TD.map (adj.counit.app K ×ₘ adj.counit.app oneD) ≫ (ρD K).hom =
      TD.map (𝟙 (L.obj (G.obj K)) ×ₘ u) ≫
        (ρD (L.obj (G.obj K))).hom ≫ adj.counit.app K := by
    rw [← Category.assoc, ← Functor.map_comp, hcomp, Functor.map_comp, Category.assoc,
      hρD (Y := L.obj (G.obj K)) (Y' := K) (adj.counit.app K)]
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hnat := α.naturality (𝟙 (G.obj K) ×ₘ η)
  change L.map (TC.map (𝟙 (G.obj K) ×ₘ η)) ≫ α.app (G.obj K, G.obj oneD) =
    α.app (G.obj K, oneC) ≫ TD.map (L.map (𝟙 (G.obj K)) ×ₘ L.map η) at hnat
  rw [← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]
  rw [hstep, ← Category.assoc, ← Category.assoc, hα']

/-- **The left unit law of the abstract relative cup product of Tag 0B68**, the mirror of
`adjunctionBitensorMap_right_unit`. -/
theorem adjunctionBitensorMap_left_unit (hη : L.map η ≫ adj.counit.app oneD = u)
    (lC : ∀ x : C, TC.obj (oneC, x) ≅ x) (lD : ∀ y : D, TD.obj (oneD, y) ≅ y)
    (hlD : ∀ {Y Y' : D} (f : Y ⟶ Y'),
      TD.map (𝟙 oneD ×ₘ f) ≫ (lD Y').hom = (lD Y).hom ≫ f)
    (hα : ∀ x : C, α.app (oneC, x) ≫ TD.map (u ×ₘ 𝟙 (L.obj x)) ≫ (lD (L.obj x)).hom =
      L.map (lC x).hom)
    (K : D) :
    TC.map (η ×ₘ 𝟙 (G.obj K)) ≫
        adjunctionBitensorMap adj TC TD α oneD K ≫ G.map (lD K).hom =
      (lC (G.obj K)).hom := by
  have hα' : (α.app (oneC, G.obj K) ≫ TD.map (u ×ₘ 𝟙 (L.obj (G.obj K)))) ≫
      (lD (L.obj (G.obj K))).hom = L.map (lC (G.obj K)).hom := by
    rw [Category.assoc]; exact hα (G.obj K)
  have hcomp : (L.map η ×ₘ L.map (𝟙 (G.obj K))) ≫
      (adj.counit.app oneD ×ₘ adj.counit.app K) =
      (u ×ₘ 𝟙 (L.obj (G.obj K))) ≫ (𝟙 oneD ×ₘ adj.counit.app K) := by
    apply Prod.hom_ext <;> simp [hη]
  have hstep : TD.map (L.map η ×ₘ L.map (𝟙 (G.obj K))) ≫
        TD.map (adj.counit.app oneD ×ₘ adj.counit.app K) ≫ (lD K).hom =
      TD.map (u ×ₘ 𝟙 (L.obj (G.obj K))) ≫
        (lD (L.obj (G.obj K))).hom ≫ adj.counit.app K := by
    rw [← Category.assoc, ← Functor.map_comp, hcomp, Functor.map_comp, Category.assoc,
      hlD (Y := L.obj (G.obj K)) (Y' := K) (adj.counit.app K)]
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hnat := α.naturality (η ×ₘ 𝟙 (G.obj K))
  change L.map (TC.map (η ×ₘ 𝟙 (G.obj K))) ≫ α.app (G.obj oneD, G.obj K) =
    α.app (oneC, G.obj K) ≫ TD.map (L.map η ×ₘ L.map (𝟙 (G.obj K))) at hnat
  rw [← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]
  rw [hstep, ← Category.assoc, ← Category.assoc, hα']

/-- **The commutativity law of the abstract relative cup product of Tag 0B68.**  If `α` commutes
with the commutativity constraints and the one of `TD` is natural, then so does the adjoint
transpose. -/
theorem adjunctionBitensorMap_braided
    (bC : ∀ x y : C, TC.obj (x, y) ≅ TC.obj (y, x))
    (bD : ∀ y z : D, TD.obj (y, z) ≅ TD.obj (z, y))
    (hbD : ∀ {Y Y' Z Z' : D} (f : Y ⟶ Y') (g : Z ⟶ Z'),
      TD.map (f ×ₘ g) ≫ (bD Y' Z').hom = (bD Y Z).hom ≫ TD.map (g ×ₘ f))
    (hα : ∀ x y : C, α.app (x, y) ≫ (bD (L.obj x) (L.obj y)).hom =
      L.map (bC x y).hom ≫ α.app (y, x))
    (K K' : D) :
    adjunctionBitensorMap adj TC TD α K K' ≫ G.map (bD K K').hom =
      (bC (G.obj K) (G.obj K')).hom ≫ adjunctionBitensorMap adj TC TD α K' K := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Category.assoc,
    hbD (Y := L.obj (G.obj K)) (Y' := K) (Z := L.obj (G.obj K')) (Z' := K')
      (adj.counit.app K) (adj.counit.app K'),
    ← Category.assoc, hα, Category.assoc]

/-- The left unit constraint built from the right one and the commutativity constraint is natural
as soon as those two are. -/
theorem leftUnitor_naturality_of_braided (ρD : ∀ y : D, TD.obj (y, oneD) ≅ y)
    (bD : ∀ y z : D, TD.obj (y, z) ≅ TD.obj (z, y))
    (hρD : ∀ {Y Y' : D} (f : Y ⟶ Y'),
      TD.map (f ×ₘ 𝟙 oneD) ≫ (ρD Y').hom = (ρD Y).hom ≫ f)
    (hbD : ∀ {Y Y' Z Z' : D} (f : Y ⟶ Y') (g : Z ⟶ Z'),
      TD.map (f ×ₘ g) ≫ (bD Y' Z').hom = (bD Y Z).hom ≫ TD.map (g ×ₘ f))
    {Y Y' : D} (f : Y ⟶ Y') :
    TD.map (𝟙 oneD ×ₘ f) ≫ (bD oneD Y' ≪≫ ρD Y').hom =
      (bD oneD Y ≪≫ ρD Y).hom ≫ f := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, hbD (𝟙 oneD) f, Category.assoc, hρD f]

/-- **The oplax left unit law is a consequence of the oplax right unit law and the oplax
commutativity law**, when both left unit constraints are the right ones transported along the
commutativity constraints. -/
theorem oplaxLeftUnit_of_braided (ρC : ∀ x : C, TC.obj (x, oneC) ≅ x)
    (ρD : ∀ y : D, TD.obj (y, oneD) ≅ y)
    (bC : ∀ x y : C, TC.obj (x, y) ≅ TC.obj (y, x))
    (bD : ∀ y z : D, TD.obj (y, z) ≅ TD.obj (z, y))
    (hbD : ∀ {Y Y' Z Z' : D} (f : Y ⟶ Y') (g : Z ⟶ Z'),
      TD.map (f ×ₘ g) ≫ (bD Y' Z').hom = (bD Y Z).hom ≫ TD.map (g ×ₘ f))
    (hαρ : ∀ x : C, α.app (x, oneC) ≫ TD.map (𝟙 (L.obj x) ×ₘ u) ≫ (ρD (L.obj x)).hom =
      L.map (ρC x).hom)
    (hαβ : ∀ x y : C, α.app (x, y) ≫ (bD (L.obj x) (L.obj y)).hom =
      L.map (bC x y).hom ≫ α.app (y, x))
    (x : C) :
    α.app (oneC, x) ≫ TD.map (u ×ₘ 𝟙 (L.obj x)) ≫
        (bD oneD (L.obj x) ≪≫ ρD (L.obj x)).hom =
      L.map (bC oneC x ≪≫ ρC x).hom := by
  have h1 : TD.map (u ×ₘ 𝟙 (L.obj x)) ≫ (bD oneD (L.obj x)).hom ≫ (ρD (L.obj x)).hom =
      (bD (L.obj oneC) (L.obj x)).hom ≫ TD.map (𝟙 (L.obj x) ×ₘ u) ≫ (ρD (L.obj x)).hom := by
    rw [← Category.assoc, hbD (Y := L.obj oneC) (Y' := oneD) (Z := L.obj x) (Z' := L.obj x)
      u (𝟙 _), Category.assoc]
  simp only [Iso.trans_hom, Functor.map_comp]
  rw [h1, ← Category.assoc, hαβ oneC x, Category.assoc, hαρ x]

end Abstract

/-! ### Unital one-point comparisons -/

variable {S : RingedSpace.{u, u}}

namespace OnePointComparison

/-- **The unit of the global cup product of a one-point comparison**, `η : A ⟶ RΓ(S, 𝒪_S)` in
`D(A)`: the adjoint transpose of a map `u : L A ⟶ 𝒪_S`. -/
def unitOfComparison (c : OnePointComparison S)
    (u : c.pullback.obj (unitBase S) ⟶ unitSheaf S) :
    unitBase S ⟶ (baseSections S).obj (unitSheaf S) :=
  c.adjunction.unit.app (unitBase S) ≫ (baseSections S).map u

/-- The transpose of `u` transposes back to `u`. -/
theorem map_unitOfComparison_comp_counit (c : OnePointComparison S)
    (u : c.pullback.obj (unitBase S) ⟶ unitSheaf S) :
    c.pullback.map (unitOfComparison c u) ≫ c.adjunction.counit.app (unitSheaf S) = u := by
  simp [unitOfComparison]

/-- **A unital one-point comparison.**  The comparison of bifunctors
`α : L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y` of `c` satisfies, against a map `u : L A ⟶ 𝒪_S`, the
right unit law and the commutativity law of an oplax symmetric monoidal structure on `L`.  This
is what the derived pullback along `S ⟶ ({*}, A)` carries, and what an unrestricted morphism of
bifunctors — the zero morphism, for instance — does not. -/
structure IsUnitalWith (c : OnePointComparison S)
    (u : c.pullback.obj (unitBase S) ⟶ unitSheaf S) : Prop where
  /-- Comparing and cancelling `𝒪_S` against `u` is `L` of the unit constraint of `⊗^𝐋_A`. -/
  right_unit (x : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    c.tensorComparison.app (x, unitBase S) ≫
        ((derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj x)).map u ≫
          (sheafRightUnitor S (c.pullback.obj x)).hom =
      c.pullback.map (baseRightUnitor S x).hom
  /-- The comparison commutes with the commutativity constraints of the two derived tensor
  products. -/
  braided (x y : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    c.tensorComparison.app (x, y) ≫
        (sheafComm S (c.pullback.obj x) (c.pullback.obj y)).hom =
      c.pullback.map (baseComm S x y).hom ≫ c.tensorComparison.app (y, x)

end OnePointComparison

/-- **Naturality of the constraints of `⊗^𝐋_{𝒪_S}`**, the part of the symmetric monoidal
structure of Tag 0FPT that `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` supplies at a
pair of objects rather than as a transformation.  Only the unit constraint on the right and the
commutativity constraint are needed; the left unit constraint is their composite and inherits
its naturality. -/
structure AreNaturalTensorConstraints (S : RingedSpace.{u, u}) : Prop where
  /-- The unit constraint on the right is natural. -/
  rightUnitor_naturality {U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
      (f : U ⟶ V) :
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (f ×ₘ 𝟙 (unitSheaf S)) ≫
        (sheafRightUnitor S V).hom = (sheafRightUnitor S U).hom ≫ f
  /-- The commutativity constraint is natural in both objects. -/
  comm_naturality {U U' V V' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
      (f : U ⟶ U') (g : V ⟶ V') :
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (f ×ₘ g) ≫
        (sheafComm S U' V').hom =
      (sheafComm S U V).hom ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (g ×ₘ f)

/-! ### The global cup product of a unital one-point comparison -/

/-- **The global cup product of a unital one-point comparison is a unital global cup product**,
with unit the adjoint transpose of `u`: the two unit laws and the commutativity law of
`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit` hold for
`Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct c`. -/
theorem isGlobalCupProductWithUnit_globalCupProduct {c : OnePointComparison S}
    {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S} (hu : c.IsUnitalWith u)
    (hS : AreNaturalTensorConstraints S) :
    IsGlobalCupProductWithUnit (globalCupProduct c) (c.unitOfComparison u) := by
  have hη := c.map_unitOfComparison_comp_counit u
  have hαρ : ∀ x : DerivedCategory (ModuleCat.{u} (baseRing S)),
      c.tensorComparison.app (x, unitBase S) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
            (𝟙 (c.pullback.obj x) ×ₘ u) ≫ (sheafRightUnitor S (c.pullback.obj x)).hom =
        c.pullback.map (baseRightUnitor S x).hom := fun x =>
    (congrArg (fun m => c.tensorComparison.app (x, unitBase S) ≫ m ≫
          (sheafRightUnitor S (c.pullback.obj x)).hom)
        (uncurry_map_id_left (derivedTensorProductFunctor S.sheaf)
          (c.pullback.obj x) u)).trans (hu.right_unit x)
  have hAlphaLeft : ∀ x : DerivedCategory (ModuleCat.{u} (baseRing S)),
      c.tensorComparison.app (unitBase S, x) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
            (u ×ₘ 𝟙 (c.pullback.obj x)) ≫
            (sheafComm S (unitSheaf S) (c.pullback.obj x) ≪≫
              sheafRightUnitor S (c.pullback.obj x)).hom =
        c.pullback.map (baseComm S (unitBase S) x ≪≫ baseRightUnitor S x).hom := fun x =>
    oplaxLeftUnit_of_braided (TC := Functor.uncurry.obj (tensorBase S))
      (TD := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
      (α := c.tensorComparison) (u := u) (ρC := baseRightUnitor S) (ρD := sheafRightUnitor S)
      (bC := baseComm S) (bD := sheafComm S) (hbD := fun f g => hS.comm_naturality f g)
      (hαρ := hαρ) (hαβ := fun y z => hu.braided y z) (x := x)
  refine ⟨fun U => ?_, fun U => ?_, fun U V => ?_⟩
  · exact (congrArg (fun m => m ≫ (globalCupProduct c).app (U, unitSheaf S) ≫
          (baseSections S).map (sheafRightUnitor S U).hom)
        (uncurry_map_id_left (tensorBase S) ((baseSections S).obj U)
          (c.unitOfComparison u))).symm.trans
      (adjunctionBitensorMap_right_unit (adj := c.adjunction)
        (TC := Functor.uncurry.obj (tensorBase S))
        (TD := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
        (α := c.tensorComparison) (u := u) (hη := hη) (ρC := baseRightUnitor S)
        (ρD := sheafRightUnitor S) (hρD := fun f => hS.rightUnitor_naturality f)
        (hα := hαρ) (K := U))
  · exact (congrArg (fun m => m ≫ (globalCupProduct c).app (unitSheaf S, U) ≫
          (baseSections S).map (sheafLeftUnitor S U).hom)
        (uncurry_map_id_right (tensorBase S) (c.unitOfComparison u)
          ((baseSections S).obj U))).symm.trans
      (adjunctionBitensorMap_left_unit (adj := c.adjunction)
        (TC := Functor.uncurry.obj (tensorBase S))
        (TD := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
        (α := c.tensorComparison) (u := u) (hη := hη)
        (lC := fun x => baseComm S (unitBase S) x ≪≫ baseRightUnitor S x)
        (lD := fun Y => sheafComm S (unitSheaf S) Y ≪≫ sheafRightUnitor S Y)
        (hlD := fun f => leftUnitor_naturality_of_braided
          (TD := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (ρD := sheafRightUnitor S) (bD := sheafComm S)
          (hρD := fun g => hS.rightUnitor_naturality g)
          (hbD := fun g h => hS.comm_naturality g h) (f := f))
        (hα := hAlphaLeft) (K := U))
  · exact adjunctionBitensorMap_braided (adj := c.adjunction)
      (TC := Functor.uncurry.obj (tensorBase S))
      (TD := Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
      (α := c.tensorComparison) (bC := baseComm S) (bD := sheafComm S)
      (hbD := fun f g => hS.comm_naturality f g) (hα := fun x y => hu.braided x y)
      (K := U) (K' := V)

/-- **The global cup product of a unital one-point comparison is a unital global cup product.**
Together with `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero` this says that it is
nonzero as soon as derived global sections are nonzero at a single object of `D(𝒪_S)`. -/
theorem isGlobalCupProduct_globalCupProduct {c : OnePointComparison S}
    {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S} (hu : c.IsUnitalWith u)
    (hS : AreNaturalTensorConstraints S) :
    IsGlobalCupProduct (globalCupProduct c) :=
  ⟨c.unitOfComparison u, isGlobalCupProductWithUnit_globalCupProduct hu hS⟩

/-- The global cup product of a unital one-point comparison is nonzero as soon as `RΓ(S, -)` is
nonzero at a single object of `D(𝒪_S)`. -/
theorem globalCupProduct_ne_zero {c : OnePointComparison S}
    {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S} (hu : c.IsUnitalWith u)
    (hS : AreNaturalTensorConstraints S)
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (hU : ¬ IsZero ((baseSections S).obj U)) : globalCupProduct c ≠ 0 :=
  (isGlobalCupProduct_globalCupProduct hu hS).ne_zero hU

end Stacks.Cohomology.DerivedGlobalCupProduct

end
