module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupWithCohomologyClass
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensorComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence

/-!
# The global cup product of the one-point comparison is invertible

Let `R` be a commutative ring and `({*}, R)` the one-point ringed space.  The global cup product
of Cohomology, Section 0FKU and the map `ξ ∪ -` of Remark 0G6W are both built in this repository
from one parameter, `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison`: a left
adjoint `L` of `RΓ(S, -)` together with a comparison of bifunctors
`α : L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`.  The field `α` is an unrestricted morphism of
bifunctors, so the structure is inhabited by data with `α = 0`, and three of its inhabitants
have exactly that; for those the global cup product is zero and everything stated about it is
true of a zero map.

`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComparisonWithTensor` is the inhabitant whose
`α` is the genuine comparison of the two derived tensor products on the point, which
`Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_onePointTensorComparison` says is *invertible*.
This file draws the consequence: at that datum the global cup product is invertible at every
pair of objects, hence nonzero, and the map `ξ ∪ -` of Remark 0G6W vanishes exactly when `ξ ⊗ 1`
does.  So the statements of Section 0FKU and of Remark 0G6W in this repository hold at a datum
that is not degenerate, and the witness needs no unitality hypothesis.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.isIso_adjunctionBitensorMap` — **the abstract
  relative cup product of Tag 0B68 is invertible when the adjunction is an adjoint equivalence
  and the comparison is invertible.**  It is the adjoint transpose of `α` followed by the counit
  in both tensor factors, and the transpose is `unit ≫ G.map -`, so all three inputs enter as
  isomorphisms.
* `Stacks.Cohomology.GlobalKunneth.ne_zero_of_isIso_app_unit` — a global cup product which is
  invertible at `(U, 𝒪_S)` is nonzero as soon as `RΓ(S, U)` is nonzero.  This replaces, for an
  invertible cup product, the route through
  `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero`, which needs a unit and its laws.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_globalCupProduct_app` — **the global cup
  product of `onePointComparisonWithTensor` is invertible at every pair**,
  `RΓ({*}, K) ⊗^𝐋_A RΓ({*}, M) ≅ RΓ({*}, K ⊗^𝐋_{𝒪} M)`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.globalCupProduct_onePointComparisonWithTensor_ne_zero`
  — **it is nonzero, unconditionally**, for a nontrivial ring.
  `DerivedSectionsOnAPoint.globalCupProduct_onePointComparisonWithTensor_ne_zero_of_model`
  concludes the same thing from the two undischarged model identities
  `Stacks.Cohomology.DerivedSectionsOnAPoint.ModelRightUnitLaw` and
  `Stacks.Cohomology.DerivedSectionsOnAPoint.ModelBraidingLaw`; neither is needed for
  nonvanishing.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass_eq_zero_iff` — **the map `ξ ∪ -` of
  Remark 0G6W vanishes exactly when `ξ ⊗ 1` does**, whenever the global cup product is invertible
  at the pair.  Both outer factors of the defining composition are then isomorphisms.

## Implementation notes

*Nothing here is tagged.*  Non-degeneracy of the parameter is a statement about this
repository's presentation of Section 0FKU, not a clause of the Stacks text: the source has no
`OnePointComparison`, it has the one-point space, for which the comparison is invertible by
construction.  The clauses of Remark 0G6W are tagged where they are stated, on
`Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass`,
`...homologyFromSingle_cupWithClass` and `...homologyFromSingle_cupWithClass_cupPairing`, and
none of them is restated here.

*Why the adjunction is an adjoint equivalence.*  The left adjoint of
`onePointComparisonWithTensor` is the one-point identification `E` read on derived categories.
`E` is an additive equivalence of abelian categories, so `E.mapDerivedCategory` is an
equivalence of derived categories (`Stacks.Injectives.mapDerivedCategory_isEquivalence`), and
Mathlib's `CategoryTheory.Adjunction` instances then make the unit and the counit of any
adjunction with that left adjoint invertible.  This is the one-point case of what Tag 0D5W does
on a general space, where neither is invertible.

*What this does not give.*  Not `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct`: that asks
for a unit satisfying the two unit laws and the commutativity law, and invertibility of the
three data does not produce the *equalities* those laws assert.  The route to them remains
`Stacks.Cohomology.DerivedSectionsOnAPoint.isUnitalWith_onePointUnitMap_of_model`, whose two
hypotheses are still open.  What is removed here is the dependence of *nonvanishing* on them.

## References

* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

/-! ### The abstract relative cup product of an adjoint equivalence -/

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract relative cup product of Tag 0B68 is invertible for an adjoint equivalence and
an invertible comparison.**  It is `adj.homEquiv` of `α` followed by the counit in both tensor
factors; the transpose is `unit ≫ G.map -`, so the unit, the two counit components and `α` all
enter as isomorphisms and the composite is one.

The three hypotheses are the whole transformations rather than their components: stated
componentwise they are not found by instance search at the derived categories this is applied
to, while the components of a transformation known to be invertible are. -/
lemma isIso_adjunctionBitensorMap (K K' : D)
    (hu : IsIso adj.unit) (hc : IsIso adj.counit) (hα : IsIso α) :
    IsIso (adjunctionBitensorMap adj A B α K K') := by
  have := hu
  have := hc
  have := hα
  have : IsIso (adj.counit.app K ×ₘ adj.counit.app K') :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  rw [adjunctionBitensorMap, Adjunction.homEquiv_unit]
  infer_instance

end Abstract

end Stacks.Cohomology.DerivedRelativeCupProduct

/-! ### An invertible global cup product is nonzero -/

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}}

/-- If a global cup product is invertible at `(U, 𝒪_S)` and vanishes there, then `RΓ(S, U)` is
the zero object: the target `RΓ(S, U ⊗^𝐋_{𝒪_S} 𝒪_S)` of an invertible zero morphism is zero, and
the unit constraint of Tag 0FPT identifies it with `RΓ(S, U)`.

This is the analogue of
`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProductWithUnit.isZero_of_app_unit_eq_zero` with
invertibility in place of the unit law; neither hypothesis implies the other. -/
theorem isZero_baseSections_of_isIso_app_unit (κ : GlobalCupProduct S)
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (hiso : IsIso (κ.app (U, unitSheaf S))) (hz : κ.app (U, unitSheaf S) = 0) :
    IsZero ((baseSections S).obj U) := by
  rw [hz] at hiso
  have htgt : IsZero ((baseSections S).obj
      (((derivedTensorProductFunctor S.sheaf).obj U).obj (unitSheaf S))) := by
    rw [IsZero.iff_id_eq_zero]
    have h := @IsIso.inv_hom_id _ _ _ _ _ hiso
    rw [comp_zero] at h
    exact h.symm
  exact htgt.of_iso ((baseSections S).mapIso (sheafRightUnitor S U)).symm

/-- **A global cup product invertible at `(U, 𝒪_S)` is nonzero** as soon as `RΓ(S, U)` is
nonzero.  Unlike `Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero` this asks for no
unit and no unit law. -/
theorem ne_zero_of_isIso_app_unit (κ : GlobalCupProduct S)
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (hiso : IsIso (κ.app (U, unitSheaf S))) (hU : ¬ IsZero ((baseSections S).obj U)) :
    κ ≠ 0 := by
  intro hκ
  refine hU (isZero_baseSections_of_isIso_app_unit κ U hiso ?_)
  rw [hκ]
  simp

end Stacks.Cohomology.GlobalKunneth

/-! ### When `ξ ∪ -` vanishes -/

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-- A composite with invertible outer factors vanishes exactly when its middle factor does.
Every category, object and morphism is a variable, so applying it is a single unification. -/
private lemma comp_comp_eq_zero_iff {C : Type*} [Category C] [HasZeroMorphisms C]
    {W X Y Z : C} (a : W ⟶ X) (f : X ⟶ Y) (b : Y ⟶ Z) (ha : IsIso a) (hb : IsIso b) :
    a ≫ f ≫ b = 0 ↔ f = 0 := by
  have := ha
  have := hb
  constructor
  · intro h
    have h1 : f ≫ b = 0 := by rw [← cancel_epi a, h, comp_zero]
    rw [← cancel_mono b, h1, zero_comp]
  · intro h
    rw [h, zero_comp, comp_zero]

variable {X : RingedSpace.{u, u}}

/-- **The map `ξ ∪ -` of Remark 0G6W vanishes exactly when `ξ ⊗ 1` does**, whenever the global
cup product is invertible at the pair.  The defining composition of
`Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass` is the identification
`RΓ(X, M)[-i] = A[-i] ⊗^𝐋_A RΓ(X, M)`, then `ξ ⊗ 1`, then the global cup product `μ`; the first
is an isomorphism always and the third is one by hypothesis.

For the one-point comparison with a genuine tensor comparison the hypothesis holds at every
pair, by
`Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_globalCupProduct_app`. -/
theorem cupWithClass_eq_zero_iff (c : OnePointComparison X)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (hμ : IsIso ((globalCupProduct c).app (K, M))) :
    cupWithClass c K M i ξ = 0 ↔
      ((tensorBase X).map (classRepresentative K i ξ)).app ((baseSections X).obj M) = 0 :=
  comp_comp_eq_zero_iff _ _ _ (Iso.isIso_inv _) hμ

end Stacks.Cohomology.DerivedGlobalCupProduct

/-! ### The one-point comparison with a genuine tensor comparison -/

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

open Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- **The one-point identification is an equivalence of derived categories.**  It is an additive
equivalence of abelian categories, and `Stacks.Injectives.mapDerivedCategory_isEquivalence`
carries that to the derived categories. -/
instance onePointDerived_isEquivalence :
    ((onePointSectionsEquivalence R).functor.mapDerivedCategory).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence (onePointSectionsEquivalence R).functor

/-- The unit of `E ⊣ RΓ({*}, -)` is invertible: `E` is an equivalence of derived categories. -/
theorem isIso_onePointDerivedAdjunction_unit :
    IsIso (onePointDerivedAdjunction R).unit := inferInstance

/-- The counit of `E ⊣ RΓ({*}, -)` is invertible, for the same reason. -/
theorem isIso_onePointDerivedAdjunction_counit :
    IsIso (onePointDerivedAdjunction R).counit := inferInstance

/-- The adjunction of `onePointComparisonWithTensor` is `onePointDerivedAdjunction`. -/
theorem onePointComparisonWithTensor_adjunction :
    (onePointComparisonWithTensor R).adjunction = onePointDerivedAdjunction R := rfl

/-- The unit of the adjunction carried by `onePointComparisonWithTensor` is invertible. -/
theorem isIso_onePointComparisonWithTensor_unit :
    IsIso (onePointComparisonWithTensor R).adjunction.unit :=
  isIso_onePointDerivedAdjunction_unit R

/-- The counit of the adjunction carried by `onePointComparisonWithTensor` is invertible. -/
theorem isIso_onePointComparisonWithTensor_counit :
    IsIso (onePointComparisonWithTensor R).adjunction.counit :=
  isIso_onePointDerivedAdjunction_counit R

/-- The tensor comparison carried by `onePointComparisonWithTensor` is invertible: it is
`onePointTensorComparison`, the morphism underlying `onePointDerivedTensorIso`.  This is what
fails for the three inhabitants of `OnePointComparison` whose comparison is the zero
morphism. -/
theorem isIso_onePointComparisonWithTensor_tensorComparison :
    IsIso (onePointComparisonWithTensor R).tensorComparison :=
  isIso_onePointTensorComparison R

/-- **The global cup product of the one-point comparison with a genuine tensor comparison is
invertible at every pair**:

`μ : RΓ({*}, K) ⊗^𝐋_A RΓ({*}, M) ≅ RΓ({*}, K ⊗^𝐋_{𝒪} M)`.

All three inputs of the construction of Tag 0B68 are isomorphisms on the point — the unit and
the counit because `E ⊣ RΓ({*}, -)` is an adjoint equivalence, and the tensor comparison because
it is the morphism underlying `onePointDerivedTensorIso` — so
`Stacks.Cohomology.DerivedRelativeCupProduct.isIso_adjunctionBitensorMap` applies. -/
theorem isIso_globalCupProduct_app
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)))) :
    IsIso ((globalCupProduct (onePointComparisonWithTensor R)).app (K, M)) := by
  rw [globalCupProduct_app]
  exact Stacks.Cohomology.DerivedRelativeCupProduct.isIso_adjunctionBitensorMap
    _ _ _ _ K M (isIso_onePointComparisonWithTensor_unit R)
    (isIso_onePointComparisonWithTensor_counit R)
    (isIso_onePointComparisonWithTensor_tensorComparison R)

/-- **The global cup product of the one-point comparison with a genuine tensor comparison is
nonzero**, for a nontrivial ring, with no further hypothesis.  Derived global sections on
`({*}, R)` do not vanish identically
(`Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections`), and at such an
object the cup product is invertible, hence nonzero.

`globalCupProduct_onePointComparisonWithTensor_ne_zero_of_model`
draws the same conclusion from `ModelRightUnitLaw` and `ModelBraidingLaw`, which are open; this
shows nonvanishing does not depend on them.  What still does is unitality itself. -/
theorem globalCupProduct_onePointComparisonWithTensor_ne_zero [Nontrivial R] :
    globalCupProduct (onePointComparisonWithTensor R) ≠ 0 := by
  obtain ⟨U, hU⟩ := not_forall.1 (not_forall_isZero_baseSections R)
  exact ne_zero_of_isIso_app_unit _ (isIso_globalCupProduct_app R U _) hU

/-- **The map `ξ ∪ -` of Remark 0G6W on the point vanishes exactly when `ξ ⊗ 1` does.**  This is
`Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClass_eq_zero_iff` at the one-point comparison
with a genuine tensor comparison, where the global cup product is invertible at every pair.  At
a comparison with `α = 0` the statement is empty, both sides being zero for every `ξ`. -/
theorem cupWithClass_onePointComparisonWithTensor_eq_zero_iff
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))))
    (i : ℤ)
    (ξ : ModuleCat.of (baseRing (onePointRingedSpace R)) (baseRing (onePointRingedSpace R)) ⟶
      cohomologyModule K i) :
    cupWithClass (onePointComparisonWithTensor R) K M i ξ = 0 ↔
      ((tensorBase (onePointRingedSpace R)).map (classRepresentative K i ξ)).app
        ((baseSections (onePointRingedSpace R)).obj M) = 0 :=
  cupWithClass_eq_zero_iff _ K M i ξ (isIso_globalCupProduct_app R K M)

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
