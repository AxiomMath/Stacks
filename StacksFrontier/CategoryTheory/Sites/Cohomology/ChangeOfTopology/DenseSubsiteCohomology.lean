module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyAlongAnAdjunction

/-!
# Sheaf cohomology is unchanged by restriction to a dense subsite

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`, and assume the Comparison
Lemma for abelian sheaves, that is, that restriction of sections along `G` is an equivalence
`Sheaf K AddCommGrpCat ≌ Sheaf J AddCommGrpCat`. This file shows that the cohomology of an
abelian sheaf on `(D, K)` agrees with the cohomology of its restriction to `(C, J)`, in every
degree and naturally in the sheaf.

## Main definitions and results

* `Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso`: restriction to the dense subsite
  carries the constant sheaf to the constant sheaf.
* `Stacks.Cohomology.DenseSubsite.hAddEquiv`: the resulting isomorphism of cohomology groups
  `H^n(D, F) ≅ H^n(C, F|_C)`.
* `Stacks.Cohomology.DenseSubsite.hAddEquiv_map`: it is compatible with the map induced on
  cohomology by a morphism of sheaves.

## Implementation notes

The one piece of data that `Stacks.ExtAdjunction.hComparison` needs and that is not formal is a
comparison of the two constant sheaves. Mathlib's `CategoryTheory.equivCommuteConstant` supplies
one, but only for sites with terminal objects matched by `G`; the small étale site of an
algebraic space has no terminal object, so that form is unusable here.
`constantSheafRestrictionIso` avoids the hypothesis: restriction of presheaves along `G.op`
carries the *constant presheaf* to the constant presheaf on the nose, and
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility` says that
restriction commutes with sheafification. Whiskering that natural isomorphism by
`CategoryTheory.Functor.const` is already the statement, with no transport: the identification
`Functor.const Dᵒᵖ ⋙ (whiskeringLeft _ _ _).obj G.op = Functor.const Cᵒᵖ` holds by `rfl`.

The direction of the adjunction is the one in which restriction is the *left* adjoint of the
equivalence read backwards, so `Stacks.ExtAdjunction.hComparison` is instantiated with its two
sites interchanged; consequently the hypothesis `EnoughInjectives` is required on the *subsite*
`(C, J)`, which is the small one in every intended application.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

universe a t u₁ v₁ u₂ v₂

namespace Stacks.Cohomology.DenseSubsite

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [HasWeakSheafify J AddCommGrpCat.{t}] [HasWeakSheafify K AddCommGrpCat.{t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).IsEquivalence]

/-- **Restriction to a dense subsite carries the constant sheaf to the constant sheaf.**

No terminal object is needed on either site: the constant *presheaf* restricts to the constant
presheaf by definition, and restriction commutes with sheafification. -/
def constantSheafRestrictionIso :
    constantSheaf K AddCommGrpCat.{t} ⋙ G.sheafPushforwardContinuous AddCommGrpCat.{t} J K ≅
      constantSheaf J AddCommGrpCat.{t} :=
  (Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
    (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K G AddCommGrpCat.{t})).symm

section Cohomology

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [HasExt.{a} (Sheaf J AddCommGrpCat.{t})] [HasExt.{a} (Sheaf K AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{t})]

/-- Restriction to a dense subsite is an additive functor. -/
instance restrictionAdditive :
    (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of restriction to a dense subsite is an additive functor. -/
instance sheafEquivFunctorAdditive :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{t}).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The same statement for the equivalence read backwards, in the syntactic form that instance
search needs at `Stacks.ExtAdjunction.hComparison_bijective`. -/
instance sheafEquivSymmInverseAdditive :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{t}).symm.inverse.Additive :=
  sheafEquivFunctorAdditive J K G

omit [HasWeakSheafify J AddCommGrpCat.{t}] [HasWeakSheafify K AddCommGrpCat.{t}]
    [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
    [HasExt.{a} (Sheaf J AddCommGrpCat.{t})] [HasExt.{a} (Sheaf K AddCommGrpCat.{t})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{t})] in
/-- The unit of the adjunction exhibiting restriction as a left adjoint is an isomorphism,
being the unit of an equivalence. -/
theorem sheafEquivSymmToAdjunctionUnitIsIso :
    IsIso (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{t}).symm.toAdjunction.unit := by
  rw [Equivalence.toAdjunction_unit]
  infer_instance

/-- **Cohomology is unchanged by restriction to a dense subsite.** The cohomology of an abelian
sheaf on `(D, K)` is the cohomology of its restriction to the dense subsite `(C, J)`, in every
degree. -/
def hAddEquiv (F : Sheaf K AddCommGrpCat.{t}) (n : ℕ) :
    Sheaf.H.{a} F n ≃+
      Sheaf.H.{a} ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj F) n :=
  let adj : G.sheafPushforwardContinuous AddCommGrpCat.{t} J K ⊣
      (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{t}).functor :=
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{t}).symm.toAdjunction
  haveI : IsIso adj.unit := sheafEquivSymmToAdjunctionUnitIsIso J K G
  AddEquiv.ofBijective
    (Stacks.ExtAdjunction.hComparison (constantSheafRestrictionIso J K G) n F)
    (Stacks.ExtAdjunction.hComparison_bijective (constantSheafRestrictionIso J K G) adj n F)

/-- The comparison of cohomology groups is compatible with the maps induced by a morphism of
sheaves. -/
theorem hAddEquiv_map {F F' : Sheaf K AddCommGrpCat.{t}} (f : F ⟶ F') (n : ℕ)
    (x : Sheaf.H.{a} F n) :
    hAddEquiv J K G F' n (Sheaf.H.map.{a} f n x) =
      Sheaf.H.map.{a}
        ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).map f) n
        (hAddEquiv J K G F n x) :=
  Stacks.ExtAdjunction.hComparison_naturality (constantSheafRestrictionIso J K G) n f x

end Cohomology

end Stacks.Cohomology.DenseSubsite

end
