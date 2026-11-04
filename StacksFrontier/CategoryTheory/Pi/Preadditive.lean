module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Pi
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Products of preadditive categories

A product `∀ i, A i` of preadditive categories is preadditive, with the abelian group structure
on morphisms taken index by index, and the evaluation functors `CategoryTheory.Pi.eval` are
additive for that structure. If every factor has finite limits then evaluation preserves them,
and dually for finite colimits; so if every factor is abelian, evaluation is an exact functor.

## Main definitions

* `CategoryTheory.Pi.preadditive`: the index-by-index preadditive structure on a product of
  preadditive categories.

## Main results

* `CategoryTheory.Pi.eval_additive`: evaluation at an index is additive.
* `CategoryTheory.Pi.preservesFiniteLimits_eval`,
  `CategoryTheory.Pi.preservesFiniteColimits_eval`: evaluation at an index is exact.

## Implementation notes

Limits in a product of categories are computed index by index, which is
`CategoryTheory.pi.coneOfConeEvalIsLimit`. That construction is stated for an index type living in
the same universe as the morphisms of the factors. The exactness statements below reindex along
`Equiv.ulift`, which is possible exactly when the index universe is contained in the morphism
universe; this is expressed by taking the factors to be `Category.{max w r}` for an index type in
`Type w` and an unconstrained `r`.
-/

@[expose] public section

namespace CategoryTheory.Pi

open CategoryTheory.Limits

universe w r v u

/-- A product of preadditive categories is preadditive, with addition of morphisms computed
index by index. -/
instance preadditive {I : Type w} {A : I → Type u} [∀ i, Category.{v} (A i)]
    [∀ i, Preadditive (A i)] : Preadditive (∀ i, A i) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ i, X i ⟶ Y i))
  add_comp _ _ _ f f' g := funext fun i => Preadditive.add_comp _ _ _ (f i) (f' i) (g i)
  comp_add _ _ _ f g g' := funext fun i => Preadditive.comp_add _ _ _ (f i) (g i) (g' i)

/-- Evaluation at an index is additive for the index-by-index preadditive structure. -/
instance eval_additive {I : Type w} {A : I → Type u} [∀ i, Category.{v} (A i)]
    [∀ i, Preadditive (A i)] (i : I) : (Pi.eval A i).Additive where
  map_add := rfl

/-- Evaluation at an index preserves finite limits: a limit in a product of categories is
computed index by index. -/
theorem preservesFiniteLimits_eval {I : Type w} {A : I → Type u}
    [∀ i, Category.{max w r} (A i)] [∀ i, HasFiniteLimits (A i)] (i : I) :
    PreservesFiniteLimits (Pi.eval A i) := by
  let u : ULift.{r} I ≃ I := Equiv.ulift
  have hR : PreservesFiniteLimits (equivalenceOfEquiv A u).inverse :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  have hE : PreservesFiniteLimits (Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
    intro J _ _
    exact ⟨fun {F} => preservesLimit_of_preserves_limit_cone
      (CategoryTheory.pi.coneOfConeEvalIsLimit
        (fun j => limit.isLimit (F ⋙ Pi.eval (fun j : ULift.{r} I => A (u j)) j)))
      (limit.isLimit (F ⋙ Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)))⟩
  have key := @comp_preservesFiniteLimits _ _ _ _ _ _ (equivalenceOfEquiv A u).inverse
    (Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)) hR hE
  have iso : (equivalenceOfEquiv A u).inverse ⋙
      Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i) ≅ Pi.eval A i :=
    Functor.pi'CompEval (fun j : ULift.{r} I => Pi.eval A (u j)) (ULift.up i)
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _ iso key

/-- Evaluation at an index preserves finite colimits: a colimit in a product of categories is
computed index by index. -/
theorem preservesFiniteColimits_eval {I : Type w} {A : I → Type u}
    [∀ i, Category.{max w r} (A i)] [∀ i, HasFiniteColimits (A i)] (i : I) :
    PreservesFiniteColimits (Pi.eval A i) := by
  let u : ULift.{r} I ≃ I := Equiv.ulift
  have hR : PreservesFiniteColimits (equivalenceOfEquiv A u).inverse :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  have hE : PreservesFiniteColimits (Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)) := by
    apply preservesFiniteColimits_of_preservesFiniteColimitsOfSize
    intro J _ _
    exact ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone
      (CategoryTheory.pi.coconeOfCoconeEvalIsColimit
        (fun j => colimit.isColimit (F ⋙ Pi.eval (fun j : ULift.{r} I => A (u j)) j)))
      (colimit.isColimit (F ⋙ Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)))⟩
  have key := @comp_preservesFiniteColimits _ _ _ _ _ _ (equivalenceOfEquiv A u).inverse
    (Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i)) hR hE
  have iso : (equivalenceOfEquiv A u).inverse ⋙
      Pi.eval (fun j : ULift.{r} I => A (u j)) (ULift.up i) ≅ Pi.eval A i :=
    Functor.pi'CompEval (fun j : ULift.{r} I => Pi.eval A (u j)) (ULift.up i)
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _ iso key

end CategoryTheory.Pi

end
