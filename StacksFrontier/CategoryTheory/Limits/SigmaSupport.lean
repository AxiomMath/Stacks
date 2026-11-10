module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# A coproduct is the coproduct of the summands that are not zero

A coproduct `∐ P` over an index type `ι` whose summands `P i` are zero outside a predicate `p`
is the coproduct of the family restricted to the subtype `{i // p i}`. The comparison is the
cofan of the inclusions of the summands where `p` holds, and its inverse is the cofan which is
the inclusion into the subtype coproduct where `p` holds and zero where it does not.

The case of a single nonzero summand is `CategoryTheory.Limits.sigmaIsoOfIsZero`.

## Main definitions

* `CategoryTheory.Limits.sigmaSubtypeIsoOfIsZero`: the isomorphism
  `(∐ fun j : {i // p i} => P j.1) ≅ ∐ P`.
* `CategoryTheory.Retract.sigma`: a coproduct of retracts is a retract of the coproducts.

## Main results

* `CategoryTheory.Limits.ι_comp_sigmaSubtypeIsoOfIsZero_hom`: the comparison carries each
  inclusion of the subtype coproduct to the corresponding inclusion of `∐ P`.
* `CategoryTheory.Limits.sigmaSubtypeIsoOfIsZero_hom_comp_ι`: the inverse carries the inclusion
  of `P i`, for `p i`, to the corresponding inclusion of the subtype coproduct.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {ι : Type*}

open Limits

/-- **A coproduct of retracts is a retract of the coproducts.** The inclusion and the retraction
are the coproducts of the inclusions and of the retractions, and their composite is the
coproduct of the identities. -/
noncomputable def Retract.sigma {X Y : ι → C} [HasCoproduct X] [HasCoproduct Y]
    (ρ : ∀ i, Retract (X i) (Y i)) : Retract (∐ X) (∐ Y) where
  i := Limits.Sigma.map fun i => (ρ i).i
  r := Limits.Sigma.map fun i => (ρ i).r
  retract := by
    rw [Limits.Sigma.map_comp_map]
    exact Eq.trans (congrArg Limits.Sigma.map (funext fun i => (ρ i).retract))
      Limits.Sigma.map_id

namespace Limits

variable [HasZeroMorphisms C]

/-- **A coproduct whose summands vanish outside a predicate is the coproduct over that
predicate.** The isomorphism is the cofan of the inclusions of the summands where `p` holds; its
inverse is the inclusion on a summand where `p` holds and zero on one where it does not. -/
noncomputable def sigmaSubtypeIsoOfIsZero (P : ι → C) (p : ι → Prop) [DecidablePred p]
    [HasCoproduct P] [HasCoproduct fun j : Subtype p => P j.1]
    (h : ∀ i, ¬ p i → IsZero (P i)) :
    (∐ fun j : Subtype p => P j.1) ≅ ∐ P where
  hom := Sigma.desc fun j => Sigma.ι P j.1
  inv := Sigma.desc fun i =>
    if hi : p i then Sigma.ι (fun j : Subtype p => P j.1) ⟨i, hi⟩ else 0
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Category.comp_id, ← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc, dite_eq_left j.2]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Category.comp_id, ← Category.assoc, Sigma.ι_comp_desc]
    by_cases hi : p i
    · rw [dite_eq_left hi, Sigma.ι_comp_desc]
    · rw [dite_eq_right hi, Limits.zero_comp]
      exact ((h i hi).eq_of_src (Sigma.ι P i) 0).symm

/-- The isomorphism `sigmaSubtypeIsoOfIsZero P p h` carries the inclusion of the summand indexed
by `j : Subtype p` to the inclusion of `P j.1` into `∐ P`. -/
@[reassoc]
lemma ι_comp_sigmaSubtypeIsoOfIsZero_hom (P : ι → C) (p : ι → Prop) [DecidablePred p]
    [HasCoproduct P] [HasCoproduct fun j : Subtype p => P j.1]
    (h : ∀ i, ¬ p i → IsZero (P i)) (j : Subtype p) :
    Sigma.ι (fun j : Subtype p => P j.1) j ≫ (sigmaSubtypeIsoOfIsZero P p h).hom =
      Sigma.ι P j.1 :=
  Sigma.ι_comp_desc _ _

/-- The inverse of `sigmaSubtypeIsoOfIsZero P p h` carries the inclusion of `P i` into `∐ P`, for
`p i`, to the inclusion of the summand indexed by `⟨i, hi⟩` into the subtype coproduct. -/
@[reassoc]
lemma sigmaSubtypeIsoOfIsZero_hom_comp_ι (P : ι → C) (p : ι → Prop) [DecidablePred p]
    [HasCoproduct P] [HasCoproduct fun j : Subtype p => P j.1]
    (h : ∀ i, ¬ p i → IsZero (P i)) {i : ι} (hi : p i) :
    Sigma.ι P i ≫ (sigmaSubtypeIsoOfIsZero P p h).inv =
      Sigma.ι (fun j : Subtype p => P j.1) ⟨i, hi⟩ := by
  rw [sigmaSubtypeIsoOfIsZero, Sigma.ι_comp_desc, dite_eq_left hi]

end Limits

end CategoryTheory

end
