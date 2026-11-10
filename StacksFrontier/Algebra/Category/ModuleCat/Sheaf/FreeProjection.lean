module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Coordinate projections of a free sheaf of modules

For a sheaf of rings `R` on a site and a type `I`, the free sheaf of modules
`SheafOfModules.free I` is the coproduct of copies of the unit sheaf indexed by `I`. This file
defines its coordinate projections `SheafOfModules.freeProjection i : free I ⟶ unit R`, the
morphisms which are the identity on the `i`-th summand and zero on every other one, and records
that over a finite index type they sum, against the coordinate inclusions, to the identity.

## Main definitions

* `SheafOfModules.freeProjection`: the `i`-th coordinate projection of `free I`.

## Main results

* `SheafOfModules.ιFree_comp_freeProjection_self` and
  `SheafOfModules.ιFree_comp_freeProjection_of_ne`: the two defining equations, which determine
  `freeProjection i` because `free I` is a coproduct.
* `SheafOfModules.ιFree_comp_freeProjection`: the two of them as a single `if`, for a decidable
  index type.
* `SheafOfModules.sum_freeProjection_comp_ιFree` and
  `SheafOfModules.eq_sum_comp_freeProjection_comp_ιFree`: over a finite index type the
  coordinate projections followed by the coordinate inclusions sum to the identity, so that a
  morphism into `free I` is the sum of its coordinates.

## Implementation notes

The index type carries no decidability assumption, so the definition itself is made with the
classical instance; the two defining equations are stated without any `if`, and the `if` form is
stated separately for a decidable index type, so that a user of the latter is free to supply
whichever instance the surrounding development already has.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Projection

attribute [local instance] Classical.propDecidable

/-- The `i`-th coordinate projection of the free sheaf of modules on `I`: it is the identity on
the `i`-th summand and zero on every other one. -/
noncomputable def freeProjection {I : Type u} (i : I) : free (R := R) I ⟶ unit R :=
  Sigma.desc fun j ↦ if j = i then 𝟙 _ else 0

/-- The composite of the `j`-th coordinate inclusion with the `i`-th coordinate projection, with
the classical `if`. -/
private theorem ιFree_comp_freeProjection_classical {I : Type u} (i j : I) :
    ιFree (R := R) j ≫ freeProjection i = if j = i then 𝟙 (unit R) else 0 :=
  Sigma.ι_comp_desc _ _

/-- The `i`-th coordinate projection of a free sheaf of modules is the identity on the `i`-th
summand. -/
@[reassoc (attr := simp)]
lemma ιFree_comp_freeProjection_self {I : Type u} (i : I) :
    ιFree (R := R) i ≫ freeProjection i = 𝟙 (unit R) :=
  (ιFree_comp_freeProjection_classical i i).trans (ite_eq_left rfl)

/-- The `i`-th coordinate projection of a free sheaf of modules is zero on the `j`-th summand
for `j ≠ i`. -/
@[reassoc (attr := simp)]
lemma ιFree_comp_freeProjection_of_ne {I : Type u} {i j : I} (hij : j ≠ i) :
    ιFree (R := R) j ≫ freeProjection i = 0 :=
  (ιFree_comp_freeProjection_classical i j).trans (ite_eq_right hij)

end Projection

/-- On the `j`-th summand the `i`-th coordinate projection of a free sheaf of modules is the
identity if `j = i` and zero otherwise. -/
@[reassoc]
lemma ιFree_comp_freeProjection {I : Type u} [DecidableEq I] (i j : I) :
    ιFree (R := R) j ≫ freeProjection i = if j = i then 𝟙 (unit R) else 0 := by
  by_cases hij : j = i
  · rw [ite_eq_left hij, hij, ιFree_comp_freeProjection_self]
  · rw [ite_eq_right hij, ιFree_comp_freeProjection_of_ne hij]

/-- Over a finite index type the coordinate projections of a free sheaf of modules, followed by
the coordinate inclusions, sum to the identity. -/
lemma sum_freeProjection_comp_ιFree {I : Type u} [Fintype I] :
    ∑ i, freeProjection (R := R) i ≫ ιFree i = 𝟙 (free (R := R) I) := by
  have key : ∀ j : I, ιFree (R := R) j ≫ ∑ i, freeProjection (R := R) i ≫ ιFree i =
      ιFree (R := R) j := by
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · rw [← Category.assoc, ιFree_comp_freeProjection_self, Category.id_comp]
    · intro b _ hb
      rw [← Category.assoc, ιFree_comp_freeProjection_of_ne (Ne.symm hb), zero_comp]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  change ιFree (R := R) j ≫ (∑ i, freeProjection (R := R) i ≫ ιFree i) =
    ιFree (R := R) j ≫ 𝟙 (free (R := R) I)
  rw [Category.comp_id]
  exact key j

/-- A morphism into a free sheaf of modules on a finite index type is the sum of its
coordinates. -/
lemma eq_sum_comp_freeProjection_comp_ιFree {I : Type u} [Fintype I] {M : SheafOfModules.{u} R}
    (x : M ⟶ free (R := R) I) :
    x = ∑ i, (x ≫ freeProjection (R := R) i) ≫ ιFree i := by
  simp_rw [Category.assoc]
  rw [← Preadditive.comp_sum, sum_freeProjection_comp_ιFree, Category.comp_id]

end SheafOfModules
