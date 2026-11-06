module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Recognising a sheafification on a basis

A morphism from a presheaf to a sheaf which is an isomorphism on every member of a basis of the
topology exhibits the target as the sheafification of the source. This is the step which converts
the affine computation of the total quotient presheaf into a statement about the sheaf of total
quotient rings, whose sections over an arbitrary open set are otherwise inaccessible.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointProduct.isIso_sheafifyLift_of_isIso_basis`: the induced
  morphism from the sheafification is an isomorphism.
* `Stacks.AlgebraicGeometry.GenericPointProduct.isIso_sheafifyLift_app_of_isIso_basis`:
  consequently the component of that morphism at *every* open set is an isomorphism.

## Implementation notes

The inverse is built on the basis and extended by `TopCat.Sheaf.restrictHomEquivHom`, which is
available because a basis is cover dense. One of the two round trips is checked on the basis by
`TopCat.Sheaf.hom_ext`; the other is checked by the uniqueness half of the universal property of
sheafification, since checking it on the basis would compare two morphisms out of the
sheafification rather than into a sheaf.

The statement is for presheaves of commutative rings, which is the only case needed, and which
avoids carrying the sheafification typeclasses.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.GenericPointProduct

variable {Y : TopCat.{u}} {ι : Type*} {B : ι → Opens Y}
  {P : TopCat.Presheaf CommRingCat.{u} Y} {G : TopCat.Sheaf CommRingCat.{u} Y}

/-- The restriction of a morphism of presheaves to a family of open sets. -/
noncomputable abbrev restrictToBasis (B : ι → Opens Y) {F F' : TopCat.Presheaf CommRingCat.{u} Y}
    (ψ : F ⟶ F') : (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ F' :=
  Functor.whiskerLeft (inducedFunctor B).op ψ

/-- A morphism from a presheaf of commutative rings to a sheaf which is an isomorphism on every
member of a basis of the topology induces an isomorphism from the sheafification of the source. -/
theorem isIso_sheafifyLift_of_isIso_basis (hB : Opens.IsBasis (Set.range B))
    (ψ : P ⟶ G.presheaf) (hψ : ∀ i, IsIso (ψ.app (op (B i)))) :
    IsIso (sheafifyLift (Opens.grothendieckTopology Y) ψ G.property) := by
  let _ := hψ
  let _ : ∀ j, IsIso ((restrictToBasis B ψ).app j) := fun j ↦ hψ j.unop
  have : IsIso (restrictToBasis B ψ) := NatIso.isIso_of_isIso_app _
  set J := Opens.grothendieckTopology Y with hJ
  set SP := (presheafToSheaf J CommRingCat.{u}).obj P with hSP
  set Φ := sheafifyLift J ψ G.property with hΦ
  set Ψ := TopCat.Sheaf.restrictHomEquivHom G.presheaf SP hB
    (inv (restrictToBasis B ψ) ≫ restrictToBasis B (toSheafify J P)) with hΨ
  have happ : ∀ i : ι, Ψ.app (op (B i)) =
      inv (ψ.app (op (B i))) ≫ (toSheafify J P).app (op (B i)) := fun i ↦
    (TopCat.Sheaf.extend_hom_app G.presheaf SP hB _ i).trans <| by
      rw [NatTrans.comp_app, NatIso.isIso_inv_app]; rfl
  have key1 : ψ ≫ Ψ = toSheafify J P :=
    TopCat.Sheaf.hom_ext _ SP hB fun i ↦ by
      rw [NatTrans.comp_app, happ i, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have key2 : Ψ ≫ Φ = 𝟙 G.presheaf :=
    TopCat.Sheaf.hom_ext _ G hB fun i ↦ by
      rw [NatTrans.comp_app, happ i, Category.assoc, hΦ, ← NatTrans.comp_app,
        toSheafify_sheafifyLift, IsIso.inv_hom_id, NatTrans.id_app]
  have key3 : Φ ≫ Ψ = 𝟙 (sheafify J P) := by
    have e1 : Φ ≫ Ψ = sheafifyLift J (toSheafify J P) SP.property :=
      sheafifyLift_unique J _ SP.property _ (by
        rw [← Category.assoc, hΦ, toSheafify_sheafifyLift, key1])
    have e2 : 𝟙 (sheafify J P) = sheafifyLift J (toSheafify J P) SP.property :=
      sheafifyLift_unique J _ SP.property _ (Category.comp_id _)
    exact e1.trans e2.symm
  exact ⟨Ψ, key3, key2⟩

/-- A morphism from a presheaf of commutative rings to a sheaf which is an isomorphism on every
member of a basis of the topology induces, at every open set whatsoever, an isomorphism from the
sections of the sheafification. -/
theorem isIso_sheafifyLift_app_of_isIso_basis (hB : Opens.IsBasis (Set.range B))
    (ψ : P ⟶ G.presheaf) (hψ : ∀ i, IsIso (ψ.app (op (B i)))) (U : Opens Y) :
    IsIso ((sheafifyLift (Opens.grothendieckTopology Y) ψ G.property).app (op U)) :=
  let := isIso_sheafifyLift_of_isIso_basis hB ψ hψ
  inferInstance

end Stacks.AlgebraicGeometry.GenericPointProduct
