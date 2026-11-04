module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restricting an adjunction to an equivalence of full subcategories

Let `F ⊣ G` be an adjunction between categories `C` and `D`, let `P` be a property of objects of
`C` and `Q` one of `D`, such that `F` carries `P` into `Q` and `G` carries `Q` into `P`. If the
unit is invertible at the objects of `P` and `G` reflects isomorphisms between objects of `Q`,
then `F` and `G` restrict to quasi-inverse equivalences between the full subcategories of `P`
and of `Q`: the counit at an object `Y` of `Q` is inverted by `G`, by the triangle identity.

## Main definitions

* `CategoryTheory.Adjunction.restrictObjectProperty`: the adjunction restricted to the full
  subcategories.
* `CategoryTheory.Adjunction.restrictEquivalence`: **the restricted equivalence**, when the unit
  is invertible on `P` and `G` reflects isomorphisms on `Q`.

## Main results

* `CategoryTheory.Adjunction.restrictEquivalence_functor_obj` and
  `CategoryTheory.Adjunction.restrictEquivalence_inverse_obj`: the functors of the equivalence
  are `F` and `G`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (P : ObjectProperty C) (Q : ObjectProperty D)
  (hF : ∀ X, P X → Q (F.obj X)) (hG : ∀ Y, Q Y → P (G.obj Y))

/-- **The adjunction `F ⊣ G` restricted to full subcategories** carried into each other. -/
noncomputable def restrictObjectProperty :
    Q.lift (P.ι ⋙ F) (fun X => hF X.obj X.property) ⊣
      P.lift (Q.ι ⋙ G) (fun Y => hG Y.obj Y.property) :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Q.liftCompιIso _ _).symm (P.liftCompιIso _ _).symm

/-- The unit of the restricted adjunction at `X` is, under the inclusion, the unit of `F ⊣ G` at
`X`. -/
theorem ι_map_restrictObjectProperty_unit_app (X : P.FullSubcategory) :
    P.ι.map ((adj.restrictObjectProperty P Q hF hG).unit.app X) = adj.unit.app X.obj := by
  rw [restrictObjectProperty, map_restrictFullyFaithful_unit_app]
  simp [ObjectProperty.liftCompιIso]

/-- The counit of the restricted adjunction at `Y` is, under the inclusion, the counit of `F ⊣ G`
at `Y`. -/
theorem ι_map_restrictObjectProperty_counit_app (Y : Q.FullSubcategory) :
    Q.ι.map ((adj.restrictObjectProperty P Q hF hG).counit.app Y) = adj.counit.app Y.obj := by
  rw [restrictObjectProperty, map_restrictFullyFaithful_counit_app]
  simp [ObjectProperty.liftCompιIso]

variable {P Q}

/-- If the unit of `F ⊣ G` is invertible at the objects of `P`, then the unit of the restricted
adjunction is invertible. -/
theorem isIso_restrictObjectProperty_unit_app
    (hu : ∀ X, P X → IsIso (adj.unit.app X)) (X : P.FullSubcategory) :
    IsIso ((adj.restrictObjectProperty P Q hF hG).unit.app X) := by
  rw [← isIso_iff_of_reflects_iso _ P.ι, ι_map_restrictObjectProperty_unit_app]
  exact hu X.obj X.property

/-- If the unit of `F ⊣ G` is invertible at the objects of `P` and `G` reflects isomorphisms
between objects of `Q`, then the counit of the restricted adjunction is invertible. -/
theorem isIso_restrictObjectProperty_counit_app
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g)
    (Y : Q.FullSubcategory) :
    IsIso ((adj.restrictObjectProperty P Q hF hG).counit.app Y) := by
  have := hu (G.obj Y.obj) (hG _ Y.property)
  have hc : IsIso (adj.counit.app Y.obj) := by
    refine hr _ (hF _ (hG _ Y.property)) Y.property ?_
    have heq : inv (adj.unit.app (G.obj Y.obj)) = G.map (adj.counit.app Y.obj) :=
      IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components Y.obj)
    rw [← heq]
    infer_instance
  rw [← isIso_iff_of_reflects_iso _ Q.ι, ι_map_restrictObjectProperty_counit_app]
  exact hc

/-- **An adjunction whose unit is invertible on `P` and whose right adjoint reflects isomorphisms
between objects of `Q` restricts to an equivalence between the full subcategories of `P` and
`Q`.** -/
noncomputable def restrictEquivalence
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g) :
    P.FullSubcategory ≌ Q.FullSubcategory :=
  have := adj.isIso_restrictObjectProperty_unit_app hF hG hu
  have := adj.isIso_restrictObjectProperty_counit_app hF hG hu hr
  (adj.restrictObjectProperty P Q hF hG).toEquivalence

/-- The functor of the restricted equivalence sends `X` to `F.obj X`. -/
@[simp] theorem restrictEquivalence_functor_obj
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g)
    (X : P.FullSubcategory) :
    ((adj.restrictEquivalence hF hG hu hr).functor.obj X).obj = F.obj X.obj := rfl

/-- The inverse of the restricted equivalence sends `Y` to `G.obj Y`. -/
@[simp] theorem restrictEquivalence_inverse_obj
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g)
    (Y : Q.FullSubcategory) :
    ((adj.restrictEquivalence hF hG hu hr).inverse.obj Y).obj = G.obj Y.obj := rfl

/-- The functor of the restricted equivalence, followed by the inclusion, is `F` on the
inclusion. -/
def restrictEquivalenceFunctorCompι
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g) :
    (adj.restrictEquivalence hF hG hu hr).functor ⋙ Q.ι ≅ P.ι ⋙ F :=
  Iso.refl _

/-- The inverse of the restricted equivalence, followed by the inclusion, is `G` on the
inclusion. -/
def restrictEquivalenceInverseCompι
    (hu : ∀ X, P X → IsIso (adj.unit.app X))
    (hr : ∀ ⦃Y Y' : D⦄ (g : Y ⟶ Y'), Q Y → Q Y' → IsIso (G.map g) → IsIso g) :
    (adj.restrictEquivalence hF hG hu hr).inverse ⋙ P.ι ≅ Q.ι ⋙ G :=
  Iso.refl _

end CategoryTheory.Adjunction
