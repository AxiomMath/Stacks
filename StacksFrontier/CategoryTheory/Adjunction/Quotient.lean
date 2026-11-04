module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Adjunctions between quotient categories

Let `r` and `s` be relations on the morphisms of categories `C` and `D`, and let `L : C ⥤ D` be
left adjoint to `R : D ⥤ C`. If both functors descend to the quotient categories — that is, if
`L' : Quotient r ⥤ Quotient s` and `R' : Quotient s ⥤ Quotient r` are given together with
natural isomorphisms filling the two squares relating them to `L` and `R` — then `L'` is left
adjoint to `R'`.

The descent is formal: the unit and the counit of the descended adjunction are the images of the
unit and the counit of the given one, which is legitimate because a natural transformation
between functors out of a quotient category may be defined on the images of the objects of `C`
alone (`CategoryTheory.Quotient.natTransLift`), and because the triangle identities are then
images of the triangle identities downstairs.

## Main definitions

* `CategoryTheory.Quotient.adjunctionLift`: the adjunction between the canonical lifts
  `CategoryTheory.Quotient.lift` of `L ⋙ Quotient.functor s` and of `R ⋙ Quotient.functor r`.
* `CategoryTheory.Quotient.adjunctionOfSquares`: the adjunction between arbitrary descents,
  obtained from the previous one by transporting along the comparison isomorphisms.

## Implementation notes

The canonical lifts are used as an intermediary because `CategoryTheory.Quotient.lift_spec`
identifies `Quotient.functor r ⋙ Quotient.lift r F H` with `F` *on the nose*, so the unit and
counit of `adjunctionLift` can be written without any intervening isomorphism and the triangle
identities reduce to the ones downstairs by `Functor.map_comp`. The general statement is then a
transport along natural isomorphisms, for which `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.ofNatIsoRight` are available.

Note that no compatibility between the two comparison isomorphisms is required: being adjoint is
invariant under natural isomorphism of each of the two functors separately.
-/

@[expose] public section

namespace CategoryTheory.Quotient

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (r : HomRel C) (s : HomRel D) {L : C ⥤ D} {R : D ⥤ C}

/-- An adjunction descends to the canonical lifts of its two functors to the quotient
categories. The unit and the counit are the images of the unit and the counit downstairs. -/
def adjunctionLift (adj : L ⊣ R)
    (hL : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ →
      (L ⋙ functor s).map f₁ = (L ⋙ functor s).map f₂)
    (hR : ∀ (x y : D) (f₁ f₂ : x ⟶ y), s f₁ f₂ →
      (R ⋙ functor r).map f₁ = (R ⋙ functor r).map f₂) :
    lift r (L ⋙ functor s) hL ⊣ lift s (R ⋙ functor r) hR where
  unit := natTransLift r
    { app := fun X => (functor r).map (adj.unit.app X)
      naturality := fun X Y f => by
        change (functor r).map f ≫ (functor r).map (adj.unit.app Y) =
          (functor r).map (adj.unit.app X) ≫ (functor r).map (R.map (L.map f))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (functor r).map (adj.unit.naturality f) }
  counit := natTransLift s
    { app := fun Y => (functor s).map (adj.counit.app Y)
      naturality := fun X Y f => by
        change (functor s).map (L.map (R.map f)) ≫ (functor s).map (adj.counit.app Y) =
          (functor s).map (adj.counit.app X) ≫ (functor s).map f
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (functor s).map (adj.counit.naturality f) }
  left_triangle_components := by
    rintro ⟨X⟩
    change (functor s).map (L.map (adj.unit.app X)) ≫
      (functor s).map (adj.counit.app (L.obj X)) = _
    rw [← Functor.map_comp, adj.left_triangle_components X]
    exact (functor s).map_id _
  right_triangle_components := by
    rintro ⟨Y⟩
    change (functor r).map (adj.unit.app (R.obj Y)) ≫
      (functor r).map (R.map (adj.counit.app Y)) = _
    rw [← Functor.map_comp, adj.right_triangle_components Y]
    exact (functor r).map_id _

/-- **An adjunction descends to the quotient categories.** If `L ⊣ R` and both functors are
compatible, up to natural isomorphism, with functors `L'` and `R'` between the quotient
categories, then `L' ⊣ R'`.

No compatibility between the two comparison isomorphisms is needed: being adjoint is invariant
under natural isomorphism of each of the two functors separately. -/
def adjunctionOfSquares {L' : Quotient r ⥤ Quotient s} {R' : Quotient s ⥤ Quotient r}
    (adj : L ⊣ R) (α : L ⋙ functor s ≅ functor r ⋙ L')
    (β : R ⋙ functor r ≅ functor s ⋙ R') : L' ⊣ R' := by
  have hL : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ →
      (L ⋙ functor s).map f₁ = (L ⋙ functor s).map f₂ := by
    intro x y f₁ f₂ h
    rw [← NatIso.naturality_2 α f₁, ← NatIso.naturality_2 α f₂, Functor.comp_map,
      Functor.comp_map, Quotient.sound r h]
  have hR : ∀ (x y : D) (f₁ f₂ : x ⟶ y), s f₁ f₂ →
      (R ⋙ functor r).map f₁ = (R ⋙ functor r).map f₂ := by
    intro x y f₁ f₂ h
    rw [← NatIso.naturality_2 β f₁, ← NatIso.naturality_2 β f₂, Functor.comp_map,
      Functor.comp_map, Quotient.sound s h]
  exact ((adjunctionLift r s adj hL hR).ofNatIsoLeft
      (natIsoLift r (eqToIso (lift_spec r (L ⋙ functor s) hL) ≪≫ α))).ofNatIsoRight
    (natIsoLift s (eqToIso (lift_spec s (R ⋙ functor r) hR) ≪≫ β))

end CategoryTheory.Quotient

end
