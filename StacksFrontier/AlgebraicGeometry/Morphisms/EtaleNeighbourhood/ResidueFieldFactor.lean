module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Both factors of a composite which is trivial on residue fields are trivial on residue fields

Residue field maps of morphisms of schemes are homomorphisms of fields, hence injective. So if a
composite `f ≫ g` induces an isomorphism of residue fields at a point, then so do `f` at that
point and `g` at its image.

This is the mechanism behind the residue field bookkeeping in the proof of Stacks Tag 0GDX: there
one knows `κ(x) = κ(x_\sigma) = κ(u)` and has a chain of field extensions
`κ(x_i) \subset κ(u_i) \subset κ(u)` whose composite is that isomorphism, and concludes
`κ(u_i) = κ(x_i)`.

## Main results

* `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_residueFieldMap_comp`: the second factor is
  trivial on residue fields at the image point.
* `AlgebraicGeometry.isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp`: the first factor
  is trivial on residue fields.
* `AlgebraicGeometry.isIso_residueFieldMap_comp_isOpenImmersion` and
  `AlgebraicGeometry.isIso_residueFieldMap_isOpenImmersion_comp`: composing or precomposing with an
  open immersion preserves triviality of the residue field extension.

## Implementation notes

`AlgebraicGeometry.Scheme.residueFieldMap_comp` writes the residue field map of a composite as
`g.residueFieldMap (f x) ≫ f.residueFieldMap x`, so the two statements are the two halves of the
elementary fact that in a composite of injections which is bijective both factors are bijective.
Isomorphy in `CommRingCat` is bijectivity of the underlying map.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If `f ≫ g` induces an isomorphism of residue fields at `a`, the underlying map of the composite
`κ(g (f a)) ⟶ κ(f a) ⟶ κ(a)` is bijective. -/
private theorem bijective_residueFieldMap_comp_of_isIso
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A)
    (h : IsIso ((f ≫ g).residueFieldMap a)) :
    Function.Bijective ((f.residueFieldMap a).hom ∘ (g.residueFieldMap (f a)).hom) := by
  rw [Scheme.residueFieldMap_comp] at h
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- If `f ≫ g` induces an isomorphism of residue fields at `a`, then `g` induces one at
`f a`. -/
public theorem isIso_residueFieldMap_of_isIso_residueFieldMap_comp
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A)
    (h : IsIso ((f ≫ g).residueFieldMap a)) :
    IsIso (g.residueFieldMap (f a)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(g.residueFieldMap (f a)).hom.injective,
      (bijective_residueFieldMap_comp_of_isIso f g a h).surjective.of_comp_left
        (f.residueFieldMap a).hom.injective⟩

/-- If `f ≫ g` induces an isomorphism of residue fields at `a`, then so does `f`. -/
public theorem isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A)
    (h : IsIso ((f ≫ g).residueFieldMap a)) :
    IsIso (f.residueFieldMap a) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap a).hom.injective,
      (bijective_residueFieldMap_comp_of_isIso f g a h).surjective.of_comp⟩

/-- Composing with an open immersion preserves triviality of the residue field extension at a
point. This is what lets a conclusion proved after shrinking the target to an open subscheme be
read back on the original target. -/
public theorem isIso_residueFieldMap_comp_isOpenImmersion
    {W X' X : Scheme.{u}} (F : W ⟶ X') (j : X' ⟶ X) [IsOpenImmersion j] (w : W)
    (h : IsIso (F.residueFieldMap w)) :
    IsIso ((F ≫ j).residueFieldMap w) := by
  have hj : IsIso (j.residueFieldMap (F w)) := inferInstance
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hj h

/-- Precomposing with an open immersion preserves triviality of the residue field extension at
the image point. This is what lets a statement about a scheme be restricted to an open
subscheme. -/
public theorem isIso_residueFieldMap_isOpenImmersion_comp
    {V X Y : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y) (v : V)
    (h : IsIso (f.residueFieldMap (j v))) :
    IsIso ((j ≫ f).residueFieldMap v) := by
  have hj : IsIso (j.residueFieldMap v) := inferInstance
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' h hj

end AlgebraicGeometry

end
