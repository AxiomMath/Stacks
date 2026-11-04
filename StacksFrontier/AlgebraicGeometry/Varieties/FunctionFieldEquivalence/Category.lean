module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# The category of varieties and the category of finitely generated field extensions

Let `k` be a field. A variety over `k` is a scheme together with a structure morphism to
`Spec k` which makes it integral, separated and of finite type over `k`. Varieties over `k` form a
category whose morphisms are the dominant rational maps over `Spec k`. On the other side, the
finitely generated field extensions of `k` form a full subcategory of the category of commutative
`k`-algebras, cut out by being a field and being essentially of finite type — the latter is
finite generation as a field extension rather than as an algebra.

## Main definitions

* `AlgebraicGeometry.Variety`: A variety over `k`, remembering its structure morphism.
* `AlgebraicGeometry.Variety.Hom`: A dominant rational map of varieties over `k`.
* `AlgebraicGeometry.FinitelyGeneratedFieldExtension`: The category of finitely generated
  field extensions of `k`.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A variety over `k`, including its structure morphism to `Spec k`. -/
structure Variety (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The structure morphism to the spectrum of the base field. -/
  structureMap : toScheme ⟶ Spec (.of k)
  /-- The variety hypotheses on the structure morphism. -/
  [isVariety : IsVariety k structureMap]

attribute [instance] Variety.isVariety

/-- A variety over `k` is a scheme over `Spec k` via its structure morphism. -/
instance {k : Type u} [Field k] (X : Variety k) : X.toScheme.Over (Spec (.of k)) where
  hom := X.structureMap

/-- A dominant rational map of varieties over `k`. -/
structure Variety.Hom {k : Type u} [Field k] (X Y : Variety k) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  /-- The rational map is dominant. -/
  [isDominant : toRationalMap.IsDominant]
  /-- The rational map is defined over the base field. -/
  [isOver : toRationalMap.IsOver (Spec (.of k))]

attribute [instance] Variety.Hom.isDominant Variety.Hom.isOver

/-- Two morphisms of varieties are equal if their underlying rational maps are equal. -/
@[ext]
lemma Variety.Hom.ext {k : Type u} [Field k] {X Y : Variety k} (f g : X.Hom Y)
    (h : f.toRationalMap = g.toRationalMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Varieties over `k` form a category whose morphisms are the dominant rational maps over
`Spec k`, with composition of rational maps. -/
noncomputable instance {k : Type u} [Field k] : Category (Variety k) where
  Hom := Variety.Hom
  id X := ⟨Scheme.RationalMap.id X.toScheme⟩
  comp f g := ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp f := Variety.Hom.ext _ _ (Scheme.RationalMap.id_comp f.toRationalMap)
  comp_id f := Variety.Hom.ext _ _ (Scheme.RationalMap.comp_id f.toRationalMap)
  assoc f g h := Variety.Hom.ext _ _
    (Scheme.RationalMap.comp_assoc f.toRationalMap g.toRationalMap h.toRationalMap)

/-- The category of finitely generated field extensions of `k` and `k`-algebra maps. -/
abbrev FinitelyGeneratedFieldExtension (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory
    (fun K : CommAlgCat.{u, u} k ↦ IsField K ∧ Algebra.EssFiniteType k K)

end AlgebraicGeometry

end
