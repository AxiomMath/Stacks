module

public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# The base change 2-square of a square of adjunctions

Consider a square of categories and functors

```
     Lf
  A ---→ B
Lg |     | Lg'
   v     v
  A' --→ B'
     Lf'
```

in which the two horizontal functors have right adjoints, `Lf ⊣ Rf` and `Lf' ⊣ Rf'`, and in which
the two composites around the square are identified with one functor `Lc : A ⥤ B'` by
isomorphisms `eg : Lg ⋙ Lf' ≅ Lc` and `ef : Lf ⋙ Lg' ≅ Lc`.  Then there is a canonical
*base change* morphism of functors `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`: the mate, under the two adjunctions,
of the comparison `Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` of the two composites.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.pullbackComparison` is the comparison of the two composites
  around the square, read as a 2-square.
* `Stacks.CategoryTheory.BaseChange.twoSquare` is the base change morphism of functors, as a
  2-square.
* `Stacks.CategoryTheory.BaseChange.map` is its component at an object, the base change map
  `Lg (Rf K) ⟶ Rf' (Lg' K)`.

## Main results

* `Stacks.CategoryTheory.BaseChange.homEquiv_symm_map` identifies the adjunct of the base change
  map under `Lf' ⊣ Rf'` with the comparison of the two composites followed by `Lg'` of the
  counit of `Lf ⊣ Rf`.  Since the adjunct is a bijection, this determines the map.
* `Stacks.CategoryTheory.BaseChange.map_eq` is the same equation read as a formula for the base
  change map itself.
* `Stacks.CategoryTheory.BaseChange.map_naturality`: naturality of the base change map in the
  object.

## Implementation notes

The base change morphism is defined through `CategoryTheory.mateEquiv`, the bijection between
2-squares across a pair of adjunctions, so it is a morphism of functors and its naturality is that
of the 2-square.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- The comparison `Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` of the two composites around the square, read as a
2-square.  Both are identified with `Lc`, and this is the resulting isomorphism. -/
def pullbackComparison : TwoSquare Lg Lf Lf' Lg' :=
  TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv)

/-- The canonical base change morphism of functors `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`: the mate, under the
two adjunctions, of the comparison of the two composites around the square. -/
def twoSquare : TwoSquare Rf Lg' Lg Rf' :=
  mateEquiv adjf adjf' (pullbackComparison eg ef)

/-- The canonical base change map `Lg (Rf K) ⟶ Rf' (Lg' K)` at an object `K`. -/
def map (K : B) : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  (twoSquare adjf adjf' eg ef).app K

/-- Under the adjunction `Lf' ⊣ Rf'`, the base change map is the comparison of the two composites
around the square followed by `Lg'` of the counit of `Lf ⊣ Rf`. -/
@[simp]
theorem homEquiv_symm_map (K : B) :
    (adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm (map adjf adjf' eg ef K) =
      eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
  rw [map, twoSquare, Adjunction.homEquiv_counit, mateEquiv_counit]
  simp only [pullbackComparison, NatTrans.comp_app, Category.assoc]

/-- The base change map is the transpose, under `Lf' ⊣ Rf'`, of the comparison of the two
composites around the square followed by `Lg'` of the counit of `Lf ⊣ Rf`. -/
theorem map_eq (K : B) :
    map adjf adjf' eg ef K =
      adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)
        (eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K)) := by
  rw [← homEquiv_symm_map, Equiv.apply_symm_apply]

/-- The base change map is natural in the object. -/
theorem map_naturality {K L : B} (u : K ⟶ L) :
    Lg.map (Rf.map u) ≫ map adjf adjf' eg ef L =
      map adjf adjf' eg ef K ≫ Rf'.map (Lg'.map u) :=
  (twoSquare adjf adjf' eg ef).naturality u

end Stacks.CategoryTheory.BaseChange

end
