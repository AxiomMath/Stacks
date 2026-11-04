module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a family of objects which covers the final object

Let `(C, J)` be a site. The predicate `CategoryTheory.GrothendieckTopology.CoversTop` says of a
family of objects `Y : I → C` that `Sieve.ofObjects Y X` is a covering sieve for every object
`X`, and membership of an arrow `T ⟶ X` in `Sieve.ofObjects Y X` asks only for *some* `i` and
*some* morphism `T ⟶ Y i`. Covering the final object is therefore monotone in the family: a
family which every member of a covering family maps into again covers the final object.

Two statements are recorded.

* The monotonicity itself, which is immediate from
  `CategoryTheory.GrothendieckTopology.superset_covering`.
* The form in which it is consumed. Let `u : C ⥤ D` be a continuous functor whose image
  `u.obj` covers the final object of `(D, K)` — the conclusion of Stacks 08H2 — and let `p` be
  a property of the objects of `C` which holds locally on `C`, in the sense that every object
  of `C` admits a covering family all of whose members satisfy `p`. Then the subfamily of
  `u.obj` indexed by the objects satisfying `p` still covers the final object of `(D, K)`.
  Here monotonicity is not enough on its own: an object `U` of `C` need not itself satisfy `p`,
  and the arrows of its covering family point *into* `U`, so the covering of `u.obj U` must be
  refined, which is `CategoryTheory.GrothendieckTopology.transitive` together with cover
  preservation of a continuous functor.

## Main results

* `CategoryTheory.GrothendieckTopology.CoversTop.of_exists_hom`: covering the final object is
  monotone under refinement of the indexing family.
* `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype`: for a continuous functor whose
  image covers the final object, the image of the objects satisfying a locally true property
  still covers the final object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.GrothendieckTopology

/-- **Covering the final object is monotone.** If the family `Y : I → C` covers the final
object and every `Y i` admits a morphism to some member of a second family `Y' : I' → C`, then
`Y'` covers the final object too.

Membership of an arrow `T ⟶ X` in `Sieve.ofObjects Y X` is the existence of an index `i` and of
a morphism `T ⟶ Y i`, so composing with the given morphisms exhibits
`Sieve.ofObjects Y X ≤ Sieve.ofObjects Y' X` and the conclusion is
`GrothendieckTopology.superset_covering`. -/
@[sga "3 IV 4.2.1" "special case", sga "3 IV 4.2.3" "special case"]
theorem CoversTop.of_exists_hom {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {I I' : Type*} {Y : I → C} {Y' : I' → C} (hY : J.CoversTop Y)
    (h : ∀ i, ∃ i', Nonempty (Y i ⟶ Y' i')) : J.CoversTop Y' := by
  intro X
  refine J.superset_covering ?_ (hY X)
  rintro T g ⟨i, ⟨b⟩⟩
  obtain ⟨i', ⟨c⟩⟩ := h i
  exact ⟨i', ⟨b ≫ c⟩⟩

/-- **The image of the objects satisfying a locally true property still covers the final
object.** Let `u : C ⥤ D` be a continuous functor of sites whose image covers the final object
of `(D, K)`, and let `p` be a property of the objects of `C` such that every object of `C`
admits a covering family all of whose members satisfy `p`. Then the family
`fun V : {V // p V} => u.obj V.val` covers the final object of `(D, K)`.

Given an object `U` of `D`, the hypothesis provides a covering of `U` by objects `V` each
carrying a morphism `k : V ⟶ u.obj W` for some object `W` of `C`. Over each such `V` the
covering family of `W` supplied by `p` is pushed forward to a covering of `u.obj W` — a
continuous functor is cover preserving — and pulled back along `k` to a covering of `V` whose
arrows all factor through `u.obj` of an object satisfying `p`. Transitivity of the topology
assembles the two layers. -/
theorem coversTop_obj_subtype {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] (hTop : K.CoversTop u.obj) (p : C → Prop)
    (hp : ∀ U : C, ∃ S : Presieve U, Sieve.generate S ∈ J U ∧
      ∀ ⦃V : C⦄ (g : V ⟶ U), S g → p V) :
    K.CoversTop (fun V : {V : C // p V} => u.obj V.val) := by
  intro U
  apply K.transitive (hTop U)
  rintro V g ⟨W, ⟨k⟩⟩
  obtain ⟨S, hS, hpS⟩ := hp W
  have hc := CoverPreserving.of_isContinuous u J K
  apply K.superset_covering _ (K.pullback_stable k (hc.cover_preserve hS))
  intro Z q hq
  obtain ⟨A, a, b, ha, hb⟩ := hq
  obtain ⟨A', l, a', ha', heq⟩ := ha
  exact ⟨⟨A', hpS a' ha'⟩, ⟨b ≫ u.map l⟩⟩

end CategoryTheory.GrothendieckTopology

end
