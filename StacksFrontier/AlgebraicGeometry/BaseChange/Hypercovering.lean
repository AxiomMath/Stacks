module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Preimage

/-!
# Base change of a hypercovering of a scheme

Consider a cartesian diagram of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

and a hypercovering `K = (I, {U_i})` of `X` in the Zariski pretopology of the opens of `X`. Its
base change is the family of the opens `S' ×_S U_i = (g')⁻¹U_i` of `X'`, and it is a
hypercovering of `X'`. Base change leaves the index type of every simplicial degree unchanged,
so a hypercovering which is finite in each degree has a base change which is finite in each
degree; and if `S` and `S'` are affine and the `U_i` are affine opens, then so are the opens
`(g')⁻¹U_i`.

## Main definitions

* `AlgebraicGeometry.baseChangeFormalCoproduct`: the base change functor on semi-representable
  objects, sending a family of opens of `V ⊆ X` to the family of their preimages in `(g')⁻¹V`.

## Main results

* `AlgebraicGeometry.isHypercovering_baseChange`: the base change of a hypercovering of an open
  `V` of `X` along an arbitrary morphism of schemes `g' : X' ⟶ X` is a hypercovering of
  `(g')⁻¹V`.
* `AlgebraicGeometry.baseChangeFormalCoproduct_obj_I` and
  `AlgebraicGeometry.baseChangeFormalCoproduct_obj_obj_left`: base change preserves the index
  type of each simplicial degree, and its member at an index is the preimage of the original
  member.
* `AlgebraicGeometry.isAffineOpen_baseChange_obj_left`: along an affine morphism the base change
  of an affine member is affine.
* `AlgebraicGeometry.exists_isHypercovering_baseChange`: for a cartesian square with `S` and
  `S'` affine, a hypercovering of `X` which is finite in every degree and all of whose members
  are affine opens has a base change which is a hypercovering of `X'`, finite in every degree
  and with affine members.

## Implementation notes

The base change of the hypercovering is a purely topological construction: the open
`S' ×_S U_i` of `X' = X ×_S S'` is the preimage `(g')⁻¹U_i`, so the base change functor is the
preimage functor on opens and the hypercovering clause is
`Stacks.CategoryTheory.Hypercovering.IsHypercovering.opensMap`, which needs no cartesian
hypothesis. The square enters only through the affineness of the members: `g'` is the base
change of `g`, which is affine because `S` and `S'` are, and the preimage of an affine open
under an affine morphism is affine.

The hypotheses of `AlgebraicGeometry.exists_isHypercovering_baseChange` are exactly what
`Stacks.AlgebraicGeometry.UniversalPushforward.exists_finite_affine_hypercovering` produces for
a quasi-compact, quasi-separated scheme, namely Tag 01H7 for the basis of affine opens.

## References

* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
* [Stacks Project, Tag 01H7](https://stacks.math.columbia.edu/tag/01H7)
* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace
open Stacks.CategoryTheory.Hypercovering

namespace AlgebraicGeometry

section BaseChange

variable {X' X : Scheme.{u}} (g' : X' ⟶ X)

/-- The base change along `g' : X' ⟶ X` of the semi-representable objects over an open `V` of
`X`: a family of opens of `V` is sent to the family of their preimages in `(g')⁻¹V`. -/
abbrev baseChangeFormalCoproduct (V : X.Opens) :
    FormalCoproduct.{w} (Over V) ⥤ FormalCoproduct.{w} (Over (g' ⁻¹ᵁ V)) :=
  mapFormalCoproduct.{w} (Over.post (Opens.map g'.base) (X := V))

/-- **The base change of a hypercovering.** The family of preimages of the members of a
hypercovering of an open `V` of `X` is a hypercovering of `(g')⁻¹V`. For `V` the whole of `X`
and a cartesian square with bottom row `g : S' ⟶ S`, the members of the image are the base
changes `X' ×_X U_i = S' ×_S U_i`. -/
theorem isHypercovering_baseChange {V : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V)))
    (hK : IsHypercovering (Opens.pretopology X) K) :
    IsHypercovering (Opens.pretopology X') (K ⋙ baseChangeFormalCoproduct.{w} g' V) :=
  IsHypercovering.opensMap g'.base K hK

/-- Base change leaves the index type of each simplicial degree unchanged. -/
theorem baseChangeFormalCoproduct_obj_I {V : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V))) (n : SimplexCategoryᵒᵖ) :
    ((K ⋙ baseChangeFormalCoproduct.{w} g' V).obj n).I = (K.obj n).I :=
  rfl

/-- The member of the base change at an index is the preimage of the member at that index. -/
theorem baseChangeFormalCoproduct_obj_obj_left {V : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V))) (n : SimplexCategoryᵒᵖ)
    (i : (K.obj n).I) :
    (((K ⋙ baseChangeFormalCoproduct.{w} g' V).obj n).obj i).left =
      g' ⁻¹ᵁ ((K.obj n).obj i).left :=
  rfl

/-- Along an affine morphism the base change of an affine member of a hypercovering is an affine
open. -/
theorem isAffineOpen_baseChange_obj_left [IsAffineHom g'] {V : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V))) (n : SimplexCategoryᵒᵖ)
    (i : (K.obj n).I) (hi : IsAffineOpen ((K.obj n).obj i).left) :
    IsAffineOpen (((K ⋙ baseChangeFormalCoproduct.{w} g' V).obj n).obj i).left :=
  hi.preimage g'

end BaseChange

/-- **The base change of a degreewise finite hypercovering by affine opens.** Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes with `S` and `S'` affine. A hypercovering of `X` which is
finite in every simplicial degree and all of whose members are affine opens base changes to a
hypercovering of `X'` with the same index types and with the affine opens `S' ×_S U_i` as
members. -/
theorem exists_isHypercovering_baseChange {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))
    (hK : IsHypercovering (Opens.pretopology X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (haffine : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I),
      IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left) :
    ∃ K' : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X'.Opens))),
      IsHypercovering (Opens.pretopology X') K' ∧
        ∀ n : ℕ, Finite (K'.obj (op ⦋n⦌)).I ∧
          ∀ i : (K'.obj (op ⦋n⦌)).I,
            IsAffineOpen ((K'.obj (op ⦋n⦌)).obj i).left := by
  have : IsAffineHom g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip
      (inferInstanceAs (IsAffineHom g))
  exact ⟨K ⋙ baseChangeFormalCoproduct.{u} g' ⊤, isHypercovering_baseChange g' K hK,
    fun n ↦ ⟨hfin n, fun i ↦ isAffineOpen_baseChange_obj_left g' K _ i (haffine n i)⟩⟩

end AlgebraicGeometry

end
