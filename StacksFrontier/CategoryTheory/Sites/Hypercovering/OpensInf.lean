module

public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map

/-!
# Restricting a hypercovering of a space to an open subset, inside the same site

Let `T` be a topological space and `W` an open subset of it.  Intersecting with `W` is a functor

`(· ⊓ W) : Opens T ⥤ Opens T`

which takes covering families to covering families and preserves fibre products, so by
[Stacks, Tag 0DAZ] the degreewise intersection with `W` of a hypercovering of an open `V` of `T` is
a hypercovering of `V ⊓ W`.

This is the variant of `Stacks.CategoryTheory.Hypercovering.IsHypercovering.opensMap` — which takes
preimages along a continuous map and therefore lands in the site of the *source* — that keeps both
the site and its sheaves fixed:  the members of the restricted hypercovering are the open subsets
`U_i ⊓ W` *of `T`*, so a sheaf on `T` can be evaluated on them directly and no restriction of the
sheaf to `W` is needed.  That is what makes it the right variant for computing the sections over an
open subset of the Čech complex of a hypercovering.

Intersecting with `W` does **not** preserve the terminal object — `⊤ ⊓ W` is `W` — and so does not
preserve finite limits.  This is no obstruction:  Tag 0DAZ asks only for the preservation of fibre
products, and the terminal object of the slice category `Opens T / V`, namely `𝟙 V`, goes to the
terminal object `𝟙 (V ⊓ W)` of `Opens T / (V ⊓ W)` for that reason alone.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.opensInf`:  the functor `(· ⊓ W)`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.preservesLimitsOfShape_opensInf`:  `(· ⊓ W)` preserves
  limits of every nonempty finite shape, in particular fibre products.
* `Stacks.CategoryTheory.Hypercovering.opensInf_mapsCoveringsToCoverings`:  the family of
  intersections with `W` of a covering family of `V` is a covering family of `V ⊓ W`.
* `Stacks.CategoryTheory.Hypercovering.IsHypercovering.opensInf`:  **Tag 0DAZ for `(· ⊓ W)`** — the
  degreewise intersection with `W` of a hypercovering of `V` is a hypercovering of `V ⊓ W`.
* `Stacks.CategoryTheory.Hypercovering.opensInf_obj_I` and
  `Stacks.CategoryTheory.Hypercovering.opensInf_obj_obj_left`:  in each simplicial degree the
  restricted hypercovering has the same index type as the original, and its member at an index is
  the intersection with `W` of the original member.

## Implementation notes

Preservation of limits of nonempty finite shape is proved from the explicit finite limit cone of a
complete lattice, `CategoryTheory.Limits.CompleteLattice.finiteLimitCone`, whose vertex is the
infimum of the values of the diagram.  `Mathlib`'s instance
`CategoryTheory.Limits.CompleteLattice.preservesLimit_finite_toFunctor` is not applicable:  it is
stated for an `InfTopHomClass`, because over the empty shape the infimum is `⊤`, and `(· ⊓ W)` is
not a `TopHom`.  Over a nonempty shape the only identity needed is `iInf_inf`, which holds for an
`InfHom`.

The index types and comparison morphisms of the formal coproducts are untouched by the degreewise
image construction, so the two identification lemmas hold by definition and degreewise finiteness
of the index types transfers verbatim.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace

namespace Stacks.CategoryTheory.Hypercovering

section OpensInf

variable {T : Type u} [TopologicalSpace T] (W : Opens T)

/-- **Intersecting with a fixed open subset**, as a functor `Opens T ⥤ Opens T`.  It is the functor
of the monotone map `A ↦ A ⊓ W` of the lattice of opens. -/
def opensInf : Opens T ⥤ Opens T :=
  OrderHom.toFunctor (OrderHom.mk (fun A : Opens T ↦ A ⊓ W) (fun _ _ h ↦ inf_le_inf_right W h))

/-- The functor `opensInf W` sends an open `A` to `A ⊓ W`. -/
@[simp]
theorem opensInf_obj (A : Opens T) : (opensInf W).obj A = A ⊓ W := rfl

/-- **Intersecting with `W` preserves limits of every nonempty finite shape.**  The limit of a
finite diagram of opens is the infimum of its values, and the infimum of a nonempty family
commutes with intersecting by a fixed open. -/
instance preservesLimitsOfShape_opensInf {J : Type} [SmallCategory J] [FinCategory J]
    [Nonempty J] : PreservesLimitsOfShape J (opensInf W) where
  preservesLimit {K} :=
    preservesLimit_of_preserves_limit_cone (CompleteLattice.finiteLimitCone K).isLimit
      ((CompleteLattice.finiteLimitCone (K ⋙ opensInf W)).isLimit.ofIsoLimit
        (Cone.ext (eqToIso (by
          change Finset.univ.inf (fun j : J ↦ K.obj j ⊓ W) =
            Finset.univ.inf (fun j : J ↦ K.obj j) ⊓ W
          rw [Finset.inf_univ_eq_iInf, Finset.inf_univ_eq_iInf]
          exact (iInf_inf (f := fun j : J ↦ K.obj j) (a := W)).symm))
          (by subsingleton)))

/-- **The covering clause of Tag 00WV for intersection with `W`.**  A point of `V ⊓ W` lies in `V`,
hence in some member `A i` of a covering family of `V`, and it lies in `W`, hence it lies in
`A i ⊓ W`. -/
theorem opensInf_mapsCoveringsToCoverings :
    MapsCoveringsToCoverings.{w} (opensInf W) (Opens.pretopology T) (Opens.pretopology T) := by
  intro V ι A g hg x hx
  obtain ⟨U, k, hk, hxU⟩ := hg x hx.1
  obtain ⟨i⟩ := hk
  exact ⟨(opensInf W).obj (A i), (opensInf W).map (g i), Presieve.ofArrows.mk i, hxU, hx.2⟩

/-- **Tag 0DAZ for intersection with a fixed open subset.**  The degreewise intersection with `W`
of a hypercovering of an open `V` of `T` is a hypercovering of `V ⊓ W`. -/
theorem IsHypercovering.opensInf {V : Opens T}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V)))
    (hK : IsHypercovering (Opens.pretopology T) K) :
    IsHypercovering (Opens.pretopology T)
      (K ⋙ mapFormalCoproduct.{w}
        (Over.post (Hypercovering.opensInf W) (X := V))) :=
  IsHypercovering.map (Opens.pretopology T) (Opens.pretopology T) (Hypercovering.opensInf W)
    (opensInf_mapsCoveringsToCoverings.{w} W) K hK

/-- The restricted simplicial family of opens has, in each degree, the index type of the original
family. -/
theorem opensInf_obj_I {V : Opens T} (K : SimplicialObject (FormalCoproduct.{w} (Over V)))
    (n : SimplexCategoryᵒᵖ) :
    ((K ⋙ mapFormalCoproduct.{w} (Over.post (opensInf W) (X := V))).obj n).I = (K.obj n).I :=
  rfl

/-- The member of the restricted family at an index is the intersection with `W` of the member of
the original family at that index. -/
theorem opensInf_obj_obj_left {V : Opens T}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V))) (n : SimplexCategoryᵒᵖ)
    (i : (K.obj n).I) :
    (((K ⋙ mapFormalCoproduct.{w} (Over.post (opensInf W) (X := V))).obj n).obj i).left =
      ((K.obj n).obj i).left ⊓ W :=
  rfl

end OpensInf

end Stacks.CategoryTheory.Hypercovering

end
