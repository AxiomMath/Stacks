module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalk.ElementaryFiber
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# The stalk of a sheaf on the small étale site at an ordinary point

Let `x` be a point of a scheme `X`. The *elementary étale stalk* of a presheaf `F` on the small
étale site of `X` at `x` is the colimit of `F` over the cofiltered category of elementary étale
neighbourhoods of `(X, x)`:
`F_x^h = colim_{(U, u)} F(U)`, the colimit running over the étale neighbourhoods `(U, u)` of
`(X, x)` with `κ(x) = κ(u)`.

This is the analogue, at an ordinary point of `X`, of the stalk at a geometric point, which is
the colimit over *all* étale neighbourhoods of that geometric point. For the structure sheaf the
two give the henselization and the strict henselization of the local ring at `x` respectively; the
former is the content of Tag 05KS, which is proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization`.

That the colimit exists is not formal: the elementary étale neighbourhoods of a point form a
category whose objects live one universe up. It follows from the cofinal family of affine
refinements provided by
`Stacks.EtaleCohomology.initiallySmall_elementaryEtaleNeighborhood`, so the colimit exists in
every category with `u`-small colimits, where `u` is the universe of the schemes.

## Main definitions

* `Stacks.EtaleCohomology.elementaryEtaleStalkDiagram` — the diagram whose colimit is the stalk.
* `Stacks.EtaleCohomology.elementaryEtaleStalk` — the stalk of a presheaf on the small étale site
  at an ordinary point.
* `Stacks.EtaleCohomology.elementaryEtaleStalkFunctor` — the same, as a functor in the presheaf.
* `Stacks.EtaleCohomology.elementaryEtaleGerm` — the germ at `x` of a section over an elementary
  étale neighbourhood.
* `Stacks.EtaleCohomology.sheafElementaryEtaleStalkFunctor` — the stalk functor on sheaves.

## Main results

* `Stacks.EtaleCohomology.elementaryEtaleGerm_map` — the germ map is compatible with restriction
  along a morphism of elementary étale neighbourhoods.
* `Stacks.EtaleCohomology.elementaryEtaleStalk_hom_ext` — a morphism out of the stalk is
  determined by its composites with the germ maps.
* `Stacks.EtaleCohomology.elementaryEtaleGerm_eq_iff` — for a `Type u`-valued presheaf, two
  sections have the same germ exactly when they agree on a common refinement.
* `Stacks.EtaleCohomology.exists_elementaryEtaleGerm_eq` — for a `Type u`-valued presheaf, every
  element of the stalk is the germ of a section over some elementary étale neighbourhood.

## Implementation notes

The indexing category is `AlgebraicGeometry.ElementaryEtaleNeighborhood X x` itself rather than
the category of elements of the fibre functor
`Stacks.EtaleCohomology.elementaryEtaleFiber`, so that the definition reads as the source does.
The fibre functor is used only to produce the smallness and cofilteredness of that category.

The description of the stalk of a `Type u`-valued presheaf by germs — joint surjectivity and the
criterion for two germs to agree — is Mathlib's description of a filtered colimit of types,
applied to the indexing category of elementary étale neighbourhoods, whose opposite is filtered by
Tag 057A.

## References

* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 05KS](https://stacks.math.columbia.edu/tag/05KS)
* [Stacks Project, Tag 057B](https://stacks.math.columbia.edu/tag/057B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v w u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} {A : Type v} [Category.{w} A]

/-- The diagram of sections of a presheaf on the small étale site over the elementary étale
neighbourhoods of a point. -/
public def elementaryEtaleStalkDiagram (x : X) (F : X.Etaleᵒᵖ ⥤ A) :
    (ElementaryEtaleNeighborhood X x)ᵒᵖ ⥤ A :=
  (elementaryEtaleNeighborhoodToSmallEtale X x).op ⋙ F

/-- The value of the stalk diagram at an elementary étale neighbourhood `N` is the object of
sections of `F` over the étale `X`-scheme underlying `N`. -/
@[simp]
public theorem elementaryEtaleStalkDiagram_obj (x : X) (F : X.Etaleᵒᵖ ⥤ A)
    (N : ElementaryEtaleNeighborhood X x) :
    (elementaryEtaleStalkDiagram x F).obj (op N) =
      F.obj (op ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N)) := rfl

/-- **The stalk of a presheaf on the small étale site at an ordinary point**, as the colimit of
its sections over the elementary étale neighbourhoods of that point. -/
public def elementaryEtaleStalk (x : X) (F : X.Etaleᵒᵖ ⥤ A)
    [HasColimit (elementaryEtaleStalkDiagram x F)] : A :=
  colimit (elementaryEtaleStalkDiagram x F)

/-- The germ at `x` of a section of a presheaf over an elementary étale neighbourhood. -/
public def elementaryEtaleGerm (x : X) (F : X.Etaleᵒᵖ ⥤ A)
    [HasColimit (elementaryEtaleStalkDiagram x F)] (N : ElementaryEtaleNeighborhood X x) :
    F.obj (op ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N)) ⟶
      elementaryEtaleStalk x F :=
  colimit.ι (elementaryEtaleStalkDiagram x F) (op N)

/-- Restricting a section along a morphism of elementary étale neighbourhoods does not change its
germ. -/
@[reassoc]
public theorem elementaryEtaleGerm_map (x : X) (F : X.Etaleᵒᵖ ⥤ A)
    [HasColimit (elementaryEtaleStalkDiagram x F)]
    {N N' : ElementaryEtaleNeighborhood X x} (f : N ⟶ N') :
    F.map ((elementaryEtaleNeighborhoodToSmallEtale X x).map f).op ≫
        elementaryEtaleGerm x F N = elementaryEtaleGerm x F N' :=
  colimit.w (elementaryEtaleStalkDiagram x F) f.op

/-- A morphism out of the stalk is determined by its composites with the germ maps. -/
public theorem elementaryEtaleStalk_hom_ext (x : X) (F : X.Etaleᵒᵖ ⥤ A)
    [HasColimit (elementaryEtaleStalkDiagram x F)] {T : A}
    {g h : elementaryEtaleStalk x F ⟶ T}
    (w : ∀ N : ElementaryEtaleNeighborhood X x,
      elementaryEtaleGerm x F N ≫ g = elementaryEtaleGerm x F N ≫ h) : g = h :=
  colimit.hom_ext (fun N => w N.unop)

section Functor

variable (X) in
/-- The stalk at an ordinary point, as a functor on presheaves on the small étale site. -/
public def elementaryEtaleStalkFunctor (x : X) (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (ElementaryEtaleNeighborhood X x)ᵒᵖ A] :
    (X.Etaleᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft (ElementaryEtaleNeighborhood X x)ᵒᵖ X.Etaleᵒᵖ A).obj
    (elementaryEtaleNeighborhoodToSmallEtale X x).op ⋙ colim

/-- The stalk functor sends a presheaf `F` to its stalk `elementaryEtaleStalk x F`. -/
@[simp]
public theorem elementaryEtaleStalkFunctor_obj (x : X)
    [HasColimitsOfShape (ElementaryEtaleNeighborhood X x)ᵒᵖ A] (F : X.Etaleᵒᵖ ⥤ A) :
    (elementaryEtaleStalkFunctor X x A).obj F = elementaryEtaleStalk x F := rfl

variable (X) in
/-- The stalk at an ordinary point, as a functor on sheaves on the small étale site. -/
public def sheafElementaryEtaleStalkFunctor (x : X) (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (ElementaryEtaleNeighborhood X x)ᵒᵖ A] :
    Sheaf (Scheme.smallEtaleTopology X) A ⥤ A :=
  sheafToPresheaf (Scheme.smallEtaleTopology X) A ⋙ elementaryEtaleStalkFunctor X x A

/-- The stalk functor on sheaves sends a sheaf `F` to the stalk of its underlying presheaf. -/
@[simp]
public theorem sheafElementaryEtaleStalkFunctor_obj (x : X)
    [HasColimitsOfShape (ElementaryEtaleNeighborhood X x)ᵒᵖ A]
    (F : Sheaf (Scheme.smallEtaleTopology X) A) :
    (sheafElementaryEtaleStalkFunctor X x A).obj F = elementaryEtaleStalk x F.obj := rfl

end Functor

/-- **Every element of the stalk is a germ.** For a `Type u`-valued presheaf on the small étale
site, every element of the stalk at `x` is the germ of a section over some elementary étale
neighbourhood of `(X, x)`. -/
public theorem exists_elementaryEtaleGerm_eq (x : X) (F : X.Etaleᵒᵖ ⥤ Type u)
    (t : elementaryEtaleStalk x F) :
    ∃ (N : ElementaryEtaleNeighborhood X x)
      (s : F.obj (op ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N))),
      elementaryEtaleGerm x F N s = t := by
  obtain ⟨N, s, hs⟩ := Types.jointly_surjective' (F := elementaryEtaleStalkDiagram x F) t
  exact ⟨N.unop, s, hs⟩

/-- **Two sections have the same germ exactly when they agree on a common refinement.** For a
`Type u`-valued presheaf on the small étale site, two sections over elementary étale
neighbourhoods of `x` have the same germ at `x` if and only if they are pulled back to the same
section over some elementary étale neighbourhood mapping to both. -/
public theorem elementaryEtaleGerm_eq_iff (x : X) (F : X.Etaleᵒᵖ ⥤ Type u)
    {N N' : ElementaryEtaleNeighborhood X x}
    (s : F.obj (op ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N)))
    (s' : F.obj (op ((elementaryEtaleNeighborhoodToSmallEtale X x).obj N'))) :
    elementaryEtaleGerm x F N s = elementaryEtaleGerm x F N' s' ↔
      ∃ (M : ElementaryEtaleNeighborhood X x) (f : M ⟶ N) (g : M ⟶ N'),
        F.map ((elementaryEtaleNeighborhoodToSmallEtale X x).map f).op s =
          F.map ((elementaryEtaleNeighborhoodToSmallEtale X x).map g).op s' :=
  (Types.FilteredColimit.colimit_eq_iff (F := elementaryEtaleStalkDiagram x F)).trans
    ⟨fun ⟨k, f, g, h⟩ => ⟨k.unop, f.unop, g.unop, h⟩,
      fun ⟨M, f, g, h⟩ => ⟨op M, f.op, g.op, h⟩⟩

end Stacks.EtaleCohomology

end
