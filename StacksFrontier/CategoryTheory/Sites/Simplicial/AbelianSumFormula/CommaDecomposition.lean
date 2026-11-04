module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# The comma category of a component inclusion, in case (A)

Let `Cs` be a simplicial site, that is, case (A) of the simplicial-site situation of
Stacks 09WE, let `(m, W)` be an object of its total category and let `n` be a simplicial degree.
This file decomposes the comma category of the inclusion of the degree-`n` component over
`(m, W)`.

An object of that comma category is a pair of an object `c` of the component `C n` and a
morphism `(m, W) ⟶ (n, c)` of the total category, which is a simplex map `ψ : n ⟶ m` together
with a morphism `W ⟶ u_ψ c` in `C m`, where `u_ψ` is the transition functor. The inclusion
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι` takes a morphism to one whose base component is
the identity, so a morphism of the comma category cannot change `ψ`: the comma category is the
disjoint union, over the *finite* set of simplex maps `ψ : n ⟶ m`, of copies of
`CategoryTheory.StructuredArrow W u_ψ`.

## Main results

* `Stacks.Sites.AbelianSumFormula.componentFunctor_inl_eq`: in case (A) the component inclusion
  is `CategoryTheory.Pseudofunctor.CoGrothendieck.ι`.
* `Stacks.Sites.AbelianSumFormula.summandInclusion`: the inclusion of the `ψ`-summand, which is
  full and faithful.
* `Stacks.Sites.AbelianSumFormula.base_eq_of_hom`: a morphism of the comma category does not
  change the simplex map, so the summands are pairwise disjoint.
* `Stacks.Sites.AbelianSumFormula.summandInclusion_obj_mk_hom_fiber`: every object of the comma
  category is the image under `summandInclusion` of an object of the summand indexed by its own
  simplex map, so the summands jointly exhaust it.

## Implementation notes

The decomposition is recorded as a full and faithful functor for each `ψ` together with the two
statements that make the family a coproduct decomposition — disjointness and exhaustion — rather
than as an equivalence with a `CategoryTheory.Sigma` category: the index of a
`CategoryTheory.Sigma.SigmaHom` has to match definitionally, while here the two simplex maps of the
source and target of a morphism agree only propositionally, by `base_eq_of_hom`.

The index set of the decomposition is finite: `Finite (n ⟶ m)` is an instance for
`SimplexCategory`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe u

namespace Stacks.Sites.AbelianSumFormula

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc CategoryTheory.Pseudofunctor.CoGrothendieck.ι

variable {Cs : SimplicialSite.{u}} {m n : SimplexCategory} {W : Cs.underlying.obj m}

/-- In case (A) of Stacks 09WE the inclusion of the degree-`n` component into the total category
is the fibre inclusion of the contravariant Grothendieck construction. -/
theorem componentFunctor_inl_eq (Cs : SimplicialSite.{u}) (n : SimplexCategory) :
    SimplicialSiteSituation.componentFunctor (⟨Sum.inl Cs⟩ : SimplicialSiteSituation.{u}) n =
      CoGrothendieck.ι Cs.totalPseudofunctor (op n) :=
  rfl

/-- A morphism `f` of the degree-`n` component underlies a morphism of the comma category
between the objects with simplex map `ψ` attached to `x` and `y` exactly when it is a morphism of
`StructuredArrow W u_ψ` from `x` to `y`. -/
theorem summandInclusion_w_iff (ψ : n ⟶ m)
    {x y : StructuredArrow W (Cs.underlying.map ψ).toFunctor} (f : x.right ⟶ y.right) :
    (StructuredArrow.mk (S := (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor))
        (T := CoGrothendieck.ι Cs.totalPseudofunctor (op n)) (Y := x.right)
        ⟨ψ.op, x.hom⟩).hom ≫
      (CoGrothendieck.ι Cs.totalPseudofunctor (op n)).map f =
    (StructuredArrow.mk (S := (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor))
        (T := CoGrothendieck.ι Cs.totalPseudofunctor (op n)) (Y := y.right)
        ⟨ψ.op, y.hom⟩).hom ↔
      x.hom ≫ (Cs.underlying.map ψ).toFunctor.map f = y.hom := by
  rw [CoGrothendieck.Hom.ext_iff]
  dsimp
  simp only [SimplicialSite.totalPseudofunctor, CoGrothendieck.categoryStruct_comp_fiber,
    CoGrothendieck.ι_map_fiber, Functor.toPseudofunctor'_mapId,
    Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app,
    CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  refine ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨Category.comp_id _, ?_⟩⟩
  · rw [← Category.assoc] at h
    exact (cancel_mono _).mp h
  · rw [← Category.assoc]
    exact congrArg (· ≫ _) h

/-- The inclusion of the summand of the comma category indexed by a simplex map `ψ : n ⟶ m`: an
object `W ⟶ u_ψ c` of `StructuredArrow W u_ψ` is read as the morphism `(m, W) ⟶ (n, c)` of the
total category with base `ψ`. -/
def summandInclusion (ψ : n ⟶ m) :
    StructuredArrow W (Cs.underlying.map ψ).toFunctor ⥤
      StructuredArrow (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
        (CoGrothendieck.ι Cs.totalPseudofunctor (op n)) where
  obj x := StructuredArrow.mk (Y := x.right) ⟨ψ.op, x.hom⟩
  map {_ _} k := StructuredArrow.homMk k.right ((summandInclusion_w_iff ψ k.right).mpr k.w)

/-- The object produced by the summand inclusion has the expected simplex map as its base. -/
@[simp]
theorem summandInclusion_obj_hom_base (ψ : n ⟶ m)
    (x : StructuredArrow W (Cs.underlying.map ψ).toFunctor) :
    ((summandInclusion ψ).obj x).hom.base = ψ.op :=
  rfl

/-- The object produced by the summand inclusion has the given structure morphism as its
fibre. -/
theorem summandInclusion_obj_hom_fiber (ψ : n ⟶ m)
    (x : StructuredArrow W (Cs.underlying.map ψ).toFunctor) :
    ((summandInclusion ψ).obj x).hom.fiber = x.hom :=
  rfl

/-- The morphism produced by the summand inclusion is the given one. -/
@[simp]
theorem summandInclusion_map_right (ψ : n ⟶ m)
    {x y : StructuredArrow W (Cs.underlying.map ψ).toFunctor} (k : x ⟶ y) :
    ((summandInclusion ψ).map k).right = k.right :=
  rfl

/-- The inclusion of the summand indexed by `ψ` into the comma category is faithful. -/
instance summandInclusion_faithful (ψ : n ⟶ m) : (summandInclusion (W := W) ψ).Faithful where
  map_injective {_ _ _ _} hk :=
    StructuredArrow.hom_ext _ _ (congrArg CategoryTheory.StructuredArrow.Hom.right hk :)

/-- The inclusion of the summand indexed by `ψ` into the comma category is full. -/
instance summandInclusion_full (ψ : n ⟶ m) : (summandInclusion (W := W) ψ).Full where
  map_surjective {_ _} g :=
    ⟨StructuredArrow.homMk g.right ((summandInclusion_w_iff ψ g.right).mp g.w),
      StructuredArrow.hom_ext _ _ rfl⟩

/-- **The summands are pairwise disjoint.** A morphism of the comma category of the component
inclusion does not change the simplex map. -/
theorem base_eq_of_hom {z z' : StructuredArrow (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
      (CoGrothendieck.ι Cs.totalPseudofunctor (op n))} (g : z ⟶ z') :
    z.hom.base = z'.hom.base := by
  have h := congrArg CoGrothendieck.Hom.base g.w
  simp only [CoGrothendieck.categoryStruct_comp_base, CoGrothendieck.ι_map_base] at h
  exact (Category.comp_id _).symm.trans h

/-- **The summands exhaust the comma category.** Every object of the comma category of the
component inclusion is the image, under the inclusion of the summand indexed by its own simplex
map, of the object given by its fibre component. -/
theorem summandInclusion_obj_mk_hom_fiber
    (z : StructuredArrow (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
      (CoGrothendieck.ι Cs.totalPseudofunctor (op n))) :
    (summandInclusion (W := W) z.hom.base.unop).obj
        (StructuredArrow.mk (Y := z.right) z.hom.fiber) = z :=
  rfl

end Stacks.Sites.AbelianSumFormula

end
