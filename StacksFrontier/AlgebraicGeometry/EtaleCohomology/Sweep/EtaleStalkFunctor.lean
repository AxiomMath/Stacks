module

public import Mathlib.CategoryTheory.Action.Continuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint

/-!
# The étale stalk as a functor, and germs of sections

Let `B` be a big étale site containing a scheme `S`, and let `s` be a geometric point of `S`.
`AlgebraicGeometry.etaleStalk` is the stalk of a single presheaf on the small étale site of `S`,
the colimit over the étale neighbourhoods of `s`. Here it is made into a functor on the small
étale topos, together with the germ map that sends a section over a pointed étale neighbourhood
to its image in the stalk.

Both are needed to state the comparison of the small étale topos of a field with the category
of continuous sets over its absolute Galois group (Stacks 03QT): the equivalence there is
pinned down by a natural isomorphism with the stalk functor together with an equation on
germs, and the Galois action is read off from the action on germs.

`AlgebraicGeometry.ContinuousGSet.forget` forgets the continuous action on a continuous `G`-set;
it is the functor against which that natural isomorphism is stated.

## Main definitions

* `AlgebraicGeometry.etaleStalkPresheafFunctor` — the stalk at `s` as a functor on presheaves
  with values in an arbitrary category having the relevant colimits.
* `AlgebraicGeometry.etaleStalkFunctor` — the set-valued stalk at `s` as a functor on the
  small étale topos of `S`, i.e. the previous functor restricted along `sheafToPresheaf`.
* `AlgebraicGeometry.etaleStalkGerm` — the germ at `s` of a section over a pointed étale
  neighbourhood.
* `AlgebraicGeometry.ContinuousGSet.forget` — the underlying set of a continuous `G`-set.

## Main results

* `AlgebraicGeometry.etaleStalkPresheafFunctor_obj` — the general functor is objectwise the
  étale stalk.
* `AlgebraicGeometry.etaleStalkFunctor_obj` — the functor is objectwise the étale stalk.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.ContinuousGSet

/-- The underlying set of a continuous `G`-set, forgetting both the topology and the action. -/
abbrev forget (G : Type u) [Group G] [TopologicalSpace G] :
    ContinuousGSet.{u, v} G ⥤ Type v :=
  letI : HasForget₂ (Type v) TopCat.{v} :=
    { forget₂ := TopCat.discrete
      forget_comp := rfl }
  (ObjectProperty.ι _ : DiscreteContAction (Type v) G ⥤ ContAction (Type v) G) ⋙
    (ObjectProperty.ι _ : ContAction (Type v) G ⥤ Action (Type v) G) ⋙
      Action.forget (Type v) G

end AlgebraicGeometry.ContinuousGSet

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The étale stalk at a geometric point, as a functor on presheaves with values in any
category having colimits over the category of pointed étale neighbourhoods of `s`.
A presheaf is restricted along the projection from that category and the colimit is taken
there. -/
def etaleStalkPresheafFunctor (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A] :
    ((SmallEtale B S hS)ᵒᵖ ⥤ A) ⥤ A :=
  elementColimit (geometricPointFiber B S hS s) A

/-- The stalk functor on presheaves is objectwise the étale stalk. -/
theorem etaleStalkPresheafFunctor_obj (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A]
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    (etaleStalkPresheafFunctor B S hS s A).obj F = etaleStalk B S hS s F :=
  rfl

/-- The set-valued étale stalk at a geometric point, as a functor on the small étale topos.
A sheaf is restricted along the projection from the category of pointed étale neighbourhoods
of `s` and the colimit is taken there. -/
def etaleStalkFunctor : smallEtaleTopos.{u, max u v} B S hS ⥤ Type max u v :=
  sheafToPresheaf _ _ ⋙ etaleStalkPresheafFunctor B S hS s (Type max u v)

/-- The stalk functor is objectwise the étale stalk of the underlying presheaf. -/
theorem etaleStalkFunctor_obj (F : smallEtaleTopos.{u, max u v} B S hS) :
    (etaleStalkFunctor.{u, v} B S hS s).obj F =
      etaleStalk B S hS s ((sheafToPresheaf _ _).obj F) :=
  rfl

/-- The germ at `s` of a section of a sheaf over a pointed étale neighbourhood of `s`,
as an element of the étale stalk. -/
def etaleStalkGerm (F : smallEtaleTopos.{u, max u v} B S hS)
    (U : (geometricPointFiber B S hS s).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    (etaleStalkFunctor.{u, v} B S hS s).obj F :=
  colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
    (sheafToPresheaf _ _).obj F) (op U) t

/-- A morphism of sheaves on the small étale site carries the germ at `s` of a section to the
germ of the image section. -/
theorem etaleStalkFunctor_map_etaleStalkGerm
    {F G : smallEtaleTopos.{u, u + 1} B S hS} (α : F ⟶ G)
    (U : (geometricPointFiber B S hS s).Elements) (t : F.obj.obj (op U.1)) :
    (etaleStalkFunctor.{u, u + 1} B S hS s).map α
        (etaleStalkGerm.{u, u + 1} B S hS s F U t) =
      etaleStalkGerm.{u, u + 1} B S hS s G U (α.hom.app (op U.1) t) := by
  change (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F.obj) (op U) ≫
    colim.map (Functor.whiskerLeft (Functor.Elements.π
      (geometricPointFiber B S hS s)).op α.hom)) t = _
  rw [colimit.ι_map]
  rfl

/-- Every element of the étale stalk at `s` is the germ of a section over a pointed étale
neighbourhood of `s`. -/
theorem exists_etaleStalkGerm_eq (F : smallEtaleTopos.{u, u + 1} B S hS)
    (z : (etaleStalkFunctor.{u, u + 1} B S hS s).obj F) :
    ∃ (U : (geometricPointFiber B S hS s).Elements) (t : F.obj.obj (op U.1)),
      etaleStalkGerm.{u, u + 1} B S hS s F U t = z := by
  obtain ⟨V, t, ht⟩ := Types.jointly_surjective'
    (F := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F.obj) z
  exact ⟨V.unop, t, ht⟩

end AlgebraicGeometry

end
