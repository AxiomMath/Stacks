module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModuleHomMk
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image functor on quasi-coherent modules on a groupoid in algebraic spaces

Let `f : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `A`.  The inverse image of a quasi-coherent module on the target
groupoid is `(ℱ, α) ↦ (f^*ℱ, f^*α)`, and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPullback.lean` proves everything
this needs: the object map, the two laws making it a quasi-coherent module on the source
groupoid, and the naturality of the transition morphism in the module.  Quasi-coherence of the
underlying module transports along an arbitrary morphism of algebraic spaces by Stacks 03GA, so
the object map is unconditional.  Here those three are assembled into the functor
`QCoh(U', R', s', t', c') ⥤ QCoh(U, R, s, t, c)` of Stacks 0442, for an arbitrary morphism `f` of
groupoids in algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackMap` is the inverse image of a morphism,
  read as a morphism of the underlying modules of the two inverse images, and
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackHom` is the resulting morphism of
  quasi-coherent modules on the source groupoid.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullback` is **Stacks 0442**, the inverse image
  functor on quasi-coherent modules along a morphism of groupoids in algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj_F`,
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj_F_obj` and
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj_alpha`: the two fields of the
  inverse image of a quasi-coherent module, as equations.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackMap_compatible`: the inverse image of a
  morphism is compatible with the two transition morphisms.  This is the morphism map of the
  functor.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackHom_id` and
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackHom_comp`: the two functor laws.
* `AlgebraicGeometry.Space.groupoidQuasicoherentPullback_obj` and
  `AlgebraicGeometry.Space.groupoidQuasicoherentPullback_map`: the object map and the morphism
  map of the functor.

## Implementation notes

Two reductions stood in the way of the functor, and both are avoided by naming things rather
than by writing them out.

**The transition morphism of the inverse image.**  The compatibility field of a morphism of
quasi-coherent modules on a groupoid reads the transition morphism of its source as `M.alpha`,
so for the inverse image it reads it as
`(AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj _ _ _ f M).alpha`, whereas
`AlgebraicGeometry.Space.groupoidModulePullbackTransition_naturality` is stated with
`AlgebraicGeometry.Space.groupoidModulePullbackTransition`.  The two are the same term after one
delta step and two projections, and yet `rfl` does not see it: the left-hand side is a field
projection applied to a *definition*, not to a constructor application, so weak-head
normalisation without delta leaves it alone; the two sides then have different head constants,
and lazy delta reduction unfolds whichever head was defined later.  That is
`groupoidModulePullbackTransition`, whose unfolding reaches into
`AlgebraicGeometry.Space.modulePullback` — the one reduction the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPullback.lean` record as beyond the
budget.  `groupoidQuasicoherentPullbackObj_alpha` sidesteps this by rewriting with the defining
equation of the object map first, after which the field projection reduces by iota and both
sides are literally the same term.

**The compatibility condition itself.**  Written out at these types it is a term of tens of
thousands of nodes, and the kernel's budget is per declaration, so no declaration can both
carry it written out and do anything further with it.  Every morphism here is therefore built
with `AlgebraicGeometry.Space.QuasicoherentModule.homMk`, which pays for the condition once with
its arguments still variables; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentModuleHomMk.lean`.  Filling the
compatibility field with the naturality statement directly does not elaborate, and filling it
with a restatement of the naturality statement whose type is written out is a kernel timeout.

## References

* [Stacks Project, Tag 0442](https://stacks.math.columbia.edu/tag/0442)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G G' : GroupoidInAlgebraicSpaces B S hS A}

variable (B S hS) (φ : Hom G G')

/-- The underlying quasi-coherent module of the inverse image of a quasi-coherent module on a
groupoid in algebraic spaces is the inverse image of the underlying quasi-coherent module. -/
theorem groupoidQuasicoherentPullbackObj_F (M : QuasicoherentModule B S hS G') :
    (groupoidQuasicoherentPullbackObj B S hS φ M).F =
      ⟨(modulePullback B S hS φ.objectsMap).obj M.F.obj,
        isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ.objectsMap
          M.F.obj M.F.property⟩ :=
  rfl

/-- The underlying module of the inverse image of a quasi-coherent module on a groupoid in
algebraic spaces is the inverse image of its underlying module. -/
@[simp]
theorem groupoidQuasicoherentPullbackObj_F_obj (M : QuasicoherentModule B S hS G') :
    (groupoidQuasicoherentPullbackObj B S hS φ M).F.obj =
      (modulePullback B S hS φ.objectsMap).obj M.F.obj :=
  rfl

/-- **The transition morphism of the inverse image, as an equation.**  It is the reindexing
`f^*α` of the given transition morphism.

This is `rfl`, but not provably so within the budget: see the implementation notes.  Rewriting
with the defining equation of the object map exposes the structure constructor, after which the
field projection reduces by iota. -/
@[simp]
theorem groupoidQuasicoherentPullbackObj_alpha (M : QuasicoherentModule B S hS G') :
    (groupoidQuasicoherentPullbackObj B S hS φ M).alpha =
      groupoidModulePullbackTransition B S hS φ M.F.obj M.alpha := by
  simp only [groupoidQuasicoherentPullbackObj]

/-- **The inverse image of a morphism of quasi-coherent modules on the target groupoid**, read
as a morphism of the underlying modules of the two inverse images.

This is `(AlgebraicGeometry.Space.modulePullback _ _ _ f.objectsMap).map φ.hom`; the point of
the name is the type it is given, which is the type the morphisms of
`AlgebraicGeometry.Space.QuasicoherentModule` are built from. -/
def groupoidQuasicoherentPullbackMap {M N : QuasicoherentModule B S hS G'} (f : M ⟶ N) :
    (groupoidQuasicoherentPullbackObj B S hS φ M).F.obj ⟶
      (groupoidQuasicoherentPullbackObj B S hS φ N).F.obj :=
  (modulePullback B S hS φ.objectsMap).map f.hom

/-- `AlgebraicGeometry.Space.groupoidQuasicoherentPullbackMap` is the inverse image of the
underlying morphism of modules. -/
theorem groupoidQuasicoherentPullbackMap_eq {M N : QuasicoherentModule B S hS G'} (f : M ⟶ N) :
    groupoidQuasicoherentPullbackMap B S hS φ f =
      (modulePullback B S hS φ.objectsMap).map f.hom :=
  rfl

/-- **The inverse image of a morphism is compatible with the two transition morphisms.**  This
is `AlgebraicGeometry.Space.groupoidModulePullbackTransition_naturality`, read at the two
inverse images, and it is the morphism map of the functor below. -/
theorem groupoidQuasicoherentPullbackMap_compatible {M N : QuasicoherentModule B S hS G'}
    (f : M ⟶ N) :
    QuasicoherentModule.Compatible (groupoidQuasicoherentPullbackMap B S hS φ f) := by
  unfold QuasicoherentModule.Compatible
  rw [groupoidQuasicoherentPullbackMap_eq, groupoidQuasicoherentPullbackObj_alpha,
    groupoidQuasicoherentPullbackObj_alpha]
  exact groupoidModulePullbackTransition_naturality B S hS φ M.F.obj M.alpha N.alpha
    f.hom f.comm

/-- The inverse image of an identity is an identity. -/
theorem groupoidQuasicoherentPullbackMap_id (M : QuasicoherentModule B S hS G') :
    groupoidQuasicoherentPullbackMap B S hS φ (𝟙 M) =
      𝟙 (groupoidQuasicoherentPullbackObj B S hS φ M).F.obj := by
  rw [groupoidQuasicoherentPullbackMap_eq]
  exact (modulePullback B S hS φ.objectsMap).map_id M.F.obj

/-- The inverse image of a composite is the composite of the inverse images. -/
theorem groupoidQuasicoherentPullbackMap_comp {M N P : QuasicoherentModule B S hS G'}
    (f : M ⟶ N) (g : N ⟶ P) :
    groupoidQuasicoherentPullbackMap B S hS φ (f ≫ g) =
      groupoidQuasicoherentPullbackMap B S hS φ f ≫
        groupoidQuasicoherentPullbackMap B S hS φ g := by
  rw [groupoidQuasicoherentPullbackMap_eq, groupoidQuasicoherentPullbackMap_eq,
    groupoidQuasicoherentPullbackMap_eq]
  exact (modulePullback B S hS φ.objectsMap).map_comp f.hom g.hom

/-- **The inverse image of a morphism of quasi-coherent modules on the target groupoid, as a
morphism of quasi-coherent modules on the source groupoid.**  This is the morphism map of the
functor below. -/
def groupoidQuasicoherentPullbackHom {M N : QuasicoherentModule B S hS G'} (f : M ⟶ N) :
    groupoidQuasicoherentPullbackObj B S hS φ M ⟶
      groupoidQuasicoherentPullbackObj B S hS φ N :=
  QuasicoherentModule.homMk (groupoidQuasicoherentPullbackMap B S hS φ f)
    (groupoidQuasicoherentPullbackMap_compatible B S hS φ f)

/-- The underlying morphism of modules of
`AlgebraicGeometry.Space.groupoidQuasicoherentPullbackHom` is
`AlgebraicGeometry.Space.groupoidQuasicoherentPullbackMap`. -/
@[simp]
theorem groupoidQuasicoherentPullbackHom_hom {M N : QuasicoherentModule B S hS G'} (f : M ⟶ N) :
    (groupoidQuasicoherentPullbackHom B S hS φ f).hom =
      groupoidQuasicoherentPullbackMap B S hS φ f :=
  rfl

/-- The inverse image of an identity is an identity. -/
theorem groupoidQuasicoherentPullbackHom_id (M : QuasicoherentModule B S hS G') :
    groupoidQuasicoherentPullbackHom B S hS φ (𝟙 M) =
      𝟙 (groupoidQuasicoherentPullbackObj B S hS φ M) := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [groupoidQuasicoherentPullbackHom_hom, QuasicoherentModule.id_hom]
  exact groupoidQuasicoherentPullbackMap_id B S hS φ M

/-- The inverse image of a composite is the composite of the inverse images. -/
theorem groupoidQuasicoherentPullbackHom_comp {M N P : QuasicoherentModule B S hS G'}
    (f : M ⟶ N) (g : N ⟶ P) :
    groupoidQuasicoherentPullbackHom B S hS φ (f ≫ g) =
      groupoidQuasicoherentPullbackHom B S hS φ f ≫
        groupoidQuasicoherentPullbackHom B S hS φ g := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [groupoidQuasicoherentPullbackHom_hom, QuasicoherentModule.comp_hom,
    groupoidQuasicoherentPullbackHom_hom, groupoidQuasicoherentPullbackHom_hom]
  exact groupoidQuasicoherentPullbackMap_comp B S hS φ f g

/-- **Stacks 0442.**  The inverse image along a morphism `f` of groupoids in algebraic spaces is
a functor `QCoh(U', R', s', t', c') ⥤ QCoh(U, R, s, t, c)`: it sends a quasi-coherent module
`(ℱ, α)` on the target groupoid to the inverse image `(f^*ℱ, f^*α)` of
`AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj`, and a morphism to the inverse image
of the underlying morphism of modules on the spaces of objects. -/
@[stacks 0442 "the inverse image functor on quasi-coherent modules"]
def groupoidQuasicoherentPullback :
    QuasicoherentModule B S hS G' ⥤ QuasicoherentModule B S hS G where
  obj M := groupoidQuasicoherentPullbackObj B S hS φ M
  map f := groupoidQuasicoherentPullbackHom B S hS φ f
  map_id M := groupoidQuasicoherentPullbackHom_id B S hS φ M
  map_comp f g := groupoidQuasicoherentPullbackHom_comp B S hS φ f g

/-- The object map of the inverse image functor is
`AlgebraicGeometry.Space.groupoidQuasicoherentPullbackObj`. -/
@[simp]
theorem groupoidQuasicoherentPullback_obj (M : QuasicoherentModule B S hS G') :
    (groupoidQuasicoherentPullback B S hS φ).obj M =
      groupoidQuasicoherentPullbackObj B S hS φ M :=
  rfl

/-- The morphism map of the inverse image functor is
`AlgebraicGeometry.Space.groupoidQuasicoherentPullbackHom`. -/
@[simp]
theorem groupoidQuasicoherentPullback_map {M N : QuasicoherentModule B S hS G'} (f : M ⟶ N) :
    (groupoidQuasicoherentPullback B S hS φ).map f =
      groupoidQuasicoherentPullbackHom B S hS φ f :=
  rfl

end AlgebraicGeometry.Space

end
