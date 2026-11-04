module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackProperties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Additivity of the direct and inverse images of sheaves of modules

The right derived direct image of Stacks 07A6, and the comparison of successive right derived
direct images of Stacks 0D6E, both take place on homotopy categories of complexes of sheaves
of modules. Forming `F.mapHomotopyCategory` requires `F` to be additive, so every statement in
that family rests on the additivity of the underlying underived functor. This file supplies it
for the whole transport chain of Stacks 03D1, 03D2 and 03D6.

The substance is one lemma. The inverse image of Stacks 03D2 along a finite-product-preserving
functor `Φ` between categories of sheaves of sets acts on a morphism of sheaves of modules by
`Φ`, on the nose, on the underlying sheaves of sets
(`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMap`), while the addition on
each transported module is `Φ` applied to the addition map of the source read through the
product comparison (`CategoryTheory.Sheaf.moduleAddObj`). So additivity in the *morphism*
variable is the statement that `Φ` carries one commuting square to another, and reduces, through
`Functor.map_comp_apply` and `Functor.map_lift_apply`, to the additivity of each
`φ.val.app X` — no adjointness, no exactness, no sheafification.

That route matters: the direct image of modules is a right adjoint
(`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`), so its additivity would
also follow from `CategoryTheory.Adjunction.right_adjoint_additive` — but that adjunction is only
available under `HasWeakSheafify X.J AddCommGrpCat` and
`X.J.WEqualsLocallyBijective AddCommGrpCat`, because the left adjoint goes through extension of
scalars. Neither hypothesis is inhabited at an arbitrary site, and neither appears in the
statement of Stacks 03D1 or 03D6, so routing additivity through the adjunction would have
imported two hypotheses that the source does not have. Everything below is unconditional.

## Main results

* `Stacks.Sheaves.ToposPullback.additive_pullbackModuleFunctor` (Stacks 03D2): the inverse image
  of sheaves of modules along a finite-product-preserving functor is additive.
* `Stacks.Sheaves.ToposPushforward.additive_pushforwardModuleFunctor` (Stacks 03D1): the direct
  image of sheaves of modules along a morphism of topoi is additive.
* `Stacks.Sheaves.RingedToposModules.additive_directImageModules`,
  `Stacks.Sheaves.RingedToposModules.additive_pushforwardModules` (Stacks 03D6, part (1)): the
  same for the direct image read as a functor to modules over the structure sheaf, and for the
  direct image along a morphism of ringed topoi.

## Implementation notes

Each statement is given as its own `instance` rather than left to instance search, because
`pushforwardModuleFunctor` and `pushforwardModules` are plain `def`s: an instance proved at one
spelling does not fire at its unfolding.

`moduleSheafFunctor_map_add_eq` and `pullbackModuleFunctor_map_addObj` are stated at the raw
type of the transported group, with no expected type imposed on the sides. Writing the chain as
a single tactic proof fails instead: the closing `rw [Functor.map_comp_apply]` is rejected
because the goal's `x` is typed through `((pullbackModuleFunctor J Φ O).obj G).val.obj X` while
the rewrite needs it at `(Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf O G)`, and the
two spellings only agree at default transparency.

No tag is placed. Stacks Tag 0D6E is registered (`@[stacks 0D6E]`) on the invertibility of the derived
comparison alone, and none of these results is any clause of 0D6E, 03D1, 03D2 or 03D6 — they are
the additivity premise those statements consume, not part of what they assert.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) {G G' : SheafOfModules.{ww'} O}

omit [K.HasSheafCompose (forget RingCat.{ww'})] in
/-- The underlying morphism of sheaves of sets of a sum of two morphisms of sheaves of modules
is the pair of the two underlying morphisms followed by the addition map of the target. This is
the hom-level form of additivity, in the shape a finite-product-preserving functor can
transport. -/
lemma moduleSheafFunctor_map_add_eq (φ ψ : G ⟶ G') :
    (moduleSheafFunctor O).map (φ + ψ) =
      Limits.prod.lift ((moduleSheafFunctor O).map φ) ((moduleSheafFunctor O).map ψ) ≫
        Sheaf.moduleAddHom O G' := by
  refine Sheaf.hom_ext_sections (fun X s ↦ ?_)
  rw [Functor.map_comp_apply, Functor.map_lift_apply, Sheaf.sectionsFunctor_map_moduleAddHom]
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The inverse image of a morphism of sheaves of modules, read on a section, is `Φ` followed by
sections applied to the underlying morphism of sheaves of sets. This is
`moduleSheafFunctor_map_pullbackModuleMap` at the level of a single element. -/
lemma pullbackModuleFunctor_map_apply (χ : G ⟶ G') (X : Cᵒᵖ)
    (x : (Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf O G)) :
    (((pullbackModuleFunctor J Φ O).map χ).val.app X).hom x =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map ((moduleSheafFunctor O).map χ) x := rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The addition of two morphisms of inverse-image modules, read on a section. -/
lemma pullbackModuleFunctor_add_apply
    (α β : (pullbackModuleFunctor J Φ O).obj G ⟶ (pullbackModuleFunctor J Φ O).obj G')
    (X : Cᵒᵖ) (x : (Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf O G)) :
    ((α + β).val.app X).hom x = (α.val.app X).hom x + (β.val.app X).hom x := rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The addition of the transported module structure is `moduleAddObj`. -/
lemma pullbackModuleFunctor_addObj_eq (X : Cᵒᵖ)
    (a b : (Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf O G')) :
    letI := Sheaf.moduleObjAddCommGroup O G' (Φ ⋙ Sheaf.sectionsFunctor J X)
    a + b = Sheaf.moduleAddObj O G' (Φ ⋙ Sheaf.sectionsFunctor J X) a b := rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- `Φ` followed by sections carries the additivity square of `moduleSheafFunctor_map_add_eq` to
the addition of the transported module. Stated at the raw type of that module. -/
lemma pullbackModuleFunctor_map_addObj (X : Cᵒᵖ) (φ ψ : G ⟶ G')
    (x : (Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.moduleSheaf O G)) :
    letI := Sheaf.moduleObjAddCommGroup O G' (Φ ⋙ Sheaf.sectionsFunctor J X)
    (Φ ⋙ Sheaf.sectionsFunctor J X).map
        (Limits.prod.lift ((moduleSheafFunctor O).map φ) ((moduleSheafFunctor O).map ψ) ≫
          Sheaf.moduleAddHom O G') x =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map ((moduleSheafFunctor O).map φ) x +
        (Φ ⋙ Sheaf.sectionsFunctor J X).map ((moduleSheafFunctor O).map ψ) x := by
  rw [Functor.map_comp_apply, Functor.map_lift_apply]
  rfl

/-- **Stacks 03D2**, additivity: the inverse image of sheaves of modules along a
finite-product-preserving functor between categories of sheaves of sets is an additive functor.
Unconditional — no adjointness and no sheafification. -/
instance additive_pullbackModuleFunctor : (pullbackModuleFunctor J Φ O).Additive where
  map_add {G G' φ ψ} := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X ↦
      ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    refine (pullbackModuleFunctor_map_apply J Φ O (φ + ψ) X x).trans ?_
    refine ((congrArg (fun m ↦ (Φ ⋙ Sheaf.sectionsFunctor J X).map m x)
      (moduleSheafFunctor_map_add_eq O φ ψ)).trans ?_).trans
        (pullbackModuleFunctor_add_apply J Φ O _ _ X x).symm
    exact pullbackModuleFunctor_map_addObj J Φ O X φ ψ x

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf J RingCat.{ww})

/-- **Stacks 03D1**, additivity: the direct image of sheaves of modules along a morphism of
topoi is an additive functor. Restated at the `pushforwardModuleFunctor` spelling, since that
is a plain `def` and the instance on `pullbackModuleFunctor` does not fire at it. -/
instance additive_pushforwardModuleFunctor : (pushforwardModuleFunctor f O).Additive :=
  inferInstanceAs (pullbackModuleFunctor K f.pushforward O).Additive

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- The direct image of a sheaf of modules over the inverse-image sheaf of rings, read as a
sheaf of modules over the structure sheaf, is additive: it is the direct image of Stacks 03D1
followed by restriction of scalars along the unit, and restriction of scalars is additive. -/
instance additive_directImageModules
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (O : Sheaf K RingCat.{w'}) :
    (directImageModules f O).Additive :=
  inferInstanceAs (pushforwardModuleFunctor f (inverseImageRingSheaf f O) ⋙
    SheafOfModules.restrictScalars (ringUnit f O)).Additive

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- **Stacks 03D6, part (1)**, additivity: the direct image of sheaves of modules along a
morphism of ringed topoi is an additive functor. This is the premise that lets
`(pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ)` be formed, and so the premise
of the right derived direct image of Stacks 07A6 and of its composition law, Stacks 0D6E. -/
instance additive_pushforwardModules (f : RingedToposHom X Y) :
    (pushforwardModules f).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars f.fSharpInverseImage ⋙
    directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).Additive

end Stacks.Sheaves.RingedToposModules

end
