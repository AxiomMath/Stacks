module

public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Unit

/-!
# `restrictFunctorIsoPullback` is pseudofunctorial, and the restriction maps of [Stacks, Tag 01XL]

The coefficient system of [Stacks, Tag 01XL] attaches to an object `A` over `X` the module
`a_* a^* ℱ`, and its restriction maps are
`Stacks.AlgebraicGeometry.RelativeCech.relativeUnit`, built from the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and from
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.  Neither of those two has a description on
sections, which is why the naturality *in the open set* of
`Stacks.Tag01XLCoefficientIso.absoluteCechOpensPresheafEvalIso` was left open.

Along an open immersion both ingredients are replaced by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, where every structure map *is* a presheaf
restriction map:

* the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is
  `ℱ(U) ⟶ ℱ(f ''ᵁ f ⁻¹ᵁ U)` (`restrictAdjunction_unit_app_app`);
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` is an `eqToHom` restriction
  (`restrictFunctorComp_inv_app_app`).

This file transports the restriction maps across
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.  The content is that that
isomorphism is **pseudofunctorial**: it carries `restrictFunctorComp` to `pullbackComp`.

That statement is not in Mathlib or elsewhere in the library.  Pinned Mathlib contains exactly two
occurrences of `restrictFunctorIsoPullback` — its own definition and the sentence of
`restrictFunctor`'s docstring announcing it — so it carries no lemma about it whatever.  Across
Mathlib and this library, 30 declarations mention it and **none states a relation between it and
`restrictFunctorComp` or `pullbackComp`**: every occurrence is a transport of a property of a
module along the isomorphism at a single morphism.

## Main results

* `Stacks.Tag01XLCoefficientNat.unit_restrictCompAdjunction_comp_restrictFunctorComp_inv`: the
  unit of the composite restriction adjunction, followed by `restrictFunctorComp`, is the unit of
  the restriction adjunction of the composite.  This is the one step taken on sections, and there
  it is three presheaf restriction maps composing to one.
* `Stacks.Tag01XLCoefficientNat.restrictFunctorIsoPullback_comp`: **pseudofunctoriality of
  `restrictFunctorIsoPullback`** — the horizontal composite of the comparisons for `u` and `b`,
  followed by `pullbackComp u b`, is `restrictFunctorComp u b` followed by the comparison for
  `u ≫ b`.
* `Stacks.Tag01XLCoefficientNat.restrictUnitStep`: the restriction map of the coefficient system
  in the `restrictFunctor` spelling, and
  `Stacks.Tag01XLCoefficientNat.map_restrictFunctorIsoPullback_comp_relativeUnit`: **it is
  `relativeUnit`**, conjugated by `restrictFunctorIsoPullback`.

## Implementation notes

Nothing is proved by a conversion between two large composites.  Every step is an identity of
natural transformations evaluated at a *variable* module `M`, and the only step that descends to
sections is `unit_restrictCompAdjunction_comp_restrictFunctorComp_inv`, where both sides are
`M.presheaf.map` of morphisms of `X.Opens` and the lattice of open sets is a thin category, so
`thin_map_comp₃` closes it.

Two spellings of one functor are used interchangeably and are definitionally equal:
`AlgebraicGeometry.Scheme.Modules.pushforward u ⋙ pushforward b` and
`pushforward (u ≫ b)` — `Stacks.AlgebraicGeometry.RelativeCech.pushforward_comp_functor_map`.
`CategoryTheory.Category.assoc` is used as a *term* rather than through `rw`, because rewriting
re-associates a composite whose intermediate object is spelled with the first of those two and
the goal is then not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Tag01XLCoefficientNat

/-! ### Thinness of the lattice of open sets -/

variable {X : Scheme.{u}}

/-- Two restriction maps of a presheaf on the open sets of a scheme compose to a restriction
map:  any two morphisms of `X.Opens` with the same source and target are equal. -/
theorem thin_map_comp₂ {A : Type*} [Category A] (P : (X.Opens)ᵒᵖ ⥤ A)
    {U V W : (X.Opens)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) :
    P.map f ≫ P.map g = P.map h :=
  (P.map_comp f g).symm.trans (congrArg P.map (Subsingleton.elim _ _))

/-- `thin_map_comp₂` for three factors, left-associated as a `simp`-normalised composite
appears. -/
theorem thin_map_comp₃ {A : Type*} [Category A] (P : (X.Opens)ᵒᵖ ⥤ A)
    {U V W T : (X.Opens)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (k : W ⟶ T) (h : U ⟶ T) :
    (P.map f ≫ P.map g) ≫ P.map k = P.map h :=
  (congrArg (· ≫ P.map k) (thin_map_comp₂ P f g (f ≫ g))).trans
    (thin_map_comp₂ P (f ≫ g) k h)

/-! ### The two composite adjunctions -/

variable {Y Z : Scheme.{u}} (u : Y ⟶ Z) (b : Z ⟶ X)

/-- The composite of the two pullback--pushforward adjunctions of `u` and `b`.  Its right
adjoint is `pushforward u ⋙ pushforward b`, which is `pushforward (u ≫ b)`. -/
noncomputable def pullbackCompAdjunction :
    Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback u ⊣
      pushforward u ⋙ pushforward b :=
  (pullbackPushforwardAdjunction b).comp (pullbackPushforwardAdjunction u)

variable [IsOpenImmersion u] [IsOpenImmersion b]

/-- The composite of the two restriction adjunctions of `u` and `b`, available because both are
open immersions.  Its right adjoint is the same `pushforward u ⋙ pushforward b`. -/
noncomputable def restrictCompAdjunction :
    restrictFunctor b ⋙ restrictFunctor u ⊣ pushforward u ⋙ pushforward b :=
  (restrictAdjunction b).comp (restrictAdjunction u)

/-- **The unit of the composite restriction adjunction, followed by
`restrictFunctorComp`, is the unit of the restriction adjunction of the composite.**  This is the
only step of this file that descends to sections, and there it reads: restricting to the image of
`b`, then to the image of `u` inside it, then along the identification of the two images, is
restricting to the image of `u ≫ b`. -/
theorem unit_restrictCompAdjunction_comp_restrictFunctorComp_inv (M : X.Modules) :
    (restrictCompAdjunction u b).unit.app M ≫
        (pushforward u ⋙ pushforward b).map ((restrictFunctorComp u b).inv.app M) =
      (restrictAdjunction (u ≫ b)).unit.app M := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  rw [restrictCompAdjunction, Adjunction.comp_unit_app]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, Scheme.Modules.restrict_map,
    Functor.comp_map]
  refine Eq.trans ?_ (Scheme.Modules.restrictAdjunction_unit_app_app (u ≫ b) M U).symm
  exact thin_map_comp₃ M.presheaf _ _ _ _

/-- The unit of `restrictFunctor u ⊣ u_*` is natural with respect to the comparison for `b`. -/
private theorem unit_comp_map_isoPullback (M : X.Modules) :
    (restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
        (pushforward u).map ((restrictFunctor u).map ((restrictFunctorIsoPullback b).hom.app M)) =
      (restrictFunctorIsoPullback b).hom.app M ≫
        (restrictAdjunction u).unit.app ((Scheme.Modules.pullback b).obj M) :=
  ((restrictAdjunction u).unit.naturality ((restrictFunctorIsoPullback b).hom.app M)).symm

/-- The unit of the composite restriction adjunction, followed by the horizontal composite of
the two comparisons `restrictFunctor ≅ pullback`, is the unit of the composite
pullback--pushforward adjunction.  Both halves are
`Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app`, after the naturality of
the unit of `restrictAdjunction u` is used to move the comparison for `b` past it. -/
theorem unit_restrictCompAdjunction_comp_isoPullback (M : X.Modules) :
    (restrictCompAdjunction u b).unit.app M ≫ (pushforward u ⋙ pushforward b).map
        ((restrictFunctor u).map ((restrictFunctorIsoPullback b).hom.app M) ≫
          (restrictFunctorIsoPullback u).hom.app ((Scheme.Modules.pullback b).obj M)) =
      (pullbackCompAdjunction u b).unit.app M := by
  have hnat := congrArg (pushforward b).map (unit_comp_map_isoPullback u b M)
  simp only [Functor.map_comp] at hnat
  rw [restrictCompAdjunction, pullbackCompAdjunction, Adjunction.comp_unit_app,
    Adjunction.comp_unit_app,
    Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app b M,
    Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app u
      ((Scheme.Modules.pullback b).obj M),
    Functor.map_comp, Functor.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  refine congrArg (fun k => (restrictAdjunction b).unit.app M ≫ k) ?_
  rw [← Category.assoc, ← Category.assoc, hnat]

/-! ### Pseudofunctoriality of the comparison of restriction with inverse image -/

/-- The transpose of the left-hand side of `restrictFunctorIsoPullback_comp` is the unit of
`(u ≫ b)^* ⊣ (u ≫ b)_*`. -/
theorem unit_restrictCompAdjunction_comp_isoPullback_comp_pullbackComp (M : X.Modules) :
    (restrictCompAdjunction u b).unit.app M ≫ (pushforward u ⋙ pushforward b).map
        (((restrictFunctor u).map ((restrictFunctorIsoPullback b).hom.app M) ≫
          (restrictFunctorIsoPullback u).hom.app ((Scheme.Modules.pullback b).obj M)) ≫
          (pullbackComp u b).hom.app M) =
      (pullbackPushforwardAdjunction (u ≫ b)).unit.app M := by
  rw [Functor.map_comp, ← Category.assoc,
    unit_restrictCompAdjunction_comp_isoPullback u b M, pullbackCompAdjunction,
    Stacks.AlgebraicGeometry.RelativeCech.unit_comp_app,
    Stacks.AlgebraicGeometry.RelativeCech.pushforward_comp_functor_map]
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun k =>
    (pullbackPushforwardAdjunction (u ≫ b)).unit.app M ≫ k) ?_) (Category.comp_id _)
  exact (((pushforward (u ≫ b)).map_comp _ _).symm.trans
    (congrArg (pushforward (u ≫ b)).map ((pullbackComp u b).inv_hom_id_app M))).trans
    (CategoryTheory.Functor.map_id _ _)

/-- The transpose of the right-hand side of `restrictFunctorIsoPullback_comp` is the same unit of
`(u ≫ b)^* ⊣ (u ≫ b)_*`. -/
theorem unit_restrictCompAdjunction_comp_restrictFunctorComp_inv_comp_isoPullback
    (M : X.Modules) :
    (restrictCompAdjunction u b).unit.app M ≫ (pushforward u ⋙ pushforward b).map
        ((restrictFunctorComp u b).inv.app M ≫
          (restrictFunctorIsoPullback (u ≫ b)).hom.app M) =
      (pullbackPushforwardAdjunction (u ≫ b)).unit.app M := by
  rw [Functor.map_comp, ← Category.assoc,
    unit_restrictCompAdjunction_comp_restrictFunctorComp_inv u b M]
  exact (Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app
    (u ≫ b) M).symm

/-- **`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is pseudofunctorial:** the
horizontal composite of the comparisons for `u` and for `b`, followed by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` followed by the comparison for `u ≫ b`.

Both sides are morphisms out of a value of the left adjoint of the composite restriction
adjunction, and both have the unit of `(u ≫ b)^* ⊣ (u ≫ b)_*` as their transpose, so they agree
by injectivity of `CategoryTheory.Adjunction.homEquiv`. -/
theorem restrictFunctorIsoPullback_comp (M : X.Modules) :
    ((restrictFunctor u).map ((restrictFunctorIsoPullback b).hom.app M) ≫
          (restrictFunctorIsoPullback u).hom.app ((Scheme.Modules.pullback b).obj M)) ≫
        (pullbackComp u b).hom.app M =
      (restrictFunctorComp u b).inv.app M ≫
        (restrictFunctorIsoPullback (u ≫ b)).hom.app M := by
  refine ((restrictCompAdjunction u b).homEquiv M _).injective ?_
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
    unit_restrictCompAdjunction_comp_isoPullback_comp_pullbackComp u b M,
    unit_restrictCompAdjunction_comp_restrictFunctorComp_inv_comp_isoPullback u b M]

/-- The pseudofunctoriality, transposed:  the comparison for `b` followed by the unit of
`u^* ⊣ u_*` and `pullbackComp` is the unit of `restrictFunctor u ⊣ u_*` followed by
`restrictFunctorComp` and the comparison for `u ≫ b`.  This is the form the restriction maps of
the coefficient system are in. -/
theorem isoPullback_comp_unit (M : X.Modules) :
    (restrictFunctorIsoPullback b).hom.app M ≫
        ((pullbackPushforwardAdjunction u).unit.app ((Scheme.Modules.pullback b).obj M) ≫
          (pushforward u).map ((pullbackComp u b).hom.app M)) =
      (restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
        (pushforward u).map ((restrictFunctorComp u b).inv.app M ≫
          (restrictFunctorIsoPullback (u ≫ b)).hom.app M) := by
  rw [← restrictFunctorIsoPullback_comp u b M, Functor.map_comp, Functor.map_comp,
    Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app u
      ((Scheme.Modules.pullback b).obj M)]
  simp only [Category.assoc]
  rw [← Category.assoc ((restrictAdjunction u).unit.app ((restrictFunctor b).obj M)),
    unit_comp_map_isoPullback u b M]
  simp only [Category.assoc]

/-! ### The restriction maps of the coefficient system, on the `restrictFunctor` side -/

/-- **The restriction map of the coefficient system of [Stacks, Tag 01XL], in the
`restrictFunctor` spelling.**  It is the unit of `restrictFunctor u ⊣ u_*` inserted inside the
restriction to `b`, followed by `restrictFunctorComp`; on sections it is a single presheaf
restriction map. -/
noncomputable def restrictUnitStep :
    restrictFunctor b ⋙ pushforward b ⟶
      restrictFunctor (u ≫ b) ⋙ pushforward (u ≫ b) :=
  Functor.whiskerRight
      (Functor.whiskerLeft (restrictFunctor b) (restrictAdjunction u).unit) (pushforward b) ≫
    Functor.whiskerRight (restrictFunctorComp u b).inv (pushforward (u ≫ b))

/-- The components of `restrictUnitStep`. -/
theorem restrictUnitStep_app (M : X.Modules) :
    (restrictUnitStep u b).app M =
      (pushforward b).map ((restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
        (pushforward u).map ((restrictFunctorComp u b).inv.app M)) := by
  change (Functor.whiskerRight
      (Functor.whiskerLeft (restrictFunctor b) (restrictAdjunction u).unit)
        (pushforward b)).app M ≫
      (Functor.whiskerRight (restrictFunctorComp u b).inv (pushforward (u ≫ b))).app M = _
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp]
  rfl

/-- **The restriction map of the coefficient system is `relativeUnit`**, conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.  This is the identification that
makes the naturality in the open set of
`Stacks.Tag01XLCoefficientIso.absoluteCechOpensPresheafEvalIso` a computation with presheaf
restriction maps. -/
theorem map_restrictFunctorIsoPullback_comp_relativeUnit (M : X.Modules) :
    (pushforward b).map ((restrictFunctorIsoPullback b).hom.app M) ≫
        (Stacks.AlgebraicGeometry.RelativeCech.relativeUnit u b).app M =
      (restrictUnitStep u b).app M ≫
        (pushforward b).map ((pushforward u).map
          ((restrictFunctorIsoPullback (u ≫ b)).hom.app M)) := by
  have hin : (restrictFunctorIsoPullback b).hom.app M ≫
        ((pullbackPushforwardAdjunction u).unit.app ((Scheme.Modules.pullback b).obj M) ≫
          (pushforward u).map ((pullbackComp u b).hom.app M)) =
      ((restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
        (pushforward u).map ((restrictFunctorComp u b).inv.app M)) ≫
        (pushforward u).map ((restrictFunctorIsoPullback (u ≫ b)).hom.app M) :=
    (isoPullback_comp_unit u b M).trans
      ((congrArg (fun k => (restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫ k)
        ((pushforward u).map_comp ((restrictFunctorComp u b).inv.app M)
          ((restrictFunctorIsoPullback (u ≫ b)).hom.app M))).trans
        (Category.assoc _ _ _).symm)
  rw [Stacks.AlgebraicGeometry.RelativeCech.relativeUnit_app, restrictUnitStep_app]
  exact ((pushforward b).map_comp ((restrictFunctorIsoPullback b).hom.app M)
      ((pullbackPushforwardAdjunction u).unit.app ((Scheme.Modules.pullback b).obj M) ≫
        (pushforward u).map ((pullbackComp u b).hom.app M))).symm.trans
    ((congrArg (pushforward b).map hin).trans
      ((pushforward b).map_comp
        ((restrictAdjunction u).unit.app ((restrictFunctor b).obj M) ≫
          (pushforward u).map ((restrictFunctorComp u b).inv.app M))
        ((pushforward u).map ((restrictFunctorIsoPullback (u ≫ b)).hom.app M))))

end Stacks.Tag01XLCoefficientNat

end
