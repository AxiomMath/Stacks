module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# The chartwise universal property of the direct image of modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. Attached to `f` is the adjoint pair

`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)`, `f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)`

on the modules of the small étale sites. This file defines a linear map of sections along `f`,
the universal property that characterizes the direct image among functors admitting such maps,
and the structure bundling the direct and inverse images of modules with their properties.

## Main definitions

* `AlgebraicGeometry.Space.ModuleFMap`: a linear map of sections along a morphism of algebraic
  spaces: a map of sections for every commutative diagram of étale scheme charts, natural under
  simultaneous restriction of both charts, additive, and semilinear over pullback of regular
  functions along the vertical scheme morphism.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation`: the universal property of the
  direct image of modules: a counit linear map and a bijection, natural in the source module,
  between module morphisms into the functor and linear maps along `f`.
* `AlgebraicGeometry.Space.ModuleImageData`: the direct and inverse image functors, the
  universal property of the direct image, additivity, the adjunction, preservation of
  quasi-coherence by the inverse image, the composition comparisons normalized against the
  universal property, and the identification of the direct image of modules of the morphism of
  small étale ringed topoi by the same universal property.

## Main results

* `AlgebraicGeometry.Space.ModuleFMap.ext`: a linear map along `f` is determined by its values
  on sections.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation.homEquiv_symm_apply`: the inverse of
  the universal correspondence is computed by the counit.
* `AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso`: two functors satisfying the
  universal property of the direct image are canonically isomorphic on every module, by the
  isomorphism matching the two counits.

## Implementation notes

The first two fields of `AlgebraicGeometry.Space.ModuleFMap` are those of
`AlgebraicGeometry.Space.FMap`, for the presheaves of sets underlying the two modules. They are
written out rather than inherited because `FMap` is stated for presheaves of types on the small
étale sites while a module is a presheaf of modules over the structure sheaf. The two further
fields are additivity and semilinearity over `AlgebraicGeometry.Space.chartDiagramPullback`,
pullback of regular functions along the vertical scheme morphism of the chart diagram.

`AlgebraicGeometry.Space.ModulePushforwardPresentation` is a structure and not a `Prop`: the
correspondence between module morphisms and linear maps is data, and the direct image is
determined by it only up to the canonical isomorphism
`AlgebraicGeometry.Space.ModulePushforwardPresentation.objIso`. Its `naturality` field, which
says the counit is natural in the source module, fixes the functor on morphisms as well as on
objects.

The module universe is the universe `u` of the structure rings. The sections of the direct
image over an étale chart `V` of `Y` are a limit over the étale charts of `X` above `X ×_Y V`,
an index category that is only essentially small at `u`, and `Type m` for `m` unrelated to `u`
is not closed under `u`-sized limits.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/


@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Pullback of regular functions along the vertical scheme morphism of a diagram of étale
scheme charts, as a homomorphism of the sheaves of rings in which the modules are indexed. -/
noncomputable def chartDiagramPullback (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op d.V) ⟶
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op d.U) :=
  (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op)

/-- A linear map of sections along a morphism `f : X ⟶ Y` of algebraic spaces, evaluated on
every commutative diagram of étale scheme charts.  The coefficient map is pullback of regular
functions along the vertical scheme morphism of the diagram. -/
structure ModuleFMap (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) where
  /-- The map of sections attached to a chart diagram. -/
  app : (d : ChartDiagram B S hS X.1 Y.1 f.hom) →
    G.val.obj (op d.V) → F.val.obj (op d.U)
  /-- The maps of sections are compatible with étale restriction of both charts. -/
  naturality : ∀ (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
      (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V),
      (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
        d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j →
      ∀ s : G.val.obj (op d.V),
        app d' (G.val.map j.op s) = F.val.map i.op (app d s)
  /-- The maps of sections are additive. -/
  map_add (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s t : G.val.obj (op d.V)) :
    app d (s + t) = app d s + app d t
  /-- The maps of sections are semilinear over pullback of regular functions along the vertical
  scheme morphism. -/
  map_smul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
      (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op d.V))
      (s : G.val.obj (op d.V)) :
    app d (r • s) = chartDiagramPullback B S hS f d r • app d s

/-- The universal property of the direct image of modules.  The correspondence sends a module
morphism into the functor to its composite with the counit on scheme charts; its naturality in
the source module fixes the functor on morphisms as well as on objects. -/
structure ModulePushforwardPresentation (f : X ⟶ Y)
    (P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2) where
  /-- The counit: the canonical linear map along `f` from a module to its direct image. -/
  counit (F) : ModuleFMap B S hS f F (P.obj F)
  /-- Module morphisms into the direct image are exactly linear maps along `f`. -/
  homEquiv (F G) : (G ⟶ P.obj F) ≃ ModuleFMap B S hS f F G
  /-- The correspondence is composition with the counit. -/
  homEquiv_apply (F G) (a : G ⟶ P.obj F)
      (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)) :
    (homEquiv F G a).app d s = (counit F).app d (a.val.app (op d.V) s)
  /-- The counit is natural in the source module. -/
  naturality {F F'} (a : F ⟶ F')
      (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : (P.obj F).val.obj (op d.V)) :
    (counit F').app d ((P.map a).val.app (op d.V) s) =
      a.val.app (op d.U) ((counit F).app d s)

/-- A linear map along `f` is determined by its values on sections. -/
@[ext]
theorem ModuleFMap.ext {f : X ⟶ Y} {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2}
    {a b : ModuleFMap B S hS f F G} (h : a.app = b.app) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The inverse of the universal correspondence is computed by the counit. -/
theorem ModulePushforwardPresentation.homEquiv_symm_apply {f : X ⟶ Y}
    {P : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (F G) (a : ModuleFMap B S hS f F G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : G.val.obj (op d.V)) :
    (hP.counit F).app d (((hP.homEquiv F G).symm a).val.app (op d.V) s) = a.app d s := by
  rw [← hP.homEquiv_apply, Equiv.apply_symm_apply]

/-- **The universal property determines the direct image of modules.**  Two functors satisfying
the chartwise universal property of the direct image along `f` are canonically isomorphic on
every module, by the unique isomorphism matching the two counits. -/
noncomputable def ModulePushforwardPresentation.objIso {f : X ⟶ Y}
    {P Q : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (hP : ModulePushforwardPresentation B S hS f P)
    (hQ : ModulePushforwardPresentation B S hS f Q)
    (F : Modules.{u, u} B S hS X.1 X.2) : P.obj F ≅ Q.obj F where
  hom := (hQ.homEquiv F (P.obj F)).symm (hP.counit F)
  inv := (hP.homEquiv F (Q.obj F)).symm (hQ.counit F)
  hom_inv_id := by
    apply (hP.homEquiv F (P.obj F)).injective
    apply ModuleFMap.ext
    funext d s
    rw [hP.homEquiv_apply, hP.homEquiv_apply]
    change (hP.counit F).app d
      (((hP.homEquiv F (Q.obj F)).symm (hQ.counit F)).val.app (op d.V)
        (((hQ.homEquiv F (P.obj F)).symm (hP.counit F)).val.app (op d.V) s)) =
      (hP.counit F).app d s
    rw [hP.homEquiv_symm_apply, hQ.homEquiv_symm_apply]
  inv_hom_id := by
    apply (hQ.homEquiv F (Q.obj F)).injective
    apply ModuleFMap.ext
    funext d s
    rw [hQ.homEquiv_apply, hQ.homEquiv_apply]
    change (hQ.counit F).app d
      (((hQ.homEquiv F (P.obj F)).symm (hP.counit F)).val.app (op d.V)
        (((hP.homEquiv F (Q.obj F)).symm (hQ.counit F)).val.app (op d.V) s)) =
      (hQ.counit F).app d s
    rw [hQ.homEquiv_symm_apply, hP.homEquiv_symm_apply]

/-- For a morphism `f : X ⟶ Y` of algebraic spaces: the direct and inverse image of modules,
the chartwise universal property of the direct image, its additivity, the adjunction,
preservation of quasi-coherence by the inverse image, the composition comparison normalized
against the universal property, and the identification of the direct image of modules of the
morphism of small étale ringed topoi induced by `f` by the same universal property. -/
structure ModuleImageData (f : X ⟶ Y) where
  /-- The direct image of modules. -/
  pushforward : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2
  /-- It satisfies the chartwise universal property of the direct image. -/
  canonical : ModulePushforwardPresentation B S hS f pushforward
  /-- The direct image is additive. -/
  additive : pushforward.Additive
  /-- The inverse image of modules. -/
  pullback : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2
  /-- The inverse image is left adjoint to the direct image. -/
  adjunction : pullback ⊣ pushforward
  /-- The inverse image preserves quasi-coherence. -/
  preservesQuasicoherent : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2),
    [F.IsQuasicoherentOnSite] → (pullback.obj F).IsQuasicoherentOnSite
  /-- A composite of direct images satisfies the universal property of the direct image along
  the composite morphism. -/
  compositionPresentation {Z : AlgebraicSpaces B S hS} (g : Y ⟶ Z)
    (Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2)
    (hPg : ModulePushforwardPresentation B S hS g Pg) :
    ModulePushforwardPresentation B S hS (f ≫ g) (pushforward ⋙ Pg)
  /-- The composition comparison, normalized by the universal property of the direct image
  along the composite morphism. -/
  composition {Z : AlgebraicSpaces B S hS} (g : Y ⟶ Z)
    (Pg : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2)
    (Pfg : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2)
    (hPg : ModulePushforwardPresentation B S hS g Pg)
    (hPfg : ModulePushforwardPresentation B S hS (f ≫ g) Pfg) :
    { e : pushforward ⋙ Pg ≅ Pfg //
      ∀ F : Modules.{u, u} B S hS X.1 X.2,
        (hPfg.homEquiv F ((pushforward ⋙ Pg).obj F)) (e.hom.app F) =
          (compositionPresentation g Pg hPg).counit F }
  /-- The direct image of modules of the morphism of small étale ringed topoi induced by `f`
  satisfies the chartwise universal property of the direct image along `f`. -/
  ordinaryCanonical : ModulePushforwardPresentation B S hS f
    (smallEtaleRingedToposHom B S hS f).pushforwardModules
  /-- The direct image of modules of the morphism of small étale ringed topoi induced by `f`
  has a left adjoint. -/
  ordinaryPullback :
    Σ F : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2,
      F ⊣ (smallEtaleRingedToposHom B S hS f).pushforwardModules

end AlgebraicGeometry.Space

end
