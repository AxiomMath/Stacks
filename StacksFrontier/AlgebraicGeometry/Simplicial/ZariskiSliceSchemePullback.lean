module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSlicePullback
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSites

/-!
# The pullback of modules along a degree map, localized at an open

Let `X` be a simplicial scheme, `φ : b ⟶ a` a map of simplicial degrees and `W` an open of `X_a`.
The morphism of schemes `X φ : X_b ⟶ X_a` localizes at `W`: it carries `(X φ)⁻¹W` to `W`, and the
pullback of sheaves of modules localizes with it, from the slice of the open-set site of `X_a` at
`W` to the slice of the open-set site of `X_b` at `(X φ)⁻¹W`.

This file constructs that localized pullback and proves the Beck–Chevalley isomorphism relating
it to the pullback along `X φ`: restricting a module on `X_a` to `W` and then pulling back along
the localized morphism is pulling back along `X φ` and then restricting to `(X φ)⁻¹W`. That is
Stacks 04J0 for the pullback of sheaves of modules, in the form
`SheafOfModules.overFunctorPullbackIso`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.sliceSchemePullback`: the pullback of sheaves of modules
  along `X φ`, localized at `W`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.sliceSchemePullbackOverFunctorIso`: the Beck–Chevalley
  isomorphism — the localized pullback of a restriction is the restriction of the pullback.

## Implementation notes

The comparison is `SheafOfModules.overFunctorPullbackIso`, which asks for the square of sites
`Over.star W ⋙ Over.post u ≅ u ⋙ Over.star (u.obj W)` for `u = Opens.map (X φ)` together with
the identification of its components with the product comparison maps of `u`. Both come from
`CategoryTheory.starCompOverPostIso`, which is exactly that square, built from the fact that
`Opens.map` of a continuous map preserves binary products: in a lattice a binary product is an
infimum, and the preimage of an intersection of opens is the intersection of their preimages.

That the pushforward of sheaves of modules along the structure map of a morphism of schemes has
a left adjoint is not proved again here: it is
`StacksTag09NE.isRightAdjoint_pushforward_toRingCatSheafHom` of
`StacksFrontier/AlgebraicGeometry/ClosedCoverGlue/Basic.lean`, which is why that module is imported.
Mathlib's own `AlgebraicGeometry.Scheme.Modules.pullback` relaxes a transparency option to find
the instance, which is not available here.

The hypothesis of `overFunctorPullbackIso` that both sites have binary products is why this is
the square the proof of Stacks 0D7M can use: the two sites here are open-set sites of schemes,
which are complete lattices, whereas the total Zariski site has no binary products at all — an
object of degree `a` and an object of degree `b` have no product over it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) {a b : SimplexCategoryᵒᵖ} (W : Opens ↥(X.obj a))
  (φ : b ⟶ a)

/-- **The inverse image of opens along a continuous map preserves finite limits.** In a lattice a
finite limit is the infimum of the finitely many objects of the diagram, and the inverse image of
an infimum of opens is the infimum of the inverse images. -/
public instance opensMap_preservesFiniteLimits {S T : TopCat.{u}} (f : S ⟶ T) :
    PreservesFiniteLimits (Opens.map f) := by
  refine ⟨fun J _ _ => ⟨fun {K} => preservesLimit_of_preserves_limit_cone
    (CompleteLattice.finiteLimitCone K).isLimit ?_⟩⟩
  refine IsLimit.ofIsoLimit (CompleteLattice.finiteLimitCone (K ⋙ Opens.map f)).isLimit
    (Cone.ext (eqToIso ?_) fun _ => Subsingleton.elim _ _)
  ext x
  simp

/-- Intersecting with `W` and then taking the inverse image along `X φ` is a continuous functor
to the slice of the degree-`b` site at `(X φ)⁻¹W`: it is a composite of two continuous
functors. -/
public instance starCompOverPost_isContinuous :
    (Over.star W ⋙ Over.post (Opens.map (X.map φ).base)).IsContinuous
      (Opens.grothendieckTopology ↥(X.obj a))
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology ↥(X.obj a)).over W) _

/-- Taking the inverse image along `X φ` and then intersecting with `(X φ)⁻¹W` is a continuous
functor: the other way round the same square. -/
public instance opensMapCompStar_isContinuous :
    (Opens.map (X.map φ).base ⋙ Over.star (slicePreimage X W φ)).IsContinuous
      (Opens.grothendieckTopology ↥(X.obj a))
      ((Opens.grothendieckTopology ↥(X.obj b)).over (slicePreimage X W φ)) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥(X.obj b)) _

/-- **The pullback of sheaves of modules along `X φ`, localized at an open `W` of `X_a`.** -/
public noncomputable abbrev sliceSchemePullback :=
  SheafOfModules.pullback.{u}
    (SheafOfModules.overComparison ((X.map φ).toRingCatSheafHom) W)

/-- **Beck–Chevalley for the localization of `X φ` at `W`,** Stacks 04J0 for the pullback of
sheaves of modules: restricting a module on `X_a` to `W` and pulling back along the localized
morphism is pulling back along `X φ` and restricting to `(X φ)⁻¹W`. -/
public noncomputable def sliceSchemePullbackOverFunctorIso :
    SheafOfModules.overFunctor.{u} ((X.obj a).ringCatSheaf) W ⋙ sliceSchemePullback X W φ ≅
      Scheme.Modules.pullback (X.map φ) ⋙
        SheafOfModules.overFunctor.{u} ((X.obj b).ringCatSheaf) (slicePreimage X W φ) :=
  SheafOfModules.overFunctorPullbackIso.{u} ((X.map φ).toRingCatSheafHom) W
    (starCompOverPostIso (Opens.map (X.map φ).base) W) (fun _ => rfl)

/-- **The arrows over `φ`, on the slice at `(a, W)`.** For an open `V ≤ W` of `X_a` the object
`(b, (X φ)⁻¹V)` of the total Zariski site maps to `(a, V)` over `φ`, and both map to `(a, W)`;
these arrows are natural in `V`, and they are what the transition of Stacks 09WF on the slice is
the direct image along.

This is the localization at `(a, W)` of
`AlgebraicGeometry.SimplicialScheme.transitionLevelNatTrans`: the triangle over `(a, W)`
commutes because both of its sides lie over `φ`, and an arrow of the total Zariski site is
determined by the simplex map it lies over. -/
public def sliceTransitionLevelNatTrans :
    Over.post (X := W) (Opens.map (X.map φ).base) ⋙ sliceComponentFunctorAt X W φ ⟶
      sliceComponentFunctor X a W where
  app V := Over.homMk (SimplicialSheafSystem.transitionHom (X := zariskiSpace X) φ V.left)
    (by
      apply SimplicialOpen.Hom.ext
      change (SimplicialOpen.Hom.base
          (SimplicialSheafSystem.transitionHom (X := zariskiSpace X) φ V.left)) ≫ 𝟙 _ =
        𝟙 _ ≫ (SimplicialOpen.Hom.base
          (SimplicialSheafSystem.transitionHom (X := zariskiSpace X) φ W))
      simp
      rfl)
  naturality _ _ _ := by
    apply Over.OverMorphism.ext
    apply SimplicialOpen.Hom.ext
    change (𝟙 _ : b ⟶ b) ≫ φ = φ ≫ (𝟙 _ : a ⟶ a)
    simp

end AlgebraicGeometry.SimplicialScheme

end
