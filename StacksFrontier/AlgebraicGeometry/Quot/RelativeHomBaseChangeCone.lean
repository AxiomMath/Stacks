module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomConeChange

/-!
# The relative Hom functor of a pullback datum, moved from the base to the source

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `P` a coherent pullback pseudofunctor
datum on the algebraic spaces (the inverse image of modules of Stacks 03LU, or the derived
pullback).  For two objects `M`, `N` over `Y`, the relative Hom functor over the test schemes
`g : T ⟶ Y` sends `T` to `Hom(g^*M, g^*N)`; pulling a morphism back along the projection
`f_T : X_T ⟶ T` of the base change `X_T = X ×_Y T` gives a morphism
`f_T^*g^*M ⟶ f_T^*g^*N`, that is, by the comparisons of the datum, a morphism
`h_T^*(f^*M) ⟶ h_T^*(f^*N)` for the projection `h_T : X_T ⟶ X`.  This file records that
operation as a morphism of relative Hom functors on the test schemes over `Y`, natural by
construction.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeProjectionCone`: the projections `X_T ⟶ X`, as a cone of test
  objects over `X` indexed by the test schemes over `Y`.
* `AlgebraicGeometry.Space.relHomBaseChange`: **pullback along the projections `X_T ⟶ T`**, as a
  morphism from the relative Hom functor over the test schemes to the relative Hom functor over
  the base changes.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The base changes `X_T` of `f` along the test schemes over `Y`, as a functor to the algebraic
spaces. -/
abbrev baseChangeSpaces : SchemesOver Y ⥤ AlgebraicSpaces B S hS :=
  baseChangeOver f ⋙ Over.forget X

/-- **The projections `X_T ⟶ X`, as a cone of test objects over `X`.** -/
def baseChangeProjectionCone : PullbackData.ConeTo (baseChangeSpaces f) X where
  leg T := baseChangeProjection f T
  w g := baseChangeMap_comp_projection f g

/-- The composites `X_T ⟶ X ⟶ Y`, as a cone of test objects over `Y`. -/
def baseChangeProjectionConeOverBase : PullbackData.ConeTo (baseChangeSpaces f) Y where
  leg T := baseChangeProjection f T ≫ f
  w g := by
    change baseChangeMap f g ≫ baseChangeProjection f _ ≫ f = baseChangeProjection f _ ≫ f
    rw [baseChangeMap_comp_projection_assoc]

/-- The projections `X_T ⟶ T` to the test schemes, as a natural transformation. -/
def baseChangeSpacesInclusion :
    baseChangeSpaces f ⟶ CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y ⋙
      schemeSpaceFunctor B S hS where
  app T := baseChangeInclusion f T
  naturality _ _ g := baseChangeMap_comp_inclusion f g

/-- The projection `X_T ⟶ T` followed by the structure morphism of `T` is the projection
`X_T ⟶ X` followed by `f`. -/
theorem baseChangeInclusion_comp_hom (T : SchemesOver Y) :
    baseChangeInclusion f T ≫ T.hom = baseChangeProjection f T ≫ f :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f ((schemesOverToOver Y).obj T).hom).w.symm

variable {D : AlgebraicSpaces B S hS → Type*} [∀ a, Category* (D a)]
  (P : PullbackData (AlgebraicSpaces B S hS) D)

/-- **Pullback along the projections `f_T : X_T ⟶ T`.**  A morphism `α : g^*M ⟶ g^*N` over a
test scheme `g : T ⟶ Y` goes to `f_T^*α`, read through the comparisons of the datum as a
morphism `h_T^*(f^*M) ⟶ h_T^*(f^*N)` over the projection `h_T : X_T ⟶ X`.  This is natural in
the test scheme. -/
def relHomBaseChange (hP : P.IsCoherent) (M N : D Y) :
    P.relHomFunctor hP (schemesOverCone Y) M N ⟶
      P.relHomFunctor hP (baseChangeProjectionCone f) ((P.pull f).obj M) ((P.pull f).obj N) :=
  P.relHomConeMap hP (schemesOverCone Y) (baseChangeProjectionConeOverBase f)
      (baseChangeSpacesInclusion f) (baseChangeInclusion_comp_hom f) M N ≫
    (P.relHomPrecompIso hP (baseChangeProjectionConeOverBase f) (𝟭 _) f (baseChangeProjectionCone f)
      (fun _ => rfl) M N).inv

/-- The component of `AlgebraicGeometry.Space.relHomBaseChange`. -/
theorem relHomBaseChange_app (hP : P.IsCoherent) (M N : D Y) (T : SchemesOver Y)
    (α : P.relHomObj (schemesOverCone Y) M N T) :
    (relHomBaseChange f P hP M N).app (Opposite.op T) α =
      Functor.transportHom (P.triangle (rfl : baseChangeProjection f T ≫ f = _)).symm
        (Functor.conjHom (P.triangle (baseChangeInclusion_comp_hom f T)) α) :=
  rfl

end AlgebraicGeometry.Space

end
