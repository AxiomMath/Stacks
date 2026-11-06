module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.HenselianPairRepresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeSmallEtale

/-!
# Stalks of a proper direct image are sections over the geometric fibre

Let `S` be a scheme, let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let
`x̄ : Spec(k) ⟶ X` be a geometric point. The geometric fibre is the algebraic space
`Y_x̄ = Y ×_{X, x̄} Spec(k)` with projection `p : Y_x̄ ⟶ Y`, and for a sheaf `ℱ` on `Y_étale` one
writes `ℱ_x̄ = p⁻¹ ℱ`. The canonical map

`(f_* ℱ)_x̄ ⟶ Γ(Y_x̄, ℱ_x̄)`

is the composite of the identification of a stalk with global sections of the pullback to the
geometric point (Stacks 04K3), global sections over `Spec(k)` of the base-change map
`x̄⁻¹ f_* ℱ ⟶ f'_* p⁻¹ ℱ` of the cartesian square of the fibre (`f' : Y_x̄ ⟶ Spec(k)` the
second projection), and the identification of global sections of a direct image with global
sections upstairs. When `f` is proper the base-change map is invertible by proper base change,
Stacks 0DG0, so the canonical map is bijective. This is Stacks 0DG1.

## Main definitions

* `AlgebraicGeometry.Space.geometricPointMorphism`: a geometric point as a morphism of
  algebraic spaces out of the space represented by its field spectrum.
* `AlgebraicGeometry.Space.geometricFibreSectionsMap`: the canonical map
  `(f_* ℱ)_x̄ ⟶ Γ(Y_x̄, ℱ_x̄)`, natural in the sheaf `ℱ` on the small étale site of `Y`.

## Main results

* `AlgebraicGeometry.Space.bijective_geometricFibreSectionsMap_of_isProper`:
  **[Stacks, Tag 0DG1]**.

## References

* [Stacks Project, Tag 0DG1](https://stacks.math.columbia.edu/tag/0DG1)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 04K3](https://stacks.math.columbia.edu/tag/04K3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- A geometric point `x̄ : Spec(k) ⟶ X` of an algebraic space, as a morphism of algebraic spaces
out of the space represented by its field spectrum. This is the morphism along which Stacks 04K3
(`AlgebraicGeometry.Space.smallEtaleStalkIsoPullbackGlobalSections`) pulls back. -/
abbrev geometricPointMorphism (x : GeometricPoint B S hS X.obj) :
    (⟨yoneda.obj x.val.siteObject, isAlgebraicSpace_yoneda B S hS x.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ X :=
  ObjectProperty.homMk (fieldMorphism B S hS X.obj x.val)

set_option synthInstance.maxHeartbeats 200000 in
/-- **The canonical map of Stacks 0DG1.** For a morphism `f : Y ⟶ X` of algebraic spaces over
`S` and a geometric point `x̄` of `X`, with geometric fibre `Y_x̄ = Y ×_{X, x̄} Spec(k)` and
projection `p : Y_x̄ ⟶ Y`, the map

`(f_* ℱ)_x̄ ⟶ Γ(Y_x̄, p⁻¹ ℱ)`,

natural in the sheaf of sets `ℱ` on the small étale site of `Y`. It is the stalk at `x̄`
identified with global sections of the pullback to `Spec(k)` (Stacks 04K3), followed by global
sections over `Spec(k)` of the base-change map `x̄⁻¹ f_* ℱ ⟶ f'_* p⁻¹ ℱ` of the cartesian square
of the fibre (`AlgebraicGeometry.Space.properBaseChangeMap`) and by the identification of global
sections of the direct image along `f' : Y_x̄ ⟶ Spec(k)` with global sections over `Y_x̄`. -/
def geometricFibreSectionsMap (f : Y ⟶ X) (x : GeometricPoint B S hS X.obj) :
    (smallToposMorphism B S hS f).pushforward ⋙
        sheafToPresheaf (SmallEtale.topology B S hS X.obj) (Type (u + 1)) ⋙
          stalkSetFunctor x ⟶
      (smallToposMorphism B S hS
          (pullback.fst f (geometricPointMorphism B S hS x))).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B S hS (pullback f (geometricPointMorphism B S hS x)).obj)
          (Type (u + 1)) :=
  (Functor.isoWhiskerLeft _ (smallEtaleStalkIsoPullbackGlobalSections B S hS x)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (properBaseChangeMap B S hS f (geometricPointMorphism B S hS x)
        (pullback.snd f (geometricPointMorphism B S hS x))
        (pullback.fst f (geometricPointMorphism B S hS x))
        (IsPullback.of_hasPullback f (geometricPointMorphism B S hS x)))
      (Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj x.val.siteObject)) (Type (u + 1))) ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft _
      (haveI := (smallToposMorphism B S hS
        (pullback.snd f (geometricPointMorphism B S hS x))).preservesFiniteLimits
      Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
        (smallToposMorphism B S hS (pullback.snd f (geometricPointMorphism B S hS x))).adj)).hom

/-- The canonical map of Stacks 0DG1 is invertible as soon as the base-change map of the
cartesian square of the geometric fibre is: its other factors are isomorphisms by
construction. -/
theorem isIso_geometricFibreSectionsMap_of_isIso (f : Y ⟶ X) (x : GeometricPoint B S hS X.obj)
    [IsIso (properBaseChangeMap B S hS f (geometricPointMorphism B S hS x)
      (pullback.snd f (geometricPointMorphism B S hS x))
      (pullback.fst f (geometricPointMorphism B S hS x))
      (IsPullback.of_hasPullback f (geometricPointMorphism B S hS x)))] :
    IsIso (geometricFibreSectionsMap B S hS f x) := by
  dsimp only [geometricFibreSectionsMap]
  infer_instance

/-- **[Stacks, Tag 0DG1].** Let `S` be a scheme, let `f : Y ⟶ X` be a proper morphism of
algebraic spaces over `S` and let `x̄` be a geometric point of `X`, with geometric fibre
`Y_x̄ = Y ×_{X, x̄} Spec(k)` and projection `p : Y_x̄ ⟶ Y`. For every sheaf of sets `ℱ` on
`Y_étale` the canonical map `(f_* ℱ)_x̄ ⟶ Γ(Y_x̄, ℱ_x̄)`, `ℱ_x̄ = p⁻¹ ℱ`, is bijective.

The proof is the source's: the base-change map of the geometric fibre square is invertible by
proper base change, Stacks 0DG0
(`AlgebraicGeometry.Space.isIso_properBaseChangeMap_of_isProper`). -/
@[stacks 0DG1]
theorem bijective_geometricFibreSectionsMap_of_isProper (f : Y ⟶ X)
    (hf : IsProper B S hS f.hom) (x : GeometricPoint B S hS X.obj)
    (ℱ : Sheaf (SmallEtale.topology B S hS Y.obj) (Type (u + 1))) :
    Function.Bijective ((geometricFibreSectionsMap B S hS f x).app ℱ) := by
  have := isIso_properBaseChangeMap_of_isProper B S hS f hf (geometricPointMorphism B S hS x)
    (pullback.snd f (geometricPointMorphism B S hS x))
    (pullback.fst f (geometricPointMorphism B S hS x))
    (IsPullback.of_hasPullback f (geometricPointMorphism B S hS x))
  have := isIso_geometricFibreSectionsMap_of_isIso B S hS f x
  exact (isIso_iff_bijective _).mp inferInstance

end AlgebraicGeometry.Space

end
