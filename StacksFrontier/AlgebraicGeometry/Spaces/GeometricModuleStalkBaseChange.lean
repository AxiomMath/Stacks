module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackEtaleLocalRing
public import StacksFrontier.Homology.ExtendScalars.CompositionAcrossUniverses
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric stalk of a pullback of modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `x̄` be a geometric
point of `X` with image `f ∘ x̄`, and let `G` be an `𝒪_Y`-module.  The stalk at `x̄` of the
pullback `f^*G` of Stacks 03LU is the base change of the stalk of `G` at `f ∘ x̄` along the
canonical homomorphism `𝒪_{Y, f ∘ x̄} ⟶ 𝒪_{X, x̄}` of étale local rings of Stacks 04NG:

`(f^*G)_{x̄} ≅ 𝒪_{X, x̄} ⊗_{𝒪_{Y, f ∘ x̄}} G_{f ∘ x̄}`.

This is the base-change clause of Stacks 05VQ.

## Main definitions

* `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`: the base-change formula.

## Main results

* `AlgebraicGeometry.Space.pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap`: the
  comparison of the structure-sheaf stalks with the étale local rings turns the homomorphism of
  stalk rings along which Stacks 05V5 extends scalars into the homomorphism of étale local rings
  of Stacks 04NG.

## Implementation notes

The étale local ring of an algebraic space is a colimit over the étale neighbourhoods of the
geometric point and so lives one universe above the stalk of the structure sheaf at the
corresponding point of the site. The two-step base changes are therefore compared with the
object-level `ModuleCat.extendScalarsCompObjIso`, which works across universes, rather than the
isomorphism of functors `ModuleCat.extendScalarsComp`.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkPullback

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The comparisons of Stacks 05VQ carry the homomorphism of stalk rings of Stacks 05V5 to the
homomorphism of étale local rings of Stacks 04NG: the square

```
(𝒪_Y)_{f ∘ x̄} ---> (𝒪_X)_{x̄}
     |                  |
     v                  v
 𝒪_{Y, f ∘ x̄} ---> 𝒪_{X, x̄}
```

whose vertical maps are the comparisons of the structure-sheaf stalks with the étale local
rings, commutes. -/
theorem pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap :
    (pointStalkRingEquiv B S hS X x).toRingHom.comp
        (smallEtaleStalkPullbackRingMap B S hS f x) =
      (etaleLocalRingMap X.2 f.hom x).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom := by
  rw [← smallEtaleStalkPullbackEtaleLocalRingMap_eq]
  exact RingHom.ext fun z => congrArg (fun w => pointStalkRingEquiv B S hS X x
    (smallEtaleStalkPullbackRingMap B S hS f x w))
    ((pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).symm_apply_apply z).symm

variable (G : Modules.{u, u} B S hS Y.1 Y.2)

/-- The stalk at a geometric point `x̄` of the
pullback of an `𝒪_Y`-module `G` along a morphism `f : X ⟶ Y` of algebraic spaces is the base
change of the stalk of `G` at the image point `f ∘ x̄` along the canonical homomorphism
`𝒪_{Y, f ∘ x̄} ⟶ 𝒪_{X, x̄}` of étale local rings of Stacks 04NG:

`(f^*G)_{x̄} ≅ 𝒪_{X, x̄} ⊗_{𝒪_{Y, f ∘ x̄}} G_{f ∘ x̄}`. -/
@[stacks 05VQ "the base-change formula `(f^*G)_x̄ ≅ 𝒪_{X, x̄} ⊗_{𝒪_{Y, f ∘ x̄}} G_{f ∘ x̄}` for the
geometric stalk of a pullback of modules"]
def geometricModuleStalkPullbackIso :
    geometricModuleStalk B S hS X x ((modulePullback B S hS f).obj G) ≅
      (ModuleCat.extendScalars (etaleLocalRingMap X.2 f.hom x)).obj
        (geometricModuleStalk B S hS Y (geometricPointMap f.hom x) G) :=
  (ModuleCat.extendScalars (pointStalkRingEquiv B S hS X x).toRingHom).mapIso
      (Stacks.moduleStalkLargeIso (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O ((modulePullback B S hS f).obj G) ≪≫
          (stalkFunctorIso (smallEtaleRingedToposModulesHom B S hS f)
              (etaleSitePoint B S hS X.1 x X.2)
              (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
              (smallEtaleInverseImageFiberIso B S hS f x)).app G ≪≫
          (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f x)).mapIso
            (Stacks.moduleStalkLargeIso
              (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
              (smallEtaleRingedTopos B S hS Y).O G).symm) ≪≫
    ModuleCat.extendScalarsCompObjIso.{u, u, u + 1, u}
        (smallEtaleStalkPullbackRingMap B S hS f x)
        (pointStalkRingEquiv B S hS X x).toRingHom
        (Stacks.moduleStalkLarge
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O G) ≪≫
    eqToIso (congrArg (fun φ => (ModuleCat.extendScalars φ).obj
        (Stacks.moduleStalkLarge
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O G))
      (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f x)) ≪≫
    (ModuleCat.extendScalarsCompObjIso.{u, u + 1, u + 1, u}
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom
        (etaleLocalRingMap X.2 f.hom x)
        (Stacks.moduleStalkLarge
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O G)).symm

end AlgebraicGeometry.Space

end

end
