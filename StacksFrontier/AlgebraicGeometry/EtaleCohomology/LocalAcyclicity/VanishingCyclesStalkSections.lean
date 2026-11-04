module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibreBaseChange

/-!
# The map out of an étale stalk at the varieties of vanishing cycles of a base change

Let

```
X' --g'--> X
|f'        |f
S' --g---> S
```

be a cartesian square of schemes, let `x'` be a geometric point of `X'` with image `x` in `X`,
let `t'` be a geometric point of `Spec 𝒪^sh_{S',f'(x')}`, and suppose the square of étale local
rings at `x'` is a pushout. The variety of vanishing cycles `F_{x',t'}` of `f'` is then the
variety of vanishing cycles `F_{x,t}` of `f` at the image `t` of `t'`, by
`AlgebraicGeometry.vanishingCyclesFibreBaseChangeIso`, and that identification lies over the
induced morphism of strict henselizations. Consequently the map of Tag 0GJN on abelian étale
sheaves for `f'` at `(x', t')`, read through the identification of the stalk of an inverse image
with the stalk at the image point, is the map for `f` at `(x, t)` followed by restriction of
global sections along the identification of the two varieties of vanishing cycles.

## Main results

* `AlgebraicGeometry.vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap`:
  the projection of `F_{x',t'}` to `Spec 𝒪^sh_{X',x'}`, followed by the induced morphism of
  strict henselizations, is the identification of the two varieties of vanishing cycles followed
  by the projection of `F_{x,t}`.
* `AlgebraicGeometry.etaleStalkToSectionsAb_vanishingCyclesFibre`: the map of Tag 0GJN on
  abelian étale sheaves at `(x', t')` is the one at `(x, t)` followed by restriction of global
  sections along that identification.

## References

* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section BaseChange

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (hS' : B.Contains S') (hX' : B.Contains X') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) {x' : GeometricPoint X'}
  (t' : GeometricPoint (strictHenselization B S' hS' (x'.map f')))
  (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
    (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
    (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
    (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')))

/-- The projection of `F_{x',t'}` to `Spec 𝒪^sh_{X',x'}`, followed by the morphism of strict
henselizations induced by `g'`, is the identification of the two varieties of vanishing cycles
followed by the projection of `F_{x,t}` to `Spec 𝒪^sh_{X,x}`. -/
public theorem vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap :
    vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t' ≫
        strictHenselizationSquareMap B hX' hX g' x' =
      (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom ≫
        vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
          (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) :=
  (vanishingCyclesFibreBaseChangeIso_hom_toStrictHenselization B hX hS hS' hX' sq t' hpush).symm

/-- For a cartesian square of schemes whose square of étale local rings at a geometric point `x'`
of the fibre product is a pushout, and for a geometric point `t'` of
`Spec 𝒪^sh_{S',f'(x')}`, the map

`(g'⁻¹F)_{x'} ⟶ Γ(F_{x',t'}, (g'⁻¹F)|_{F_{x',t'}})`

on abelian sheaves of the small étale site of `X`, read through the identification of the stalk of
an inverse image with the stalk at the image point `x`, is the map

`F_x ⟶ Γ(F_{x,t}, F|_{F_{x,t}})`

at the image `t` of `t'`, followed by restriction of global sections along the identification
`F_{x',t'} ≅ F_{x,t}` of the two varieties of vanishing cycles. Both sides are read in the global
sections on `F_{x',t'}` of the inverse image of `F` along the structure morphism of `F_{x',t'}`
over `X`. -/
public theorem etaleStalkToSectionsAb_vanishingCyclesFibre :
    (smallEtaleStalkPullbackAbIso g' x'.hom).inv ≫
        Functor.whiskerLeft (smallEtalePullbackAb g')
            (etaleStalkToSectionsAb B X' hX' x'
              (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t')) ≫
          (Functor.associator (smallEtalePullbackAb g')
              (smallEtalePullbackAb
                (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t' ≫
                  strictHenselizationToBase B X' hX' x'))
              (Sheaf.Γ (smallEtaleTopology (vanishingCyclesFibre B hX' hS' f' x' t'))
                Ab.{u + 1})).inv ≫
            Functor.whiskerRight
              (smallEtalePullbackAbCompIso
                (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t' ≫
                  strictHenselizationToBase B X' hX' x') g').hom
              (Sheaf.Γ (smallEtaleTopology (vanishingCyclesFibre B hX' hS' f' x' t'))
                Ab.{u + 1}) =
      etaleStalkToSectionsAb B X hX (x'.map g')
          (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
            (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x'))) ≫
        Functor.whiskerLeft
            (smallEtalePullbackAb
              (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
                  (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) ≫
                strictHenselizationToBase B X hX (x'.map g')))
            (smallEtaleGlobalSectionsRestrictionAb
              (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom) ≫
          (Functor.associator
              (smallEtalePullbackAb
                (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
                    (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) ≫
                  strictHenselizationToBase B X hX (x'.map g')))
              (smallEtalePullbackAb
                (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom)
              (Sheaf.Γ (smallEtaleTopology (vanishingCyclesFibre B hX' hS' f' x' t'))
                Ab.{u + 1})).inv ≫
            Functor.whiskerRight
              ((smallEtalePullbackAbCompIso
                  (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom
                  (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
                      (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) ≫
                    strictHenselizationToBase B X hX (x'.map g'))).hom ≫
                (eqToIso (congrArg
                  (fun m : vanishingCyclesFibre B hX' hS' f' x' t' ⟶ X =>
                    smallEtalePullbackAb m)
                  (comp_strictHenselizationToBase_of_comp B hX hX' g' x'
                    (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
                      (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')))
                    (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t')
                    (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom
                    (vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap
                      B hX hS hS' hX' sq t' hpush)))).hom)
              (Sheaf.Γ (smallEtaleTopology (vanishingCyclesFibre B hX' hS' f' x' t'))
                Ab.{u + 1}) :=
  etaleStalkToSectionsAb_pullback B hX hX' g' x'
    (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
      (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')))
    (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t')
    (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom
    (vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap
      B hX hS hS' hX' sq t' hpush)

end BaseChange

end AlgebraicGeometry

end
