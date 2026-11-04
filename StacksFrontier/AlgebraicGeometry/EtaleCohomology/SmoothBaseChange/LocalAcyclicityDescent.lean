module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.BaseChangeTransfer

/-!
# Local acyclicity descends along a base change with the same strict henselizations

Let
```
X' --g'--> X
|f'        |f
S' --g---> S
```
be a cartesian square of schemes and `x'` a geometric point of `X'` at which the square of étale
local rings is a pushout. Stacks 0GJS transfers local acyclicity of `f` at the image `x` of `x'`
to local acyclicity of `f'` at `x'`. When moreover the induced morphism of strict henselizations
`Spec 𝒪^sh_{S',s'} ⟶ Spec 𝒪^sh_{S,s}` is an isomorphism, every geometric point of the strict
henselization of `S` comes from one of `S'`, and the transfer runs backwards: local acyclicity of
`f'` at `x'` gives local acyclicity of `f` at `x`. The proof of Proposition 0GJQ uses this for the
base change of `f` to the strict henselization of `S` at `f(x)`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isLocallyAcyclicAt_of_isPushout_of_isIso`

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (hS' : B.Contains S') (hX' : B.Contains X') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) (K : smallEtaleDerivedCategory X)
  {x' : GeometricPoint X'}

/-- The vanishing-cycles fibre map of `f` at the image of a geometric point of the strict
henselization of `S'` is an isomorphism when `f'` is locally acyclic at `x'`. -/
private theorem isIso_vanishingCyclesFibreMap_map_of_isPushout
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')))
    (h : IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x')
    (t' : GeometricPoint (strictHenselization B S' hS' (x'.map f'))) :
    IsIso ((vanishingCyclesFibreMap B hX hS f (x'.map g')
      (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x'))).app K) := by
  have key := NatTrans.congr_app (vanishingCyclesMap_pullback B hX hX' g' x' _ _ _
    (vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap
      B hX hS hS' hX' sq t' hpush)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at key
  have hD : IsIso ((vanishingCyclesMap B X' hX' x'
      (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t')).app
        ((smallEtaleDerivedPullbackAb g').obj K)) := h t'
  have hE := Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction
    (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom
  rw [vanishingCyclesFibreMap_eq]
  have hE' : IsIso ((smallEtaleDerivedGlobalSectionsRestriction
      (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom).app
        ((smallEtaleDerivedPullbackAb
          (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
            (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')) ≫
              strictHenselizationToBase B X hX (x'.map g'))).obj K)) :=
    NatIso.isIso_app_of_isIso _ _
  refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ ?_ ?_ key.symm
  · exact @IsIso.comp_isIso _ _ _ _ _ _ _ hE' (Functor.map_isIso _ _)
  · infer_instance

/-- **Local acyclicity descends along a cartesian square with a pushout of étale local rings and
an isomorphism of strict henselizations of the bases.** The identity of
`AlgebraicGeometry.vanishingCyclesMap_pullback` used for Stacks 0GJS compares the canonical maps
of Tag 0GJN for `f'` at `(x', t')` and for `f` at `(x, t)`, `t` the image of `t'`, up to
isomorphisms; every `t` is such an image when the strict henselizations of the bases agree. -/
theorem isLocallyAcyclicAt_of_isPushout_of_isIso
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')))
    [IsIso (baseChangeStrictHenselizationMap B hS hS' sq x')]
    (h : IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x') :
    IsLocallyAcyclicAt B hX hS f K (x'.map g') := by
  intro t
  let φ := baseChangeStrictHenselizationMap B hS hS' sq x'
  let t' : GeometricPoint (strictHenselization B S' hS' (x'.map f')) := ⟨_, t.hom ≫ inv φ⟩
  have ht : t'.map φ = t := by
    cases t
    simp only [GeometricPoint.map, t', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← ht]
  exact isIso_vanishingCyclesFibreMap_map_of_isPushout B hX hS hS' hX' sq K hpush h t'

end Stacks.EtaleCohomology.SmoothBaseChange

end
