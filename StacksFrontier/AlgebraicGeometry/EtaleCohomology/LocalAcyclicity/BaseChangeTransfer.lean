module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedStalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesStalkSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local acyclicity at a geometric point under base change

Let

```
X' --g'--> X
|f'        |f
S' --g---> S
```

be a cartesian diagram of schemes, let `K` be an object of `D(X_étale)` and let `x'` be a
geometric point of `X'` with image `x` in `X`. If `f` is locally acyclic at `x` relative to `K`,
then `f'` is locally acyclic at `x'` relative to `(g')⁻¹K` in each of the following cases: `g`
integral; `g` locally of finite type and locally quasi-finite; `S'` the limit of a cofiltered
inverse system of schemes with affine transition morphisms, each locally of finite type and
locally quasi-finite over `S` compatibly with the transitions.

## Main results

* `AlgebraicGeometry.isLocallyAcyclicAt_of_isPushout`: local acyclicity at a geometric point
  transfers along a cartesian square whose square of étale local rings at that point is a
  pushout.
* `AlgebraicGeometry.isLocallyAcyclicAt_of_isIntegralHom`: the case of `g` integral.
* `AlgebraicGeometry.isLocallyAcyclicAt_of_locallyQuasiFinite`: the case of `g` locally of finite
  type and locally quasi-finite.
* `AlgebraicGeometry.isLocallyAcyclicAt_of_limit`: the case of `S'` a cofiltered limit of schemes
  locally quasi-finite over `S` with affine transition morphisms.

## References

* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (hS' : B.Contains S') (hX' : B.Contains X') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) (K : smallEtaleDerivedCategory X)
  {x' : GeometricPoint X'}

/-- For a cartesian square of schemes whose square of étale local rings at a geometric point `x'`
of the fibre product is a pushout, local acyclicity of `f` at the image `x` of `x'` relative to an
object `K` of `D(X_étale)` implies local acyclicity of `f'` at `x'` relative to `(g')⁻¹K`. -/
public theorem isLocallyAcyclicAt_of_isPushout
    (hpush : IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')))
    (h : IsLocallyAcyclicAt B hX hS f K (x'.map g')) :
    IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x' := by
  intro t'
  have key := NatTrans.congr_app (vanishingCyclesMap_pullback B hX hX' g' x' _ _ _
    (vanishingCyclesFibreToStrictHenselization_comp_strictHenselizationSquareMap
      B hX hS hS' hX' sq t' hpush)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at key
  rw [vanishingCyclesFibreMap_eq]
  have hD : IsIso ((vanishingCyclesMap B X hX (x'.map g')
      (vanishingCyclesFibreToStrictHenselization B hX hS f (x'.map g')
        (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x')))).app K) :=
    h (t'.map (baseChangeStrictHenselizationMap B hS hS' sq x'))
  have hE := Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction
    (vanishingCyclesFibreBaseChangeIso B hX hS hS' hX' sq t' hpush).hom
  have main : IsIso ((vanishingCyclesMap B X' hX' x'
      (vanishingCyclesFibreToStrictHenselization B hX' hS' f' x' t')).app
      ((smallEtaleDerivedPullbackAb g').obj K)) :=
    IsIso.of_isIso_fac_right ((IsIso.inv_comp_eq _).mpr key.symm).symm
  exact main

include sq in
/-- For a cartesian square of schemes with `g` integral, an
object `K` of `D(X_étale)` and a geometric point `x'` of the fibre product with image `x` in `X`,
local acyclicity of `f` at `x` relative to `K` implies local acyclicity of `f'` at `x'` relative
to `(g')⁻¹K`. -/
@[stacks 0GJS "integral base change"]
public theorem isLocallyAcyclicAt_of_isIntegralHom [IsIntegralHom g]
    (h : IsLocallyAcyclicAt B hX hS f K (x'.map g')) :
    IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x' :=
  isLocallyAcyclicAt_of_isPushout B hX hS hS' hX' sq K
    (isPushout_etaleLocalRingHom_of_isIntegralHom B hX hS hS' hX' sq x') h

include sq in
/-- For a cartesian square of schemes with `g` locally of finite type and locally quasi-finite, an
object `K` of `D(X_étale)` and a geometric point `x'` of the fibre product with image `x` in `X`,
local acyclicity of `f` at `x` relative to `K` implies local acyclicity of `f'` at `x'` relative
to `(g')⁻¹K`. -/
@[stacks 0GJS "locally quasi-finite base change", sga "4½ Arcata 5.1.4" "more general"]
public theorem isLocallyAcyclicAt_of_locallyQuasiFinite [LocallyOfFiniteType g]
    [LocallyQuasiFinite g] (h : IsLocallyAcyclicAt B hX hS f K (x'.map g')) :
    IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x' :=
  isLocallyAcyclicAt_of_isPushout B hX hS hS' hX' sq K
    (isPushout_etaleLocalRingHom_of_locallyQuasiFinite B hX hS hS' hX' sq x') h

end BaseChange

section BaseChangeLimit

variable (B : BigEtaleSite.{u}) {X S X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)] {c : Cone D} (hc : IsLimit c)
  (hS' : B.Contains c.pt) (hX' : B.Contains X') {f : X ⟶ S} {g : c.pt ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ c.pt} (sq : IsPullback g' f' f g) (K : smallEtaleDerivedCategory X)
  {x' : GeometricPoint X'}

include sq hc in
/-- Let `{ Dᵢ }` be an inverse system of
schemes indexed by a cofiltered category, with affine transition morphisms, whose stages are
locally of finite type and locally quasi-finite over `S` compatibly with the transition
morphisms, let `S' = lim Dᵢ`, and let

```
X' --g'--> X
|f'        |f
S' --g---> S
```

be a cartesian square whose `g` is induced by the morphisms from the stages. For an object `K` of
`D(X_étale)` and a geometric point `x'` of `X'` with image `x` in `X`, local acyclicity of `f` at
`x` relative to `K` implies local acyclicity of `f'` at `x'` relative to `(g')⁻¹K`. -/
@[stacks 0GJS "directed inverse limit base change", sga "4½ Arcata 5.1.4" "more general"]
public theorem isLocallyAcyclicAt_of_limit (p : ∀ i : I, D.obj i ⟶ S)
    (hp : ∀ i : I, c.π.app i ≫ p i = g) (hcompat : ∀ {i j : I} (a : i ⟶ j), D.map a ≫ p j = p i)
    [∀ i : I, LocallyOfFiniteType (p i)] [∀ i : I, LocallyQuasiFinite (p i)]
    (h : IsLocallyAcyclicAt B hX hS f K (x'.map g')) :
    IsLocallyAcyclicAt B hX' hS' f' ((smallEtaleDerivedPullbackAb g').obj K) x' :=
  isLocallyAcyclicAt_of_isPushout B hX hS hS' hX' sq K
    (isPushout_etaleLocalRingHom_of_limit B hX hS hc hS' hX' sq p hp hcompat x') h

end BaseChangeLimit

end AlgebraicGeometry

end
