module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.TopFormsNormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups

/-!
# The reflexive hull of a top exterior power commutes with pullback along a point blowup

Let `W` be an integral regular Noetherian scheme of dimension two, let `w ∈ W` be a closed point
and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`. Let `Ω` be a coherent
`𝒪_W`-module of generic rank `r`. This file compares

`(⋀^r b^*Ω)^{∨∨}` — the reflexive hull of the top exterior power of the pullback — and
`b^*((⋀^r Ω)^{∨∨})` — the pullback of the determinant line bundle of `Ω`.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `reflexiveHullExteriorPowerPullbackIso`: `(⋀^r f^*Ω)^{∨∨} ≅ f^*((⋀^r Ω)^{∨∨})` for an
  arbitrary morphism `f` from an integral locally Noetherian scheme into an integral regular
  scheme of dimension at most two, for `Ω` coherent of generic rank `r` whose top exterior power
  is reflexive.
* `pullbackHullForms_iso`: the same at the blowing up of an integral regular Noetherian surface
  in a closed point, stated with `Stacks.BlowupTwistUnit.hullForms`.
* `pullbackHullForms_iso_of_isFiniteLocallyFree`: the same with the reflexivity hypothesis
  replaced by finite local freeness of `⋀^r Ω_{W/S₀}`, under which it holds automatically.

## Implementation notes

The reflexivity hypothesis cannot be dropped. Write `M = ⋀^r Ω` and `L = M^{∨∨}`, and let
`c : M ⟶ L` be the canonical map. The identity asserted above is *false* in general: `c` is an
isomorphism away from the locus where `M` fails to be reflexive, which on a two-dimensional scheme
is a finite set of closed points, and if the blown-up point `w` is one of them then `b^*c` fails
to be an isomorphism along the whole exceptional divisor — a divisor, not a codimension-two locus,
so the hull does not forget it. Concretely, with `M_w = 𝔪 ⊆ 𝒪_{W,w} = L_w` the image of `b^*M`
inside the invertible module `b^*L` is `𝔪 · 𝒪_{W'}`, which is `𝒪_{W'}(-E)` and not `𝒪_{W'}`, so
the two sides differ by the exceptional divisor. Since the hull is invertible by
[Stacks, Tag 0B3T], the hypothesis that `⋀^r Ω` is reflexive is equivalent to `⋀^r Ω` being
invertible, and is exactly the condition that makes `c` an isomorphism.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The pullback of the determinant line bundle is reflexive -/

/-- The pullback of the determinant line bundle of a coherent module of generic rank `r` on an
integral regular scheme of dimension at most two is reflexive, along an arbitrary morphism from an
integral locally Noetherian scheme. -/
theorem isReflexive_pullback_reflexiveHull_exteriorPower {X' X : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral X'] [IsLocallyNoetherian X']
    (hX : AlgebraicGeometry.IsRegular X) (hXdim : topologicalKrullDim X ≤ 2)
    (Ω : X.Modules) [Ω.IsCoherent] (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Ω.over U) r] :
    IsReflexive ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ)))) := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))) :=
    AlgebraicGeometry.isInvertible_reflexiveHull_exteriorPower_of_genericRank X hX hXdim Ω r U hU
  have : Stacks.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj
        (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ)))) :=
    Stacks.Modules.isInvertible_pullback f
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ)))
  exact AlgebraicGeometry.isReflexive_of_isInvertible X' _

/-! ### The comparison -/

/-- Let `X` be an integral regular scheme of dimension at most two, let `Ω` be a coherent
`𝒪_X`-module which is finite locally free of rank `r` on a nonempty open (its generic rank is `r`),
and assume `⋀^r Ω` is reflexive. Then for every morphism `f : X' ⟶ X` from an integral locally
Noetherian scheme the reflexive hull of the top exterior power of `f^*Ω` is the pullback of the
determinant line bundle of `Ω`: `(⋀^r f^*Ω)^{∨∨} ≅ f^*((⋀^r Ω)^{∨∨})`. -/
def reflexiveHullExteriorPowerPullbackIso {X' X : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral X'] [IsLocallyNoetherian X']
    (hX : AlgebraicGeometry.IsRegular X) (hXdim : topologicalKrullDim X ≤ 2)
    (Ω : X.Modules) [Ω.IsCoherent] (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Ω.over U) r]
    (hrefl : IsReflexive (Scheme.Modules.exteriorPower Ω (r : ℤ))) :
    reflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback f).obj Ω) (r : ℤ)) ≅
      (Scheme.Modules.pullback f).obj
        (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))) :=
  haveI : IsIso (toReflexiveHull ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))))).1 :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp
      (isReflexive_pullback_reflexiveHull_exteriorPower f hX hXdim Ω r U hU)
  haveI : IsIso (toReflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))).1 :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp hrefl
  (reflexiveHullFunctor X').mapIso
      ((Scheme.Modules.exteriorPowerPullbackIso f Ω (r : ℤ)).symm ≪≫
        (Scheme.Modules.pullback f).mapIso
          (asIso (toReflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))).1)) ≪≫
    (asIso (toReflexiveHull ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))))).1).symm

/-! ### At a blowup in a closed point, in the spelling of the induction -/

/-- `(⋀^r b^*Ω_{W/S₀})^{∨∨} ≅ b^*((Ω^r_{W/S₀})^{∨∨})` at the blowing up `b` of an integral regular
Noetherian surface `W` in a closed point `w`, the target written as the pullback of
`Stacks.BlowupTwistUnit.hullForms`, when `⋀^r Ω_{W/S₀}` is reflexive. -/
def pullbackHullForms_iso {S₀ S W : Scheme.{u}} (p : S ⟶ S₀) (h : W ⟶ S)
    [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W)) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (U : W.Opens) (hU : ∃ x : W, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over U) r]
    (hrefl : IsReflexive (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ))) :
    reflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ)) ≅
      (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (hullForms p (r : ℤ) h) :=
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    AlgebraicGeometry.isIntegral_blowUp _
      (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw)
  haveI : IsNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) := inferInstance
  reflexiveHullExteriorPowerPullbackIso (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
    hreg hdim.le (Scheme.Hom.relativeDifferentials (h ≫ p)) r U hU hrefl

/-- `Stacks.BlowupTwistUnit.pullbackHullForms_iso` with the reflexivity hypothesis replaced by
finite local freeness of `⋀^r Ω_{W/S₀}`. -/
def pullbackHullForms_iso_of_isFiniteLocallyFree {S₀ S W : Scheme.{u}} (p : S ⟶ S₀) (h : W ⟶ S)
    [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W)) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (U : W.Opens) (hU : ∃ x : W, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over U) r]
    (hfree : Scheme.Modules.IsFiniteLocallyFree
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ))) :
    reflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ)) ≅
      (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (hullForms p (r : ℤ) h) :=
  pullbackHullForms_iso p h hreg hdim w hw r U hU
    (Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree' _ hfree)

end Stacks.BlowupTwistUnit

end
