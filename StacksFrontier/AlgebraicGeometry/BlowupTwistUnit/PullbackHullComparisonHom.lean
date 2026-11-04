module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PullbackHullComparison

/-!
# The reflexive hull of a top exterior power maps to the pullback of the determinant, always

Let `X` be an integral regular scheme of dimension at most two, let `Ω` be a coherent
`𝒪_X`-module of generic rank `r` and let `f : X' ⟶ X` be a morphism from an integral locally
Noetherian scheme. Write `L = (⋀^r Ω)^{**}` for the determinant line bundle, invertible by
[Stacks, Tag 0B3T]. This file produces the canonical morphism

`(⋀^r f^*Ω)^{**} ⟶ f^*L`

with **no hypothesis on `⋀^r Ω`**.

`Stacks.BlowupTwistUnit.reflexiveHullExteriorPowerPullbackIso` produces an *isomorphism* between
the same two modules, but only under `IsReflexive (⋀^r Ω)`. That hypothesis cannot be discharged
at a stage of the induction of [Stacks, Tag 0B4T] past the first: with
`A = 𝔽_p[x, y]_{(x,y)}` and `A₀ = 𝔽_p[y]`, so that `Ω_{A/A₀} = A·dx` is free of rank one, the
chart `B = A[t]/(xt − y)` of the blowup of the closed point has `dy = t·dx + x·dt = 0` and hence
`Ω_{B/A₀} ≅ (x, t)B`, which at the chart origin is the maximal ideal `𝔪`, whose reflexive hull is
`B ≠ 𝔪`. So the hull of the top exterior power is not reflexive there, while the generic rank is
still one.

The two sides genuinely differ: the image of `f^*(⋀^r Ω)` inside the invertible module `f^*L` is
`f^{-1}(I)·f^*L` for `I` the image ideal of `⋀^r Ω ⟶ L`, so along a blowup the hull of the left
side is `f^*L` twisted *down* by the vanishing order of `I` at the centre. The morphism below is
the inclusion of that twisted-down module, and it is an isomorphism exactly when the order is
zero — which is what the reflexivity hypothesis of the isomorphism amounts to.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `reflexiveHullExteriorPowerPullbackHom`: **`(⋀^r f^*Ω)^{**} ⟶ f^*((⋀^r Ω)^{**})`**, for an
  arbitrary morphism `f` into an integral regular scheme of dimension at most two and `Ω`
  coherent of generic rank `r`. No hypothesis on `⋀^r Ω`.
* `pullbackHullForms_hom`: the same at the blowing up of an integral regular Noetherian surface
  in a closed point, with the target written as the pullback of
  `Stacks.BlowupTwistUnit.hullForms`, the spelling the induction of [Stacks, Tag 0B4T] consumes.

## Main results

* `toReflexiveHull_comp_reflexiveHullExteriorPowerPullbackHom`: the morphism restricts along the
  canonical map to the hull to the pullback of `⋀^r Ω ⟶ L` read through
  `⋀^r f^*Ω ≅ f^*(⋀^r Ω)`. This is the sense in which it is *the* comparison and not merely some
  morphism: it is determined by the universal property of the hull, and in particular it is
  nonzero whenever that pullback is.

## Implementation notes

**The route.** Two steps. The canonical map `⋀^r f^*Ω ≅ f^*(⋀^r Ω) ⟶ f^*L` is
`AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso` — the exterior-algebra clause of
[Stacks, Tag 01CI], unconditional — followed by `f^*` applied to `⋀^r Ω ⟶ (⋀^r Ω)^{**}`. Then
the universal property of the reflexive hull extends it across `⋀^r f^*Ω ⟶ (⋀^r f^*Ω)^{**}`,
because the target `f^*L` is reflexive: `L` is invertible by [Stacks, Tag 0B3T], invertibility is
preserved by pullback ([Stacks, Tag 0B8P]) and an invertible module on an integral locally
Noetherian scheme is reflexive. That reflexivity is
`Stacks.BlowupTwistUnit.isReflexive_pullback_reflexiveHull_exteriorPower`, which carries no
hypothesis on `⋀^r Ω` — the whole of the dropped hypothesis was used, in the isomorphism, to
invert `f^*(⋀^r Ω) ⟶ f^*L`, which is exactly the step omitted here.

**No `@[stacks]` attribute is placed.** The comparison is an input of the inductive step of
[Stacks, Tag 0B4T] and is not asserted by that tag or by any other; the source does not state
it.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The universal property of the reflexive hull at a reflexive target -/

/-- **The extension of a morphism across the canonical map to the reflexive hull restricts to
that morphism.** For `g : A ⟶ B` with `B` reflexive, the composite
`A^{**} ⟶ B^{**} ≅ B` obtained from the functoriality of the hull and the invertibility of
`B ⟶ B^{**}` is the unique morphism `A^{**} ⟶ B` restricting to `g` along `A ⟶ A^{**}`.

This is the universal property [Stacks, Tag 0AVU] gives the hull, read off from naturality of
the canonical map to the double dual (`toDoubleDual_naturality`). Uniqueness is not stated
separately: it is `cancel_epi` at the canonical map, which is an epimorphism whenever its target
is the hull of a module whose hull map is epi, and is not needed below. -/
theorem toReflexiveHull_comp_extendToReflexive {X : Scheme.{u}} {A B : X.Modules} (g : A ⟶ B)
    [IsIso (toReflexiveHull B).1] :
    (toReflexiveHull A).1 ≫ (reflexiveHullFunctor X).map g ≫
        (asIso (toReflexiveHull B).1).inv = g :=
  calc (toReflexiveHull A).1 ≫ (reflexiveHullFunctor X).map g ≫
          (asIso (toReflexiveHull B).1).inv
      = ((toReflexiveHull A).1 ≫ (reflexiveHullFunctor X).map g) ≫
          (asIso (toReflexiveHull B).1).inv := (Category.assoc _ _ _).symm
    _ = (g ≫ (toReflexiveHull B).1) ≫ (asIso (toReflexiveHull B).1).inv :=
        congrArg (· ≫ (asIso (toReflexiveHull B).1).inv) (toDoubleDual_naturality g).symm
    _ = g ≫ (toReflexiveHull B).1 ≫ (asIso (toReflexiveHull B).1).inv :=
        Category.assoc _ _ _
    _ = g ≫ 𝟙 B := congrArg (g ≫ ·) (IsIso.hom_inv_id (f := (toReflexiveHull B).1))
    _ = g := Category.comp_id g

/-! ### The comparison morphism -/

/-- The canonical map `⋀^r f^*Ω ⟶ f^*((⋀^r Ω)^{**})`: the identification of the top exterior
power of a pullback with the pullback of the top exterior power, followed by `f^*` of the
canonical map to the reflexive hull. -/
def exteriorPowerPullbackToPullbackHull {X' X : Scheme.{u}} (f : X' ⟶ X) (Ω : X.Modules)
    (r : ℕ) :
    Scheme.Modules.exteriorPower ((Scheme.Modules.pullback f).obj Ω) (r : ℤ) ⟶
      (Scheme.Modules.pullback f).obj
        (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))) :=
  (Scheme.Modules.exteriorPowerPullbackIso f Ω (r : ℤ)).inv ≫
    (Scheme.Modules.pullback f).map
      (toReflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))).1

/-- **`(⋀^r f^*Ω)^{**} ⟶ f^*((⋀^r Ω)^{**})`.** Let `X` be an integral regular scheme of
dimension at most two and let `Ω` be a coherent `𝒪_X`-module which is finite locally free of rank
`r` on a nonempty open — its generic rank is `r`. Then for every morphism `f : X' ⟶ X` from an
integral locally Noetherian scheme there is a canonical morphism from the reflexive hull of the
top exterior power of `f^*Ω` to the pullback of the determinant line bundle of `Ω`.

**There is no hypothesis on `⋀^r Ω`**, which is the point: the isomorphism
`Stacks.BlowupTwistUnit.reflexiveHullExteriorPowerPullbackIso` between the same two modules needs
`IsReflexive (⋀^r Ω)`, and that fails at every stage of the induction of [Stacks, Tag 0B4T] past
the first (see the module docstring). What survives unconditionally is this morphism, obtained
from the universal property of the hull: the target is reflexive, being the pullback of an
invertible module, so the canonical map
`Stacks.BlowupTwistUnit.exteriorPowerPullbackToPullbackHull` out of `⋀^r f^*Ω` extends across
`⋀^r f^*Ω ⟶ (⋀^r f^*Ω)^{**}` — uniquely, by
`Stacks.BlowupTwistUnit.toReflexiveHull_comp_reflexiveHullExteriorPowerPullbackHom`. -/
def reflexiveHullExteriorPowerPullbackHom {X' X : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral X'] [IsLocallyNoetherian X']
    (hX : AlgebraicGeometry.IsRegular X) (hXdim : topologicalKrullDim X ≤ 2)
    (Ω : X.Modules) [Ω.IsCoherent] (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Ω.over U) r] :
    reflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback f).obj Ω) (r : ℤ)) ⟶
      (Scheme.Modules.pullback f).obj
        (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))) :=
  haveI : IsIso (toReflexiveHull ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))))).1 :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp
      (isReflexive_pullback_reflexiveHull_exteriorPower f hX hXdim Ω r U hU)
  (reflexiveHullFunctor X').map (exteriorPowerPullbackToPullbackHull f Ω r) ≫
    (asIso (toReflexiveHull ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))))).1).inv

/-- **The comparison morphism restricts to the canonical map along `⋀^r f^*Ω ⟶ (⋀^r f^*Ω)^{**}`**:
it is the unique extension of `Stacks.BlowupTwistUnit.exteriorPowerPullbackToPullbackHull` across
the hull, by naturality of the canonical map to the double dual.

This is what makes `Stacks.BlowupTwistUnit.reflexiveHullExteriorPowerPullbackHom` *the*
comparison. In particular it is nonzero whenever
`Stacks.BlowupTwistUnit.exteriorPowerPullbackToPullbackHull` is, so it cannot be replaced by the
zero morphism. -/
theorem toReflexiveHull_comp_reflexiveHullExteriorPowerPullbackHom {X' X : Scheme.{u}}
    (f : X' ⟶ X)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral X'] [IsLocallyNoetherian X']
    (hX : AlgebraicGeometry.IsRegular X) (hXdim : topologicalKrullDim X ≤ 2)
    (Ω : X.Modules) [Ω.IsCoherent] (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Ω.over U) r] :
    (toReflexiveHull (Scheme.Modules.exteriorPower
          ((Scheme.Modules.pullback f).obj Ω) (r : ℤ))).1 ≫
        reflexiveHullExteriorPowerPullbackHom f hX hXdim Ω r U hU =
      exteriorPowerPullbackToPullbackHull f Ω r :=
  have : IsIso (toReflexiveHull ((Scheme.Modules.pullback f).obj
      (reflexiveHull (Scheme.Modules.exteriorPower Ω (r : ℤ))))).1 :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp
      (isReflexive_pullback_reflexiveHull_exteriorPower f hX hXdim Ω r U hU)
  toReflexiveHull_comp_extendToReflexive (exteriorPowerPullbackToPullbackHull f Ω r)

/-! ### At a blowup in a closed point, in the spelling of the induction -/

/-- **`(⋀^r b^*Ω_{W/S₀})^{**} ⟶ b^*((Ω^r_{W/S₀})^{**})` at the blowing up `b` of an integral
regular Noetherian surface `W` in a closed point `w`**, the target written as the pullback of
`Stacks.BlowupTwistUnit.hullForms`, which is the spelling the induction of [Stacks, Tag 0B4T]
consumes.

The integrality of the blowup is [Stacks, Tag 02ND] at the ideal sheaf of a reduced closed point
of an integral surface, which is nonzero
(`Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot`), and its Noetherianity is
`Stacks.ResolutionOfSurfaces.isNoetherian_blowUp`.

This is `Stacks.BlowupTwistUnit.pullbackHullForms_iso` with its reflexivity hypothesis dropped
and its conclusion weakened from an isomorphism to the underlying canonical morphism. The
hypothesis is false past the first stage of the induction and the isomorphism with it; the
morphism is unconditional. -/
def pullbackHullForms_hom {S₀ S W : Scheme.{u}} (p : S ⟶ S₀) (h : W ⟶ S)
    [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W)) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (U : W.Opens) (hU : ∃ x : W, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over U) r] :
    reflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ)) ⟶
      (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (hullForms p (r : ℤ) h) :=
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    AlgebraicGeometry.isIntegral_blowUp _
      (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw)
  haveI : IsNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) := inferInstance
  reflexiveHullExteriorPowerPullbackHom (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
    hreg hdim.le (Scheme.Hom.relativeDifferentials (h ≫ p)) r U hU

end Stacks.BlowupTwistUnit

end
