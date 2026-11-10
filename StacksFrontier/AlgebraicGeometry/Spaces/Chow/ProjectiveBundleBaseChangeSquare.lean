module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# The base change of a projective bundle along a morphism of good algebraic spaces

In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module and
`(π : P → X, 𝒪_P(1))` its projective bundle. Stacks 0ERY works, for every morphism `g : X' → X`
of good algebraic spaces over `B`, with the base change

```
P' = P ×_X X'  ──g'──▶  P
     │                  │
  π' │                  │ π
     ▼                  ▼
     X'  ─────g─────▶   X
```

and the invertible module `𝒪_{P'}(1) = (g')^*𝒪_P(1)`. The square has the following properties:
`P'` is an algebraic space which is good over the base, `π'` is proper, and, for `ℰ` of rank
`n + 1`, `π'` is flat of relative dimension `n`; `𝒪_{P'}(1)` is invertible.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleBaseChangeSpace`: the algebraic space `P' = P ×_X X'`.
* `AlgebraicGeometry.Space.projectiveBundleBaseChangeMap`: the morphism `g' : P' ⟶ P`.
* `AlgebraicGeometry.Space.projectiveBundleBaseChangeTwist`: the module `𝒪_{P'}(1)`.

## Main results

* `AlgebraicGeometry.Space.isProper_projectiveBundleBaseChangeProj`: `π'` is proper (Stacks 04WP).
* `AlgebraicGeometry.Space.isGood_projectiveBundleBaseChangeProj_comp`: `P'` is good over the base.
* `AlgebraicGeometry.Space.isFlat_projectiveBundleBaseChangeProj`: `π'` is flat (Stacks 0AMM).
* `AlgebraicGeometry.Space.hasRelativeDimension_projectiveBundleBaseChangeProj`: `π'` has relative
  dimension `n` (Stacks 04NS).
* `AlgebraicGeometry.Space.isInvertibleModule_projectiveBundleBaseChangeTwist`: `𝒪_{P'}(1)` is
  invertible (Stacks 0B8P).

## Implementation notes

`P'` is the presheaf fibre product `pullback π g` of the ambient category, the convention of
`AlgebraicGeometry.Space.BivariantClass` for base changes; `π'` is `pullback.snd π g` and `g'` is
`pullback.fst π g`. Its structure morphism to the base is `π' ≫ g ≫ s_X`.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- instance search over presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProjectiveBundleBaseChangeSquare
    (D : BaseSpaceDimensionSituation.{u}) :
    HasPullbacks ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProjectiveBundleBaseChangeSquare
    (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (D : BaseSpaceDimensionSituation.{u})
  {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
  (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
  [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (g : X' ⟶ X) (hX' : D.IsGood (g ≫ sX))

/-- The morphism `g : X' ⟶ X` of algebraic spaces underlying a morphism of good spaces. -/
abbrev goodSpaceHom : (⟨X', hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
  ObjectProperty.homMk g

/-- **The base change `P' = P ×_X X'` of the projective bundle `π : P ⟶ X` along `g : X' ⟶ X`**,
as an algebraic space: its underlying presheaf is `pullback π g`. -/
abbrev projectiveBundleBaseChangeSpace : AlgebraicSpaces D.site D.base D.base_mem :=
  AlgebraicSpaces.fiberProduct D.site D.base D.base_mem
    (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree) (goodSpaceHom D sX hX g hX')

/-- The morphism `g' : P' ⟶ P` of the base change square, as a morphism of algebraic spaces. -/
abbrev projectiveBundleBaseChangeMap :
    projectiveBundleBaseChangeSpace D sX hX E hfree g hX' ⟶
      projectiveBundle (X := ⟨X, hX.1⟩) E hfree :=
  ObjectProperty.homMk (pullback.fst (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g)

/-- The base change square `P' ⟶ P` over `X' ⟶ X` is cartesian. -/
theorem isPullback_projectiveBundleBaseChange :
    IsPullback (pullback.fst (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g)
      (pullback.snd (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g)
      (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g :=
  IsPullback.of_hasPullback _ _

include hX' in
/-- **The base change `π' : P' ⟶ X'` of the projection of a projective bundle is proper**: the
projection is proper, and properness is stable under base change (Stacks 04WP). -/
theorem isProper_projectiveBundleBaseChangeProj :
    IsProper D.site D.base D.base_mem
      (pullback.snd (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g) :=
  (isProper_isStableUnderBaseChange D.site D.base D.base_mem).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct D.site D.base D.base_mem
      (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree) (goodSpaceHom D sX hX g hX'))
    (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree)

include hX' in
/-- **The base change `P'` of a projective bundle is good over the base**, with structure
morphism `π' ≫ g ≫ s_X`: `π'` is proper, hence separated and locally of finite type, and
`X'` is good. -/
theorem isGood_projectiveBundleBaseChangeProj_comp :
    D.IsGood (pullback.snd (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g ≫ g ≫ sX) := by
  have hprop := isProper_projectiveBundleBaseChangeProj D sX hX E hfree g hX'
  refine ⟨(projectiveBundleBaseChangeSpace D sX hX E hfree g hX').2, ?_, ?_⟩
  · exact isQuasiSeparated_comp D.site D.base D.base_mem
      (projectiveBundleBaseChangeSpace D sX hX E hfree g hX').2 hX'.1 _ (g ≫ sX)
      (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hprop.1) hX'.2.1
  · exact isLocallyOfFiniteType_comp D.site D.base D.base_mem
      (projectiveBundleBaseChangeSpace D sX hX E hfree g hX').2 hX'.1 D.isAlgebraicSpace _ (g ≫ sX)
      hprop.2.1.1 hX'.2.2

section Rank

variable (n : ℕ) (hr : RingedSite.IsFiniteLocallyFreeOfRank
  (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (n + 1))

include hX' hr in
/-- **The base change `π' : P' ⟶ X'` of the projection of a projective bundle is flat**: the
projection is flat (`AlgebraicGeometry.Space.isFlat_projectiveBundleProj`), and flatness is
stable under base change, being étale local on source and target (Stacks 0AMM). -/
theorem isFlat_projectiveBundleBaseChangeProj :
    IsFlat D.site D.base D.base_mem
      (pullback.snd (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g) :=
  (holdsOnEveryEtaleChart_isStableUnderBaseChange D.site D.base D.base_mem
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      isEtaleLocalOnSourceAndTarget_flat).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct D.site D.base D.base_mem
      (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree) (goodSpaceHom D sX hX g hX'))
    (isFlat_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree)

include hX' hr in
/-- **The base change `π' : P' ⟶ X'` of the projection of the projective bundle of a module of
rank `n + 1` has relative dimension `n`**: the relative dimension at a point of the base change
is the relative dimension of `π` at its image (Stacks 04NS, part (1)). -/
theorem hasRelativeDimension_projectiveBundleBaseChangeProj :
    HasRelativeDimension n D.site D.base D.base_mem
      (pullback.snd (projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom g) := fun x' =>
  (hasRelativeDimensionAt_iff_of_isPullback D.site D.base D.base_mem
      (isPullback_projectiveBundleBaseChange D sX hX E hfree g)
      (projectiveBundle (X := ⟨X, hX.1⟩) E hfree).2 hX'.1 hX.1
      (isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).2.1.1 x' n).1
    (hasRelativeDimension_projectiveBundleProj (X := ⟨X, hX.1⟩) E n hr hfree _)

end Rank

/-- **The invertible module `𝒪_{P'}(1)` on the base change `P'`**: the inverse image of the twist
`𝒪_P(1)` along `g' : P' ⟶ P`. -/
abbrev projectiveBundleBaseChangeTwist :
    Modules.{u, u} D.site D.base D.base_mem
      (projectiveBundleBaseChangeSpace D sX hX E hfree g hX').1
      (projectiveBundleBaseChangeSpace D sX hX E hfree g hX').2 :=
  (modulePullback D.site D.base D.base_mem
      (projectiveBundleBaseChangeMap D sX hX E hfree g hX')).obj
    (projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree).obj

/-- **`𝒪_{P'}(1)` is invertible**: it is the inverse image of the invertible module `𝒪_P(1)`
(Stacks 0B8P). -/
theorem isInvertibleModule_projectiveBundleBaseChangeTwist :
    IsInvertibleModule (projectiveBundleBaseChangeSpace D sX hX E hfree g hX')
      (projectiveBundleBaseChangeTwist D sX hX E hfree g hX') :=
  modulePullbackInvertible _ _
    (isInvertibleModule_projectiveBundleTwist (X := ⟨X, hX.1⟩) E hfree)

end AlgebraicGeometry.Space

end
