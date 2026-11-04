module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernRuleSubspaceImagePrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRuleDifferenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# Stacks 0ER6 at a cartesian square, and its inputs for the bivariant classes

In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B`, let `ℒ` be an invertible `𝒪_X`-module with a global section `s`, `E = Z(s)` its
vanishing locus with closed immersion `i : E → X`, and let `E' = Z(f^*s) ⊆ X'`, with the
projection `g : E' ⟶ E` of the cartesian square of Remark 0ER3.  **Stacks 0ER6** says

  `(i')^* f^* α = g^* i^* α`   in `CH_{k+r}(E')`

for every `(k+1)`-cycle `α` on `X`.  The base proves it over the constructed Chow groups
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap`).  This file reads it
at any projection `g` of a cartesian square and any spelling of the degree, the form in which the
registrations of Stacks 0ERN and Stacks 0ERP use it, and collects the other cycle-level inputs of
those two bivariant classes.  It carries no `@[stacks]` registration.

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback`: the
  base's **Stacks 0ER6**
  (`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap`) at any projection
  `g` of a cartesian square and any spelling `m` of the degree `k + r`.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_gysinPullbackProjection`: such a `g` is
  flat of relative dimension `r`.
* `AlgebraicGeometry.Space.exists_isPullback_vanishingLocus_pullbackSheaf`: **Stacks 0ER3**, the
  vanishing locus of the pulled-back section is the base change, as a cartesian square: the
  square `AlgebraicGeometry.Space.pullbackDivisor_isPullback` read through
  `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`.
* `AlgebraicGeometry.Space.properCyclePushforward_id` and
  `AlgebraicGeometry.Space.properCyclePushforward_flatPullbackMap_of_isIso`: proper pushforward
  along the identity is the identity, and pushing forward along an isomorphism undoes a flat
  pullback.

## Implementation notes

The Chow groups are taken in the index universe `u + 1`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapCanonical`: the flat pullback
of Stacks 0EQB raises the universe of a presenting family to `max v (u + 1)`.

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 083Z](https://stacks.math.columbia.edu/tag/083Z)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Capping on a closed subspace and capping on the image of a subspace of it -/

section ClosedSubspaceImage

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ)

include hN in
/-- The restriction `𝒩|_E` of an invertible module to a closed subspace is invertible. -/
theorem isInvertibleModule_closedSubspaceRestrictSheaf :
    IsInvertibleModule (⟨E.1.toFunctor, (isGood_closedSubspace D sX hX E).1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) (closedSubspaceRestrictSheaf D sX hX N E) :=
  modulePullbackInvertible (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hX.1⟩ E) N hN

end ClosedSubspaceImage

/-! ### The projection of the cartesian square of Remark 0ER3 -/

section Contained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L)
    {g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' (ObjectProperty.homMk f) L)
        (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)).1.toFunctor ⟶
      (vanishingLocus D p hp L s).1.toFunctor}
    (hsq : IsPullback g (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp'
        (ObjectProperty.homMk f) L)
        (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)).1.ι
      (vanishingLocus D p hp L s).1.ι f)

include hfbase hflat hr hsq in
/-- **Remark 0ER3: the projection `g : E' ⟶ E` is flat of relative dimension `r`**, being the base
change of `f` along the closed immersion `E ⟶ X` (Stacks 0EPD, second assertion). -/
theorem isFlat_and_hasRelativeDimension_gysinPullbackProjection :
    IsFlat D.site D.base D.base_mem g ∧ HasRelativeDimension r D.site D.base D.base_mem g :=
  (isFlat_and_hasRelativeDimension_of_isPullback D _
    (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' (ObjectProperty.homMk f) L)
      (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)) _
    (isGood_vanishingLocus D p hp L s) p' hp' p hp
    (comp_structure_of_isPullback D p p' hfbase hsq) hfbase hsq r hflat hr).2

end Contained

/-! ### Proper pushforward along the identity, and along an isomorphism after flat pullback -/

section Bookkeeping

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- The closure of the image of `V` under the identity is `V`. -/
private theorem closureImage_id_eq_self (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) (𝟙 X) V = V :=
  (IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hX.1 hX.1
    (D.isDecentSpace_of_isGood sX hX) (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X))
      V).trans
    (IntegralClosedSubspace.pushforward_id_eq_self D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X))
      V)

/-- The degree of Stacks 0EP1 along the identity is `1`. -/
theorem properCycleDegree_id (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleDegree D sX hX sX hX (𝟙 X) V = 1 := by
  have hone : functionFieldDegree D sX hX sX hX (𝟙 X) V = 1 :=
    IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sX hX)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X)) V
  rw [properCycleDegree, if_pos (by rw [closureImage_id_eq_self D sX hX V]), hone, Nat.cast_one]

open scoped Classical in
/-- The multiplicity of Stacks 0EP1 along the identity is the indicator of the diagonal. -/
theorem properCycleMult_id (V Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleMult D sX hX sX hX (𝟙 X) V Z = if V = Z then 1 else 0 := by
  rw [properCycleMult, properCycleDegree_id D sX hX V, closureImage_id_eq_self D sX hX V]

/-- **Proper pushforward along the identity is the identity**, on cycles and so on every Chow
group. -/
theorem properCyclePushforward_id (hqc : IsQuasiCompact D.site D.base D.base_mem (𝟙 X)) (k : ℤ)
    (α : CycleGroup D sX k) :
    properCyclePushforward D sX hX sX hX (f := 𝟙 X) (Category.id_comp sX) hqc k α = α := by
  classical
  refine Subtype.ext (funext fun Z => ?_)
  show properCyclePushforwardCoeff D sX hX sX hX (𝟙 X) α.1 Z = α.1 Z
  rw [properCyclePushforwardCoeff, finsum_eq_single _ Z fun V hV => by
      rw [properCycleMult_id D sX hX V Z, if_neg hV, mul_zero],
    properCycleMult_id D sX hX Z Z, if_pos rfl, mul_one]

/-- **Pushing forward along an isomorphism undoes a flat pullback.**  Let `e : P ⟶ Q` be an
isomorphism over a good `T`, i.e. `e ≫ b = a` for flat morphisms `a : P ⟶ T` and `b : Q ⟶ T` of
relative dimension `r`.  Then `e_*(a^* x) = b^* x` for every cycle `x` on `T`.  This is Stacks
0EPD on the cartesian square with sides `e` and `𝟙_T`, together with
`AlgebraicGeometry.Space.properCyclePushforward_id`. -/
theorem properCyclePushforward_flatPullbackMap_of_isIso {P Q T : (BigFppfOver D.site D.base
    D.base_mem)ᵒᵖ ⥤ Type u} (sP : P ⟶ D.space) (hP : D.IsGood sP) (sQ : Q ⟶ D.space)
    (hQ : D.IsGood sQ) (sT : T ⟶ D.space) (hT : D.IsGood sT) {e : P ⟶ Q} [IsIso e]
    {a : P ⟶ T} {b : Q ⟶ T} (hab : e ≫ b = a) (ha : a ≫ sT = sP) (hb : b ≫ sT = sQ)
    (he : e ≫ sQ = sP) (heqc : IsQuasiCompact D.site D.base D.base_mem e) (r : ℕ)
    (haf : IsFlat D.site D.base D.base_mem a) (har : HasRelativeDimension r D.site D.base
      D.base_mem a)
    (hbf : IsFlat D.site D.base D.base_mem b) (hbr : HasRelativeDimension r D.site D.base
      D.base_mem b)
    (k n : ℤ) (hkn : k + (r : ℤ) = n) (x : CycleGroup D sT k) :
    properCyclePushforward D sP hP sQ hQ he heqc n
        (flatPullbackMap D sP hP sT hT a ha r haf har k n hkn x) =
      flatPullbackMap D sQ hQ sT hT b hb r hbf hbr k n hkn x := by
  have hsq : IsPullback a e (𝟙 T) b :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hab]⟩
  have h := flatPullback_properPushforward_unconditional D sP hP sT hT sQ hQ sT hT ha he
    (Category.id_comp sT) hb r hbf hbr hsq
    (isProper_of_isClosedImmersion D.site D.base D.base_mem hT.1 hT.1 (𝟙 T)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 T))) k n hkn x
  rw [properCyclePushforward_id] at h
  exact h.symm

end Bookkeeping

/-! ### Stacks 0ER3: the vanishing locus of the pulled-back section is the base change -/

section BaseChangeSquare

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- **Stacks 0ER3.**  For `ℒ` invertible on `X` with a global section `s` and `f : X' ⟶ X`, the
vanishing locus `E' = Z(f^*s)` of the pulled-back section is the base change `X' ×_X E` of
`E = Z(s)`: there is a projection `g : E' ⟶ E` making the square with the two closed immersions
and `f` cartesian.  This is the cartesian square
`AlgebraicGeometry.Space.pullbackDivisor_isPullback` of `f^{-1}(E)`, read through the
identification `f^{-1}(E) = E'` of `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`. -/
theorem exists_isPullback_vanishingLocus_pullbackSheaf (hL : IsInvertibleSheaf D p hp L) :
    ∃ g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)).1.toFunctor ⟶
        (vanishingLocus D p hp L s).1.toFunctor,
      IsPullback g (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)).1.ι (vanishingLocus D p hp L s).1.ι
        f.hom := by
  rw [← pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL]
  exact ⟨_, pullbackDivisor_isPullback D p hp p' hp' f L s⟩

end BaseChangeSquare

/-! ### Stacks 0ER6 at a cartesian square -/

section NonContainedHelpers

variable (D : BaseSpaceDimensionSituation.{u})

/-- The cycle of an integral closed subspace, read as a closed subspace, is its fundamental
cycle. -/
theorem cycleCoeffOfClosedSubspace_integralClosedSubspace
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (n : ℤ)
    (hn : deltaDimension D sY W = n) :
    cycleCoeffOfClosedSubspace D sY hY W.subspace W.isClosedSubspace n
        (canonicalGeometricPoint D.site D.base D.base_mem W.subspace.toFunctor) =
      integralCycleCoeff D W := by
  subst hn
  refine funext fun V => ?_
  have hdim := (deltaDimensionSubspace_integralClosedSubspace D sY hY W).le
  by_cases hV : V = W
  · subst hV
    have h := closedSubspaceCycle_integral_apply_self D sY hY V hdim
    rw [closedSubspaceCycle_coe] at h
    rw [h, integralCycleCoeff_self]
  · have h := closedSubspaceCycle_integral_apply_of_ne D sY hY W V hdim hV
    rw [closedSubspaceCycle_coe] at h
    rw [h, integralCycleCoeff_eq_zero D W hV]

end NonContainedHelpers

section NonContained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L)
    {g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' (ObjectProperty.homMk f) L)
        (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)).1.toFunctor ⟶
      (vanishingLocus D p hp L s).1.toFunctor}
    (hsq : IsPullback g (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp'
        (ObjectProperty.homMk f) L)
        (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)).1.ι
      (vanishingLocus D p hp L s).1.ι f)

local notation "𝔼" => vanishingLocus D p hp L s
local notation "𝕃'" => pullbackSheaf D p hp p' hp' (ObjectProperty.homMk f) L
local notation "𝕤'" => pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s
local notation "𝔼'" => vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp'
  (ObjectProperty.homMk f) L) (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)
local notation "h𝔼" => isGood_vanishingLocus D p hp L s
local notation "h𝔼'" => isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp'
  (ObjectProperty.homMk f) L) (pullbackGlobalSection D p hp p' hp' (ObjectProperty.homMk f) L s)
local notation "h𝕃'" => isInvertibleSheaf_pullbackSheaf D p hp p' hp' (ObjectProperty.homMk f) L hL
local notation "hgfr" => isFlat_and_hasRelativeDimension_gysinPullbackProjection D p hp p' hp'
  hfbase r hflat hr L s hsq
local notation "hgbase" => comp_structure_of_isPullback D p p' hfbase hsq

include hfbase hflat hr hL hsq

/-- **Stacks 0ER6 at any projection `g` of a cartesian square and any spelling `m` of the degree
`k + r`.**  For `f : X' ⟶ X` flat of relative dimension `r`, `(ℒ, s)` with `E = Z(s)` and
`E' = Z(f^*s)`, and any `g : E' ⟶ E` making the square of Remark 0ER3 cartesian,
`(i')^* f^* α = g^* i^* α` in `CH_m(E')`.  The inclusion `E → X` is a monomorphism, so `g` is the
base's projection `AlgebraicGeometry.Space.pullbackVanishingLocusProjection`, and this is the
base's Stacks 0ER6, `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap`,
with the target degree a second integer, which is how the degree `(k + 1) - p` of a bivariant
class of degree `p = -r` is written. -/
theorem chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback (k m : ℤ)
    (hm : k + (r : ℤ) = m) (hkm : k + 1 + (r : ℤ) = m + 1) (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ p') h𝔼' m
        (gysinCycleMap D p' 𝔼' h𝔼' m (sectionGysinRule D p' hp' 𝕃' 𝕤' m h𝕃')
          (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (m + 1) hkm α)) =
      chowClassCanonical.{u + 1} D ((𝔼').1.ι ≫ p') h𝔼' m
        (flatPullbackMap D ((𝔼').1.ι ≫ p') h𝔼' ((𝔼).1.ι ≫ p) h𝔼 g hgbase r (hgfr).1 (hgfr).2 k
          m hm (gysinCycleMap D p 𝔼 h𝔼 k (sectionGysinRule D p hp L s k hL) α)) := by
  subst hm
  have hg : g = pullbackVanishingLocusProjection D p hp p' hp' (ObjectProperty.homMk f) L s hL :=
    (cancel_mono (vanishingLocus D p hp L s).1.ι).1 (hsq.w.trans
      (pullbackVanishingLocusProjection_comm D p hp p' hp' (ObjectProperty.homMk f) L s hL).symm)
  subst hg
  exact chowClassCanonical_gysinCycleMap_flatPullbackMap D p hp p' hp' (ObjectProperty.homMk f)
    hfbase r hflat hr L s hL k α

end NonContained

end AlgebraicGeometry.Space

end
