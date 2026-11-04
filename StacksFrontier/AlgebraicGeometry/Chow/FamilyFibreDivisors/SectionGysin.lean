module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# The Gysin map on cycles read along a presentation of the zero scheme

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42, let `L` be an
invertible `𝒪_X`-module, let `s ∈ Γ(X, L)` and let `D = Z(s)` be its zero scheme. A triple
`(L, s, i : D → X)` as in Stacks 02T8 presents `D` by a closed immersion, and the Gysin map of
Stacks 0B6Z — available on cycles because `L|_D` is trivial — then reads

```
  i^* : Z_{k+1}(X) ⟶ Z_k(D).
```

`Stacks.Chow.gysinCycleMap` is this map for the canonical presentation
`i = (Z(s)).subschemeι`. The source states its rules for an arbitrary closed immersion `i`
cutting out `Z(s)`, and the identification of the source of such an `i` with the canonical
`(Z(s)).subscheme` is implicit there. It cannot be implicit in Lean: a scheme isomorphic to
`(Z(s)).subscheme` is not that scheme, and the cycle groups over the two are different groups.
This file therefore carries out the construction along an arbitrary presentation, and compares
it with the canonical one.

The point of doing so is the zero and the infinity section of the family of projective lines
`X ×_S ℙ¹_S ⟶ X`, which are closed immersions cutting out effective Cartier divisors with
trivial normal bundle (`StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionCartier`).
Read along them, the Gysin map on cycles is *literally* the fibre cycle map of
`Stacks.Chow.zeroFiber`, because `Stacks.Chow.zeroFiber` is the inverse image of a closed
subscheme along the zero section.

## Main definitions

* `Stacks.Chow.gysinCycleMapComponentAlong` — the two rules of Stacks 0B6Z on an integral closed
  subscheme, read along a presentation `i` of the zero scheme.
* `Stacks.Chow.gysinCycleMapRuleAlong` — those rules as a
  `Stacks.Chow.IntegralComponentRule` along `i`.
* `Stacks.Chow.gysinCycleMapAlong` — the Gysin map on cycles `Z_{k+1}(X) ⟶ Z_k(D)` of
  Stacks 0B6Z, read along `i`.

## Main results

* `Stacks.Chow.gysinCycleMapAlong_of_le` and `Stacks.Chow.gysinCycleMapAlong_of_not_le` — the two
  rules of Stacks 0B6Z.
* `Stacks.Chow.gysinCycleMapAlong_apply_of_presentation` — the locally finite component formula.
* `Stacks.Chow.gysinCycleMapAlong_subschemeι` — at the canonical presentation the map is
  `Stacks.Chow.gysinCycleMap`.
* `Stacks.Chow.properPushforward_gysinCycleMapAlong` — along any presentation the map is the
  canonical one transported by the induced isomorphism, so nothing new is being defined.
* `Stacks.Chow.gysinCycleMapAlong_zeroSection_of_not_le` and
  `Stacks.Chow.gysinCycleMapAlong_infinitySection_of_not_le` — at the two distinguished sections
  of `X ×_S ℙ¹_S` the map sends the fundamental cycle of an integral closed subscheme `W` to the
  fundamental cycle of the corresponding fibre `W₀`, resp. `W_∞`.

## References

* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The rules of Stacks 0B6Z along a presentation of the zero scheme -/

section Along

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Z ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Stacks 0B6Z along a presentation.** The cycle on `Z` attached to an integral closed
subscheme `W ⊆ X` of delta-dimension `k + 1` by the two rules of Stacks 0B6Z, read along a closed
immersion `i : Z ⟶ X` cutting out the zero scheme `D = Z(s)`: zero if `W` lies inside `D`, and
the fundamental cycle of the inverse image `i⁻¹ W` otherwise.

Ideal sheaves are ordered oppositely to their closed subschemes, so `Z(s) ≤ W` says that `W` lies
inside `Z(s)`. For `i = (Z(s)).subschemeι` this is
`Stacks.Chow.gysinCycleMapComponent`. -/
def gysinCycleMapComponentAlong (W : X.IdealSheafData) (_hW : IsIntegral W.subscheme)
    (_hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    CycleGroup C q k :=
  open Classical in
  if Stacks.Divisors.zeroScheme X L s ≤ W then 0
  else cycleAssociatedToClosedSubscheme C q ((W.comap i).subschemeι) k

omit [IsClosedImmersion i] in
/-- The component cycle of Stacks 0B6Z vanishes on an integral closed subscheme inside the zero
scheme. -/
theorem gysinCycleMapComponentAlong_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapComponentAlong C p q k L s i W hW hDim = 0 := by
  classical
  rw [gysinCycleMapComponentAlong]
  exact ite_eq_left h

omit [IsClosedImmersion i] in
/-- On an integral closed subscheme not inside the zero scheme the component cycle of
Stacks 0B6Z is the fundamental cycle of the inverse image along the presentation. -/
theorem gysinCycleMapComponentAlong_of_not_le (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapComponentAlong C p q k L s i W hW hDim =
      cycleAssociatedToClosedSubscheme C q ((W.comap i).subschemeι) k := by
  classical
  rw [gysinCycleMapComponentAlong]
  exact ite_eq_right h

omit [IsClosedImmersion i] in
/-- The component cycle attached to `W` is supported over `W`: it is either zero, or the
fundamental cycle of the inverse image of `W`. -/
theorem support_gysinCycleMapComponentAlong_subset (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    Function.support (gysinCycleMapComponentAlong C p q k L s i W hW hDim).1 ⊆
      i.base ⁻¹' (W.support : Set X) := by
  classical
  by_cases h : Stacks.Divisors.zeroScheme X L s ≤ W
  · rw [gysinCycleMapComponentAlong_of_le C p q k L s i W hW hDim h]
    simp
  · rw [gysinCycleMapComponentAlong_of_not_le C p q k L s i W hW hDim h]
    refine (support_cycleAssociatedToClosedSubscheme_subset C q
      ((W.comap i).subschemeι) k).trans ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact subset_rfl

/-- The two rules of Stacks 0B6Z along a presentation of the zero scheme, packaged so that
`Stacks.Chow.IntegralComponentRule.extendCycleGroup` can extend them coefficientwise. -/
def gysinCycleMapRuleAlong : IntegralComponentRule C p q i k where
  cycle := gysinCycleMapComponentAlong C p q k L s i
  support_subset := support_gysinCycleMapComponentAlong_subset C p q k L s i

/-- **Stacks 0B6Z along a presentation.** The Gysin map on cycles
`i^* : Z_{k+1}(X) ⟶ Z_k(D)` attached to a triple `(L, s, i : D ⟶ X)` as in Stacks 02T8 whose
invertible module restricts trivially to `D`.

The triple is the data `(L, s, i)` together with `_hker`, which says that `i` cuts out the zero
scheme of `s`, and `_hq`, which says that `i` is a morphism over the base. Neither is used in the
construction, exactly as `Stacks.Chow.gysinCycleMap` does not use its triviality hypothesis
`_htriv`; what they buy is that the map is the Gysin map of the source rather than some other
extension of a rule on integral components, and that is
`Stacks.Chow.properPushforward_gysinCycleMapAlong`. -/
def gysinCycleMapAlong
    (_htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (_hq : i ≫ p = q) (_hker : i.ker = Stacks.Divisors.zeroScheme X L s) :
    CycleGroup C p (k + 1) →+ CycleGroup C q k :=
  (gysinCycleMapRuleAlong C p q k L s i).extendCycleGroup

variable (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
  (hq : i ≫ p = q) (hker : i.ker = Stacks.Divisors.zeroScheme X L s)

omit [IsClosedImmersion i] in
/-- **Stacks 0B6Z.** An integral closed subscheme inside the zero scheme has zero image. -/
theorem gysinCycleMapAlong_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapAlong C p q k L s i htriv hq hker
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) = 0 :=
  (gysinCycleMapRuleAlong C p q k L s i).extendCycleGroup_cycleAssociatedToClosedSubscheme
      W hW hDim |>.trans (gysinCycleMapComponentAlong_of_le C p q k L s i W hW hDim h)

omit [IsClosedImmersion i] in
/-- **Stacks 0B6Z.** Away from the zero scheme the Gysin map on cycles sends the fundamental
cycle of an integral closed subscheme `W` to the fundamental cycle of the inverse image
`i⁻¹ W`. -/
theorem gysinCycleMapAlong_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapAlong C p q k L s i htriv hq hker
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C q ((W.comap i).subschemeι) k :=
  (gysinCycleMapRuleAlong C p q k L s i).extendCycleGroup_cycleAssociatedToClosedSubscheme
      W hW hDim |>.trans (gysinCycleMapComponentAlong_of_not_le C p q k L s i W hW hDim h)

omit [IsClosedImmersion i] in
/-- **Stacks 0B6Z.** The locally finite component formula: on a presentation `α = ∑ n_j [W_j]` of
a `(k+1)`-cycle by integral closed subschemes of delta-dimension `k + 1`, the coefficient of the
image at a point of `D` is the corresponding sum of the coefficients of the component cycles. -/
theorem gysinCycleMapAlong_apply_of_presentation {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) (y : Z) :
    (gysinCycleMapAlong C p q k L s i htriv hq hker α).1 y = ∑ᶠ j : J, n j *
      (gysinCycleMapComponentAlong C p q k L s i (W j) (hW j) (hDim j)).1 y :=
  (gysinCycleMapRuleAlong C p q k L s i).extendCycleGroup_apply_of_presentation W hW hDim hLocal
    n α hα y

end Along

/-! ### Comparison with the canonical presentation -/

section Comparison

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))

/-- At the canonical presentation of the zero scheme the Gysin map along a presentation is
`Stacks.Chow.gysinCycleMap`: the two component rules are the same rule. -/
theorem gysinCycleMapAlong_subschemeι :
    gysinCycleMapAlong C p ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k L s
        (Stacks.Divisors.zeroScheme X L s).subschemeι htriv rfl
        (Scheme.IdealSheafData.ker_subschemeι _) =
      gysinCycleMap C p k L s htriv :=
  rfl

variable {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q] (i : Z ⟶ X)
  [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- **The Gysin map along a presentation is the canonical one, transported.** Proper pushforward
along the isomorphism `e : Z ≅ Z(s)` induced by a presentation `i` carries the Gysin map read
along `i` to `Stacks.Chow.gysinCycleMap`. So reading the Gysin map along a presentation defines
nothing new; it only names the identification the source leaves implicit. -/
theorem properPushforward_gysinCycleMapAlong
    (hq : i ≫ p = q) (hker : i.ker = Stacks.Divisors.zeroScheme X L s)
    (e : Z ≅ (Stacks.Divisors.zeroScheme X L s).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι = i)
    (α : CycleGroup C p (k + 1)) :
    properPushforward C q ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) e.hom
        (by rw [← Category.assoc, he, hq]) k
        (gysinCycleMapAlong C p q k L s i htriv hq hker α) =
      gysinCycleMap C p k L s htriv α := by
  classical
  have hcomp : e.hom ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p = q := by
    rw [← Category.assoc, he, hq]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  obtain ⟨z, rfl⟩ : ∃ z : Z, e.hom.base z = y :=
    ⟨e.inv.base y, by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩
  rw [properPushforward_apply_of_isIso C q ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    e.hom hcomp k _ z]
  rw [gysinCycleMapAlong_apply_of_presentation C p q k L s i htriv hq hker
      (fun x : cycleSupportIndex α ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex α x)
      (locallyFinite_support_integralComponentAt α) (fun x ↦ α.1 x.1) α
      (cycle_eq_finsum_primeCycles α) z,
    isGysinCycleMap_gysinCycleMap C p k L s htriv
      (fun x : cycleSupportIndex α ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex α x)
      (locallyFinite_support_integralComponentAt α) (fun x ↦ α.1 x.1) α
      (cycle_eq_finsum_primeCycles α) (e.hom.base z)]
  refine finsum_congr fun x ↦ ?_
  refine congrArg (fun c : ℤ ↦ α.1 x.1 * c) ?_
  have hI := isIntegral_integralComponentAt x.1
  have hD := schemeDeltaDimension_cycleSupportIndex α x
  by_cases h : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x.1
  · rw [gysinCycleMapComponentAlong_of_le C p q k L s i _ hI hD h,
      gysinCycleMapComponent_of_le C p k L s _ hI hD h]
    rfl
  · rw [gysinCycleMapComponentAlong_of_not_le C p q k L s i _ hI hD h,
      gysinCycleMapComponent_of_not_le C p k L s _ hI hD h]
    have hci : (integralComponentAt x.1).comap i =
        ((integralComponentAt x.1).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι).comap e.hom := by
      rw [← Scheme.IdealSheafData.comap_comp, he]
    rw [hci, ← properPushforward_apply_of_isIso C q
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) e.hom hcomp k _ z,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isIso C q
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) e hcomp
        ((((integralComponentAt x.1).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι).comap e.hom).subschemeι) k,
      cycleAssociatedToClosedSubscheme_eq_of_iso C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) _
        ((integralComponentAt x.1).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι
        (comapSubschemeIsoOfIsIso e.hom ((integralComponentAt x.1).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι))
        (comapSubschemeIsoOfIsIso_hom_subschemeι e.hom _) k]

end Comparison

/-! ### The Gysin map at the two distinguished sections of a family of projective lines -/

/-- The structure morphism over the base of the family of projective lines `X ×_S ℙ¹_S`: the
first projection followed by the structure morphism of `X`. The delta-dimension function of
chapter 42 on a closed subscheme of the family, `Stacks.Chow.familyBase`, is its restriction. -/
abbrev familyStructureMorphism {X S : Scheme.{u}} (f : X ⟶ S) : projectiveLineProduct f ⟶ S :=
  pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f

attribute [local instance] isEffectiveCartierDivisor_ker_zeroSection
  isEffectiveCartierDivisor_ker_infinitySection

section SectionTriples

variable {B S : Scheme.{u}} (sB : B ⟶ S)

/-- The zero section is a morphism over the base: it is a section of the family. -/
theorem zeroSection_comp_familyStructureMorphism :
    zeroSection sB ≫ familyStructureMorphism sB = sB := by
  rw [familyStructureMorphism, ← Category.assoc, zeroSection_comp_fst, Category.id_comp]

/-- The infinity section is a morphism over the base. -/
theorem infinitySection_comp_familyStructureMorphism :
    infinitySection sB ≫ familyStructureMorphism sB = sB := by
  rw [familyStructureMorphism, ← Category.assoc, infinitySection_comp_fst, Category.id_comp]

/-- **Stacks 0F93.** The zero section presents the zero scheme of the canonical global section of
the invertible module attached to its image. So `(𝒪(D₀), 1_{D₀}, i₀)` is a triple as in
Stacks 02T8. -/
theorem ker_zeroSection_eq_zeroScheme :
    (zeroSection sB).ker =
      Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker) :=
  (zeroScheme_divisorSheafGlobalSection_ker_zeroSection sB).symm

/-- **Stacks 0F93.** The infinity section presents the zero scheme of the canonical global
section of the invertible module attached to its image. -/
theorem ker_infinitySection_eq_zeroScheme :
    (infinitySection sB).ker =
      Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection sB).ker) :=
  (zeroScheme_divisorSheafGlobalSection_ker_infinitySection sB).symm

/-- **Stacks 0F93.** The normal bundle of the zero section is trivial, read on the zero scheme of
the canonical section. This is the hypothesis `_htriv` of Stacks 0B6Z at the zero section. -/
theorem isTrivial_zeroScheme_ker_zeroSection :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection
          (zeroSection sB).ker)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection
          (zeroSection sB).ker)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
          (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
          (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker)).subschemeι).obj
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)) := by
  rw [← ker_zeroSection_eq_zeroScheme sB]
  exact isTrivial_pullback_divisorSheaf_ker_zeroSection sB

/-- **Stacks 0F93.** The normal bundle of the infinity section is trivial, read on the zero
scheme of the canonical section. -/
theorem isTrivial_zeroScheme_ker_infinitySection :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection
          (infinitySection sB).ker)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection
          (infinitySection sB).ker)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
          (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
          (Stacks.Divisors.divisorSheafGlobalSection
            (infinitySection sB).ker)).subschemeι).obj
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)) := by
  rw [← ker_infinitySection_eq_zeroScheme sB]
  exact isTrivial_pullback_divisorSheaf_ker_infinitySection sB

end SectionTriples

section FamilySections

variable (C : ChowSituation.{u}) {B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
  (k : ℤ)

/-- **Stacks 0B6Z at the zero section: the Gysin map on cycles is the zero-fibre cycle map.** For
an integral closed subscheme `W` of `X ×_S ℙ¹_S` of delta-dimension `k + 1` which does not lie
inside the zero section, the Gysin map of the triple `(𝒪(D₀), 1_{D₀}, i₀)`, read along the zero
section, sends `[W]_{k+1}` to the fundamental cycle of the zero fibre `W₀` of Stacks 02S4.

The two agree on the nose and not merely up to an identification: `Stacks.Chow.zeroFiber` is the
inverse image of `W` along the zero section, which is exactly the rule
`i_0^*[W] = [D₀ ∩ W]_k` of Stacks 02T8 read on `X`. -/
theorem gysinCycleMapAlong_zeroSection_of_not_le
    (W : (projectiveLineProduct sB).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ familyStructureMorphism sB) =
      ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
      (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
      (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker) ≤ W) :
    gysinCycleMapAlong C (familyStructureMorphism sB) sB k
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker) (zeroSection sB)
        (isTrivial_zeroScheme_ker_zeroSection sB)
        (zeroSection_comp_familyStructureMorphism sB) (ker_zeroSection_eq_zeroScheme sB)
        (cycleAssociatedToClosedSubscheme C (familyStructureMorphism sB) W.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C sB (zeroFiber sB W).subschemeι k :=
  gysinCycleMapAlong_of_not_le C (familyStructureMorphism sB) sB k _ _ (zeroSection sB)
    (isTrivial_zeroScheme_ker_zeroSection sB) (zeroSection_comp_familyStructureMorphism sB)
    (ker_zeroSection_eq_zeroScheme sB) W hW hDim h

/-- **Stacks 0B6Z at the infinity section: the Gysin map on cycles is the infinity-fibre cycle
map.** -/
theorem gysinCycleMapAlong_infinitySection_of_not_le
    (W : (projectiveLineProduct sB).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ familyStructureMorphism sB) =
      ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
      (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
      (Stacks.Divisors.divisorSheafGlobalSection (infinitySection sB).ker) ≤ W) :
    gysinCycleMapAlong C (familyStructureMorphism sB) sB k
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection sB).ker)
        (infinitySection sB) (isTrivial_zeroScheme_ker_infinitySection sB)
        (infinitySection_comp_familyStructureMorphism sB)
        (ker_infinitySection_eq_zeroScheme sB)
        (cycleAssociatedToClosedSubscheme C (familyStructureMorphism sB) W.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C sB (infinityFiber sB W).subschemeι k :=
  gysinCycleMapAlong_of_not_le C (familyStructureMorphism sB) sB k _ _ (infinitySection sB)
    (isTrivial_zeroScheme_ker_infinitySection sB)
    (infinitySection_comp_familyStructureMorphism sB) (ker_infinitySection_eq_zeroScheme sB)
    W hW hDim h

/-- **Stacks 0B6Z at the zero section: the vanishing rule.** An integral closed subscheme lying
inside the zero section has zero image. -/
theorem gysinCycleMapAlong_zeroSection_of_le
    (W : (projectiveLineProduct sB).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ familyStructureMorphism sB) =
      ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
      (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
      (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker) ≤ W) :
    gysinCycleMapAlong C (familyStructureMorphism sB) sB k
        (Stacks.Divisors.divisorSheaf (zeroSection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (zeroSection sB).ker) (zeroSection sB)
        (isTrivial_zeroScheme_ker_zeroSection sB)
        (zeroSection_comp_familyStructureMorphism sB) (ker_zeroSection_eq_zeroScheme sB)
        (cycleAssociatedToClosedSubscheme C (familyStructureMorphism sB) W.subschemeι (k + 1)) =
      0 :=
  gysinCycleMapAlong_of_le C (familyStructureMorphism sB) sB k _ _ (zeroSection sB)
    (isTrivial_zeroScheme_ker_zeroSection sB) (zeroSection_comp_familyStructureMorphism sB)
    (ker_zeroSection_eq_zeroScheme sB) W hW hDim h

/-- **Stacks 0B6Z at the infinity section: the vanishing rule.** -/
theorem gysinCycleMapAlong_infinitySection_of_le
    (W : (projectiveLineProduct sB).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ familyStructureMorphism sB) =
      ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme (projectiveLineProduct sB)
      (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
      (Stacks.Divisors.divisorSheafGlobalSection (infinitySection sB).ker) ≤ W) :
    gysinCycleMapAlong C (familyStructureMorphism sB) sB k
        (Stacks.Divisors.divisorSheaf (infinitySection sB).ker)
        (Stacks.Divisors.divisorSheafGlobalSection (infinitySection sB).ker)
        (infinitySection sB) (isTrivial_zeroScheme_ker_infinitySection sB)
        (infinitySection_comp_familyStructureMorphism sB)
        (ker_infinitySection_eq_zeroScheme sB)
        (cycleAssociatedToClosedSubscheme C (familyStructureMorphism sB) W.subschemeι (k + 1)) =
      0 :=
  gysinCycleMapAlong_of_le C (familyStructureMorphism sB) sB k _ _ (infinitySection sB)
    (isTrivial_zeroScheme_ker_infinitySection sB)
    (infinitySection_comp_familyStructureMorphism sB) (ker_infinitySection_eq_zeroScheme sB)
    W hW hDim h

end FamilySections

end Stacks.Chow

end
