module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRuleDifferenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapDefect
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# Stacks 0ER5 reduced to one integral closed subspace, in the Chow group

In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic spaces over `B`, let
`(ℒ, s, i : D → X)` be as in Definition 0ER1 and form the diagram of Remark 0ER3

```
D' --i'--> X'
|          |
g          f
|          |
v          v
D  --i-->  X
```

with `ℒ' = f^*ℒ`, `s' = f^*s` and `D' = Z(s') = X' ×_X D`. Stacks 0ER5 is the identity
`i^* f_* α' = g_* (i')^* α'` in `CH_k(D)`. The letter `D` is taken by the dimension situation,
so the vanishing loci are called `E = Z(s)` and `E' = Z(s')` below.

This file builds the diagram from the two vanishing loci and reduces the identity to the
source's two cases at a single integral closed subspace `W' ⊆ X'` of δ-dimension `k + 1`, with
`W` the closure of the image of `W'`.

## The route

The Gysin map of Stacks 0ER1 pushed forward to the ambient space is a cap product of
Stacks 0EQJ: `i_*(i^*β) = c₁ ∩ β` at the component rule whose value at `W ⊄ E` is
`div_{ℒ|_W}(s|_W)` and at `W ⊆ E` is `c₁(ℒ|_W) ∩ [W]`
(`AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap`).
Hence, `i ∘ g = f ∘ i'` and proper pushforward being functorial (Stacks 0EP2),

`i_*(i^* f_* α' - g_* (i')^* α') = c₁(ℒ) ∩ f_*α' - f_*(c₁(ℒ') ∩ α')`,

which is minus the commutator of Stacks 0EQT, the sum over `W'` of the defects
`α'(W') · (f_*(c₁(ℒ'|_{W'}) ∩ [W']) - deg(W'/W) · (c₁(ℒ|_W) ∩ [W]))`.  A rational equivalence
on `E` is what is wanted, and a cycle on `E` whose pushforward to `X` is rationally equivalent
to zero by integral closed subspaces *inside `|E|`* is rationally equivalent to zero on `E`.
So the defect at each `W'` has to vanish rationally inside `|E|`, and this is exactly the
source's case analysis:

* `W' ⊄ E'`: then `W ⊄ E`, and the defect vanishes **as a cycle** (the source: "Hence the
  equality holds as cycles"), by Stacks 0EQS for `W' → W`;
* `W' ⊆ E'`: then `W ⊆ E`, and the defect is rationally equivalent to zero inside `|W| ⊆ |E|`,
  by the second assertion of Stacks 0EQS.

The passage from the prime cycles to `α'` is Stacks 0EQ8, the carriers being the closures of
the images of the `W'`, which are locally finite by Stacks 0ENZ.

## Main definitions

* `AlgebraicGeometry.Space.pullbackSectionVanishingLocus`: `E' = Z(f^*s)`.
* `AlgebraicGeometry.Space.pullbackVanishingLocusProjection`: `g : E' ⟶ E`.

## Main results

* `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`: `X' ×_X E = Z(f^*s)`.
* `AlgebraicGeometry.Space.isProper_pullbackVanishingLocusProjection`: `g` is proper.
* `isRationallyEquivalentToZeroWithinCanonical_properPushforward_firstChernCapCycleMap_sub`:
  the commutator of Stacks 0EQT is rationally equivalent to zero inside the union of any
  carriers of the defects contained in the closures of the images.
* `AlgebraicGeometry.Space.chowClassCanonical_gysin_properPushforward_eq_of_defects`: Stacks 0ER5
  from the two prime-cycle cases.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The diagram of Remark 0ER3 between the two vanishing loci -/

section Diagram

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- The morphism `g : E' ⟶ E` of the diagram of Remark 0ER3: `E' = Z(f^*s)` is the inverse
image `f^{-1}(E)` by `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`, followed by the
projection of the inverse image onto `E`. -/
def pullbackVanishingLocusProjection (hL : IsInvertibleSheaf D p hp L) :
    (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.toFunctor ⟶
      (vanishingLocus D p hp L s).1.toFunctor :=
  Subfunctor.homOfLe
      (congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL)).ge ≫
    pullbackDivisorProjection D p hp p' hp' f L s

/-- **Stacks 0ER3.** The diagram commutes: `g ≫ i = i' ≫ f`. -/
theorem pullbackVanishingLocusProjection_comm (hL : IsInvertibleSheaf D p hp L) :
    pullbackVanishingLocusProjection D p hp p' hp' f L s hL ≫ (vanishingLocus D p hp L s).1.ι =
      (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ f.hom := by
  rw [pullbackVanishingLocusProjection, Category.assoc, pullbackDivisor_comm, ← Category.assoc,
    Subfunctor.homOfLe_ι]

/-- The projection `g : E' ⟶ E` is a morphism over the base. -/
theorem pullbackVanishingLocusProjection_comp_structure (hL : IsInvertibleSheaf D p hp L)
    (hf : f.hom ≫ p = p') :
    pullbackVanishingLocusProjection D p hp p' hp' f L s hL ≫
        ((vanishingLocus D p hp L s).1.ι ≫ p) =
      (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p' := by
  rw [← Category.assoc, pullbackVanishingLocusProjection_comm, Category.assoc, hf]

/-- The inclusion of a closed subspace of an algebraic space is proper. -/
private theorem isProper_closedSubspaces_ι
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Z : ClosedSubspaces D.site D.base D.base_mem X) :
    IsProper D.site D.base D.base_mem Z.1.ι :=
  isProper_of_isClosedImmersion D.site D.base D.base_mem Z.2.1 hX _ Z.2.2

/-- **The projection `g : E' ⟶ E` is proper**, `f` being proper: `g ≫ i = i' ≫ f` is proper,
and `i` is a closed immersion, hence separated (Stacks 04NX). -/
theorem isProper_pullbackVanishingLocusProjection (hL : IsInvertibleSheaf D p hp L)
    (hf : IsProper D.site D.base D.base_mem f.hom) :
    IsProper D.site D.base D.base_mem (pullbackVanishingLocusProjection D p hp p' hp' f L s hL) :=
  isProper_of_comp_of_isSeparated D.site D.base D.base_mem
    (pullbackSectionVanishingLocus D p hp p' hp' f L s).2.1 (vanishingLocus D p hp L s).2.1 hp.1 _ _
    (by
      rw [pullbackVanishingLocusProjection_comm]
      exact isProper_comp D.site D.base D.base_mem
        (pullbackSectionVanishingLocus D p hp p' hp' f L s).2.1
        hp'.1 hp.1 _ _ (isProper_closedSubspaces_ι D hp'.1 _) hf)
    (isSeparated_of_isClosedImmersion D.site D.base D.base_mem _ (vanishingLocus D p hp L s).2.2)

end Diagram

/-! ### The commutator of Stacks 0EQT inside chosen carriers -/

section Carrier

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k)

/-- **Stacks 0EQ8 for the commutator of Stacks 0EQT, with carriers.**  If the multiple
`α(W) · (defect at W)` of the defect of the projection formula at each integral closed subspace
`W ⊆ X` occurring in `α` is rationally equivalent to zero inside a subset `C W` of the closure
of the image of `|W|`, then `p_*(c₁(𝒩) ∩ α) - c₁(ℒ) ∩ p_*α` is rationally equivalent to zero
inside the union of the `C W`.

The closures of the images form a locally finite family by Stacks 0ENZ, hence so do the `C W`,
and the commutator is coefficientwise the sum of the multiples of the defects
(`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_sub_apply`). -/
theorem isRationallyEquivalentToZeroWithinCanonical_properPushforward_firstChernCapCycleMap_sub
    (α : CycleGroup D sX (k + 1))
    (C : IntegralClosedSubspace D.site D.base D.base_mem X →
      Set (points D.site D.base D.base_mem Y))
    (hC : ∀ W, C W ⊆ subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) p W).subspace)
    (hdefect : ∀ W, α.1 W ≠ 0 →
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sY hY k
        (α.1 W • properPushforwardChernDefect D hX hY hpB hp k chernX chernY W) (C W)) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sY hY k
      (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) -
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α))
      (⋃ j : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0}, C j.1) := by
  classical
  let J := {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0}
  have hlf := (locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp.2.1.2
    (fun j : J => subspacePointSet D.site D.base D.base_mem X j.1.subspace)
    (fun j => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 j.1)
    (locallyFinite_cycleSupport α)).1
  have hE : (fun j : J => closure (pointsMap D.site D.base D.base_mem X p ''
      subspacePointSet D.site D.base D.base_mem X j.1.subspace)) = fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) p j.1).subspace :=
    funext fun j => (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base
      D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p j.1).symm
  rw [hE] at hlf
  refine isRationallyEquivalentToZeroWithinCanonical_finsum.{u + 1} D sY hY k (J := J)
    (fun j => α.1 j.1 • properPushforwardChernDefect D hX hY hpB hp k chernX chernY j.1)
    (fun j => C j.1) (hlf.subset fun j => hC j.1) (fun j => hdefect j.1 j.2) fun T => ?_
  rw [properPushforward_firstChernCapCycleMap_sub_apply (hp := hp)]
  have hj : ∀ j : J, ((α.1 j.1 • properPushforwardChernDefect D hX hY hpB hp k chernX chernY
      j.1 : CycleGroup D sY k) : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) T =
      α.1 j.1 * (properPushforwardChernDefect D hX hY hpB hp k chernX chernY j.1).1 T :=
    fun j => zsmul_cycleGroup_apply D sY k _ _ T
  rw [finsum_congr hj]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun W => α.1 W * (properPushforwardChernDefect D hX hY hpB hp k chernX chernY W).1 T)
    (fun W => α.1 W ≠ 0)).symm
  refine finsum_congr fun W => ?_
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul, finsum_eq_if, if_neg (not_not.2 rfl)]
  · rw [finsum_eq_if, if_pos hW]

end Carrier

/-! ### Stacks 0ER5 from the two prime-cycle cases -/

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (hf : IsProper D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

/-- The component rule of Stacks 0EQJ through which the Gysin map of `(ℒ, s)` is read on `X`:
`div_{ℒ|_W}(s|_W)` at `W ⊄ Z(s)` and `c₁(ℒ|_W) ∩ [W]` at `W ⊆ Z(s)`. -/
abbrev sectionGysinChernRule : FirstChernComponentCycleRule D p k :=
  restrictedSectionChernRule D p hp L s hL k (restrictedDivisorCycle D p hp L k hL)

/-- The pushforward to `X` of the Gysin map of Stacks 0ER1 is the cap product at
`AlgebraicGeometry.Space.sectionGysinChernRule`. -/
theorem cycleGroupClosedPushforward_sectionGysin_eq (α : CycleGroup D p (k + 1)) :
    cycleGroupClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2 p hp.2.2
        ((vanishingLocus D p hp L s).1.ι ≫ p) rfl k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL) α) =
      firstChernCapCycleMap D p hp k (sectionGysinChernRule D p hp L s hL k) α :=
  cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p hp L s hL k
    (restrictedDivisorCycle D p hp L k hL) α

/-- **Stacks 0ER5 from the source's two prime-cycle cases.**  Let `f : X' ⟶ X` be proper, let
`(ℒ, s)` be an invertible sheaf with a global section and form the diagram of Remark 0ER3 with
`E = Z(s)` and `E' = Z(f^*s)`. Suppose that at every integral closed subspace `W' ⊆ X'` of
δ-dimension `k + 1`

* if `W' ⊄ E'`, the defect of the projection formula at `W'`, for the Gysin component rules of
  `(f^*ℒ, f^*s)` on `X'` and of `(ℒ, s)` on `X`, vanishes as a cycle; and
* if `W' ⊆ E'`, every multiple of it is rationally equivalent to zero inside the closure of the
  image of `W'`.

Then `i^* f_* α' = g_* (i')^* α'` in `CH_k(E)` for every `α' ∈ Z_{k+1}(X')`. -/
theorem chowClassCanonical_gysin_properPushforward_eq_of_defects
    (hnot : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      deltaDimension D p' W' = k + 1 →
      ¬ W'.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 →
      properPushforwardChernDefect D hp' hp hfbase hf k
        (sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)
          (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) k)
        (sectionGysinChernRule D p hp L s hL k) W' = 0)
    (hle : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      deltaDimension D p' W' = k + 1 →
      W'.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 → ∀ a : ℤ,
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D p hp k
        (a • properPushforwardChernDefect D hp' hp hfbase hf k
          (sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s)
            (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) k)
          (sectionGysinChernRule D p hp L s hL k) W')
        (subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
            (D.isDecentSpace_of_isGood p hp) f.hom W').subspace))
    (α' : CycleGroup D p' (k + 1)) :
    chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL)
          (properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 (k + 1) α')) =
      chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s) k
        (properCyclePushforward D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L s)
          (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase)
          (isProper_pullbackVanishingLocusProjection D p hp p' hp' f L s hL hf).2.1.2 k
          (gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
            (isGood_vanishingLocus D p' hp' _ _) k
            (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s) k
              (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL)) α')) := by
  classical
  set E := vanishingLocus D p hp L s with hEdef
  set E' := pullbackSectionVanishingLocus D p hp p' hp' f L s with hE'def
  set L' := pullbackSheaf D p hp p' hp' f L
  set s' := pullbackGlobalSection D p hp p' hp' f L s
  have hL' := isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL
  set g := pullbackVanishingLocusProjection D p hp p' hp' f L s hL
  have hgP := isProper_pullbackVanishingLocusProjection D p hp p' hp' f L s hL hf
  have hgB := pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase
  have hE := isGood_vanishingLocus D p hp L s
  have hE' : D.IsGood (E'.1.ι ≫ p') := isGood_vanishingLocus D p' hp' L' s'
  set γ := gysinCycleMap D p' E' hE' k (sectionGysinRule D p' hp' L' s' k hL') α'
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  refine isRationallyEquivalentToZeroCanonical_of_isRationallyEquivalentToZeroWithinCanonical_closedPushforward
    D p hp E.1 E.2 k ?_
  -- the pushforward of the right-hand side to `X`
  have hEι := isProper_closedSubspaces_ι D hp.1 E
  have hE'ι := isProper_closedSubspaces_ι D hp'.1 E'
  have hrhs : cycleGroupClosedPushforward D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2 p
      hp.2.2 (E.1.ι ≫ p) rfl k
      (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgB hgP.2.1.2 k γ) =
      properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 k
        (firstChernCapCycleMap D p' hp' k (sectionGysinChernRule D p' hp' L' s' hL' k) α') := by
    rw [← cycleGroupClosedPushforward_sectionGysin_eq D p' hp' L' s' hL' k α',
      ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D p hp E.1 E.2 k,
      ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D p' hp' E'.1 E'.2 k,
      properCyclePushforward_comp D (E'.1.ι ≫ p') (E.1.ι ≫ p) p hE' hE hp hgB rfl hgP hEι,
      properCyclePushforward_comp D (E'.1.ι ≫ p') p' p hE' hp' hp rfl hfbase hE'ι hf]
    exact properCyclePushforward_congr D (E'.1.ι ≫ p') hE' p hp
      (pullbackVanishingLocusProjection_comm D p hp p' hp' f L s hL) _ _ _ _ k γ
  rw [map_sub, cycleGroupClosedPushforward_sectionGysin_eq D p hp L s hL k, hrhs, ← neg_sub]
  refine IsRationallyEquivalentToZeroWithinCanonical.neg
    (IsRationallyEquivalentToZeroWithinCanonical.mono
      (isRationallyEquivalentToZeroWithinCanonical_properPushforward_firstChernCapCycleMap_sub D
        hp' hp hfbase hf k _ _ α'
        (fun W' => if W'.subspace ≤ E'.1 then subspacePointSet D.site D.base D.base_mem X
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
              (D.isDecentSpace_of_isGood p hp) f.hom W').subspace else ∅)
        (fun W' => by
          dsimp only
          split_ifs
          · exact le_rfl
          · exact Set.empty_subset _)
        (fun W' hW' => ?_)) ?_)
  · dsimp only
    by_cases hle' : W'.subspace ≤ E'.1
    · rw [if_pos hle']
      exact hle W' (α'.2.2 W' hW') hle' _
    · rw [if_neg hle', hnot W' (α'.2.2 W' hW') hle', smul_zero]
      exact isRationallyEquivalentToZeroWithinCanonical_zero D p hp k ∅
  · refine Set.iUnion_subset fun j => ?_
    dsimp only
    split_ifs with hle'
    · exact subspacePointSet_mono_of_le D (closureImage_le_of_le D p hp f.hom E E' g
        (pullbackVanishingLocusProjection_comm D p hp p' hp' f L s hL) j.1 hle')
    · exact Set.empty_subset _

end Reduction

end AlgebraicGeometry.Space

end
