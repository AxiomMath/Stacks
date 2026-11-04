module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IteratedChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ClosedSubschemeCycleRules
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerExpansion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product

/-!
# The smash power of `[x] - [x']` as an iterated first Chern class cap product

Let `k` be algebraically closed, `X` a variety of dimension one over `k`, `x`, `x'` rational
points of `X`, and `ℒ` an invertible module on `X` with `c₁(ℒ) ∩ [X] = [x] - [x']` in
`CH_0(X)` (for a smooth curve, `ℒ = 𝒪_X(x - x')`). Stacks 0FH9 observes that

  `αₙ = ([x] - [x']) × ⋯ × ([x] - [x']) = c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒₙ) ∩ [Xⁿ]`,

with `ℒᵢ = prᵢ^*ℒ`. This file proves it, for the smash power
`Stacks.Chow.smashPointDifference` on the fibre power `Xⁿ` parenthesized from the left.

## The argument

Write `Y = X^n` and `Y ×_k X = X^{n+1}`, with projections `pr₁`, `pr₂`, and for a rational point
`x` let `j_x = (1, x) : Y ⟶ Y ×_k X`, a closed immersion (`Stacks.Chow.sectionSlice`). Then:

* `c₁(pr₂^*ℒ) ∩ [Y ×_k X] = pr₂^*(c₁(ℒ) ∩ [X]) = pr₂^*[x] - pr₂^*[x']`, by Stacks 02SS and the
  flat pullback of a fundamental class;
* `pr₂^*[x] = j_{x*}[Y]`, because `j_x` is the base change of `x` along `pr₂` and flat pullback of
  the cycle of a closed subscheme is the cycle of its inverse image (Stacks 02RE);
* `c₁(pr₁^*ℒᵢ) ∩ ⋯ ∩ j_{x*}[Y] = j_{x*}(c₁(ℒᵢ) ∩ ⋯ ∩ [Y])`, by the projection formula, since
  `j_x^* pr₁^* = 1`;
* `αₙ × [x] = j_{x*} αₙ`, since `αₙ` is a signed sum of rational points
  (`Stacks.Chow.smashPointDifference_cycle_eq_sum`) and `[p] × [x] = [(p, x)] = j_{x*}[p]`.

Together these give the recursion `α_{n+1} = j_{x*}αₙ - j_{x'*}αₙ` for both sides.

## Main definitions

* `Stacks.Chow.sectionSlice` — the closed immersion `(1, x) : Y ⟶ Y ×_k X`.
* `Stacks.Chow.smashProjection` — the projections `prᵢ : Xⁿ ⟶ X` of the smash power.

## Main results

* `Stacks.Chow.smashPointDifference_cycle_eq_iteratedChernCapOnChow` — **deliverable**:
  `αₙ = c₁(pr₀^*ℒ) ∩ ⋯ ∩ c₁(pr_{n-1}^*ℒ) ∩ [Xⁿ]` in `CH_0(Xⁿ)`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-! ### The slice through a rational point -/

section Slice

variable {X Y : Scheme.{u}} (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
  (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _)

/-- The slice `(1, x) : Y ⟶ Y ×_k X` through a rational point `x` of `X`. -/
def sectionSlice : Y ⟶ pullback g f :=
  pullback.lift (𝟙 Y) (g ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id])

omit [LocallyOfFiniteType g] [LocallyOfFiniteType f] in
/-- The slice followed by the first projection is the identity of `Y`. -/
@[reassoc (attr := simp)]
theorem sectionSlice_fst : sectionSlice k g f x hx ≫ pullback.fst g f = 𝟙 Y :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType g] [LocallyOfFiniteType f] in
/-- The slice followed by the second projection is `g ≫ x`. -/
@[reassoc (attr := simp)]
theorem sectionSlice_snd : sectionSlice k g f x hx ≫ pullback.snd g f = g ≫ x :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType g] [LocallyOfFiniteType f] in
/-- The slice is the base change of `x` along `pr₂ : Y ×_k X ⟶ X`. -/
theorem isPullback_sectionSlice :
    IsPullback (sectionSlice k g f x hx) g (pullback.snd g f) x := by
  refine IsPullback.of_right (h₁₂ := pullback.fst g f) (h₂₂ := f) (v₁₃ := g) ?_ (by simp)
    (IsPullback.of_hasPullback g f)
  rw [sectionSlice_fst, hx]
  exact IsPullback.of_id_fst

include hx in
omit [LocallyOfFiniteType f] in
/-- A rational point is a closed immersion. -/
theorem isClosedImmersion_point : IsClosedImmersion x :=
  isClosedImmersion_of_comp_eq_id f x hx

/-- The slice through a rational point is a closed immersion. -/
instance isClosedImmersion_sectionSlice : IsClosedImmersion (sectionSlice k g f x hx) :=
  haveI := isClosedImmersion_point k f x hx
  MorphismProperty.of_isPullback (isPullback_sectionSlice k g f x hx).flip inferInstance

omit [LocallyOfFiniteType g] [LocallyOfFiniteType f] in
/-- The structure morphism of the product, through the slice, is the structure morphism of
`Y`. -/
theorem sectionSlice_comp_structure :
    sectionSlice k g f x hx ≫ (pullback.fst g f ≫ g) = g := by
  rw [sectionSlice_fst_assoc]

/-- **Pushforward along the slice of a rational point** is the rational point of the product:
`j_{x*}[p] = [(p, x)]`. -/
theorem properChowPushforward_sectionSlice_rationalPointChowClass
    (p : (fieldChowSituation k).S ⟶ Y) (hp : p ≫ g = 𝟙 _) :
    properChowPushforward (fieldChowSituation k) g (pullback.fst g f ≫ g)
        (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (rationalPointChowClass k g p hp) =
      rationalPointChowClass k (pullback.fst g f ≫ g)
        (pullback.lift (f := g) (g := f) p x (hp.trans hx.symm))
        (by rw [pullback.lift_fst_assoc, hp]) := by
  have := isClosedImmersion_of_comp_eq_id g p hp
  have he : p ≫ sectionSlice k g f x hx =
      pullback.lift (f := g) (g := f) p x (hp.trans hx.symm) :=
    pullback.hom_ext (by rw [Category.assoc, sectionSlice_fst, Category.comp_id, pullback.lift_fst])
      (by rw [Category.assoc, sectionSlice_snd, reassoc_of% hp, pullback.lift_snd])
  have : IsClosedImmersion (p ≫ sectionSlice k g f x hx) := inferInstance
  have : IsClosedImmersion (pullback.lift (f := g) (g := f) p x (hp.trans hx.symm)) :=
    he ▸ inferInstance
  show QuotientAddGroup.mk' _ (properPushforward _ g (pullback.fst g f ≫ g)
      (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) 0
      (cycleAssociatedToClosedSubscheme _ g p 0)) = QuotientAddGroup.mk' _ _
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (Iso.refl _)
    (by rw [Iso.refl_hom, Category.id_comp, he]) 0)

end Slice

/-! ### The fibre power is a variety of the expected dimension -/

section Variety

attribute [local instance] SmashPowerData.finiteType

variable {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)

/-- `Spec k` is a variety over `k`. -/
instance isVariety_id_spec : IsVariety k (𝟙 (Spec (.of k))) where

/-- Over an algebraically closed field, the `n`-fold fibre power of a variety of dimension `d`
is a variety of dimension `n d`. -/
theorem isVariety_smashPointDifference [IsAlgClosed k] [IsVariety k f] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (n : ℕ) :
    IsVariety k (smashPointDifference k f x x' hx hx' n).Y.hom ∧
      topologicalKrullDim (smashPointDifference k f x x' hx hx' n).Y.left =
        ((n * d : ℕ) : WithBot ℕ∞) := by
  induction n with
  | zero =>
    refine ⟨isVariety_id_spec k, ?_⟩
    show topologicalKrullDim (Spec (.of k)) = _
    rw [zero_mul, Nat.cast_zero]
    exact topologicalKrullDim_eq_zero_of_subsingleton
  | succ n ih =>
    obtain ⟨hv, hdim⟩ := ih
    refine ⟨isVariety_pullback k _ f, ?_⟩
    show topologicalKrullDim
      ↑(pullback (smashPointDifference k f x x' hx hx' n).Y.hom f : Scheme.{u}) = _
    rw [topologicalKrullDim_pullback_of_isVariety k, hdim, hd, ← Nat.cast_add, add_mul, one_mul]

end Variety

/-! ### The last factor -/

section LastFactor

variable {X Y : Scheme.{u}} (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
  (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
  (n : ℕ) (hrel : AlgebraicGeometry.RelativeDimension (pullback.snd g f) n)

/-- **The flat pullback of a rational point along `pr₂ : Y ×_k X ⟶ X` is the slice through
it**: `pr₂^*[x] = j_{x*}[Y]` in `CH_n(Y ×_k X)`, for `pr₂` flat of relative dimension `n`. This is
Stacks 02RE for the closed subscheme `x`, whose inverse image under `pr₂` is the slice. -/
theorem flatPullback_rationalPointChowClass_pullbackSnd :
    flatPullbackChowOfRelativeDimension (fieldChowSituation k) (pullback.fst g f ≫ g) f
        (pullback.snd g f) pullback.condition.symm n hrel 0 (rationalPointChowClass k f x hx) =
      properChowPushforward (fieldChowSituation k) g (pullback.fst g f ≫ g)
        (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) ((0 : ℤ) + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) g ((0 : ℤ) + n)) := by
  have := isClosedImmersion_point k f x hx
  have hZ : schemeDeltaDimension (fieldChowSituation k) (x ≫ f) ≤ ((0 : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le _ f x fun w ↦
      (relativeDimension_section_eq_zero k f x hx w).le
  have hsq := (isPullback_sectionSlice k g f x hx).flip
  have : IsClosedImmersion (𝟙 Y ≫ sectionSlice k g f x hx) := by
    rw [Category.id_comp]; infer_instance
  show QuotientAddGroup.mk' _ (flatPullback _ _ _ _ _ n hrel 0
      (cycleAssociatedToClosedSubscheme _ f x 0)) =
    QuotientAddGroup.mk' _ (properPushforward _ g (pullback.fst g f ≫ g)
      (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) _
      (cycleAssociatedToClosedSubscheme _ g (𝟙 Y) _))
  rw [flatPullback_cycleAssociatedToClosedSubscheme_snd _ _ _ _ _ n hrel 0 x hZ,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ hsq.isoPullback.symm
    (by rw [Iso.symm_hom, Category.id_comp, hsq.isoPullback_inv_snd]) _)

include hrel in
/-- **The last first Chern class.** For `ℒ` on `X` with `c₁(ℒ) ∩ [X] = [x] - [x']` and `pr₂`
flat of relative dimension `n`,

  `c₁(pr₂^*ℒ) ∩ [Y ×_k X] = j_{x*}[Y] - j_{x'*}[Y]`   in `CH_n(Y ×_k X)`. -/
theorem invCap_pullbackSnd_capOnChow_fundamentalChowClass (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) f L).capOnChow (fieldChowSituation k) f 0
      (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) =
        pointDifference k f x x' hx hx')
    (hdimX : schemeDeltaDimension (fieldChowSituation k) f ≤ (((0 : ℤ) + 1 : ℤ) : EInt)) :
    (invCap (fieldChowSituation k) (pullback.fst g f ≫ g)
        ((Scheme.Modules.pullback (pullback.snd g f)).obj L)).capOnChow (fieldChowSituation k)
        (pullback.fst g f ≫ g) ((0 : ℤ) + n)
        (fundamentalChowClass (fieldChowSituation k) (pullback.fst g f ≫ g) ((0 : ℤ) + n + 1)) =
      properChowPushforward (fieldChowSituation k) g (pullback.fst g f ≫ g)
          (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) ((0 : ℤ) + n)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) g ((0 : ℤ) + n)) -
        properChowPushforward (fieldChowSituation k) g (pullback.fst g f ≫ g)
          (sectionSlice k g f x' hx') (sectionSlice_comp_structure k g f x' hx') ((0 : ℤ) + n)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) g ((0 : ℤ) + n)) := by
  have hxy : flatPullbackChowOfRelativeDimension (fieldChowSituation k) (pullback.fst g f ≫ g) f
      (pullback.snd g f) pullback.condition.symm n hrel (0 + 1)
        (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) ≍
      fundamentalChowClass (fieldChowSituation k) (pullback.fst g f ≫ g) ((0 : ℤ) + n + 1) := by
    rw [flatPullbackChowOfRelativeDimension_fundamentalChowClass _ _ _ _ _ n hrel _ hdimX]
    have e : (0 : ℤ) + 1 + n = 0 + n + 1 := by ring
    rw [e]
  rw [← flatPullbackChowOfRelativeDimension_invCap_capOnChow _ _ _ _ _ n hrel L 0 _ _ hxy, hL,
    pointDifference, map_sub, flatPullback_rationalPointChowClass_pullbackSnd k g f x hx n hrel,
    flatPullback_rationalPointChowClass_pullbackSnd k g f x' hx' n hrel]

end LastFactor

/-! ### Exterior product with a rational point -/

section PointProduct

variable {X Y : Scheme.{u}} (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
  (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _)

/-- **The exterior product of a signed sum of rational points with a rational point `x` is its
pushforward along the slice through `x`**: `(∑ cᵢ [pᵢ]) × [x] = j_{x*}(∑ cᵢ [pᵢ])`. -/
theorem chowExteriorProduct_sum_tmul_rationalPointChowClass {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (P : ι → ((fieldChowSituation k).S ⟶ Y)) (hP : ∀ i, P i ≫ g = 𝟙 _) :
    chowExteriorProduct (fieldChowSituation k) (fieldChowSituation_dimensionFunction_of_isClosed k)
        g f 0 0 ((∑ i ∈ s, c i • rationalPointChowClass k g (P i) (hP i)) ⊗ₜ
          rationalPointChowClass k f x hx) =
      properChowPushforward (fieldChowSituation k) g (pullback.fst g f ≫ g)
        (sectionSlice k g f x hx) (sectionSlice_comp_structure k g f x hx) 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (∑ i ∈ s, c i • rationalPointChowClass k g (P i) (hP i)) := by
  rw [TensorProduct.sum_tmul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← TensorProduct.smul_tmul', map_zsmul, map_zsmul,
    chowExteriorProduct_rationalPointChowClass,
    properChowPushforward_sectionSlice_rationalPointChowClass]

omit [LocallyOfFiniteType f] in
/-- Pulling back along the slice undoes pulling back along the first projection:
`j_x^*(pr₁ ≫ pr)^*ℒ ≅ pr^*ℒ`, so the two have the same first Chern class cap. -/
theorem invCap_capOnChow_sectionSlice_pullback (pr : Y ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (m : ℤ) (z : chowGroup (fieldChowSituation k) g (m + 1)) :
    (invCap (fieldChowSituation k) g ((Scheme.Modules.pullback (sectionSlice k g f x hx)).obj
        ((Scheme.Modules.pullback (pullback.fst g f ≫ pr)).obj L))).capOnChow
        (fieldChowSituation k) g m z =
      (invCap (fieldChowSituation k) g ((Scheme.Modules.pullback pr).obj L)).capOnChow
        (fieldChowSituation k) g m z := by
  have e : (Scheme.Modules.pullback (sectionSlice k g f x hx)).obj
      ((Scheme.Modules.pullback (pullback.fst g f ≫ pr)).obj L) ≅
        (Scheme.Modules.pullback pr).obj L :=
    (Scheme.Modules.pullbackComp (sectionSlice k g f x hx) (pullback.fst g f ≫ pr)).app L ≪≫
      eqToIso (congrArg (fun h => (Scheme.Modules.pullback h).obj L)
        (sectionSlice_fst_assoc k g f x hx pr))
  exact invCap_capOnChow_congr (fieldChowSituation k) g _ _ e m z

end PointProduct

/-! ### The smash power as an iterated cap product -/

section Smash

attribute [local instance] SmashPowerData.finiteType

variable {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
  (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)

/-- **The projections `prᵢ : Xⁿ ⟶ X`** of the fibre power carrying the smash power, the last
one being the newest factor. -/
def smashProjection : (n : ℕ) → Fin n →
    ((smashPointDifference k f x x' hx hx' n).Y.left ⟶ X)
  | 0 => Fin.elim0
  | n + 1 => Fin.lastCases (pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom f)
      fun i => pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        smashProjection n i

/-- The last projection of `Xⁿ⁺¹` is the second projection of the fibre product. -/
@[simp]
theorem smashProjection_last (n : ℕ) :
    smashProjection k f x x' hx hx' (n + 1) (Fin.last n) =
      pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom f := by
  simp [smashProjection]

/-- The `i`-th projection of `Xⁿ⁺¹`, for `i < n`, is the first projection to `Xⁿ` followed by
the `i`-th projection of `Xⁿ`. -/
@[simp]
theorem smashProjection_castSucc (n : ℕ) (i : Fin n) :
    smashProjection k f x x' hx hx' (n + 1) i.castSucc =
      pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        smashProjection k f x x' hx hx' n i := by
  simp [smashProjection]

/-- **The smash power is a combination of slices.** `α_{n+1} = j_{x*}αₙ - j_{x'*}αₙ`. -/
theorem smashPointDifference_succ_cycle (n : ℕ) :
    (smashPointDifference k f x x' hx hx' (n + 1)).cycle =
      properChowPushforward (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
          (pullback.fst _ f ≫ _) (sectionSlice k _ f x hx)
          (sectionSlice_comp_structure k _ f x hx) 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
          (smashPointDifference k f x x' hx hx' n).cycle -
        properChowPushforward (fieldChowSituation k)
          (smashPointDifference k f x x' hx hx' n).Y.hom
          (pullback.fst _ f ≫ _) (sectionSlice k _ f x' hx')
          (sectionSlice_comp_structure k _ f x' hx') 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
          (smashPointDifference k f x x' hx hx' n).cycle := by
  show chowExteriorProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k) _ f 0 0
      ((smashPointDifference k f x x' hx hx' n).cycle ⊗ₜ
        (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx')) = _
  rw [smashPointDifference_cycle_eq_sum, TensorProduct.tmul_sub, map_sub,
    chowExteriorProduct_sum_tmul_rationalPointChowClass,
    chowExteriorProduct_sum_tmul_rationalPointChowClass]

/-- Fundamental classes in equal degrees are heterogeneously equal. -/
theorem fundamentalChowClass_heq_of_eq {T : Scheme.{u}} (C : ChowSituation.{u}) (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {d₁ d₂ : ℤ} (h : d₁ = d₂) :
    fundamentalChowClass C sT d₁ ≍ fundamentalChowClass C sT d₂ := by
  subst h; rfl

/-- **The cycle computation of Stacks 0FH9.** Let `k` be algebraically closed, `X` a variety of
dimension one over `k`, `x`, `x'` rational points and `ℒ` invertible on `X` with
`c₁(ℒ) ∩ [X] = [x] - [x']` in `CH_0(X)`. Then the `n`-th smash power of `[x] - [x']` is

  `αₙ = c₁(pr₀^*ℒ) ∩ ⋯ ∩ c₁(pr_{n-1}^*ℒ) ∩ [Xⁿ]`   in `CH_0(Xⁿ)`,

the fundamental class `[Xⁿ]` taken in the degree `0 + n` the iterated cap product starts from. -/
theorem smashPointDifference_cycle_eq_iteratedChernCapOnChow [IsAlgClosed k] [IsVariety k f]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) f L).capOnChow (fieldChowSituation k) f 0
      (fundamentalChowClass (fieldChowSituation k) f (0 + 1)) =
        pointDifference k f x x' hx hx') (n : ℕ) :
    (smashPointDifference k f x x' hx hx' n).cycle =
      iteratedChernCapOnChow (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
        (List.ofFn fun i => invCap (fieldChowSituation k) _
          ((Scheme.Modules.pullback (smashProjection k f x x' hx hx' n i)).obj L)) 0
        (fundamentalChowClass (fieldChowSituation k) _ (0 + ((List.ofFn fun i =>
          invCap (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
            ((Scheme.Modules.pullback (smashProjection k f x x' hx hx' n i)).obj L)).length :
              ℤ))) := by
  have hdimX : schemeDeltaDimension (fieldChowSituation k) f ≤ (((0 : ℤ) + 1 : ℤ) : EInt) := by
    rw [zero_add, schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq f
      (n := 1) (by rw [hdim]; rfl)]
    rfl
  induction n with
  | zero =>
    refine chowGroup_eq_of_heq (fieldChowSituation k) _ (HEq.symm ?_)
    refine (iteratedChernCapOnChow_heq_of_eq (fieldChowSituation k) _ List.ofFn_zero 0
      (HEq.refl _)).trans ?_
    refine (iteratedChernCapOnChow_nil_heq (fieldChowSituation k) _ 0 _).trans ?_
    exact fundamentalChowClass_heq_of_eq (fieldChowSituation k) _ (by simp)
  | succ n ih =>
    obtain ⟨hv, hdY⟩ := isVariety_smashPointDifference k f x x' hx hx' 1
      (by rw [hdim]; rfl) n
    have hg : AlgebraicGeometry.RelativeDimension
        (smashPointDifference k f x x' hx hx' n).Y.hom n :=
      relativeDimension_of_flat_of_isVariety k _ (𝟙 _) _ (Category.comp_id _) n (by
        rw [hdY, mul_one]
        rw [topologicalKrullDim_eq_zero_of_subsingleton, zero_add])
    have hrel : AlgebraicGeometry.RelativeDimension
        (pullback.snd (smashPointDifference k f x x' hx hx' n).Y.hom f) n :=
      relativeDimension_pullbackSnd _ hg f
    -- the notation of the step
    have hlast := invCap_pullbackSnd_capOnChow_fundamentalChowClass k
      (smashPointDifference k f x x' hx hx' n).Y.hom f x x' hx hx' n hrel L hL hdimX
    -- the slice formula, on the iterated cap of the first `n` factors
    have hslice : ∀ (y : (fieldChowSituation k).S ⟶ X) (hy : y ≫ f = 𝟙 _),
        iteratedChernCapOnChow (fieldChowSituation k)
            (pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
              (smashPointDifference k f x x' hx hx' n).Y.hom)
            (List.ofFn fun j : Fin n => invCap (fieldChowSituation k) _
              ((Scheme.Modules.pullback (pullback.fst _ f ≫
                smashProjection k f x x' hx hx' n j)).obj L)) 0
            (properChowPushforward (fieldChowSituation k)
              (smashPointDifference k f x x' hx hx' n).Y.hom
              (pullback.fst _ f ≫ _) (sectionSlice k _ f y hy)
              (sectionSlice_comp_structure k _ f y hy) _
              (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
              (fundamentalChowClass (fieldChowSituation k) _ (0 + ((List.ofFn fun j : Fin n =>
                invCap (fieldChowSituation k) (pullback.fst
                  (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
                  (smashPointDifference k f x x' hx hx' n).Y.hom)
                ((Scheme.Modules.pullback (pullback.fst _ f ≫
                  smashProjection k f x x' hx hx' n j)).obj L)).length : ℤ)))) =
          properChowPushforward (fieldChowSituation k)
              (smashPointDifference k f x x' hx hx' n).Y.hom
              (pullback.fst _ f ≫ _) (sectionSlice k _ f y hy)
              (sectionSlice_comp_structure k _ f y hy) 0
              (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
              (iteratedChernCapOnChow (fieldChowSituation k)
                (smashPointDifference k f x x' hx hx' n).Y.hom
                (List.ofFn fun i => invCap (fieldChowSituation k) _
                  ((Scheme.Modules.pullback (smashProjection k f x x' hx hx' n i)).obj L)) 0
                (fundamentalChowClass (fieldChowSituation k) _ (0 + ((List.ofFn fun i =>
                  invCap (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
                    ((Scheme.Modules.pullback
                      (smashProjection k f x x' hx hx' n i)).obj L)).length : ℤ)))) := by
      intro y hy
      symm
      rw [← iteratedChernCapOnChow_congr_forall₂ (fieldChowSituation k) _
        (forall₂_ofFn fun j m z => invCap_capOnChow_sectionSlice_pullback k _ f y hy
          (smashProjection k f x x' hx hx' n j) L m z) 0
        (fundamentalChowClass (fieldChowSituation k) _ (0 + ((List.ofFn fun j : Fin n =>
          invCap (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
            ((Scheme.Modules.pullback (sectionSlice k _ f y hy)).obj
              ((Scheme.Modules.pullback (pullback.fst _ f ≫
                smashProjection k f x x' hx hx' n j)).obj L))).length : ℤ)))
        _ (fundamentalChowClass_heq_of_eq _ _ (by simp))]
      refine properChowPushforward_iteratedChernCapOnChow_ofFn (fieldChowSituation k) _ _
        (sectionSlice k _ f y hy) (sectionSlice_comp_structure k _ f y hy) _ 0 _ _ ?_
      exact properChowPushforward_heq _ _ _ _ _ (by simp) (fundamentalChowClass_heq_of_eq _ _
        (by simp))
    -- the last factor, in the degree the first `n` factors start from
    set Os := List.ofFn fun j : Fin n => invCap (fieldChowSituation k)
      (pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom)
      ((Scheme.Modules.pullback (pullback.fst _ f ≫
        smashProjection k f x x' hx hx' n j)).obj L) with hOs
    set O := invCap (fieldChowSituation k)
      (pullback.fst (smashPointDifference k f x x' hx hx' n).Y.hom f ≫
        (smashPointDifference k f x x' hx hx' n).Y.hom)
      ((Scheme.Modules.pullback (pullback.snd
        (smashPointDifference k f x x' hx hx' n).Y.hom f)).obj L) with hO
    have hlast' : ∀ (d : ℤ) (_ : d = 0 + n), O.capOnChow (fieldChowSituation k) _ d
        (fundamentalChowClass (fieldChowSituation k) _ (d + 1)) =
      properChowPushforward (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
          (pullback.fst _ f ≫ _) (sectionSlice k _ f x hx)
          (sectionSlice_comp_structure k _ f x hx) d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) _ d) -
        properChowPushforward (fieldChowSituation k) (smashPointDifference k f x x' hx hx' n).Y.hom
          (pullback.fst _ f ≫ _) (sectionSlice k _ f x' hx')
          (sectionSlice_comp_structure k _ f x' hx') d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) _ d) := by
      rintro d rfl
      exact hlast
    have hlen : (Os.length : ℤ) = n := by simp [hOs]
    rw [smashPointDifference_succ_cycle, ih, ← hslice x hx, ← hslice x' hx', ← map_sub,
      ← hlast' _ (by rw [hlen])]
    -- the list of `n + 1` factors is the first `n` followed by the last
    have hlist : (List.ofFn fun i : Fin (n + 1) => invCap (fieldChowSituation k)
        (smashPointDifference k f x x' hx hx' (n + 1)).Y.hom
        ((Scheme.Modules.pullback (smashProjection k f x x' hx hx' (n + 1) i)).obj L)) =
          Os ++ [O] := by
      rw [List.ofFn_succ', List.concat_eq_append, hOs, hO]
      simp only [smashProjection_castSucc, smashProjection_last]
      rfl
    symm
    refine (chowGroup_eq_of_heq (fieldChowSituation k) _ (iteratedChernCapOnChow_heq_of_eq
      (fieldChowSituation k) _ hlist 0
      (fundamentalChowClass_heq_of_eq (fieldChowSituation k) _ (by rw [hlist])))).trans ?_
    show iteratedChernCapOnChow (fieldChowSituation k) (pullback.fst _ f ≫ _) (Os ++ [O]) 0
      (fundamentalChowClass (fieldChowSituation k) (pullback.fst _ f ≫ _)
        (0 + ((Os ++ [O]).length : ℤ))) = _
    rw [iteratedChernCapOnChow_append (fieldChowSituation k) _ Os [O] 0 _
      (fundamentalChowClass (fieldChowSituation k) _ (0 + (Os.length : ℤ) + ([O].length : ℤ)))
      (fundamentalChowClass_heq_of_eq (fieldChowSituation k) _
        (by rw [List.length_append, List.length_singleton]; push_cast; ring)),
      iteratedChernCapOnChow_singleton_eq (fieldChowSituation k) _ O _ _
        (fundamentalChowClass (fieldChowSituation k) _ (0 + (Os.length : ℤ) + 1))
        (fundamentalChowClass_heq_of_eq (fieldChowSituation k) _ (by simp))]

/-- The projections are morphisms over `k`. -/
theorem smashProjection_comp (n : ℕ) (i : Fin n) :
    smashProjection k f x x' hx hx' n i ≫ f = (smashPointDifference k f x x' hx hx' n).Y.hom := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last =>
      rw [smashProjection_last]
      exact pullback.condition.symm
    | cast i =>
      rw [smashProjection_castSucc]
      show pullback.fst _ f ≫ smashProjection k f x x' hx hx' n i ≫ f = pullback.fst _ f ≫ _
      rw [ih]

/-- The projections `prᵢ : Xⁿ ⟶ X` are locally of finite type. -/
instance locallyOfFiniteType_smashProjection (n : ℕ) (i : Fin n) :
    LocallyOfFiniteType (smashProjection k f x x' hx hx' n i) := by
  have : LocallyOfFiniteType (smashProjection k f x x' hx hx' n i ≫ f) := by
    rw [smashProjection_comp]; infer_instance
  exact LocallyOfFiniteType.of_comp (f := smashProjection k f x x' hx hx' n i) (g := f) this

end Smash

end Stacks.Chow

end
