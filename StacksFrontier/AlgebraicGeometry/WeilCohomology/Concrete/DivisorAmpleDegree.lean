module

public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.StrictColength
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionGysinCap
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsTotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.DirectImage
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalDiagonalSelfIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeChow

/-!
# The degree of `[D] · (c₁(𝓛) ∩ [X])` on a surface

Let `k` be a field, let `X` be a smooth projective scheme over `k` of pure dimension `2`, let
`D ⊆ X` be a nonempty effective Cartier divisor and let `𝓛` be an ample invertible `𝒪_X`-module.
Write `θ = c₁(𝓛) ∩ [X] ∈ CH^1(X)` (the degree-one part of the total Chern class of `𝓛` capped
with the fundamental class, part by part, `Stacks.Chow.totalChowClassCapFundamental`) and
`[D] ∈ CH^1(X)` for the class of the closed subscheme `D`. Then

  `deg([D] · θ) = deg_𝓛(D) > 0`,

the degree on the left being that of zero cycles on `CH^2(X) = CH_0(X)` and `deg_𝓛(D)` the
degree of `D` with respect to `𝓛` (Stacks 0BEW), which is positive (Stacks 0BEV).

The computation: `D ⟶ X` is a regular immersion (an effective Cartier divisor is locally cut out
by a nonzerodivisor) and `D` has pure dimension `1` (a relative effective Cartier divisor drops the
relative dimension by one, and over a field every morphism is flat), so by Stacks 0FFE
`[D] · θ = i_*(i^!θ)`, and `i^!(c₁(𝓛) ∩ [X]) = c₁(i^*𝓛) ∩ [D]_1`. Pushforward preserves degrees,
and by the projection formula (Stacks 02SU) and Stacks 0BFI
`deg(c₁(i^*𝓛) ∩ [D]_1) = deg(c₁(𝓛) ∩ i_*[D]_1) = (𝓛 · D) = deg_𝓛(D)`.

This is an input of the proof that the Hodge first Chern class of `𝒪_X(D)` does not vanish
(used for Stacks 0D1R).

## Main results

* `Stacks.WeilCohomology.relativeDimension_subschemeι_of_isEffectiveCartierDivisor`: an effective
  Cartier divisor on a scheme of pure dimension `n + 1` over a field has pure dimension `n`.
* `Stacks.WeilCohomology.chowCohomologyCapFundamentalClass_totalChernOfFiniteLocallyFree_one_heq`:
  for `𝓜` of rank one, the degree-one part of `c(𝓜)` capped with `[Y]_1` is `c₁(𝓜) ∩ [Y]_1`.
* `Stacks.WeilCohomology.capDegree_pullback_fundamentalChowClass`:
  `deg(c₁(i^*𝓛) ∩ [Z]_1) = deg(c₁(𝓛) ∩ [Z]_1)` for a closed subscheme `i : Z ⟶ X`.
* `Stacks.WeilCohomology.codimensionDegree_closedSubschemeClass_mul_firstChernCap`:
  `deg([D] · (c₁(𝓛) ∩ [X])) = deg_𝓛(D)`; it is positive by
  `AlgebraicGeometry.degreeWithRespectTo_pos` (Stacks 0BEV).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **An effective Cartier divisor on a scheme of pure dimension `n + 1` over a field has pure
dimension `n`.** Over a field every morphism is flat, so `D` is a relative effective Cartier divisor
(Stacks 062T), and these drop the relative dimension by one. -/
theorem relativeDimension_subschemeι_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (n + 1)) (D : X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.RelativeDimension (D.subschemeι ≫ p) n :=
  Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor p n hp D
    ⟨hD, Stacks.KunnethLowDegree.flat_of_spec_field _⟩

/-- **A nonempty effective Cartier divisor on a scheme of pure dimension `n + 1` over a field has
dimension `n`.** -/
theorem topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (n + 1)) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D ≠ ⊤) :
    topologicalKrullDim D.subscheme = (n : WithBot ℕ∞) := by
  have := Stacks.Divisors.nonempty_subscheme_of_ne_top D hD
  exact (equidimensional_and_topologicalKrullDim_of_relativeDimension k (D.subschemeι ≫ p) n
    (relativeDimension_subschemeι_of_isEffectiveCartierDivisor p n hp D)).2

/-- A class of `CH_m(Y)`, `m = 0`, heterogeneously equal to a zero cycle class, has its degree. -/
theorem chowDegree_chowGroupDegreeEquiv_eq_of_heq {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsProper sY] {m : ℤ} (hm : m = 0) (x : chowGroup (fieldChowSituation k) sY m)
    (y : chowGroup (fieldChowSituation k) sY 0) (h : x ≍ y) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) sY
        (IsLocalRing.closedPoint k) (chowGroupDegreeEquiv _ _ hm x) =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) sY
        (IsLocalRing.closedPoint k) y := by
  subst hm
  cases eq_of_heq h
  rfl

/-- **`c₁(𝓜) ∩ [Y]_1` through the total Chern class**: for `𝓜` of rank one, the degree-one part of
`c(𝓜)` capped with the fundamental class `[Y]_1` is the first Chern class cap `c₁(𝓜) ∩ [Y]_1` of
Stacks 02SO / 02TI. -/
theorem chowCohomologyCapFundamentalClass_totalChernOfFiniteLocallyFree_one_heq
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (M : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    haveI := GenuineChern.isInvertible_of_rank_one M
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
        (totalChernOfFiniteLocallyFree C sY M 1) ≍
      (invCap C sY M).capOnChow C sY ((0 : ℕ) : ℤ)
        (chowGroupCast C sY (by norm_num) (fundamentalChowClass C sY ((1 : ℕ) : ℤ))) := by
  rw [← chowCohomologyCap_fundamentalChowClass,
    totalChernOfFiniteLocallyFree_eq_totalChern C sY M 1]
  refine (Stacks.WeilDeRham.chowCohomologyCap_totalChern_heq C sY M 1 1 ((1 : ℕ) : ℤ) _).trans ?_
  rw [GenuineChern.chernCap_one_eq_invCap]
  exact capOnChow_heq C sY _ (by norm_num)
    ((chowGroupCast_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm)

/-- The degree of `c₁(𝓜) ∩ [Y]_1` is `capDegree` of the one-member family `𝓜` on `[Y]_1`. -/
theorem chowDegree_invCap_fundamentalChowClass {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsProper sY] (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (h : ((1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1) :
    haveI : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := ‹_›
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) sY
        (IsLocalRing.closedPoint k)
        ((invCap (fieldChowSituation k) sY M).capOnChow (fieldChowSituation k) sY ((0 : ℕ) : ℤ)
          (chowGroupCast (fieldChowSituation k) sY h
            (fundamentalChowClass (fieldChowSituation k) sY ((1 : ℕ) : ℤ)))) =
      capDegree k sY (fun _ : Fin 1 => M)
        (fundamentalChowClass (fieldChowSituation k) sY ((1 : ℕ) : ℤ)) := by
  rw [capDegree_succ, capDegree_zero]

/-- The degree of `c₁(i^*𝓛) ∩ [Z]_1` on a closed subscheme `i : Z ⟶ X` is the degree of
`c₁(𝓛) ∩ [Z]_1` on `X` (projection formula, Stacks 02SU). -/
theorem capDegree_pullback_fundamentalChowClass {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [Smooth f] (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    capDegree k (i ≫ f) (fun _ : Fin 1 => (Scheme.Modules.pullback i).obj L)
        (fundamentalChowClass (fieldChowSituation k) (i ≫ f) ((1 : ℕ) : ℤ)) =
      capDegree k f (fun _ : Fin 1 => L)
        (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f ((1 : ℕ) : ℤ))
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f i ((1 : ℕ) : ℤ))) := by
  have h1 := capDegree_properChowPushforward k f (i ≫ f) i rfl (fun _ : Fin 1 => L)
    (fundamentalChowClass (fieldChowSituation k) (i ≫ f) ((1 : ℕ) : ℤ))
  rw [properChowPushforward_fundamentalChowClass_eq_mk] at h1
  exact h1

/-- **`deg([D] · (c₁(𝓛) ∩ [X])) = deg_𝓛(D)`** for a nonempty effective Cartier divisor `D` and an
ample invertible module `𝓛` on a smooth projective scheme `X` of pure dimension `2` over a field.
Here `c₁(𝓛) ∩ [X] ∈ CH^1(X)` is the degree-one component of the total Chern class `c([𝓛])` capped
with the fundamental class, `[D] ∈ CH^1(X)` is the class of the closed subscheme `D`, the product is
the intersection product of Stacks 0FC0 and the degree is that of zero cycles on
`CH^2(X) = CH_0(X)`; `deg_𝓛(D)` is the degree of Stacks 0BEW. -/
theorem codimensionDegree_closedSubschemeClass_mul_firstChernCap
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom 2) (D : X.obj.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D ≠ ⊤) (L : X.obj.left.Modules)
    [SheafOfModules.IsInvertible X.obj.left.presheaf X.obj.left.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X.obj.left L) :
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
        (hM := @GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible X.obj.left L ‹_›)
    haveI : IsProper X.obj.hom := (SmoothProjectiveScheme.isProjective X).isProper
    codimensionDegree X 2 (codimensionChowGroupCongr X.obj.hom (by norm_num)
        (codimensionIntersectionProduct k X.obj.hom 1 ((1 : ℕ) : ℤ)
          (closedSubschemeClass X.obj.hom D.subschemeι 1)
          (totalChowClassCapFundamental X.obj.hom
            (totalChernKClass (fieldChowSituation k) X.obj.hom
              (VectorBundleKZero.classOf X.obj.left L)) 1))) =
      degreeWithRespectTo k X.obj.hom D.subschemeι 1
        (topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor X.obj.hom 1 hX D hD) L hL := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    @GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible X.obj.left L ‹_›
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have : IsProper X.obj.hom := (SmoothProjectiveScheme.isProjective X).isProper
  set i := D.subschemeι
  have hreg := Stacks.AlgebraicGeometry.isRegularImmersion_subschemeι_of_isEffectiveCartierDivisor
    D inferInstance
  have hY : AlgebraicGeometry.RelativeDimension (i ≫ X.obj.hom) 1 :=
    relativeDimension_subschemeι_of_isEffectiveCartierDivisor X.obj.hom 1 hX D
  set M := (Scheme.Modules.pullback i).obj L
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i L 1
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
  rw [codimensionIntersectionProduct_closedSubschemeClass X.obj.hom i hreg 1 hY 1 ((1 : ℕ) : ℤ),
    regularImmersionGysin_totalChowClassCapFundamental X.obj.hom i hreg 1 hY,
    res_totalChernKClass, VectorBundleKZero.pullback_classOf, totalChernKClass_classOf,
    codimensionChowGroupCongr_chowGroupToCodimension,
    codimensionDegree_chowGroupToCodimension X hX (IsLocalRing.closedPoint k) (sub_self _)]
  refine (congrArg _ (properChowPushforward_chowGroupDegreeEquiv _ _ _ i rfl (sub_self _) _
    (properPushforwardDescends _ _ _ _ _ _) _).symm).trans ?_
  refine (AlgebraicGeometry.chowDegree_properChowPushforward k X.obj.hom (i ≫ X.obj.hom) i rfl
    _).symm.trans ?_
  have : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2 M :=
    GenuineChern.isInvertible_of_rank_one M
  refine (chowDegree_chowGroupDegreeEquiv_eq_of_heq (i ≫ X.obj.hom) _ _ _
    (chowCohomologyCapFundamentalClass_totalChernOfFiniteLocallyFree_one_heq _ _ M)).trans ?_
  refine (chowDegree_invCap_fundamentalChowClass (i ≫ X.obj.hom) M _).trans ?_
  refine (capDegree_pullback_fundamentalChowClass X.obj.hom i L).trans ?_
  exact (intersectionNumber_eq_chowDegree_iteratedFirstChernCap k X.obj.hom i 1
    (topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor X.obj.hom 1 hX D hD)
    (fun _ => L)).symm

end Stacks.WeilCohomology

end
