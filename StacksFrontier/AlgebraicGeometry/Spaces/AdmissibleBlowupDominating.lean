module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupOfEffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupComposite
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupDivisorPullback
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A common dominating admissible blowup of an algebraic space

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S`, let
`U ⊆ X` be a quasi-compact open subspace and let `b i : X i ⟶ X` be finitely many `U`-admissible
blowups.  Stacks 086E asserts that there is a `U`-admissible blowup `b : X' ⟶ X` such that (a) `b`
factors as `X' ⟶ X i ⟶ X` for every `i`, and (b) each factor morphism `X' ⟶ X i` is itself an
admissible blowup.

The dominating blowup is the blowup of `X` in the **sum** of the centres — the closed subspace cut
out by the product of their defining ideals, Stacks 083U,
`AlgebraicGeometry.Space.sumClosedSubspaces` — iterated over the family by
`AlgebraicGeometry.Space.sumClosedSubspacesList`.  Its existence is Stacks 085Q together with the
universal property of Stacks 085U, `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_factoring` is **clause (a)** of Stacks 086E.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_factoring_isAdmissibleBlowup` is the same
  statement with **clause (b)** added.

## What this file has to supply about the sum

Three facts about `AlgebraicGeometry.Space.sumClosedSubspaces` which the development did not have
and which the admissibility of the dominating blowup needs; all three are read off the étale
scheme chart on which the sum is formed, where the sum is cut out by the product of the two chart
ideal sheaves (`AlgebraicGeometry.Space.chartKer_sumClosedSubspaces`).

* `AlgebraicGeometry.Space.isFinitePresentation_ι_sumClosedSubspaces`: the inclusion of a sum of
  two finitely presented closed subspaces is of finite presentation.  Finite presentation of a
  closed immersion is finite generation of the chart ideal over the affine opens of a surjective
  étale chart, Stacks 084Q in the unconditional form
  `AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart`, and a product
  of finite type ideal sheaves is of finite type.
* `AlgebraicGeometry.Space.subspacePointSet_sumClosedSubspaces`: the point set of a sum is the
  union of the point sets.  The support of a product of quasi-coherent ideal sheaves is the union
  of the supports, and the chart is surjective on points.
* `AlgebraicGeometry.Space.sumClosedSubspaces_comm` and
  `AlgebraicGeometry.Space.sumClosedSubspaces_assoc`: the sum is commutative and associative,
  because the product of chart ideal sheaves is.  With them every member of the family is a left
  summand of the sum, `AlgebraicGeometry.Space.exists_eq_sumClosedSubspaces_of_mem`, which is how
  clause (b) names the complementary centre.

## The empty family

For the empty family the dominating blowup is the identity of `X`, which is the blowup in the
**empty closed subspace** `AlgebraicGeometry.Space.emptyClosedSubspace`: a closed subspace with no
points is cut out on every chart by the unit ideal, so its inclusion is of finite presentation
(`AlgebraicGeometry.Space.isFinitePresentation_ι_emptyClosedSubspace`), it is disjoint from every
open subspace, and its inverse image along any morphism is an effective Cartier divisor, which
makes the identity final in the category of Stacks 085U.

## References

* [Stacks Project, Tag 086E](https://stacks.math.columbia.edu/tag/086E)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 083W](https://stacks.math.columbia.edu/tag/083W)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Finite presentation of the inclusion of a closed subspace, read as finite generation of the
chart ideal sheaf on the atlas chart over the affine opens there. -/
theorem isFinitePresentation_ι_iff_fg_chartKer (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    IsFinitePresentation B S hS Z.1.ι ↔
      ∀ A : ((BigFppfOver.toScheme B S hS).obj (atlasObj B S hS X)).affineOpens,
        ((chartKer B S hS X Z (atlasHom B S hS X)).ideal A).FG :=
  isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := ⟨Z.1.toFunctor, Z.2.1⟩) (X := X) (ObjectProperty.homMk Z.1.ι) Z.2.2
    (atlasHom_etale B S hS X) (atlasHom_surjective B S hS X)

/-- **The inclusion of a sum of two finitely presented closed subspaces is of finite
presentation.** -/
theorem isFinitePresentation_ι_sumClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (h₁ : IsFinitePresentation B S hS D₁.1.ι)
    (h₂ : IsFinitePresentation B S hS D₂.1.ι) :
    IsFinitePresentation B S hS (sumClosedSubspaces B S hS X D₁ D₂).1.ι := by
  rw [isFinitePresentation_ι_iff_fg_chartKer, chartKer_sumClosedSubspaces]
  exact Scheme.IdealSheafData.IsFiniteType.mul
    ((isFinitePresentation_ι_iff_fg_chartKer X D₁).1 h₁)
    ((isFinitePresentation_ι_iff_fg_chartKer X D₂).1 h₂)

/-- The topological range of the base change of the inclusion of a closed subspace along a
chart is the support of the chart ideal sheaf. -/
theorem range_rep_snd_eq_support_chartKer (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) :
    Set.range ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd q)) =
      ((chartKer B S hS X D q).support : Set ((BigFppfOver.toScheme B S hS).obj A)) :=
  (Stacks.AffineClosedUnion.support_ker_eq_range
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd q))).symm

/-- **The point set of a sum of two closed subspaces is the union of their point sets.**  On the
étale scheme chart on which the sum is formed the sum is cut out by the product of the two chart
ideal sheaves, and the support of a product of quasi-coherent ideal sheaves is the union of the
supports; the chart is surjective on points, so the identity descends to `X`. -/
theorem subspacePointSet_sumClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    subspacePointSet B S hS X.1 (sumClosedSubspaces B S hS X D₁ D₂).1 =
      subspacePointSet B S hS X.1 D₁.1 ∪ subspacePointSet B S hS X.1 D₂.1 := by
  have hsurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj (atlasObj B S hS X)) (atlasHom B S hS X)) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 (atlasObj B S hS X)
      (atlasHom B S hS X)).1 (atlasHom_surjective B S hS X)
  ext p
  obtain ⟨w, rfl⟩ := hsurj p
  rw [Set.mem_union, mem_range_pointsMap_ι_iff, mem_range_pointsMap_ι_iff,
    mem_range_pointsMap_ι_iff, range_rep_snd_eq_support_chartKer,
    range_rep_snd_eq_support_chartKer, range_rep_snd_eq_support_chartKer,
    chartKer_sumClosedSubspaces, Scheme.IdealSheafData.support_mul,
    TopologicalSpace.Closeds.coe_sup, Set.mem_union]

/-- Pullback-definedness along a morphism splits off the first summand of a sum of closed
subspaces. -/
theorem isPullbackDefined_left_of_sumClosedSubspaces {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (h : IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X D₁ D₂)) :
    IsPullbackDefined B S hS f D₁ :=
  isEffectiveCartierDivisor_left_of_sumClosedSubspaces B S hS Y _ _
    (isEffectiveCartierDivisor_of_subfunctor_eq
      (congrArg Subtype.val (preimage_sumClosedSubspaces B S hS f D₁ D₂)).symm h)

/-- Pullback-definedness along a morphism splits off the second summand of a sum of closed
subspaces. -/
theorem isPullbackDefined_right_of_sumClosedSubspaces {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (h : IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X D₁ D₂)) :
    IsPullbackDefined B S hS f D₂ :=
  isEffectiveCartierDivisor_right_of_sumClosedSubspaces B S hS Y _ _
    (isEffectiveCartierDivisor_of_subfunctor_eq
      (congrArg Subtype.val (preimage_sumClosedSubspaces B S hS f D₁ D₂)).symm h)

/-! ### The empty closed subspace -/

/-- **The empty closed subspace** of an algebraic space: the sheafification of the bottom
subfunctor.  It has no points. -/
def emptyClosedSubspace (X : AlgebraicSpaces B S hS) : ClosedSubspaces B S hS X.1 :=
  ⟨(⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS),
    isClosedSubspace_sheafify_bot B S hS X.2⟩

/-- The empty closed subspace has no points. -/
theorem subspacePointSet_emptyClosedSubspace (X : AlgebraicSpaces B S hS) :
    subspacePointSet B S hS X.1 (emptyClosedSubspace X).1 = ∅ :=
  range_pointsMap_ι_sheafify_bot B S hS X.1

/-- A closed subspace with no points is cut out on every chart by the unit ideal: the support of
its chart ideal sheaf is the topological range of the base-changed inclusion, which is empty. -/
theorem chartKer_eq_top_of_subspacePointSet_eq_empty (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : subspacePointSet B S hS X.1 D.1 = ∅)
    {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1) :
    chartKer B S hS X D q = ⊤ := by
  refine (Scheme.IdealSheafData.support_eq_bot_iff _).1 (SetLike.coe_injective ?_)
  rw [← range_rep_snd_eq_support_chartKer]
  refine Set.eq_empty_of_forall_notMem fun x ⟨y, hy⟩ => ?_
  obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS A x
  refine Set.notMem_empty (pointsMap B S hS (yoneda.obj A) q w) ?_
  rw [← h]
  exact (mem_range_pointsMap_ι_iff B S hS X D q w).2 ⟨y, hy⟩

/-- The inclusion of a closed subspace with no points is of finite presentation. -/
theorem isFinitePresentation_ι_of_subspacePointSet_eq_empty (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (h : subspacePointSet B S hS X.1 D.1 = ∅) :
    IsFinitePresentation B S hS D.1.ι := by
  rw [isFinitePresentation_ι_iff_fg_chartKer,
    chartKer_eq_top_of_subspacePointSet_eq_empty X D h]
  intro A
  simpa using Ideal.fg_top Γ((BigFppfOver.toScheme B S hS).obj (atlasObj B S hS X), A.1)

/-- The inclusion of the empty closed subspace is of finite presentation. -/
theorem isFinitePresentation_ι_emptyClosedSubspace (X : AlgebraicSpaces B S hS) :
    IsFinitePresentation B S hS (emptyClosedSubspace X).1.ι :=
  isFinitePresentation_ι_of_subspacePointSet_eq_empty X _
    (subspacePointSet_emptyClosedSubspace X)

/-- Every morphism pulls the empty closed subspace back to an effective Cartier divisor: the
inverse image has no points. -/
theorem isPullbackDefined_of_subspacePointSet_eq_empty {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (D : ClosedSubspaces B S hS X.1)
    (h : subspacePointSet B S hS X.1 D.1 = ∅) :
    IsPullbackDefined B S hS f D :=
  isEffectiveCartierDivisor_of_isEmpty_points B S hS Y _
    (isEmpty_points_preimage_of_disjoint_range B S hS f.hom D.1
      (by rw [show Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) = ∅ from h]
          exact disjoint_bot_right))

/-- **A closed subspace with no points has the identity as its blowup**, and the identity is a
`U`-admissible blowup for every open subspace `U`. -/
theorem isAdmissibleBlowup_id_emptyClosedSubspace (X : AlgebraicSpaces B S hS)
    (U : OpenSubspaces B S hS X.1) : IsAdmissibleBlowup B S hS U (𝟙 X) :=
  ⟨emptyClosedSubspace X, isFinitePresentation_ι_emptyClosedSubspace X,
    by rw [subspacePointSet_emptyClosedSubspace]; exact disjoint_bot_right,
    isBlowupAlong_id_of_isEffectiveCartierDivisor B S hS X _
      (isEffectiveCartierDivisor_of_isEmpty_points B S hS X _
        (isEmpty_points_sheafify_bot B S hS X.1))⟩

/-! ### The sum of a finite family of closed subspaces -/

/-- The sum of the closed subspaces indexed by a list, formed on top of a seed closed
subspace. -/
def sumClosedSubspacesList (X : AlgebraicSpaces B S hS) {ι : Type v}
    (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1) :
    List ι → ClosedSubspaces B S hS X.1
  | [] => Z₀
  | i :: l => sumClosedSubspaces B S hS X (Z i) (sumClosedSubspacesList X Z Z₀ l)

/-- The point set of the sum along a list is the union of the point set of the seed with those
of the listed closed subspaces; stated as the disjointness that the admissibility of a blowup in
that sum needs. -/
theorem disjoint_subspacePointSet_sumClosedSubspacesList (X : AlgebraicSpaces B S hS)
    {ι : Type v} (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1)
    (W : Set (points B S hS X.1))
    (hZ₀ : Disjoint W (subspacePointSet B S hS X.1 Z₀.1))
    (hZ : ∀ i, Disjoint W (subspacePointSet B S hS X.1 (Z i).1)) :
    ∀ l : List ι, Disjoint W (subspacePointSet B S hS X.1 (sumClosedSubspacesList X Z Z₀ l).1)
  | [] => hZ₀
  | i :: l => by
    rw [sumClosedSubspacesList, subspacePointSet_sumClosedSubspaces]
    exact (hZ i).union_right
      (disjoint_subspacePointSet_sumClosedSubspacesList X Z Z₀ W hZ₀ hZ l)

/-- The inclusion of the sum along a list is of finite presentation when the inclusions of the
seed and of the listed closed subspaces are. -/
theorem isFinitePresentation_ι_sumClosedSubspacesList (X : AlgebraicSpaces B S hS)
    {ι : Type v} (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1)
    (hZ₀ : IsFinitePresentation B S hS Z₀.1.ι)
    (hZ : ∀ i, IsFinitePresentation B S hS (Z i).1.ι) :
    ∀ l : List ι, IsFinitePresentation B S hS (sumClosedSubspacesList X Z Z₀ l).1.ι
  | [] => hZ₀
  | i :: l => isFinitePresentation_ι_sumClosedSubspaces X _ _ (hZ i)
      (isFinitePresentation_ι_sumClosedSubspacesList X Z Z₀ hZ₀ hZ l)

/-- **Every member of the family pulls back to an effective Cartier divisor along a morphism
along which the sum does.**  Splitting the sum one summand at a time, Stacks 083W. -/
theorem isPullbackDefined_of_mem_of_sumClosedSubspacesList {X Y : AlgebraicSpaces B S hS}
    {ι : Type v} (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1)
    (f : Y ⟶ X) :
    ∀ (l : List ι), IsPullbackDefined B S hS f (sumClosedSubspacesList X Z Z₀ l) →
      ∀ i ∈ l, IsPullbackDefined B S hS f (Z i)
  | [], _, _, hi => absurd hi (List.not_mem_nil)
  | j :: l, h, i, hi => by
    rw [sumClosedSubspacesList] at h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact isPullbackDefined_left_of_sumClosedSubspaces f _ _ h
    · exact isPullbackDefined_of_mem_of_sumClosedSubspacesList Z Z₀ f l
        (isPullbackDefined_right_of_sumClosedSubspaces f _ _ h) i hi

/-! ### Commutativity and associativity of the sum -/

/-- The sum of two closed subspaces is the descent of the closed subscheme cut out on the atlas
chart by the product of the two chart ideal sheaves. -/
theorem sumClosedSubspaces_val (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    (sumClosedSubspaces B S hS X D₁ D₂).1 =
      invariantSubspace B S hS (atlasHom B S hS X)
        (Subobject.mk (chartKer B S hS X D₁ (atlasHom B S hS X) *
          chartKer B S hS X D₂ (atlasHom B S hS X)).subschemeι) :=
  rfl

/-- **The sum of two closed subspaces is commutative**, Stacks 083U: it is cut out on the atlas
chart by the product of the two chart ideal sheaves, and that product is commutative. -/
theorem sumClosedSubspaces_comm (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    sumClosedSubspaces B S hS X D₁ D₂ = sumClosedSubspaces B S hS X D₂ D₁ :=
  Subtype.ext (by
    rw [sumClosedSubspaces_val, sumClosedSubspaces_val,
      mul_comm (chartKer B S hS X D₂ (atlasHom B S hS X))
        (chartKer B S hS X D₁ (atlasHom B S hS X))])

/-- **The sum of closed subspaces is associative**, Stacks 083U, for the same reason as
`AlgebraicGeometry.Space.sumClosedSubspaces_comm`: the chart ideal sheaf of a sum is the product
of those of the summands. -/
theorem sumClosedSubspaces_assoc (X : AlgebraicSpaces B S hS)
    (D₁ D₂ D₃ : ClosedSubspaces B S hS X.1) :
    sumClosedSubspaces B S hS X (sumClosedSubspaces B S hS X D₁ D₂) D₃ =
      sumClosedSubspaces B S hS X D₁ (sumClosedSubspaces B S hS X D₂ D₃) :=
  Subtype.ext (by
    rw [sumClosedSubspaces_val, sumClosedSubspaces_val, chartKer_sumClosedSubspaces,
      chartKer_sumClosedSubspaces,
      mul_assoc (chartKer B S hS X D₁ (atlasHom B S hS X))
        (chartKer B S hS X D₂ (atlasHom B S hS X))
        (chartKer B S hS X D₃ (atlasHom B S hS X))])

/-- **Every member of the family is a summand of the sum along a list containing it.**  The
complementary summand is the sum of the others, so it inherits finite presentation of its
inclusion and disjointness from a set of points; the extraction itself is commutativity and
associativity of the sum. -/
theorem exists_eq_sumClosedSubspaces_of_mem (X : AlgebraicSpaces B S hS) {ι : Type v}
    (Z : ι → ClosedSubspaces B S hS X.1) (Z₀ : ClosedSubspaces B S hS X.1)
    (hZ₀fp : IsFinitePresentation B S hS Z₀.1.ι)
    (hZfp : ∀ j, IsFinitePresentation B S hS (Z j).1.ι)
    (W : Set (points B S hS X.1))
    (hZ₀d : Disjoint W (subspacePointSet B S hS X.1 Z₀.1))
    (hZd : ∀ j, Disjoint W (subspacePointSet B S hS X.1 (Z j).1)) :
    ∀ (l : List ι) (i : ι), i ∈ l → ∃ J : ClosedSubspaces B S hS X.1,
      sumClosedSubspacesList X Z Z₀ l = sumClosedSubspaces B S hS X (Z i) J ∧
        IsFinitePresentation B S hS J.1.ι ∧
          Disjoint W (subspacePointSet B S hS X.1 J.1)
  | [], _, hi => absurd hi List.not_mem_nil
  | j :: l, i, hi => by
    rcases List.mem_cons.1 hi with rfl | hi
    · exact ⟨sumClosedSubspacesList X Z Z₀ l, rfl,
        isFinitePresentation_ι_sumClosedSubspacesList X Z Z₀ hZ₀fp hZfp l,
        disjoint_subspacePointSet_sumClosedSubspacesList X Z Z₀ W hZ₀d hZd l⟩
    · obtain ⟨J', hJ', hJ'fp, hJ'd⟩ :=
        exists_eq_sumClosedSubspaces_of_mem X Z Z₀ hZ₀fp hZfp W hZ₀d hZd l i hi
      refine ⟨sumClosedSubspaces B S hS X (Z j) J', ?_,
        isFinitePresentation_ι_sumClosedSubspaces X _ _ (hZfp j) hJ'fp, ?_⟩
      · rw [sumClosedSubspacesList, hJ', ← sumClosedSubspaces_assoc,
          sumClosedSubspaces_comm X (Z j) (Z i), sumClosedSubspaces_assoc]
      · rw [subspacePointSet_sumClosedSubspaces]
        exact (hZd j).union_right hJ'd

/-! ### Inheritance of admissibility data along a morphism and along an isomorphism -/

/-- The inclusion of the inverse image of a finitely presented closed subspace is again of
finite presentation: it is a base change of the inclusion, Stacks 083Q. -/
theorem isFinitePresentation_ι_preimage {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (hfp : IsFinitePresentation B S hS Z.1.ι) :
    IsFinitePresentation B S hS (Z.1.preimage f.hom).ι := by
  have hcs : IsClosedSubspace B S hS (Z.1.preimage f.hom) :=
    isClosedSubspace_preimage B S hS f.hom Z.1 X.2 Y.2 Z.2
  have hsqA : IsPullback
      (ObjectProperty.homMk (Z.1.fromPreimage f.hom) :
        (⟨(Z.1.preimage f.hom).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (Z.1.preimage f.hom).ι :
        (⟨(Z.1.preimage f.hom).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) f :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f.hom Z.1)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) ↦ IsFinitePresentation B S hS g.hom)
    hsqA hfp

/-- **Being the blowup in a closed subspace is invariant under an isomorphism of the source.**
If `f : X' ⟶ X` is the blowup of `X` in `Z` and `e : X'' ≅ X'` then `e.hom ≫ f` is too: the
inverse image of `Z` crosses the isomorphism by
`AlgebraicGeometry.Space.isPullbackDefined_of_iso_over`, and lifts through `e.hom ≫ f`
correspond to lifts through `f`. -/
theorem IsBlowupAlong.of_iso_over {X X' X'' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X} (hf : IsBlowupAlong B S hS Z f)
    (e : X'' ≅ X') : IsBlowupAlong B S hS Z (e.hom ≫ f) := by
  refine isBlowupAlong_of_existsUnique_lift
    (isPullbackDefined_of_iso_over e rfl Z hf.isPullbackDefined) fun W w hw => ?_
  obtain ⟨l, hl, hlu⟩ := hf.existsUnique_lift w hw
  refine ⟨l ≫ e.inv, ?_, fun m hm => ?_⟩
  · show (l ≫ e.inv) ≫ e.hom ≫ f = w
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact hl
  · have hm' : m ≫ e.hom ≫ f = w := hm
    have h1 : m ≫ e.hom = l := hlu (m ≫ e.hom)
      (show (m ≫ e.hom) ≫ f = w by rw [Category.assoc]; exact hm')
    rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### Clause (a) of Stacks 086E -/
/-! ### Clause (a) of Stacks 086E -/

/-- **Stacks 086E, clause (a).**  Let `S` be a scheme, let `X` be a quasi-compact and
quasi-separated algebraic space over `S`, let `U ⊆ X` be a quasi-compact open subspace and let
`b i : X i ⟶ X`, `i : ι` with `ι` finite, be `U`-admissible blowups.  There is a `U`-admissible
blowup `c : X' ⟶ X` which factors as `X' ⟶ X i ⟶ X` for every `i`.

Take for `X'` the blowup of `X` in the sum `Z i₀ + Z i₁ + ⋯` of the centres of the given
blowups, Stacks 083U; the sum of finitely many finitely presented centres disjoint from `U` is
again finitely presented (`AlgebraicGeometry.Space.isFinitePresentation_ι_sumClosedSubspaces`)
and disjoint from `U` (`AlgebraicGeometry.Space.subspacePointSet_sumClosedSubspaces`), so `c` is
`U`-admissible.  The inverse image of the sum along `c` is an effective Cartier divisor, hence so
is the inverse image of each summand `Z i` by Stacks 083W, and the universal property of `b i`,
Stacks 085U, then produces the factorisation through `b i`.  For the empty family the identity of
`X` is a `U`-admissible blowup, being the blowup in the empty closed subspace.

The hypotheses beyond the source's are the construction data of Stacks 085Q for the blowup of
`X`: an étale presentation `P` of `X`, the universe choice `HasSheafify` for the quotient
presheaf, and the three `B.Contains` smallness side conditions on the relative `Proj`s, asked for
every closed subspace of `X` since the centre is built inside the proof.  None of these says
anything about blowups; they are exactly what
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` takes. -/
@[stacks 086E "clause (a): a U-admissible blowup factoring through each member of a finite \
family of U-admissible blowups, with no assumed inputs beyond the Stacks 085Q construction \
data for X -- a presentation P, the HasSheafify universe choice, and the three B.Contains side \
conditions on the relative Projs, asked for EVERY closed subspace of X because the centre is \
the sum of the given centres and is built inside the proof, so it cannot be named in advance -- \
none of which occurs in the conclusion"]
theorem exists_isAdmissibleBlowup_factoring
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hZtop : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZtop X.1)
    (U : OpenSubspaces B S hS X.1)
    (_hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    {ι : Type v} [Finite ι] (Xi : ι → AlgebraicSpaces B S hS) (b : ∀ i, Xi i ⟶ X)
    (hb : ∀ i, IsAdmissibleBlowup B S hS U (b i))
    (P : Presentation B S hS X.obj X.property)
    (hc : ∀ K : ClosedSubspaces B S hS X.obj,
      B.Contains (reesChartSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
        B.Contains (reesRelationSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
          B.Contains (reesDoubleSituation (centreIdeal K)
            (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj) :
    ∃ (X' : AlgebraicSpaces B S hS) (c : X' ⟶ X), IsAdmissibleBlowup B S hS U c ∧
      ∃ g : ∀ i, X' ⟶ Xi i, ∀ i, g i ≫ b i = c := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hne
  · exact ⟨X, 𝟙 X, isAdmissibleBlowup_id_emptyClosedSubspace X U,
      fun i => (hι.false i).elim, fun i => (hι.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  have : Fintype ι := Fintype.ofFinite ι
  choose Z hZfp hZdisj hZb using hb
  set K : ClosedSubspaces B S hS X.1 :=
    sumClosedSubspacesList X Z (Z i₀) Finset.univ.toList with hK
  obtain ⟨hc₁, hc₂, hc₃⟩ := hc K
  have hKb := isBlowupAlong_blowUpAlongHom' K P hc₁ hc₂ hc₃
  have hsplit : ∀ i, IsPullbackDefined B S hS
      (blowUpAlongHom' K P hc₁ hc₂ hc₃) (Z i) := fun i =>
    isPullbackDefined_of_mem_of_sumClosedSubspacesList Z (Z i₀) _ _ hKb.isPullbackDefined i
      (Finset.mem_toList.2 (Finset.mem_univ i))
  exact ⟨blowUpAlong' K P hc₁ hc₂ hc₃,
    blowUpAlongHom' K P hc₁ hc₂ hc₃,
    ⟨K, isFinitePresentation_ι_sumClosedSubspacesList X Z (Z i₀) (hZfp i₀) hZfp _,
      disjoint_subspacePointSet_sumClosedSubspacesList X Z (Z i₀) _ (hZdisj i₀) hZdisj _,
      hKb⟩,
    fun i => ((hZb i).existsUnique_lift _ (hsplit i)).choose,
    fun i => ((hZb i).existsUnique_lift _ (hsplit i)).choose_spec.1⟩

/-! ### Clause (b) of Stacks 086E -/

/-- **Stacks 086E, clause (b).**  In the situation of clause (a) the dominating `U`-admissible
blowup `c : X' ⟶ X` can be chosen so that, in addition, each factor morphism `g i : X' ⟶ X i` is
itself a `b i⁻¹(U)`-admissible blowup.

Writing the centre of `c` as `Z i + J i` — every member of the family is a summand of the sum,
`AlgebraicGeometry.Space.exists_eq_sumClosedSubspaces_of_mem` — the blowup `c i` of `X i` in the
inverse image of `J i` exists by Stacks 085Q and 085U, and Stacks 085Y identifies the composite
`c i ≫ b i` with the blowup of `X` in `Z i + J i`, the input it needs being Stacks 085X for `c i`
and the exceptional divisor of `b i`
(`AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong`).  Blowups in a fixed centre are
isomorphic over the base, so `X'` is isomorphic over `X` to the source of `c i ≫ b i`, and the
factor morphism transported along that isomorphism is again the blowup of `X i` in the inverse
image of `J i`.  That centre is finitely presented (a base change of `J i`) and disjoint from
`b i⁻¹(U)` (the inverse image of a disjointness), so the factor morphism is
`b i⁻¹(U)`-admissible.  For the empty family the identity of `X` is the blowup in the empty
closed subspace and there is nothing to factor.

The hypotheses beyond the source's are the construction data of Stacks 085Q, now also for each
`X i` because the second blowup of the tower is formed there: étale presentations `P` of `X` and
`Pi i` of `X i`, the universe choice `HasSheafify`, and the `B.Contains` smallness side
conditions on the relative `Proj`s.  None of them occurs in the conclusion, and none says
anything about blowups. -/
@[stacks 086E "clause (b): the factor morphisms of the dominating blowup are themselves \
admissible blowups, with no assumed inputs beyond the Stacks 085Q construction data for X and \
for the X i -- presentations P and Pi, the HasSheafify universe choice, and the B.Contains side \
conditions on the relative Projs, asked for EVERY closed subspace of X and of each X i because \
the centres are built inside the proof and cannot be named in advance -- none of which occurs \
in the conclusion"]
theorem exists_isAdmissibleBlowup_factoring_isAdmissibleBlowup
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hZtop : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (_hXqc : IsQuasiCompactSpace B S hS X.1)
    (_hXqs : IsAbsolutelyQuasiSeparated B S hS hZtop X.1)
    (U : OpenSubspaces B S hS X.1)
    (_hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    {ι : Type v} [Finite ι] (Xi : ι → AlgebraicSpaces B S hS) (b : ∀ i, Xi i ⟶ X)
    (hb : ∀ i, IsAdmissibleBlowup B S hS U (b i))
    (P : Presentation B S hS X.obj X.property)
    (hc : ∀ K : ClosedSubspaces B S hS X.obj,
      B.Contains (reesChartSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
        B.Contains (reesRelationSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
          B.Contains (reesDoubleSituation (centreIdeal K)
            (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj)
    (Pi : ∀ i, Presentation B S hS (Xi i).obj (Xi i).property)
    (hci : ∀ (i : ι) (K : ClosedSubspaces B S hS (Xi i).obj),
      B.Contains (reesChartSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) (Pi i)).relativeProj ∧
        B.Contains (reesRelationSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) (Pi i)).relativeProj ∧
          B.Contains (reesDoubleSituation (centreIdeal K)
            (isCartesianOnAffineCharts_centreIdeal K) (Pi i)).relativeProj) :
    ∃ (X' : AlgebraicSpaces B S hS) (c : X' ⟶ X), IsAdmissibleBlowup B S hS U c ∧
      ∃ g : ∀ i, X' ⟶ Xi i, (∀ i, g i ≫ b i = c) ∧
        ∀ i, IsAdmissibleBlowup B S hS
          ⟨U.1.preimage (b i).hom,
            isOpenSubspace_preimage B S hS (b i).hom U.1 X.2 (Xi i).2 U.2⟩ (g i) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hne
  · exact ⟨X, 𝟙 X, isAdmissibleBlowup_id_emptyClosedSubspace X U,
      fun i => (hι.false i).elim, fun i => (hι.false i).elim, fun i => (hι.false i).elim⟩
  obtain ⟨i₀⟩ := hne
  have : Fintype ι := Fintype.ofFinite ι
  choose Z hZfp hZdisj hZb using hb
  set K : ClosedSubspaces B S hS X.1 :=
    sumClosedSubspacesList X Z (Z i₀) Finset.univ.toList with hK
  obtain ⟨hc₁, hc₂, hc₃⟩ := hc K
  have hKb := isBlowupAlong_blowUpAlongHom' K P hc₁ hc₂ hc₃
  have key : ∀ i : ι, ∃ g : blowUpAlong' K P hc₁ hc₂ hc₃ ⟶ Xi i,
      g ≫ b i = blowUpAlongHom' K P hc₁ hc₂ hc₃ ∧
        IsAdmissibleBlowup B S hS
          ⟨U.1.preimage (b i).hom,
            isOpenSubspace_preimage B S hS (b i).hom U.1 X.2 (Xi i).2 U.2⟩ g := by
    intro i
    obtain ⟨J, hJ, hJfp, hJd⟩ := exists_eq_sumClosedSubspaces_of_mem X Z (Z i₀) (hZfp i₀) hZfp
      (subspacePointSet B S hS X.1 U.1) (hZdisj i₀) hZdisj Finset.univ.toList i
      (Finset.mem_toList.2 (Finset.mem_univ i))
    set Jb : ClosedSubspaces B S hS (Xi i).1 := preimageClosedSubspace (b i) J with hJb
    obtain ⟨hci₁, hci₂, hci₃⟩ := hci i Jb
    have hcib := isBlowupAlong_blowUpAlongHom' Jb (Pi i) hci₁ hci₂ hci₃
    have h085X : IsPullbackDefined B S hS
        (blowUpAlongHom' Jb (Pi i) hci₁ hci₂ hci₃)
        (preimageClosedSubspace (b i) (Z i)) :=
      isPullbackDefined_of_isBlowupAlong Jb (Pi i) hci₁ hci₂ hci₃
        hcib _ (hZb i).isPullbackDefined
    have hcomp : IsBlowupAlong B S hS K
        (blowUpAlongHom' Jb (Pi i) hci₁ hci₂ hci₃ ≫ b i) := by
      rw [hK, hJ]
      exact isBlowupAlong_comp_of_isBlowupAlong (hZb i) hcib h085X
    obtain ⟨e, he⟩ := hKb.exists_iso hcomp
    refine ⟨e.hom ≫ blowUpAlongHom' Jb (Pi i) hci₁ hci₂ hci₃,
      by rw [Category.assoc]; exact he,
      Jb, isFinitePresentation_ι_preimage (b i) J hJfp, ?_, hcib.of_iso_over e⟩
    show Disjoint (subspacePointSet B S hS (Xi i).1 (U.1.preimage (b i).hom))
      (subspacePointSet B S hS (Xi i).1 (J.1.preimage (b i).hom))
    rw [subspacePointSet_preimage, subspacePointSet_preimage]
    exact hJd.preimage _
  exact ⟨blowUpAlong' K P hc₁ hc₂ hc₃,
    blowUpAlongHom' K P hc₁ hc₂ hc₃,
    ⟨K, isFinitePresentation_ι_sumClosedSubspacesList X Z (Z i₀) (hZfp i₀) hZfp _,
      disjoint_subspacePointSet_sumClosedSubspacesList X Z (Z i₀) _ (hZdisj i₀) hZdisj _,
      hKb⟩,
    fun i => (key i).choose, fun i => (key i).choose_spec.1,
    fun i => (key i).choose_spec.2⟩

end AlgebraicGeometry.Space

end
