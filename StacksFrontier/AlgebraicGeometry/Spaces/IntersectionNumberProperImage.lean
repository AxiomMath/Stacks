module

public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristicHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosedImageGenericLength
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerTopDimensionalComponents
public import StacksFrontier.Topology.Dimension.MaximalPointDrop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Intersection numbers along a morphism of spaces proper over a field (Stacks 0EDJ)

Let `k` be a field, `f : Y ⟶ X` a morphism of algebraic spaces proper over `k`, `Z ⊂ Y` an
integral closed subspace of dimension `d` and `L₁, …, L_d` invertible `𝒪_X`-modules. Stacks 0EDJ
says that

`(f^*L₁ ⋯ f^*L_d · Z) = deg(Z → f(Z)) (L₁ ⋯ L_d · f(Z))`,

where `f(Z) ⊂ X` is the scheme-theoretic image of `Z`, `deg(Z → f(Z))` is the degree of
Stacks 0AD6, and the right hand side is read as `0` when `dim f(Z) < d`.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq`: **Stacks 0EDJ.**
* `AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq_degree_mul` and
  `AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq_zero_of_dimension_lt`: the two
  cases.
* `AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq_sum`: the pulled-back
  intersection number is `∑_q (-1)^q` times the `d`-fold mixed finite difference of the twisted
  Euler characteristics of `R^q (Z ⟶ X)_*𝒪_Z`.

## The route

This is the source's proof. The intersection number is the `d`-fold mixed finite difference of
the twisted Euler characteristics at the indicator exponents (Stacks 0EDF).

* Along the closed immersion `Z ⟶ Y` these Euler characteristics are those of `𝒪_Z` twisted by
  the inverse images of the `L_j`
  (`AlgebraicGeometry.Space.eulerCharacteristic_twist_structureSheafPushforward_eq`).
* Along `g : Z ⟶ X` they are `∑_q (-1)^q χ(X, R^q g_*𝒪_Z ⊗ ⨂ L_j)`, by Stacks 0EDD and the
  projection formula for invertible modules
  (`AlgebraicGeometry.Space.eulerCharacteristic_twist_unit_eq_finsum`).
* Each `R^q g_*𝒪_Z` is supported in `f(Z)`. For `q > 0` it also vanishes at the generic point of
  `f(Z)` when `dim f(Z) = d`, by Stacks 0A4K. So its support has dimension `< d` and its mixed
  finite difference vanishes, by Stacks 0DN4
  (`AlgebraicGeometry.Space.sum_neg_one_pow_mul_eulerCharacteristic_twist_eq_zero`).
* For `q = 0` and `dim f(Z) = d`, Stacks 0EDE identifies the leading term with `deg(Z/f(Z))`
  times that of `𝒪_{f(Z)}`, the length of `g_*𝒪_Z` at the generic point of `f(Z)` being the
  degree
  (`AlgebraicGeometry.Space.IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree`).

## Implementation notes

`Z` is an `AlgebraicGeometry.Space.IntegralClosedSubspace` of `Y`, and `f(Z)` is
`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage`: the integral closed subspace of `X`
on the closure of `f(|Z|)`. The registered statement records that this is the scheme-theoretic
image of `Z ⟶ X` (Stacks 0830), that its dimension is at most `d`, and the formula, with the case
`dim f(Z) < d` as the `else` branch of a dependent `if`. The higher direct images are those of
`AlgebraicGeometry.Space.modulePushforward` at module universe `u`, as in Stacks 0EDD.

## References

* [Stacks Project, Tag 0EDJ](https://stacks.math.columbia.edu/tag/0EDJ)
* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0EDD](https://stacks.math.columbia.edu/tag/0EDD)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0EDE](https://stacks.math.columbia.edu/tag/0EDE)
* [Stacks Project, Tag 0AD6](https://stacks.math.columbia.edu/tag/0AD6)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    {X Y : AlgebraicSpaces B (Spec (.of k)) hk}
    (pX : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hpX : IsProper B (Spec (.of k)) hk pX)
    (pY : Y.1 ⟶ yoneda.obj (baseObject k B hk)) (hpY : IsProper B (Spec (.of k)) hk pY)

/-- **Step one: from `Y` to `Z`.** The twisted Euler characteristic of `i_*𝒪_Z` on `Y`, twisted
by the inverse images `f^*L_j` at an indicator exponent, is that of `𝒪_Z` twisted by the inverse
images `(Z ⟶ X)^*L_j`. -/
theorem eulerCharacteristic_twist_structureSheafPushforward_eq (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) {d : ℕ}
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (T : Finset (Fin d)) :
    let ZA := closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
    let i := closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
    letI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j)
      (hM := hL j)
    letI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk (i ≫ f) (L j)
      (hM := hL j)
    have hpZ : IsProper B (Spec (.of k)) hk (i.hom ≫ pY) :=
      isProper_comp B (Spec (.of k)) hk ZA.2 Y.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom pY
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk ZA.2 Y.2 i.hom Z.isClosedSubspace.2) hpY
    @eulerCharacteristic.{u, w} k _ B hk Y.1 Y.2 pY hpY
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk Y.1 Y.2
          (structureSheafPushforward B (Spec (.of k)) hk i)
          (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
          fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk Y ZA pY hpY i
          Z.isClosedSubspace.2 _ _) =
      @eulerCharacteristic.{u, w} k _ B hk ZA.1 ZA.2 (i.hom ≫ pY) hpZ
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk ZA.1 ZA.2
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O))
          (fun j => (modulePullback B (Spec (.of k)) hk (i ≫ f)).obj (L j))
          fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk ZA (i.hom ≫ pY) hpZ _ _
          (isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2) _) := by
  intro ZA i hpZ
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j) (hM := hL j)
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk (i ≫ f) (L j)
    (hM := hL j)
  have h := eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion.{u, w}
    k B hk pY hpY i Z.isClosedSubspace.2 _
    (isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2)
    (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j)) fun j => if j ∈ T then 1 else 0
  refine h.trans ?_
  have hI : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk ZA.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O).property
      ((modulePullback B (Spec (.of k)) hk f ⋙ modulePullback B (Spec (.of k)) hk i).obj (L j)) :=
    fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i
      ((modulePullback B (Spec (.of k)) hk f).obj (L j))
  have hO := isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2
  exact @eulerCharacteristic_congr.{u, w} k _ B hk ZA.1 ZA.2 _ hpZ _ _
    (uliftForPresentationMapIso.{u, w} B (Spec (.of k)) hk ZA.1 ZA.2
      (twistedModuleCongrIndicatorIso B (Spec (.of k)) hk ZA
        (fun j => (modulePullbackCompIso B (Spec (.of k)) hk i f).app (L j)) T _))
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk ZA (i.hom ≫ pY) hpZ
      (fun j => (modulePullback B (Spec (.of k)) hk f ⋙ modulePullback B (Spec (.of k)) hk i).obj
        (L j)) _ hO fun j => if j ∈ T then 1 else 0)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk ZA (i.hom ≫ pY) hpZ
      (fun j => (modulePullback B (Spec (.of k)) hk (i ≫ f)).obj (L j)) _ hO
      fun j => if j ∈ T then 1 else 0)

/-- **Step two: along `Z ⟶ X`, Stacks 0EDD and the projection formula.** For a morphism
`g : Z ⟶ X` of algebraic spaces proper over `k` and invertible `𝒪_X`-modules `L_j`, the twisted
Euler characteristic of `𝒪_Z` by the `g^*L_j` at an indicator exponent is the alternating sum of
the twisted Euler characteristics of the higher direct images `R^q g_*𝒪_Z` by the `L_j`. -/
theorem eulerCharacteristic_twist_unit_eq_finsum {Z : AlgebraicSpaces B (Spec (.of k)) hk}
    (pZ : Z.1 ⟶ yoneda.obj (baseObject k B hk)) (hpZ : IsProper B (Spec (.of k)) hk pZ)
    (g : Z ⟶ X) {d : ℕ} (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (T : Finset (Fin d)) :
    letI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk g (L j)
      (hM := hL j)
    have := hasInjectiveResolutions_modules B (Spec (.of k)) hk Z.1 Z.2
    have hO : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O)) :=
      haveI : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Z.1
          (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
        ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Z.1 Z.2 pZ hpZ⟩
      inferInstance
    @eulerCharacteristic.{u, w} k _ B hk Z.1 Z.2 pZ hpZ
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk Z.1 Z.2
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O))
          (fun j => (modulePullback B (Spec (.of k)) hk g).obj (L j))
          fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk Z pZ hpZ _ _ hO _) =
      ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (((modulePushforward B (Spec (.of k)) hk g).rightDerived q).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O)))
          L fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L _
          (@isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ g pX hpX pZ hpZ _ hO q)
          _) := by
  intro _ hO
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk g (L j) (hM := hL j)
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Z.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Z.1 Z.2 pZ hpZ⟩
  have hG := isCoherent_twistedModule B (Spec (.of k)) hk Z.1 Z.2
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O))
    (fun j => (modulePullback B (Spec (.of k)) hk g).obj (L j))
    (fun j => if j ∈ T then 1 else 0) hO
  obtain ⟨-, h⟩ := eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage.{u, w}
    k B hk g pX hpX pZ hpZ (twistedModule B (Spec (.of k)) hk Z.1 Z.2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O))
      (fun j => (modulePullback B (Spec (.of k)) hk g).obj (L j))
      (fun j => if j ∈ T then 1 else 0))
  refine h.trans (finsum_congr fun q => ?_)
  congr 1
  exact @eulerCharacteristic_congr.{u, w} k _ B hk X.1 X.2 pX hpX _ _
    (uliftForPresentationMapIso.{u, w} B (Spec (.of k)) hk X.1 X.2
      (rightDerivedTwistedModuleIndicatorIso B (Spec (.of k)) hk g L T _ q))
    (by
      have := isCoherent_higherDirectImage_of_isProper_toBase k B hk g pX hpX pZ hpZ
        (twistedModule B (Spec (.of k)) hk Z.1 Z.2
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O))
          (fun j => (modulePullback B (Spec (.of k)) hk g).obj (L j))
          (fun j => if j ∈ T then 1 else 0)) q
      infer_instance)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L _
      (@isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ g pX hpX pZ hpZ _ hO q) _)

/-! ### Alternating sums of twisted Euler characteristics at the indicator exponents -/

/-- If a function of the exponent tuples is given by a rational polynomial which is zero or of
total degree `< d`, its `d`-fold mixed finite difference at the indicator tuples vanishes. -/
theorem sum_neg_one_pow_mul_eq_zero_of_eval_eq {d : ℕ} (φ : (Fin d → ℤ) → ℤ)
    (P : MvPolynomial (Fin d) ℚ) (hP : ∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) P = φ n)
    (hdeg : P = 0 ∨ P.totalDegree < d) :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * φ (fun j => if j ∈ T then 1 else 0) = 0 := by
  have h := MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_zero_of_totalDegree_lt P hdeg
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [← h]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  rw [← hP]
  exact congrArg (fun v => MvPolynomial.eval v P) (funext fun j => by split_ifs <;> simp)

/-- **The `d`-fold mixed finite difference of the twisted Euler characteristics of a coherent
module with support of dimension `< d` vanishes**, by Stacks 0DN4. -/
theorem sum_neg_one_pow_mul_eulerCharacteristic_twist_eq_zero {d : ℕ}
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (H : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hH : IsCoherent B (Spec (.of k)) hk X.1 X.2 H)
    (hdim : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X H) < d) :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 H L fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L H hH _) = 0 := by
  obtain ⟨P, hP, hdeg⟩ := exists_representsTwistedEuler_of_isCoherent.{u, w} k B hk X pX hpX L H hH
  refine sum_neg_one_pow_mul_eq_zero_of_eval_eq (fun n => @eulerCharacteristic.{u, w} k _ B hk
    X.1 X.2 pX hpX (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 H L n)
    (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L H hH n)) P hP ?_
  refine hdeg.imp_right fun h => ?_
  exact_mod_cast (h.trans_lt hdim : (P.totalDegree : WithBot ℕ∞) < (d : WithBot ℕ∞))

/-- If a function of the exponent tuples differs from `m` times another by a rational polynomial
which is zero or of total degree `< d`, the two `d`-fold mixed finite differences at the indicator
tuples differ by the factor `m`. -/
theorem sum_neg_one_pow_mul_eq_mul_of_eval_eq_sub {d : ℕ} (φ ψ : (Fin d → ℤ) → ℤ) (m : ℤ)
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) P = (φ n : ℚ) - m * ψ n)
    (hdeg : P = 0 ∨ P.totalDegree < d) :
    ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) * φ (fun j => if j ∈ T then 1 else 0) =
      m * ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        ψ (fun j => if j ∈ T then 1 else 0) := by
  have h := sum_neg_one_pow_mul_eq_zero_of_eval_eq (fun n => φ n - m * ψ n) P
    (fun n => by rw [hP n]; push_cast; ring) hdeg
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  rw [Finset.mul_sum]
  rw [sub_eq_zero] at h
  rw [h]
  exact Finset.sum_congr rfl fun T _ => by ring

/-- The empty set has Krull dimension `< d`. -/
private theorem topologicalKrullDim_empty_lt {T : Type*} [TopologicalSpace T] (d : ℕ) :
    topologicalKrullDim (∅ : Set T) < d := by
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 (Set.isEmpty_coe_sort.2 rfl)]
  exact WithBot.bot_lt_coe _

/-- A closed subset of an irreducible set `C` of Krull dimension at most `d`, contained in `C` and
missing one of its points, has Krull dimension `< d`. -/
theorem topologicalKrullDim_lt_of_subset_of_notMem {T : Type*} [TopologicalSpace T]
    {C F : Set T} (hC : IsIrreducible C) (hF : IsClosed F) (hFC : F ⊆ C) {η : T} (hηC : η ∈ C)
    (hηF : η ∉ F) {d : ℕ} (hd : topologicalKrullDim C ≤ d) :
    topologicalKrullDim F < d := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact topologicalKrullDim_empty_lt d
  have hCF : ¬ C ⊆ F := fun h => hηF (h hηC)
  have hinter : C ∩ F = F := Set.inter_eq_right.2 hFC
  obtain ⟨h1, h2⟩ := topologicalKrullDim_inter_le_pred_of_not_subset hC hF hCF
    (by rw [hinter]; exact hne) hd
  rw [hinter] at h2
  refine h2.trans_lt ?_
  exact_mod_cast (by omega : d - 1 < d)

/-- The Krull dimension of a subset is at most that of a set containing it. -/
theorem topologicalKrullDim_mono_set {T : Type*} [TopologicalSpace T] {F C : Set T}
    (h : F ⊆ C) : topologicalKrullDim F ≤ topologicalKrullDim C :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-! ### The intersection number on `Y` as an alternating sum over the higher direct images -/

/-- **The pulled-back intersection number as an alternating sum.** For a morphism `f : Y ⟶ X` of
algebraic spaces proper over `k`, an integral closed subspace `Z ⊂ Y` of dimension `d` and
invertible `𝒪_X`-modules `L_j`, write `g : Z ⟶ X` for the restriction of `f` and `H_q` for
`R^q g_*𝒪_Z`. Then for any finite set `S` of degrees outside of which the `H_q` vanish,

`(f^*L₁ ⋯ f^*L_d · Z) = ∑_{q ∈ S} (-1)^q ∑_T (-1)^{d - |T|} χ(X, H_q ⊗ ⨂_{j ∈ T} L_j)`.

This combines `AlgebraicGeometry.Space.eulerCharacteristic_twist_structureSheafPushforward_eq`,
`AlgebraicGeometry.Space.eulerCharacteristic_twist_unit_eq_finsum` and the vanishing of the
twisted Euler characteristics of a zero module (Stacks 0DN2). -/
theorem intersectionNumber_modulePullback_eq_sum (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) {d : ℕ}
    (hZd : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (S : Finset ℕ) :
    let ZA := closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
    let i := closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
    have hpZ : IsProper B (Spec (.of k)) hk (i.hom ≫ pY) :=
      isProper_comp B (Spec (.of k)) hk ZA.2 Y.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom pY
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk ZA.2 Y.2 i.hom Z.isClosedSubspace.2) hpY
    have := hasInjectiveResolutions_modules B (Spec (.of k)) hk ZA.1 ZA.2
    have := modulePushforward_additive B (Spec (.of k)) hk (i ≫ f)
    have hO := isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2
    (∀ q ∉ S, IsZero (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived q).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O)))) →
    @intersectionNumber.{u, w} k _ B hk Y ZA d pY hpY i Z.isClosedSubspace.2 hZd
        (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
        (fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j)
          (hM := hL j)) =
      ∑ q ∈ S, (-1 : ℤ) ^ q * ∑ T : Finset (Fin d), (-1 : ℤ) ^ (d - T.card) *
        @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived q).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O)))
            L fun j => if j ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L _
            (@isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ (i ≫ f) pX hpX
              (i.hom ≫ pY) hpZ _ hO q) _) := by
  intro ZA i hpZ _ _ hO hS
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j) (hM := hL j)
  have hadd := hasAdditiveTwistedEulerOnCoherent_of_isProper.{u, w} k B hk X pX hpX L
  have hT : ∀ T : Finset (Fin d),
      @eulerCharacteristic.{u, w} k _ B hk Y.1 Y.2 pY hpY
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk Y.1 Y.2
          (structureSheafPushforward B (Spec (.of k)) hk i)
          (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
          fun j => if j ∈ T then 1 else 0)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk Y ZA pY hpY i
          Z.isClosedSubspace.2 _ _) =
      ∑ q ∈ S, (-1 : ℤ) ^ q * @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived q).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O)))
            L fun j => if j ∈ T then 1 else 0)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L _
            (@isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ (i ≫ f) pX hpX
              (i.hom ≫ pY) hpZ _ hO q) _) := fun T => by
    rw [eulerCharacteristic_twist_structureSheafPushforward_eq.{u, w} k B hk pY hpY f Z L T,
      eulerCharacteristic_twist_unit_eq_finsum.{u, w} k B hk pX hpX (i.hom ≫ pY) hpZ (i ≫ f) L T]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra hqS
    refine hq ?_
    have h0 := eulerCharacteristic_twistedModuleUlift_eq_zero_of_isZero hadd (hS q hqS)
      (fun j => if j ∈ T then 1 else 0)
    beta_reduce
    rw [h0, mul_zero]
  rw [intersectionNumber_eq_sum]
  simp_rw [hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun T _ => by ring

/-- The twisted Euler characteristics of `i_*𝒪_V` for a closed subspace `V` depend only on the
subfunctor `V`. -/
theorem eulerCharacteristic_twist_structureSheafPushforward_congr {V V' : Subfunctor X.1}
    (hV : IsClosedSubspace B (Spec (.of k)) hk V) (hV' : IsClosedSubspace B (Spec (.of k)) hk V')
    (h : V = V') {r : ℕ} (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (n : Fin r → ℤ) :
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk
            (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨V, hV⟩)) L n)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X
          (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨V, hV⟩) pX hpX
          (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨V, hV⟩) hV.2 L n) =
      @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk
            (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨V', hV'⟩)) L n)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X
          (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨V', hV'⟩) pX hpX
          (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨V', hV'⟩) hV'.2 L n) := by
  subst h
  rfl

/-! ### Stacks 0EDJ -/

/-- The composite of the inclusion of a closed subspace `Z ⊂ Y` with `pY` is proper. -/
private theorem isProper_closedSubspaceInclusion_comp
    (hpY : IsProper B (Spec (.of k)) hk pY) (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) :
    IsProper B (Spec (.of k)) hk
      ((closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩).hom ≫
        pY) :=
  isProper_comp B (Spec (.of k)) hk
    (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩).2 Y.2
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) _ pY
    (isProper_of_isClosedImmersion B (Spec (.of k)) hk
      (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩).2 Y.2 _
      Z.isClosedSubspace.2) hpY

/-- **Stacks 0EDJ, the case `dim f(Z) < d`.** Let `f : Y ⟶ X` be a morphism of algebraic spaces
proper over a field `k`, let `Z ⊂ Y` be an integral closed subspace of dimension `d` and let
`L₁, …, L_d` be invertible `𝒪_X`-modules. If the image `f(Z) ⊂ X` (the integral closed subspace
on the closure of `f(|Z|)`, which is the scheme-theoretic image of `Z ⟶ X` by Stacks 0830) has
dimension `< d`, then `(f^*L₁ ⋯ f^*L_d · Z) = 0`.

Every `R^q (Z ⟶ X)_*𝒪_Z` is supported in `f(Z)`, so by Stacks 0DN4 its twisted Euler
characteristics are a polynomial of total degree `< d`, whose `d`-fold mixed finite difference
vanishes. -/
@[sga "6 X 4.4" "(4.4.3), special case"]
theorem intersectionNumber_modulePullback_eq_zero_of_dimension_lt (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) {d : ℕ}
    (hZd : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    let W := IntegralClosedSubspace.closureImage B (Spec (.of k)) hk X.2
      (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX) f.hom Z
    dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 < d →
    @intersectionNumber.{u, w} k _ B hk Y
        (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩) d pY hpY
        (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩)
        Z.isClosedSubspace.2 hZd
        (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
        (fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j)
          (hM := hL j)) = 0 := by
  intro W hW
  have hXdec := isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j) (hM := hL j)
  have hf := isProper_of_isProper_toBase k B hk f pX hpX pY hpY
  let ZA := closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
  let i := closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
  have hpZ := isProper_closedSubspaceInclusion_comp k B hk pY hpY Z
  have := hasInjectiveResolutions_modules B (Spec (.of k)) hk ZA.1 ZA.2
  have := modulePushforward_additive B (Spec (.of k)) hk (i ≫ f)
  have hO := isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2
  obtain ⟨hfin, -⟩ := @eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage.{u, w}
    k _ B hk _ _ (i ≫ f) pX hpX (i.hom ≫ pY) hpZ _ hO
  rw [intersectionNumber_modulePullback_eq_sum.{u, w} k B hk pX hpX pY hpY f Z hZd L hfin.toFinset
    (fun q hq => by simpa using hq)]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [sum_neg_one_pow_mul_eulerCharacteristic_twist_eq_zero.{u, w} k B hk pX hpX L _
    (@isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ (i ≫ f) pX hpX (i.hom ≫ pY)
      hpZ _ hO q) ?_, mul_zero]
  have hsub := IntegralClosedSubspace.supportOfSheaf_rightDerived_modulePushforward_subset
    B (Spec (.of k)) hk Y.2 X.2 hXdec f.hom hf Z q
  refine (topologicalKrullDim_mono_set hsub).trans_lt ?_
  rw [← dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk X.2 hXdec
    W.isClosedSubspace.1 W.subspace.ι W.isClosedSubspace.2]
  exact hW

/-- **Stacks 0EDJ, the case `dim f(Z) = d`.** Let `f : Y ⟶ X` be a morphism of algebraic spaces
proper over a field `k`, let `Z ⊂ Y` be an integral closed subspace of dimension `d` and let
`L₁, …, L_d` be invertible `𝒪_X`-modules. If the image `f(Z) ⊂ X` (the integral closed subspace
on the closure of `f(|Z|)`, which is the scheme-theoretic image of `Z ⟶ X` by Stacks 0830) has
dimension `d`, then

`(f^*L₁ ⋯ f^*L_d · Z) = deg(Z/f(Z)) · (L₁ ⋯ L_d · f(Z))`,

with `deg(Z/f(Z))` the degree of `Z ⟶ f(Z)` of Stacks 0AD6.

The proof is the source's: `χ(Y, 𝒪_Z ⊗ f^*L^{⊗ n}) = ∑ (-1)^q χ(X, R^q f_*𝒪_Z ⊗ L^{⊗ n})` by
Stacks 0EDD and the projection formula; the terms with `q > 0` are polynomials of total degree
`< d` (Stacks 0DN4) because `R^q f_*𝒪_Z` vanishes at the generic point of `f(Z)` (Stacks 0A4K,
`Z ⟶ f(Z)` being finite over a neighbourhood of it by Stacks 0AD5); and the term with `q = 0` is
`deg(Z/f(Z)) χ(f(Z), L^{⊗ n}|_{f(Z)})` up to such a polynomial (Stacks 0EDE), the length of
`f_*𝒪_Z` at the generic point of `f(Z)` being the degree. -/
@[sga "6 X 4.4" "special case"]
theorem intersectionNumber_modulePullback_eq_degree_mul (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) {d : ℕ}
    (hZd : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    let W := IntegralClosedSubspace.closureImage B (Spec (.of k)) hk X.2
      (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX) f.hom Z
    ∀ hW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 = d,
    @intersectionNumber.{u, w} k _ B hk Y
        (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩) d pY hpY
        (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩)
        Z.isClosedSubspace.2 hZd
        (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
        (fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j)
          (hM := hL j)) =
      (degree B (Spec (.of k)) hk Z.isClosedSubspace.1 W.isClosedSubspace.1 Z.isIntegralSpace
          W.isIntegralSpace
          (IntegralClosedSubspace.toClosureImage B (Spec (.of k)) hk X.2
            (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX) f.hom Z) : ℤ) *
        intersectionNumber.{u, w} k B hk X
          (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩) d pX hpX
          (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)
          W.isClosedSubspace.2 hW L := by
  intro W hW
  have hXdec := isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX
  have hXLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 pX hpX
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j) (hM := hL j)
  have hf := isProper_of_isProper_toBase k B hk f pX hpX pY hpY
  let ZA := closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
  let i := closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩
  have hpZ := isProper_closedSubspaceInclusion_comp k B hk pY hpY Z
  have := hasInjectiveResolutions_modules B (Spec (.of k)) hk ZA.1 ZA.2
  have := modulePushforward_additive B (Spec (.of k)) hk (i ≫ f)
  have hO := isCoherent_unit_of_isClosedImmersion k B hk Y ZA pY hpY i Z.isClosedSubspace.2
  have hcoh := fun q => @isCoherent_higherDirectImage_of_isProper_toBase k _ B hk _ _ (i ≫ f) pX
    hpX (i.hom ≫ pY) hpZ _ hO q
  have h0 := IntegralClosedSubspace.hasTranscendenceDegreeAt_zero_of_dimension_eq B (Spec (.of k))
    hk Y.2 X.2 hXdec hXLN f.hom hf Z d hZd hW
  have hη := IntegralClosedSubspace.isGenericPoint_pointsMap_ambientGenericPoint B (Spec (.of k))
    hk Y.2 X.2 hXdec f.hom Z
  let η := pointsMap B (Spec (.of k)) hk Y.1 f.hom (Z.ambientGenericPoint B (Spec (.of k)) hk)
  have hdimW := dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk
    X.2 hXdec W.isClosedSubspace.1 W.subspace.ι W.isClosedSubspace.2
  have hsub := fun q => IntegralClosedSubspace.supportOfSheaf_rightDerived_modulePushforward_subset
    B (Spec (.of k)) hk Y.2 X.2 hXdec f.hom hf Z q
  have hirr := isIrreducible_range_pointsMap_integralClosedSubspace B (Spec (.of k)) hk W
  have hdegT := hdimW.symm.trans hW
  obtain ⟨hfin, -⟩ := @eulerCharacteristic_eq_finsum_eulerCharacteristic_higherDirectImage.{u, w}
    k _ B hk _ _ (i ≫ f) pX hpX (i.hom ≫ pY) hpZ _ hO
  have hS : ∀ q ∉ hfin.toFinset,
      IsZero (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived q).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O))) := fun q hq => by
    simpa using hq
  rw [intersectionNumber_modulePullback_eq_sum.{u, w} k B hk pX hpX pY hpY f Z hZd L hfin.toFinset
    hS, Finset.sum_eq_single 0]
  · rw [pow_zero, one_mul, intersectionNumber_eq_sum]
    -- the image as a closed set with a single irreducible component
    set T := Set.range (pointsMap B (Spec (.of k)) hk W.subspace.toFunctor W.subspace.ι) with hTdef
    have hT : IsClosed T :=
      isClosed_range_pointsMap_integralClosedSubspace B (Spec (.of k)) hk X.2 W
    have : IrreducibleSpace T := isIrreducible_iff_irreducibleSpace.mp hirr
    have hcomp : irreducibleComponents T = {Set.univ} := irreducibleComponents_eq_singleton
    let C₀ : irreducibleComponents T := ⟨Set.univ, by rw [hcomp]; rfl⟩
    have hC : ∀ C : irreducibleComponents T, C = C₀ := fun C =>
      Subtype.ext (Set.mem_singleton_iff.1 (hcomp ▸ C.2))
    have himg : ∀ C : irreducibleComponents T, Subtype.val '' (C : Set T) = T := fun C => by
      rw [hC C]
      change Subtype.val '' (Set.univ : Set T) = T
      rw [Set.image_univ, Subtype.range_coe]
    let x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1 :=
      fun _ => canonicalGeometricPoint B (Spec (.of k)) hk X.1 η
    have hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)) := fun C => by
      rwa [himg C, canonicalGeometricPoint_image]
    obtain ⟨P, hPdeg, hval⟩ := exists_twistedEuler_sub_finsum_mul_componentStructureSheaf.{u, w}
      k B hk X pX hpX L hT x hx _ (hcoh 0) (hsub 0)
    -- the length of the direct image at the generic point of the image
    have := preservesFiniteLimits_modulePushforward B (Spec (.of k)) hk (i ≫ f)
    have hlen : (geometricLength B (Spec (.of k)) hk X (x C₀)
        (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O)))).toNat =
        degree B (Spec (.of k)) hk Z.isClosedSubspace.1 W.isClosedSubspace.1 Z.isIntegralSpace
          W.isIntegralSpace
          (IntegralClosedSubspace.toClosureImage B (Spec (.of k)) hk X.2 hXdec f.hom Z) := by
      rw [geometricLength_eq_of_iso B (Spec (.of k)) hk X (x C₀)
        (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerivedZeroIsoSelf).app _)]
      have hl := IntegralClosedSubspace.geometricLength_modulePushforward_eq_degree B (Spec (.of k))
        hk Y.2 X.2 hXdec hXLN f.hom hf Z h0 hη (x C₀) (canonicalGeometricPoint_image _ _ _ _ _)
      exact (congrArg ENat.toNat hl).trans (ENat.toNat_natCast _)
    have hset : {C : irreducibleComponents T | topologicalKrullDim (Subtype.val '' (C : Set T)) =
        topologicalKrullDim T} = {C₀} := by
      ext C
      refine ⟨fun _ => hC C, fun _ => ?_⟩
      change topologicalKrullDim (Subtype.val '' (C : Set T)) = topologicalKrullDim T
      rw [himg C]
    refine sum_neg_one_pow_mul_eq_mul_of_eval_eq_sub
      (fun n => @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O))) L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X pX hpX L _ (hcoh 0) n))
      (fun n => @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 pX hpX
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk
            (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)) L n)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X
          (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩) pX hpX
          (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)
          W.isClosedSubspace.2 L n))
      _ P (fun n => ?_) ?_
    · rw [hval n, hset, finsum_mem_singleton, hlen]
      push_cast
      congr 2
      exact congrArg (fun z : ℤ => (z : ℚ))
        (eulerCharacteristic_twist_structureSheafPushforward_congr.{u, w} k B hk pX hpX
          (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
            (closedSetComponentPoints B (Spec (.of k)) hk T hT C₀).isClosed)
          W.isClosedSubspace
          (eq_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _ _ W.subspace W.isClosedSubspace
            (himg C₀).symm W.isIntegralSpace.1).symm L n)
    · rw [hdegT] at hPdeg
      exact hPdeg.imp_right fun h => by exact_mod_cast h
  · intro q _ hq0
    rw [sum_neg_one_pow_mul_eulerCharacteristic_twist_eq_zero.{u, w} k B hk pX hpX L _ (hcoh q) ?_,
      mul_zero]
    have hfib : {z : points B (Spec (.of k)) hk ZA.1 |
        pointsMap B (Spec (.of k)) hk ZA.1 (i ≫ f).hom z = η}.Finite := by
      have h := IntegralClosedSubspace.setOf_pointsMap_eq_eq_singleton B (Spec (.of k)) hk Y.2 X.2
        hXdec f.hom hf Z h0 hη
      change {z | pointsMap B (Spec (.of k)) hk Z.subspace.toFunctor (Z.subspace.ι ≫ f.hom) z =
        η}.Finite
      rw [h]
      exact Set.finite_singleton _
    have hnot := notMem_supportOfSheaf_rightDerived_modulePushforward_of_finite B (Spec (.of k)) hk
      (Z := ZA) (X := X) Z.isIntegralSpace.2.1 hXdec (i ≫ f)
      (isProper_comp B (Spec (.of k)) hk ZA.2 Y.2 X.2 i.hom f.hom
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk ZA.2 Y.2 i.hom Z.isClosedSubspace.2) hf)
      _ hO.toIsQuasicoherentOnSite hfib q (Nat.pos_of_ne_zero hq0)
    have hcl := isClosed_moduleSupportSet B (Spec (.of k)) hk X _ (hcoh q)
    exact topologicalKrullDim_lt_of_subset_of_notMem hirr hcl (hsub q) hη.mem hnot hdegT.le
  · intro h0S
    rw [sum_neg_one_pow_mul_eulerCharacteristic_twist_eq_zero.{u, w} k B hk pX hpX L _ (hcoh 0) ?_,
      mul_zero]
    have he : moduleSupportSet B (Spec (.of k)) hk X
        (((modulePushforward B (Spec (.of k)) hk (i ≫ f)).rightDerived 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk ZA.1 ZA.2).O))) = ∅ :=
      supportOfSheaf_eq_empty_of_isZero B (Spec (.of k)) hk X (hS 0 h0S)
    rw [he]
    exact topologicalKrullDim_empty_lt d

/-- **Stacks 0EDJ.** Let `k` be a field, let `f : Y ⟶ X` be a morphism of algebraic spaces proper
over `k`, let `Z ⊂ Y` be an integral closed subspace of dimension `d` and let `L₁, …, L_d` be
invertible `𝒪_X`-modules. Let `f(Z) ⊂ X` be the image of `Z`: the integral closed subspace on the
closure of `f(|Z|)`, which is the scheme-theoretic image of `Z ⟶ X`, and has dimension at most
`d`. Then

`(f^*L₁ ⋯ f^*L_d · Z) = deg(Z/f(Z)) · (L₁ ⋯ L_d · f(Z))`

where `deg(Z/f(Z))` is the degree of Stacks 0AD6 if `dim f(Z) = d`, and the right hand side is
`0` if `dim f(Z) < d`.

The three conjuncts are: `f(Z)` is the scheme-theoretic image of `Z ⟶ X`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_subspace_eq_schemeTheoreticImage`,
Stacks 0830); `dim f(Z) ≤ d`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.dimension_closureImage_le`, Stacks 0EDC); and
the formula, which is
`AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq_degree_mul` when `dim f(Z) = d` and
`AlgebraicGeometry.Space.intersectionNumber_modulePullback_eq_zero_of_dimension_lt` otherwise. -/
@[stacks 0EDJ]
theorem intersectionNumber_modulePullback_eq (f : Y ⟶ X)
    (Z : IntegralClosedSubspace B (Spec (.of k)) hk Y.1) {d : ℕ}
    (hZd : dimension B (Spec (.of k)) hk Z.subspace.toFunctor Z.isClosedSubspace.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    let W := IntegralClosedSubspace.closureImage B (Spec (.of k)) hk X.2
      (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX) f.hom Z
    W.subspace = schemeTheoreticImageSubfunctor B (Spec (.of k)) hk (Z.subspace.ι ≫ f.hom) ∧
      dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 ≤ d ∧
      @intersectionNumber.{u, w} k _ B hk Y
          (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩) d pY hpY
          (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨Z.subspace, Z.isClosedSubspace⟩)
          Z.isClosedSubspace.2 hZd
          (fun j => (modulePullback B (Spec (.of k)) hk f).obj (L j))
          (fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk f (L j)
            (hM := hL j)) =
        if hW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 = d then
          (degree B (Spec (.of k)) hk Z.isClosedSubspace.1 W.isClosedSubspace.1 Z.isIntegralSpace
              W.isIntegralSpace
              (IntegralClosedSubspace.toClosureImage B (Spec (.of k)) hk X.2
                (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX) f.hom Z) : ℤ) *
            intersectionNumber.{u, w} k B hk X
              (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩) d pX
              hpX (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)
              W.isClosedSubspace.2 hW L
        else 0 := by
  intro W
  have hXdec := isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 pX hpX
  have hXLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 pX hpX
  have hf := isProper_of_isProper_toBase k B hk f pX hpX pY hpY
  have hle : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 ≤ d :=
    hZd ▸ IntegralClosedSubspace.dimension_closureImage_le B (Spec (.of k)) hk Y.2 X.2 hXdec hXLN
      f.hom hf Z
  refine ⟨IntegralClosedSubspace.closureImage_subspace_eq_schemeTheoreticImage B (Spec (.of k))
    hk X.2 hXdec f.hom Z, hle, ?_⟩
  split_ifs with hW
  · exact intersectionNumber_modulePullback_eq_degree_mul.{u, w} k B hk pX hpX pY hpY f Z hZd L hW
  · exact intersectionNumber_modulePullback_eq_zero_of_dimension_lt.{u, w} k B hk pX hpX pY hpY f
      Z hZd L (lt_of_le_of_ne hle hW)

end AlgebraicGeometry.Space

end
