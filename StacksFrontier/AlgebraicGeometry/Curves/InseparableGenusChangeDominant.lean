module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeProjection

/-!
# The coordinate projection of [Stacks, Tag 0CD1] is dominant

`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeExample.lean` constructs the
coordinate projection `f : Z ⟶ 𝐏¹_k` of [Stacks, Tag 0CD1] but only asserts that it *exists*.
This file gives it a name, `Stacks.Curves.InseparableGenus.planeCubicProjection`, and proves that
it is **dominant**, so that it induces an extension of function fields at all.

## Main definitions

* `Stacks.Curves.InseparableGenus.trivariateEquiv`: `k[T₀, T₁, T₂]` read as `k[T₀, T₁][T₂]`.
* `Stacks.Curves.InseparableGenus.planeCubicProjection`: the coordinate projection
  `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)` on the curve `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`.
* `Stacks.Curves.InseparableGenus.planeCubicGenericPoint`: the generic point of `Z`, the zero
  ideal of the graded quotient.
* `Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra`: **the embedding of `k(x)` into the
  function field of `Z` that `f` induces**, through the identification of the function field of
  `𝐏¹_k` with `RatFunc k`.

## Main results

* `Stacks.Curves.InseparableGenus.planeCubic_notDvd_coordProjHom`: `F` does not divide a nonzero
  polynomial in `T₀` and `T₁` — read in `T₂` the cubic has degree three and `G(T₀, T₁)` has
  degree zero.
* `Stacks.Curves.InseparableGenus.base_planeCubicProjection_planeCubicGenericPoint`: `f` carries
  the generic point of `Z` to the generic point of `𝐏¹_k`.
* `Stacks.Curves.InseparableGenus.isDominant_planeCubicProjection`: **`f` is dominant.**

## Implementation notes

The generic point of `Proj` of a graded domain is the zero ideal
(`AlgebraicGeometry.projBot`, `AlgebraicGeometry.isGenericPoint_projBot`, both in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurveDimension.lean`), and a morphism
out of a space with a generic point is dominant as soon as it hits a generic point of the target.
So dominance comes down to computing the homogeneous ideal of the image of the generic point of
`Z`, and that is read off the standard opens without computing the map on points at all: for
homogeneous `G` of positive degree, `f ⁻¹ᵁ D₊(G) = i ⁻¹ᵁ D₊(G(T₀, T₁))` by
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`, and
`i ⁻¹ᵁ D₊(s) = D₊(s mod F)` because `i` is `Proj` of the quotient map. So `G` vanishes at the
image of the generic point exactly when `F ∣ G(T₀, T₁)`, which happens only for `G = 0`. A form
of degree zero is multiplied by `T₀` first, which is why no separate argument about constants is
needed.

## Not done here

The identification

`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra =
  Stacks.Curves.InseparableGenus.chartRatFuncAlgebra`,

that is: the embedding of `k(x)` which `f` induces on function fields is the one the chart
`Z ∩ D₊(T₀)` gives, which sends `x` to the coordinate `T₁/T₀`. It is
`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean`; what it
needed, and what that file supplies, is `f` read on the sections of that chart —
`f ⁻¹ᵁ D₊(S₀) = Z ∩ D₊(T₀)`, on which `f` is `k[S₁/S₀] → k[Y₀, Y₁] ⧸ (Y₀² - Y₁³ + a)`,
`S₁/S₀ ↦ Y₀`.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)
open Stacks.RingTheory.HomogeneousQuotient (quotientGrading quotientMk)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom mapHom_preimage_basicOpen)

universe u

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### `k[T₀, T₁, T₂]` read as a polynomial ring in `T₂` -/

/-- `k[T₀, T₁, T₂]` read as `k[T₀, T₁][T₂]`, with `T₂` as the polynomial variable: the swap of
`T₀` and `T₂` followed by `MvPolynomial.finSuccEquiv`, which splits off the *first* variable. -/
def trivariateEquiv (k : Type u) [CommRing k] :
    MvPolynomial (Fin 3) k ≃+* Polynomial (MvPolynomial (Fin 2) k) :=
  (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 3) 2)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv k 2).toRingEquiv

/-- `trivariateEquiv` is the swap of `T₀` and `T₂` followed by `MvPolynomial.finSuccEquiv`. -/
theorem trivariateEquiv_apply (k : Type u) [CommRing k] (x : MvPolynomial (Fin 3) k) :
    trivariateEquiv k x =
      MvPolynomial.finSuccEquiv k 2 (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 2) x) := rfl

/-- `trivariateEquiv` sends a constant to the same constant. -/
@[simp] theorem trivariateEquiv_C (k : Type u) [CommRing k] (r : k) :
    trivariateEquiv k (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [trivariateEquiv_apply, MvPolynomial.rename_C]
  simp [MvPolynomial.finSuccEquiv_apply]

/-- `trivariateEquiv` sends `T₂` to the polynomial variable. -/
@[simp] theorem trivariateEquiv_X_two (k : Type u) [CommRing k] :
    trivariateEquiv k (MvPolynomial.X 2) = Polynomial.X := by
  rw [trivariateEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_right]
  simp [MvPolynomial.finSuccEquiv_apply]

/-- `trivariateEquiv` sends `T₀` to the constant polynomial `X 1`. -/
@[simp] theorem trivariateEquiv_X_zero (k : Type u) [CommRing k] :
    trivariateEquiv k (MvPolynomial.X 0) = Polynomial.C (MvPolynomial.X 1) := by
  rw [trivariateEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- `trivariateEquiv` sends `T₁` to the constant polynomial `X 0`. -/
@[simp] theorem trivariateEquiv_X_one (k : Type u) [CommRing k] :
    trivariateEquiv k (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
  rw [trivariateEquiv_apply, MvPolynomial.rename_X,
    show Equiv.swap (0 : Fin 3) 2 1 = (0 : Fin 2).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ]

/-- The cubic of [Stacks, Tag 0CD1], read as a polynomial in `T₂`: it is
`-(T₂³ - (T₁²T₀ + aT₀³))`, of degree three. -/
theorem trivariateEquiv_planeCubic (k : Type u) [CommRing k] (a : k) :
    trivariateEquiv k (planeCubic k a) =
      -(Polynomial.X ^ 3 - Polynomial.C (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
        MvPolynomial.C a * MvPolynomial.X 1 ^ 3)) := by
  rw [planeCubic]
  simp only [map_add, map_sub, map_mul, map_pow, trivariateEquiv_C, trivariateEquiv_X_zero,
    trivariateEquiv_X_one, trivariateEquiv_X_two]
  ring

/-- Over a nontrivial ring, the cubic read as a polynomial in `T₂` has degree three. -/
theorem natDegree_trivariateEquiv_planeCubic (k : Type u) [CommRing k] [Nontrivial k] (a : k) :
    (trivariateEquiv k (planeCubic k a)).natDegree = 3 := by
  rw [trivariateEquiv_planeCubic, Polynomial.natDegree_neg, Polynomial.natDegree_X_pow_sub_C]

/-- The coordinate projection on equations lands in the coefficients: `G(T₀, T₁)` has no `T₂`,
so read in `T₂` it is a constant — the constant being `G` with its two variables swapped, since
`trivariateEquiv` moves `T₀` past `T₂`. -/
theorem trivariateEquiv_coordProjHom (k : Type u) [CommRing k] (g : MvPolynomial (Fin 2) k) :
    trivariateEquiv k (coordProjHom k g) =
      Polynomial.C (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) g) := by
  have hX : ∀ j : Fin 2, trivariateEquiv k (coordProjHom k (MvPolynomial.X j)) =
      Polynomial.C (MvPolynomial.X (Equiv.swap (0 : Fin 2) 1 j)) := by
    intro j
    rw [coordProjHom_X]
    fin_cases j
    · exact (trivariateEquiv_X_zero k).trans (by simp)
    · exact (trivariateEquiv_X_one k).trans (by simp)
  refine MvPolynomial.induction_on
    (motive := fun x => trivariateEquiv k (coordProjHom k x) =
      Polynomial.C (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) x))
    g (fun r => ?_) (fun p q hp hq => ?_) (fun p j hp => ?_)
  · rw [show coordProjHom k (MvPolynomial.C r) = MvPolynomial.C r by simp [coordProjHom],
      trivariateEquiv_C, MvPolynomial.rename_C]
  · rw [map_add, map_add, hp, hq, map_add, Polynomial.C_add]
  · rw [map_mul, map_mul, hp, map_mul, Polynomial.C_mul, MvPolynomial.rename_X, ← hX j,
      coordProjHom_X]

/-- **The cubic does not divide a nonzero polynomial in `T₀` and `T₁`.** Read in `T₂`, the cubic
has degree three and `G(T₀, T₁)` has degree zero. -/
theorem planeCubic_notDvd_coordProjHom (k : Type u) [Field k] (a : k)
    {g : MvPolynomial (Fin 2) k} (hg : g ≠ 0) : ¬ planeCubic k a ∣ coordProjHom k g := by
  intro hdvd
  have hdvd' := map_dvd (trivariateEquiv k) hdvd
  rw [trivariateEquiv_coordProjHom] at hdvd'
  have hne : Polynomial.C (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) g) ≠ 0 := by
    simpa using fun h => hg ((MvPolynomial.rename_injective _ (Equiv.injective _)) h)
  have h := Polynomial.natDegree_le_of_dvd hdvd' hne
  rw [natDegree_trivariateEquiv_planeCubic, Polynomial.natDegree_C] at h
  omega

/-! ### The coordinate projection as a named morphism -/

/-- The curve lies in the domain of definition of the coordinate projection: it misses the point
`(0 : 0 : 1)` where the projection is undefined. -/
theorem range_base_subset_range_mapDomain (k : Type u) [Field k] (a : k) :
    Set.range (planeCubicEmbedding k a).base ⊆
      Set.range (mapDomain (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k)).ι.base := by
  rintro y ⟨x, rfl⟩
  exact ⟨⟨(planeCubicEmbedding k a).base x,
    mem_mapDomain_coordProjGradedHom a ((planeCubicEmbedding k a).base x)
      (planeCubic_mem_asHomogeneousIdeal a (planeCubicEmbedding k a)
        (idealOfClosedSubscheme_planeCubicEmbedding k a) x)⟩, rfl⟩

/-- **The coordinate projection `f : Z ⟶ 𝐏¹_k` of [Stacks, Tag 0CD1]** at the explicitly
constructed curve: the morphism whose existence `exists_coordProj_hom` asserts, given a name so
that statements can be made about it. -/
def planeCubicProjection (k : Type u) [Field k] (a : k) :
    planeCubicCurve k a ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
  IsOpenImmersion.lift
      (mapDomain (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k)).ι
      (planeCubicEmbedding k a) (range_base_subset_range_mapDomain k a) ≫
    mapHom _ _ (coordProjGradedHom k)

/-- **The projection is the coordinate projection `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`**: the standard
open of a homogeneous `G` of positive degree pulls back to the standard open of `G(T₀, T₁)`. -/
theorem planeCubicProjection_preimage_basicOpen (k : Type u) [Field k] (a : k)
    (G : MvPolynomial (Fin 2) k) (d : ℕ)
    (hG : G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) (hd : 0 < d) :
    planeCubicProjection k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
      planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G) := by
  rw [planeCubicProjection, Scheme.Hom.comp_preimage,
    mapHom_preimage_basicOpen _ _ _ G d hG hd, ← Scheme.Hom.comp_preimage,
    IsOpenImmersion.lift_fac]
  rfl

/-- The standard open of `s` pulls back along the embedding of the curve to the standard open of
`s` read in the quotient: the embedding is `Proj` of the quotient map. -/
theorem planeCubicEmbedding_preimage_basicOpen (k : Type u) [Field k] (a : k)
    (s : MvPolynomial (Fin 3) k) :
    planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 3) k) s =
      AlgebraicGeometry.Proj.basicOpen
        (quotientGrading (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a))
        (quotientMk (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a) s) :=
  AlgebraicGeometry.Proj.map_preimage_basicOpen _ _ s

/-! ### The projection is dominant -/

/-- **The generic point of the curve of [Stacks, Tag 0CD1]**: the zero ideal of the graded
quotient `k[T₀, T₁, T₂] ⧸ (F)`, which is a domain because `F` is irreducible. -/
def planeCubicGenericPoint (k : Type u) [Field k] (a : k) : ↥(planeCubicCurve k a) :=
  haveI := nonempty_planeCubicCurve k a
  AlgebraicGeometry.projBot (quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 3) k) (planeCubicIdeal k a))

/-- The homogeneous ideal of the generic point of the curve is the zero ideal. -/
@[simp] theorem asHomogeneousIdeal_planeCubicGenericPoint (k : Type u) [Field k] (a : k) :
    (planeCubicGenericPoint k a).asHomogeneousIdeal = ⊥ := rfl

/-- The projective line `Proj k[S₀, S₁]` over a field is nonempty. -/
instance nonempty_projectiveLine (k : Type u) [Field k] :
    Nonempty ↥(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :=
  haveI := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  inferInstance

/-- **The generic point of the curve lies over the standard open of every nonzero homogeneous
form of positive degree**: the projection carries it there because `F` does not divide
`G(T₀, T₁)`. -/
theorem mem_preimage_basicOpen_planeCubicGenericPoint (k : Type u) [Field k] (a : k) {d : ℕ}
    (hd : 0 < d) {g : MvPolynomial (Fin 2) k}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) (hgne : g ≠ 0) :
    planeCubicGenericPoint k a ∈ planeCubicProjection k a ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) g := by
  rw [planeCubicProjection_preimage_basicOpen k a g d hg hd,
    planeCubicEmbedding_preimage_basicOpen, AlgebraicGeometry.Proj.mem_basicOpen,
    asHomogeneousIdeal_planeCubicGenericPoint]
  intro hmem
  have h0 := Ideal.mem_bot.mp (HomogeneousIdeal.mem_iff.mpr hmem)
  rw [Stacks.RingTheory.HomogeneousQuotient.quotientMk_apply, Ideal.Quotient.eq_zero_iff_mem,
    toIdeal_planeCubicIdeal, Ideal.mem_span_singleton] at h0
  exact planeCubic_notDvd_coordProjHom k a hgne h0

/-- **No nonzero homogeneous form vanishes at the image of the generic point.** For a form of
positive degree this is `mem_preimage_basicOpen_planeCubicGenericPoint`; a form of degree zero is
multiplied by `T₀` first, which changes neither its vanishing nor its being nonzero. -/
theorem notMem_asHomogeneousIdeal_base_planeCubicGenericPoint (k : Type u) [Field k] (a : k)
    {d : ℕ} {g : MvPolynomial (Fin 2) k}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) (hgne : g ≠ 0) :
    g ∉ ((planeCubicProjection k a).base
      (planeCubicGenericPoint k a)).asHomogeneousIdeal := by
  intro hmem
  have hgX : g * MvPolynomial.X 0 ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k (d + 1) :=
    SetLike.mul_mem_graded hg (MvPolynomial.isHomogeneous_X k 0)
  have hne : g * MvPolynomial.X (0 : Fin 2) ≠ 0 :=
    mul_ne_zero hgne (MvPolynomial.X_ne_zero 0)
  have hmemX : g * MvPolynomial.X 0 ∈ ((planeCubicProjection k a).base
      (planeCubicGenericPoint k a)).asHomogeneousIdeal :=
    Ideal.mul_mem_right _ _ hmem
  exact ((AlgebraicGeometry.Proj.mem_basicOpen _ (g * MvPolynomial.X 0) _).mp
    (mem_preimage_basicOpen_planeCubicGenericPoint k a (Nat.succ_pos d) hgX hne)) hmemX

/-- **The projection carries the generic point of the curve to the generic point of `𝐏¹_k`.**
The homogeneous ideal of the image contains no nonzero homogeneous form, by
`notMem_asHomogeneousIdeal_base_planeCubicGenericPoint`, and a homogeneous ideal is determined by
its homogeneous elements. -/
theorem base_planeCubicProjection_planeCubicGenericPoint (k : Type u) [Field k] (a : k) :
    (planeCubicProjection k a).base (planeCubicGenericPoint k a) =
      AlgebraicGeometry.projBot (MvPolynomial.homogeneousSubmodule (Fin 2) k) := by
  classical
  refine ProjectiveSpectrum.ext ?_
  rw [AlgebraicGeometry.asHomogeneousIdeal_projBot]
  refine HomogeneousIdeal.toIdeal_injective ?_
  rw [HomogeneousIdeal.toIdeal_bot]
  refine le_antisymm (fun y hy => ?_) bot_le
  rw [Ideal.mem_bot]
  have hhom := ((planeCubicProjection k a).base
    (planeCubicGenericPoint k a)).asHomogeneousIdeal.isHomogeneous
  have hcomp := (Ideal.IsHomogeneous.mem_iff _ hhom).mp hy
  have hzero : ∀ i : ℕ,
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) y i :
        MvPolynomial (Fin 2) k)) = 0 := fun i => by
    by_contra hne
    exact notMem_asHomogeneousIdeal_base_planeCubicGenericPoint k a
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) y i).2 hne (hcomp i)
  rw [← DirectSum.sum_support_decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) y]
  exact Finset.sum_eq_zero fun i _ => hzero i

/-- **The coordinate projection `f : Z ⟶ 𝐏¹_k` of [Stacks, Tag 0CD1] is dominant.** It hits the
generic point of `𝐏¹_k`, whose closure is everything. -/
theorem isDominant_planeCubicProjection (k : Type u) [Field k] (a : k) :
    IsDominant (planeCubicProjection k a) := by
  have key : (Set.univ : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) k)))
      ⊆ closure (Set.range (planeCubicProjection k a).base) := by
    rw [← AlgebraicGeometry.isGenericPoint_projBot
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)]
    exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨planeCubicGenericPoint k a, base_planeCubicProjection_planeCubicGenericPoint k a⟩)
  rw [isDominant_iff]
  exact fun x => key (Set.mem_univ x)

/-! ### The extension of function fields that the projection induces -/

/-- **The extension of function fields that the coordinate projection `f : Z ⟶ 𝐏¹_k` of
[Stacks, Tag 0CD1] induces**, [Stacks, Tag 02JU]: the stalk map of `f` at the generic point,
available because `f` is dominant and both curves are integral. -/
def planeCubicProjectionFunctionFieldMap (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionField →+*
      (planeCubicCurve k a).functionField :=
  letI := isIntegral_planeCubicCurve k a ha
  letI := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  letI := isDominant_planeCubicProjection k a
  AlgebraicGeometry.dominantFunctionFieldMap (planeCubicProjection k a)

/-- **The embedding of `k(x)` into the function field of the curve that the projection
induces**: the extension of function fields of `f`, read through the identification of the
function field of `𝐏¹_k` with `RatFunc k`.

This is `Stacks.Curves.InseparableGenus.chartRatFuncAlgebra`, the embedding the chart
`Z ∩ D₊(T₀)` gives, by
`Stacks.Curves.InseparableGenus.projectionRatFuncAlgebra_eq_chartRatFuncAlgebra`. -/
@[instance_reducible] def projectionRatFuncAlgebra (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) : Algebra (RatFunc k) (planeCubicCurve k a).functionField :=
  ((planeCubicProjectionFunctionFieldMap k a ha).comp
    (projectiveLineFunctionFieldEquiv k).symm.toRingHom).toAlgebra

end Stacks.Curves.InseparableGenus

end
