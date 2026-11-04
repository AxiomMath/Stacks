module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.EmbeddedPointCounterexample
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product of a smooth scheme and the Chern character

Let `k` be a field and let `X` be a scheme smooth over `k`. Section 0FC0 of the Stacks Project
defines the intersection product `α · β = Δ^!(α × β)` on `CH_*(X)`: if `X` is equidimensional of
dimension `d` it carries `CH_n(X) × CH_m(X)` to `CH_{n+m-d}(X)`, "and in general we can decompose
into the parts lying over the open and closed subschemes of `X` where `X` has a given dimension".
For `X` quasi-compact only finitely many of the parts `X_d` are nonempty; the product on each part
`X_d` is the product of Stacks 0FC0 formed with the Gysin class of the diagonal of `X_d`
(Stacks 0FBR), and on `CH^*(X) = ∏_d CH^*(X_d)` it is `Stacks.Chow.codimensionIntersectionProduct`.

Section 0FEX defines a product on `CH_*(X) ⊗ 𝐐` for `X` regular, by
`(ch(α') ∩ [X]) · β = ch(α') ∩ β` for `α' ∈ K_0(Vect(X)) ⊗ 𝐐`, and Stacks 0FFF asserts that it
agrees with the product of Section 0FC0 for `X` smooth over `k`. The proof of the source rests on
Stacks 0FC2: on a part `X_d`, which is equidimensional of dimension `d`, a class `c ∈ A^p(X_d)`
satisfies `(c ∩ [X_d]) · β = c ∩ β`. This file supplies the part-by-part form of that identity on
`X`: for every nonempty part `X_d` and `c ∈ A^p(X) ⊗ 𝐐`,

  `(c ∩ β)|_{X_d} = (c ∩ [X])|_{X_d} · β|_{X_d}`,

since restriction to `X_d` carries `c ∩ -` to `res(c) ∩ -` and `[X]` to `[X_d]`; summing over `p`
gives the same for a total class such as `ch(α') = ∑_p ch_p(α')`, the sum being finite on each
`CH_n(X) ⊗ 𝐐`. Together with the decomposition `CH_*(X) ⊗ 𝐐 = ⨁_d CH_*(X_d) ⊗ 𝐐` proved here,
this determines the product of Section 0FEX part by part.

## Main definitions

* `Stacks.Chow.rationalSelfIntersectionProduct`: the product `CH_*(W) ⊗ 𝐐 × CH_*(W) ⊗ 𝐐 ⟶
  CH_*(W) ⊗ 𝐐` induced by the intersection product of Stacks 0FC0 formed with a class of the
  diagonal of `W` of a given degree.
* `Stacks.Chow.nonemptyDimParts`: the finitely many `d` with `X_d` nonempty, for `X`
  quasi-compact.
* `Stacks.Chow.rationalRestrictPart`, `Stacks.Chow.rationalIncludePart`: restriction to the part
  `X_d` and pushforward from it, on rational Chow groups.

## Main results

* `Stacks.Chow.sum_rationalIncludePart_rationalRestrictPart`:
  `CH_*(X) ⊗ 𝐐 = ⨁_d CH_*(X_d) ⊗ 𝐐`, through restriction to and pushforward from the parts.

* `Stacks.Chow.rationalRestrictPart_rationalChowCap_eq_canonicalRationalIntersectionProduct`,
  `Stacks.Chow.rationalRestrictPart_totalRationalChowCap_eq_canonicalRationalIntersectionProduct`:
  `(c ∩ β)|_{X_d} = (c ∩ [X])|_{X_d} · β|_{X_d}` on every nonempty part, for the product of
  Stacks 0FC0 on `X_d`; the comparison of Stacks 0FFF with the product of Section 0FEX is
  assembled from it in
  `StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.RationalIntersectionProduct`.

## Implementation notes

The parts `X_d` are `Stacks.WeilCohomology.dimPart`, and the product on each part is formed with
`Stacks.WeilCohomology.canonicalDiagonalClassFamily`, the Gysin class of the diagonal of
Stacks 0FBR; on integral classes it is `Stacks.Chow.dimPartIntersectionProduct`. Stacks 0FC2 for
that family is `Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`. No
separatedness of `X` is assumed: the decomposition `CH_*(X) ⊗ 𝐐 = ⨁_d CH_*(X_d) ⊗ 𝐐` is proved
here from the decomposition of Chow groups along a family of open and closed subschemes
(`Stacks.Chow.eq_zero_of_chowGroupRestrict_eq_zero`). Quasi-compactness is expressed as
`AlgebraicGeometry.IsNoetherian X` where the fundamental class `[X] ∈ CH_*(X) ⊗ 𝐐` is used; for
`X` locally of finite type over `k` the two are equivalent.

Only the second clause of Stacks 0FC2 enters, in the form `c ∩ β = (c ∩ [X_d]_d) · β` on each
part.

## References

* [Stacks Project, Section 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
* [Stacks Project, Tag 0FFF](https://stacks.math.columbia.edu/tag/0FFF)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart canonicalDiagonalClassFamily
  canonicalDiagonalClassFamily_capEqProduct fieldGysinSystem
  restrictPart includePart)

open Stacks.Sheaves.BilinearChangeOfRings (baseChange₂ baseChange₂_tmul)

universe u

namespace Stacks.Chow

/-! ### The rational intersection product on a scheme with a diagonal class -/

section SelfProduct

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (D : ℤ)
  (Dc : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
    (diagonal_comp_selfProductStructure C sW) D)

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j

/-- **The intersection product of Stacks 0FC0 on `CH_*(W) ⊗ 𝐐`**, for a scheme `W` whose diagonal
carries the Gysin class `Dc` of degree `D`: on `CH_n(W) ⊗ 𝐐 × CH_m(W) ⊗ 𝐐` it is the base change
to `𝐐` of `Stacks.Chow.selfIntersectionProduct`, landing in `CH_{n+m-D}(W) ⊗ 𝐐`. -/
def rationalSelfIntersectionProduct : CHQ →ₗ[ℚ] CHQ →ₗ[ℚ] CHQ :=
  DirectSum.toModule ℚ ℤ _ fun n => LinearMap.flip <| DirectSum.toModule ℚ ℤ _ fun m =>
    LinearMap.flip <| (baseChange₂ (S := ℚ) (selfIntersectionProduct C hδ G sW D Dc n m)).compr₂
      (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) (n + m - D))

/-- The rational intersection product on `CH_n(W) ⊗ 𝐐 × CH_m(W) ⊗ 𝐐`. -/
theorem rationalSelfIntersectionProduct_lof_lof (n m : ℤ) (s : ℚ ⊗[ℤ] chowGroup C sW n)
    (t : ℚ ⊗[ℤ] chowGroup C sW m) :
    rationalSelfIntersectionProduct C hδ G sW D Dc
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) n s)
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) m t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) (n + m - D)
        (baseChange₂ (S := ℚ) (selfIntersectionProduct C hδ G sW D Dc n m) s t) := by
  simp only [rationalSelfIntersectionProduct, DirectSum.toModule_lof, LinearMap.flip_apply,
    LinearMap.compr₂_apply]

/-- The rational intersection product of `r ⊗ α` and `q ⊗ β` is `rq ⊗ (α · β)`. -/
theorem rationalSelfIntersectionProduct_of_tmul (n m : ℤ) (r : ℚ) (a : chowGroup C sW n)
    (q : ℚ) (b : chowGroup C sW m) :
    rationalSelfIntersectionProduct C hδ G sW D Dc
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) n (r ⊗ₜ a))
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) m (q ⊗ₜ b)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sW j) (n + m - D)
        ((r * q) ⊗ₜ selfIntersectionProduct C hδ G sW D Dc n m a b) := by
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, rationalSelfIntersectionProduct_lof_lof,
    baseChange₂_tmul, DirectSum.lof_eq_of]

end SelfProduct

/-! ### Schemes smooth of constant dimension over a field -/

section Constant

variable (k : Type u) [Field k]

local notation "CHQ(" s ")" =>
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) s j

/-- **The fundamental class of a scheme flat of relative dimension `N` over `k` is concentrated in
degree `N`**: every irreducible component has dimension `N` (Stacks 02R8), so `[W]_n = 0` for
`n ≠ N`. -/
theorem fundamentalChowClass_eq_zero_of_relativeDimension {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Flat sW] {N : ℕ}
    (hN : RelativeDimension sW N) {n : ℤ} (hn : n ≠ N) :
    fundamentalChowClass (fieldChowSituation k) sW n = 0 := by
  refine fundamentalChowClass_eq_zero_of_deltaDimension_eq (fieldChowSituation k) sW
    (fun V => ?_) hn
  have h := deltaDimension_irreducibleComponent_eq_add_of_irreducible (fieldChowSituation k) sW
    (𝟙 _) N hN V
  rw [deltaDimension_eq_of_isGenericPoint (fieldChowSituation k) (𝟙 _) _ _
      (genericPoint_spec (fieldChowSituation k).S),
    relativeDimension_id_fieldChowSituation_eq_zero, zero_add] at h
  simpa only [Category.comp_id] using h

/-- A sum of `1 ⊗ f n` over `s` collapses to the term `N` when `f` vanishes off `N`, and at `N`
if `N ∉ s`. -/
private theorem sum_of_one_tmul_eq_of_eq_zero {G : ℤ → Type*} [∀ n, AddCommGroup (G n)]
    (s : Finset ℤ) (N : ℤ) (f : ∀ n, G n) (h : ∀ n, n ≠ N → f n = 0) (h0 : N ∉ s → f N = 0) :
    ∑ n ∈ s, DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] G j) n ((1 : ℚ) ⊗ₜ f n) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] G j) N ((1 : ℚ) ⊗ₜ f N) := by
  by_cases hN : N ∈ s
  · refine Finset.sum_eq_single_of_mem _ hN fun n _ hn => ?_
    rw [h n hn, TensorProduct.tmul_zero, map_zero]
  · rw [h0 hN, TensorProduct.tmul_zero, map_zero]
    exact Finset.sum_eq_zero fun n hn => by
      rw [h n (fun e => hN (e ▸ hn)), TensorProduct.tmul_zero, map_zero]

/-- For `W` flat of relative dimension `N` over `k` and Noetherian, the fundamental class
`[W] ∈ CH_*(W) ⊗ 𝐐` is `1 ⊗ [W]_N`. -/
theorem rationalFundamentalClass_eq_of_relativeDimension {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Flat sW] [IsNoetherian W]
    {N : ℕ} (hN : RelativeDimension sW N) :
    rationalFundamentalClass (fieldChowSituation k) sW =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sW j) N
        ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) sW N) := by
  rw [rationalFundamentalClass_eq]
  refine sum_of_one_tmul_eq_of_eq_zero _ N _
    (fun n hn => fundamentalChowClass_eq_zero_of_relativeDimension k sW hN hn) fun hN' => ?_
  rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees _ sW
    fun h => hN' ((fundamentalClassDegrees_finite _ sW).mem_toFinset.2 h), map_zero]

/-- The rational intersection product of Stacks 0FC0 on a scheme `W` smooth over `k` of constant
dimension `N`, formed with the Gysin class of its diagonal (Stacks 0FBR). -/
abbrev canonicalRationalIntersectionProduct {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)
    [Smooth sW] (N : ℕ) (hN : RelativeDimension sW N) :
    CHQ(sW) →ₗ[ℚ] CHQ(sW) →ₗ[ℚ] CHQ(sW) :=
  rationalSelfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN)

/-- **Stacks 0FC2 on `CH_*(W) ⊗ 𝐐`.** For `W` smooth and Noetherian over `k`, of
constant dimension `N`, and `c ∈ A^p(W) ⊗ 𝐐`,

  `(c ∩ [W]) · β = c ∩ β`

for the intersection product of Stacks 0FC0. It is the second clause of Stacks 0FC2 in the form
`c ∩ β = (c ∩ [W]_N) · β` (`Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`),
`[W]` being concentrated in degree `N`. -/
theorem canonicalRationalIntersectionProduct_rationalChowCap {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [Smooth sW] [IsNoetherian W] {N : ℕ}
    (hN : RelativeDimension sW N) (p : ℤ)
    (c : rationalChowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sW p)
    (y : CHQ(sW)) :
    canonicalRationalIntersectionProduct k sW N hN
        (rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sW p c
          (rationalFundamentalClass (fieldChowSituation k) sW)) y =
      rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sW p c y := by
  rw [rationalFundamentalClass_eq_of_relativeDimension k sW hN]
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add c c' hc hc' => simp only [map_add, LinearMap.add_apply, hc, hc']
  | tmul r c =>
    rw [rationalChowCap_of_tmul, mul_one, chowCohomologyCap_fundamentalChowClass]
    refine LinearMap.congr_fun (rationalChowHomology_linearMap_ext _ sW fun m q β => ?_) y
    rw [rationalSelfIntersectionProduct_of_tmul, rationalChowCap_of_tmul]
    refine of_tmul_eq_of_tmul_of_heq _ sW (by ring) _ ?_
    rw [canonicalDiagonalClassFamily_capEqProduct k sW N hN p c m β]
    exact (chowGroupDegreeEquiv_heq _ _ _ _).symm

/-- On a scheme all of whose points have nonnegative `δ`, for instance one locally of finite type
over `k`, the total cap operation of a family `c ∈ ∏_p A^p(W) ⊗ 𝐐` on a given class is the sum of
the `c_p ∩ -` over all `p ≤ M`, for every large enough `M`. -/
theorem exists_totalRationalChowCap_eq_sum_range {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    (G : GysinSystem (fieldChowSituation k))
    (c : fullRationalChowCohomology (fieldChowSituation k) G sW)
    (x : CHQ(sW)) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      totalRationalChowCap (fieldChowSituation k) G sW c x =
        ∑ p ∈ Finset.range (M + 1),
          rationalChowCap (fieldChowSituation k) G sW p (c p) x := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, fun M _ => by simp only [map_zero, Finset.sum_const_zero]⟩
  | of j t =>
    refine ⟨j.toNat, fun M hM => ?_⟩
    rw [← DirectSum.lof_eq_of ℚ]
    exact totalRationalChowCap_lof_eq_sum_range _ _ sW 0
      (fun x => relativeDimension_fieldChowSituation_nonneg k sW x) c j t M (by omega)
  | add x y hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨max N₁ N₂, fun M hM => ?_⟩
    rw [map_add, h₁ M (le_of_max_le_left hM), h₂ M (le_of_max_le_right hM),
      ← Finset.sum_add_distrib]
    simp only [map_add]

end Constant

/-! ### The parts of a smooth scheme -/

section Parts

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX]

local notation "CHQ(" s ")" =>
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) s j

/-- The finitely many dimensions `d` for which the part `X_d` of a quasi-compact scheme smooth
over `k` is nonempty: the parts are disjoint and open, hence a locally finite family. -/
def nonemptyDimParts [CompactSpace X] : Finset ℕ :=
  Set.Finite.toFinset (s := {d | (dimPart sX d : Set X).Nonempty})
    (Stacks.Topology.locallyFinite_of_disjoint_open_cover _ (fun d ↦ (dimPart sX d).2)
      (isClopenDecomposition_dimPart sX).exists_mem fun _ _ hij ↦
        TopologicalSpace.Opens.coe_disjoint.2
          ((isClopenDecomposition_dimPart sX).disjoint _ _ hij)).finite_nonempty_of_compact

/-- `d` lies in `Stacks.Chow.nonemptyDimParts` exactly when the part `X_d` is nonempty. -/
theorem mem_nonemptyDimParts [CompactSpace X] {d : ℕ} :
    d ∈ nonemptyDimParts k sX ↔ (dimPart sX d : Set X).Nonempty :=
  Set.Finite.mem_toFinset _

/-- **The parts decompose `CH_m(X)`**: for `X` quasi-compact, a class is the sum over the
nonempty parts of the pushforwards of its restrictions. -/
theorem sum_properChowPushforward_chowGroupRestrict_dimPart [CompactSpace X] (m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX m) :
    ∑ d ∈ nonemptyDimParts k sX, (haveI := (isClopenDecomposition_dimPart sX).isProper_ι d
      properChowPushforward (fieldChowSituation k) (partBase sX d) sX (dimPart sX d).ι rfl m
        (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m
          α)) = α := by
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero (fieldChowSituation k) sX
    (fun i : ULift.{u} ℕ ↦ partBase sX i.down) (fun i ↦ (dimPart sX i.down).ι) (fun _ ↦ rfl)
    ⟨fun i j hij ↦ by
      simpa only [Scheme.Opens.opensRange_ι] using
        (isClopenDecomposition_dimPart sX).disjoint i.down j.down
          fun h ↦ hij (ULift.ext _ _ h), by
      simp only [Scheme.Opens.opensRange_ι]
      exact (ULift.down_surjective.iSup_comp (dimPart sX)).trans
        (isClopenDecomposition_dimPart sX).iSup_eq_top⟩ m _ fun i ↦ ?_
  rw [map_sub, map_sum, sub_eq_zero]
  by_cases hi : i.down ∈ nonemptyDimParts k sX
  · rw [Finset.sum_eq_single i.down]
    · have := (isClopenDecomposition_dimPart sX).isProper_ι i.down
      exact chowGroupRestrict_properChowPushforward_opens_self _ _ _ _ _ _
    · intro d _ hd
      have := (isClopenDecomposition_dimPart sX).isProper_ι d
      exact chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
        ((isClopenDecomposition_dimPart sX).disjoint d i.down hd) _ _ _
    · exact fun h ↦ (h hi).elim
  · have : IsEmpty (dimPart sX i.down).toScheme :=
      ⟨fun y ↦ hi ((mem_nonemptyDimParts k sX).2 ⟨y.1, y.2⟩)⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX i.down) m
    exact Subsingleton.elim _ _

/-- A part `X_d` of a Noetherian scheme smooth over `k` is Noetherian, being open and closed. -/
instance isNoetherian_dimPart [IsNoetherian X] (d : ℕ) : IsNoetherian (dimPart sX d).toScheme :=
  haveI : CompactSpace (dimPart sX d).toScheme := isCompact_iff_compactSpace.mp
    ((isClopenDecomposition_dimPart sX).isClopen d).1.isCompact
  ⟨⟩

/-- Restriction `CH_*(X) ⊗ 𝐐 ⟶ CH_*(X_d) ⊗ 𝐐` to the part of dimension `d`. -/
abbrev rationalRestrictPart (d : ℕ) : CHQ(sX) →ₗ[ℚ] CHQ(partBase sX d) :=
  rationalChowMap (fieldChowSituation k) (partBase sX d) sX (fun j => j)
    fun j => chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl j

/-- Pushforward `CH_*(X_d) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐` along the closed immersion of the part of
dimension `d`. -/
abbrev rationalIncludePart (d : ℕ) : CHQ(partBase sX d) →ₗ[ℚ] CHQ(sX) :=
  haveI := (isClopenDecomposition_dimPart sX).isProper_ι d
  rationalProperChowPushforward (fieldChowSituation k) (partBase sX d) sX
    (f := (dimPart sX d).ι) rfl

/-- Restriction to a part on `CH_m(X) ⊗ 𝐐` is `Stacks.WeilCohomology.restrictPart`. -/
theorem rationalRestrictPart_lof (d : ℕ) (m : ℤ)
    (t : ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX m) :
    rationalRestrictPart k sX d
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
        m (restrictPart k sX d m t) :=
  rationalChowMap_lof _ _ _ _ _ m t

/-- Pushforward from a part on `CH_m(X_d) ⊗ 𝐐` is `Stacks.WeilCohomology.includePart`. -/
theorem rationalIncludePart_lof (d : ℕ) (m : ℤ)
    (t : ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) m) :
    rationalIncludePart k sX d
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
          m t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m
        (includePart k sX d m t) :=
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  rationalProperChowPushforward_lof _ _ _ _ m t

/-- Restricting to a part what was pushed forward from it is the identity. -/
theorem rationalRestrictPart_rationalIncludePart (d : ℕ) (z : CHQ(partBase sX d)) :
    rationalRestrictPart k sX d (rationalIncludePart k sX d z) = z := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  refine LinearMap.congr_fun (f := (rationalRestrictPart k sX d).comp (rationalIncludePart k sX d))
    (g := LinearMap.id) (rationalChowHomology_linearMap_ext _ (partBase sX d) fun m q α => ?_) z
  simp only [LinearMap.comp_apply, rationalProperChowPushforward_of_tmul, rationalChowMap_of_tmul,
    chowGroupRestrict_properChowPushforward_opens_self, LinearMap.id_apply]

/-- Restricting to a part what was pushed forward from another part gives zero. -/
theorem rationalRestrictPart_rationalIncludePart_of_ne {d d' : ℕ} (h : d ≠ d')
    (z : CHQ(partBase sX d)) :
    rationalRestrictPart k sX d' (rationalIncludePart k sX d z) = 0 := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  refine LinearMap.congr_fun (f := (rationalRestrictPart k sX d').comp (rationalIncludePart k sX d))
    (g := 0) (rationalChowHomology_linearMap_ext _ (partBase sX d) fun m q α => ?_) z
  simp only [LinearMap.comp_apply, rationalProperChowPushforward_of_tmul, rationalChowMap_of_tmul,
    chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
      ((isClopenDecomposition_dimPart sX).disjoint d d' h), TensorProduct.tmul_zero, map_zero,
    LinearMap.zero_apply]

/-- **The parts decompose `CH_*(X) ⊗ 𝐐`**: for `X` quasi-compact, a class is the sum over the
nonempty parts of the pushforwards of its restrictions. -/
theorem sum_rationalIncludePart_rationalRestrictPart [CompactSpace X] (y : CHQ(sX)) :
    ∑ d ∈ nonemptyDimParts k sX,
      rationalIncludePart k sX d (rationalRestrictPart k sX d y) = y := by
  suffices key : ∑ d ∈ nonemptyDimParts k sX,
      (rationalIncludePart k sX d).comp (rationalRestrictPart k sX d) = LinearMap.id by
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun key y
  refine rationalChowHomology_linearMap_ext _ sX fun m q α => ?_
  have h : ∀ d ∈ nonemptyDimParts k sX,
      rationalIncludePart k sX d (rationalRestrictPart k sX d
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m (q ⊗ₜ α))) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m
        (q ⊗ₜ (have := (isClopenDecomposition_dimPart sX).isProper_ι d
          properChowPushforward (fieldChowSituation k) (partBase sX d) sX (dimPart sX d).ι
            rfl m (properPushforwardDescends _ _ _ _ _ _)
            (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι
              rfl m α))) := fun d _ => by
    have := (isClopenDecomposition_dimPart sX).isProper_ι d
    rw [rationalChowMap_of_tmul, rationalProperChowPushforward_of_tmul]
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  simp only [LinearMap.comp_apply]
  rw [Finset.sum_congr rfl h, ← map_sum, ← TensorProduct.tmul_sum,
    sum_properChowPushforward_chowGroupRestrict_dimPart]

/-- **The projection formula for a part**: `(i_d)_*(res(c) ∩ z) = c ∩ (i_d)_* z` for
`c ∈ A^p(X) ⊗ 𝐐`. -/
theorem rationalIncludePart_rationalChowCap (d : ℕ) (p : ℤ)
    (c : rationalChowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sX p)
    (z : CHQ(partBase sX d)) :
    rationalIncludePart k sX d (rationalChowCap (fieldChowSituation k) (fieldGysinSystem k)
        (partBase sX d) p
        ((chowCohomologyRestrictionOfEq (fieldChowSituation k) (partBase sX d) sX
          (f := (dimPart sX d).ι) rfl (gysinSystemOfInvertible _)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p).toIntLinearMap.baseChange ℚ
          c) z) =
      rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sX p c
        (rationalIncludePart k sX d z) :=
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  LinearMap.congr_fun (rationalProperChowPushforward_comp_rationalChowCap _ (partBase sX d) sX
    (f := (dimPart sX d).ι) rfl p c) z

/-- **Restriction to a part commutes with capping**: `(c ∩ y)|_{X_d} = res(c) ∩ y|_{X_d}` for
`c ∈ A^p(X) ⊗ 𝐐` and a nonempty part `X_d` of a quasi-compact `X`. -/
theorem rationalRestrictPart_rationalChowCap [CompactSpace X] {d : ℕ}
    (hd : d ∈ nonemptyDimParts k sX) (p : ℤ)
    (c : rationalChowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sX p)
    (y : CHQ(sX)) :
    rationalRestrictPart k sX d (rationalChowCap (fieldChowSituation k) (fieldGysinSystem k)
        sX p c y) =
      rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) (partBase sX d) p
        ((chowCohomologyRestrictionOfEq (fieldChowSituation k) (partBase sX d) sX
          (f := (dimPart sX d).ι) rfl (gysinSystemOfInvertible _)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _) p).toIntLinearMap.baseChange ℚ
          c)
        (rationalRestrictPart k sX d y) := by
  conv_lhs => rw [← sum_rationalIncludePart_rationalRestrictPart k sX y]
  rw [map_sum, map_sum, Finset.sum_eq_single_of_mem d hd]
  · rw [← rationalIncludePart_rationalChowCap, rationalRestrictPart_rationalIncludePart]
  · intro d' _ hd'
    rw [← rationalIncludePart_rationalChowCap,
      rationalRestrictPart_rationalIncludePart_of_ne k sX hd']

/-- **The fundamental class restricts to the fundamental class**: `[X]|_{X_d} = [X_d]` in
`CH_*(X_d) ⊗ 𝐐`. -/
theorem rationalRestrictPart_rationalFundamentalClass [IsNoetherian X] (d : ℕ) :
    rationalRestrictPart k sX d (rationalFundamentalClass (fieldChowSituation k) sX) =
      rationalFundamentalClass (fieldChowSituation k) (partBase sX d) := by
  rw [rationalFundamentalClass_eq_of_relativeDimension k (partBase sX d)
      (relativeDimension_partBase sX d), rationalFundamentalClass_eq, map_sum]
  simp only [rationalChowMap_of_tmul, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  refine sum_of_one_tmul_eq_of_eq_zero _ d _ (fun n hn =>
    fundamentalChowClass_eq_zero_of_relativeDimension k _ (relativeDimension_partBase sX d) hn)
    fun hd => ?_
  rw [← chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion _ sX (partBase sX d)
      (dimPart sX d).ι rfl, fundamentalChowClass,
    fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees _ sX
      fun h => hd ((fundamentalClassDegrees_finite _ sX).mem_toFinset.2 h), map_zero, map_zero]

/-! ### Stacks 0FC2 on the parts -/

/-- **Stacks 0FC2 on a part, for a single class**: for `X` smooth and Noetherian over `k`, a
nonempty part `X_d` and `c ∈ A^p(X) ⊗ 𝐐`,

  `(c ∩ y)|_{X_d} = (c ∩ [X])|_{X_d} · y|_{X_d}`

for the intersection product of Stacks 0FC0 on `X_d`. Restriction to the part carries `c ∩ -`
to `res(c) ∩ -` and `[X]` to `[X_d]`, and on `X_d` the identity is
`Stacks.Chow.canonicalRationalIntersectionProduct_rationalChowCap`. -/
theorem rationalRestrictPart_rationalChowCap_eq_canonicalRationalIntersectionProduct
    [IsNoetherian X] {d : ℕ} (hd : d ∈ nonemptyDimParts k sX) (p : ℤ)
    (c : rationalChowCohomologyComponent (fieldChowSituation k) (fieldGysinSystem k) sX p)
    (y : CHQ(sX)) :
    rationalRestrictPart k sX d
        (rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sX p c y) =
      canonicalRationalIntersectionProduct k (partBase sX d) d (relativeDimension_partBase sX d)
        (rationalRestrictPart k sX d
          (rationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sX p c
            (rationalFundamentalClass (fieldChowSituation k) sX)))
        (rationalRestrictPart k sX d y) := by
  rw [rationalRestrictPart_rationalChowCap k sX hd, rationalRestrictPart_rationalChowCap k sX hd,
    rationalRestrictPart_rationalFundamentalClass,
    canonicalRationalIntersectionProduct_rationalChowCap]

/-- **Stacks 0FC2 on a part, for a total class**: for `X` smooth and Noetherian over `k`, a
nonempty part `X_d` and `c ∈ ∏_p A^p(X) ⊗ 𝐐` acting by its total cap operation,
`(c ∩ y)|_{X_d} = (c ∩ [X])|_{X_d} · y|_{X_d}` for the intersection product of Stacks 0FC0 on
`X_d`. -/
theorem rationalRestrictPart_totalRationalChowCap_eq_canonicalRationalIntersectionProduct
    [IsNoetherian X] {d : ℕ} (hd : d ∈ nonemptyDimParts k sX)
    (c : fullRationalChowCohomology (fieldChowSituation k) (fieldGysinSystem k) sX)
    (y : CHQ(sX)) :
    rationalRestrictPart k sX d
        (totalRationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sX c y) =
      canonicalRationalIntersectionProduct k (partBase sX d) d (relativeDimension_partBase sX d)
        (rationalRestrictPart k sX d
          (totalRationalChowCap (fieldChowSituation k) (fieldGysinSystem k) sX c
            (rationalFundamentalClass (fieldChowSituation k) sX)))
        (rationalRestrictPart k sX d y) := by
  obtain ⟨N₁, h₁⟩ := exists_totalRationalChowCap_eq_sum_range k sX (fieldGysinSystem k) c
    (rationalFundamentalClass (fieldChowSituation k) sX)
  obtain ⟨N₂, h₂⟩ := exists_totalRationalChowCap_eq_sum_range k sX (fieldGysinSystem k) c y
  rw [h₁ (max N₁ N₂) (le_max_left _ _), h₂ (max N₁ N₂) (le_max_right _ _)]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun p _ =>
    rationalRestrictPart_rationalChowCap_eq_canonicalRationalIntersectionProduct k sX hd p (c p) y

end Parts

end Stacks.Chow

end
