module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SupportedWeightOperator
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CoherentLeadingTerm
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.WeightSeparation
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.WideLayerClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# Injectivity in Stacks 0FEW, given an operator with codimension weights

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : X ⟶ Y` be a
closed immersion of schemes locally of finite type over `S`, with `Y` regular and quasi-compact,
and write `G(Z) = 𝐐 ⊗ K₀(Coh_Z(X))` for the closed subsets `Z ⊆ X`. The Adams-type operator `ψ`
of the proof of Stacks 0FEW is a natural endomorphism of `G` with *codimension* weights: whenever
every point of `Z` has `δ ≤ k`, at a point `ξ ∈ Z` with `δ(ξ) = k` the coefficient of the
`k`-cycle of `ψ x` is `ℓ^{c(ξ)}` times that of `x`, where `c(ξ) = dim 𝒪_{Y, i(ξ)}`. This file
shows that such a `ψ` already gives the injectivity of `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, with no bound
on `δ` and no separatedness of `Y`.

The argument is the separation of weights of
`Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup_of_exists_multiset`, with the weight `c`
in place of `-δ`.

* On a nonempty closed `Z`, let `k` be the largest value of `δ` on `Z`. The points of `Z` with
  `δ = k` admit no proper generization in `Z`, so they are generic points of the finitely many
  irreducible components of `Z`. If `p` is the product of the factors `X - ℓ^{c(ξ)}` over these
  points, the `k`-cycle of `p(ψ) x` has coefficient `p(ℓ^{c(ξ)}) · [x]_k(ξ) = 0` at each of them,
  and is zero elsewhere, so `p(ψ) x` comes from a closed `Z' ⊊ Z` on which `δ ≤ k - 1`. Noetherian
  induction then kills every element of `G(Z)` by a product of factors `ψ - ℓ^n` over weights
  `n` of points of `Z`.
* Along a specialization `η ⤳ ξ` the drop `δ(η) - δ(ξ)` is the dimension of the local ring at `ξ`
  of `\overline{\{η\}}`, which is at most `dim 𝒪_{X, ξ} ≤ dim 𝒪_{Y, i(ξ)}`. Every point of the
  Noetherian `X` specializes from a generic point of one of its finitely many irreducible
  components, so `c ≥ m - δ` for a constant `m`. A class in `F_k K'₀(X)` therefore comes from
  supports of weight at least `m - k`, which is arbitrarily large, and the two coprime
  polynomials argument shows that an element of every `F_k` is torsion.

## Main definitions

* `Stacks.Chow.rationalCycleCoeff` — the coefficient at a point, `Z_k(X) ⊗ 𝐐 ⟶ 𝐐`.

## Main results

* `Stacks.Chow.eq_zero_of_forall_rationalCycleCoeff_eq_zero` — a rational `k`-cycle is determined
  by its coefficients.
* `Stacks.Chow.finite_setOf_mem_and_relativeDimension_eq` — a closed subset of a Noetherian scheme
  has finitely many points of maximal relative dimension.
* `Stacks.Chow.exists_forall_exists_specializes_le` — on a Noetherian space a function is bounded
  below on generizations: every point specializes from a point where it is at least `m`.
* `Stacks.Chow.coheight_le_coheight_base_of_isInducing` — an inducing morphism of schemes does not
  decrease the dimension of local rings.
* `Stacks.Chow.exists_relativeDimension_sub_eq_le_coheight` — the drop of the relative dimension
  along a specialization is at most the dimension of the local ring at the special point.
* `Stacks.Chow.exists_zsmul_eq_zero_of_pointwiseWeightOperator` — an endomorphism with pointwise
  weights `w` bounded below by `m - δ` separates the filtration by dimension of supports.
* `Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator` —
  injectivity in Stacks 0FEW, given an operator with codimension weights.

## Implementation notes

The weight condition is stated through the coefficient `Stacks.Chow.rationalCycleCoeff` at the
points `ξ ∈ Z` of relative dimension `k`, and the codimension through a natural number `n` with
`dim 𝒪_{Y, i(ξ)} = n`; every local ring of the locally Noetherian `Y` has finite dimension, so
this is no restriction.

The source decomposes `Y` into its connected components, which for a regular `Y` are its
irreducible components `Y_a`, and rescales the operator on the part supported in `Y_a` by
`2^{-δ(η_a)}`, so that it acts by `2^{-k}` on `k`-cycles. Here the weights are separated
directly: the separation argument is indifferent to which scalar each point carries, as long as
the weights grow along the filtration, and the codimension `c ≥ m - δ` does. In particular the
regularity of `Y` is used only through the map of Stacks 0FEW itself.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

universe u v

open _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open scoped _root_.TensorProduct

namespace Stacks.Chow

/-! ### The coefficient of a rational cycle at a point -/

section Coefficient

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- The coefficient at a point `x` of a rational `k`-cycle, `Z_k(X) ⊗ 𝐐 ⟶ 𝐐`, the base change of
`Stacks.Chow.cycleCoeffHom`. -/
def rationalCycleCoeff (k : ℤ) (x : X) : ℚ ⊗[ℤ] CycleGroup C f k →ₗ[ℚ] ℚ :=
  ((Int.castAddHom ℚ).comp (cycleCoeffHom C f k x)).toIntLinearMap.liftBaseChange ℚ

/-- The coefficient at `x` of `q ⊗ c` is `q` times the coefficient of `c` at `x`. -/
@[simp]
theorem rationalCycleCoeff_tmul (k : ℤ) (x : X) (q : ℚ) (c : CycleGroup C f k) :
    rationalCycleCoeff C f k x (q ⊗ₜ[ℤ] c) = q * (c.1 x : ℚ) := by
  simp [rationalCycleCoeff, LinearMap.liftBaseChange_tmul]

/-- A rational `k`-cycle has coefficient zero at the points of relative dimension other than
`k`. -/
theorem rationalCycleCoeff_eq_zero_of_relativeDimension_ne {k : ℤ} {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) (y : ℚ ⊗[ℤ] CycleGroup C f k) :
    rationalCycleCoeff C f k x y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul q c =>
    rw [rationalCycleCoeff_tmul]
    by_cases hc : c.1 x = 0
    · rw [hc, Int.cast_zero, mul_zero]
    · exact absurd ((mem_cyclesOfDimension_iff_forall_point C f k c.1).1 c.2 x hc) hx
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

/-- **A rational cycle is determined by its coefficients.** An element of `Z_k(X) ⊗ 𝐐` all of
whose coefficients vanish is zero: a nonzero integer multiple of it is `1 ⊗ c` for a cycle `c`,
whose coefficients then all vanish. -/
theorem eq_zero_of_forall_rationalCycleCoeff_eq_zero {k : ℤ} {y : ℚ ⊗[ℤ] CycleGroup C f k}
    (h : ∀ x : X, rationalCycleCoeff C f k x y = 0) : y = 0 := by
  let g := TensorProduct.mk ℤ ℚ (CycleGroup C f k) 1
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) g y
  rw [Function.uncurry_apply_pair] at h ⊢
  have hs : (s : ℤ) • IsLocalizedModule.mk' g c s = g c := IsLocalizedModule.mk'_cancel' _ _ _
  have hc : c = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
    have hx := congrArg (rationalCycleCoeff C f k x) hs
    rw [map_zsmul, h x, smul_zero] at hx
    have hx' : (1 : ℚ) * (c.1 x : ℚ) = 0 :=
      (rationalCycleCoeff_tmul C f k x 1 c).symm.trans hx.symm
    exact_mod_cast (one_mul (c.1 x : ℚ)).symm.trans hx'
  have hs' : ((s : ℤ) : ℚ) • IsLocalizedModule.mk' g c s = 0 := by
    rw [Int.cast_smul_eq_zsmul, hs, hc, map_zero]
  exact (smul_eq_zero.1 hs').resolve_left (by exact_mod_cast nonZeroDivisors.coe_ne_zero s)

variable [IsLocallyNoetherian X]

/-- The `k`-cycle of an element of `𝐐 ⊗ K₀(Coh_Z(X))` has coefficient zero away from `Z`: the
stalks of a module supported in `Z` vanish there. -/
theorem rationalCycleCoeff_supportedCoherentKZeroRatCycle_eq_zero_of_notMem {Z : Closeds X}
    {k : ℤ} (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
    (y : (supportedCoherentKZeroRat X).obj Z) {x : X} (hx : x ∉ Z) :
    rationalCycleCoeff C f k x (supportedCoherentKZeroRatCycle C f Z k hZ y) = 0 := by
  have h : (cycleCoeffHom C f k x).comp (supportedCoherentKZeroCycle C f Z k hZ) = 0 :=
    KZero.hom_ext fun A => by
      rw [AddMonoidHom.comp_apply, cycleCoeffHom_apply, AddMonoidHom.zero_apply]
      by_cases hk : relativeDimension C.dimensionFunction f x = k
      · rw [supportedCoherentKZeroCycle_mk_apply_of_eq C f Z k hZ A hk]
        exact sheafMultiplicity_eq_zero_of_notMem_supp _ fun h => hx (A.property h)
      · by_contra hne
        exact hk ((mem_cyclesOfDimension_iff_forall_point C f k _).1
          (supportedCoherentKZeroCycle C f Z k hZ (KZero.mk _ A)).2 x hne)
  induction y using TensorProduct.induction_on with
  | zero =>
    exact (congrArg (rationalCycleCoeff C f k x)
      (map_zero (supportedCoherentKZeroRatCycle C f Z k hZ))).trans (map_zero _)
  | tmul q a =>
    rw [supportedCoherentKZeroRatCycle_tmul, rationalCycleCoeff_tmul]
    have := DFunLike.congr_fun h a
    rw [AddMonoidHom.comp_apply, cycleCoeffHom_apply, AddMonoidHom.zero_apply] at this
    rw [this, Int.cast_zero, mul_zero]
  | add y z hy hz =>
    exact (congrArg (rationalCycleCoeff C f k x)
      (map_add (supportedCoherentKZeroRatCycle C f Z k hZ) y z)).trans
        ((map_add _ _ _).trans ((congrArg₂ (· + ·) hy hz).trans (add_zero 0)))

end Coefficient

/-! ### Points of maximal relative dimension, and generic points -/

section Points

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- A closed subset of a Noetherian space has finitely many points, in it, from which each of its
points is a specialization: the generic points of its irreducible components. -/
private theorem exists_finite_subset_forall_exists_specializes {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {Z : Set T} (hZ : IsClosed Z) :
    ∃ G : Set T, G.Finite ∧ G ⊆ Z ∧ ∀ ξ ∈ Z, ∃ g ∈ G, g ⤳ ξ := by
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  choose g hg using fun t : S => QuasiSober.sober (hSi t t.2) (hSc t t.2)
  have := hSf.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_, fun ξ hξ => ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hSU ▸ Set.mem_sUnion_of_mem (hg t).mem t.2
  · obtain ⟨t, ht, hξt⟩ : ξ ∈ ⋃₀ S := hSU ▸ hξ
    exact ⟨g ⟨t, ht⟩, ⟨_, rfl⟩, (hg ⟨t, ht⟩).specializes hξt⟩

/-- **A closed subset of a Noetherian scheme has finitely many points of maximal relative
dimension.** If every point of the closed `Z` has relative dimension at most `k`, a point of `Z`
of relative dimension `k` has no proper generization in `Z` (Stacks 02JW), so it is the generic
point of one of the finitely many irreducible closed subsets whose union is `Z`. -/
theorem finite_setOf_mem_and_relativeDimension_eq [NoetherianSpace X] {Z : Set X}
    (hZ : IsClosed Z) {k : ℤ} (hk : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k) :
    {ξ : X | ξ ∈ Z ∧ relativeDimension C.dimensionFunction f ξ = k}.Finite := by
  obtain ⟨G, hGf, hGZ, hG⟩ := exists_finite_subset_forall_exists_specializes hZ
  refine hGf.subset ?_
  rintro ξ ⟨hξZ, hξk⟩
  obtain ⟨g, hgG, hgξ⟩ := hG ξ hξZ
  suffices ξ = g by rwa [this]
  by_contra hne
  have hlt := relativeDimension_lt_of_mem_closure_of_ne C f
    (specializes_iff_mem_closure.mp hgξ) hne
  have := hk g (hGZ hgG)
  omega

/-- **A function on the generic points of a Noetherian space is bounded below.** For any
`d : T → ℤ` on a Noetherian quasi-sober `T₀` space there is `m` such that every point specializes
from a point at which `d` is at least `m`: the generic points of the finitely many irreducible
closed subsets covering `T`. -/
theorem exists_forall_exists_specializes_le {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    [QuasiSober T] [T0Space T] (d : T → ℤ) :
    ∃ m : ℤ, ∀ ξ : T, ∃ η : T, η ⤳ ξ ∧ m ≤ d η := by
  obtain ⟨G, hGf, -, hG⟩ := exists_finite_subset_forall_exists_specializes (isClosed_univ (X := T))
  obtain ⟨m, hm⟩ := (hGf.image d).bddBelow
  refine ⟨m, fun ξ => ?_⟩
  obtain ⟨g, hgG, hgξ⟩ := hG ξ (Set.mem_univ ξ)
  exact ⟨g, hgξ, hm ⟨g, hgG, rfl⟩⟩

/-- A morphism of schemes whose underlying map is inducing does not decrease the coheight of a
point for the specialization order, that is, the dimension of its local ring (Stacks 02IZ). -/
theorem coheight_le_coheight_base_of_isInducing {X' Y' : Scheme.{u}} (g : X' ⟶ Y')
    (hg : Topology.IsInducing g.base) (x : X') :
    Order.coheight x ≤ Order.coheight (g.base x) :=
  Order.coheight_le_coheight_apply_of_strictMono _ (fun a b hab => by
    rw [lt_iff_le_not_ge] at hab ⊢
    exact ⟨Specializes.map (show b ⤳ a from hab.1) g.base.hom.continuous,
      fun h => hab.2 (show a ⤳ b from hg.specializes_iff.1 h)⟩) x

/-- **The drop of the relative dimension along a specialization is at most a codimension.** For
`x ⤳ y` the drop `δ(x) - δ(y)` is a natural number `n`, the dimension of the local ring at `y` of
`\overline{\{x\}}` (`Stacks.Chow.relativeDimension_drop_of_specialization`), hence at most the
dimension `coheight y` of the local ring of `X` at `y`. -/
theorem exists_relativeDimension_sub_eq_le_coheight {x y : X} (hxy : x ⤳ y) :
    ∃ n : ℕ, relativeDimension C.dimensionFunction f x -
      relativeDimension C.dimensionFunction f y = n ∧ (n : ℕ∞) ≤ Order.coheight y := by
  obtain ⟨n, hn, hdim⟩ := relativeDimension_drop_of_specialization C.isUniversallyCatenary
    C.dimensionFunction f hxy
  refine ⟨n, hn, ?_⟩
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  rw [← WithBot.coe_inj.1 ((ringKrullDim_stalk_eq_coheight _).symm.trans hdim)]
  exact (coheight_le_coheight_base_of_isInducing I.subschemeι
    I.subschemeι.isClosedEmbedding.isInducing _).trans_eq rfl

end Points

/-! ### Separation of the filtration, given pointwise weights -/

section Separation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [AlgebraicGeometry.IsNoetherian X]

/-- **One step of the separation, given pointwise weights.** Let `ψ` be a natural endomorphism
of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` which, whenever every point of `Z` has relative dimension at most `k`,
multiplies the coefficient at each point `ξ ∈ Z` of relative dimension `k` of the `k`-cycle by
`ℓ^{w(ξ)}`. Then on every nonempty closed `Z` each `x` is killed, modulo the image of a closed
`Z' ⊊ Z`, by a product of factors `ψ - ℓ^n` over weights `n` of points of `Z`: take the factors
`ψ - ℓ^{w(ξ)}` over the finitely many points `ξ` of `Z` of maximal relative dimension `k`, which
kill the `k`-cycle, and `Z'` with relative dimension at most `k - 1`. -/
theorem exists_multiset_lt_aeval_mem_range_of_pointwiseWeightOperator {ℓ : ℚ} (w : X → ℤ)
    (ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X)
    (hψ : ∀ (Z : Closeds X) (k : ℤ)
      (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
      (x : (supportedCoherentKZeroRat X).obj Z) (ξ : X), ξ ∈ Z →
        relativeDimension C.dimensionFunction f ξ = k →
        rationalCycleCoeff C f k ξ (supportedCoherentKZeroRatCycle C f Z k hZ ((ψ.app Z).hom x)) =
          ℓ ^ w ξ * rationalCycleCoeff C f k ξ (supportedCoherentKZeroRatCycle C f Z k hZ x))
    (Z : Closeds X) (x : (supportedCoherentKZeroRat X).obj Z) (hZ : Z ≠ ⊥) :
    ∃ s : Multiset ℤ, (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧ ∃ (Z' : Closeds X) (h : Z' < Z),
      Polynomial.aeval (ψ.app Z).hom
          (s.map fun n => Polynomial.X - Polynomial.C (ℓ ^ n)).prod x ∈
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE h.le)).hom := by
  obtain ⟨z₁, hz₁⟩ : (Z : Set X).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun h => hZ (Closeds.ext h)
  obtain ⟨hi, hhi⟩ := exists_relativeDimension_le C f
  obtain ⟨k, ⟨z₀, hz₀, rfl⟩, hk⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => ∃ z ∈ Z, relativeDimension C.dimensionFunction f z = k)
    ⟨hi, fun _ ⟨z, _, hz⟩ => hz ▸ hhi z⟩ ⟨_, z₁, hz₁, rfl⟩
  set k := relativeDimension C.dimensionFunction f z₀
  have hZk : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k :=
    fun z hz => hk _ ⟨z, hz, rfl⟩
  have hfin := finite_setOf_mem_and_relativeDimension_eq C f Z.isClosed hZk
  refine ⟨hfin.toFinset.val.map w, fun n hn => ?_, ?_⟩
  · obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hn
    exact ⟨ξ, ((Set.Finite.mem_toFinset hfin).1 hξ).1, rfl⟩
  set p := ((hfin.toFinset.val.map w).map
    fun n => Polynomial.X - Polynomial.C (ℓ ^ n)).prod with hp
  have hcyc : supportedCoherentKZeroRatCycle C f Z k hZk
      (Polynomial.aeval (ψ.app Z).hom p x) = 0 := by
    refine eq_zero_of_forall_rationalCycleCoeff_eq_zero C f fun ξ => ?_
    by_cases hξZ : ξ ∈ Z
    swap
    · exact rationalCycleCoeff_supportedCoherentKZeroRatCycle_eq_zero_of_notMem C f hZk _ hξZ
    by_cases hξk : relativeDimension C.dimensionFunction f ξ = k
    swap
    · exact rationalCycleCoeff_eq_zero_of_relativeDimension_ne C f hξk _
    let L := (rationalCycleCoeff C f k ξ).comp (supportedCoherentKZeroRatCycle C f Z k hZk)
    have hL : ∀ v, L ((ψ.app Z).hom v) = (algebraMap ℚ (Module.End ℚ ℚ) (ℓ ^ w ξ)) (L v) :=
      fun v => by
        rw [Module.algebraMap_end_apply, smul_eq_mul]
        exact hψ Z k hZk v ξ hξZ hξk
    change L (Polynomial.aeval (ψ.app Z).hom p x) = 0
    rw [LinearMap.apply_aeval_of_apply_eq hL p x,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply]
    have hev : Polynomial.eval (ℓ ^ w ξ) p = 0 := by
      rw [hp, Polynomial.eval_multiset_prod]
      exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨Polynomial.X - Polynomial.C (ℓ ^ w ξ),
        Multiset.mem_map.2 ⟨w ξ, Multiset.mem_map.2 ⟨ξ,
          (Set.Finite.mem_toFinset hfin).2 ⟨hξZ, hξk⟩, rfl⟩, rfl⟩, by simp⟩)
    rw [hev, zero_smul]
  obtain ⟨Z', h, hZ', hmem⟩ := exists_mem_range_of_supportedCoherentKZeroRatCycle_eq_zero C f Z
    k hZk _ hcyc
  refine ⟨Z', h.lt_of_ne fun he => ?_, hmem⟩
  have := hZ' z₀ (he ▸ hz₀)
  omega

/-- **Separation of the filtration by dimension of supports, given pointwise weights.** Let
`ℓ > 1`, let `w : X → ℤ` be a weight with `w ≥ m - δ` for a constant `m`, and let `ψ` be a
natural endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` which, whenever every point of `Z` has relative
dimension at most `k`, multiplies the coefficient at each point `ξ ∈ Z` of relative dimension `k`
of the `k`-cycle by `ℓ^{w(ξ)}`. Then an element of `K'₀(X)` with a nonzero multiple in every
`F_k K'₀(X)` is torsion: a class from supports on which `δ ≤ k` comes from supports of weight at
least `m - k`, and `Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup_of_exists_multiset`
applies. -/
theorem exists_zsmul_eq_zero_of_pointwiseWeightOperator {ℓ : ℚ} (hℓ : 1 < ℓ) (w : X → ℤ)
    (hw : ∃ m : ℤ, ∀ ξ : X, m - relativeDimension C.dimensionFunction f ξ ≤ w ξ)
    (ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X)
    (hψ : ∀ (Z : Closeds X) (k : ℤ)
      (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ k)
      (x : (supportedCoherentKZeroRat X).obj Z) (ξ : X), ξ ∈ Z →
        relativeDimension C.dimensionFunction f ξ = k →
        rationalCycleCoeff C f k ξ (supportedCoherentKZeroRatCycle C f Z k hZ ((ψ.app Z).hom x)) =
          ℓ ^ w ξ * rationalCycleCoeff C f k ξ (supportedCoherentKZeroRatCycle C f Z k hZ x))
    (b : CoherentKZero X)
    (hb : ∀ k : ℤ, ∃ m : ℤ, m ≠ 0 ∧ m • b ∈ coherentKZeroFiltration C f k) :
    ∃ m : ℤ, m ≠ 0 ∧ m • b = 0 := by
  obtain ⟨m₀, hm₀⟩ := hw
  have hx : ∀ c : ℤ, coherentKZeroToSupportedCoherentKZeroRatTop b ∈
      ⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, c ≤ w z),
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom := by
    intro c
    obtain ⟨m, hm, hmb⟩ := hb (m₀ - c)
    have hle : (⨆ (Z : Closeds X)
        (_ : ∀ z ∈ Z, relativeDimension C.dimensionFunction f z ≤ m₀ - c),
        LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom) ≤
        ⨆ (Z : Closeds X) (_ : ∀ z ∈ Z, c ≤ w z),
          LinearMap.range ((supportedCoherentKZeroRat X).map (homOfLE (le_top : Z ≤ ⊤))).hom :=
      iSup₂_mono' fun Z hZ => ⟨Z, fun z hz => by linarith [hZ z hz, hm₀ z], le_rfl⟩
    have h2 := hle (coherentKZeroToSupportedCoherentKZeroRatTop_mem_iSup C f (m₀ - c) hmb)
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at h2
    have h3 := Submodule.smul_mem _ (m : ℚ)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm), one_smul] at h3
  have hx0 : coherentKZeroToSupportedCoherentKZeroRatTop b = 0 :=
    WeightSeparation.eq_zero_of_forall_mem_iSup_of_exists_multiset ψ (w := w)
      (μ := fun n : ℤ => ℓ ^ n) (zpow_right_strictMono₀ hℓ).injective
      subsingleton_supportedCoherentKZeroRat_bot
      (exists_multiset_lt_aeval_mem_range_of_pointwiseWeightOperator C f w ψ hψ) _ hx
  refine exists_zsmul_eq_zero_of_one_tmul_eq_zero ?_
  rw [← supportedCoherentKZeroRatToCoherent_coherentKZeroToSupportedCoherentKZeroRatTop, hx0,
    map_zero]

end Separation

/-! ### Injectivity in Stacks 0FEW, given an operator with codimension weights -/

section Composite

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (a : Y ⟶ C.S) [LocallyOfFiniteType a]
  (i : X ⟶ Y) [IsClosedImmersion i] (hY : IsRegular Y) [CompactSpace Y]

/-- **Injectivity in Stacks 0FEW, given an operator with codimension weights.** Let
`i : X ⟶ Y` be a closed immersion with `Y` regular and quasi-compact, and let `ℓ > 1`. Suppose
`ψ` is a natural endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` such that, whenever every point of `Z`
has `δ ≤ k`, at every point `ξ ∈ Z` with `δ(ξ) = k` the coefficient of the `k`-cycle of `ψ x` is
`ℓ^n` times that of `x`, where `n = dim 𝒪_{Y, i(ξ)}`. Then
`K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `[ℱ] ↦ ch(X ⟶ Y, ℱ[0]) ∩ [Y]`, is injective.

The codimension `c(ξ) = dim 𝒪_{Y, i(ξ)}` is at least the drop `δ(η) - δ(ξ)` along any
generization `η` of `ξ` (`Stacks.Chow.exists_relativeDimension_sub_eq_le_coheight`), and the
relative dimension of the generic points of `X` is bounded below, so `c ≥ m - δ`; the filtration
by dimension of supports is then separated
(`Stacks.Chow.exists_zsmul_eq_zero_of_pointwiseWeightOperator`), which is all of injectivity
(`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_separated`). -/
theorem injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator
    {ℓ : ℚ} (hℓ : 1 < ℓ) :
    haveI := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
    ∀ ψ : supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X,
      (∀ (Z : Closeds X) (k : ℤ)
          (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k)
          (x : (supportedCoherentKZeroRat X).obj Z) (ξ : X), ξ ∈ Z →
          relativeDimension C.dimensionFunction (i ≫ a) ξ = k → ∀ n : ℕ,
          ringKrullDim (Y.presheaf.stalk (i.base ξ)) = (n : ℕ∞) →
          rationalCycleCoeff C (i ≫ a) k ξ
              (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ ((ψ.app Z).hom x)) =
            ℓ ^ n * rationalCycleCoeff C (i ≫ a) k ξ
              (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ x)) →
        Function.Injective ((coherentChowCharacter C a i hY).toIntLinearMap.liftBaseChange ℚ) := by
  have := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian a
  intro ψ hψ
  -- the codimension of `i(ξ)` in `Y` is finite
  have hfin : ∀ ξ : X, Order.coheight (i.base ξ) ≠ ⊤ := fun ξ h => by
    have := ringKrullDim_ne_top (R := Y.presheaf.stalk (i.base ξ))
    rw [ringKrullDim_stalk_eq_coheight, h] at this
    exact this rfl
  let w : X → ℤ := fun ξ => ((Order.coheight (i.base ξ)).toNat : ℤ)
  have hdim : ∀ ξ : X, ringKrullDim (Y.presheaf.stalk (i.base ξ)) =
      (((Order.coheight (i.base ξ)).toNat : ℕ) : ℕ∞) := fun ξ => by
    rw [ringKrullDim_stalk_eq_coheight, ENat.natCast_toNat (hfin ξ)]
  have hψ' : ∀ (Z : Closeds X) (k : ℤ)
      (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k)
      (x : (supportedCoherentKZeroRat X).obj Z) (ξ : X), ξ ∈ Z →
        relativeDimension C.dimensionFunction (i ≫ a) ξ = k →
        rationalCycleCoeff C (i ≫ a) k ξ
            (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ ((ψ.app Z).hom x)) =
          ℓ ^ w ξ * rationalCycleCoeff C (i ≫ a) k ξ
            (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ x) :=
    fun Z k hZ x ξ hξZ hξk => by
      rw [hψ Z k hZ x ξ hξZ hξk _ (hdim ξ), zpow_natCast]
  have hw : ∃ m : ℤ, ∀ ξ : X, m - relativeDimension C.dimensionFunction (i ≫ a) ξ ≤ w ξ := by
    obtain ⟨m, hm⟩ := exists_forall_exists_specializes_le
      (relativeDimension C.dimensionFunction (i ≫ a))
    refine ⟨m, fun ξ => ?_⟩
    obtain ⟨η, hηξ, hmη⟩ := hm ξ
    obtain ⟨n, hn, hle⟩ := exists_relativeDimension_sub_eq_le_coheight C (i ≫ a) hηξ
    have h2 : n ≤ (Order.coheight (i.base ξ)).toNat := by
      rw [← ENat.natCast_le_natCast, ENat.natCast_toNat (hfin ξ)]
      exact hle.trans
        (coheight_le_coheight_base_of_isInducing i i.isClosedEmbedding.isInducing ξ)
    have h3 : (n : ℤ) ≤ w ξ := Nat.cast_le.2 h2
    omega
  exact injective_liftBaseChange_coherentChowCharacter_of_separated C a i hY
    (exists_zsmul_eq_zero_of_pointwiseWeightOperator C (i ≫ a) hℓ w hw ψ hψ')

end Composite

end Stacks.Chow

end
