module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.ReductionToIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.ClosedPointCase

/-!
# Stacks 0FC5: the inverse map acts by exterior product

Every bivariant class over a Dedekind base caps as the exterior product with its image
`c ∩ [S]₁`, and the inverse map of Stacks 0FC5.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Stacks 0FC5: the bivariant class attached to a Chow class acts by exterior product -/

section Main

variable {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-- The class of the pushforward to `X` of a cycle representing `c ∩ [S]₁` on `X ×_S S`, and any
other cycle with the same class, have the same exterior products with every cycle. -/
theorem mk_exteriorProductDedekindCycles_eq_of_mk_eq (hS : IsDedekindChowBase C) {U : Scheme.{u}}
    (u : U ⟶ C.S) [LocallyOfFiniteType u] (n k : ℤ) {a a' : CycleGroup C sX n}
    (haa' : QuotientAddGroup.mk' (rationalEquivalences C sX n) a =
      QuotientAddGroup.mk' (rationalEquivalences C sX n) a') (b : CycleGroup C u k) :
    QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX u ≫ sX) (n + k - 1))
        (exteriorProductDedekindCycles C sX u n k a b) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX u ≫ sX) (n + k - 1))
        (exteriorProductDedekindCycles C sX u n k a' b) := by
  have hfac := hS.exteriorProductFactorsThroughRationalEquivalence sX u n k
  rw [← exteriorProductDedekindChow_mk_mk C sX u _ _ hfac,
    ← exteriorProductDedekindChow_mk_mk C sX u _ _ hfac, haa']

/-- **Capping the fundamental class of an integral scheme over a closed point of the base.**
Let `c ∈ A^p(X → S)` with `c ∩ [S]₁` the class of the cycle `a`, and let `T` be integral over the
base with generic point over a point which is not a generic point of the base. Then
`c ∩ [T] = a × [T]`: the image of `T` is a closed point `s`, and
`Stacks.Chow.cap_fundamentalCycle_heq_of_zeroScheme` applies to the factorization of `T ⟶ S`
through the reduced point `s` of an integral neighbourhood on which `s` is a principal divisor. -/
theorem cap_fundamentalCycle_heq_of_notMem_genericPoints (hS : IsDedekindChowBase C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (a : CycleGroup C sX (1 - p))
    (ha : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a)
    {T : Scheme.{u}} [IsIntegral T] (t : T ⟶ C.S) [LocallyOfFiniteType t]
    (hgen : t.base (genericPoint T) ∉ genericPoints C.S) (k : ℤ) :
    c.cap t k (chowGroupCongr C (Category.comp_id t).symm k
        (QuotientAddGroup.mk' (rationalEquivalences C t k) (fundamentalCycle C t k))) ≍
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX t ≫ sX) (1 - p + k - 1))
        (exteriorProductDedekindCycles C sX t (1 - p) k a (fundamentalCycle C t k)) := by
  obtain ⟨V, hsV, L, hL, σ, hVint, hσ, htriv, h, _, _, r, hr, hht, hrel⟩ :=
    hS.exists_lift_zeroScheme_of_notMem_genericPoints t hgen
  by_cases hk : k = r
  swap
  · rw [fundamentalCycle_eq_zero_of_ne C t genericPoints_eq_singleton
      (by rw [hrel]; exact Ne.symm hk),
      map_zero, map_zero, map_zero, map_zero, map_zero]
    exact heq_zero_chowGroup_of_degree_eq C _ (by ring)
  subst hk
  subst hht
  obtain ⟨κ, hκ⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C
    (pullback.fst sX (𝟙 C.S) ≫ sX) (1 - p)) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C))
  have hαa : QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p))
      (properPushforward C _ sX (pullback.fst sX (𝟙 C.S)) rfl (1 - p) κ) =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a := by
    rw [← ha, bivariantCapBaseFundamentalClass_apply,
      basePullbackPushforward_eq_chowPushforwardOfIso,
      ← hκ, chowPushforwardOfIso_mk]
  exact (cap_fundamentalCycle_heq_of_zeroScheme sX hS p c κ hκ.symm hgen V hsV L σ hσ htriv h r
    hr hrel).trans (heq_of_eq (mk_exteriorProductDedekindCycles_eq_of_mk_eq sX hS _ _ _ hαa _))

/-- **Stacks 0FC5, the inverse map acts by exterior product**, corrected form. Over a base as in
section 42.63 with no zero-dimensional component, every bivariant class `c ∈ A^p(X → S)` caps as
the exterior product of Stacks 0FC4 with its image `α = c ∩ [S]₁ ∈ CH_{1-p}(X)`:

  `c ∩ α' = α × α'`

for every scheme `U` locally of finite type over the base and every `α' ∈ CH_k(U)`.

By Stacks 02UC it suffices to check this on fundamental classes of integral schemes `T`
(`Stacks.Chow.cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral`). If `T` dominates a
component of the base, `[T]` is a flat pullback of `[S]₁`; otherwise `T` lies over a closed point
`s` and `[T]` is a flat pullback of the Gysin image of the restriction of `[S]₁` to a neighbourhood
of `s`. Since `c` commutes with flat pullback and Gysin maps, in both cases `c ∩ [T]` is computed
from `c ∩ [S]₁`, and on cycles the outcome is the defining rule of the exterior product. This is
the final paragraph of the proof of Stacks 0FC5, read for `c` and `c_α`. -/
theorem isExteriorProductOverBase_bivariantCapBaseFundamentalClass (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - p) p
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c) c := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX (1 - p))
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c)
  intro U u _ k hfac α'
  induction α' using QuotientAddGroup.induction_on with
  | H b =>
  rw [← ha]
  refine cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral C _ sX (1 - p) p c a rfl
    (fun t _ _ l ↦ ?_) u k b
  by_cases hgen : t.base (genericPoint _) ∈ genericPoints C.S
  · exact cap_fundamentalCycle_heq_of_mem_genericPoints _ sX p hS hS1 c a ha.symm t hgen l
  · exact cap_fundamentalCycle_heq_of_notMem_genericPoints sX p hS c a ha.symm t hgen l

/-- **Stacks 0FC5, the inverse map**, corrected form. Over a base as in section 42.63 with no
zero-dimensional component, every `α ∈ CH_{1-p}(X)` is `c_α ∩ [S]₁` for a bivariant class
`c_α ∈ A^p(X → S)` acting by exterior product with `α`, `c_α ∩ α' = α × α'`; by
`Stacks.Chow.bivariantCapBaseFundamentalClass_injective` it is unique. -/
@[stacks 0FC5 "corrected form: the inverse α ↦ c_α acts by exterior product, c_α ∩ α' = α × α'"]
theorem exists_isExteriorProductOverBase (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) (α : chowGroup C sX (1 - p)) :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p,
      IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - p) p α c ∧
        bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c = α := by
  obtain ⟨c, hc⟩ := bivariantCapBaseFundamentalClass_surjective C sX p hS hS1 α
  exact ⟨c, hc ▸ isExteriorProductOverBase_bivariantCapBaseFundamentalClass sX p hS hS1 c, hc⟩

end Main

end Stacks.Chow

end
