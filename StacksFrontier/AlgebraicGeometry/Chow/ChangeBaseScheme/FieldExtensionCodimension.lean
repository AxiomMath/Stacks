module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionGysinRational
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Base change of the Chow groups of codimension `i` along a field extension

Let `k'/k` be an extension of fields and `X` smooth over `k`, with base change
`X' = X ×_k k'`. The part `X'_d` of `X'` of dimension `d` contains the inverse image of the part
`X_d` of `X` (base change preserves the relative dimension). The base change of Chow groups of
[Stacks, Tag 0FVJ] therefore induces

  `g^* : CH^i(X) = ∏_d CH_{d-i}(X_d) ⟶ CH^i(X') = ∏_d CH_{d-i}(X'_d)`

(`Stacks.Chow.codimensionChowBaseChange`): a class on `X_d` is pushed into `X`, base changed and
restricted to `X'_d`. It is compatible with the map `CH^i(-) ⟶ CH_*(-) ⊗ 𝐐` and with the
base change of `CH_*(-) ⊗ 𝐐`; with the compatibility of base change with the Chern character
(`Stacks.Chow.rationalBaseChangeChowPullback_rationalChernCharacterCap`) and with fundamental
classes, this gives the identity of [Stacks, Tag 0FVT] on `CH^*(X) ⊗ 𝐐 ≅ K_0(Vect(X)) ⊗ 𝐐`:
the class `α'` with `ch(α') ∩ [X] = α` base changes to the class of `g^*α`
(`Stacks.Chow.symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange`).

## Main definitions

* `Stacks.Chow.codimensionChowBaseChange` — `g^* : CH^i(X) ⟶ CH^i(X')`.

## Main results

* `Stacks.Chow.mem_dimPart_pullbackSnd` — `X'_d ⊇ (X' ⟶ X)⁻¹(X_d)`.
* `Stacks.Chow.codimensionToRationalChow_codimensionChowBaseChange` — compatibility with
  `CH^i(-) ⟶ CH_*(-) ⊗ 𝐐`.
* `Stacks.Chow.symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange` — compatibility
  with `CH^*(-) ⊗ 𝐐 ≅ K_0(Vect(-)) ⊗ 𝐐`.

## References

* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart)

universe u

namespace Stacks.Chow

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

local notation "𝔅" => fieldExtensionBaseChangeSituation k k'

/-! ### Parts of the base change -/

/-- **A point in the image of an open immersion along which `X` has relative dimension `d` lies in
the part of dimension `d`.** -/
theorem mem_dimPart_of_relativeDimension {S W Y : Scheme.{u}} (sY : Y ⟶ S) [Smooth sY]
    (j : W ⟶ Y) [IsOpenImmersion j] {d : ℕ} (h : RelativeDimension (j ≫ sY) d) {y : Y}
    (hy : y ∈ j.opensRange) : y ∈ dimPart sY d := by
  have hU : RelativeDimension (j.opensRange.ι ≫ sY) d := by
    have sq : IsPullback j.isoOpensRange.inv (j.opensRange.ι ≫ sY) (j ≫ sY) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.comp_id, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]⟩
    exact RelativeDimension.of_isPullback sq h
  change y ∈ relativeDimensionOpen _ _ d
  rw [mem_relativeDimensionOpen]
  have h1 := topologicalKrullDimAt_fiber_eq_of_relativeDimension sY j.opensRange d hU y hy
  have h2 := relativeDimensionFunction_apply sY (fun s ↦ isCohenMacaulay_fiber_of_smooth sY s) y
  exact_mod_cast h2.symm.trans h1

/-- **A scheme of relative dimension `n` has empty parts in all other dimensions.** -/
theorem isEmpty_dimPart_of_relativeDimension {S Y : Scheme.{u}} (sY : Y ⟶ S) [Smooth sY]
    {n : ℕ} (h : RelativeDimension sY n) {m : ℕ} (hm : m ≠ n) :
    IsEmpty (dimPart sY m).toScheme := by
  refine ⟨fun y => ?_⟩
  have h1 : y.1 ∈ dimPart sY n :=
    mem_dimPart_of_relativeDimension sY (𝟙 Y) (by simpa only [Category.id_comp] using h)
      (by rw [Scheme.Hom.opensRange_of_isIso]; trivial)
  exact (TopologicalSpace.Opens.coe_disjoint.2
    ((isClopenDecomposition_dimPart sY).disjoint m n hm)).le_bot ⟨y.2, h1⟩

/-- **The part of `X'` of dimension `d` contains the inverse image of the part of `X` of
dimension `d`.** -/
theorem mem_dimPart_pullbackSnd {d : ℕ} (x : (pullback sX (𝔅).g : Scheme.{u}))
    (hx : (pullback.fst sX (𝔅).g).base x ∈ dimPart sX d) :
    x ∈ dimPart (pullback.snd sX (𝔅).g) d := by
  have hrange := opensRange_baseChangeMorphism (𝔅) sX (dimPart sX d).ι
  rw [Scheme.Opens.opensRange_ι] at hrange
  have hxm : x ∈ (baseChangeMorphism (𝔅) sX (dimPart sX d).ι).opensRange := by
    rw [hrange]
    exact hx
  have hrel : RelativeDimension
      (baseChangeMorphism (𝔅) sX (dimPart sX d).ι ≫ pullback.snd sX (𝔅).g) d := by
    convert relativeDimension_pullbackSnd _ (relativeDimension_partBase sX d) (𝔅).g using 1
    exact baseChangeMorphism_comp_snd _ _ _
  exact mem_dimPart_of_relativeDimension _ _ hrel hxm

/-! ### Base change of codimension-graded Chow groups -/

/-- Base change of `CH_n` along `k'/k`, in the same degree `n` (the dimension shift of a field
extension is zero). -/
def fieldBaseChangeChow (n : ℤ) :
    chowGroup (fieldChowSituation k) sX n →+
      chowGroup (fieldChowSituation k') (pullback.snd sX (𝔅).g) n :=
  (chowGroupCast (fieldChowSituation k') (pullback.snd sX (𝔅).g) (add_zero n)).toAddMonoidHom.comp
    (baseChangeChowPullback (𝔅) sX n)

/-- `fieldBaseChangeChow` agrees, up to the cast `n + 0 = n`, with the base change
`baseChangeChowPullback`. -/
theorem fieldBaseChangeChow_heq (n : ℤ) (α : chowGroup (fieldChowSituation k) sX n) :
    fieldBaseChangeChow k k' sX n α ≍ baseChangeChowPullback (𝔅) sX n α :=
  chowGroupCast_heq _ _ (add_zero n) _

/-- **Base change `CH^i(X) ⟶ CH^i(X')` of the Chow groups of codimension `i`** along `k'/k`, for
`X` smooth over `k`: the component on the part `X'_d` of a class `(a_d)_d` is the restriction to
`X'_d` of the base change of the pushforward of `a_d` to `X`. -/
def codimensionChowBaseChange (i : ℤ) :
    codimensionChowGroup k sX i →+ codimensionChowGroup k' (pullback.snd sX (𝔅).g) i :=
  AddMonoidHom.pi fun d =>
    (chowGroupRestrict (fieldChowSituation k') (pullback.snd sX (𝔅).g)
        (partBase (pullback.snd sX (𝔅).g) d) (dimPart (pullback.snd sX (𝔅).g) d).ι rfl
        ((d : ℤ) - i)).comp
      ((fieldBaseChangeChow k k' sX ((d : ℤ) - i)).comp
        ((partPushforward sX d ((d : ℤ) - i)).comp
          (Pi.evalAddMonoidHom
            (fun d : ℕ => chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i)) d)))

/-- The component of `codimensionChowBaseChange` on the part `X'_d` is the restriction to `X'_d`
of the base change of the pushforward of the component on `X_d`. -/
theorem codimensionChowBaseChange_apply (i : ℤ) (a : codimensionChowGroup k sX i) (d : ℕ) :
    codimensionChowBaseChange k k' sX i a d =
      chowGroupRestrict (fieldChowSituation k') (pullback.snd sX (𝔅).g)
        (partBase (pullback.snd sX (𝔅).g) d) (dimPart (pullback.snd sX (𝔅).g) d).ι rfl
        ((d : ℤ) - i) (fieldBaseChangeChow k k' sX ((d : ℤ) - i)
          (partPushforward sX d ((d : ℤ) - i) (a d))) :=
  rfl

/-- The base change of a class pushed forward from the part `X_d` restricts to zero on every
other part `X'_e` of `X'`. -/
theorem chowGroupRestrict_baseChangeChowPullback_partPushforward_of_ne {d e : ℕ} (hde : d ≠ e)
    (m : ℤ) (x : chowGroup (fieldChowSituation k) (partBase sX d) m) :
    chowGroupRestrict (fieldChowSituation k') (pullback.snd sX (𝔅).g)
        (partBase (pullback.snd sX (𝔅).g) e) (dimPart (pullback.snd sX (𝔅).g) e).ι rfl (m + (𝔅).c)
        (baseChangeChowPullback (𝔅) sX m (partPushforward sX d m x)) = 0 := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [properChowPushforward_mk, baseChangeChowPullback_mk, chowGroupRestrict_mk]
  refine (congrArg (QuotientAddGroup.mk' _) ?_).trans (map_zero _)
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  rw [cycleGroupRestrict_apply, baseChangeCyclePullback_apply,
    properPushforward_apply_eq_zero_of_notMem_range, zero_mul]
  · rfl
  · rintro ⟨z, hz⟩
    have h1 : (dimPart (pullback.snd sX (𝔅).g) e).ι.base y ∈ dimPart (pullback.snd sX (𝔅).g) d :=
      mem_dimPart_pullbackSnd k k' sX _ (by rw [← hz]; exact z.2)
    have h2 : (dimPart (pullback.snd sX (𝔅).g) e).ι.base y ∈ dimPart (pullback.snd sX (𝔅).g) e :=
      y.2
    exact (TopologicalSpace.Opens.coe_disjoint.2
      ((isClopenDecomposition_dimPart (pullback.snd sX (𝔅).g)).disjoint d e hde)).le_bot ⟨h1, h2⟩

/-- If `X` is quasi-compact, then so is its base change `X ×_k k'`. -/
instance compactSpace_pullback_fieldExtension [CompactSpace X] :
    CompactSpace (pullback sX (𝔅).g : Scheme.{u}) := by
  have : QuasiCompact sX := (quasiCompact_iff_compactSpace sX).mpr inferInstance
  exact (quasiCompact_iff_compactSpace (pullback.snd sX (𝔅).g)).mp inferInstance

/-- **Base change of `CH^i` is compatible with `CH^i(-) ⟶ CH_*(-) ⊗ 𝐐`**: the class of
`g^*a ∈ CH^i(X')` in `CH_*(X') ⊗ 𝐐` is the base change of the class of `a ∈ CH^i(X)`. -/
theorem codimensionToRationalChow_codimensionChowBaseChange [CompactSpace X] (i : ℤ)
    (a : codimensionChowGroup k sX i) :
    codimensionToRationalChow k' (pullback.snd sX (𝔅).g) i (codimensionChowBaseChange k k' sX i a) =
      rationalBaseChangeChowPullback (𝔅) sX (codimensionToRationalChow k sX i a) := by
  classical
  set sX' := pullback.snd sX (𝔅).g
  rw [← sum_rationalIncludePart_rationalRestrictPart k' sX'
      (codimensionToRationalChow k' sX' i (codimensionChowBaseChange k k' sX i a)),
    ← sum_rationalIncludePart_rationalRestrictPart k' sX'
      (rationalBaseChangeChowPullback (𝔅) sX (codimensionToRationalChow k sX i a))]
  refine Finset.sum_congr rfl fun e he => congrArg _ ?_
  rw [rationalRestrictPart_codimensionToRationalChow k' sX' i _ he,
    codimensionToRationalChow_apply, map_sum, map_sum]
  have hterm : ∀ d ∈ nonemptyDimParts k sX,
      rationalRestrictPart k' sX' e (rationalBaseChangeChowPullback (𝔅) sX
        (rationalIncludePart k sX d
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase sX d) j)
            ((d : ℤ) - i) ((1 : ℚ) ⊗ₜ[ℤ] a d)))) =
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k') (partBase sX' e) j)
          ((d : ℤ) - i + (𝔅).c) ((1 : ℚ) ⊗ₜ[ℤ] chowGroupRestrict (fieldChowSituation k') sX'
            (partBase sX' e) (dimPart sX' e).ι rfl ((d : ℤ) - i + (𝔅).c)
            (baseChangeChowPullback (𝔅) sX ((d : ℤ) - i) (partPushforward sX d ((d : ℤ) - i)
              (a d)))) := fun d _ => by
    have := (isClopenDecomposition_dimPart sX).isProper_ι d
    rw [rationalProperChowPushforward_of_tmul, rationalBaseChangeChowPullback_of_tmul,
      rationalChowMap_of_tmul]
  rw [Finset.sum_congr rfl hterm]
  by_cases hX : e ∈ nonemptyDimParts k sX
  · rw [Finset.sum_eq_single_of_mem e hX fun d _ hde => by
      rw [chowGroupRestrict_baseChangeChowPullback_partPushforward_of_ne k k' sX hde
        ((d : ℤ) - i) (a d), TensorProduct.tmul_zero, map_zero]]
    refine (of_tmul_eq_of_tmul_of_heq _ _ (by simp) _ ?_).symm
    rw [codimensionChowBaseChange_apply]
    exact chowGroupRestrict_heq_of_eq (fieldChowSituation k') _ _ rfl rfl rfl rfl rfl (by simp) _ _
      (fieldBaseChangeChow_heq k k' sX _ _).symm
  · exfalso
    obtain ⟨y, hy⟩ := (mem_nonemptyDimParts k' sX').1 he
    obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart sX).exists_mem
      ((pullback.fst sX (𝔅).g).base y)
    have h1 := mem_dimPart_pullbackSnd k k' sX y hd
    have hde : d = e := by
      by_contra h
      exact (TopologicalSpace.Opens.coe_disjoint.2
        ((isClopenDecomposition_dimPart sX').disjoint d e h)).le_bot ⟨h1, hy⟩
    subst hde
    exact hX ((mem_nonemptyDimParts k sX).2 ⟨_, hd⟩)

/-! ### The identity of Stacks 0FVT on `CH^*(X) ⊗ 𝐐 ≅ K_0(Vect(X)) ⊗ 𝐐` -/

variable [IsNoetherian X] [IsSeparated sX]

/-- For `X` separated over `k`, the diagonal of the base change `X ×_k k'` is affine. -/
instance isAffineHom_diagonal_pullback_fieldExtension :
    IsAffineHom (pullback.diagonal (terminal.from (pullback sX (𝔅).g : Scheme.{u}))) :=
  isAffineHom_diagonal_of_isSeparated_fieldChowSituation k' (pullback.snd sX (𝔅).g)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **The class in `K_0(Vect(X')) ⊗ 𝐐` of the base change of a class of codimension `i`.** For
`a ∈ CH^i(X)` with class `α ∈ CH^*(X) ⊗ 𝐐 ≅ K_0(Vect(X)) ⊗ 𝐐`, `α = ch(α') ∩ [X]`, the class of
`g^*a ∈ CH^i(X')` corresponds to the pullback of `α'` to `X'`. -/
theorem symm_rationalChernCharacterAlgEquiv_codimensionChowBaseChange (i : ℤ)
    (a : codimensionChowGroup k sX i) :
    (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field (pullback.snd sX (𝔅).g))
        (exists_bounds_relativeDimension_fieldChowSituation k' (pullback.snd sX (𝔅).g))).symm
      (smoothChowEquiv (pullback.snd sX (𝔅).g)
        (codimensionToRationalChow k' (pullback.snd sX (𝔅).g) i
          (codimensionChowBaseChange k k' sX i a))) =
      (VectorBundleKZero.pullback (pullback.fst sX (𝔅).g)).toIntLinearMap.baseChange ℚ
        ((rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field sX)
          (exists_bounds_relativeDimension_fieldChowSituation k sX)).symm
          (smoothChowEquiv sX (codimensionToRationalChow k sX i a))) := by
  set sX' := pullback.snd sX (𝔅).g
  rw [AlgEquiv.symm_apply_eq, rationalChernCharacterAlgEquiv_apply]
  set β := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field sX)
    (exists_bounds_relativeDimension_fieldChowSituation k sX)).symm
      (smoothChowEquiv sX (codimensionToRationalChow k sX i a)) with hβ
  have hβ' : rationalChernCharacterCap (fieldChowSituation k) sX β
      (rationalFundamentalClass (fieldChowSituation k) sX) =
        codimensionToRationalChow k sX i a := by
    have h := congrArg (RationalIntersectionRing.equiv _ _).symm
      ((rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field sX)
        (exists_bounds_relativeDimension_fieldChowSituation k sX)).apply_symm_apply
        (smoothChowEquiv sX (codimensionToRationalChow k sX i a)))
    rw [rationalChernCharacterAlgEquiv_apply] at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  obtain ⟨lo, _, hlo⟩ := exists_bounds_relativeDimension_fieldChowSituation k sX
  obtain ⟨lo', _, hlo'⟩ := exists_bounds_relativeDimension_fieldChowSituation k' sX'
  have hX : BddBelow (Set.range (relativeDimension (fieldChowSituation k).dimensionFunction sX)) :=
    ⟨lo, by rintro _ ⟨x, rfl⟩; exact (hlo x).1⟩
  have hX' : BddBelow (Set.range
      (relativeDimension (fieldChowSituation k').dimensionFunction sX')) :=
    ⟨lo', by rintro _ ⟨x, rfl⟩; exact (hlo' x).1⟩
  rw [← rationalBaseChangeChowPullback_rationalFundamentalClass k k' sX,
    ← rationalBaseChangeChowPullback_rationalChernCharacterCap (𝔅) sX hX hX', hβ',
    codimensionToRationalChow_codimensionChowBaseChange]

end Stacks.Chow

end
