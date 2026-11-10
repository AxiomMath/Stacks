module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionTorsion
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionFiniteStageDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Divisibility of a Chow class descends along a finite extension of degree prime to the divisor

Let `E/k` be a finite extension of fields of degree `d` and let `X` be locally of finite type over
`k`. If the base change of a class `α ∈ CH_i(X)` to `X_E` is `n` times a class, then `d α` is `n`
times a class of `CH_i(X)`. This is the push-pull formula of Stacks 02RH along the finite locally
free projection `π : X_E ⟶ X` of degree `d`: if `π^* α = n δ` then `d α = π_* π^* α = n π_* δ`.
Consequently, when `d` and `n` are coprime, `α` itself is divisible by `n`.

This is how the proof of [Stacks, Tag 0FH7] passes from an algebraic closure of `k` to a separable
closure: a finite subextension of `k̄ / k^sep` is purely inseparable, so its degree is a power of
the characteristic, which is prime to `n`.

## Main results

* `Stacks.Chow.exists_finrank_zsmul_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul`:
  `π^* α = n δ` implies `d α = n β` for some `β`.
* `Stacks.Chow.exists_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul_of_isCoprime`:
  the same with `d` prime to `n` gives `α = n γ`.

## Implementation notes

The base change is read through `Stacks.Chow.baseChangeChowPullbackOfIsPullback` at the canonical
square, as in `Stacks.Chow.exists_finiteSubextension_baseChangeChowPullback_eq_zsmul`. The base
changed cycle lives in the Chow situation of `E`, and the push-pull formula in that of `k`. They
are matched as in
`Stacks.Chow.nsmul_eq_zero_of_baseChangeChowPullback_eq_zero_of_finiteDimensional`, through
`Stacks.Chow.isRationallyEquivalentToZero_congr` and
`Stacks.Chow.val_baseChangeCyclePullback_eq_val_flatPullback`.

## References

* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Along the base change `X_E ⟶ X` of a finite field extension `E/k`, the relative dimension of a
closed subscheme of `X_E` over `E` equals its relative dimension over `k`. -/
theorem relativeDimension_comp_pullbackSnd_fieldExtension
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType (pullback.fst f (fieldExtensionBaseChangeSituation k E).g)]
    (W : Scheme.{u}) (j : W ⟶ pullback f (fieldExtensionBaseChangeSituation k E).g)
    [IsClosedImmersion j] :
    relativeDimension (fieldChowSituation E).dimensionFunction
        (j ≫ pullback.snd f (fieldExtensionBaseChangeSituation k E).g) =
      relativeDimension (fieldChowSituation k).dimensionFunction
        (j ≫ (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f)) := by
  funext w
  rw [show j ≫ (pullback.fst f _ ≫ f) =
      (j ≫ pullback.snd f _) ≫ (fieldExtensionBaseChangeSituation k E).g by
    rw [pullback.condition, Category.assoc]]
  exact (relativeDimension_comp_fieldExtension k E _ w).symm

/-- Along the base change `X_E ⟶ X` of a finite field extension `E/k`, an `i`-cycle of `X_E` over
`E` is an `i`-cycle of `X_E` over `k`. -/
theorem mem_cyclesOfDimension_pullbackFst_comp_fieldExtension
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType (pullback.fst f (fieldExtensionBaseChangeSituation k E).g)] (i : ℤ)
    (c : CycleGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i) :
    c.1 ∈ cyclesOfDimension (fieldChowSituation k)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) i := fun Z hZ ↦ by
  have h := relativeDimension_comp_pullbackSnd_fieldExtension k E f _ (𝟙 _)
  simp only [Category.id_comp] at h
  simpa [deltaDimension, h] using c.2 Z hZ

/-- For a finite field extension `E/k`, the base change of a cycle along the canonical pullback
square agrees with its flat pullback along the projection `X_E ⟶ X`. -/
theorem val_baseChangeCyclePullbackOfIsPullback_eq_val_flatPullback
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    [LocallyOfFiniteType (pullback.fst f (fieldExtensionBaseChangeSituation k E).g)]
    [Flat (pullback.fst f (fieldExtensionBaseChangeSituation k E).g)]
    (hrd : AlgebraicGeometry.RelativeDimension
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) 0)
    (i : ℤ) (z : CycleGroup (fieldChowSituation k) f i) :
    (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i z).1 =
      (flatPullback (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0 hrd i z).1 := by
  ext y
  have hiso :
      (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g).isoPullback.hom =
        𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [baseChangeCyclePullbackOfIsPullback_apply, hiso]
  exact DFunLike.congr_fun (val_baseChangeCyclePullback_eq_val_flatPullback k E f hrd i z) y

/-- **Push-pull for divisibility along a finite field extension.** Let `E/k` be finite of degree
`d`, let `X` be locally of finite type over `k`, and let `α ∈ CH_i(X)` have base change to `X_E`
equal to `n δ`. Then `d α = n β` for some `β ∈ CH_i(X)`, namely `β = π_* δ` for the projection
`π : X_E ⟶ X`. -/
theorem exists_finrank_zsmul_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (i n : ℤ)
    (α : chowGroup (fieldChowSituation k) f i)
    (δ : chowGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i)
    (hα : baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i α = n • δ) :
    ∃ β : chowGroup (fieldChowSituation k) f i, (Module.finrank k E : ℤ) • α = n • β := by
  set B := fieldExtensionBaseChangeSituation k E
  set π := pullback.fst f B.g
  set q := pullback.snd f B.g
  set d := Module.finrank k E
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d :=
    isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension k E f
  have : LocallyOfFiniteType π :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank _ d
  have : Flat π := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank _ d
  have : IsProper π := Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank π d
  have hrd : AlgebraicGeometry.RelativeDimension π 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank _ d
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences _ f i) α
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences _ q i) δ
  rw [baseChangeChowPullbackOfIsPullback_mk, ← map_zsmul, QuotientAddGroup.mk'_eq_mk'] at hα
  obtain ⟨r, hr, hrz⟩ := hα
  have hcast : i + ((0 : ℕ) : ℤ) = i := by simp
  let P : CycleGroup (fieldChowSituation k) (π ≫ f) i :=
    hcast ▸ flatPullback (fieldChowSituation k) (π ≫ f) f π rfl 0 hrd i z
  let W : CycleGroup (fieldChowSituation k) (π ≫ f) i :=
    ⟨w.1, mem_cyclesOfDimension_pullbackFst_comp_fieldExtension k E f i w⟩
  have hre : P - n • W ∈ rationalEquivalences (fieldChowSituation k) (π ≫ f) i := by
    have hr' : baseChangeCyclePullbackOfIsPullback B rfl f (IsPullback.of_hasPullback f B.g) i z
        - n • w ∈ rationalEquivalences (fieldChowSituation E) q i := by
      convert neg_mem hr using 1
      rw [← hrz]
      abel
    refine (isRationallyEquivalentToZero_congr (fieldChowSituation E) (fieldChowSituation k)
      q (π ≫ f) (relativeDimension_comp_pullbackSnd_fieldExtension k E f) i _ _ ?_).1 hr'
    rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul,
      val_cycleGroup_cast,
      val_baseChangeCyclePullbackOfIsPullback_eq_val_flatPullback k E f hrd i z]
  have hpush : properPushforward (fieldChowSituation k) (π ≫ f) f π rfl i (P - n • W) ∈
      rationalEquivalences (fieldChowSituation k) f i := by
    simpa [RationallyEquivalent, properPushforward_zero] using
      properPushforward_rationallyEquivalent_of_isProper (fieldChowSituation k)
        (π ≫ f) f π rfl i (α := P - n • W) (β := 0) (by simpa using hre)
  have hπP : properPushforward (fieldChowSituation k) (π ≫ f) f π rfl i P = (d : ℤ) • z := by
    rw [← properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank (fieldChowSituation k)
      (π ≫ f) f π d rfl i hcast z]
    apply Subtype.ext
    rw [val_cycleGroup_cast]
    change AlgebraicCycle.map π _ _ P.1 = AlgebraicCycle.map π _ _ _
    rw [val_cycleGroup_cast]
  refine ⟨QuotientAddGroup.mk' _ (properPushforward (fieldChowSituation k) (π ≫ f) f π rfl i W),
    ?_⟩
  rw [← map_zsmul, ← map_zsmul, QuotientAddGroup.mk'_eq_mk']
  refine ⟨-(properPushforward (fieldChowSituation k) (π ≫ f) f π rfl i (P - n • W)),
    neg_mem hpush, ?_⟩
  rw [properPushforward_sub, ← properPushforwardHom_apply (fieldChowSituation k) _ _ _ _ _ (n • W),
    map_zsmul, properPushforwardHom_apply, hπP]
  abel

/-- **Divisibility of a Chow class descends along a finite field extension of degree prime to
the divisor.** Let `E/k` be finite of degree `d` with `d` and `n` coprime, and let `α ∈ CH_i(X)`
have base change to `X_E` divisible by `n`. Then `α` is divisible by `n` in `CH_i(X)`. -/
theorem exists_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul_of_isCoprime
    (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] {X : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (i n : ℤ)
    (hcop : IsCoprime (Module.finrank k E : ℤ) n)
    (α : chowGroup (fieldChowSituation k) f i)
    (δ : chowGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i)
    (hα : baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i α = n • δ) :
    ∃ γ : chowGroup (fieldChowSituation k) f i, α = n • γ := by
  obtain ⟨β, hβ⟩ :=
    exists_finrank_zsmul_eq_zsmul_of_baseChangeChowPullbackOfIsPullback_eq_zsmul k E f i n α δ hα
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a • β + b • α, ?_⟩
  calc α = (a * (Module.finrank k E : ℤ) + b * n) • α := by rw [hab, one_smul]
    _ = a • ((Module.finrank k E : ℤ) • α) + b • (n • α) := by
        rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • β + b • α) := by
        rw [hβ, smul_add, smul_comm a n β, smul_comm b n α]

end Stacks.Chow

end
