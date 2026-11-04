module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CupLengthVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterVectorBundle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded

/-!
# Vanishing of the power sums and Chern classes of high degree on a quasi-compact scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and quasi-compact, and let `E ∈ D(𝒪_X)` be an object whose Chern classes are
defined (Stacks 0F9E). The last sentence of Stacks 0FET asserts that the Chern character of `E`
lies in `A^*(X) ⊗ 𝐐 = ⊕_p A^p(X) ⊗ 𝐐` rather than only in `∏_p A^p(X) ⊗ 𝐐`: the power sums
`P_p(E) ∈ A^p(X)` vanish for all large `p`. The same holds for the Chern classes `c_p(E)`. No
finite-dimensionality of `X` is assumed.

The proof is a cup-length argument (`Stacks.Chow.TotalChowClass.prod_ofFn_eq_zero_of_res_eq_zero`).
A finite locally free module `ℰ` of constant rank `r` on a quasi-compact scheme is free on the
members of a finite open cover `X = U_1 ∪ ⋯ ∪ U_m`, and the Chern classes of a free module are
trivial, so `c_i(ℰ)` restricts to zero on every `U_a` for `i ≥ 1`. The classes restricting to zero
on every `U_a` form an ideal of the commutative ring of Chern classes whose `m`-th power is zero.
The power sum `P_p(ℰ)` is Newton's polynomial in `c_1(ℰ), …, c_r(ℰ)`, weighted homogeneous of
degree `p`, so each of its monomials has at least `p / r` factors, and `P_p(ℰ) = 0` for `p > m r`.
Likewise `1 - c(ℰ)` is nilpotent, so `c(ℰ)⁻¹` is a finite geometric series and has only finitely
many nonzero components. For `E` with defined Chern classes these statements pass to a presentation
`Lf^*E ≅ ℰ^•` on an envelope `f : Y ⟶ X`, where `Y` is quasi-compact, `ℰ^•` is a bounded complex,
its terms have finitely many rank loci, and restriction along `f` is injective.

## Main definitions

* `Stacks.Chow.freeSuccIso` — the free module of rank `r + 1` is that of rank `r` plus `𝒪_X`.
* `Stacks.Chow.TotalChowClass.finiteSupport` — the subring `⊕_p A^p(X)` of `∏_p A^p(X)`.
* `Stacks.Chow.chernRingVanishingIdeal` — the ideal of the Chern classes vanishing on every
  member of a family of open subschemes.

## Main results

* `Stacks.Chow.totalChern_free` — the total Chern class of a free module is `1`.
* `Stacks.Chow.exists_cover_res_totalChern_eq_one` — on a quasi-compact scheme a module of
  constant rank is trivial on the members of a finite open cover.
* `Stacks.Chow.powerSumEval_mem_pow` — Newton's polynomials of a sequence in an ideal.
* `Stacks.Chow.exists_powerSumTotal_eq_zero`,
  `Stacks.Chow.exists_powerSumOfFiniteLocallyFree_eq_zero`,
  `Stacks.Chow.exists_powerSumComplex_eq_zero` — the power sums of modules and complexes on a
  quasi-compact scheme vanish in high degrees.
* `Stacks.Chow.exists_perfectPowerSum_eq_zero`, `Stacks.Chow.exists_perfectPowerSumClass_eq_zero`,
  `Stacks.Chow.exists_perfectChernCharacter_eq_zero` — the last sentence of Stacks 0FET for
  `P_p(E)` and `ch_p(E)`.
* `Stacks.Chow.perfectChernClass_mem_finiteSupport`, `Stacks.Chow.exists_perfectChernClass_eq_zero`
  — the same for `c(E)` and `c_p(E)`.

## Implementation notes

The source states the result for perfect `E`; only the definedness of the Chern classes of `E` is
used. On a quasi-compact scheme the Chern classes of a perfect object are always defined
(Stacks 0GUE (4), `Stacks.Chow.hasDefinedChernClasses_of_compactSpace`).

## References

* [Stacks Project, Tag 0FET](https://stacks.math.columbia.edu/tag/0FET)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free

section Free

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The free module of rank `r + 1` is the direct sum of the free module of rank `r` and the
structure sheaf. -/
def freeSuccIso (r : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r + 1))) ≅
      (SheafOfModules.free (ULift.{u} (Fin r)) : X.Modules) ⊞
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SheafOfModules.freeFunctor.mapIso
      (Equiv.ulift.trans ((finSuccEquiv' (Fin.last r)).trans
        ((Equiv.optionEquivSumPUnit.{u} (Fin r)).trans
          (Equiv.sumCongr Equiv.ulift.symm (Equiv.refl _))))).toIso ≪≫
    (SheafOfModules.freeSumIso _ _).symm ≪≫
    coprod.mapIso (Iso.refl _) (Stacks.SheafOfModules.Invertible.freeUniqueIso PUnit) ≪≫
    (biprod.isoCoprod _ _).symm

/-- **The total Chern class of a free module is `1`.** -/
theorem totalChern_free (r : ℕ) :
    totalChern C sX (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) r = 1 := by
  induction r with
  | zero => exact totalChern_of_rank_zero C sX _
  | succ r ih =>
    have hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (SheafOfModules.unit X.ringCatSheaf) 1 :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        (Stacks.SheafOfModules.Invertible.freeUniqueIso (ULift.{u} (Fin 1)))
        inferInstance
    have key := totalChern_biprod C sX
      (SheafOfModules.free (ULift.{u} (Fin r)) : X.Modules)
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) r 1
    rw [ih, totalChern_eq_one_of_iso_unit C sX _ (Iso.refl _), one_mul] at key
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((SheafOfModules.free (ULift.{u} (Fin r)) : X.Modules) ⊞
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (r + 1) :=
      GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
        (ShortComplex.Splitting.ofHasBinaryBiproduct
          (SheafOfModules.free (ULift.{u} (Fin r)) : X.Modules)
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)).shortExact r 1
        inferInstance hG
    exact (totalChern_congr C sX (freeSuccIso r) rfl).trans key

/-- **A module free of rank `r` on an open subscheme has total Chern class `1` there.** -/
theorem res_totalChern_eq_one_of_restrict_iso_free (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    TotalChowClass.res U.ι rfl (totalChern C sX M r) = 1 := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank M r U.ι
  rw [TotalChowClass.res_totalChern]
  exact (totalChern_congr C _
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) rfl).trans
    (totalChern_free C _ r)

/-- A quasi-compact scheme covered by the members of a family of opens is covered by finitely many
of them. -/
private theorem exists_finset_cover {X : Scheme.{u}} [CompactSpace X] {I : Type*}
    (U : I → X.Opens) (h : ∀ x : X, ∃ i, x ∈ U i) : ∃ t : Finset I, ∀ x : X, ∃ i ∈ t, x ∈ U i := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr (h x))
  exact ⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩

/-- **On a quasi-compact scheme a module of constant rank is free on the members of a finite open
cover**, so its total Chern class restricts to `1` on each of them. -/
theorem exists_cover_res_totalChern_eq_one [CompactSpace X] (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    ∃ (m : ℕ) (U : Fin m → X.Opens), (∀ x : X, ∃ a, x ∈ U a) ∧
      ∀ a, TotalChowClass.res (U a).ι rfl (totalChern C sX M r) = 1 := by
  classical
  have h := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M r).mpr ‹_›
  choose V hV e using h
  obtain ⟨t, ht⟩ := exists_finset_cover V fun x ↦ ⟨x, hV x⟩
  refine ⟨t.card, fun a ↦ V (t.equivFin.symm a), fun x ↦ ?_, fun a ↦
    res_totalChern_eq_one_of_restrict_iso_free C sX M r _ (e _).some⟩
  obtain ⟨y, hy, hxy⟩ := ht x
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end Free

/-! ### Clopen decompositions of a quasi-compact scheme -/

/-- **A decomposition of a quasi-compact scheme into open and closed pieces has only finitely many
nonempty pieces.** -/
theorem IsClopenDecomposition.exists_finset {X : Scheme.{u}} [CompactSpace X] {I : Type*}
    {U : I → X.Opens} (hU : IsClopenDecomposition U) :
    ∃ t : Finset I, ∀ i ∉ t, ∀ x : X, x ∉ U i := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_cover U hU.exists_mem
  refine ⟨t, fun i hi x hx ↦ hi ?_⟩
  obtain ⟨j, hj, hxj⟩ := ht x
  rwa [hU.eq_of_mem hx hxj]

/-- The pieces of a decomposition of a quasi-compact scheme into open and closed pieces are
quasi-compact. -/
theorem IsClopenDecomposition.compactSpace {X : Scheme.{u}} [CompactSpace X] {I : Type*}
    {U : I → X.Opens} (hU : IsClopenDecomposition U) (i : I) : CompactSpace (U i : Scheme.{u}) :=
  isCompact_iff_compactSpace.mp (hU.isClopen i).isClosed.isCompact

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The homogeneous component of degree `i` of a total class vanishes exactly when its
component of degree `i` does. -/
theorem homPart_eq_zero_iff (i : ℕ) (c : TotalChowClass C sX) :
    TotalChowClass.homComponent i c = 0 ↔ c i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ext fun p ↦ ?_⟩
  · have := congrFun h i
    rwa [TotalChowClass.homComponent_apply, if_pos rfl] at this
  · rw [TotalChowClass.homComponent_apply]
    split_ifs with hp
    · subst hp
      exact h
    · rfl

/-- **Vanishing in high degrees is detected on the pieces of a decomposition of a quasi-compact
scheme into open and closed pieces.** If on every piece the restrictions of a sequence of total
classes vanish from some index on, so does the sequence. -/
theorem exists_forall_ge_eq_zero_of_res [CompactSpace X] {I : Type u} {U : I → X.Opens}
    (hU : IsClopenDecomposition U) (c : ℕ → TotalChowClass C sX)
    (h : ∀ i, ∃ N, ∀ p ≥ N, res (U i).ι rfl (c p) = 0) : ∃ N, ∀ p ≥ N, c p = 0 := by
  classical
  obtain ⟨t, ht⟩ := hU.exists_finset
  choose N hN using h
  refine ⟨t.sup N, fun p hp ↦ eq_of_res_eq hU fun i ↦ ?_⟩
  rw [map_zero]
  by_cases hi : i ∈ t
  · exact hN i p (le_trans (Finset.le_sup hi) hp)
  · have : IsEmpty (U i : Scheme.{u}) := ⟨fun x ↦ ht i hi _ x.2⟩
    exact (subsingleton_of_isEmpty _).elim _ _

variable (C sX) in
/-- **The total classes with finitely many nonzero components**, `⊕_p A^p(X)` inside
`∏_p A^p(X)`, as a subring. -/
def finiteSupport : Subring (TotalChowClass C sX) where
  carrier := {c | ∃ N, ∀ p ≥ N, c p = 0}
  mul_mem' := by
    rintro c d ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨N + N', fun p hp ↦ ?_⟩
    rw [← homPart_eq_zero_iff, TotalChowClass.homComponent_mul_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    by_cases hjN : N' ≤ j
    · rw [(homPart_eq_zero_iff j d).mpr (hN' j hjN), mul_zero]
    · rw [(homPart_eq_zero_iff (p - j) c).mpr (hN (p - j) (by omega)), zero_mul]
  one_mem' := ⟨1, fun _ hp ↦ one_apply_of_ne (by omega)⟩
  add_mem' := by
    rintro c d ⟨N, hN⟩ ⟨N', hN'⟩
    exact ⟨max N N', fun p hp ↦ by
      rw [add_apply, hN p (le_of_max_le_left hp), hN' p (le_of_max_le_right hp), add_zero]⟩
  zero_mem' := ⟨0, fun _ _ ↦ rfl⟩
  neg_mem' := by
    rintro c ⟨N, hN⟩
    exact ⟨N, fun p hp ↦ by rw [neg_apply, hN p hp, neg_zero]⟩

/-- A class lies in `⊕_p A^p(X)` exactly when its components vanish from some degree on. -/
theorem mem_finiteSupport_iff (c : TotalChowClass C sX) :
    c ∈ finiteSupport C sX ↔ ∃ N, ∀ p ≥ N, c p = 0 :=
  Iff.rfl

/-- A class lies in `⊕_p A^p(X)` exactly when its homogeneous components vanish from some degree
on. -/
theorem mem_finiteSupport_iff_homPart (c : TotalChowClass C sX) :
    c ∈ finiteSupport C sX ↔ ∃ N, ∀ p ≥ N, TotalChowClass.homComponent p c = 0 := by
  simp only [mem_finiteSupport_iff, homPart_eq_zero_iff]

/-- Restriction maps `⊕_p A^p(X)` to `⊕_p A^p(X')`. -/
theorem res_mem_finiteSupport {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']
    (h : X' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sX') {c : TotalChowClass C sX}
    (hc : c ∈ finiteSupport C sX) : res h hs c ∈ finiteSupport C sX' := by
  rw [mem_finiteSupport_iff_homPart] at hc ⊢
  obtain ⟨N, hN⟩ := hc
  exact ⟨N, fun p hp ↦ by rw [← TotalChowClass.res_homComponent, hN p hp, map_zero]⟩

/-- A class whose restriction along an envelope lies in `⊕_p A^p` lies in `⊕_p A^p`. -/
theorem mem_finiteSupport_of_res_of_isEnvelope {Y : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] (f : Y ⟶ X) [LocallyOfFiniteType f] (hf : IsEnvelope f)
    (hs : f ≫ sX = sY) {c : TotalChowClass C sX} (hc : res f hs c ∈ finiteSupport C sY) :
    c ∈ finiteSupport C sX := by
  rw [mem_finiteSupport_iff_homPart] at hc ⊢
  obtain ⟨N, hN⟩ := hc
  exact ⟨N, fun p hp ↦ res_injective_of_isEnvelope f hf hs (by
    rw [TotalChowClass.res_homComponent, hN p hp, map_zero])⟩

/-- **`⊕_p A^p` is detected on the pieces of a decomposition of a quasi-compact scheme into open
and closed pieces.** -/
theorem mem_finiteSupport_of_res [CompactSpace X] {I : Type u} {U : I → X.Opens}
    (hU : IsClopenDecomposition U) {c : TotalChowClass C sX}
    (h : ∀ i, res (U i).ι rfl c ∈ finiteSupport C ((U i).ι ≫ sX)) : c ∈ finiteSupport C sX := by
  rw [mem_finiteSupport_iff_homPart]
  refine exists_forall_ge_eq_zero_of_res hU (fun p ↦ TotalChowClass.homComponent p c) fun i ↦ ?_
  obtain ⟨N, hN⟩ := (mem_finiteSupport_iff_homPart _).mp (h i)
  exact ⟨N, fun p hp ↦ by rw [TotalChowClass.res_homComponent, hN p hp]⟩

/-- **The inverse of a unit `u` with `1 - u` nilpotent lies in `⊕_p A^p` if `u` does**: it is the
finite geometric series `∑_{k < m} (1 - u)^k`. -/
theorem val_inv_mem_finiteSupport (u : (TotalChowClass C sX)ˣ)
    (hu : (u : TotalChowClass C sX) ∈ finiteSupport C sX) {m : ℕ}
    (hm : (1 - (u : TotalChowClass C sX)) ^ m = 0) :
    ((u⁻¹ : (TotalChowClass C sX)ˣ) : TotalChowClass C sX) ∈ finiteSupport C sX := by
  have key : (∑ k ∈ Finset.range m, (1 - (u : TotalChowClass C sX)) ^ k) * u = 1 := by
    have h := geom_sum_mul (1 - (u : TotalChowClass C sX)) m
    rw [hm, sub_sub_cancel_left, mul_neg, zero_sub, neg_inj] at h
    exact h
  rw [Units.inv_eq_of_mul_eq_one_left key]
  exact Subring.sum_mem _ fun k _ ↦ Subring.pow_mem _ (Subring.sub_mem _ (Subring.one_mem _) hu) k

/-- The integer powers of a unit which lies in `⊕_p A^p` together with its inverse lie in
`⊕_p A^p`. -/
theorem val_zpow_mem_finiteSupport (u : (TotalChowClass C sX)ˣ)
    (hu : (u : TotalChowClass C sX) ∈ finiteSupport C sX)
    (hu' : ((u⁻¹ : (TotalChowClass C sX)ˣ) : TotalChowClass C sX) ∈ finiteSupport C sX)
    (k : ℤ) : ((u ^ k : (TotalChowClass C sX)ˣ) : TotalChowClass C sX) ∈ finiteSupport C sX := by
  rcases k with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact Subring.pow_mem _ hu k
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    exact Subring.pow_mem _ hu' _

end TotalChowClass

/-! ### The Chern classes of a module of constant rank -/

section ConstantRank

open TotalChowClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The total Chern class of a module of constant rank `r` vanishes above degree `r`. -/
theorem totalChern_mem_finiteSupport (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    totalChern C sX M r ∈ finiteSupport C sX :=
  ⟨r + 1, fun _ hp ↦ totalChern_apply_of_lt C sX M r (by omega)⟩

/-- **On a quasi-compact scheme `1 - c(ℰ)` is nilpotent** for a module `ℰ` of constant rank: it
vanishes on the members of a finite open cover trivializing `ℰ`. -/
theorem isNilpotent_one_sub_totalChern [CompactSpace X] (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    ∃ m : ℕ, (1 - totalChern C sX M r) ^ m = 0 := by
  obtain ⟨m, U, hU, h⟩ := exists_cover_res_totalChern_eq_one C sX M r
  exact ⟨m, pow_eq_zero_of_res_eq_zero U hU _ fun a ↦ by rw [map_sub, map_one, h a, sub_self]⟩

/-- **On a quasi-compact scheme the inverse of the total Chern class of a module of constant rank
lies in `⊕_p A^p(X)`.** -/
theorem val_inv_totalChernUnit_mem_finiteSupport [CompactSpace X] (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    (((totalChernUnit C sX M r)⁻¹ : (TotalChowClass C sX)ˣ) : TotalChowClass C sX) ∈
      finiteSupport C sX := by
  obtain ⟨m, hm⟩ := isNilpotent_one_sub_totalChern C sX M r
  exact val_inv_mem_finiteSupport _ (totalChern_mem_finiteSupport C sX M r) hm

/-- The ideal of the ring of Chern classes of the classes vanishing on every member of a family
of open subschemes. -/
def chernRingVanishingIdeal {m : ℕ} (U : Fin m → X.Opens) : Ideal (chernRing C sX) :=
  ⨅ a, RingHom.ker ((res (U a).ι rfl).comp (chernRing C sX).subtype)

/-- A Chern class lies in the ideal exactly when it restricts to zero on every member. -/
theorem mem_chernRingVanishingIdeal {m : ℕ} (U : Fin m → X.Opens) (x : chernRing C sX) :
    x ∈ chernRingVanishingIdeal C sX U ↔ ∀ a, res (U a).ι rfl (x : TotalChowClass C sX) = 0 := by
  simp [chernRingVanishingIdeal]

/-- **Cup-length vanishing in the ring of Chern classes**: for an open cover by `m` members, the
`m`-th power of the ideal of the classes vanishing on every member is zero. -/
theorem chernRingVanishingIdeal_pow_eq_bot {m : ℕ} (U : Fin m → X.Opens)
    (hU : ∀ x : X, ∃ a, x ∈ U a) : chernRingVanishingIdeal C sX U ^ m = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hx
  refine Subtype.ext ?_
  have hmap := map_list_prod (chernRing C sX).subtype (List.ofFn fun i ↦ (f i : chernRing C sX))
  rw [List.map_ofFn] at hmap
  change (chernRing C sX).subtype _ = _
  rw [hmap]
  exact prod_ofFn_eq_zero_of_res_eq_zero U hU _ fun a ↦
    (mem_chernRingVanishingIdeal C sX U _).mp (f a).2 a

end ConstantRank

/-! ### Newton's polynomials evaluated at a sequence in an ideal -/

/-- **The power sums of a sequence in an ideal lie in powers of the ideal.** Let `a_1, a_2, …` lie
in an ideal `J` and vanish beyond the index `r`. Then `P_p(a) ∈ J^{n+1}` as soon as `n r < p`:
every monomial of the weighted-homogeneous polynomial `P_p` of degree `p` has more than `n`
factors. -/
theorem powerSumEval_mem_pow {R : Type*} [CommRing R] (J : Ideal R) (a : ℕ → R) (r : ℕ)
    (ha : ∀ i, 1 ≤ i → a i ∈ J) (hr : ∀ i, r < i → a i = 0) (n p : ℕ) (hp : n * r < p) :
    AlgebraicGeometry.powerSumEval a p ∈ J ^ (n + 1) := by
  induction n generalizing p with
  | zero =>
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [AlgebraicGeometry.powerSumEval_succ, zero_add, pow_one]
    refine J.add_mem (J.sum_mem fun j _ ↦ ?_) (J.mul_mem_left _ (ha _ (by omega)))
    exact J.mul_mem_right _ (J.mul_mem_left _ (ha _ (by omega)))
  | succ n ih =>
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by rw [Nat.succ_mul] at hp; omega⟩
    rw [AlgebraicGeometry.powerSumEval_succ]
    have hrp : r < p + 1 := by rw [Nat.succ_mul] at hp; omega
    refine (J ^ (n + 1 + 1)).add_mem ((J ^ (n + 1 + 1)).sum_mem fun j _ ↦ ?_) ?_
    · by_cases hjr : r < j + 1
      · rw [hr _ hjr, mul_zero, zero_mul]
        exact zero_mem _
      · rw [pow_succ']
        refine Ideal.mul_mem_mul (J.mul_mem_left _ (ha _ (by omega))) (ih _ ?_)
        rw [Nat.succ_mul] at hp
        generalize n * r = q at hp ⊢
        omega
    · rw [hr _ hrp, mul_zero]
      exact zero_mem _

/-! ### The power sums of a module of constant rank -/

section PowerSum

open TotalChowClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **On a quasi-compact scheme the power sums of a module of constant rank vanish in high
degrees**: if the module is free on the members of an open cover with `m` members, then
`P_p(ℰ) = 0` for `p > m r`. -/
theorem exists_powerSumTotal_eq_zero [CompactSpace X] (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    ∃ N, ∀ p ≥ N, powerSumTotal C sX M r p = 0 := by
  obtain ⟨m, U, hU, h⟩ := exists_cover_res_totalChern_eq_one C sX M r
  refine ⟨m * r + 1, fun p hp ↦ ?_⟩
  rw [powerSumTotal_of_ne_zero C sX M r (by omega)]
  have hmem := powerSumEval_mem_pow (chernRingVanishingIdeal C sX U) (chernSeq C sX M r) r
    (fun i hi ↦ (mem_chernRingVanishingIdeal C sX U _).mpr fun a ↦ by
      change res (U a).ι rfl (TotalChowClass.homComponent i (totalChern C sX M r)) = 0
      rw [TotalChowClass.res_homComponent, h a, homPart_eq_zero_iff, one_apply_of_ne (by omega)])
    (fun i hi ↦ Subtype.ext ((homPart_eq_zero_iff i _).mpr
      (totalChern_apply_of_lt C sX M r hi))) m p (by omega)
  have h0 : AlgebraicGeometry.powerSumEval (chernSeq C sX M r) p = 0 := by
    have h1 := Ideal.pow_le_pow_right (Nat.le_succ m) hmem
    rw [chernRingVanishingIdeal_pow_eq_bot C sX U hU] at h1
    exact (Submodule.mem_bot _).mp h1
  rw [h0]
  rfl

/-- **On a quasi-compact scheme the power sums of a finite locally free module vanish in high
degrees**, whatever its ranks: on each of the finitely many nonempty rank loci it has constant
rank. -/
theorem exists_powerSumOfFiniteLocallyFree_eq_zero [CompactSpace X] (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    ∃ N, ∀ p ≥ N, powerSumOfFiniteLocallyFree C sX F p = 0 := by
  have hU := isClopenDecomposition_rankLociFamily F
  refine exists_forall_ge_eq_zero_of_res hU _ fun r ↦ ?_
  have := hU.compactSpace r
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily F r
  obtain ⟨N, hN⟩ := exists_powerSumTotal_eq_zero C ((rankLociFamily F r).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLociFamily F r).ι).obj F) r.down
  exact ⟨N, fun p hp ↦ (res_powerSumOfFiniteLocallyFree_rankLocus C sX F r p).trans (hN p hp)⟩

/-- **On a quasi-compact scheme the power sums of a locally bounded complex of finite locally free
modules vanish in high degrees**: the complex is bounded, and `P_p(ℰ^•)` is the alternating sum of
the power sums of its finitely many nonzero terms. -/
theorem exists_powerSumComplex_eq_zero [CompactSpace X] {P : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    ∃ N, ∀ p ≥ N, powerSumComplex C sX hP p = 0 := by
  classical
  obtain ⟨w, hw⟩ := exists_window_of_isLocallyBoundedFiniteLocallyFree hP
  have h : ∀ n, ∃ N, ∀ p ≥ N, @powerSumOfFiniteLocallyFree C _ sX _ (P.X n) (hP.1 n) p = 0 :=
    fun n ↦ @exists_powerSumOfFiniteLocallyFree_eq_zero C _ sX _ _ (P.X n) (hP.1 n)
  choose N hN using h
  refine ⟨(Finset.Icc w.1 (w.1 + w.2)).sup N, fun p hp ↦ ?_⟩
  rw [powerSumComplex_eq_sum_Icc C sX hP w.1 (w.1 + w.2) hw p]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [hN n p (le_trans (Finset.le_sup hn) hp), smul_zero]

end PowerSum

/-! ### The power sums and the Chern classes of a perfect object -/

section Perfect

open TotalChowClass

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- The source of an envelope of a quasi-compact scheme is quasi-compact. -/
theorem EnvelopePresentation.compactSpace [CompactSpace X] (H : EnvelopePresentation E) :
    CompactSpace H.Y :=
  have : IsProper H.f := H.envelope.1
  QuasiCompact.compactSpace_of_compactSpace H.f

/-- **Stacks 0FET, the power sums of a perfect object on a quasi-compact scheme.** If `X` is
quasi-compact and the Chern classes of `E ∈ D(𝒪_X)` are defined, then `P_p(E) = 0` for all large
`p`. Along the envelope of a presentation, `P_p(E)` restricts to `P_p(ℰ^•)` for a locally bounded
complex `ℰ^•` of finite locally free modules on a quasi-compact scheme, which vanishes for large
`p`; restriction along an envelope is injective. -/
theorem exists_perfectPowerSum_eq_zero [CompactSpace X] (hE : HasDefinedChernClasses E) :
    ∃ N, ∀ p ≥ N, perfectPowerSum C sX hE p = 0 := by
  let H := hE.some
  have := H.compactSpace
  obtain ⟨N, hN⟩ := exists_powerSumComplex_eq_zero C (H.f ≫ sX) H.locallyBounded
  exact ⟨N, fun p hp ↦ res_injective_of_isEnvelope H.f H.envelope rfl (by
    rw [res_perfectPowerSum_eq_powerSumComplex C sX hE H p, map_zero, hN p hp])⟩

/-- **Stacks 0FET, `P_p(E) ∈ A^p(X)`.** On a quasi-compact scheme, `P_p(E) = 0` in `A^p(X)` for
all large `p`. -/
theorem exists_perfectPowerSumClass_eq_zero [CompactSpace X] (hE : HasDefinedChernClasses E) :
    ∃ N, ∀ p ≥ N, perfectPowerSumComponent C sX hE p = 0 := by
  obtain ⟨N, hN⟩ := exists_perfectPowerSum_eq_zero C sX hE
  exact ⟨N, fun p hp ↦ by rw [perfectPowerSumComponent, hN p hp, TotalChowClass.zero_apply]⟩

/-- **Stacks 0FET, the Chern character of a perfect object on a quasi-compact scheme.** On a
quasi-compact scheme, `ch_p(E) = 0` in `A^p(X) ⊗ 𝐐` for all large `p`: the Chern character lies in
`A^*(X) ⊗ 𝐐`. -/
theorem exists_perfectChernCharacter_eq_zero [CompactSpace X] (hE : HasDefinedChernClasses E) :
    ∃ N, ∀ p ≥ N, perfectChernCharacterComponent C sX hE p = 0 := by
  obtain ⟨N, hN⟩ := exists_perfectPowerSumClass_eq_zero C sX hE
  exact ⟨N, fun p hp ↦ by rw [perfectChernCharacterComponent, hN p hp, TensorProduct.tmul_zero]⟩

/-- On a quasi-compact scheme the total Chern class of a bounded complex of finite locally free
modules of constant ranks lies in `⊕_p A^p`. -/
theorem complexChernBounded_mem_finiteSupport [CompactSpace X] (P : CochainComplex X.Modules ℤ)
    (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n)) :
    complexChernBounded C sX P ρ hP ∈ finiteSupport C sX := by
  rw [complexChernBounded, complexChernProd, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine Subring.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
  have := hP n
  exact val_zpow_mem_finiteSupport _ (totalChern_mem_finiteSupport C sX (P.X n) (ρ n))
    (val_inv_totalChernUnit_mem_finiteSupport C sX (P.X n) (ρ n)) _

/-- On a quasi-compact scheme the total Chern class of a locally bounded complex of finite locally
free modules lies in `⊕_p A^p`. -/
theorem complexChern_mem_finiteSupport [CompactSpace X] {P : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) : complexChern C sX hP ∈ finiteSupport C sX := by
  have hU := isClopenDecomposition_complexRankLoci hP
  refine mem_finiteSupport_of_res hU fun ρ ↦ ?_
  have := hU.compactSpace ρ
  rw [res_complexChern_complexRankLocus]
  exact complexChernBounded_mem_finiteSupport C _ _ _ _

/-- **Stacks 0FET, the Chern classes of a perfect object on a quasi-compact scheme.** If `X` is
quasi-compact and the Chern classes of `E ∈ D(𝒪_X)` are defined, then the total Chern class
`c(E)` lies in `⊕_p A^p(X)`. -/
theorem perfectChernClass_mem_finiteSupport [CompactSpace X] (hE : HasDefinedChernClasses E) :
    perfectChernClass C sX hE ∈ finiteSupport C sX := by
  let H := hE.some
  have := H.compactSpace
  refine mem_finiteSupport_of_res_of_isEnvelope H.f H.envelope rfl ?_
  rw [res_perfectChernClass C sX hE H]
  exact complexChern_mem_finiteSupport C _ H.locallyBounded

/-- **Stacks 0FET, the Chern classes of a perfect object on a quasi-compact scheme.** If `X` is
quasi-compact and the Chern classes of `E ∈ D(𝒪_X)` are defined, then `c_p(E) = 0` in `A^p(X)` for
all large `p`. -/
theorem exists_perfectChernClass_eq_zero [CompactSpace X] (hE : HasDefinedChernClasses E) :
    ∃ N, ∀ p ≥ N, perfectChernClass C sX hE p = 0 :=
  perfectChernClass_mem_finiteSupport C sX hE

end Perfect

end Stacks.Chow

end
