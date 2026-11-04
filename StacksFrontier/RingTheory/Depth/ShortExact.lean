module

public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Depth in a short exact sequence

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `0 → N' → N → N'' → 0` a short exact sequence of
finite `R`-modules. Then

* `min {depth N', depth N''} ≤ depth N`,
* `min {depth N, depth N' - 1} ≤ depth N''`,
* `min {depth N, depth N'' + 1} ≤ depth N'`,

where the depths are `I`-depths in `ℕ∞` and the subtraction is truncated.

## Main results

* `Module.min_depth_le_depth_of_exact`: the three inequalities above.

## References

* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX)

## Tags

depth, short exact sequence, regular sequence, ext
-/

@[expose] public section

universe v u u₁ u₂ u₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Ideal RingTheory.Sequence

namespace Stacks.Depth.ShortExactInequalities

/-! ### Comparisons in `ℕ∞` -/

/-- To bound `min a b` by `c` in `ℕ∞` it suffices to bound each natural number below both `a` and
`b` by `c`. -/
private lemma min_le_of_forall_natCast_le {a b c : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) ≤ a → (n : ℕ∞) ≤ b → (n : ℕ∞) ≤ c) : min a b ≤ c :=
  ENat.forall_natCast_le_iff_le.mp fun n hn =>
    h n (hn.trans (min_le_left _ _)) (hn.trans (min_le_right _ _))

/-- If `i < n` and `n ≤ b` in `ℕ∞`, then `i < b`. -/
private lemma natCast_lt_of_lt_of_le {b : ℕ∞} {n i : ℕ} (hi : i < n) (h : (n : ℕ∞) ≤ b) :
    (i : ℕ∞) < b :=
  lt_of_lt_of_le (by exact_mod_cast hi) h

/-- If `i < n` and `n ≤ b - 1` in `ℕ∞`, with the truncated subtraction, then `i + 1 < b`. -/
private lemma natCast_add_one_lt_of_lt_of_le_sub_one {b : ℕ∞} {n i : ℕ} (hi : i < n)
    (h : (n : ℕ∞) ≤ b - 1) : ((i + 1 : ℕ) : ℕ∞) < b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · exact ENat.natCast_lt_top _
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hb
    rw [← Nat.cast_one, ← ENat.natCast_sub, Nat.cast_le] at h
    rw [Nat.cast_lt]
    omega

/-- If `i + 1 < n` and `n ≤ b + 1` in `ℕ∞`, then `i < b`. -/
private lemma natCast_lt_of_add_one_lt_of_le_add_one {b : ℕ∞} {n i : ℕ} (hi : i + 1 < n)
    (h : (n : ℕ∞) ≤ b + 1) : (i : ℕ∞) < b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · exact ENat.natCast_lt_top _
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hb
    rw [← Nat.cast_add_one, Nat.cast_le] at h
    rw [Nat.cast_lt]
    omega

/-! ### Regular sequences and `Module.depth` -/

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {I : Ideal R}

/-- A weakly regular sequence drawn from `I` is regular as soon as `I • M ≠ M`. -/
private lemma isRegular_of_isWeaklyRegular (hI : I • (⊤ : Submodule R M) ≠ ⊤) {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ I) (h : IsWeaklyRegular M rs) : IsRegular M rs := by
  refine (isRegular_iff M rs).mpr ⟨h, fun hc => hI (le_antisymm le_top ?_)⟩
  calc (⊤ : Submodule R M) = Ideal.ofList rs • ⊤ := hc
    _ ≤ I • ⊤ := Submodule.smul_mono_left (Ideal.span_le.mpr hmem)

/-- If `I • M ≠ M`, then `n ≤ depth_I(M)` if and only if `I` contains an `M`-regular sequence of
length `n`. -/
private lemma natCast_le_depth_iff_exists_isRegular (hI : I • (⊤ : Submodule R M) ≠ ⊤) (n : ℕ) :
    (n : ℕ∞) ≤ Module.depth R I M ↔
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  have hntr : Nontrivial M :=
    (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ (lt_top_iff_ne_top.mpr hI))
  rw [Module.depth, ite_eq_right_of_eq_false _ _ (eq_false hI)]
  refine ⟨fun hn => ?_, fun ⟨rs, hlen, hmem, hreg⟩ => hlen ▸ le_biSup
    (fun rs : List R => (rs.length : ℕ∞)) (show rs ∈ {rs : List R | _} from ⟨hmem, hreg⟩)⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact ⟨[], rfl, by simp, .nil R M⟩
  obtain ⟨rs, hrs⟩ := lt_iSup_iff.mp
    (lt_of_lt_of_le (show ((n - 1 : ℕ) : ℕ∞) < (n : ℕ∞) by rw [Nat.cast_lt]; omega) hn)
  obtain ⟨⟨hmem, hreg⟩, hlen⟩ := lt_iSup_iff.mp hrs
  rw [Nat.cast_lt] at hlen
  exact ⟨rs.take n, List.length_take_of_le (by omega),
    fun r hr => hmem r (List.mem_of_mem_take hr), isRegular_take rs hreg n⟩

/-! ### Rees' theorem for `Module.depth` -/

/-- The quotient `R ⧸ I` as an object of `ModuleCat.{v} R`. -/
private noncomputable abbrev shrinkQuotient (R : Type u) [CommRing R] [Small.{v} R]
    (I : Ideal R) : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} (R ⧸ I))

/-- If `M` is finite and `I • M = M`, then every `Ext^i_R(R/I, M)` vanishes. -/
private lemma subsingleton_ext_of_smul_top_eq_top [Small.{v} R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (htop : I • (⊤ : Submodule R M) = ⊤)
    (i : ℕ) : Subsingleton (Ext (shrinkQuotient.{v} R I) (ModuleCat.of R M) i) := by
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
    Module.Finite.fg_top htop.ge
  have hann : (1 - r) ∈ Module.annihilator R (Shrink.{v} (R ⧸ I)) := by
    rw [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq, annihilator_quotient]
    simpa only [neg_sub] using (Ideal.neg_mem_iff I).mpr hr1
  have hid : ((1 - r) • 𝟙 (ModuleCat.of R M) : ModuleCat.of R M ⟶ ModuleCat.of R M)
      = 𝟙 (ModuleCat.of R M) := by
    ext m; simpa [sub_smul] using hr0 m Submodule.mem_top
  have hz := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
    (M := ModuleCat.of R M) (N := shrinkQuotient.{v} R I) hann i
  rw [hid] at hz
  rw [← AddCommGrpCat.isZero_of_iff_subsingleton, IsZero.iff_id_eq_zero, ← hz]
  ext x
  simp

/-- **Rees' theorem.** For a finite module `M` over a Noetherian ring `R` and an ideal `I ⊆ R`, one
has `n ≤ depth_I(M)` if and only if `Ext^i_R(R/I, M) = 0` for every `i < n`. -/
private lemma natCast_le_depth_iff [IsNoetherianRing R] [Small.{v} R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ Module.depth R I M ↔
      ∀ i < n, Subsingleton (Ext (shrinkQuotient.{v} R I) (ModuleCat.of R M) i) := by
  by_cases htop : I • (⊤ : Submodule R M) = ⊤
  · simp only [Module.depth, ite_eq_left_of_eq_true _ _ (eq_true htop), le_top, true_iff]
    exact fun i _ => subsingleton_ext_of_smul_top_eq_top I M htop i
  · rw [natCast_le_depth_iff_exists_isRegular htop]
    exact (ModuleCat.exists_isRegular_tfae I n (ModuleCat.of R M)
      (lt_top_iff_ne_top.mpr htop)).out 4 2

/-- Every `Ext^i_R(R/I, M)` with `i` below the `I`-depth of `M` vanishes. -/
private lemma subsingleton_ext_of_lt_depth [IsNoetherianRing R] [Small.{v} R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] {i : ℕ}
    (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (Ext (shrinkQuotient.{v} R I) (ModuleCat.of R M) i) :=
  (natCast_le_depth_iff I M (i + 1)).mp
    (by exact_mod_cast Order.add_one_le_of_lt hi) i (Nat.lt_succ_self i)

/-! ### Chasing the long exact sequence -/

/-- The middle term of a three-term exact stretch of abelian groups is trivial as soon as its two
neighbours are. -/
private lemma subsingleton_X₂_of_exact {S : ShortComplex AddCommGrpCat} (hS : S.Exact)
    (h₁ : Subsingleton S.X₁) (h₃ : Subsingleton S.X₃) : Subsingleton S.X₂ :=
  AddCommGrpCat.subsingleton_of_isZero <| hS.isZero_of_both_zeros
    ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₁).eq_zero_of_src _)
    ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₃).eq_zero_of_tgt _)

/-- If `f : A ⟶ B` is a monomorphism and `Ext^0(X, B)` is trivial, then so is `Ext^0(X, A)`. -/
private lemma subsingleton_ext_zero_of_mono {C : Type*} [Category C] [Abelian C] [HasExt C]
    (X : C) {A B : C} (f : A ⟶ B) [Mono f] (h : Subsingleton (Ext X B 0)) :
    Subsingleton (Ext X A 0) :=
  ⟨fun _ _ => Ext.postcomp_mk₀_injective_of_mono X f (Subsingleton.elim _ _)⟩

/-- The three depth inequalities of a short exact sequence `0 → A → B → C → 0` of finite modules
over a Noetherian ring, for `A`, `B`, `C` in one universe. -/
private lemma min_depth_le_depth_aux [IsNoetherianRing R] [Small.{v} R] (I : Ideal R)
    {A B C : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R B] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    min (Module.depth R I A) (Module.depth R I C) ≤ Module.depth R I B ∧
      min (Module.depth R I B) (Module.depth R I A - 1) ≤ Module.depth R I C ∧
      min (Module.depth R I B) (Module.depth R I C + 1) ≤ Module.depth R I A := by
  have : Module.Finite R C := Module.Finite.of_surjective g hg
  have : Module.Finite R A := Module.Finite.of_injective f hf
  have hS : (ModuleCat.shortComplexOfCompEqZero f g h.linearMap_comp_eq_zero).ShortExact :=
    ModuleCat.shortComplex_shortExact _ h hf hg
  have := hS.mono_f
  refine ⟨min_le_of_forall_natCast_le fun n hA hC =>
      (natCast_le_depth_iff I B n).mpr fun i hi =>
        subsingleton_X₂_of_exact (Ext.covariant_sequence_exact₂' (shrinkQuotient.{v} R I) hS i)
          (subsingleton_ext_of_lt_depth I A (natCast_lt_of_lt_of_le hi hA))
          (subsingleton_ext_of_lt_depth I C (natCast_lt_of_lt_of_le hi hC)),
    min_le_of_forall_natCast_le fun n hB hA =>
      (natCast_le_depth_iff I C n).mpr fun i hi =>
        subsingleton_X₂_of_exact
          (Ext.covariant_sequence_exact₃' (shrinkQuotient.{v} R I) hS i (i + 1) rfl)
          (subsingleton_ext_of_lt_depth I B (natCast_lt_of_lt_of_le hi hB))
          (subsingleton_ext_of_lt_depth I A (natCast_add_one_lt_of_lt_of_le_sub_one hi hA)),
    min_le_of_forall_natCast_le fun n hB hC =>
      (natCast_le_depth_iff I A n).mpr fun i hi => ?_⟩
  cases i with
  | zero =>
    exact subsingleton_ext_zero_of_mono _ (ModuleCat.ofHom f)
      (subsingleton_ext_of_lt_depth I B (natCast_lt_of_lt_of_le hi hB))
  | succ j =>
    exact subsingleton_X₂_of_exact
      (Ext.covariant_sequence_exact₁' (shrinkQuotient.{v} R I) hS j (j + 1) rfl)
      (subsingleton_ext_of_lt_depth I C (natCast_lt_of_add_one_lt_of_le_add_one hi hC))
      (subsingleton_ext_of_lt_depth I B (natCast_lt_of_lt_of_le hi hB))

/-- The three depth inequalities of a short exact sequence `0 → N' → N → N'' → 0` of finite modules
over a Noetherian ring, for `R`, `N'`, `N`, `N''` in arbitrary universes. -/
public theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {N' : Type u₁} {N : Type u₂} {N'' : Type u₃} [AddCommGroup N'] [Module R N']
    [AddCommGroup N] [Module R N] [AddCommGroup N''] [Module R N''] [Module.Finite R N]
    {f : N' →ₗ[R] N} {g : N →ₗ[R] N''} (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    min (Module.depth R I N') (Module.depth R I N'') ≤ Module.depth R I N ∧
      min (Module.depth R I N) (Module.depth R I N' - 1) ≤ Module.depth R I N'' ∧
      min (Module.depth R I N) (Module.depth R I N'' + 1) ≤ Module.depth R I N' := by
  have eN' : ULift.{max u u₁ u₂ u₃} N' ≃ₗ[R] N' := ULift.moduleEquiv
  have eN : ULift.{max u u₁ u₂ u₃} N ≃ₗ[R] N := ULift.moduleEquiv
  have eN'' : ULift.{max u u₁ u₂ u₃} N'' ≃ₗ[R] N'' := ULift.moduleEquiv
  have : Module.Finite R (ULift.{max u u₁ u₂ u₃} N) := Module.Finite.equiv eN.symm
  rw [← Module.depth_eq_depth_of_linearEquiv I eN', ← Module.depth_eq_depth_of_linearEquiv I eN,
    ← Module.depth_eq_depth_of_linearEquiv I eN'']
  exact min_depth_le_depth_aux I
    (A := ULift.{max u u₁ u₂ u₃} N') (B := ULift.{max u u₁ u₂ u₃} N)
    (C := ULift.{max u u₁ u₂ u₃} N'')
    (f := eN.symm.toLinearMap ∘ₗ f ∘ₗ eN'.toLinearMap)
    (g := eN''.symm.toLinearMap ∘ₗ g ∘ₗ eN.toLinearMap)
    (Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := eN'.symm) (e₂ := eN.symm)
      (e₃ := eN''.symm) (LinearMap.ext fun x => by simp) (LinearMap.ext fun x => by simp) h)
    (eN.symm.injective.comp (hf.comp eN'.injective))
    (eN''.symm.surjective.comp (hg.comp eN.surjective))

end Stacks.Depth.ShortExactInequalities

namespace Module

/-- **Depth in a short exact sequence.** Let `R` be a Noetherian ring, `I ⊆ R` an ideal, and let
`0 → N' → N → N'' → 0` be a short exact sequence of finite `R`-modules, given by `f : N' →ₗ[R] N`
injective, `g : N →ₗ[R] N''` surjective and `Function.Exact f g`. Then

1. `min {depth_I(N'), depth_I(N'')} ≤ depth_I(N)`,
2. `min {depth_I(N), depth_I(N') - 1} ≤ depth_I(N'')`,
3. `min {depth_I(N), depth_I(N'') + 1} ≤ depth_I(N')`,

the subtraction being the truncated one of `ℕ∞`. -/
@[stacks 00LX]
public theorem min_depth_le_depth_of_exact {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {N' N N'' : Type*} [AddCommGroup N'] [Module R N'] [AddCommGroup N]
    [Module R N] [AddCommGroup N''] [Module R N''] [Module.Finite R N] {f : N' →ₗ[R] N}
    {g : N →ₗ[R] N''} (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    min (depth R I N') (depth R I N'') ≤ depth R I N ∧
      min (depth R I N) (depth R I N' - 1) ≤ depth R I N'' ∧
      min (depth R I N) (depth R I N'' + 1) ≤ depth R I N' :=
  Stacks.Depth.ShortExactInequalities.solution I h hf hg

end Module
