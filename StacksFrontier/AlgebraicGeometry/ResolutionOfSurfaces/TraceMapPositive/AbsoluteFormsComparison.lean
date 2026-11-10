module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsNaturality
public import StacksFrontier.RingTheory.FormsTrace.Defs
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.DeRhamTraceComparison
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# Absolute and relative differential forms

For a ring `Λ` and a `Λ`-algebra `A` the canonical surjection `Ω_{A/ℤ} → Ω_{A/Λ}` induces maps
`Ω^n_{A/ℤ} → Ω^n_{A/Λ}` on exterior powers, `KaehlerDifferential.absoluteToRelative`.  They are
surjective, multiplicative for the wedge product, compatible with the pull-back of forms along a
tower `Λ → R → S`, and commute with the de Rham differentials.  Their kernel in degree `n + 1` is
spanned by the wedges `dλ ∧ η` with `λ ∈ Λ`.

This is the input for property (3) of Stacks, Proposition 0FLC: a family of maps
`Θ^n : Ω^n_{S/ℤ} → Ω^n_{R/ℤ}` that is linear over the forms of `R` kills those wedges modulo the
forms `dλ` of `R`, and so descends to maps `Ω^n_{S/Λ} → Ω^n_{R/Λ}`,
`KaehlerDifferential.relativeTrace`.

## Main definitions

* `KaehlerDifferential.absoluteToRelative`: the map `Ω^n_{A/ℤ} → Ω^n_{A/Λ}`.
* `KaehlerDifferential.relativeTrace`: the maps `Ω^n_{S/Λ} → Ω^n_{R/Λ}` induced by a family
  `Θ^n : Ω^n_{S/ℤ} → Ω^n_{R/ℤ}` which is linear over the forms of `R`
  (`Stacks.FormsTrace.IsWedgeLinear`), and `KaehlerDifferential.relativeTraceComplex`, the map of
  de Rham complexes they form when `Θ` commutes with `d` (`Stacks.FormsTrace.CommutesWithD`).

## Main results

* `KaehlerDifferential.absoluteToRelative_surjective`,
  `KaehlerDifferential.absoluteToRelative_wedgeMul`,
  `KaehlerDifferential.absoluteToRelative_formsMap` and
  `KaehlerDifferential.absoluteToRelative_deRhamDifferential`: the comparison maps are surjective
  and compatible with wedge, pull-back and `d`.
* `KaehlerDifferential.ker_absoluteToRelative_le`: their kernel.
* `KaehlerDifferential.relativeTrace_absoluteToRelative`: the defining property of the descended
  maps, `Θ_Λ ∘ (Ω_{S/ℤ} → Ω_{S/Λ}) = (Ω_{R/ℤ} → Ω_{R/Λ}) ∘ Θ`.
* `KaehlerDifferential.universalRoot_eq_D` and `KaehlerDifferential.eq_D_of_universal`: the value
  `Θ(x ^ (d - 1) dx) = da` of Example 0FLD, in the universal case `ℤ[T][x]/(x ^ d - T)` and over
  any ring by base change.
* `KaehlerDifferential.relativeTraceComplex_eq_higherTraceComplexMap`: **`Tr = Θ_{S/R}`**
  (Remark 0FLF) for the relative trace induced by any family satisfying the conditions of
  `StacksFrontier.RingTheory.FormsTrace.Defs` and Example 0FLD, and
  `KaehlerDifferential.relativeTraceComplex_eq_higherTraceComplexMap_of_baseChange`, the same
  with Example 0FLD obtained from a family on a `p`-torsion-free base (such as `ℤ[T]`, see
  `KaehlerDifferential.mvPolynomial_kaehler_eq_zero_of_natCast_smul`) by base change.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FLF](https://stacks.math.columbia.edu/tag/0FLF)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace KaehlerDifferential

universe u

section Comparison

variable (Λ A : Type*) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- **The comparison map `Ω^n_{A/ℤ} → Ω^n_{A/Λ}`**: the `n`-th exterior power of the canonical
surjection of the absolute differentials onto the differentials relative to `Λ`. -/
def absoluteToRelative (n : ℕ) : ⋀[A]^n Ω[A⁄ℤ] →ₗ[A] ⋀[A]^n Ω[A⁄Λ] :=
  exteriorPower.map n (KaehlerDifferential.map ℤ Λ A A)

/-- The comparison map sends a wedge `v₁ ∧ ⋯ ∧ vₙ` of absolute differentials to the wedge of their
images in `Ω_{A/Λ}`. -/
@[simp]
theorem absoluteToRelative_ιMulti (n : ℕ) (v : Fin n → Ω[A⁄ℤ]) :
    absoluteToRelative Λ A n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti A n fun i => KaehlerDifferential.map ℤ Λ A A (v i) :=
  exteriorPower.map_apply_ιMulti _ _

/-- The comparison map sends `d_ℤ b₁ ∧ ⋯ ∧ d_ℤ bₙ` to `d_Λ b₁ ∧ ⋯ ∧ d_Λ bₙ`. -/
theorem absoluteToRelative_ιMulti_D (n : ℕ) (b : Fin n → A) :
    absoluteToRelative Λ A n (exteriorPower.ιMulti A n fun i => D ℤ A (b i)) =
      exteriorPower.ιMulti A n fun i => D Λ A (b i) := by
  rw [absoluteToRelative_ιMulti]
  simp only [map_D, Algebra.algebraMap_self, RingHom.id_apply]

/-- The comparison map `Ω^n_{A/ℤ} → Ω^n_{A/Λ}` is surjective. -/
theorem absoluteToRelative_surjective (n : ℕ) :
    Function.Surjective (absoluteToRelative Λ A n) :=
  exteriorPower.map_surjective (KaehlerDifferential.map_surjective ℤ Λ A)

/-- The comparison maps are multiplicative for the wedge product. -/
theorem absoluteToRelative_wedgeMul (i j : ℕ) (α : ⋀[A]^i Ω[A⁄ℤ]) (β : ⋀[A]^j Ω[A⁄ℤ]) :
    absoluteToRelative Λ A (i + j) (exteriorPower.wedgeMul i j α β) =
      exteriorPower.wedgeMul i j (absoluteToRelative Λ A i α) (absoluteToRelative Λ A j β) :=
  exteriorPower.wedgeMul_map i j _ α β

/-- In degree zero the comparison map is the identity of `A`. -/
theorem zeroEquiv_absoluteToRelative (ω : ⋀[A]^0 Ω[A⁄ℤ]) :
    exteriorPower.zeroEquiv A (Ω[A⁄Λ]) (absoluteToRelative Λ A 0 ω) =
      exteriorPower.zeroEquiv A (Ω[A⁄ℤ]) ω :=
  LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality _) ω

/-- **The comparison maps commute with the de Rham differentials.**  Both composites send
`b₀ · (db₁ ∧ ⋯ ∧ db_n)` to `db₀ ∧ ⋯ ∧ db_n`, and those elements span `Ω^n_{A/ℤ}` over `ℤ`. -/
theorem absoluteToRelative_deRhamDifferential (n : ℕ) (η : ⋀[A]^n Ω[A⁄ℤ]) :
    absoluteToRelative Λ A (n + 1) (deRhamDifferential (A := ℤ) n η) =
      deRhamDifferential (A := Λ) n (absoluteToRelative Λ A n η) := by
  have key : ((absoluteToRelative Λ A (n + 1)).restrictScalars ℤ) ∘ₗ
      deRhamDifferential (A := ℤ) (B := A) n =
      (deRhamDifferential (A := Λ) (B := A) n).restrictScalars ℤ ∘ₗ
        ((absoluteToRelative Λ A n).restrictScalars ℤ) := by
    refine LinearMap.ext_on (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (D ℤ A)
      (span_range_derivation ℤ A) n) ?_
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    rw [deRhamDifferential_smul_ιMulti_D n b, absoluteToRelative_ιMulti_D, map_smul,
      absoluteToRelative_ιMulti_D, deRhamDifferential_smul_ιMulti_D n b]
  exact LinearMap.congr_fun key η

end Comparison

section Kernel

/-- The kernel of `Ω_{B/A₀} → Ω_{B/A}` for a tower `A₀ → A → B` is generated over `B` by the
differentials of the elements of `A`. -/
theorem ker_map_le_span_D_algebraMap (A₀ A B : Type*) [CommRing A₀] [CommRing A] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B] [Algebra A B] [IsScalarTower A₀ A B] :
    LinearMap.ker (KaehlerDifferential.map A₀ A B B) ≤
      Submodule.span B (Set.range fun a : A => D A₀ B (algebraMap A B a)) := by
  rw [← KaehlerDifferential.range_mapBaseChange]
  rintro w ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul b a =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    apply Submodule.smul_mem
    have ha : a ∈ Submodule.span A (Set.range (D A₀ A)) := by
      rw [span_range_derivation]
      trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, rfl⟩ := ha
      rw [map_D]
      exact Submodule.subset_span (Set.mem_range_self a)
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      simpa only [map_smul, algebraMap_smul] using Submodule.smul_mem _ (algebraMap A B r) hx

/-- The kernel of `⋀^{n+1}` of a surjection `q` is spanned by the wedges whose first factor lies
in the kernel of `q`. -/
theorem ker_exteriorPower_map_le_span {K M N : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (q : M →ₗ[K] N) (hq : Function.Surjective q) (n : ℕ) :
    LinearMap.ker (exteriorPower.map (n + 1) q) ≤
      Submodule.span K {z | ∃ (a : M) (s : Fin n → M),
        q a = 0 ∧ z = exteriorPower.ιMulti K (n + 1) (Fin.cons a s)} := by
  intro z hz
  obtain ⟨t, rfl⟩ := exterior_ker_le_im_beta q.ker.subtype q hq
    (Submodule.range_subtype _).symm.le n hz
  clear hz
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | tmul a b =>
    have hb : b ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K n)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨a, s, a.property, ?_⟩
      apply Subtype.ext
      simp only [ExtPow.beta_tmul, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
      rfl
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      simpa only [TensorProduct.tmul_smul, map_smul] using Submodule.smul_mem _ r hx

/-- A wedge with a degree-one element in front, read in degree `n + 1`. -/
theorem degCongr_wedgeMul_one {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (n : ℕ) (m : M) (s : Fin n → M) :
    exteriorPower.degCongr (Nat.add_comm 1 n)
        (exteriorPower.wedgeMul 1 n (exteriorPower.ιMulti K 1 fun _ => m)
          (exteriorPower.ιMulti K n s)) =
      exteriorPower.ιMulti K (n + 1) (Fin.cons m s) :=
  Subtype.ext (by
    simp only [exteriorPower.coe_degCongr, exteriorPower.wedgeMul_apply_coe,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl)

variable (Λ A : Type*) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- **The kernel of `Ω^{n+1}_{A/ℤ} → Ω^{n+1}_{A/Λ}`** is spanned over `A` by the wedges
`dλ ∧ η`, `λ ∈ Λ`, `η ∈ Ω^n_{A/ℤ}`. -/
theorem ker_absoluteToRelative_le (n : ℕ) :
    LinearMap.ker (absoluteToRelative Λ A (n + 1)) ≤
      Submodule.span A (Set.range fun lη : Λ × ⋀[A]^n Ω[A⁄ℤ] =>
        exteriorPower.degCongr (Nat.add_comm 1 n)
          (exteriorPower.wedgeMul 1 n
            (exteriorPower.ιMulti A 1 fun _ => D ℤ A (algebraMap Λ A lη.1)) lη.2)) := by
  set G := Submodule.span A (Set.range fun lη : Λ × ⋀[A]^n Ω[A⁄ℤ] =>
    exteriorPower.degCongr (Nat.add_comm 1 n)
      (exteriorPower.wedgeMul 1 n
        (exteriorPower.ιMulti A 1 fun _ => D ℤ A (algebraMap Λ A lη.1)) lη.2)) with hG
  refine (ker_exteriorPower_map_le_span _ (KaehlerDifferential.map_surjective ℤ Λ A) n).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨a, s, ha, rfl⟩
  have ha' := ker_map_le_span_D_algebraMap ℤ Λ A ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      rw [← degCongr_wedgeMul_one]
      exact Submodule.subset_span ⟨(l, exteriorPower.ιMulti A n s), rfl⟩
  | zero =>
      rw [(exteriorPower.ιMulti A (n + 1)).map_coord_zero 0 (Fin.cons_zero _ _)]
      exact G.zero_mem
  | add x y _ _ hx hy =>
      have h : exteriorPower.ιMulti A (n + 1) (Fin.cons (x + y) s) =
          exteriorPower.ιMulti A (n + 1) (Fin.cons x s) +
            exteriorPower.ιMulti A (n + 1) (Fin.cons y s) :=
        (exteriorPower.ιMulti A (n + 1)).toMultilinearMap.cons_add s x y
      rw [h]
      exact G.add_mem hx hy
  | smul c x _ hx =>
      have h : exteriorPower.ιMulti A (n + 1) (Fin.cons (c • x) s) =
          c • exteriorPower.ιMulti A (n + 1) (Fin.cons x s) :=
        (exteriorPower.ιMulti A (n + 1)).toMultilinearMap.cons_smul s c x
      rw [h]
      exact G.smul_mem c hx

end Kernel

section PullBack

variable (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S] [Algebra Λ R] [Algebra Λ S]
  [Algebra R S] [IsScalarTower Λ R S]

/-- Changing the base from `ℤ` to `Λ` commutes with the pull-back of differentials along
`R → S`. -/
theorem map_map_int_eq (w : Ω[R⁄ℤ]) :
    KaehlerDifferential.map ℤ Λ S S (KaehlerDifferential.map ℤ ℤ R S w) =
      KaehlerDifferential.map Λ Λ R S (KaehlerDifferential.map ℤ Λ R R w) := by
  refine LinearMap.congr_fun (LinearMap.ext_on_range (R := R) (v := D ℤ R)
    (f := (KaehlerDifferential.map ℤ Λ S S).restrictScalars R ∘ₗ KaehlerDifferential.map ℤ ℤ R S)
    (g := KaehlerDifferential.map Λ Λ R S ∘ₗ KaehlerDifferential.map ℤ Λ R R)
    (span_range_derivation ℤ R) fun r => ?_) w
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_D, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- **The comparison maps are compatible with the pull-back of forms** along `R → S`: absolute
forms are pulled back by `⋀^n` of `Ω_{R/ℤ} → Ω_{S/ℤ}` and relative forms by
`KaehlerDifferential.mapExteriorPower`. -/
theorem absoluteToRelative_formsMap (n : ℕ) (ω : ⋀[R]^n Ω[R⁄ℤ]) :
    absoluteToRelative Λ S n (ExteriorAlgebra.powMapₛₗ n (algebraMap R S)
        (Stacks.DeRham.kaehlerMapₛₗ R S) ω) =
      mapExteriorPower Λ R S n (absoluteToRelative Λ R n ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨v, rfl⟩ := hv
      rw [ExteriorAlgebra.powMapₛₗ_ιMulti, absoluteToRelative_ιMulti, absoluteToRelative_ιMulti,
        mapExteriorPower_ιMulti]
      congr 1
      funext i
      exact map_map_int_eq Λ R S (v i)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
      rw [LinearMap.map_smulₛₗ, map_smul, hx, map_smul, map_smul, algebraMap_smul]

end PullBack

/-- A family of maps between exterior powers commutes with reindexing along an equality of
degrees. -/
theorem family_degCongr {K K' M N : Type*} [CommRing K] [CommRing K'] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K' N]
    (F : (n : ℕ) → ⋀[K]^n M → ⋀[K']^n N) {m n : ℕ} (h : m = n) (y : ⋀[K]^m M) :
    F n (exteriorPower.degCongr h y) = exteriorPower.degCongr h (F m y) := by
  subst h
  rfl

section Descent

variable {Λ R S : Type u} [CommRing Λ] [CommRing R] [CommRing S] [Algebra Λ R] [Algebra Λ S]
  [Algebra R S] [IsScalarTower Λ R S]

variable (Λ) in
/-- **A family linear over the forms of `R` kills the kernel of `Ω^n_{S/ℤ} → Ω^n_{S/Λ}` modulo
the kernel of `Ω^n_{R/ℤ} → Ω^n_{R/Λ}`**: `Θ(dλ ∧ η) = dλ ∧ Θ(η)`, and `dλ` vanishes in
`Ω_{R/Λ}`. -/
theorem ker_absoluteToRelative_le_ker_comp
    (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ]) (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (n : ℕ) :
    LinearMap.ker ((absoluteToRelative Λ S n).restrictScalars R) ≤
      LinearMap.ker (absoluteToRelative Λ R n ∘ₗ Θ n) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply] at hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  cases n with
  | zero =>
      have hx0 : x = 0 := by
        have h := zeroEquiv_absoluteToRelative Λ S x
        rw [hx, map_zero] at h
        exact (exteriorPower.zeroEquiv S (Ω[S⁄ℤ])).injective (h.symm.trans (map_zero _).symm)
      rw [hx0, map_zero, map_zero]
  | succ k =>
  have hmem := ker_absoluteToRelative_le Λ S k hx
  -- the generators, multiplied by any scalar of `S`, are killed
  have hgen : ∀ (l : Λ) (η : ⋀[S]^k Ω[S⁄ℤ]),
      absoluteToRelative Λ R (k + 1) (Θ (k + 1) (exteriorPower.degCongr (Nat.add_comm 1 k)
        (exteriorPower.wedgeMul 1 k
          (exteriorPower.ιMulti S 1 fun _ => D ℤ S (algebraMap Λ S l)) η))) = 0 := by
    intro l η
    have hpull : (exteriorPower.ιMulti S 1 fun _ => D ℤ S (algebraMap Λ S l)) =
        ExteriorAlgebra.powMapₛₗ 1 (algebraMap R S) (Stacks.DeRham.kaehlerMapₛₗ R S)
          (exteriorPower.ιMulti R 1 fun _ => D ℤ R (algebraMap Λ R l)) := by
      rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
      congr 1
      funext _
      change _ = KaehlerDifferential.map ℤ ℤ R S _
      rw [map_D, ← IsScalarTower.algebraMap_apply]
    rw [family_degCongr (fun n => ⇑(Θ n)), hpull, hΘ 1 k,
      family_degCongr (fun n => ⇑(absoluteToRelative Λ R n)), absoluteToRelative_wedgeMul,
      absoluteToRelative_ιMulti_D]
    have hz : (exteriorPower.ιMulti R 1 fun _ => D Λ R (algebraMap Λ R l)) = 0 := by
      rw [Derivation.map_algebraMap]
      exact (exteriorPower.ιMulti R 1).map_coord_zero 0 rfl
    rw [hz, LinearMap.map_zero₂, LinearEquiv.map_zero]
  suffices h : ∀ c : S, absoluteToRelative Λ R (k + 1) (Θ (k + 1) (c • x)) = 0 by
    simpa only [one_smul] using h 1
  clear hx
  induction hmem using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨l, η⟩, rfl⟩ := hv
      intro c
      rw [← LinearEquiv.map_smul, ← LinearMap.map_smul]
      exact hgen l (c • η)
  | zero => intro c; rw [smul_zero, map_zero, map_zero]
  | add v w _ _ hv hw => intro c; rw [smul_add, map_add, map_add, hv c, hw c, add_zero]
  | smul a v _ hv => intro c; rw [smul_smul]; exact hv (c * a)

variable (Λ) in
/-- **The trace on relative forms** `Ω^n_{S/Λ} → Ω^n_{R/Λ}` induced by a family
`Θ^n : Ω^n_{S/ℤ} → Ω^n_{R/ℤ}` which is linear over the forms of `R`: the unique map with
`relativeTrace (ω mod Λ) = Θ(ω) mod Λ`.  This is the passage from (2) to (3) in Stacks,
Proposition 0FLC. -/
def relativeTrace (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ) (n : ℕ) : ⋀[S]^n Ω[S⁄Λ] →ₗ[R] ⋀[R]^n Ω[R⁄Λ] :=
  ((LinearMap.ker ((absoluteToRelative Λ S n).restrictScalars R)).liftQ
      (absoluteToRelative Λ R n ∘ₗ Θ n) (ker_absoluteToRelative_le_ker_comp Λ Θ hΘ n)).comp
    (LinearMap.quotKerEquivOfSurjective ((absoluteToRelative Λ S n).restrictScalars R)
      (absoluteToRelative_surjective Λ S n)).symm.toLinearMap

variable (Λ) in
/-- **The defining property of the trace on relative forms**: it is induced by `Θ`. -/
theorem relativeTrace_absoluteToRelative (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ) (n : ℕ) (x : ⋀[S]^n Ω[S⁄ℤ]) :
    relativeTrace Λ Θ hΘ n (absoluteToRelative Λ S n x) =
      absoluteToRelative Λ R n (Θ n x) := by
  unfold relativeTrace
  rw [LinearMap.comp_apply]
  rw [show absoluteToRelative Λ S n x = LinearMap.quotKerEquivOfSurjective
      ((absoluteToRelative Λ S n).restrictScalars R) (absoluteToRelative_surjective Λ S n)
        (Submodule.Quotient.mk x) from rfl]
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply]

variable (Λ) in
/-- The trace on relative forms is the only map with the defining property. -/
theorem eq_relativeTrace (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ) (n : ℕ) (θ : ⋀[S]^n Ω[S⁄Λ] →ₗ[R] ⋀[R]^n Ω[R⁄Λ])
    (hθ : ∀ x, θ (absoluteToRelative Λ S n x) = absoluteToRelative Λ R n (Θ n x)) :
    θ = relativeTrace Λ Θ hΘ n := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := absoluteToRelative_surjective Λ S n y
  rw [hθ, relativeTrace_absoluteToRelative]

variable (Λ) in
/-- **The trace on relative forms is linear over the relative forms of `R`**:
`Θ(α ∧ β) = α ∧ Θ(β)` for `α ∈ Ω^i_{R/Λ}` and `β ∈ Ω^j_{S/Λ}`. -/
theorem relativeTrace_wedgeMul (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ) (i j : ℕ) (α : ⋀[R]^i Ω[R⁄Λ]) (β : ⋀[S]^j Ω[S⁄Λ]) :
    relativeTrace Λ Θ hΘ (i + j)
        (exteriorPower.wedgeMul i j (mapExteriorPower Λ R S i α) β) =
      exteriorPower.wedgeMul i j α (relativeTrace Λ Θ hΘ j β) := by
  obtain ⟨α', rfl⟩ := absoluteToRelative_surjective Λ R i α
  obtain ⟨β', rfl⟩ := absoluteToRelative_surjective Λ S j β
  rw [← absoluteToRelative_formsMap, ← absoluteToRelative_wedgeMul,
    relativeTrace_absoluteToRelative, hΘ, absoluteToRelative_wedgeMul,
    relativeTrace_absoluteToRelative]

variable (Λ) in
/-- **The trace on relative forms commutes with the de Rham differentials**, when `Θ` does. -/
theorem relativeTrace_deRhamDifferential
    (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ]) (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (hd : Stacks.FormsTrace.CommutesWithD R S Θ)
    (n : ℕ) (β : ⋀[S]^n Ω[S⁄Λ]) :
    relativeTrace Λ Θ hΘ (n + 1) (deRhamDifferential (A := Λ) n β) =
      deRhamDifferential (A := Λ) n (relativeTrace Λ Θ hΘ n β) := by
  obtain ⟨β', rfl⟩ := absoluteToRelative_surjective Λ S n β
  rw [← absoluteToRelative_deRhamDifferential, relativeTrace_absoluteToRelative, hd,
    absoluteToRelative_deRhamDifferential, relativeTrace_absoluteToRelative]

variable (Λ) in
/-- In degree zero the trace on relative forms is `Θ⁰`. -/
theorem zeroEquiv_relativeTrace_zero (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ) (s : S) :
    exteriorPower.zeroEquiv R (Ω[R⁄Λ])
        (relativeTrace Λ Θ hΘ 0 ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) =
      exteriorPower.zeroEquiv R (Ω[R⁄ℤ])
        (Θ 0 ((exteriorPower.zeroEquiv S (Ω[S⁄ℤ])).symm s)) := by
  have hs : (exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s =
      absoluteToRelative Λ S 0 ((exteriorPower.zeroEquiv S (Ω[S⁄ℤ])).symm s) := by
    apply (exteriorPower.zeroEquiv S (Ω[S⁄Λ])).injective
    rw [zeroEquiv_absoluteToRelative, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [hs, relativeTrace_absoluteToRelative, zeroEquiv_absoluteToRelative]

variable (Λ) in
/-- **The trace on relative forms as a map of de Rham complexes**
`Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}`, for a family `Θ` linear over the forms of `R` and commuting with the
absolute de Rham differentials (Stacks, Proposition 0FLC (3)). -/
def relativeTraceComplex (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (hd : Stacks.FormsTrace.CommutesWithD R S Θ) :
    deRhamComplex Λ S ⟶ deRhamComplex Λ R :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom ((relativeTrace Λ Θ hΘ n).restrictScalars Λ))
    fun n => by
      ext β
      simp only [deRhamComplex_d]
      exact (relativeTrace_deRhamDifferential Λ Θ hΘ hd n β).symm

/-- In degree `n`, the trace map of de Rham complexes is the relative trace on `n`-forms. -/
@[simp]
theorem relativeTraceComplex_f (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (hd : Stacks.FormsTrace.CommutesWithD R S Θ)
    (n : ℕ) :
    (relativeTraceComplex Λ Θ hΘ hd).f n =
      ModuleCat.ofHom ((relativeTrace Λ Θ hΘ n).restrictScalars Λ) := rfl

end Descent

section Universal

open Polynomial

/-- **The value of Example 0FLD is compatible with base change.**  Let `A₀ → B₀` and `A → B` be
ring maps, with maps `A₀ → A` and `B₀ → B`, and let `θ₀ : Ω_{B₀/ℤ} → Ω_{A₀/ℤ}` and
`θ : Ω_{B/ℤ} → Ω_{A/ℤ}` be compatible with the pull-backs of differentials.  If `θ₀` sends
`x₀ ^ (d - 1) dx₀` to `da₀`, then `θ` sends `x ^ (d - 1) dx` to `da` for the images `x` of `x₀`
and `a` of `a₀`. -/
theorem eq_D_of_baseChange {A₀ B₀ A B : Type*} [CommRing A₀] [CommRing B₀] [CommRing A]
    [CommRing B] [Algebra A₀ A] [Algebra B₀ B] (θ₀ : Ω[B₀⁄ℤ] → Ω[A₀⁄ℤ]) (θ : Ω[B⁄ℤ] → Ω[A⁄ℤ])
    (hθ : ∀ ω, θ (KaehlerDifferential.map ℤ ℤ B₀ B ω) =
      KaehlerDifferential.map ℤ ℤ A₀ A (θ₀ ω))
    (d : ℕ) (x₀ : B₀) (a₀ : A₀) (h₀ : θ₀ (x₀ ^ (d - 1) • D ℤ B₀ x₀) = D ℤ A₀ a₀) :
    θ (algebraMap B₀ B x₀ ^ (d - 1) • D ℤ B (algebraMap B₀ B x₀)) =
      D ℤ A (algebraMap A₀ A a₀) := by
  have h : algebraMap B₀ B x₀ ^ (d - 1) • D ℤ B (algebraMap B₀ B x₀) =
      KaehlerDifferential.map ℤ ℤ B₀ B (x₀ ^ (d - 1) • D ℤ B₀ x₀) := by
    rw [map_smul, map_D, ← algebraMap_smul B (x₀ ^ (d - 1)), map_pow]
  rw [h, hθ, h₀, map_D]

/-- The base of the universal `d`-th root, `ℤ[T]`, in universe `u`: the polynomial ring over `ℤ`
in one variable indexed by `PUnit`. -/
abbrev UniversalBase : Type u := MvPolynomial PUnit.{u + 1} ℤ

/-- The variable `T` of `UniversalBase`. -/
abbrev universalVar : UniversalBase.{u} := MvPolynomial.X PUnit.unit

/-- **The universal `d`-th root**: `ℤ[T][x]/(x ^ d - T)` over `ℤ[T]`, in universe `u`. -/
abbrev UniversalRoot (d : ℕ) : Type u := AdjoinRoot (X ^ d - C universalVar.{u})

/-- The absolute differentials of a polynomial ring over `ℤ` are torsion free: `Ω_{ℤ[σ]/ℤ}` is
free over the domain `ℤ[σ]`. -/
theorem mvPolynomial_kaehler_eq_zero_of_natCast_smul {σ : Type*} {d : ℕ} (hd : 0 < d)
    (ω : Ω[MvPolynomial σ ℤ⁄ℤ]) (h : ((d : MvPolynomial σ ℤ)) • ω = 0) : ω = 0 := by
  have hd' : (d : MvPolynomial σ ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  apply (KaehlerDifferential.mvPolynomialBasis ℤ σ).repr.injective
  refine Finsupp.ext fun i => ?_
  have h' := congrArg (fun w => (KaehlerDifferential.mvPolynomialBasis ℤ σ).repr w i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
    Pi.zero_apply] at h'
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.mp h').resolve_left hd'

/-- **Example 0FLD in the universal case.**  Over `ℤ[T]` with `x ^ d = T`, any map
`θ : Ω_{ℤ[T][x]/(x^d - T)} → Ω_{ℤ[T]}` (absolute differentials) satisfying the projection
formula `θ(b · ω) = Trace(b) · ω` sends `x ^ (d - 1) dx` to `dT`: the absolute differentials of
`ℤ[T]` are free, so torsion free, and `d · x ^ (d - 1) dx = d(x ^ d) = dT` goes to
`Trace(1) · dT = d · dT`.

[Stacks, Tag 0FLD] (not registered here: this is not the whole statement of the tag): the value
Θ(x ^ (d - 1) dx) = dT for the universal extension ℤ[T][x]/(x ^ d - T), from the projection
formula alone
-/
theorem universalRoot_eq_D {d : ℕ} (hd : 0 < d)
    (θ : Ω[UniversalRoot.{u} d⁄ℤ] →ₗ[UniversalBase.{u}] Ω[UniversalBase.{u}⁄ℤ])
    (hθ : ∀ (b : UniversalRoot.{u} d) (ω : Ω[UniversalBase.{u}⁄ℤ]),
      θ (b • KaehlerDifferential.map ℤ ℤ UniversalBase.{u} (UniversalRoot.{u} d) ω) =
        Algebra.trace UniversalBase.{u} (UniversalRoot.{u} d) b • ω) :
    θ (AdjoinRoot.root (X ^ d - C universalVar.{u}) ^ (d - 1) •
        D ℤ (UniversalRoot.{u} d) (AdjoinRoot.root (X ^ d - C universalVar.{u}))) =
      D ℤ UniversalBase.{u} universalVar.{u} :=
  eq_D_of_smul_map_eq_trace_smul hd universalVar (AlgEquiv.refl) θ hθ
    (mvPolynomial_kaehler_eq_zero_of_natCast_smul hd)

/-- The map `ℤ[T] → R`, `T ↦ a`. -/
abbrev universalBaseMap {R : Type*} [CommRing R] (a : R) : UniversalBase.{u} →+* R :=
  (MvPolynomial.aeval fun _ => a).toRingHom

/-- The map `ℤ[T] → R`, `T ↦ a`, sends `T` to `a`. -/
theorem universalBaseMap_var {R : Type*} [CommRing R] (a : R) :
    universalBaseMap.{u} a universalVar = a :=
  MvPolynomial.aeval_X _ _

/-- The map `ℤ[T][x]/(x ^ d - T) → R[x]/(x ^ d - a) ≅ S`, `T ↦ a`, `x ↦ x`. -/
noncomputable def universalRootMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {d : ℕ}
    (a : R) (e : AdjoinRoot (X ^ d - C a) ≃ₐ[R] S) : UniversalRoot.{u} d →+* S :=
  AdjoinRoot.lift ((algebraMap R S).comp (universalBaseMap.{u} a))
    (e (AdjoinRoot.root (X ^ d - C a))) (by
      have h := AdjoinRoot.eval₂_root (X ^ d - C a)
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        sub_eq_zero] at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        sub_eq_zero, RingHom.comp_apply, universalBaseMap_var, ← map_pow, h,
        ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes])

/-- The map `ℤ[T][x]/(x ^ d - T) → S` sends the root `x` to the image under `e` of the root of
`x ^ d - a`. -/
theorem universalRootMap_root {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {d : ℕ}
    (a : R) (e : AdjoinRoot (X ^ d - C a) ≃ₐ[R] S) :
    universalRootMap.{u} a e (AdjoinRoot.root (X ^ d - C universalVar.{u})) =
      e (AdjoinRoot.root (X ^ d - C a)) :=
  AdjoinRoot.lift_root _

/-- **Example 0FLD for `x ^ d - a` over any ring, by base change from the universal case.**
Let `S ≅ R[x]/(x ^ d - a)`, and let `θ : Ω_{S/ℤ} → Ω_{R/ℤ}` be compatible, along
`ℤ[T] → R` and `ℤ[T][x]/(x ^ d - T) → S`, with a map `θ₀` for the universal extension satisfying
the projection formula.  Then `θ(x ^ (d - 1) dx) = da`.

[Stacks, Tag 0FLD] (not registered here: this is not the whole statement of the tag): Θ(x ^ (d -
1) dx) = da for R[x]/(x ^ d - a), by base change from the universal case
-/
theorem eq_D_of_universal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {d : ℕ}
    (hd : 0 < d) (a : R) (e : AdjoinRoot (X ^ d - C a) ≃ₐ[R] S)
    (θ₀ : Ω[UniversalRoot.{u} d⁄ℤ] →ₗ[UniversalBase.{u}] Ω[UniversalBase.{u}⁄ℤ])
    (hθ₀ : ∀ (b : UniversalRoot.{u} d) (ω : Ω[UniversalBase.{u}⁄ℤ]),
      θ₀ (b • KaehlerDifferential.map ℤ ℤ UniversalBase.{u} (UniversalRoot.{u} d) ω) =
        Algebra.trace UniversalBase.{u} (UniversalRoot.{u} d) b • ω)
    (θ : Ω[S⁄ℤ] → Ω[R⁄ℤ])
    (hθ : letI := (universalBaseMap.{u} a).toAlgebra
      letI := (universalRootMap.{u} a e).toAlgebra
      ∀ ω, θ (KaehlerDifferential.map ℤ ℤ (UniversalRoot.{u} d) S ω) =
        KaehlerDifferential.map ℤ ℤ UniversalBase.{u} R (θ₀ ω)) :
    θ (e (AdjoinRoot.root (X ^ d - C a)) ^ (d - 1) • D ℤ S (e (AdjoinRoot.root (X ^ d - C a)))) =
      D ℤ R a := by
  let := (universalBaseMap.{u} a).toAlgebra
  let := (universalRootMap.{u} a e).toAlgebra
  have h := eq_D_of_baseChange θ₀ θ hθ d _ _ (universalRoot_eq_D hd θ₀ hθ₀)
  have hx : algebraMap (UniversalRoot.{u} d) S (AdjoinRoot.root (X ^ d - C universalVar.{u})) =
      e (AdjoinRoot.root (X ^ d - C a)) := universalRootMap_root a e
  have ha : algebraMap UniversalBase.{u} R universalVar = a := universalBaseMap_var a
  rwa [hx, ha] at h

end Universal

section Identification

open Polynomial

variable {p : ℕ} {Λ R S : Type u} [CommRing Λ] [CommRing R] [CommRing S] [Algebra Λ R]
  [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

/-- A form of degree zero on `S`, written as a scalar multiple of the pull-back of the unit. -/
theorem zeroEquiv_symm_eq_smul_powMapₛₗ (s : S) :
    (exteriorPower.zeroEquiv S (Ω[S⁄ℤ])).symm s =
      s • ExteriorAlgebra.powMapₛₗ 0 (algebraMap R S) (Stacks.DeRham.kaehlerMapₛₗ R S)
        (exteriorPower.ιMulti R 0 fun i => i.elim0) := by
  apply (exteriorPower.zeroEquiv S (Ω[S⁄ℤ])).injective
  rw [LinearEquiv.apply_symm_apply, ExteriorAlgebra.powMapₛₗ_ιMulti, map_smul,
    exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

/-- **Tr = Θ_{S/R} (Stacks, Remark 0FLF), for the map of complexes induced by absolute traces.**
Let `𝐅_p ⊂ Λ ⊂ R ⊂ S` with `S ≅ R[x]/(x ^ p - a)`, and let `Θ^n : Ω^n_{S/ℤ} → Ω^n_{R/ℤ}` be a
family of maps of absolute differential forms which is compatible with the trace
(Stacks, Lemma 0FLB (1)), linear over the forms of `R` (Proposition 0FLC (2)), commutes with the
de Rham differentials, and sends `x ^ (p - 1) dx` to `da` (Example 0FLD).  Then the induced map
of relative de Rham complexes `Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}` (Proposition 0FLC (3)) is the map built
from the trace `Tr` of Lemma 0AX5. -/
theorem relativeTraceComplex_eq_higherTraceComplexMap (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) [Module.Finite R S] [Module.Projective R S]
    (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (htr : Stacks.FormsTrace.IsFormsTrace R S Θ)
    (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (hd : Stacks.FormsTrace.CommutesWithD R S Θ)
    (htop : Θ 1 (exteriorPower.ιMulti S 1 fun _ =>
        e (AdjoinRoot.root (X ^ p - C a)) ^ (p - 1) • D ℤ S (e (AdjoinRoot.root (X ^ p - C a)))) =
      exteriorPower.ιMulti R 1 fun _ => D ℤ R a) :
    relativeTraceComplex Λ Θ hΘ hd = higherTraceComplexMap hp a e := by
  set x := e (AdjoinRoot.root (X ^ p - C a)) with hx
  have : Module.Free R S :=
    Module.Free.of_basis ((AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne_zero)).map e).basis
  refine eq_higherTraceComplexMap hp a e _ (fun s => ?_) (fun i j α β => ?_) ?_
  · change exteriorPower.zeroEquiv R (Ω[R⁄Λ])
        (relativeTrace Λ Θ hΘ 0 ((exteriorPower.zeroEquiv S (Ω[S⁄Λ])).symm s)) = _
    rw [zeroEquiv_relativeTrace_zero, zeroEquiv_symm_eq_smul_powMapₛₗ (R := R), htr, map_smul,
      exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one, LinearMap.comp_apply,
      Stacks.Discriminant.finiteProjectiveTrace_eq_trace]
    rfl
  · exact relativeTrace_wedgeMul Λ Θ hΘ i j α β
  · change relativeTrace Λ Θ hΘ 1 _ = _
    have hlift : (exteriorPower.ιMulti S 1 fun _ => x ^ (p - 1) • D Λ S x) =
        absoluteToRelative Λ S 1 (exteriorPower.ιMulti S 1 fun _ => x ^ (p - 1) • D ℤ S x) := by
      rw [absoluteToRelative_ιMulti]
      simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hlift, relativeTrace_absoluteToRelative, htop]
    exact absoluteToRelative_ιMulti_D Λ R 1 fun _ => a

/-- In degree one the pull-back of forms is the map of differentials. -/
theorem formsMap_one_oneEquiv_symm {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (w : Ω[A⁄ℤ]) :
    Stacks.FormsTrace.formsMap A B 1 ((exteriorPower.oneEquiv A (Ω[A⁄ℤ])).symm w) =
      (exteriorPower.oneEquiv B (Ω[B⁄ℤ])).symm (KaehlerDifferential.map ℤ ℤ A B w) := by
  rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
    Stacks.FormsTrace.formsMap, ExteriorAlgebra.powMapₛₗ_ιMulti]
  rfl

/-- **Tr = Θ_{S/R} (Stacks, Remark 0FLF), with Example 0FLD supplied by base change.**  Let
`𝐅_p ⊂ Λ ⊂ R ⊂ S` with `S ≅ R[x]/(x ^ p - a)`, and let `Θ` be a family of maps of absolute forms
of `S/R` with property (1) of Lemma 0FLB and (2) of Proposition 0FLC, commuting with `d`.  Suppose
that in degree one `Θ` is the base change of a family `Θ₀` with property (1) for an extension
`B₀ ≅ A₀[x]/(x ^ p - a₀)` whose absolute differentials `Ω_{A₀/ℤ}` have no `p`-torsion (for
instance the universal one, `A₀ = ℤ[T]`, `a₀ = T`), along maps `A₀ → R`, `B₀ → S` sending
`a₀ ↦ a` and `x₀ ↦ x`.  Then the induced map of relative de Rham complexes
`Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}` is the map built from the trace `Tr` of Lemma 0AX5. -/
theorem relativeTraceComplex_eq_higherTraceComplexMap_of_baseChange (hp : p.Prime) [CharP Λ p]
    (a : R) (e : AdjoinRoot (X ^ p - C a) ≃ₐ[R] S) [Module.Finite R S] [Module.Projective R S]
    (Θ : (n : ℕ) → ⋀[S]^n Ω[S⁄ℤ] →ₗ[R] ⋀[R]^n Ω[R⁄ℤ])
    (htr : Stacks.FormsTrace.IsFormsTrace R S Θ) (hΘ : Stacks.FormsTrace.IsWedgeLinear R S Θ)
    (hd : Stacks.FormsTrace.CommutesWithD R S Θ)
    {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
    [Module.Projective A₀ B₀] (a₀ : A₀) (e₀ : AdjoinRoot (X ^ p - C a₀) ≃ₐ[A₀] B₀)
    (htors : ∀ ω : Ω[A₀⁄ℤ], (p : A₀) • ω = 0 → ω = 0)
    (Θ₀ : (n : ℕ) → ⋀[B₀]^n Ω[B₀⁄ℤ] →ₗ[A₀] ⋀[A₀]^n Ω[A₀⁄ℤ])
    (htr₀ : Stacks.FormsTrace.IsFormsTrace A₀ B₀ Θ₀) [Algebra A₀ R] [Algebra B₀ S]
    (ha : algebraMap A₀ R a₀ = a)
    (hx : algebraMap B₀ S (e₀ (AdjoinRoot.root (X ^ p - C a₀))) = e (AdjoinRoot.root (X ^ p - C a)))
    (hbc : ∀ η, Θ 1 (Stacks.FormsTrace.formsMap B₀ S 1 η) =
      Stacks.FormsTrace.formsMap A₀ R 1 (Θ₀ 1 η)) :
    relativeTraceComplex Λ Θ hΘ hd = higherTraceComplexMap hp a e := by
  have : Module.Free A₀ B₀ :=
    Module.Free.of_basis ((AdjoinRoot.powerBasis' (monic_X_pow_sub_C a₀ hp.ne_zero)).map e₀).basis
  let θ₀ : Ω[B₀⁄ℤ] →ₗ[A₀] Ω[A₀⁄ℤ] :=
    (exteriorPower.oneEquiv A₀ (Ω[A₀⁄ℤ])).toLinearMap ∘ₗ Θ₀ 1 ∘ₗ
      (exteriorPower.oneEquiv B₀ (Ω[B₀⁄ℤ])).symm.toLinearMap.restrictScalars A₀
  have hθ₀ : ∀ (b : B₀) (ω : Ω[A₀⁄ℤ]),
      θ₀ (b • KaehlerDifferential.map ℤ ℤ A₀ B₀ ω) = Algebra.trace A₀ B₀ b • ω := by
    intro b ω
    change exteriorPower.oneEquiv A₀ (Ω[A₀⁄ℤ])
      (Θ₀ 1 ((exteriorPower.oneEquiv B₀ (Ω[B₀⁄ℤ])).symm
        (b • KaehlerDifferential.map ℤ ℤ A₀ B₀ ω))) = _
    rw [map_smul, ← formsMap_one_oneEquiv_symm, htr₀ 1 b, map_smul, LinearEquiv.apply_symm_apply,
      Stacks.FormsTrace.trace, LinearMap.comp_apply,
      Stacks.Discriminant.finiteProjectiveTrace_eq_trace]
    rfl
  have hθ : ∀ w : Ω[B₀⁄ℤ],
      exteriorPower.oneEquiv R (Ω[R⁄ℤ]) (Θ 1 ((exteriorPower.oneEquiv S (Ω[S⁄ℤ])).symm
        (KaehlerDifferential.map ℤ ℤ B₀ S w))) = KaehlerDifferential.map ℤ ℤ A₀ R (θ₀ w) := by
    intro w
    rw [← formsMap_one_oneEquiv_symm, hbc, ← LinearEquiv.eq_symm_apply,
      ← formsMap_one_oneEquiv_symm]
    exact congrArg _ (LinearEquiv.symm_apply_apply _ _).symm
  have h₀ := eq_D_of_smul_map_eq_trace_smul (k := ℤ) hp.pos a₀ e₀ θ₀ hθ₀ htors
  have h := eq_D_of_baseChange θ₀ (fun w => exteriorPower.oneEquiv R (Ω[R⁄ℤ]) (Θ 1
    ((exteriorPower.oneEquiv S (Ω[S⁄ℤ])).symm w))) hθ p _ _ h₀
  rw [hx, ha] at h
  refine relativeTraceComplex_eq_higherTraceComplexMap hp a e Θ htr hΘ hd ?_
  rw [← exteriorPower.oneEquiv_symm_apply, ← exteriorPower.oneEquiv_symm_apply, ← h,
    LinearEquiv.symm_apply_apply]

end Identification

end KaehlerDifferential

end
