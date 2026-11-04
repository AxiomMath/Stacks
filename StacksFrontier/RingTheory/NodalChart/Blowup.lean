module

public import StacksFrontier.RingTheory.NodalChart.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Blowup.Defs

/-!
# Blowing up the standard nodal model in its singular point

Let `R` be a commutative ring, `π : R`, and `A = R[x, y]/(xy - πⁿ)` the standard nodal model.
Its singular point is cut out by `𝔪 = (π, x, y)`, and the blowup of `A` in `𝔪` is covered by
the three affine blowup algebras `A[𝔪/π]`, `A[𝔪/x]` and `A[𝔪/y]`. This file identifies all
three, for `n ≥ 2`:

* `A[𝔪/π] ≅ R[x', y']/(x'y' - π^(n-2))`, with `x ↦ πx'` and `y ↦ πy'`;
* `A[𝔪/x] ≅ R[x, u]/(xu - π)`, with `x ↦ x` and `y ↦ u·π^(n-1)`;
* `A[𝔪/y] ≅ R[y, v]/(yv - π)`, with `y ↦ y` and `x ↦ v·π^(n-1)`.

The first is the drop `n ↦ n - 2` in the exponent that drives the resolution of the singularity
by repeated blowups; the other two charts are already of the shape with exponent one.

## Main definitions

* `Stacks.nodalCenter` — the ideal `(π, x, y)` of `R[x, y]/(xy - h)`.

## Main results

* `Stacks.affineBlowupAlgebra_le_subalgebra` — the affine blowup algebra of an ideal
  `(a, bᵢ)` lies in any subalgebra containing the image of the base and the fractions `bᵢ/a`.
* `Stacks.nodalCentralChart_equiv` — the chart `A[𝔪/π]`, with the exponent drop `n ↦ n - 2`.
* `Stacks.nodalXChart_equiv`, `Stacks.nodalYChart_equiv` — the charts `A[𝔪/x]` and `A[𝔪/y]`.

## Implementation notes

The three identifications are produced by one mechanism. In each case there is a ring map `F`
from the claimed chart ring `T` into the localization `S` of `A` at the denominator, and a ring
map `G : A → T` going back, with `F ∘ G` the localization map `A → S`. Injectivity of `F` is
then obtained by composing with the lift of `G` to `S`, which turns `F` into the localization
map of `T` at one element; that map is injective because `T` is a domain. Surjectivity onto the
chart is `Stacks.affineBlowupAlgebra_le_subalgebra` together with the observation that each
fraction `g/a`, `g` a generator of `𝔪`, is in the image of `F`. For the chart at `x` the
fraction `y/x` equals `(π/x)²·π^(n-2)`, which is where `n ≥ 2` is used; the other two charts use
it through the exponent `n - 2` itself.

No hypothesis beyond `π ≠ 0` and unique factorization in `R` is needed: the source states the
example for a discrete valuation ring with uniformizer `π`, which satisfies both.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks

section General

variable {A B S : Type u} [CommRing A] [CommRing B] [CommRing S] [Algebra A S]

/-- A lift to a localization away from `a` is computed on the fraction `y/a` by multiplying
through by `a` and cancelling. -/
public theorem awayLift_mk'_eq {a : A} [IsLocalization.Away a S] {g : A →+* B}
    (hu : IsUnit (g a)) (y : A) (z : B) (hz : z * g a = g y) :
    IsLocalization.Away.lift a hu
      (IsLocalization.mk' S y ⟨a, Submonoid.mem_powers a⟩) = z := by
  have hspec : IsLocalization.mk' S y ⟨a, Submonoid.mem_powers a⟩ *
      algebraMap A S a = algebraMap A S y :=
    IsLocalization.mk'_spec S y (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
  have hmap := congrArg (IsLocalization.Away.lift a hu) hspec
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at hmap
  exact hu.mul_right_cancel (hmap.trans hz.symm)

/-- A ring map into a localization is injective as soon as some lift of a map back out of the
base turns it into an injective localization map. -/
public theorem injective_of_awayLift_comp {T S' : Type u} [CommRing T] [CommRing S']
    [Algebra T S'] {a : A} {t : T} [IsLocalization.Away a S] [IsLocalization.Away t S']
    [IsDomain T] (ht : t ≠ 0) (F : T →+* S) {g : A →+* S'} (hGa : IsUnit (g a))
    (hGF : ∀ u : T, IsLocalization.Away.lift a hGa (F u) = algebraMap T S' u) :
    Function.Injective F := fun x y hxy ↦
  IsLocalization.injective S' (powers_le_nonZeroDivisors_of_noZeroDivisors ht) <| by
    rw [← hGF x, ← hGF y, hxy]

variable {R : Type u} [CommRing R] [Algebra R S]

/-- The affine blowup algebra of `I = (a, bᵢ : i)` inside a localization of `A` away from `a`
is contained in every subalgebra of that localization which contains the image of `A` and the
fractions `bᵢ/a`. -/
public theorem affineBlowupAlgebra_le_subalgebra {ι : Type*} {b : ι → A} {I : Ideal A} {a : A}
    [IsLocalization.Away a S] (hI : I = Ideal.span (insert a (Set.range b)))
    (W : Subalgebra R S) (hA : ∀ x : A, algebraMap A S x ∈ W)
    (hb : ∀ i, IsLocalization.mk' S (b i) ⟨a, Submonoid.mem_powers a⟩ ∈ W) :
    ∀ z ∈ affineBlowupAlgebra I a S, z ∈ W := by
  have hfrac : ∀ x : A, IsLocalization.mk' S x ⟨a, Submonoid.mem_powers a⟩ =
      algebraMap A S x * IsLocalization.mk' S 1 ⟨a, Submonoid.mem_powers a⟩ :=
    fun x ↦ IsLocalization.mk'_eq_mul_mk'_one x _
  have hgen : ∀ y ∈ I, IsLocalization.mk' S y ⟨a, Submonoid.mem_powers a⟩ ∈ W := by
    intro y hy
    rw [hI] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_range] at hx
      obtain rfl | ⟨i, rfl⟩ := hx
      · rw [show IsLocalization.mk' S x ⟨x, Submonoid.mem_powers x⟩ = 1 from
          IsLocalization.mk'_self' (M := Submonoid.powers x) S
            (x := ⟨x, Submonoid.mem_powers x⟩)]
        exact W.one_mem
      · exact hb i
    | zero => rw [hfrac]; simp
    | add _ _ _ _ hx hy =>
      rw [hfrac] at hx hy ⊢
      rw [map_add, add_mul]
      exact W.add_mem hx hy
    | smul c _ _ hx =>
      rw [hfrac] at hx ⊢
      rw [smul_eq_mul, map_mul, mul_assoc]
      exact W.mul_mem (hA c) hx
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem _ hx => obtain ⟨y, hy, rfl⟩ := hx; exact hgen y hy
  | algebraMap r => exact hA r
  | add _ _ _ _ hx hy => exact W.add_mem hx hy
  | mul _ _ _ _ hx hy => exact W.mul_mem hx hy

variable (S) in
/-- An injective ring map into a localization whose image is exactly an affine blowup algebra
identifies that chart with the source. -/
public def affineBlowupChartEquiv {T : Type u} [CommRing T] {I : Ideal A} {a : A}
    [IsLocalization.Away a S] (F : T →+* S) (hinj : Function.Injective F)
    (hmem : ∀ u : T, F u ∈ affineBlowupAlgebra I a S)
    (hsurj : ∀ z ∈ affineBlowupAlgebra I a S, ∃ u : T, F u = z) :
    ↥(affineBlowupAlgebra I a S) ≃+* T :=
  (RingEquiv.ofBijective (F.codRestrict (affineBlowupAlgebra I a S) hmem)
    ⟨fun _ _ hxy ↦ hinj (congrArg Subtype.val hxy),
      fun z ↦ (hsurj z.1 z.2).imp fun _ hu ↦ Subtype.ext hu⟩).symm

public theorem affineBlowupChartEquiv_apply {T : Type u} [CommRing T] {I : Ideal A} {a : A}
    [IsLocalization.Away a S] (F : T →+* S) (hinj : Function.Injective F)
    (hmem : ∀ u : T, F u ∈ affineBlowupAlgebra I a S)
    (hsurj : ∀ z ∈ affineBlowupAlgebra I a S, ∃ u : T, F u = z)
    (z : ↥(affineBlowupAlgebra I a S)) (u : T) (h : F u = (z : S)) :
    affineBlowupChartEquiv S F hinj hmem hsurj z = u := by
  have hz : z = (affineBlowupChartEquiv S F hinj hmem hsurj).symm u := Subtype.ext h.symm
  rw [hz, RingEquiv.apply_symm_apply]

end General

/-- The center of the blowup resolving the standard nodal model: the ideal `(π, x, y)` of
`R[x, y]/(xy - h)`. -/
public def nodalCenter (R : Type u) [CommRing R] (π h : R) : Ideal (nodalChartRing R h) :=
  Ideal.span {algebraMap R (nodalChartRing R h) π, nodalGen R h 0, nodalGen R h 1}

section Center

variable {R : Type u} [CommRing R] (π h : R)

private theorem range_pair {B : Type u} (p q : B) : Set.range ![p, q] = {p, q} := by
  ext z
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]

public theorem algebraMap_mem_nodalCenter :
    algebraMap R (nodalChartRing R h) π ∈ nodalCenter R π h :=
  Ideal.subset_span (by simp)

public theorem nodalGen_mem_nodalCenter :
    ∀ i : Fin 2, nodalGen R h i ∈ nodalCenter R π h :=
  Fin.forall_fin_two.2 ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩

public theorem nodalCenter_eq_span_insert_algebraMap :
    nodalCenter R π h = Ideal.span (insert (algebraMap R (nodalChartRing R h) π)
      (Set.range ![nodalGen R h 0, nodalGen R h 1])) := by
  rw [nodalCenter, range_pair]

public theorem nodalCenter_eq_span_insert_gen_zero :
    nodalCenter R π h = Ideal.span (insert (nodalGen R h 0)
      (Set.range ![algebraMap R (nodalChartRing R h) π, nodalGen R h 1])) := by
  rw [nodalCenter, range_pair]
  exact congrArg Ideal.span (Set.insert_comm _ _ _)

public theorem nodalCenter_eq_span_insert_gen_one :
    nodalCenter R π h = Ideal.span (insert (nodalGen R h 1)
      (Set.range ![algebraMap R (nodalChartRing R h) π, nodalGen R h 0])) := by
  rw [nodalCenter, range_pair]
  refine congrArg Ideal.span ?_
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end Center

/-- The range of `nodalLift ![p, q]` lies in any subalgebra containing `p` and `q`. -/
private theorem nodalLift_pair_mem {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S] {h : R} {p q : S}
    {hpq : ![p, q] 0 * ![p, q] 1 = algebraMap R S h} {W : Subalgebra A S} (hp : p ∈ W)
    (hq : q ∈ W) (v : nodalChartRing R h) : nodalLift ![p, q] hpq v ∈ W := by
  have hsub : (nodalLift ![p, q] hpq).range ≤ Subalgebra.restrictScalars R W := by
    rw [range_nodalLift, Algebra.adjoin_le_iff, range_pair]
    exact Set.insert_subset hp (Set.singleton_subset_iff.2 hq)
  exact (Subalgebra.mem_restrictScalars R).1 (hsub ⟨v, rfl⟩)

/-- If `t = π/a` in the localization away from `a` and `b * a = πⁿ`, then `b = t·π^(n-1)`. -/
private theorem frac_mul_pow_eq {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S] {π : R} {n : ℕ} {a b : A}
    [IsLocalization.Away a S] {t : S} (ht : t * algebraMap A S a = algebraMap R S π)
    (hab : b * a = algebraMap R A (π ^ n)) (hn : 1 ≤ n) :
    t * algebraMap R S (π ^ (n - 1)) = algebraMap A S b := by
  have hpi : π * π ^ (n - 1) = π ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  refine (IsLocalization.Away.algebraMap_isUnit (S := S) a).mul_right_cancel ?_
  calc t * algebraMap R S (π ^ (n - 1)) * algebraMap A S a
      = t * algebraMap A S a * algebraMap R S (π ^ (n - 1)) := by ring
    _ = algebraMap R S (π ^ n) := by rw [ht, ← map_mul, hpi]
    _ = algebraMap A S b * algebraMap A S a := by
        rw [← map_mul, hab, ← IsScalarTower.algebraMap_apply]

/-- If `t = π/a` in the localization away from `a` and `b * a = πⁿ`, then `b/a = t²·π^(n-2)`. -/
private theorem frac_sq_mul_pow_eq {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S] {π : R} {n : ℕ} {a b : A}
    [IsLocalization.Away a S] {t : S} (ht : t * algebraMap A S a = algebraMap R S π)
    (hab : b * a = algebraMap R A (π ^ n)) (hn : 2 ≤ n) :
    t ^ 2 * algebraMap R S (π ^ (n - 2))
      = IsLocalization.mk' S b ⟨a, Submonoid.mem_powers a⟩ := by
  have hpi : π * π ^ (n - 2) = π ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine IsLocalization.eq_mk'_iff_mul_eq.2 ?_
  calc t ^ 2 * algebraMap R S (π ^ (n - 2)) * algebraMap A S a
      = t * (t * algebraMap A S a) * algebraMap R S (π ^ (n - 2)) := by ring
    _ = t * algebraMap R S (π ^ (n - 1)) := by rw [ht, mul_assoc, ← map_mul, hpi]
    _ = algebraMap A S b := frac_mul_pow_eq ht hab (by omega)

section XChart

variable {R : Type u} [CommRing R] (π : R) (n : ℕ)
  (S : Type u) [CommRing S] [Algebra (nodalChartRing R (π ^ n)) S]
  [IsLocalization.Away (nodalGen R (π ^ n) 0) S]

/-- The `x`-chart `A[𝔪/x]` of the blowup of `A = R[x, y]/(xy - πⁿ)` in `𝔪 = (π, x, y)`. -/
public abbrev nodalXChart : Subalgebra (nodalChartRing R (π ^ n)) S :=
  affineBlowupAlgebra (nodalCenter R π (π ^ n)) (nodalGen R (π ^ n) 0) S

/-- The fraction `u = π/x` in the localization of `R[x, y]/(xy - πⁿ)` away from `x`. -/
public def nodalXFrac : S :=
  IsLocalization.mk' S (algebraMap R (nodalChartRing R (π ^ n)) π)
    ⟨nodalGen R (π ^ n) 0, Submonoid.mem_powers _⟩

public theorem nodalXFrac_mem : nodalXFrac π n S ∈ nodalXChart π n S :=
  Algebra.subset_adjoin
    ⟨algebraMap R (nodalChartRing R (π ^ n)) π, Ideal.subset_span (by simp), rfl⟩

variable [Algebra R S] [IsScalarTower R (nodalChartRing R (π ^ n)) S]

public theorem nodalXFrac_mul :
    nodalXFrac π n S * algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 0)
      = algebraMap R S π :=
  (IsLocalization.mk'_spec S (algebraMap R (nodalChartRing R (π ^ n)) π)
    (⟨nodalGen R (π ^ n) 0, Submonoid.mem_powers _⟩ :
      Submonoid.powers (nodalGen R (π ^ n) 0))).trans
    (IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S π).symm

/-- The map `R[x, u]/(xu - π) → S` realizing the `x`-chart: `x ↦ x`, `u ↦ π/x`. -/
public def nodalXChartMap : nodalChartRing R π →ₐ[R] S :=
  nodalLift
    ![algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 0), nodalXFrac π n S]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_comm]
      exact nodalXFrac_mul π n S)

@[simp] public theorem nodalXChartMap_gen_zero :
    nodalXChartMap π n S (nodalGen R π 0)
      = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 0) := by
  rw [nodalXChartMap, nodalLift_nodalGen]
  simp

@[simp] public theorem nodalXChartMap_gen_one :
    nodalXChartMap π n S (nodalGen R π 1) = nodalXFrac π n S := by
  rw [nodalXChartMap, nodalLift_nodalGen]
  simp

/-- The map back, `R[x, y]/(xy - πⁿ) → R[x, u]/(xu - π)`: `x ↦ x`, `y ↦ u·π^(n-1)`. -/
public def nodalXChartBack (hn : 1 ≤ n) :
    nodalChartRing R (π ^ n) →ₐ[R] nodalChartRing R π :=
  nodalLift
    ![nodalGen R π 0, nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1))]
    (by
      have hpi : π * π ^ (n - 1) = π ^ n := by
        rw [← pow_succ']
        congr 1
        omega
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← mul_assoc, nodalGen_zero_mul_nodalGen_one, ← map_mul, hpi])

@[simp] public theorem nodalXChartBack_gen_zero (hn : 1 ≤ n) :
    nodalXChartBack π n hn (nodalGen R (π ^ n) 0) = nodalGen R π 0 := by
  rw [nodalXChartBack, nodalLift_nodalGen]
  simp

@[simp] public theorem nodalXChartBack_gen_one (hn : 1 ≤ n) :
    nodalXChartBack π n hn (nodalGen R (π ^ n) 1)
      = nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)) := by
  rw [nodalXChartBack, nodalLift_nodalGen]
  simp

/-- `y = u·π^(n-1)` holds in the localization: the fraction `π/x` times `π^(n-1)` is `y`. -/
public theorem nodalXFrac_mul_pow (hn : 1 ≤ n) :
    nodalXFrac π n S * algebraMap R S (π ^ (n - 1))
      = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 1) :=
  frac_mul_pow_eq (nodalXFrac_mul π n S)
    (by rw [mul_comm]; exact nodalGen_zero_mul_nodalGen_one _) hn

/-- `F ∘ G` is the localization map: the `x`-chart contains the image of `A`. -/
public theorem nodalXChartMap_comp_back (hn : 1 ≤ n) (p : nodalChartRing R (π ^ n)) :
    nodalXChartMap π n S (nodalXChartBack π n hn p)
      = algebraMap (nodalChartRing R (π ^ n)) S p := by
  have hext : (nodalXChartMap π n S).comp (nodalXChartBack π n hn) =
      IsScalarTower.toAlgHom R (nodalChartRing R (π ^ n)) S := by
    refine nodalChartRing_algHom_ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp
    · simp only [AlgHom.coe_comp, Function.comp_apply, nodalXChartBack_gen_one, map_mul,
        nodalXChartMap_gen_one, AlgHom.commutes]
      exact nodalXFrac_mul_pow π n S hn
  exact DFunLike.congr_fun hext p

/-- The fraction `y/x` equals `(π/x)²·π^(n-2)`; this is where `n ≥ 2` enters. -/
public theorem nodalXFrac_sq_mul_pow (hn : 2 ≤ n) :
    nodalXFrac π n S ^ 2 * algebraMap R S (π ^ (n - 2))
      = IsLocalization.mk' S (nodalGen R (π ^ n) 1)
          ⟨nodalGen R (π ^ n) 0, Submonoid.mem_powers _⟩ :=
  frac_sq_mul_pow_eq (nodalXFrac_mul π n S)
    (by rw [mul_comm]; exact nodalGen_zero_mul_nodalGen_one _) hn

/-- The denominator `x` becomes a unit after transport along the backward map. -/
public theorem nodalXChart_isUnit_back (hn : 1 ≤ n) :
    IsUnit (((algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0))).comp
      (nodalXChartBack π n hn).toRingHom) (nodalGen R (π ^ n) 0)) := by
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    nodalXChartBack_gen_zero]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Composing the chart map with the lift of the backward map gives the localization map of
`R[x, u]/(xu - π)` at `x`. -/
public theorem nodalXChartMap_awayLift (hn : 1 ≤ n) (v : nodalChartRing R π) :
    IsLocalization.Away.lift (nodalGen R (π ^ n) 0) (nodalXChart_isUnit_back π n hn)
        (nodalXChartMap π n S v)
      = algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0)) v := by
  have hext : (IsLocalization.Away.lift (nodalGen R (π ^ n) 0)
        (nodalXChart_isUnit_back π n hn)).comp (nodalXChartMap π n S).toRingHom
      = algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0)) := by
    refine nodalChartRing_ringHom_ext (fun r ↦ ?_) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes,
        IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S,
        IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalXChartMap_gen_zero, IsLocalization.Away.lift_eq,
        nodalXChartBack_gen_zero]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalXChartMap_gen_one, nodalXFrac]
      refine awayLift_mk'_eq (nodalXChart_isUnit_back π n hn) _ _ ?_
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalXChartBack_gen_zero, AlgHom.commutes]
      rw [← map_mul, mul_comm (nodalGen R π 1), nodalGen_zero_mul_nodalGen_one]
  exact RingHom.congr_fun hext v

/-- The chart map is injective. -/
public theorem nodalXChartMap_injective [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 1 ≤ n) : Function.Injective (nodalXChartMap π n S) := by
  have : IsDomain (nodalChartRing R π) := isDomain_nodalChartRing hπ
  exact injective_of_awayLift_comp (S' := Localization.Away (nodalGen R π 0))
    (nodalGen_zero_ne_zero π) (nodalXChartMap π n S).toRingHom
    (nodalXChart_isUnit_back π n hn) (nodalXChartMap_awayLift π n S hn)

/-- **The `x`-chart of the blowup of the standard nodal model.** For `n ≥ 2` the affine blowup
algebra `A[𝔪/x]` of `A = R[x, y]/(xy - πⁿ)` at `x`, where `𝔪 = (π, x, y)`, is
`R[x, u]/(xu - π)`, the identification carrying `x` to `x` and `y` to `u·π^(n-1)`. -/
@[stacks 0CDC "the algebra A[𝔪/x] has generators x, u = π/x subject to the relation xu - π"]
public theorem nodalXChart_equiv [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : ↥(nodalXChart π n S) ≃+* nodalChartRing R π,
      (∀ r : R, e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalXChart π n S)
          (algebraMap R (nodalChartRing R (π ^ n)) r))
        = algebraMap R (nodalChartRing R π) r) ∧
      e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalXChart π n S) (nodalGen R (π ^ n) 0))
        = nodalGen R π 0 ∧
      e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalXChart π n S) (nodalGen R (π ^ n) 1))
        = nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)) := by
  have hmem : ∀ v : nodalChartRing R π, nodalXChartMap π n S v ∈ nodalXChart π n S :=
    nodalLift_pair_mem (Subalgebra.algebraMap_mem _ _) (nodalXFrac_mem π n S)
  have hA : ∀ p : nodalChartRing R (π ^ n),
      algebraMap (nodalChartRing R (π ^ n)) S p ∈ (nodalXChartMap π n S).range :=
    fun p ↦ ⟨nodalXChartBack π n (by omega) p,
      nodalXChartMap_comp_back π n S (by omega) p⟩
  have hb : ∀ i : Fin 2,
      IsLocalization.mk' S
          (![algebraMap R (nodalChartRing R (π ^ n)) π, nodalGen R (π ^ n) 1] i)
          ⟨nodalGen R (π ^ n) 0, Submonoid.mem_powers _⟩ ∈ (nodalXChartMap π n S).range := by
    refine Fin.forall_fin_two.2 ⟨⟨nodalGen R π 1, ?_⟩,
      ⟨nodalGen R π 1 ^ 2 * algebraMap R (nodalChartRing R π) (π ^ (n - 2)), ?_⟩⟩
    · simp [nodalXFrac]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.cons_val_one]
      rw [map_mul, map_pow, nodalXChartMap_gen_one, AlgHom.commutes]
      exact nodalXFrac_sq_mul_pow π n S hn
  have hsurj : ∀ z ∈ nodalXChart π n S, ∃ v, nodalXChartMap π n S v = z := fun z hz ↦
    affineBlowupAlgebra_le_subalgebra
      (nodalCenter_eq_span_insert_gen_zero π (π ^ n)) (nodalXChartMap π n S).range hA hb z hz
  refine ⟨affineBlowupChartEquiv S (nodalXChartMap π n S).toRingHom
    (nodalXChartMap_injective π n S hπ (by omega)) hmem hsurj, fun r ↦ ?_, ?_, ?_⟩
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simpa using IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S r
  · exact affineBlowupChartEquiv_apply _ _ _ _ _ _ (by simp)
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, nodalXChartMap_gen_one, AlgHom.commutes]
    simpa using nodalXFrac_mul_pow π n S (by omega)

end XChart

section CentralChart

variable {R : Type u} [CommRing R] (π : R) (n : ℕ)
  (S : Type u) [CommRing S] [Algebra (nodalChartRing R (π ^ n)) S]
  [IsLocalization.Away (algebraMap R (nodalChartRing R (π ^ n)) π) S]

/-- The central chart `A[𝔪/π]` of the blowup of `A = R[x, y]/(xy - πⁿ)` in `𝔪 = (π, x, y)`. -/
public abbrev nodalCentralChart : Subalgebra (nodalChartRing R (π ^ n)) S :=
  affineBlowupAlgebra (nodalCenter R π (π ^ n))
    (algebraMap R (nodalChartRing R (π ^ n)) π) S

/-- The fractions `x/π` (for `i = 0`) and `y/π` (for `i = 1`). -/
public def nodalCentralFrac (i : Fin 2) : S :=
  IsLocalization.mk' S (nodalGen R (π ^ n) i)
    ⟨algebraMap R (nodalChartRing R (π ^ n)) π, Submonoid.mem_powers _⟩

public theorem nodalCentralFrac_mem (i : Fin 2) :
    nodalCentralFrac π n S i ∈ nodalCentralChart π n S :=
  Algebra.subset_adjoin
    ⟨nodalGen R (π ^ n) i, nodalGen_mem_nodalCenter π (π ^ n) i, rfl⟩

variable [Algebra R S] [IsScalarTower R (nodalChartRing R (π ^ n)) S]

public theorem nodalCentralFrac_mul (i : Fin 2) :
    nodalCentralFrac π n S i * algebraMap R S π
      = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) i) := by
  rw [IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S]
  exact IsLocalization.mk'_spec S (nodalGen R (π ^ n) i)
    (⟨algebraMap R (nodalChartRing R (π ^ n)) π, Submonoid.mem_powers _⟩ :
      Submonoid.powers (algebraMap R (nodalChartRing R (π ^ n)) π))

/-- The map `R[x', y']/(x'y' - π^(n-2)) → S` realizing the central chart:
`x' ↦ x/π` and `y' ↦ y/π`. -/
public def nodalCentralChartMap (hn : 2 ≤ n) :
    nodalChartRing R (π ^ (n - 2)) →ₐ[R] S :=
  nodalLift ![nodalCentralFrac π n S 0, nodalCentralFrac π n S 1] (by
    have hunit : IsUnit (algebraMap R S π) := by
      rw [IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hpi : π ^ (n - 2) * π * π = π ^ n := by
      have h2 : π ^ (n - 2) * π * π = π ^ (n - 2 + 1 + 1) := by rw [pow_succ, pow_succ]
      rw [h2]
      congr 1
      omega
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine (hunit.mul hunit).mul_right_cancel ?_
    calc nodalCentralFrac π n S 0 * nodalCentralFrac π n S 1 *
          (algebraMap R S π * algebraMap R S π)
        = nodalCentralFrac π n S 0 * algebraMap R S π *
            (nodalCentralFrac π n S 1 * algebraMap R S π) := by ring
      _ = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 0) *
            algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 1) := by
          rw [nodalCentralFrac_mul, nodalCentralFrac_mul]
      _ = algebraMap R S (π ^ n) := by
          rw [← map_mul, nodalGen_zero_mul_nodalGen_one,
            ← IsScalarTower.algebraMap_apply]
      _ = algebraMap R S (π ^ (n - 2)) * (algebraMap R S π * algebraMap R S π) := by
          rw [← map_mul, ← map_mul, ← mul_assoc, hpi])

@[simp] public theorem nodalCentralChartMap_gen (hn : 2 ≤ n) (i : Fin 2) :
    nodalCentralChartMap π n S hn (nodalGen R (π ^ (n - 2)) i)
      = nodalCentralFrac π n S i := by
  rw [nodalCentralChartMap, nodalLift_nodalGen]
  fin_cases i <;> rfl

/-- The map back, `R[x, y]/(xy - πⁿ) → R[x', y']/(x'y' - π^(n-2))`:
`x ↦ πx'` and `y ↦ πy'`. -/
public def nodalCentralChartBack (hn : 2 ≤ n) :
    nodalChartRing R (π ^ n) →ₐ[R] nodalChartRing R (π ^ (n - 2)) :=
  nodalLift
    ![algebraMap R (nodalChartRing R (π ^ (n - 2))) π * nodalGen R (π ^ (n - 2)) 0,
      algebraMap R (nodalChartRing R (π ^ (n - 2))) π * nodalGen R (π ^ (n - 2)) 1]
    (by
      have hpi : π * π * π ^ (n - 2) = π ^ n := by
        have h2 : π * π * π ^ (n - 2) = π ^ (n - 2 + 1 + 1) := by
          rw [pow_succ, pow_succ]; ring
        rw [h2]
        congr 1
        omega
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      calc algebraMap R (nodalChartRing R (π ^ (n - 2))) π * nodalGen R (π ^ (n - 2)) 0 *
            (algebraMap R (nodalChartRing R (π ^ (n - 2))) π * nodalGen R (π ^ (n - 2)) 1)
          = algebraMap R (nodalChartRing R (π ^ (n - 2))) π *
              algebraMap R (nodalChartRing R (π ^ (n - 2))) π *
              (nodalGen R (π ^ (n - 2)) 0 * nodalGen R (π ^ (n - 2)) 1) := by ring
        _ = algebraMap R (nodalChartRing R (π ^ (n - 2))) (π ^ n) := by
            rw [nodalGen_zero_mul_nodalGen_one, ← map_mul, ← map_mul, hpi])

@[simp] public theorem nodalCentralChartBack_gen (hn : 2 ≤ n) (i : Fin 2) :
    nodalCentralChartBack π n hn (nodalGen R (π ^ n) i)
      = algebraMap R (nodalChartRing R (π ^ (n - 2))) π * nodalGen R (π ^ (n - 2)) i := by
  rw [nodalCentralChartBack, nodalLift_nodalGen]
  fin_cases i <;> rfl

/-- `F ∘ G` is the localization map: the central chart contains the image of `A`. -/
public theorem nodalCentralChartMap_comp_back (hn : 2 ≤ n) (p : nodalChartRing R (π ^ n)) :
    nodalCentralChartMap π n S hn (nodalCentralChartBack π n hn p)
      = algebraMap (nodalChartRing R (π ^ n)) S p := by
  have hext : (nodalCentralChartMap π n S hn).comp (nodalCentralChartBack π n hn) =
      IsScalarTower.toAlgHom R (nodalChartRing R (π ^ n)) S := by
    refine nodalChartRing_algHom_ext fun i ↦ ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, nodalCentralChartBack_gen, map_mul,
      nodalCentralChartMap_gen, AlgHom.commutes]
    rw [mul_comm]
    exact nodalCentralFrac_mul π n S i
  exact DFunLike.congr_fun hext p

public theorem nodalCentral_isUnit_back (hn : 2 ≤ n) :
    IsUnit (((algebraMap (nodalChartRing R (π ^ (n - 2)))
        (Localization.Away (algebraMap R (nodalChartRing R (π ^ (n - 2))) π))).comp
      (nodalCentralChartBack π n hn).toRingHom)
      (algebraMap R (nodalChartRing R (π ^ n)) π)) := by
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Composing the central chart map with the lift of the backward map gives the localization map
of `R[x', y']/(x'y' - π^(n-2))` at `π`. -/
public theorem nodalCentralChartMap_awayLift (hn : 2 ≤ n)
    (v : nodalChartRing R (π ^ (n - 2))) :
    IsLocalization.Away.lift (algebraMap R (nodalChartRing R (π ^ n)) π)
        (nodalCentral_isUnit_back π n hn) (nodalCentralChartMap π n S hn v)
      = algebraMap (nodalChartRing R (π ^ (n - 2)))
          (Localization.Away (algebraMap R (nodalChartRing R (π ^ (n - 2))) π)) v := by
  have hext : (IsLocalization.Away.lift (algebraMap R (nodalChartRing R (π ^ n)) π)
        (nodalCentral_isUnit_back π n hn)).comp (nodalCentralChartMap π n S hn).toRingHom
      = algebraMap (nodalChartRing R (π ^ (n - 2)))
          (Localization.Away (algebraMap R (nodalChartRing R (π ^ (n - 2))) π)) := by
    refine nodalChartRing_ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes,
        IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S,
        IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalCentralChartMap_gen, nodalCentralFrac]
      refine awayLift_mk'_eq (nodalCentral_isUnit_back π n hn) _ _ ?_
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalCentralChartBack_gen, AlgHom.commutes]
      rw [← map_mul, mul_comm]
  exact RingHom.congr_fun hext v

public theorem nodalCentralChartMap_injective [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 2 ≤ n) :
    Function.Injective (nodalCentralChartMap π n S hn) := by
  have : IsDomain (nodalChartRing R (π ^ (n - 2))) :=
    isDomain_nodalChartRing (pow_ne_zero _ hπ)
  exact injective_of_awayLift_comp
    (S' := Localization.Away (algebraMap R (nodalChartRing R (π ^ (n - 2))) π))
    (algebraMap_nodalChartRing_ne_zero (π ^ (n - 2)) hπ)
    (nodalCentralChartMap π n S hn).toRingHom (nodalCentral_isUnit_back π n hn)
    (nodalCentralChartMap_awayLift π n S hn)

/-- **The central chart of the blowup of the standard nodal model, and the drop `n ↦ n - 2`.**
For `n ≥ 2` the affine blowup algebra `A[𝔪/π]` of `A = R[x, y]/(xy - πⁿ)` at `π`, where
`𝔪 = (π, x, y)`, is again a standard nodal model, with the exponent lowered by two:
`R[x', y']/(x'y' - π^(n-2))`, the identification carrying `x` to `πx'` and `y` to `πy'`. -/
@[stacks 0CDC "the algebra A[𝔪/π] has generators x' = x/π and y' = y/π with x'y' = π^(n-2), so \
this part of X' is the spectrum of R[x', y']/(x'y' - π^(n-2))"]
public theorem nodalCentralChart_equiv [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : ↥(nodalCentralChart π n S) ≃+* nodalChartRing R (π ^ (n - 2)),
      (∀ r : R, e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalCentralChart π n S)
          (algebraMap R (nodalChartRing R (π ^ n)) r))
        = algebraMap R (nodalChartRing R (π ^ (n - 2))) r) ∧
      (∀ i : Fin 2,
        e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalCentralChart π n S)
            (nodalGen R (π ^ n) i))
          = algebraMap R (nodalChartRing R (π ^ (n - 2))) π *
              nodalGen R (π ^ (n - 2)) i) := by
  have hmem : ∀ v : nodalChartRing R (π ^ (n - 2)),
      nodalCentralChartMap π n S hn v ∈ nodalCentralChart π n S :=
    nodalLift_pair_mem (nodalCentralFrac_mem π n S 0) (nodalCentralFrac_mem π n S 1)
  have hA : ∀ p : nodalChartRing R (π ^ n),
      algebraMap (nodalChartRing R (π ^ n)) S p ∈
        (nodalCentralChartMap π n S hn).range :=
    fun p ↦ ⟨nodalCentralChartBack π n hn p, nodalCentralChartMap_comp_back π n S hn p⟩
  have hb : ∀ i : Fin 2,
      IsLocalization.mk' S (![nodalGen R (π ^ n) 0, nodalGen R (π ^ n) 1] i)
          ⟨algebraMap R (nodalChartRing R (π ^ n)) π, Submonoid.mem_powers _⟩ ∈
        (nodalCentralChartMap π n S hn).range := by
    refine Fin.forall_fin_two.2 ⟨⟨nodalGen R (π ^ (n - 2)) 0, ?_⟩,
      ⟨nodalGen R (π ^ (n - 2)) 1, ?_⟩⟩
    · simp [nodalCentralFrac]
    · simp [nodalCentralFrac]
  have hsurj : ∀ z ∈ nodalCentralChart π n S,
      ∃ v, nodalCentralChartMap π n S hn v = z := fun z hz ↦
    affineBlowupAlgebra_le_subalgebra
      (nodalCenter_eq_span_insert_algebraMap π (π ^ n))
      (nodalCentralChartMap π n S hn).range hA hb z hz
  refine ⟨affineBlowupChartEquiv S (nodalCentralChartMap π n S hn).toRingHom
    (nodalCentralChartMap_injective π n S hπ hn) hmem hsurj, fun r ↦ ?_, fun i ↦ ?_⟩
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simpa using IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S r
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, nodalCentralChartMap_gen, AlgHom.commutes, mul_comm]
    simpa using nodalCentralFrac_mul π n S i

end CentralChart

section YChart

variable {R : Type u} [CommRing R] (π : R) (n : ℕ)
  (S : Type u) [CommRing S] [Algebra (nodalChartRing R (π ^ n)) S]
  [IsLocalization.Away (nodalGen R (π ^ n) 1) S]

/-- The `y`-chart `A[𝔪/y]` of the blowup of `A = R[x, y]/(xy - πⁿ)` in `𝔪 = (π, x, y)`. -/
public abbrev nodalYChart : Subalgebra (nodalChartRing R (π ^ n)) S :=
  affineBlowupAlgebra (nodalCenter R π (π ^ n)) (nodalGen R (π ^ n) 1) S

/-- The fraction `v = π/y` in the localization of `R[x, y]/(xy - πⁿ)` away from `y`. -/
public def nodalYFrac : S :=
  IsLocalization.mk' S (algebraMap R (nodalChartRing R (π ^ n)) π)
    ⟨nodalGen R (π ^ n) 1, Submonoid.mem_powers _⟩

public theorem nodalYFrac_mem : nodalYFrac π n S ∈ nodalYChart π n S :=
  Algebra.subset_adjoin
    ⟨algebraMap R (nodalChartRing R (π ^ n)) π, algebraMap_mem_nodalCenter π (π ^ n), rfl⟩

variable [Algebra R S] [IsScalarTower R (nodalChartRing R (π ^ n)) S]

public theorem nodalYFrac_mul :
    nodalYFrac π n S * algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 1)
      = algebraMap R S π :=
  (IsLocalization.mk'_spec S (algebraMap R (nodalChartRing R (π ^ n)) π)
    (⟨nodalGen R (π ^ n) 1, Submonoid.mem_powers _⟩ :
      Submonoid.powers (nodalGen R (π ^ n) 1))).trans
    (IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S π).symm

/-- The map `R[y, v]/(yv - π) → S` realizing the `y`-chart: `y ↦ y`, `v ↦ π/y`. -/
public def nodalYChartMap : nodalChartRing R π →ₐ[R] S :=
  nodalLift
    ![algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 1), nodalYFrac π n S]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_comm]
      exact nodalYFrac_mul π n S)

@[simp] public theorem nodalYChartMap_gen_zero :
    nodalYChartMap π n S (nodalGen R π 0)
      = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 1) := by
  rw [nodalYChartMap, nodalLift_nodalGen]
  simp

@[simp] public theorem nodalYChartMap_gen_one :
    nodalYChartMap π n S (nodalGen R π 1) = nodalYFrac π n S := by
  rw [nodalYChartMap, nodalLift_nodalGen]
  simp

/-- The map back, `R[x, y]/(xy - πⁿ) → R[y, v]/(yv - π)`: `y ↦ y`, `x ↦ v·π^(n-1)`. -/
public def nodalYChartBack (hn : 1 ≤ n) :
    nodalChartRing R (π ^ n) →ₐ[R] nodalChartRing R π :=
  nodalLift
    ![nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)), nodalGen R π 0]
    (by
      have hpi : π * π ^ (n - 1) = π ^ n := by
        rw [← pow_succ']
        congr 1
        omega
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      calc nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)) *
            nodalGen R π 0
          = nodalGen R π 0 * nodalGen R π 1 *
              algebraMap R (nodalChartRing R π) (π ^ (n - 1)) := by ring
        _ = algebraMap R (nodalChartRing R π) (π ^ n) := by
            rw [nodalGen_zero_mul_nodalGen_one, ← map_mul, hpi])

@[simp] public theorem nodalYChartBack_gen_one (hn : 1 ≤ n) :
    nodalYChartBack π n hn (nodalGen R (π ^ n) 1) = nodalGen R π 0 := by
  rw [nodalYChartBack, nodalLift_nodalGen]
  simp

@[simp] public theorem nodalYChartBack_gen_zero (hn : 1 ≤ n) :
    nodalYChartBack π n hn (nodalGen R (π ^ n) 0)
      = nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)) := by
  rw [nodalYChartBack, nodalLift_nodalGen]
  simp

/-- `x = v·π^(n-1)` holds in the localization. -/
public theorem nodalYFrac_mul_pow (hn : 1 ≤ n) :
    nodalYFrac π n S * algebraMap R S (π ^ (n - 1))
      = algebraMap (nodalChartRing R (π ^ n)) S (nodalGen R (π ^ n) 0) :=
  frac_mul_pow_eq (nodalYFrac_mul π n S) (nodalGen_zero_mul_nodalGen_one _) hn

public theorem nodalYChartMap_comp_back (hn : 1 ≤ n) (p : nodalChartRing R (π ^ n)) :
    nodalYChartMap π n S (nodalYChartBack π n hn p)
      = algebraMap (nodalChartRing R (π ^ n)) S p := by
  have hext : (nodalYChartMap π n S).comp (nodalYChartBack π n hn) =
      IsScalarTower.toAlgHom R (nodalChartRing R (π ^ n)) S := by
    refine nodalChartRing_algHom_ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [AlgHom.coe_comp, Function.comp_apply, nodalYChartBack_gen_zero, map_mul,
        nodalYChartMap_gen_one, AlgHom.commutes]
      exact nodalYFrac_mul_pow π n S hn
    · simp
  exact DFunLike.congr_fun hext p

/-- The fraction `x/y` equals `(π/y)²·π^(n-2)`; this is where `n ≥ 2` enters. -/
public theorem nodalYFrac_sq_mul_pow (hn : 2 ≤ n) :
    nodalYFrac π n S ^ 2 * algebraMap R S (π ^ (n - 2))
      = IsLocalization.mk' S (nodalGen R (π ^ n) 0)
          ⟨nodalGen R (π ^ n) 1, Submonoid.mem_powers _⟩ :=
  frac_sq_mul_pow_eq (nodalYFrac_mul π n S) (nodalGen_zero_mul_nodalGen_one _) hn

public theorem nodalYChart_isUnit_back (hn : 1 ≤ n) :
    IsUnit (((algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0))).comp
      (nodalYChartBack π n hn).toRingHom) (nodalGen R (π ^ n) 1)) := by
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    nodalYChartBack_gen_one]
  exact IsLocalization.Away.algebraMap_isUnit _

public theorem nodalYChartMap_awayLift (hn : 1 ≤ n) (v : nodalChartRing R π) :
    IsLocalization.Away.lift (nodalGen R (π ^ n) 1) (nodalYChart_isUnit_back π n hn)
        (nodalYChartMap π n S v)
      = algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0)) v := by
  have hext : (IsLocalization.Away.lift (nodalGen R (π ^ n) 1)
        (nodalYChart_isUnit_back π n hn)).comp (nodalYChartMap π n S).toRingHom
      = algebraMap (nodalChartRing R π) (Localization.Away (nodalGen R π 0)) := by
    refine nodalChartRing_ringHom_ext (fun r ↦ ?_) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes,
        IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S,
        IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalYChartMap_gen_zero, IsLocalization.Away.lift_eq,
        nodalYChartBack_gen_one]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalYChartMap_gen_one, nodalYFrac]
      refine awayLift_mk'_eq (nodalYChart_isUnit_back π n hn) _ _ ?_
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, nodalYChartBack_gen_one, AlgHom.commutes]
      rw [← map_mul, mul_comm (nodalGen R π 1), nodalGen_zero_mul_nodalGen_one]
  exact RingHom.congr_fun hext v

public theorem nodalYChartMap_injective [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 1 ≤ n) : Function.Injective (nodalYChartMap π n S) := by
  have : IsDomain (nodalChartRing R π) := isDomain_nodalChartRing hπ
  exact injective_of_awayLift_comp (S' := Localization.Away (nodalGen R π 0))
    (nodalGen_zero_ne_zero π) (nodalYChartMap π n S).toRingHom
    (nodalYChart_isUnit_back π n hn) (nodalYChartMap_awayLift π n S hn)

/-- **The `y`-chart of the blowup of the standard nodal model.** For `n ≥ 2` the affine blowup
algebra `A[𝔪/y]` of `A = R[x, y]/(xy - πⁿ)` at `y`, where `𝔪 = (π, x, y)`, is
`R[y, v]/(yv - π)`, the identification carrying `y` to `y` and `x` to `v·π^(n-1)`. -/
@[stacks 0CDC "by symmetry the case of the algebra A[𝔪/y] is the same as the case of A[𝔪/x]"]
public theorem nodalYChart_equiv [IsDomain R] [UniqueFactorizationMonoid R]
    (hπ : π ≠ 0) (hn : 2 ≤ n) :
    ∃ e : ↥(nodalYChart π n S) ≃+* nodalChartRing R π,
      (∀ r : R, e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalYChart π n S)
          (algebraMap R (nodalChartRing R (π ^ n)) r))
        = algebraMap R (nodalChartRing R π) r) ∧
      e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalYChart π n S) (nodalGen R (π ^ n) 1))
        = nodalGen R π 0 ∧
      e (algebraMap (nodalChartRing R (π ^ n)) ↥(nodalYChart π n S) (nodalGen R (π ^ n) 0))
        = nodalGen R π 1 * algebraMap R (nodalChartRing R π) (π ^ (n - 1)) := by
  have hmem : ∀ v : nodalChartRing R π, nodalYChartMap π n S v ∈ nodalYChart π n S :=
    nodalLift_pair_mem (Subalgebra.algebraMap_mem _ _) (nodalYFrac_mem π n S)
  have hA : ∀ p : nodalChartRing R (π ^ n),
      algebraMap (nodalChartRing R (π ^ n)) S p ∈ (nodalYChartMap π n S).range :=
    fun p ↦ ⟨nodalYChartBack π n (by omega) p,
      nodalYChartMap_comp_back π n S (by omega) p⟩
  have hb : ∀ i : Fin 2,
      IsLocalization.mk' S
          (![algebraMap R (nodalChartRing R (π ^ n)) π, nodalGen R (π ^ n) 0] i)
          ⟨nodalGen R (π ^ n) 1, Submonoid.mem_powers _⟩ ∈ (nodalYChartMap π n S).range := by
    refine Fin.forall_fin_two.2 ⟨⟨nodalGen R π 1, ?_⟩,
      ⟨nodalGen R π 1 ^ 2 * algebraMap R (nodalChartRing R π) (π ^ (n - 2)), ?_⟩⟩
    · simp [nodalYFrac]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.cons_val_one]
      rw [map_mul, map_pow, nodalYChartMap_gen_one, AlgHom.commutes]
      exact nodalYFrac_sq_mul_pow π n S hn
  have hsurj : ∀ z ∈ nodalYChart π n S, ∃ v, nodalYChartMap π n S v = z := fun z hz ↦
    affineBlowupAlgebra_le_subalgebra
      (nodalCenter_eq_span_insert_gen_one π (π ^ n)) (nodalYChartMap π n S).range hA hb z hz
  refine ⟨affineBlowupChartEquiv S (nodalYChartMap π n S).toRingHom
    (nodalYChartMap_injective π n S hπ (by omega)) hmem hsurj, fun r ↦ ?_, ?_, ?_⟩
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simpa using IsScalarTower.algebraMap_apply R (nodalChartRing R (π ^ n)) S r
  · exact affineBlowupChartEquiv_apply _ _ _ _ _ _ (by simp)
  · refine affineBlowupChartEquiv_apply _ _ _ _ _ _ ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, nodalYChartMap_gen_one, AlgHom.commutes]
    simpa using nodalYFrac_mul_pow π n S (by omega)

end YChart

end Stacks

end
