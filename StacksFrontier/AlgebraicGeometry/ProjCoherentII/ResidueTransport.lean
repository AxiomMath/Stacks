module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ResidueFiniteness

/-!
# Transporting one residue class of a graded truncation across a degree-scaling comparison

This is the step the Veronese reduction of [Stacks, Tag 0B5R] performs once for each residue
class. Let `S = ⨁_{i ≥ 0} 𝒮 i` be a graded ring, `d ≥ 1`, `S⁽ᵈ⁾` the Veronese subring, and let
`⨁_{n ∈ ℤ} V n` carry a degree-raising `S`-action. Suppose `⨁_{m ∈ ℤ} W m` carries a
degree-raising `S⁽ᵈ⁾`-action and there are surjections

`θ m : W m → V (m d + q)`

compatible with the two actions — a scalar of Veronese degree `e`, that is an element of
`S_{ed}`, acts the same on both sides. Then a finite generating family over `S⁽ᵈ⁾` for the
truncation `⨁_{m ≥ k'} W m` produces one for the part of `⨁_{n ≥ k} V n` supported in the
degrees congruent to `q` modulo `d` — which is exactly the hypothesis of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_gradedActionTruncation_of_residues`.

Nothing here is about `Proj`. Downstairs `⨁ V n` will be the twisted global sections of a sheaf
on `X = Proj S`, upstairs `⨁ W m` the twisted global sections of a sheaf on `X' = Proj S⁽ᵈ⁾`,
and `θ` the composite of Tag 0B5J's comparison with the identifications `ℱ(q + md) ≅ (ℱ(q))(md)`;
but the assembly of the degreewise comparisons into a semilinear map, and the identification of
its image with one residue class, are pure bookkeeping and are done once, here.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistedSections.residueEmbedding`: the map
  `⨁_{m ∈ ℤ} W m → ⨁_{n ∈ ℤ} V n` assembled from the `θ m`, placing the degree-`m` summand in
  degree `m d + q`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.residueScalarDegree`: the degree bookkeeping
  `ed + (md + q) = (e + m)d + q` the comparison transports along.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.residueEmbedding_smul`: the assembled map is
  `S⁽ᵈ⁾`-linear.
* `Stacks.AlgebraicGeometry.ProjTwistedSections.exists_finite_span_residue`: **the transport.**

## Implementation notes

**The degree equation is a named theorem.** `θ ((e : ℤ) + m)` lands in `V (((e : ℤ) + m) d + q)`
while the action downstairs lands in `V (ed + (md + q))`, and those are the same integer only
propositionally. Giving the identification one name, `residueScalarDegree`, keeps the two sides of
every `exact` syntactically equal; writing it inline makes the unifier reduce two distinct
elaborations of the same arithmetic.

`θ` is only required to be **surjective**, not bijective: the conclusion is that every element of
one residue class of the truncation is an `S⁽ᵈ⁾`-combination of finitely many fixed elements, and
for that only the image of `θ` matters. The comparisons the consumers supply happen to be
bijective, but nothing uses their injectivity.

The residue index is recovered from the degree by division: an `n` with `n % d = q` is
`(n / d) d + q`, so the degree-`n` summand of a residue-`q` element is the image of the
degree-`n / d` summand upstairs. The hypothesis `hk` is the matching translation of the two
truncation bounds.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The degree bookkeeping of the residue transport.** A scalar of Veronese degree `e`, acting
on the degree-`m` summand upstairs, lands in Veronese degree `e + m`, which the comparison reads
in degree `(e + m)d + q`; downstairs the same scalar has degree `ed` and carries degree `md + q`
to `ed + (md + q)`. -/
public theorem residueScalarDegree (e : ℕ) (m : ℤ) (d q : ℕ) :
    ((e * d : ℕ) : ℤ) + (m * d + q) = ((e : ℤ) + m) * d + q := by
  push_cast
  ring

variable {V : ℤ → Type u} [∀ n, AddCommGroup (V n)]

/-- Transporting a summand along an equality of degrees does not change the element of the direct
sum it names. -/
public theorem of_cast_degree {n n' : ℤ} (h : n' = n) (z : V n') :
    DirectSum.of V n (cast (congrArg V h) z) = DirectSum.of V n' z := by
  subst h
  rfl

/-- A degree in the support of an element is not one on which a vanishing criterion applies. -/
private theorem not_of_mem_support [∀ i (x : V i), Decidable (x ≠ 0)] {y : ⨁ n : ℤ, V n}
    {n : ℤ} (hn : n ∈ DFinsupp.support y) {P : ℤ → Prop}
    (h : ∀ n, P n → DirectSum.component ℤ ℤ V n y = 0) : ¬ P n := fun hP =>
  DFinsupp.mem_support_iff.mp hn (h n hP)

/-- A homogeneous element of degree `≥ k` lies in the degree-`≥ k` truncation of a graded
action. -/
public theorem of_mem_gradedActionTruncation [Module S (⨁ n : ℤ, V n)]
    (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
      (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
        DirectSum.of V ((i : ℤ) + n) (act i n a s))
    (k m : ℤ) (hm : k ≤ m) (z : V m) :
    (DirectSum.of V m z : ⨁ n : ℤ, V n) ∈ gradedActionTruncation 𝒮 act hsmul k := by
  intro n hn
  rw [← DirectSum.apply_eq_component]
  exact DirectSum.of_eq_of_ne _ _ _ (by omega)

section Transport

variable [Module S (⨁ n : ℤ, V n)]
  (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
  (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
    (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
      DirectSum.of V ((i : ℤ) + n) (act i n a s))

variable (d : ℕ) [GradedRing (Stacks.Veronese.veroneseGrading 𝒮 d)]

variable {W : ℤ → Type u} [∀ m, AddCommGroup (W m)]
  [Module (Stacks.Veronese.veroneseSubring 𝒮 d) (⨁ m : ℤ, W m)]
  (act' : ∀ (e : ℕ) (m : ℤ), Stacks.Veronese.veroneseGrading 𝒮 d e → W m → W ((e : ℤ) + m))
  (hsmul' : ∀ (e : ℕ) (m : ℤ) (b : Stacks.Veronese.veroneseGrading 𝒮 d e) (y : W m),
    (b : Stacks.Veronese.veroneseSubring 𝒮 d) •
        (DirectSum.of W m y : ⨁ j : ℤ, W j) =
      DirectSum.of W ((e : ℤ) + m) (act' e m b y))

variable (q : ℕ) (θ : ∀ m : ℤ, W m →+ V (m * d + q))

/-- **The assembled residue comparison** `⨁_{m ∈ ℤ} W m → ⨁_{n ∈ ℤ} V n`: the degree-`m` summand
goes to the degree-`md + q` summand by `θ m`. -/
public def residueEmbedding : (⨁ m : ℤ, W m) →+ (⨁ n : ℤ, V n) :=
  DirectSum.toAddMonoid fun m => (DirectSum.of V (m * d + q)).comp (θ m)

/-- `residueEmbedding d q θ` sends the degree-`m` element `y` to `θ m y` in degree `md + q`. -/
@[simp] public theorem residueEmbedding_of (m : ℤ) (y : W m) :
    residueEmbedding d q θ (DirectSum.of W m y) =
      DirectSum.of V (m * (d : ℤ) + q) (θ m y) :=
  DirectSum.toAddMonoid_of _ _ _

variable (hθ : ∀ (e : ℕ) (m : ℤ) (b : Stacks.Veronese.veroneseGrading 𝒮 d e) (y : W m),
  θ ((e : ℤ) + m) (act' e m b y) =
    cast (congrArg V (residueScalarDegree e m d q))
      (act (e * d) (m * (d : ℤ) + q)
        ⟨((b : Stacks.Veronese.veroneseSubring 𝒮 d) : S), b.2⟩ (θ m y)))

omit [GradedRing 𝒮] in
include hsmul hsmul' hθ in
/-- **The assembled residue comparison is `S⁽ᵈ⁾`-linear.** On a homogeneous scalar and a single
summand this is the hypothesis `hθ`; the general case follows by decomposing the scalar into its
Veronese-homogeneous pieces and the argument into its summands. -/
public theorem residueEmbedding_smul (c : Stacks.Veronese.veroneseSubring 𝒮 d)
    (x : ⨁ m : ℤ, W m) :
    residueEmbedding d q θ (c • x) = (c : S) • residueEmbedding d q θ x := by
  classical
  have hhom : ∀ (e : ℕ) (b : Stacks.Veronese.veroneseGrading 𝒮 d e) (y : ⨁ m : ℤ, W m),
      residueEmbedding d q θ ((b : Stacks.Veronese.veroneseSubring 𝒮 d) • y) =
        (((b : Stacks.Veronese.veroneseSubring 𝒮 d) : S)) • residueEmbedding d q θ y := by
    intro e b y
    induction y using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of m z =>
        rw [hsmul' e m b z, residueEmbedding_of, residueEmbedding_of, hθ e m b z,
          hsmul (e * d) (m * (d : ℤ) + q)
            ⟨((b : Stacks.Veronese.veroneseSubring 𝒮 d) : S), b.2⟩ (θ m z)]
        exact of_cast_degree (residueScalarDegree e m d q) _
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  have hc := DirectSum.sum_support_decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c
  have hstep : residueEmbedding d q θ
        ((∑ e ∈ (DirectSum.decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c).support,
            ((DirectSum.decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c e :
              Stacks.Veronese.veroneseSubring 𝒮 d))) • x) =
      (((∑ e ∈ (DirectSum.decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c).support,
            ((DirectSum.decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c e :
              Stacks.Veronese.veroneseSubring 𝒮 d))) :
          Stacks.Veronese.veroneseSubring 𝒮 d) : S) • residueEmbedding d q θ x := by
    rw [Finset.sum_smul, map_sum]
    push_cast
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun e _ =>
      hhom e (DirectSum.decompose (Stacks.Veronese.veroneseGrading 𝒮 d) c e) x
  rwa [hc] at hstep

include hsmul hsmul' in
/-- The assembled comparison carries the degree-`≥ k'` truncation upstairs into the degree-`≥ k`
truncation downstairs, as soon as `m ≥ k'` forces `md + q ≥ k`. -/
public theorem residueEmbedding_mem_truncation (k k' : ℤ)
    (hk : ∀ m : ℤ, k' ≤ m → k ≤ m * (d : ℤ) + q)
    {x : ⨁ m : ℤ, W m}
    (hx : x ∈ gradedActionTruncation (Stacks.Veronese.veroneseGrading 𝒮 d) act' hsmul' k') :
    residueEmbedding d q θ x ∈ gradedActionTruncation 𝒮 act hsmul k := by
  classical
  have hsupp : ∀ m ∈ (DFinsupp.support x), k' ≤ m := by
    intro m hm
    by_contra hlt
    exact not_of_mem_support hm hx (by omega)
  have hsum : residueEmbedding d q θ x =
      ∑ m ∈ DFinsupp.support x, DirectSum.of V (m * (d : ℤ) + q) (θ m (x m)) := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => residueEmbedding_of d q θ m (x m)
  rw [hsum]
  refine Submodule.sum_mem _ fun m hm => ?_
  exact of_mem_gradedActionTruncation 𝒮 act hsmul k _ (hk m (hsupp m hm)) _

include hsmul hsmul' hθ in
/-- **The transport.** Suppose the degree-`≥ k'` truncation upstairs is a finite `S⁽ᵈ⁾`-module,
every `θ m` is surjective, and the two truncation bounds correspond. Then there is a finite
subset of the degree-`≥ k` truncation downstairs whose `S⁽ᵈ⁾`-span contains every element of that
truncation supported in the degrees congruent to `q` modulo `d`.

This is precisely the per-residue hypothesis of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_gradedActionTruncation_of_residues`. -/
public theorem exists_finite_span_residue (hd : 0 < d) (k k' : ℤ)
    (hk : ∀ m : ℤ, k' ≤ m ↔ k ≤ m * (d : ℤ) + q)
    (hsurj : ∀ m : ℤ, Function.Surjective (θ m))
    (hfin : Module.Finite (Stacks.Veronese.veroneseSubring 𝒮 d)
      (gradedActionTruncation (Stacks.Veronese.veroneseGrading 𝒮 d) act' hsmul' k')) :
    ∃ G : Set (⨁ n : ℤ, V n), G.Finite ∧
      G ⊆ (gradedActionTruncation 𝒮 act hsmul k : Set (⨁ n : ℤ, V n)) ∧
      ∀ y ∈ gradedActionTruncation 𝒮 act hsmul k,
        (∀ n : ℤ, Stacks.Veronese.degreeResidue d n ≠ q →
          DirectSum.component ℤ ℤ V n y = 0) →
        y ∈ Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d) G := by
  classical
  obtain ⟨t, ht⟩ : (gradedActionTruncation (Stacks.Veronese.veroneseGrading 𝒮 d)
    act' hsmul' k').FG := Module.Finite.iff_fg.mp hfin
  refine ⟨residueEmbedding d q θ '' (t : Set (⨁ m : ℤ, W m)), (t.finite_toSet).image _, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine residueEmbedding_mem_truncation 𝒮 act hsmul d act' hsmul' q θ k k'
      (fun m hm => (hk m).mp hm) ?_
    rw [← ht]
    exact Submodule.subset_span hz
  · -- every element of the truncation supported in the residue class of `q` is in the span
    have himg : ∀ x ∈ gradedActionTruncation (Stacks.Veronese.veroneseGrading 𝒮 d)
        act' hsmul' k', residueEmbedding d q θ x ∈
        Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d)
          (residueEmbedding d q θ '' (t : Set (⨁ m : ℤ, W m))) := by
      intro x hx
      rw [← ht] at hx
      induction hx using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha =>
          rw [residueEmbedding_smul 𝒮 act hsmul d act' hsmul' q θ hθ]
          exact Submodule.smul_mem _ c ha
    intro y hy hres
    suffices hterm : ∀ n ∈ DFinsupp.support y,
        (DirectSum.of V n (y n) : ⨁ j : ℤ, V j) ∈
          Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d)
            (residueEmbedding d q θ '' (t : Set (⨁ m : ℤ, W m))) by
      have hsum := Submodule.sum_mem (Submodule.span (Stacks.Veronese.veroneseSubring 𝒮 d)
        (residueEmbedding d q θ '' (t : Set (⨁ m : ℤ, W m)))) hterm
      rwa [DirectSum.sum_support_of y] at hsum
    intro n hn
    -- the degree `n` is `m * d + q`
    have hq : Stacks.Veronese.degreeResidue d n = q := by
      by_contra hne
      exact not_of_mem_support hn hres hne
    have hmod : n % (d : ℤ) = (q : ℤ) := by
      rw [← Stacks.Veronese.coe_degreeResidue hd n, hq]
    set m : ℤ := n / (d : ℤ) with hm_def
    have hmn : m * (d : ℤ) + (q : ℤ) = n := by
      have h := Int.emod_def n (d : ℤ)
      rw [hmod] at h
      rw [hm_def, mul_comm]
      linarith
    have hkn : k ≤ n := by
      by_contra hlt
      exact not_of_mem_support hn hy (by omega)
    have hk' : k' ≤ m := (hk m).mpr (by rw [hmn]; exact hkn)
    obtain ⟨wz, hwz⟩ := hsurj m (cast (congrArg V hmn.symm) (y n))
    have hof : residueEmbedding d q θ (DirectSum.of W m wz) = DirectSum.of V n (y n) := by
      rw [residueEmbedding_of, hwz]
      exact of_cast_degree hmn.symm (y n)
    rw [← hof]
    exact himg _ (of_mem_gradedActionTruncation _ act' hsmul' k' m hk' wz)

end Transport

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
