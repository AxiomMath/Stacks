module

public import StacksFrontier.RingTheory.AffineBlowup.Rescale
public import StacksFrontier.RingTheory.Flat.BlowupStrictTransformAlg

/-!
# Flattening by blowing up: the proof of Stacks Tag 053I

Let `(R, 𝔪)` be a local domain with fraction field `K`, let `𝔪 ≠ 0`, let `S` be a finite type
`R`-algebra, let `M` be a finite `S`-module and let `A ⊆ K` be a valuation ring dominating `R`.
[Stacks, Tag 053I] produces an admissible affine blowup chart `R[I/a]` of Stacks Tag 052M on which
the strict transforms of `S` and `M` become flat and of finite presentation.  This file completes
the proof, whose earlier steps are in

* `StacksFrontier.RingTheory.Flat.BlowupValuationModel` (the valuation-ring model, Stacks Tags 0537,
  0539 and 053E),
* `StacksFrontier.RingTheory.Flat.BlowupDescent` (descent of flatness along the chart system,
  Stacks Tag 02JO (3)),
* `StacksFrontier.RingTheory.Flat.BlowupFlatten` (the chart bridges and the identification of the
  strict transform with a quotient of a finite free module),
* `StacksFrontier.RingTheory.Flat.BlowupStrictTransformAlg` (clause (4) for a polynomial algebra,
  given the relation submodule), and
* `StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction` (the ring theory of the reduction from a
  finite type algebra to a polynomial one).

The argument runs as follows.  Fix a surjection `π : R[x_1, …, x_n]ʳ → M` and let `Z_B` denote,
for a commutative `R`-algebra `B`, the base change to `B[x_1, …, x_n]ʳ` of `ker π`.  Over the
valuation ring the saturation of `Z_A` — the vectors carried into `Z_A` by a nonzero element of
`A` — is finitely generated, because the corresponding quotient is the valuation-ring model, which
is finitely presented by Nagata's theorem, and it is flat over `A`.  Finitely many generators
`k_1, …, k_m` of that saturation involve finitely many coefficients, so they come from a single
chart, and Stacks Tag 02JO (3) descends flatness to a chart `c`.  Comparing back: a base-changed
relation over the chart becomes, over `A`, a combination of the `k_j`, and clearing denominators
turns that into a combination with coefficients in `R[x_1, …, x_n]` at the cost of one nonzero
factor from `R`, which the torsion freeness of the flat quotient then cancels; the same move turns
the saturation witnesses into nonzero elements `w_1, …, w_m` of `R`.  Rescaling the chart by
`∏ w_j` leaves the chart ring untouched and makes the new denominator divisible by every `w_j`, so
the first power of the denominator carries the whole relation submodule into `Z`, which is exactly
the hypothesis that
`Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_mvPolynomial` needs.  That
  gives clause (4) for
a polynomial algebra.  For a general finite type `S = R[x_1, …, x_n]/J` one applies the polynomial
case to the module `N = S ⊕ M` over `R[x_1, …, x_n]` and reads off the two summands.

## Main definitions

* `Stacks.Flatness.BlowupFlattening.chartBlowupToVal`: the inclusion of the quotient model `Blowup
  c.I c.a` of an
  admissible chart into the valuation ring.
* `Stacks.Flatness.BlowupFlattening.blowupRescaleAlgEquiv`: the quotient models of `(I, a)` and of
  the rescaled pair
  `((x) I, x a)` are isomorphic as `R`-algebras.
* `Stacks.Flatness.BlowupFlattening.baseChangeAlgHom`,
  `Stacks.Flatness.BlowupFlattening.strictTransformAlgMap`,
  `Stacks.Flatness.BlowupFlattening.strictTransformAlgAlgebra`: functoriality of the strict
    transform algebra in the
  algebra, so that the strict transform of `S` is an algebra over the strict transform of
  `R[x_1, …, x_n]`.
* `Stacks.Flatness.BlowupFlattening.prodLinearEquiv`,
  `Stacks.Flatness.BlowupFlattening.strictTransformAlgLinearEquiv`: the identifications
  `strictTransform.prodEquiv` and `strictTransformAlg.linearEquivStrictTransform` with their
  linearity upgraded from `R[I/a]` to the strict transform of `R[x_1, …, x_n]`.

## Main results

* `Stacks.Flatness.BlowupFlattening.exists_smul_mem_of_vecMap_mem_span`: **denominator clearing.**
  A relation that holds
  after applying an injective `R`-algebra map to the coefficients holds already, up to a nonzero
  factor from `R`.
* `Stacks.Flatness.BlowupFlattening.exists_saturating_family`: **the valuation-ring step.** Over a
  valuation ring `V`
  and a finite type `V`-algebra `W`, the saturation of any submodule of `Wʳ` is finitely generated
  and the quotient by it is flat over `V`.
* `Stacks.Flatness.BlowupFlattening.le_span_and_exists_smul_mem_relSpanOf`: the comparison of the
  descended relations
  with the base change of a fixed presentation of `M`.
* `Stacks.Flatness.BlowupFlattening.exists_chart_relations`: the relation data on the quotient
  model of a chart.
* `Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_of_dvd`,
  `Stacks.Flatness.BlowupFlattening.exists_admissiblePair_mvPolynomial`: **clause (4) for a
    polynomial algebra.**
* `Stacks.Flatness.BlowupFlattening.stacks053I`: **Stacks Tag 053I.**

## Implementation notes

Statements are formulated over abstract coefficient rings wherever possible and instantiated at
`Blowup c.I c.a` only at the end: unification against `Stacks.AffineBlowup.chartRing c`, which
  unfolds to a
subring of `K` cut out by `Stacks.AffineBlowup.affineBlowupImage`, and against a syntactically
  large chart
such as `Blowup (Ideal.span {x} * c.I) (x * c.a)` diverges — the same phenomenon recorded in the
implementation notes of `StacksFrontier.RingTheory.Flat.BlowupDescent`.  For the same reason the
rescaled chart is introduced as an opaque `Stacks.AffineBlowup.AdmissibleChart` rather than by its
formula.

The formalized statement deviates from the source in two ways: the hypothesis `𝔪 ≠ 0`,
without which the conclusion is unsatisfiable, and clause (4) being read over `R[I/a]` rather than
over `R`.

## References

* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
* [Stacks Project, Tag 052M](https://stacks.math.columbia.edu/tag/052M)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 053E](https://stacks.math.columbia.edu/tag/053E)
* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Flatness.BlowupFlattening

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ### Componentwise transport of spans along a map of coefficient rings -/

section SpanTransport

variable {B : Type*} [CommRing B] {D : Type*} [CommRing D] {n r : ℕ}

/-- Componentwise application of a ring homomorphism to the coefficients is compatible with the
action of the base ring: it carries the `B`-action on `B[x_1, …, x_n]ʳ` to the `D`-action on
`D[x_1, …, x_n]ʳ` along `φ`. -/
theorem vecMap_smul_base (φ : B →+* D) (b : B) (v : Fin r → MvPolynomial (Fin n) B) :
    vecMap n r φ (b • v) = φ b • vecMap n r φ v := by
  funext i
  show MvPolynomial.map φ (b • v i) = φ b • MvPolynomial.map φ (v i)
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

/-- The `B`-action on `B[x_1, …, x_n]ʳ` is the restriction of the action of the polynomial
ring. -/
theorem smul_base_eq_algebraMap_smul (b : B) (v : Fin r → MvPolynomial (Fin n) B) :
    b • v = (algebraMap B (MvPolynomial (Fin n) B) b) • v := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

/-- **Componentwise `MvPolynomial.map` carries spans into spans.** If `v` lies in the span of a
set `W` of vectors over `B`, then its componentwise image lies in the span, over the polynomial
ring on `D`, of the componentwise image of `W`. -/
theorem mem_span_vecMap_of_mem_span (φ : B →+* D)
    (W : Set (Fin r → MvPolynomial (Fin n) B)) {v : Fin r → MvPolynomial (Fin n) B}
    (hv : v ∈ Submodule.span (MvPolynomial (Fin n) B) W) :
    vecMap n r φ v ∈ Submodule.span (MvPolynomial (Fin n) D) (vecMap n r φ '' W) := by
  induction hv using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u u' _ _ hu hu' => rw [map_add]; exact Submodule.add_mem _ hu hu'
  | smul c u _ hu => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hu

/-- Componentwise application of the inverse of a ring isomorphism and of the isomorphism
cancel. -/
theorem vecMap_vecMap_symm (φ : B ≃+* D) (v : Fin r → MvPolynomial (Fin n) D) :
    vecMap n r (φ : B →+* D) (vecMap n r (φ.symm : D →+* B) v) = v := by
  rw [vecMap_vecMap,
    show (φ : B →+* D).comp (φ.symm : D →+* B) = RingHom.id D from
      RingHom.ext φ.apply_symm_apply,
    vecMap_id]

/-- Componentwise application of a ring isomorphism and of its inverse cancel. -/
theorem vecMap_symm_vecMap (φ : B ≃+* D) (v : Fin r → MvPolynomial (Fin n) B) :
    vecMap n r (φ.symm : D →+* B) (vecMap n r (φ : B →+* D) v) = v :=
  vecMap_vecMap_symm φ.symm v

/-- **Componentwise transport of spans along a ring isomorphism.** For `φ : B ≃+* D` a vector over
`B` lies in the span of a set `W` exactly when its componentwise image lies in the span of the
componentwise image of `W`. -/
theorem mem_span_vecMap_iff (φ : B ≃+* D) (W : Set (Fin r → MvPolynomial (Fin n) B))
    {v : Fin r → MvPolynomial (Fin n) B} :
    vecMap n r (φ : B →+* D) v ∈ Submodule.span (MvPolynomial (Fin n) D)
        (vecMap n r (φ : B →+* D) '' W) ↔
      v ∈ Submodule.span (MvPolynomial (Fin n) B) W := by
  refine ⟨fun h => ?_, mem_span_vecMap_of_mem_span _ W⟩
  have h' := mem_span_vecMap_of_mem_span (φ.symm : D →+* B) _ h
  rw [Set.image_image] at h'
  simp only [vecMap_symm_vecMap] at h'
  rwa [Set.image_id'] at h'

end SpanTransport

/-! ### Descent of a relation along an injective map of coefficient rings -/

section Descent

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B] {V : Type w}
  [CommRing V] [Algebra R V] {n r : ℕ}

/-- **Descent of a relation, after clearing denominators.** Let `ψ : B → V` be an injective
`R`-algebra map for which denominators can be cleared, in the sense that finitely many
polynomials over `V` become polynomials over `R` after multiplication by one nonzero element of
`R` (this is `Stacks.Flatness.BlowupFlattening.exists_common_denominator` when `V` is a valuation
  ring inside the
fraction field of `R`).  Let `N` be a submodule of `B[x_1, …, x_n]ʳ` and let `v` be a vector whose
componentwise image over `V` lies in the span of the componentwise image of `N`.  Then a nonzero
multiple of `v` by an element of `R` already lies in `N`.

This is the move that makes the last step of Stacks Tag 053I go: relations that hold over the
valuation ring hold over a chart, up to a factor coming from `R`, which the torsion freeness
supplied by flatness then cancels. -/
theorem exists_smul_mem_of_vecMap_mem_span (ψ : B →+* V) (hψ : Function.Injective ψ)
    (hψalg : ∀ x : R, ψ (algebraMap R B x) = algebraMap R V x)
    (hclear : ∀ (t : ℕ) (γ : Fin t → MvPolynomial (Fin n) V), ∃ s : R, s ≠ 0 ∧
      ∀ i, ∃ q : MvPolynomial (Fin n) R, MvPolynomial.map (algebraMap R V) q = s • γ i)
    (N : Submodule (MvPolynomial (Fin n) B) (Fin r → MvPolynomial (Fin n) B))
    {v : Fin r → MvPolynomial (Fin n) B}
    (hv : vecMap n r ψ v ∈ Submodule.span (MvPolynomial (Fin n) V)
      (vecMap n r ψ '' (N : Set (Fin r → MvPolynomial (Fin n) B)))) :
    ∃ s : R, s ≠ 0 ∧ algebraMap R B s • v ∈ N := by
  classical
  obtain ⟨t, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  choose w hwN hw using fun i => (g i).2
  obtain ⟨s, hs0, hq⟩ := hclear t f
  choose q hqf using hq
  refine ⟨s, hs0, ?_⟩
  have hsmul : ∀ (p : MvPolynomial (Fin n) V) (y : Fin r → MvPolynomial (Fin n) V),
      (s • p) • y = algebraMap R V s • (p • y) := fun p y => by
    rw [← algebraMap_smul V s p, smul_assoc]
  have key : vecMap n r ψ (algebraMap R B s • v) =
      vecMap n r ψ (∑ i, MvPolynomial.map (algebraMap R B) (q i) • w i) := by
    rw [vecMap_smul_base, hψalg, map_sum]
    have hstep : ∀ i : Fin t,
        vecMap n r ψ (MvPolynomial.map (algebraMap R B) (q i) • w i) =
          algebraMap R V s • (f i • vecMap n r ψ (w i)) := by
      intro i
      rw [map_smulₛₗ, MvPolynomial.map_map,
        show (ψ.comp (algebraMap R B) : R →+* V) = algebraMap R V from
          RingHom.ext hψalg, hqf i, hsmul]
    rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.smul_sum]
    congr 1
    rw [← hfg]
    exact Finset.sum_congr rfl fun i _ => by rw [hw i]
  have hmem : (∑ i, MvPolynomial.map (algebraMap R B) (q i) • w i) ∈ N :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwN i)
  rwa [vecMap_injective n r ψ hψ key]

end Descent

/-! ### The saturation of a relation submodule over a valuation ring -/

section AbstractSaturation

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {W : Type v} [CommRing W]
  [Algebra V W] [Algebra.FiniteType V W] {r : ℕ}

/-- **The saturation of a relation submodule over a valuation ring is finitely generated.** Let
`V` be a valuation ring, `W` a `V`-algebra of finite type and `Z` any `W`-submodule of `Wʳ`.  Let
`L` be the saturation of `Z`, that is, the set of vectors carried into `Z` by a nonzero element of
`V`.  Then `L` is spanned by finitely many vectors `k_1, …, k_m`, and `Wʳ / L` is flat over `V`.

Indeed `Wʳ / L` is the quotient of `Wʳ / Z` by its `V`-torsion, so it is flat over `V` by
Stacks Tags 0537 and 0539 (`Module.instFlatTorsionFreeQuot`) and finitely presented over `W` by
Nagata's theorem, Stacks Tag 053E (`Module.instFinitePresentationTorsionFreeQuot`); the latter is
what makes `L` finitely generated.

This is the valuation-ring step of Stacks Tag 053I in the shape the rest of the argument
consumes: `V` is the valuation ring `A`, `W` the polynomial ring `A[x_1, …, x_n]`, and `Z` the
relation submodule of the base change to `A[x_1, …, x_n]` of a presentation of `M`, so that
`Wʳ / Z` is `A[x_1, …, x_n] ⊗_{R[x_1, …, x_n]} M` and `Wʳ / L` is the valuation-ring model. -/
theorem exists_saturating_family (Z : Submodule W (Fin r → W)) :
    ∃ (m : ℕ) (k : Fin m → (Fin r → W)),
      Z ≤ Submodule.span W (Set.range k) ∧
        (∀ v ∈ Submodule.span W (Set.range k), ∃ α : V, α ≠ 0 ∧ α • v ∈ Z) ∧
        Module.Flat V ((Fin r → W) ⧸ Submodule.span W (Set.range k)) := by
  have hZL : Z ≤ Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z)) := by
    intro v hv
    rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Z).mpr hv]
    exact Submodule.zero_mem _
  have hmap : (Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z))).map Z.mkQ =
      Module.baseTorsion V W ((Fin r → W) ⧸ Z) :=
    Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
  have E : ((Fin r → W) ⧸ Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z)))
      ≃ₗ[W] Module.torsionFreeQuot V W ((Fin r → W) ⧸ Z) :=
    (Submodule.quotientQuotientEquivQuotient Z _ hZL).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hmap
  have hflat : Module.Flat V
      ((Fin r → W) ⧸ Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z))) :=
    Module.Flat.of_linearEquiv (E.restrictScalars V)
  have hfp : Module.FinitePresentation W
      ((Fin r → W) ⧸ Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z))) :=
    Module.FinitePresentation.of_equiv E.symm
  have hfg : (Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z))).FG := by
    have h := Module.FinitePresentation.fg_ker
      (Submodule.comap Z.mkQ (Module.baseTorsion V W ((Fin r → W) ⧸ Z))).mkQ
      (Submodule.mkQ_surjective _)
    rwa [Submodule.ker_mkQ] at h
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨m, k, hk ▸ hZL, fun v hv => ?_, hk ▸ hflat⟩
  rw [hk] at hv
  obtain ⟨α, hα⟩ := Submodule.mem_comap.mp hv
  refine ⟨(α : V), nonZeroDivisors.ne_zero α.2, ?_⟩
  have h0 : algebraMap V W (α : V) • Z.mkQ v = 0 := by
    rw [algebraMap_smul]
    exact hα
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul] at h0
  have h1 := (Submodule.Quotient.mk_eq_zero Z).mp h0
  rwa [algebraMap_smul] at h1

end AbstractSaturation

/-! ### Comparing the relations over a chart with the relations over the valuation ring -/

section AbstractChart

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B] {V : Type w}
  [CommRing V] [Algebra R V] {n r : ℕ}

/-- Componentwise application of an `R`-algebra map to the coefficients commutes with the base
change of a vector of polynomials over `R`. -/
theorem vecMap_freeBaseChange (ψ : B →+* V)
    (hψalg : ∀ t : R, ψ (algebraMap R B t) = algebraMap R V t)
    (v : Fin r → MvPolynomial (Fin n) R) :
    vecMap n r ψ (freeBaseChange (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r v) =
      freeBaseChange (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r v := by
  funext i
  simp only [vecMap_apply, freeBaseChange_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_map]
  rw [show (ψ.comp (algebraMap R B) : R →+* V) = algebraMap R V from RingHom.ext hψalg]

variable (ψ : B →+* V) (hψalg : ∀ t : R, ψ (algebraMap R B t) = algebraMap R V t)
  (Z : Submodule (MvPolynomial (Fin n) R) (Fin r → MvPolynomial (Fin n) R))

include hψalg in
/-- Componentwise application of an `R`-algebra map carries the base change of `Z` to `B` onto the
base change of `Z` to `V`. -/
theorem vecMap_image_freeBaseChange_image :
    vecMap n r ψ ''
        (freeBaseChange (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r ''
          (Z : Set (Fin r → MvPolynomial (Fin n) R))) =
      freeBaseChange (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r ''
        (Z : Set (Fin r → MvPolynomial (Fin n) R)) := by
  rw [Set.image_image]
  exact Set.image_congr' (fun z => vecMap_freeBaseChange ψ hψalg z)

include hψalg in
/-- The base-changed relations over `B` are carried into the base-changed relations over `V`. -/
theorem vecMap_mem_relSpanOf {v : Fin r → MvPolynomial (Fin n) B}
    (hv : v ∈ relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r Z) :
    vecMap n r ψ v ∈ relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r Z := by
  have h := mem_span_vecMap_of_mem_span ψ _ hv
  rwa [vecMap_image_freeBaseChange_image ψ hψalg Z] at h

include hψalg in
/-- The base-changed relations over `V` lie in the span of the componentwise image of the
base-changed relations over `B`. -/
theorem relSpanOf_le_span_vecMap_image :
    relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r Z ≤
      Submodule.span (MvPolynomial (Fin n) V) (vecMap n r ψ ''
        (relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r Z :
          Set (Fin r → MvPolynomial (Fin n) B))) := by
  rw [relSpanOf, ← vecMap_image_freeBaseChange_image ψ hψalg Z]
  exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end AbstractChart

/-! ### The relation submodule on a chart -/

section ChartPackage

variable {R : Type u} [CommRing R] [IsDomain R] {B : Type v} [CommRing B] [IsDomain B]
  [Algebra R B] {V : Type w} [CommRing V] [Algebra R V] {n r m : ℕ} {M : Type*} [AddCommGroup M]
  [Module (MvPolynomial (Fin n) R) M]

/-- **The hypotheses of clause (4) of Stacks Tag 053I, descended from the valuation ring to a
chart.** Let `π : R[x_1, …, x_n]ʳ → M` be a surjection, let `ψ : B → V` be an injective
`R`-algebra map for which denominators can be cleared, and suppose given relation vectors
`k_1, …, k_m` over `V` and `k'_1, …, k'_m` over `B` with `ψ(k'_j) = k_j` such that

* the base-changed relations over `V` lie in the span of the `k_j`,
* each `k_j` is killed, modulo the base-changed relations over `V`, by a nonzero element of `R`,
* the quotient of `B[x_1, …, x_n]ʳ` by the span of the `k'_j` is flat over `B`.

Then the base-changed relations over `B` lie in the span of the `k'_j`, and each `k'_j` is killed,
modulo those relations, by a nonzero element of `R`.

These are the hypotheses `hZL` and (after enlarging the denominator of the chart, so that a single
power of it is divisible by the finitely many elements produced here) `hLsat` of
`Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_mvPolynomial`.  Both
  statements are proved by
`Stacks.Flatness.BlowupFlattening.exists_smul_mem_of_vecMap_mem_span`; in the first the resulting
  factor from `R` is
cancelled against the torsion freeness that flatness supplies (Stacks Tag 0538), while in the
second it is retained. -/
theorem le_span_and_exists_smul_mem_relSpanOf
    {π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M} (ψ : B →+* V)
    (hψ : Function.Injective ψ) (hψalg : ∀ t : R, ψ (algebraMap R B t) = algebraMap R V t)
    (hRB : ∀ t : R, t ≠ 0 → algebraMap R B t ≠ 0)
    (hclear : ∀ (t : ℕ) (γ : Fin t → MvPolynomial (Fin n) V), ∃ s : R, s ≠ 0 ∧
      ∀ i, ∃ q : MvPolynomial (Fin n) R, MvPolynomial.map (algebraMap R V) q = s • γ i)
    (k : Fin m → (Fin r → MvPolynomial (Fin n) V))
    (k₁ : Fin m → (Fin r → MvPolynomial (Fin n) B)) (hk : ∀ j, vecMap n r ψ (k₁ j) = k j)
    (hZk : relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r (LinearMap.ker π) ≤
      Submodule.span (MvPolynomial (Fin n) V) (Set.range k))
    (hsatV : ∀ j, ∃ y : R, y ≠ 0 ∧ algebraMap R V y • k j ∈
      relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) V) r (LinearMap.ker π))
    (hflat : Module.Flat B ((Fin r → MvPolynomial (Fin n) B) ⧸
      Submodule.span (MvPolynomial (Fin n) B) (Set.range k₁))) :
    relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r (LinearMap.ker π) ≤
        Submodule.span (MvPolynomial (Fin n) B) (Set.range k₁) ∧
      ∀ j, ∃ w : R, w ≠ 0 ∧ algebraMap R B w • k₁ j ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r (LinearMap.ker π) := by
  have htf : Module.IsTorsionFree B ((Fin r → MvPolynomial (Fin n) B) ⧸
    Submodule.span (MvPolynomial (Fin n) B) (Set.range k₁)) := Module.Flat.isTorsionFree
  refine ⟨fun v hv => ?_, fun j => ?_⟩
  · have h1 : vecMap n r ψ v ∈ Submodule.span (MvPolynomial (Fin n) V)
        (vecMap n r ψ '' (Submodule.span (MvPolynomial (Fin n) B) (Set.range k₁) :
          Set (Fin r → MvPolynomial (Fin n) B))) := by
      refine Submodule.span_mono ?_ (hZk (vecMap_mem_relSpanOf ψ hψalg (LinearMap.ker π) hv))
      rintro _ ⟨j, rfl⟩
      exact ⟨k₁ j, Submodule.subset_span ⟨j, rfl⟩, hk j⟩
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem_of_vecMap_mem_span ψ hψ hψalg hclear _ h1
    exact mem_of_smul_mem
      ((Submodule.span (MvPolynomial (Fin n) B) (Set.range k₁)).restrictScalars B)
      (hRB s hs0) htf hs
  · obtain ⟨y, hy0, hy⟩ := hsatV j
    have h1 : vecMap n r ψ (algebraMap R B y • k₁ j) ∈ Submodule.span (MvPolynomial (Fin n) V)
        (vecMap n r ψ '' (relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r
          (LinearMap.ker π) : Set (Fin r → MvPolynomial (Fin n) B))) := by
      rw [vecMap_smul_base, hψalg, hk j]
      exact relSpanOf_le_span_vecMap_image ψ hψalg (LinearMap.ker π) hy
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem_of_vecMap_mem_span ψ hψ hψalg hclear _ h1
    refine ⟨s * y, mul_ne_zero hs0 hy0, ?_⟩
    rwa [map_mul, mul_smul]

end ChartPackage

/-! ### Transport of the relation data along an isomorphism of the chart -/

section RingEquivTransport

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B] {D : Type w}
  [CommRing D] [Algebra R D] {n r : ℕ} {M : Type*} [AddCommGroup M]
  [Module (MvPolynomial (Fin n) R) M]

/-- **The base-changed relations are transported along an isomorphism of the coefficients.** For
`φ : B ≃+* D` compatible with the maps from `R`, a vector over `B` lies in the base change of `Z`
to `B[x_1, …, x_n]` exactly when its componentwise image lies in the base change of `Z` to
`D[x_1, …, x_n]`. -/
theorem mem_relSpanOf_vecMap_iff (φ : B ≃+* D)
    (hφ : ∀ t : R, φ (algebraMap R B t) = algebraMap R D t)
    (Z : Submodule (MvPolynomial (Fin n) R) (Fin r → MvPolynomial (Fin n) R))
    {v : Fin r → MvPolynomial (Fin n) B} :
    vecMap n r (φ : B →+* D) v ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) D) r Z ↔
      v ∈ relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) B) r Z := by
  rw [show relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) D) r Z =
      Submodule.span (MvPolynomial (Fin n) D)
        (freeBaseChange (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) D) r ''
          (Z : Set (Fin r → MvPolynomial (Fin n) R))) from rfl,
    ← vecMap_image_freeBaseChange_image (φ : B →+* D) hφ Z]
  exact mem_span_vecMap_iff φ _

end RingEquivTransport

/-! ### The quotient model of a chart inside the valuation ring -/

section ChartToVal

open Stacks.AffineBlowup

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

/-- **The quotient model of an admissible chart sits inside the valuation ring.** This is the
bridge `Stacks.AffineBlowup.AdmissibleChart.blowupRingEquiv` from `Blowup c.I c.a` to the chart
  ring,
followed by the inclusion `Stacks.AffineBlowup.chartToVal` of the chart ring into `A`. -/
noncomputable def chartBlowupToVal (c : AdmissibleChart R A) : Blowup c.I c.a →+* valRing A :=
  (chartToVal c).comp (AdmissibleChart.blowupRingEquiv c).toRingHom

omit [IsDomain R] in
/-- The inclusion of the quotient model of a chart into the valuation ring is injective, both of
its factors being so. -/
theorem chartBlowupToVal_injective (c : AdmissibleChart R A) :
    Function.Injective (chartBlowupToVal c) :=
  (chartToVal_injective c).comp (AdmissibleChart.blowupRingEquiv c).injective

omit [IsDomain R] in
/-- The inclusion of the quotient model of a chart into the valuation ring is a map of
`R`-algebras: both factors are, the second because
  `Stacks.AffineBlowup.blowupEquivAffineBlowupImage'` is
an isomorphism of `R`-algebras and the first because it does not move the underlying element
of `K`. -/
theorem chartBlowupToVal_algebraMap (hdom : Dominates R A) (c : AdmissibleChart R A) (t : R) :
    letI := hdom.algebra
    chartBlowupToVal c (algebraMap R (Blowup c.I c.a) t) = algebraMap R (valRing A) t := by
  let _ := hdom.algebra
  refine Subtype.ext ?_
  show ((AdmissibleChart.blowupRingEquiv c (algebraMap R (Blowup c.I c.a) t) : chartRing c) : K)
    = algebraMap R K t
  rw [AdmissibleChart.blowupRingEquiv]
  show ((blowupEquivAffineBlowupImage' (K := K) c.a_ne_zero
    (algebraMap R (Blowup c.I c.a) t) : affineBlowupImageAlg c.I c.a c.ha) : K) = algebraMap R K t
  rw [AlgEquiv.commutes]
  rfl

end ChartToVal

/-! ### Enlarging the denominator of a chart -/

section Rescale

open Stacks.AffineBlowup

/-- **The quotient model of a rescaled pair is the quotient model of the pair.** For `R` a domain
with fraction field `K`, `0 ≠ a ∈ I` and `x ≠ 0`, the two quotient models
`Blowup ((x) I) (x a)` and `Blowup I a` are isomorphic as `R`-algebras:
`Stacks.AffineBlowup.blowupEquivAffineBlowupImage'` carries both onto the same subalgebra of `K`,
by `Stacks.AffineBlowup.affineBlowupImageAlg_rescale`.

Rescaling is the move of Stacks Tag 053I that makes the denominator of the chart divisible by a
prescribed nonzero element of `R`, without moving the chart; see
`StacksFrontier.RingTheory.AffineBlowup.Rescale`. -/
noncomputable def blowupRescaleAlgEquiv {R : Type u} [CommRing R] [IsDomain R] {K : Type v}
    [Field K] [Algebra R K] [IsFractionRing R K] {I : Ideal R} {a x : R} [Fact (a ∈ I)]
    [Fact (x * a ∈ Ideal.span {x} * I)] (hx : x ≠ 0) (ha0 : a ≠ 0) :
    Blowup (Ideal.span {x} * I) (x * a) ≃ₐ[R] Blowup I a :=
  (blowupEquivAffineBlowupImage' (K := K) (mul_ne_zero hx ha0)).trans
    ((Subalgebra.equivOfEq _ _
        (affineBlowupImageAlg_rescale (K := K) hx Fact.out Fact.out)).trans
      (blowupEquivAffineBlowupImage' (K := K) ha0).symm)

end Rescale

/-! ### The polynomial case of Stacks Tag 053I -/

section PolynomialCase

open Stacks.AffineBlowup

/-- **Clause (4) of Stacks Tag 053I for a polynomial algebra, from relation data on the chart.**
Let `C = R[I/a]` be a chart which is a domain, let `π : R[x_1, …, x_n]ʳ → M` be a surjection and
let `k_1, …, k_m` be vectors in `C[x_1, …, x_n]ʳ` such that

* the base-changed relations lie in the span `L` of the `k_j`,
* each `k_j` is killed, modulo those relations, by the image of a divisor of `a` in `R`, and
* `C[x_1, …, x_n]ʳ / L` is flat over `C`.

Then the strict transforms of `R[x_1, …, x_n]` and of `M` satisfy clause (4) of Stacks Tag 053I.

Divisibility of `a` is what replaces the hypothesis `hLsat` of
`Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_mvPolynomial`: the first
  power of the image of
`a` already carries every `k_j`, hence every element of `L`, into the base-changed relations.  It
is arranged by rescaling the chart, `Stacks.AffineBlowup.AdmissibleChart.rescale`. -/
theorem strictTransformFlatFinitePresentation_of_dvd {R : Type u} [CommRing R] {I : Ideal R}
    {a : R} [Fact (a ∈ I)] [IsDomain (Blowup I a)] {n r m : ℕ} (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    {π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M}
    (hπ : Function.Surjective π) (k : Fin m → (Fin r → MvPolynomial (Fin n) (Blowup I a)))
    (hZL : relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
      (LinearMap.ker π) ≤ Submodule.span (MvPolynomial (Fin n) (Blowup I a)) (Set.range k))
    (hsat : ∀ j, ∃ w : R, w ∣ a ∧ algebraMap R (Blowup I a) w • k j ∈
      relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r (LinearMap.ker π))
    (hflat : Module.Flat (Blowup I a) ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸
      Submodule.span (MvPolynomial (Fin n) (Blowup I a)) (Set.range k))) :
    StrictTransformFlatFinitePresentation I a (MvPolynomial (Fin n) R) M := by
  have hgen : ∀ v ∈ Submodule.span (MvPolynomial (Fin n) (Blowup I a)) (Set.range k),
      algebraMap R (Blowup I a) a • v ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
          (LinearMap.ker π) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      obtain ⟨y, ⟨d, hd⟩, hmem⟩ := hsat j
      rw [show algebraMap R (Blowup I a) a =
          algebraMap R (Blowup I a) d * algebraMap R (Blowup I a) y from by
            rw [← map_mul, mul_comm, ← hd],
        mul_smul, smul_base_eq_algebraMap_smul]
      exact Submodule.smul_mem _ _ hmem
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add u u' _ _ hu hu' => rw [smul_add]; exact Submodule.add_mem _ hu hu'
    | smul p u _ hu =>
      rw [smul_base_eq_algebraMap_smul, smul_comm, ← smul_base_eq_algebraMap_smul]
      exact Submodule.smul_mem _ _ hu
  exact strictTransformFlatFinitePresentation_mvPolynomial I a n M hπ _ hZL
    (fun v hv => ⟨1, by rw [pow_one]; exact hgen v hv⟩)
    (Submodule.fg_span (Set.finite_range _)) hflat

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

omit [IsDomain R] in
/-- The structure map of the valuation ring is injective, being the restriction of the injective
`algebraMap R K`. -/
theorem algebraMap_valRing_injective (hdom : Dominates R A) :
    letI := hdom.algebra
    Function.Injective (algebraMap R (valRing A)) := fun _ _ h =>
  IsFractionRing.injective R K (congrArg (fun z : valRing A => (z : K)) h)

/-- **The relation data on the quotient model of a chart.** For `(R, 𝔪)` a local domain with
fraction field `K` and `𝔪 ≠ 0`, `A ⊆ K` a valuation ring dominating `R`, `M` a module over
`R[x_1, …, x_n]` and `π : R[x_1, …, x_n]ʳ → M` any linear map, there are an admissible chart `c`
and finitely many vectors over the quotient model `Blowup c.I c.a` of its chart whose span
contains the base-changed relations of `π`, each of which is killed modulo those relations by a
nonzero element of `R`, and such that the corresponding quotient is flat over
`Blowup c.I c.a`.

This is the whole descent chain: `Stacks.Flatness.BlowupFlattening.exists_saturating_family` over
  the valuation ring
(Stacks Tags 0537, 0539, 053E), `Stacks.Flatness.BlowupFlattening.exists_chart_relGenTop_eq` for
  the coefficients,
`Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient` for flatness (Stacks Tag 02JO (3)),
`Stacks.Flatness.BlowupFlattening.flat_quotient_of_ringEquiv` to pass to the quotient model, and
`Stacks.Flatness.BlowupFlattening.le_span_and_exists_smul_mem_relSpanOf` to compare with the base
  change of `π`. -/
theorem exists_chart_relations (hdom : Dominates R A) (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (n : ℕ) (M : Type w) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] {r : ℕ}
    (π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    ∃ (m : ℕ) (c : AdmissibleChart R A)
      (k : Fin m → (Fin r → MvPolynomial (Fin n) (Blowup c.I c.a))),
      relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup c.I c.a)) r
          (LinearMap.ker π) ≤
        Submodule.span (MvPolynomial (Fin n) (Blowup c.I c.a)) (Set.range k) ∧
      (∀ j, ∃ y : R, y ≠ 0 ∧ algebraMap R (Blowup c.I c.a) y • k j ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup c.I c.a)) r
          (LinearMap.ker π)) ∧
      Module.Flat (Blowup c.I c.a) ((Fin r → MvPolynomial (Fin n) (Blowup c.I c.a)) ⧸
        Submodule.span (MvPolynomial (Fin n) (Blowup c.I c.a)) (Set.range k)) := by
  classical
  let _ := hdom.algebra
  let _ : ValuationRing (valRing A) := inferInstanceAs (ValuationRing A)
  have hRV : Function.Injective (algebraMap R (valRing A)) := algebraMap_valRing_injective hdom
  -- The relations over the valuation ring, with their saturation witnesses.
  obtain ⟨m, k, hZk, hsat, hflatA⟩ := exists_saturating_family (V := valRing A)
    (W := MvPolynomial (Fin n) (valRing A))
    (relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (valRing A)) r (LinearMap.ker π))
  -- Clearing denominators turns the saturation witnesses into nonzero elements of `R`.
  have hsatR : ∀ j, ∃ y : R, y ≠ 0 ∧ algebraMap R (valRing A) y • k j ∈
      relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (valRing A)) r
        (LinearMap.ker π) := by
    intro j
    obtain ⟨α, hα0, hαmem⟩ := hsat (k j) (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨b, y, hy⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) (S := K)
      ((α : valRing A) : K)
    have hbK : algebraMap R K (b : R) ≠ 0 := fun h =>
      nonZeroDivisors.ne_zero b.2 (IsFractionRing.to_map_eq_zero_iff.mp h)
    have hαK : ((α : valRing A) : K) ≠ 0 := fun h => hα0 (Subtype.ext h)
    have hyK : algebraMap R K y = algebraMap R K (b : R) * ((α : valRing A) : K) := by
      rw [hy, Algebra.smul_def]
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, map_zero] at hyK
      exact (mul_ne_zero hbK hαK) hyK.symm
    refine ⟨y, hy0, ?_⟩
    rw [show algebraMap R (valRing A) y = algebraMap R (valRing A) (b : R) * α from
      Subtype.ext hyK, mul_smul, smul_base_eq_algebraMap_smul]
    exact Submodule.smul_mem _ _ hαmem
  -- Descend the relations to a chart, and flatness with them.
  obtain ⟨c₀, k₀, hk₀⟩ := exists_chart_relGenTop_eq hm hdom k
  have hflatA' : Module.Flat (valRing A)
      ((Fin r → MvPolynomial (Fin n) (valRing A)) ⧸ relSpanTop k₀) := by
    rw [show relSpanTop k₀ = Submodule.span (MvPolynomial (Fin n) (valRing A))
      (Set.range k) from by
        rw [show relSpanTop k₀ = Submodule.span (MvPolynomial (Fin n) (valRing A))
          (Set.range (relGenTop k₀)) from rfl, hk₀]]
    exact hflatA
  obtain ⟨c, hc, hflatc⟩ := exists_chart_flat_quotient hm hdom c₀ k₀ hflatA'
  -- Carry the descended flat model onto the quotient model of the chart.
  obtain ⟨k₁, hkk, hflat₁⟩ : ∃ k₁ : Fin m → (Fin r → MvPolynomial (Fin n) (Blowup c.I c.a)),
      (∀ j, vecMap n r (chartBlowupToVal c) (k₁ j) = k j) ∧
        Module.Flat (Blowup c.I c.a) ((Fin r → MvPolynomial (Fin n) (Blowup c.I c.a)) ⧸
          Submodule.span (MvPolynomial (Fin n) (Blowup c.I c.a)) (Set.range k₁)) := by
    refine ⟨fun j => vecMap n r (AdmissibleChart.blowupRingEquiv c).symm.toRingHom
      (relGen hc k₀ j), fun j => ?_,
      flat_quotient_of_ringEquiv (AdmissibleChart.blowupRingEquiv c) (relGen hc k₀) hflatc⟩
    rw [vecMap_vecMap,
      show (chartBlowupToVal c).comp ((AdmissibleChart.blowupRingEquiv c).symm.toRingHom) =
        chartToVal c from RingHom.ext fun y => by
          show chartToVal c ((AdmissibleChart.blowupRingEquiv c)
            ((AdmissibleChart.blowupRingEquiv c).symm y)) = chartToVal c y
          rw [RingEquiv.apply_symm_apply],
      show relGen hc k₀ j = vecMap n r (chartMap c₀ c hc) (k₀ j) from rfl, vecMap_vecMap,
      chartToVal_comp_chartMap]
    exact congrFun hk₀ j
  have hdomB : IsDomain (Blowup c.I c.a) := AdmissibleChart.isDomain_blowup c
  obtain ⟨hZL₁, hw⟩ := le_span_and_exists_smul_mem_relSpanOf (π := π) (chartBlowupToVal c)
    (chartBlowupToVal_injective c) (chartBlowupToVal_algebraMap hdom c)
    (fun t ht h => ht (hRV (by rw [← chartBlowupToVal_algebraMap hdom c t, h, map_zero, map_zero])))
    (fun _ γ => exists_common_denominator hdom γ) k k₁ hkk hZk hsatR hflat₁
  exact ⟨m, c, k₁, hZL₁, hw, hflat₁⟩

/-- **Clause (4) of Stacks Tag 053I for a polynomial algebra.** Let `(R, 𝔪)` be a local domain
with fraction field `K` and `𝔪 ≠ 0`, let `A ⊆ K` be a valuation ring dominating `R` and let `M` be
a finite module over `P = R[x_1, …, x_n]`.  Then there is an admissible pair `(I, a)` of
Stacks Tag 052M on whose chart the strict transforms of `P` and of `M` satisfy clause (4).

`Stacks.Flatness.BlowupFlattening.exists_chart_relations` produces a chart together with the
  relation vectors and the
finitely many nonzero elements of `R` that kill them; the chart is then rescaled by the product of
those elements, which does not move the chart ring
(`Stacks.AffineBlowup.AdmissibleChart.subring_rescale`) but makes the new denominator divisible by
  each of
them, and `Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_of_dvd`
concludes.

The conclusion is flatness over the chart, not over `R`, a deviation from the source. -/
theorem exists_admissiblePair_mvPolynomial (hdom : Dominates R A)
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (n : ℕ) (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M] [Module.Finite (MvPolynomial (Fin n) R) M] :
    ∃ (I : Ideal R) (a : R) (ha : a ∈ I),
      IsAdmissiblePair R A I a ha ∧
        @StrictTransformFlatFinitePresentation R _ I a ⟨ha⟩ (MvPolynomial (Fin n) R) _ _
          M _ _ _ _ := by
  classical
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M
  obtain ⟨m, c, k, hZL, hw, hflat⟩ := exists_chart_relations hdom hm n M π
  choose w hw0 hwmem using hw
  have hx0 : (∏ j, w j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hw0 j
  -- Rescale the chart by the product of the `w j`; the chart ring does not move.
  have _ : Fact ((∏ j, w j) * c.a ∈ Ideal.span {∏ j, w j} * c.I) :=
    ⟨mul_mem_span_singleton_mul _ c.a c.I c.ha⟩
  obtain ⟨c', hfact', ⟨e⟩, hdvd⟩ : ∃ (c' : AdmissibleChart R A) (_ : Fact (c'.a ∈ c'.I)),
      Nonempty (Blowup c'.I c'.a ≃ₐ[R] Blowup c.I c.a) ∧ ∀ j, w j ∣ c'.a :=
    ⟨c.rescale hx0, AdmissibleChart.instFactMem _,
      ⟨blowupRescaleAlgEquiv (K := K) hx0 c.a_ne_zero⟩,
      fun j => Dvd.dvd.mul_right (Finset.dvd_prod_of_mem w (Finset.mem_univ j)) c.a⟩
  have _ : Fact (c'.a ∈ c'.I) := hfact'
  have hdomB : IsDomain (Blowup c.I c.a) := AdmissibleChart.isDomain_blowup c
  have hdomB' : IsDomain (Blowup c'.I c'.a) := AdmissibleChart.isDomain_blowup c'
  -- Transport the relation data along the isomorphism of the two quotient models.
  obtain ⟨k', hk', hflat'⟩ : ∃ k' : Fin m → (Fin r → MvPolynomial (Fin n) (Blowup c'.I c'.a)),
      (∀ j, vecMap n r (e.toRingEquiv : Blowup c'.I c'.a →+* Blowup c.I c.a) (k' j) = k j) ∧
        Module.Flat (Blowup c'.I c'.a) ((Fin r → MvPolynomial (Fin n) (Blowup c'.I c'.a)) ⧸
          Submodule.span (MvPolynomial (Fin n) (Blowup c'.I c'.a)) (Set.range k')) :=
    ⟨fun j => vecMap n r (e.toRingEquiv.symm : Blowup c.I c.a →+* Blowup c'.I c'.a) (k j),
      fun j => vecMap_vecMap_symm _ _, flat_quotient_of_ringEquiv e.toRingEquiv k hflat⟩
  have hiff := fun v => mem_relSpanOf_vecMap_iff e.toRingEquiv (fun t => e.commutes t)
    (LinearMap.ker π) (v := v)
  have himg : vecMap n r (e.toRingEquiv : Blowup c'.I c'.a →+* Blowup c.I c.a) ''
      Set.range k' = Set.range k := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hk')
  refine ⟨c'.I, c'.a, c'.ha, c'.adm,
    strictTransformFlatFinitePresentation_of_dvd M hπ k' (fun v hv => ?_) (fun j => ?_) hflat'⟩
  · rw [← mem_span_vecMap_iff e.toRingEquiv, himg]
    exact hZL ((hiff _).mpr hv)
  · refine ⟨w j, hdvd j, (hiff _).mp ?_⟩
    rw [vecMap_smul_base,
      show (e.toRingEquiv : Blowup c'.I c'.a →+* Blowup c.I c.a)
        (algebraMap R (Blowup c'.I c'.a) (w j)) = algebraMap R (Blowup c.I c.a) (w j) from
          e.commutes (w j), hk' j]
    exact hwmem j

end PolynomialCase

/-! ### The strict transform of a quotient of a polynomial algebra -/

section Functoriality

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (P : Type*) [CommRing P]
  [Algebra R P] (S : Type*) [CommRing S] [Algebra R S] [Algebra P S] [IsScalarTower R P S]

/-- **The base change to the chart of the structure map of a `P`-algebra**: the `R[I/a]`-algebra
map `R[I/a] ⊗_R P → R[I/a] ⊗_R S`. -/
noncomputable def baseChangeAlgHom :
    TensorProduct R (Blowup I a) P →ₐ[Blowup I a] TensorProduct R (Blowup I a) S :=
  Algebra.TensorProduct.map (AlgHom.id (Blowup I a) (Blowup I a)) (IsScalarTower.toAlgHom R P S)

/-- The base change of the structure map sends `b ⊗ p` to `b ⊗ f p`, where `f : P → S` is the
structure map. -/
@[simp]
theorem baseChangeAlgHom_tmul (b : Blowup I a) (p : P) :
    baseChangeAlgHom I a P S (b ⊗ₜ[R] p) = b ⊗ₜ[R] algebraMap P S p :=
  Algebra.TensorProduct.map_tmul _ _ _ _

/-- The base change of the structure map is `R[I/a]`-linear, being an `R[I/a]`-algebra map. -/
theorem baseChangeAlgHom_smul (c : Blowup I a) (t : TensorProduct R (Blowup I a) P) :
    baseChangeAlgHom I a P S (c • t) = c • baseChangeAlgHom I a P S t := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]

/-- The base change of a surjection is surjective. -/
theorem baseChangeAlgHom_surjective (hf : Function.Surjective (algebraMap P S)) :
    Function.Surjective (baseChangeAlgHom I a P S) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b s =>
    obtain ⟨p, rfl⟩ := hf s
    exact ⟨b ⊗ₜ[R] p, baseChangeAlgHom_tmul I a P S b p⟩
  | add z z' hz hz' =>
    obtain ⟨u, rfl⟩ := hz
    obtain ⟨u', rfl⟩ := hz'
    exact ⟨u + u', map_add _ _ _⟩

/-- The base change of the structure map carries `a`-power torsion to `a`-power torsion. -/
theorem baseChangeAlgHom_mem_strictTransformIdeal {t : TensorProduct R (Blowup I a) P}
    (ht : t ∈ strictTransformIdeal I a P) :
    baseChangeAlgHom I a P S t ∈ strictTransformIdeal I a S := by
  obtain ⟨N, hN⟩ := (mem_strictTransformIdeal_iff I a P).mp ht
  refine (mem_strictTransformIdeal_iff I a S).mpr ⟨N, ?_⟩
  rw [← baseChangeAlgHom_smul, hN, map_zero]

/-- **The strict transform of the structure map of a `P`-algebra.** The base change carries the
`a`-power torsion of `R[I/a] ⊗_R P` into that of `R[I/a] ⊗_R S`, so it descends to the strict
transform algebras. -/
noncomputable def strictTransformAlgMap :
    strictTransformAlg I a P →ₐ[Blowup I a] strictTransformAlg I a S :=
  Ideal.Quotient.liftₐ (strictTransformIdeal I a P)
    ((strictTransformAlg.mk I a S).comp (baseChangeAlgHom I a P S))
    fun _t ht => (strictTransformAlg.mk_eq_zero_iff I a S).mpr
      (baseChangeAlgHom_mem_strictTransformIdeal I a P S ht)

/-- The strict transform of the structure map sends the class of `t` to the class of the image of
`t` under the base change of the structure map. -/
@[simp]
theorem strictTransformAlgMap_mk (t : TensorProduct R (Blowup I a) P) :
    strictTransformAlgMap I a P S (strictTransformAlg.mk I a P t) =
      strictTransformAlg.mk I a S (baseChangeAlgHom I a P S t) :=
  rfl

/-- The strict transform of a surjection is surjective. -/
theorem strictTransformAlgMap_surjective (hf : Function.Surjective (algebraMap P S)) :
    Function.Surjective (strictTransformAlgMap I a P S) := by
  intro y
  obtain ⟨z, rfl⟩ := strictTransformAlg.mk_surjective I a S y
  obtain ⟨t, rfl⟩ := baseChangeAlgHom_surjective I a P S hf z
  exact ⟨strictTransformAlg.mk I a P t, rfl⟩

/-- The strict transform algebra of `S` as an algebra over the strict transform algebra of `P`,
through `Stacks.Flatness.BlowupFlattening.strictTransformAlgMap`. -/
@[instance_reducible]
noncomputable def strictTransformAlgAlgebra :
    Algebra (strictTransformAlg I a P) (strictTransformAlg I a S) :=
  (strictTransformAlgMap I a P S).toRingHom.toAlgebra

attribute [local instance] strictTransformAlgAlgebra

/-- The `R[I/a]`-algebra structure on the strict transform algebra of `S` is the one induced from
the strict transform algebra of `P`. -/
theorem isScalarTower_strictTransformAlg :
    IsScalarTower (Blowup I a) (strictTransformAlg I a P) (strictTransformAlg I a S) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((strictTransformAlgMap I a P S).commutes c).symm

attribute [local instance] strictTransform.baseChangeModule

/-- **The action of `R[I/a] ⊗_R P` on `R[I/a] ⊗_R S` is multiplication through the base change of
the structure map.** -/
theorem baseChange_smul_eq_mul (t : TensorProduct R (Blowup I a) P)
    (z : TensorProduct R (Blowup I a) S) :
    t • z = baseChangeAlgHom I a P S t * z := by
  induction t using TensorProduct.induction_on with
  | zero => rw [zero_smul, map_zero, zero_mul]
  | add t t' ht ht' => rw [add_smul, ht, ht', map_add, add_mul]
  | tmul b p =>
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, mul_zero]
    | add z z' hz hz' => rw [smul_add, hz, hz', mul_add]
    | tmul c s =>
      rw [strictTransform.baseChange_smul_tmul, baseChangeAlgHom_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module P M] [Module S M]
  [IsScalarTower R P M] [IsScalarTower P S M] [IsScalarTower R S M]

/-- **The action of `R[I/a] ⊗_R P` on `R[I/a] ⊗_R M` factors through `R[I/a] ⊗_R S`**, for `M` an
`S`-module regarded as a `P`-module. -/
theorem baseChange_smul_eq_baseChange_smul (t : TensorProduct R (Blowup I a) P)
    (z : TensorProduct R (Blowup I a) M) :
    t • z = baseChangeAlgHom I a P S t • z := by
  induction t using TensorProduct.induction_on with
  | zero => rw [zero_smul, map_zero, zero_smul]
  | add t t' ht ht' => rw [add_smul, ht, ht', map_add, add_smul]
  | tmul b p =>
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, smul_zero]
    | add z z' hz hz' => rw [smul_add, hz, hz', smul_add]
    | tmul c x =>
      rw [strictTransform.baseChange_smul_tmul, baseChangeAlgHom_tmul,
        strictTransform.baseChange_smul_tmul, IsScalarTower.algebraMap_smul]

/-- The action of the strict transform algebra of `S` on the strict transform of `M` extends the
action of the strict transform algebra of `P`. -/
theorem isScalarTower_strictTransform :
    IsScalarTower (strictTransformAlg I a P) (strictTransformAlg I a S)
      (strictTransform I a M) :=
  IsScalarTower.of_algebraMap_smul fun τ x => by
    obtain ⟨t, rfl⟩ := strictTransformAlg.mk_surjective I a P τ
    obtain ⟨z, rfl⟩ := strictTransform.mkQ_surjective I a M x
    show strictTransformAlgMap I a P S (strictTransformAlg.mk I a P t) • _ = _
    rw [strictTransformAlgMap_mk, strictTransformAlg.mk_smul, strictTransformAlg.mk_smul,
      strictTransform.smul_mkQ, strictTransform.smul_mkQ,
      baseChange_smul_eq_baseChange_smul I a P S M t z]

end Functoriality

/-! ### Reading off the two summands of the strict transform of a product -/

section ProdSplit

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (P : Type*) [CommRing P]
  [Algebra R P] (X : Type*) [AddCommGroup X] [Module R X] [Module P X] [IsScalarTower R P X]
  (Y : Type*) [AddCommGroup Y] [Module R Y] [Module P Y] [IsScalarTower R P Y]

attribute [local instance] strictTransform.baseChangeModule

/-- **The comparison of the base change of a product with the product of the base changes is
linear over `R[I/a] ⊗_R P`**, not merely over `R[I/a]`. -/
theorem prodRight_baseChange_smul (t : TensorProduct R (Blowup I a) P)
    (z : TensorProduct R (Blowup I a) (X × Y)) :
    TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y (t • z) =
      (t • (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y z).1,
        t • (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y z).2) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [Prod.ext_iff]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht']; simp [add_smul]
  | tmul b p =>
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz']; simp [smul_add]
    | tmul c xy =>
      obtain ⟨x, y⟩ := xy
      rw [strictTransform.baseChange_smul_tmul]
      simp [strictTransform.baseChange_smul_tmul]

/-- The identification of the strict transform of a product with the product of the strict
transforms is linear over `R[I/a] ⊗_R P`. -/
theorem prodEquiv_baseChange_smul (t : TensorProduct R (Blowup I a) P)
    (u : strictTransform I a (X × Y)) :
    strictTransform.prodEquiv I a X Y (t • u) = t • strictTransform.prodEquiv I a X Y u := by
  obtain ⟨z, rfl⟩ := strictTransform.mkQ_surjective I a (X × Y) u
  rw [strictTransform.smul_mkQ, strictTransform.prodEquiv_mkQ, strictTransform.prodEquiv_mkQ,
    prodRight_baseChange_smul]
  exact Prod.ext (strictTransform.smul_mkQ I a P X t _).symm
    (strictTransform.smul_mkQ I a P Y t _).symm

/-- The identification of the strict transform of a product with the product of the strict
transforms is linear over the strict transform algebra of `P`. -/
theorem prodEquiv_smul (τ : strictTransformAlg I a P) (u : strictTransform I a (X × Y)) :
    strictTransform.prodEquiv I a X Y (τ • u) = τ • strictTransform.prodEquiv I a X Y u := by
  obtain ⟨t, rfl⟩ := strictTransformAlg.mk_surjective I a P τ
  rw [strictTransformAlg.mk_smul, prodEquiv_baseChange_smul]
  exact (Prod.ext (strictTransformAlg.mk_smul I a P X t _)
    (strictTransformAlg.mk_smul I a P Y t _)).symm

/-- **The strict transform of a product is the product of the strict transforms, linearly over the
strict transform algebra of `P`.** This upgrade of `strictTransform.prodEquiv` is what lets the
finite presentation of the strict transform of `S ⊕ M` over the strict transform of
`R[x_1, …, x_n]` be read off on each summand. -/
noncomputable def prodLinearEquiv :
    strictTransform I a (X × Y) ≃ₗ[strictTransformAlg I a P]
      strictTransform I a X × strictTransform I a Y :=
  AddEquiv.toLinearEquiv (strictTransform.prodEquiv I a X Y).toAddEquiv (prodEquiv_smul I a P X Y)

end ProdSplit

/-! ### The strict transform algebra over the strict transform of the polynomial algebra -/

section AlgLinear

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (S : Type*) [CommRing S]
  [Algebra R S]

/-- **The comparison map between the two readings of the strict transform of an algebra is
bijective.** This is the content of `strictTransformAlg.linearEquivStrictTransform`, isolated so
that the comparison can be upgraded to a map of modules over the strict transform algebra of a
subalgebra. -/
theorem ofStrictTransform_bijective :
    Function.Bijective (strictTransformAlg.ofStrictTransform I a S) := by
  refine ⟨fun u v huv => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl⟩ := strictTransform.mkQ_surjective I a S u
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a S v
    rw [strictTransformAlg.ofStrictTransform_mkQ, strictTransformAlg.ofStrictTransform_mkQ,
      strictTransformAlg.mk_eq_mk_iff] at huv
    exact (Submodule.Quotient.eq _).mpr
      ((mem_strictTransformIdeal_iff_mem_torsionSubmodule I a S).mp huv)
  · obtain ⟨x, rfl⟩ := strictTransformAlg.mk_surjective I a S z
    exact ⟨strictTransform.mkQ I a S x, rfl⟩

variable (P : Type*) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]

attribute [local instance] strictTransformAlgAlgebra strictTransform.baseChangeModule

/-- The comparison map from the strict transform of `S` as a module to the strict transform algebra
of `S` is linear over the strict transform algebra of `P`. -/
theorem ofStrictTransform_smul (τ : strictTransformAlg I a P) (x : strictTransform I a S) :
    strictTransformAlg.ofStrictTransform I a S (τ • x) =
      τ • strictTransformAlg.ofStrictTransform I a S x := by
  obtain ⟨t, rfl⟩ := strictTransformAlg.mk_surjective I a P τ
  obtain ⟨z, rfl⟩ := strictTransform.mkQ_surjective I a S x
  rw [strictTransformAlg.mk_smul, strictTransform.smul_mkQ,
    strictTransformAlg.ofStrictTransform_mkQ, strictTransformAlg.ofStrictTransform_mkQ,
    baseChange_smul_eq_mul I a P S t z, map_mul, Algebra.smul_def]
  rfl

/-- The comparison map from the strict transform of `S` as a module to the strict transform algebra
of `S`, as a map of modules over the strict transform algebra of `P`. -/
noncomputable def ofStrictTransformLinearMap :
    strictTransform I a S →ₗ[strictTransformAlg I a P] strictTransformAlg I a S where
  toFun := strictTransformAlg.ofStrictTransform I a S
  map_add' := map_add _
  map_smul' := ofStrictTransform_smul I a S P

/-- **The strict transform algebra of `S` and the strict transform of `S` as a module are
identified as modules over the strict transform algebra of `P`.** This is
`strictTransformAlg.linearEquivStrictTransform` with its linearity upgraded from `R[I/a]` to the
strict transform of `P`, which is what the finite-type reduction of Stacks Tag 053I needs. -/
noncomputable def strictTransformAlgLinearEquiv :
    strictTransform I a S ≃ₗ[strictTransformAlg I a P] strictTransformAlg I a S :=
  LinearEquiv.ofBijective (ofStrictTransformLinearMap I a S P)
    (ofStrictTransform_bijective I a S)

end AlgLinear

/-! ### Stacks Tag 053I -/

section Conclusion

open Stacks.AffineBlowup

universe uM

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

/-- **Stacks Tag 053I: flattening by blowing up.** Let `(R, 𝔪)` be a local domain with fraction
field `K` and `𝔪 ≠ 0`, let `S` be a finite type `R`-algebra, let `M` be a finite `S`-module and
let `A ⊆ K` be a valuation ring dominating `R`.  Then there is an admissible affine blowup chart
`R[I/a]` — so `I ⊆ 𝔪` is finitely generated, the fibre ring of `R → R[I/a]` at `𝔪` is nonzero and
`A` has center on `R[I/a]` — on which the strict transform of `S` is flat and of finite
presentation over `R[I/a]` and the strict transform of `M` is flat over `R[I/a]` and finitely
presented over the strict transform of `S`.

The polynomial case is `Stacks.Flatness.BlowupFlattening.exists_admissiblePair_mvPolynomial`.  The
  reduction to it is
the source's first step: write `S` as a quotient of `P = R[x_1, …, x_n]` and apply the polynomial
case to the `P`-module `N = S ⊕ M`.  The strict transform of `N` is the product of the strict
transforms of `S` and of `M` (`Stacks.Flatness.BlowupFlattening.prodLinearEquiv`, the version of
`strictTransform.prodEquiv` that is linear over the strict transform of `P`), so flatness and
finite presentation of each summand follow from `Module.Flat.prod_iff` and
`Module.FinitePresentation.prod_iff`.  Finite presentation of the strict transform of `S` as an
`R[I/a]`-*algebra* is then
`Algebra.FinitePresentation.of_surjective_of_module_finitePresentation`, and finite presentation
of the strict transform of `M` over the strict transform of `S` is Stacks Tag 0561,
`Module.FinitePresentation.of_restrictScalars_of_finiteType`.

The statement deviates from the source in two ways: the
hypothesis `𝔪 ≠ 0`, without which the conclusion is unsatisfiable, and clause (4) being read over
`R[I/a]` rather than over `R`. -/
@[stacks 053I]
theorem stacks053I (hdom : Dominates R A) (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (S : Type w)
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (M : Type uM) [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M] :
    Stacks053IConclusion R A S M := by
  classical
  -- Present `S` as a quotient of a polynomial algebra `P`.
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have hfsurj : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) S) := hf
  let : Module (MvPolynomial (Fin n) R) M :=
    Module.compHom M (algebraMap (MvPolynomial (Fin n) R) S)
  have : IsScalarTower (MvPolynomial (Fin n) R) S M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (MvPolynomial (Fin n) R) M :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      show algebraMap (MvPolynomial (Fin n) R) S
        (algebraMap R (MvPolynomial (Fin n) R) r) • x = r • x
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
  have : Module.Finite (MvPolynomial (Fin n) R) S :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin n) R) S) hfsurj
  have : Module.Finite (MvPolynomial (Fin n) R) M := Module.Finite.trans S M
  -- Apply the polynomial case to `N = S ⊕ M`.
  obtain ⟨I, a, ha, hadm, hflatAlgP, hfpAlgP, hflatN, hfpN⟩ :=
    exists_admissiblePair_mvPolynomial hdom hm n (S × M)
  have : Fact (a ∈ I) := ⟨ha⟩
  have := hfpAlgP
  have := hflatN
  have := hfpN
  -- Read off the two summands.
  have : Module.FinitePresentation (strictTransformAlg I a (MvPolynomial (Fin n) R))
      (strictTransform I a S × strictTransform I a M) :=
    Module.FinitePresentation.of_equiv (prodLinearEquiv I a (MvPolynomial (Fin n) R) S M)
  obtain ⟨hfpS, hfpM⟩ := Module.FinitePresentation.prod_iff.mp this
  have hflatprod : Module.Flat (Blowup I a) (strictTransform I a S × strictTransform I a M) :=
    Module.Flat.of_linearEquiv (strictTransform.prodEquiv I a S M).symm
  obtain ⟨hflatS, hflatM⟩ := Module.Flat.prod_iff.mp hflatprod
  have := hfpS
  have := hflatS
  -- The strict transform of `S` over the strict transform of `P`.
  let := strictTransformAlgAlgebra I a (MvPolynomial (Fin n) R) S
  have := isScalarTower_strictTransformAlg I a (MvPolynomial (Fin n) R) S
  have := isScalarTower_strictTransform I a (MvPolynomial (Fin n) R) S M
  have hsurjT : Function.Surjective (algebraMap (strictTransformAlg I a (MvPolynomial (Fin n) R))
      (strictTransformAlg I a S)) :=
    strictTransformAlgMap_surjective I a (MvPolynomial (Fin n) R) S hfsurj
  have : Module.FinitePresentation (strictTransformAlg I a (MvPolynomial (Fin n) R))
      (strictTransformAlg I a S) :=
    Module.FinitePresentation.of_equiv
      (strictTransformAlgLinearEquiv I a S (MvPolynomial (Fin n) R))
  have : Algebra.FiniteType (strictTransformAlg I a (MvPolynomial (Fin n) R))
      (strictTransformAlg I a S) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId _ _) hsurjT
  refine ⟨I, a, ha, (isAdmissiblePair_iff_isAdmissibleBlowupChart A I a).mp hadm,
    Module.Flat.of_linearEquiv (strictTransformAlg.linearEquivStrictTransform I a S),
    Algebra.FinitePresentation.of_surjective_of_module_finitePresentation hsurjT, hflatM,
    Module.FinitePresentation.of_restrictScalars_of_finiteType
      (strictTransformAlg I a (MvPolynomial (Fin n) R)) (strictTransformAlg I a S)
      (strictTransform I a M)⟩

end Conclusion

end Stacks.Flatness.BlowupFlattening
