module

public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham

/-!
# Integrability makes `M ⊗^∧_D Ω^*_D` a complex

`Crystalline.CompletedDeRham.complex` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionDeRham.lean` — the complex
`M ⊗^∧_D Ω^*_D` of [Stacks, Proposition 60.21.3, Tag 07LG] — carries the hypothesis
`Crystalline.CompletedDeRham.IsSquareZero`, that consecutive differentials compose to zero.
This module discharges that hypothesis.

## What the discharge needs, and what it does not

The differential of `M ⊗^∧_D Ω^*_D` is `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`, so

`∇²(m ⊗ ω) = Σ_{j,k} θ_k θ_j m ⊗ (d x_k ∧ d x_j ∧ ω)`
`            + Σ_j θ_j m ⊗ (d (d x_j ∧ ω) + d x_j ∧ d ω) + m ⊗ d(d ω)`

once `∇ m = Σ_j θ_j m ⊗ d x_j` is substituted twice.  The first sum vanishes because the `θ_i`
commute — this is integrability, `Crystalline.IsIntegrable`, [Stacks, Tag 07JD] — *and* because
the wedge of a one-form with itself is zero.  The second vanishes by the Leibniz rule for the
de Rham differential of forms, and the third because `d ∘ d = 0`.

So integrability is one of three inputs, and the other two are properties of the *forms*.  The
family of forms is a carried parameter `Om : ℕ → Type v` of
`Crystalline.CompletedDeRham.complex`, pinned there by one identity only, the Leibniz rule
`Crystalline.CompletedDeRham.IsGradedLeibniz`.  Nothing in that data says `d ∘ d = 0` or that the
wedge is alternating, and `Crystalline.CompletedDeRham.SquareZeroExamples` below shows that
without them the conclusion is false: it exhibits a `Crystalline.Pair` — all four conditions
(07JB)-(07JE) of [Stacks, Tag 07JG], integrability included — together with a family of forms
satisfying `IsGradedLeibniz`, for which `IsSquareZero` fails.  **`IsSquareZero` is therefore not a
consequence of `Crystalline.IsIntegrable` alone**, and cannot be: integrability constrains `∇`,
whereas the failure above is in `deRham`, which integrability does not mention.

What is proved here is the discharge from integrability together with the two missing properties
of the forms, collected as `Crystalline.CompletedDeRham.IsGradedExterior`.  Both hold for the
genuine completed divided power forms `Ω^*_D` of [Stacks, Tag 07HZ]; they are hypotheses here only
because `Om` is a parameter.

## What is and is not proved

**No `@[stacks]` attribute is placed anywhere in this module.**

* Proved, with the hypotheses listed exhaustively in its docstring:
  `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable`, hence
  `Crystalline.CompletedDeRham.complexOfIsIntegrable`, the complex `M ⊗^∧_D Ω^*_D` with no
  `IsSquareZero` hypothesis.
* Proved: `Crystalline.CompletedDeRham.SquareZeroExamples.not_isSquareZero`, that the
  hypothesis cannot be dropped outright, and
  `Crystalline.CompletedDeRham.SquareZeroExamples.isSquareZero_deRhamZero`, that the hypotheses
  of the positive theorem are consistent, so it is not vacuous.
* Not proved here: [Stacks, Tag 07LG] itself, i.e.
  `Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG`.  Nothing in this module bears
  on it beyond making the complex it names unconditional.

The coordinate expansion `∇ m = Σ_j θ_j m ⊗ d x_j` enters here in the form
`Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion`: the sum is a *finite* sum over a fixed
`Finset` of coordinates, uniformly in `m`.  `Crystalline.IsCoordinateExpansion` states instead a
`HasSum` in the `p`-adic topology, and
`Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion.isCoordinateExpansion` proves the finite
form implies it, which is how `Crystalline.IsIntegrable` — quantified over every family realizing
the expansion — is applied.  The finite form is what the two substitutions above need: the
cancellation pairs the term `(j, k)` with the term `(k, j)`, and over an infinite index set that
rearrangement would need summability of the double family, which `HasSum` of the single family
does not give.  So the result is proved for finitely many coordinates, which is the case of
[Stacks, Tag 07LG] where `D` is the envelope of a polynomial ring in finitely many variables.

One hypothesis of `IsGradedExterior` is weaker than the identity it stands for, for a reason of
vocabulary.  The graded Leibniz rule for the wedge is `d (η ∧ ω) = d η ∧ ω - η ∧ d ω`, and `d η`
is a *two*-form, whereas `wedge` only multiplies by a one-form, so `d η ∧ ω` cannot be written in
the carried data at all.  The field `IsGradedExterior.deRham_wedge` is therefore the rule
restricted to *closed* one-forms `η`, where the unwritable term is absent.  That is all the proof
uses, since the one-forms it is applied to are the coordinate differentials `d x_j`.

## Main definitions

* `Crystalline.CompletedDeRham.IsGradedExterior` — the two properties of the carried forms that
  the discharge needs beyond `IsGradedLeibniz`: `d ∘ d = 0`, and the wedge is alternating and
  satisfies the Leibniz rule against closed one-forms.
* `Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion` — the coordinate expansion
  `∇ m = Σ_j θ_j m ⊗ d x_j` as a finite sum over a fixed `Finset` of coordinates.
* `Crystalline.CompletedDeRham.complexOfIsIntegrable` — **the complex `M ⊗^∧_D Ω^*_D` with its
  `IsSquareZero` hypothesis discharged**.
* `Crystalline.CompletedDeRham.SquareZeroExamples` — the two examples, both over `D = ℤ/2` with
  `p = 2`, `Ω^i = ℤ/2` and zero wedge: with `d = id` the counterexample, with `d = 0` a witness
  that the hypotheses of the positive theorem are consistent.

## Main results

* `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` — **integrability and
  `IsGradedExterior` give `IsSquareZero`**.
* `Crystalline.CompletedDeRham.IsGradedExterior.wedge_comm` — an alternating wedge is
  antisymmetric, by polarization.
* `Crystalline.CompletedDeRham.differential_differential_toCompletedTensor` — the square of the
  differential vanishes on the image of the uncompleted tensor product, which is the whole
  computation.
* `Crystalline.CompletedDeRham.SquareZeroExamples.not_isSquareZero` together with
  `Crystalline.CompletedDeRham.SquareZeroExamples.pair` — a pair satisfying all of
  (07JB)-(07JE) whose completed de Rham differentials do not compose to zero.
* `Crystalline.CompletedDeRham.SquareZeroExamples.isSquareZero_deRhamZero` — the hypotheses of
  `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` are jointly satisfiable, so that
  theorem is not vacuous.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w uI

namespace Crystalline

namespace CompletedDeRham

/-! ### The exterior properties of the carried family of forms -/

section Exterior

variable (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))

/-- **The properties of a graded family of forms that make `M ⊗^∧_D Ω^*_D` a complex**, beyond
the Leibniz rule `Crystalline.CompletedDeRham.IsGradedLeibniz` already carried by
`Crystalline.CompletedDeRham.complex`: the de Rham differential squares to zero, and the wedge
product is alternating on one-forms and obeys the Leibniz rule against a closed one-form.

All three hold for the genuine divided power forms of [Stacks, Tag 07HZ]; they are hypotheses
because the family of forms is a carried parameter of
`Crystalline.CompletedDeRham.complex`, pinned there by the Leibniz rule alone.

`deRham_wedge` is the graded Leibniz rule `d (η ∧ ω) = d η ∧ ω - η ∧ d ω` restricted to closed
one-forms `η`.  The unrestricted rule cannot be stated in this data: `d η` is a two-form and
`wedge` multiplies only by one-forms, so the term `d η ∧ ω` has no name here.  The restriction is
all that the proof of `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` uses, because the
one-forms it is applied to are the coordinate differentials. -/
public structure IsGradedExterior : Prop where
  /-- The de Rham differential of the forms squares to zero. -/
  deRham_deRham : ∀ (i : ℕ) (ω : Om i), deRham (i + 1) (deRham i ω) = 0
  /-- The wedge product is alternating: wedging twice by the same one-form gives zero. -/
  wedge_self : ∀ (i : ℕ) (ω : Om i) (η : Om 1), wedge (i + 1) (wedge i ω η) η = 0
  /-- The graded Leibniz rule `d (η ∧ ω) = - η ∧ d ω` for a *closed* one-form `η`. -/
  deRham_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1), deRham 1 η = 0 →
    deRham (i + 1) (wedge i ω η) + wedge (i + 1) (deRham i ω) η = 0

/-- **An alternating wedge is antisymmetric**: `ζ ∧ (η ∧ ω) = - η ∧ (ζ ∧ ω)`.  This is
polarization — the map `(η, ζ) ↦ ζ ∧ (η ∧ ω)` is bilinear, so expanding
`(η + ζ) ∧ ((η + ζ) ∧ ω) = 0` and cancelling the two diagonal terms leaves the identity.  It is
why `Crystalline.CompletedDeRham.IsGradedExterior` asks only for the alternating property and not
for antisymmetry as well; over a ring in which `2` is not invertible the two are not equivalent,
and it is the alternating property that is the stronger one. -/
public theorem IsGradedExterior.wedge_comm (h : IsGradedExterior D Om wedge deRham) (i : ℕ)
    (ω : Om i) (η ζ : Om 1) :
    wedge (i + 1) (wedge i ω η) ζ + wedge (i + 1) (wedge i ω ζ) η = 0 := by
  have h0 := h.wedge_self i ω (η + ζ)
  simp only [map_add, LinearMap.add_apply, h.wedge_self i ω η, h.wedge_self i ω ζ,
    zero_add, add_zero] at h0
  exact (add_comm _ _).trans h0

end Exterior

/-! ### The coordinate expansion as a finite sum -/

section Expansion

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] {ι : Type uI} (dx : ι → Omega) {dmap : D → Omega} {M : Type w}
  [AddCommGroup M] [Module D M] (nabla : CompletedConnection p D Omega dmap M)
  (theta : ι → (M → M)) (s : Finset ι)

/-- **The coordinate expansion `∇ m = Σ_j θ_j m ⊗ d x_j` as a finite sum**: the sum is taken over
a fixed finite set `s` of coordinates, uniformly in `m`, and the coordinates outside `s`
contribute nothing.

`Crystalline.IsCoordinateExpansion` states the same expansion as a `HasSum` in the `p`-adic
topology, and
`Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion.isCoordinateExpansion` shows this form
implies it.  This form is what
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` needs: that proof substitutes the
expansion twice and then cancels the term indexed `(j, k)` against the term indexed `(k, j)`, a
rearrangement of a double family which a `HasSum` for the single family does not license. -/
public structure IsFiniteCoordinateExpansion : Prop where
  /-- The connection is the finite sum of its coordinate terms over `s`. -/
  sum_eq : ∀ m : M, nabla m =
    ∑ j ∈ s, toCompletedTensor p D Omega M (theta j m ⊗ₜ[D] dx j)
  /-- A coordinate outside `s` contributes a zero term. -/
  eq_zero_of_notMem : ∀ j ∉ s, ∀ m : M,
    toCompletedTensor p D Omega M (theta j m ⊗ₜ[D] dx j) = 0

/-- A finite coordinate expansion is a coordinate expansion in the sense of
`Crystalline.IsCoordinateExpansion`: a sum with finitely many nonzero terms has that sum as its
`HasSum`.  This is what lets `Crystalline.IsIntegrable`, which is quantified over every family of
operators realizing the expansion, be applied to the family at hand. -/
public theorem IsFiniteCoordinateExpansion.isCoordinateExpansion
    (h : IsFiniteCoordinateExpansion p D Omega dx nabla theta s) :
    IsCoordinateExpansion p D Omega dx nabla theta := by
  let := completedTensorTopology p D Omega M
  intro m
  rw [h.sum_eq m]
  exact hasSum_sum_of_ne_finset_zero fun j hj => h.eq_zero_of_notMem j hj m

end Expansion

/-- Two pure tensors over the same `m` whose forms sum to zero have images summing to zero. -/
private theorem toCompletedTensor_tmul_add_eq_zero (p : ℕ) (D : Type u) [CommRing D]
    (Omega : Type v) [AddCommGroup Omega] [Module D Omega] (M : Type w) [AddCommGroup M]
    [Module D M] (m : M) {a b : Omega} (h : a + b = 0) :
    toCompletedTensor p D Omega M (m ⊗ₜ[D] a) + toCompletedTensor p D Omega M (m ⊗ₜ[D] b) = 0 := by
  rw [← map_add, ← TensorProduct.tmul_add, h, TensorProduct.tmul_zero, map_zero]

/-! ### The square of the differential -/

section SquareZero

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) {dmap : D → Om 1} (M : Type w) [AddCommGroup M]
  [Module D M] (nabla : CompletedConnection p D (Om 1) dmap M)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap) {ι : Type uI} (dx : ι → Om 1)
  (theta : ι → (M → M)) (s : Finset ι)

/-- **The differential of `M ⊗^∧_D Ω^*_D` on a pure tensor, with the connection expanded in
coordinates**: `∇(m ⊗ ω) = Σ_j θ_j m ⊗ (d x_j ∧ ω) + m ⊗ d ω`.  This is
`Crystalline.CompletedDeRham.differential_of_tmul` with the value `∇ m` replaced by its finite
coordinate expansion, and it is the one step the computation of the square iterates. -/
public theorem differential_toCompletedTensor_tmul
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s) (i : ℕ) (m : M) (ω : Om i) :
    differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)) =
      (∑ j ∈ s, toCompletedTensor p D (Om (i + 1)) M (theta j m ⊗ₜ[D] wedge i ω (dx j))) +
        toCompletedTensor p D (Om (i + 1)) M (m ⊗ₜ[D] deRham i ω) := by
  rw [differential_of_tmul, hexp.sum_eq m, map_sum]
  simp only [wedgeMap_of_tmul]

/-- **The square of the differential vanishes on a pure tensor.**  Substituting the coordinate
expansion twice leaves three groups of terms: a double sum over pairs of coordinates, which
cancels because the coordinate operators commute — integrability — and the wedge is alternating;
a single sum, which cancels by the Leibniz rule for the de Rham differential of the forms against
the closed one-forms `d x_j`; and `m ⊗ d(d ω)`, which vanishes because `d ∘ d = 0`. -/
public theorem differential_differential_tmul (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j)
    (i : ℕ) (m : M) (ω : Om i) :
    differential p D Om wedge deRham M nabla hleib (i + 1)
      (differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω))) = 0 := by
  classical
  have hW : toCompletedTensor p D (Om (i + 1 + 1)) M
      (m ⊗ₜ[D] deRham (i + 1) (deRham i ω)) = 0 := by
    rw [hext.deRham_deRham, TensorProduct.tmul_zero, map_zero]
  have hYZ : (∑ j ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
        (theta j m ⊗ₜ[D] deRham (i + 1) (wedge i ω (dx j)))) +
      (∑ j ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
        (theta j m ⊗ₜ[D] wedge (i + 1) (deRham i ω) (dx j))) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => toCompletedTensor_tmul_add_eq_zero p D _ M _
      (hext.deRham_wedge i ω (dx j) (hdx j))
  have hA : (∑ j ∈ s, ∑ k ∈ s, toCompletedTensor p D (Om (i + 1 + 1)) M
      (theta k (theta j m) ⊗ₜ[D] wedge (i + 1) (wedge i ω (dx j)) (dx k))) = 0 := by
    rw [← Finset.sum_product']
    refine Finset.sum_involution (fun a _ => a.swap) (fun a _ => ?_) (fun a _ hne => ?_)
      (fun a ha => ?_) (fun a _ => ?_)
    · obtain ⟨j, k⟩ := a
      have hjk : theta j (theta k m) = theta k (theta j m) := congrFun (hcomm j k) m
      simp only [Prod.swap_prod_mk, hjk]
      exact toCompletedTensor_tmul_add_eq_zero p D _ M _
        (hext.wedge_comm D Om wedge deRham i ω (dx j) (dx k))
    · obtain ⟨j, k⟩ := a
      intro heq
      rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      refine hne ?_
      obtain ⟨rfl, -⟩ := heq
      rw [hext.wedge_self, TensorProduct.tmul_zero, map_zero]
    · exact Finset.mem_product.2 ⟨(Finset.mem_product.1 ha).2, (Finset.mem_product.1 ha).1⟩
    · exact Prod.swap_swap a
  rw [differential_toCompletedTensor_tmul p D Om wedge deRham M nabla hleib dx theta s hexp,
    map_add, map_sum]
  simp only [differential_toCompletedTensor_tmul p D Om wedge deRham M nabla hleib dx theta s hexp]
  rw [Finset.sum_add_distrib, hW, add_zero, hA, zero_add]
  exact hYZ

/-- The level-`n` value of the differential depends on its argument only through the argument's
level-`n` value.  This is what makes the image of the uncompleted tensor product enough: the
differential is local at the levels by construction. -/
public theorem differential_val_congr (i n : ℕ) (x y : CompletedTensor p D (Om i) M)
    (h : x.val n = y.val n) :
    (differential p D Om wedge deRham M nabla hleib i x).val n =
      (differential p D Om wedge deRham M nabla hleib i y).val n := by
  rw [differential_val, differential_val, h]

/-- The square of the differential vanishes on the image of the whole uncompleted tensor product
`M ⊗_D Ω^i_D`, not only on pure tensors. -/
public theorem differential_differential_toCompletedTensor
    (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hcomm : ∀ j k, theta j ∘ theta k = theta k ∘ theta j)
    (i : ℕ) (y : M ⊗[D] Om i) :
    differential p D Om wedge deRham M nabla hleib (i + 1)
      (differential p D Om wedge deRham M nabla hleib i
        (toCompletedTensor p D (Om i) M y)) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m ω =>
    exact differential_differential_tmul p D Om wedge deRham M nabla hleib dx theta s hext hexp
      hdx hcomm i m ω
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]

/-- **The differentials of `M ⊗^∧_D Ω^*_D` compose to zero**, that is
`Crystalline.CompletedDeRham.IsSquareZero` holds, given integrability.

The hypotheses are, exhaustively: the data of
`Crystalline.CompletedDeRham.complex` itself (`p`, `D`, the graded family of forms `Om` with its
wedge product and de Rham differential, the module `M`, the completed connection `nabla`, and the
Leibniz rule `hleib`), together with

* `hext`, that the forms are exterior in the sense of
  `Crystalline.CompletedDeRham.IsGradedExterior` — `d ∘ d = 0`, the wedge alternating, the
  Leibniz rule for the wedge against closed one-forms.  These hold for the genuine divided power
  forms and are hypotheses only because `Om` is a parameter;
* `hexp`, a coordinate expansion `∇ m = Σ_{j ∈ s} θ_j m ⊗ d x_j` over a fixed finite set `s` of
  coordinates, in the sense of
  `Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion`;
* `hdx`, that the coordinate differentials `d x_j` are closed;
* `hint`, **integrability of the connection**, `Crystalline.IsIntegrable`, [Stacks, Tag 07JD].
  For a pair this is the field `Crystalline.Pair.isIntegrable`.

No further hypothesis is carried.  `Crystalline.CompletedDeRham.SquareZeroExamples` shows
that `hext` cannot be dropped. -/
public theorem isSquareZero_of_isIntegrable (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) :
    IsSquareZero p D Om wedge deRham M nabla hleib := by
  have hcomm := hint theta hexp.isCoordinateExpansion
  intro i
  refine AddMonoidHom.ext fun x => ?_
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val n)
  have hxz : x.val n = (toCompletedTensor p D (Om i) M z).val n := hz.symm
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, AdicCompletion.val_zero_apply,
    differential_val_congr p D Om wedge deRham M nabla hleib (i + 1) n _ _
      (differential_val_congr p D Om wedge deRham M nabla hleib i n x _ hxz),
    differential_differential_toCompletedTensor p D Om wedge deRham M nabla hleib dx theta s
      hext hexp hdx hcomm i z, AdicCompletion.val_zero_apply]

/-- **The complex `M ⊗^∧_D Ω^*_D` of [Stacks, Tag 07LG], with its `IsSquareZero` hypothesis
discharged.**  This is `Crystalline.CompletedDeRham.complex` with the hypothesis that consecutive
differentials compose to zero replaced by integrability of the connection and the exterior
properties of the forms; see
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` for the exhaustive list of what it
carries.  For a pair `P : Crystalline.Pair` take `nabla := P.nabla` and
`hint := P.isIntegrable`. -/
public noncomputable def complexOfIsIntegrable (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) :
    CochainComplex AddCommGrpCat.{max v w} ℕ :=
  complex p D Om wedge deRham M nabla hleib
    (isSquareZero_of_isIntegrable p D Om wedge deRham M nabla hleib dx theta s hext hexp hdx hint)

/-- The complex of `Crystalline.CompletedDeRham.complexOfIsIntegrable` is
`Crystalline.CompletedDeRham.complex`: its degree-`i` term is `M ⊗̂_D Ω^i_D`. -/
public theorem complexOfIsIntegrable_X (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) (i : ℕ) :
    (complexOfIsIntegrable p D Om wedge deRham M nabla hleib dx theta s hext hexp hdx hint).X i =
      AddCommGrpCat.of (CompletedTensor p D (Om i) M) := rfl

/-- The differential of `Crystalline.CompletedDeRham.complexOfIsIntegrable` is the de Rham
differential of the connection. -/
public theorem complexOfIsIntegrable_d (hext : IsGradedExterior D Om wedge deRham)
    (hexp : IsFiniteCoordinateExpansion p D (Om 1) dx nabla theta s)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (hint : IsIntegrable p D (Om 1) dx nabla) (i : ℕ) :
    (complexOfIsIntegrable p D Om wedge deRham M nabla hleib dx theta s hext hexp hdx hint).d i
        (i + 1) =
      AddCommGrpCat.ofHom (differential p D Om wedge deRham M nabla hleib i) :=
  complex_d p D Om wedge deRham M nabla hleib _ i

end SquareZero

/-! ### Integrability alone does not make `M ⊗^∧_D Ω^*_D` a complex -/

namespace SquareZeroExamples

/-- The ring `D` of the counterexample: `ℤ/2`, in which the prime `p = 2` is zero, so that the
`p`-adic ideal is `(0)` and the `p`-adic completion of a module is that module at every positive
level.  Taking `p` to be a prime that vanishes in `D` is what makes the completed tensor product
visible enough to compute in; nothing else about `ℤ/2` is used. -/
public abbrev D : Type := ZMod 2

/-- The module `M` of the counterexample: `ℤ/2` over itself. -/
public abbrev M : Type := ZMod 2

/-- The graded family of forms of the counterexample: `Ω^i = ℤ/2` in every degree.  It satisfies
the Leibniz rule `Crystalline.CompletedDeRham.IsGradedLeibniz` and nothing else; in particular its
de Rham differential does not square to zero. -/
public abbrev Om : ℕ → Type := fun _ => ZMod 2

/-- The wedge product of the counterexample: zero.  With a zero wedge the Leibniz rule
`Crystalline.CompletedDeRham.IsGradedLeibniz` reduces to `D`-linearity of the de Rham
differential. -/
public def wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1) := fun _ => 0

/-- The de Rham differential of the counterexample: the identity `ℤ/2 → ℤ/2` in every degree.  It
is `D`-linear, hence satisfies the Leibniz rule against the zero wedge, and it does **not** square
to zero, which is the whole point. -/
public def deRham : ∀ i, Om i →+ Om (i + 1) := fun _ => AddMonoidHom.id (ZMod 2)

/-- The de Rham differential `deRham i` of the counterexample is the identity on `ℤ/2`. -/
@[simp] public theorem deRham_apply (i : ℕ) (x : Om i) : deRham i x = x := rfl

/-- The derivation `d : D → Ω¹` of the counterexample: zero.  The zero connection below is a
connection exactly for this choice. -/
public def dmap : D → Om 1 := fun _ => 0

/-- The connection of the counterexample: the zero map, which is a completed connection because
the carried derivation `d` is zero. -/
public noncomputable def nabla : CompletedConnection 2 D (Om 1) dmap M where
  toFun _ := 0
  map_add' _ _ := by rw [add_zero]
  leibniz' f m := by simp [dmap]

/-- The connection `nabla` of the counterexample sends every element of `M` to zero. -/
@[simp] public theorem nabla_apply (m : M) : nabla m = 0 := rfl

/-- The `p`-adic ideal of the counterexample is zero, because `2 = 0` in `ℤ/2`. -/
public theorem pAdicIdeal_eq_bot : pAdicIdeal (A := D) 2 = ⊥ := by
  have h : ((2 : ℕ) : D) = 0 := by decide
  rw [pAdicIdeal, h, Ideal.span_singleton_eq_bot]

/-- **The image of `1 ⊗ 1` in the completed tensor product is not zero.**  The `p`-adic ideal is
`(0)`, so the level-one quotient of `M ⊗_D Ω^i_D` is `M ⊗_D Ω^i_D` itself, and `1 ⊗ 1` is nonzero
there because `ℤ/2 ⊗_{ℤ/2} ℤ/2 ≅ ℤ/2`. -/
public theorem toCompletedTensor_one_ne_zero (i : ℕ) :
    toCompletedTensor 2 D (Om i) M (1 ⊗ₜ[D] 1) ≠ 0 := by
  intro h
  have h1 : (toCompletedTensor 2 D (Om i) M (1 ⊗ₜ[D] (1 : Om i))).val 1 = 0 := by
    rw [h, AdicCompletion.val_zero_apply]
  rw [AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    pAdicIdeal_eq_bot, pow_one, Submodule.bot_smul, Submodule.mem_bot] at h1
  have h2 := congrArg (TensorProduct.lid D (Om i)) h1
  simp only [TensorProduct.lid_tmul, one_smul, map_zero] at h2
  exact one_ne_zero h2

/-- The forms of the counterexample satisfy the Leibniz rule
`Crystalline.CompletedDeRham.IsGradedLeibniz`, which is the only identity
`Crystalline.CompletedDeRham.complex` imposes on them. -/
public theorem isGradedLeibniz : IsGradedLeibniz D Om wedge deRham dmap := by
  intro i f ω
  simp [wedge]

/-- The single coordinate of the counterexample: `d x = 1`. -/
public def dx : Unit → Om 1 := fun _ => 1

/-- The zero family of coordinate operators realizes the coordinate expansion of the zero
connection, so the integrability of
`Crystalline.CompletedDeRham.SquareZeroExamples.isIntegrable` is not vacuous: a family of
operators realizing the expansion does exist. -/
public theorem isCoordinateExpansion_zero :
    IsCoordinateExpansion 2 D (Om 1) dx nabla (fun _ _ => 0) := by
  let := completedTensorTopology 2 D (Om 1) M
  intro m
  simp only [nabla_apply, TensorProduct.zero_tmul, map_zero]
  exact hasSum_zero

/-- **The connection of the counterexample is integrable**, `Crystalline.IsIntegrable`, and not
vacuously: by
`Crystalline.CompletedDeRham.SquareZeroExamples.isCoordinateExpansion_zero` a family of
operators realizing its coordinate expansion exists.  With one coordinate any two coordinate
operators are the same operator, so they commute. -/
public theorem isIntegrable : IsIntegrable 2 D (Om 1) dx nabla := by
  intro theta _ i j
  rw [Subsingleton.elim i j]

/-- The module of the counterexample is `p`-adically complete: the `p`-adic ideal is zero. -/
public theorem isPAdicallyComplete : IsPAdicallyComplete 2 D M := by
  show IsAdicComplete (pAdicIdeal (A := D) 2) M
  rw [pAdicIdeal_eq_bot]
  infer_instance

/-- The empty family of coordinates, used only to exhibit a `Crystalline.Pair`: with no
coordinates the conditions (07JD) and (07JE) of [Stacks, Tag 07JG] hold outright, so the pair
below satisfies all four conditions of that tag with nothing left to check.  Integrability for a
nonempty family of coordinates is
`Crystalline.CompletedDeRham.SquareZeroExamples.isIntegrable`, and neither the complex nor
`Crystalline.CompletedDeRham.IsSquareZero` mentions the coordinates at all, so the choice here
does not affect the counterexample. -/
public def dxEmpty : Empty → Om 1 := fun i => i.elim

/-- With no coordinates every family of operators realizes the coordinate expansion of the zero
connection, the empty sum being zero. -/
public theorem isCoordinateExpansion_empty (theta : Empty → M → M) :
    IsCoordinateExpansion 2 D (Om 1) dxEmpty nabla theta := by
  let := completedTensorTopology 2 D (Om 1) M
  intro m
  have h : nabla m = ∑ b ∈ (∅ : Finset Empty),
      toCompletedTensor 2 D (Om 1) M (theta b m ⊗ₜ[D] dxEmpty b) := by
    rw [Finset.sum_empty, nabla_apply]
  rw [h]
  exact hasSum_sum_of_ne_finset_zero fun b _ => b.elim

/-- The zero connection has a finite coordinate expansion over the empty set of coordinates, in
the sense of `Crystalline.CompletedDeRham.IsFiniteCoordinateExpansion`. -/
public theorem isFiniteCoordinateExpansion_empty :
    IsFiniteCoordinateExpansion 2 D (Om 1) dxEmpty nabla (fun i _ => i.elim)
      (∅ : Finset Empty) where
  sum_eq m := by rw [Finset.sum_empty, nabla_apply]
  eq_zero_of_notMem j _ _ := j.elim

/-- **A pair `(M, ∇)` satisfying all four conditions (07JB)-(07JE) of
[Stacks, Lemma 60.17.3, Tag 07JG]**, integrability included, whose completed de Rham
differentials against the forms of this counterexample do not compose to zero. -/
public noncomputable def pair : Pair 2 D (Om 1) dxEmpty dmap where
  carrier := M
  isPAdicallyComplete := isPAdicallyComplete
  nabla := nabla
  hasCoordinateOperators := ⟨fun i _ => i.elim, isCoordinateExpansion_empty _⟩
  isIntegrable := fun _ _ i => i.elim
  isTopologicallyQuasiNilpotent := fun _ _ _ =>
    Set.finite_empty.subset fun q _ => q.1.elim

/-- **Integrability does not make `M ⊗^∧_D Ω^*_D` a complex.**  For the data of this
counterexample the differential in degree `i` sends the image of `1 ⊗ 1` to the image of `1 ⊗ 1`,
so its square is not zero, even though the connection is integrable
(`Crystalline.CompletedDeRham.SquareZeroExamples.isIntegrable`) and the forms satisfy the
Leibniz rule
(`Crystalline.CompletedDeRham.SquareZeroExamples.isGradedLeibniz`).  What fails is
`Crystalline.CompletedDeRham.IsGradedExterior`: here `d ∘ d = id ≠ 0`.  So the hypothesis
`Crystalline.CompletedDeRham.IsSquareZero` of `Crystalline.CompletedDeRham.complex` is not a
consequence of `Crystalline.IsIntegrable`, and the properties of the forms assumed by
`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` are needed. -/
public theorem not_isSquareZero :
    ¬ IsSquareZero 2 D Om wedge deRham M nabla isGradedLeibniz := by
  intro h
  have hd : ∀ i : ℕ, differential 2 D Om wedge deRham M nabla isGradedLeibniz i
      (toCompletedTensor 2 D (Om i) M (1 ⊗ₜ[D] 1)) =
      toCompletedTensor 2 D (Om (i + 1)) M (1 ⊗ₜ[D] 1) := by
    intro i
    rw [differential_of_tmul, nabla_apply, map_zero, zero_add, deRham_apply]
  have h0 := DFunLike.congr_fun (h 0) (toCompletedTensor 2 D (Om 0) M (1 ⊗ₜ[D] 1))
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, hd 0, hd (0 + 1)] at h0
  exact toCompletedTensor_one_ne_zero (0 + 1 + 1) h0

/-! ### The hypotheses of the positive theorem are consistent -/

/-- A second de Rham differential on the same family of forms: zero in every degree.  Unlike
`Crystalline.CompletedDeRham.SquareZeroExamples.deRham` it satisfies
`Crystalline.CompletedDeRham.IsGradedExterior`. -/
public def deRhamZero : ∀ i, Om i →+ Om (i + 1) := fun _ => 0

/-- The zero de Rham differential satisfies the Leibniz rule against the zero wedge. -/
public theorem isGradedLeibniz_zero : IsGradedLeibniz D Om wedge deRhamZero dmap := by
  intro i f ω
  simp [wedge, deRhamZero]

/-- **The zero de Rham differential is exterior**: `Crystalline.CompletedDeRham.IsGradedExterior`
is satisfiable. -/
public theorem isGradedExterior_zero : IsGradedExterior D Om wedge deRhamZero where
  deRham_deRham i ω := by simp [deRhamZero]
  wedge_self i ω η := by simp [wedge]
  deRham_wedge i ω η _ := by simp [wedge, deRhamZero]

/-- **The hypotheses of `Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` are jointly
satisfiable, so that theorem is not vacuous.**  The data is that of this section with the zero de
Rham differential in place of the identity: the forms are then exterior, the zero connection has
a finite coordinate expansion over the empty set of coordinates and is integrable, and the
conclusion `Crystalline.CompletedDeRham.IsSquareZero` follows from the theorem.  The complex it
produces is not the zero complex: its degree-`i` term is `M ⊗̂_D Ω^i_D`, which contains the
nonzero element exhibited by
`Crystalline.CompletedDeRham.SquareZeroExamples.toCompletedTensor_one_ne_zero`. -/
public theorem isSquareZero_deRhamZero :
    IsSquareZero 2 D Om wedge deRhamZero M nabla isGradedLeibniz_zero :=
  isSquareZero_of_isIntegrable 2 D Om wedge deRhamZero M nabla isGradedLeibniz_zero dxEmpty
    (fun i _ => i.elim) ∅ isGradedExterior_zero isFiniteCoordinateExpansion_empty
    (fun j => j.elim) (fun _ _ i => i.elim)

end SquareZeroExamples

end CompletedDeRham

end Crystalline

end
