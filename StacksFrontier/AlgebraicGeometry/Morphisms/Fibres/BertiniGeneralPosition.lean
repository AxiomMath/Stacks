module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmoothIrreducibleMember
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPrimeThroughPoints

/-!
# The general member is in general position at a closed point

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and let `x` be a point
of `X`. The proof of [Stacks, Tag 0FH7] asserts, with "details omitted", that the members `v` of
the linear system whose section `ψ(v)` has nonzero `1`-jet at `x` — that is, whose germ at `x`
avoids `𝔪_x²ℒ_x` — form a *nonempty open* of the parameter space `𝔸^r_k`. That is what this module
proves, and it separates the assertion into its two halves.

* **The surjection onto the `1`-jet**, the substantive half, is isolated as the single hypothesis
  `ev_x ≠ 0` on the basis-free evaluation `Stacks.Bertini.FamilyDivisors.evalVector`. Nothing more
  than nonvanishing is needed: surjectivity is stronger than the statement requires.

* **Openness** is proved here with no hypothesis beyond that one — no smoothness, no
  algebraically closed base field, not even closedness of `x`. The good locus is the complement of
  the linear subspace `ker ev_x`, which is open but need not be a *basic* open; what a generality
  statement needs is a nonempty open inside it, and one is obtained by choosing a linear
  functional `φ` on `V` that kills `ker ev_x` and not some vector outside it
  (`Submodule.exists_dual_map_eq_bot_of_notMem`). The coefficient vector `aᵢ = φ(vᵢ)` is then
  nonzero, so the basic open of `∑ᵢ aᵢxᵢ` in `Γ(𝔸^r_k, ⊤) = k[x₁, …, x_r]` is nonempty — `𝔸^r_k`
  is reduced — and a `k`-rational parameter of it is not killed by `φ`, hence not by `ev_x`.

Where the linear system *does* generate `L` and define an immersion — hypotheses (2) and (3) of
[Stacks, Tag 0FD6] — the hypothesis `ev_x ≠ 0` is discharged at a closed point of a smooth `X`
over an algebraically closed field, by the surjectivity of `ev_x` that
`Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed` proves and
`Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis` records as a matrix. That is *not* the
situation of [Stacks, Tag 0FH7], whose linear system consists of the sections vanishing at the
very points being put in general position, so that hypothesis (2) fails there and the source reads
the surjection off the very ampleness of a high power of `ℒ` instead; the `ev_x ≠ 0` form is
therefore the one a consumer of that argument wants.

The last section combines the general-position open with the open witnessing a
`Stacks.Bertini.FamilyDivisors.ForGeneral` smoothness conclusion of [Stacks, Tag 0FD6]: two
nonempty opens of `𝔸^r_k` meet because the parameter space is irreducible, so a single nonzero
member of the linear system has both properties at once.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.coeffLinearForm` is the polynomial `∑ᵢ aᵢxᵢ` of a coefficient
  vector, and `Stacks.Bertini.FamilyDivisors.coeffOpen` is its basic open in `𝔸^r_k`.

## Main results

* `Stacks.Bertini.FamilyDivisors.nonempty_coeffOpen`: the basic open of a linear form with one
  nonzero coefficient is nonempty.
* `Stacks.Bertini.FamilyDivisors.sum_ne_zero_of_parameterPoint_mem_coeffOpen`: a `k`-rational
  parameter of that open is not annihilated by the coefficient vector.
* `Stacks.Bertini.FamilyDivisors.notMem_maximalSqSmul_iff_evalVector_ne_zero`: the germ of `ψ(v)`
  at `x` avoids `𝔪_x²ℒ_x` exactly when `ev_x` does not kill `v`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero`:
  **the general-position assertion of [Stacks, Tag 0FH7]**, from `ev_x ≠ 0` and nothing else — a
  nonempty open of `𝔸^r_k` at every `k`-rational parameter of which the germ of the corresponding
  member at `x` avoids `𝔪_x²ℒ_x`.
* `Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_of_isImmersive` and
  `…exists_nonempty_opens_notMem_maximalSqSmul_constCoeffSection`: the hypothesis discharged, and
  the assertion, under hypotheses (2) and (3) of [Stacks, Tag 0FD6].
* `Stacks.Bertini.FamilyDivisors.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_of_evalVector_`
  `ne_zero` and `…exists_ne_zero_smooth_divisor_notMem_maximalSqSmul`: **a single nonzero member
  whose divisor is smooth and whose `1`-jet at `x` is nonzero**, from a `ForGeneral` smoothness
  conclusion together with the preceding open.

## Implementation notes

The open is built in the polynomial coordinates `Stacks.Bertini.FamilyDivisors.parameterBaseΓEquiv`
rather than as a combination of `AlgebraicGeometry.AffineSpace.coord`, because the only facts
needed about it are that a nonzero polynomial has nonempty basic open and that a `k`-rational
parameter evaluates it; the second is
`Stacks.Bertini.FamilyDivisors.parameterPoint_appTop_parameterBaseΓEquiv`, which is already stated
through that identification. The sibling construction
`Stacks.Bertini.FamilyDivisors.rationalPointLinearForm` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalPointOpen` is a different linear
form — its coefficients are the values at a `k`-point of the chart equations of the system, and
its open is the one where the divisor *avoids* that point — and is consumed through the universal
divisor rather than through evaluation at a parameter, so nothing is shared beyond the shape.

In the immersive case the column index `0` of the evaluation matrix is used rather than a column
chosen for being nonzero: the target `Fin (n + 1)` of `coeffMap M` is never trivial, so
surjectivity already forces that column to be nonzero. Hypothesis (3) may be taken at any basis of
the linear system, as in `Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis`, because
nonvanishing of the evaluation is a property of the basis-free `evalVector`
(`Stacks.Bertini.FamilyDivisors.evalCoord_sectionOf_apply`). The local dimension of `X` at `x` is
not an input: it exists because the local ring of a smooth scheme at a closed point is regular
(`Stacks.Bertini.FamilyDivisors.exists_natCast_eq_topologicalKrullDimAt_of_isClosed`). Neither is
the infinitude of `k` that `Stacks.Bertini.FamilyDivisors.exists_parameterPoint_mem` needs to find
a rational parameter: an algebraically closed field is infinite, and instance search supplies it,
so `[Infinite D.k]` is a binder only on the statements that do not assume `[IsAlgClosed D.k]`.

**No `@[stacks]` attribute is attached.** This is the step the proof of [Stacks, Tag 0FH7] omits,
not the assertion of a tag; the tags whose material it reuses are registered where they are
proved.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.Bertini.FamilyDivisors

open Stacks.LinearSubspace

variable (D : FamilyDivisors.{u, u})

/-! ### The basic open of a linear form in the parameters -/

/-- **The linear form `∑ᵢ aᵢxᵢ`** of a coefficient vector, in the polynomial coordinates of the
parameter space `𝔸^r_k`. -/
def coeffLinearForm (a : D.basisIndex → D.k) : MvPolynomial D.basisIndex D.k :=
  ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i

/-- The value of the linear form at a coordinate tuple. -/
theorem eval_coeffLinearForm (a c : D.basisIndex → D.k) :
    MvPolynomial.eval c (D.coeffLinearForm a) = ∑ i, a i * c i := by
  rw [coeffLinearForm, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- **The linear form is nonzero** as soon as one of its coefficients is: it takes the value
`aᵢ₀` at the `i₀`-th standard basis vector. -/
theorem coeffLinearForm_ne_zero {a : D.basisIndex → D.k} {i₀ : D.basisIndex} (h : a i₀ ≠ 0) :
    D.coeffLinearForm a ≠ 0 := by
  classical
  intro hzero
  have hval := D.eval_coeffLinearForm a (Pi.single i₀ 1)
  rw [hzero, map_zero, Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
    (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero]), Pi.single_eq_same,
    mul_one] at hval
  exact h hval.symm

/-- **The basic open `D(∑ᵢ aᵢxᵢ) ⊂ 𝔸^r_k`** of a coefficient vector. -/
def coeffOpen (a : D.basisIndex → D.k) : D.parameterBase.Opens :=
  D.parameterBase.basicOpen (D.parameterBaseΓEquiv (D.coeffLinearForm a))

/-- **The basic open of a linear form with a nonzero coefficient is nonempty**: the parameter
space is reduced, so only the zero function has empty basic open. -/
theorem nonempty_coeffOpen {a : D.basisIndex → D.k} {i₀ : D.basisIndex} (h : a i₀ ≠ 0) :
    ((D.coeffOpen a : D.parameterBase.Opens) : Set D.parameterBase).Nonempty := by
  let := D.isField
  by_contra hne
  rw [TopologicalSpace.Opens.not_nonempty_iff_eq_bot, coeffOpen,
    AlgebraicGeometry.basicOpen_eq_bot_iff] at hne
  exact D.coeffLinearForm_ne_zero h
    (D.parameterBaseΓEquiv.injective (hne.trans (map_zero _).symm))

/-- **A `k`-rational parameter of the open is not annihilated by the coefficient vector.** The
`k`-point of `𝔸^r_k` with coordinate tuple `c` evaluates the linear form at `c`, and a point of
`Spec k` lies in the basic open of a global function exactly when that function is nonzero. -/
theorem sum_ne_zero_of_parameterPoint_mem_coeffOpen (a : D.basisIndex → D.k)
    (c : Fin (Module.finrank D.k D.V) → D.k)
    (hc : ∀ q : Spec (.of D.k), D.parameterPoint c q ∈ D.coeffOpen a) :
    ∑ i, a i * c i.down ≠ 0 := by
  let := D.isField
  intro h0
  obtain ⟨q⟩ : Nonempty (Spec (.of D.k)) := inferInstance
  have hmem : q ∈ D.parameterPoint c ⁻¹ᵁ D.coeffOpen a := hc q
  rw [coeffOpen, Scheme.preimage_basicOpen_top,
    D.parameterPoint_appTop_parameterBaseΓEquiv c (D.coeffLinearForm a),
    D.eval_coeffLinearForm a (fun i => c i.down), h0, map_zero,
    Scheme.basicOpen_zero] at hmem
  exact hmem

/-! ### The germ of a member, read through the basis-free evaluation -/

/-- **The germ of `ψ(v)` at `x` avoids `𝔪_x²ℒ_x` exactly when `ev_x` does not kill `v`.** The
quotient `ℒ_x/𝔪_x²ℒ_x` is the target of the basis-free evaluation
`Stacks.Bertini.FamilyDivisors.evalVector`, and the class of the germ of `ψ(v)` in it *is* the
value of that evaluation at `v`. -/
theorem notMem_maximalSqSmul_iff_evalVector_ne_zero (x : D.X) (v : D.V) :
    (D.L.presheaf.Γgerm x).hom (D.sectionOf v) ∉ maximalSqSmul D.L x ↔ D.evalVector x v ≠ 0 := by
  refine not_congr ?_
  exact (Submodule.Quotient.mk_eq_zero (maximalSqSmul D.L x)).symm

/-! ### The general-position open -/

/-- **The general-position assertion of [Stacks, Tag 0FH7], with the `1`-jet surjection as its
only input.** If the evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x` of the linear system at a point `x` of
`X` is not identically zero, then there is a nonempty open of the parameter space `𝔸^r_k` such
that the member `∑ᵢ cᵢψ(vᵢ)` of every `k`-rational parameter `c` of it has germ at `x` outside
`𝔪_x²ℒ_x`.

This is the openness half of the assertion the source states and does not prove, and it costs no
hypothesis at all beyond `ev_x ≠ 0`: no smoothness, no algebraically closed base field, not even
closedness of `x`. The good locus is the complement of the linear subspace `ker ev_x`, which need
not be a basic open; but a *nonempty open inside it* is all that a generality statement needs, and
one is produced by choosing a linear functional `φ` on `V` killing `ker ev_x` and not killing a
vector that `ev_x` does not kill (`Submodule.exists_dual_map_eq_bot_of_notMem`, every module over
a field being projective). The coefficient vector `aᵢ = φ(vᵢ)` is then nonzero, so
`Stacks.Bertini.FamilyDivisors.coeffOpen` of it is nonempty, and a `k`-rational parameter `c` of
that open has `φ(∑ᵢ cᵢvᵢ) ≠ 0`, hence `∑ᵢ cᵢvᵢ ∉ ker ev_x`. -/
theorem exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero {x : D.X}
    (hev : D.evalVector x ≠ 0) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ∀ c : Fin (Module.finrank D.k D.V) → D.k,
        (∀ q : Spec (.of D.k), D.parameterPoint c q ∈ U) →
          (D.L.presheaf.Γgerm x).hom (D.constCoeffSection c) ∉ maximalSqSmul D.L x := by
  classical
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hev
  obtain ⟨φ, hφ0, hφker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := LinearMap.ker (D.evalVector x)) (x := v₀) (fun h => hv₀ h) inferInstance
  have hv₀sum : φ v₀ = ∑ i, D.basis.repr v₀ i * φ (D.basis i) := by
    conv_lhs => rw [← D.basis.sum_repr v₀]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hv₀sum ▸ hφ0)
  refine ⟨D.coeffOpen (fun i => φ (D.basis i.down)),
    D.nonempty_coeffOpen (i₀ := ULift.up i₀) (right_ne_zero_of_mul hi₀), fun c hc => ?_⟩
  have hsum := D.sum_ne_zero_of_parameterPoint_mem_coeffOpen
    (fun i => φ (D.basis i.down)) c hc
  have hφc : φ (∑ i, c i • D.basis i) ≠ 0 := by
    rw [map_sum, Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]]
    refine fun h0 => hsum ?_
    exact (Fintype.sum_equiv (Equiv.ulift (α := Fin (Module.finrank D.k D.V)))
      (fun i : D.basisIndex => φ (D.basis i.down) * c i.down)
      (fun j => c j * φ (D.basis j)) fun _ => mul_comm _ _).trans h0
  rw [D.constCoeffSection_eq_sectionOf c]
  refine (D.notMem_maximalSqSmul_iff_evalVector_ne_zero x (∑ i, c i • D.basis i)).mpr fun h0 => ?_
  have hmem : φ (∑ i, c i • D.basis i) ∈
      Submodule.map φ (LinearMap.ker (D.evalVector x)) :=
    Submodule.mem_map_of_mem (LinearMap.mem_ker.mpr h0)
  rw [hφker, Submodule.mem_bot] at hmem
  exact hφc hmem

/-- **The `1`-jet surjection from hypothesis (3) of [Stacks, Tag 0FD6]**: where the linear system
generates `L` and the morphism `φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion, the evaluation
at a closed point of a smooth `X` over an algebraically closed field is not identically zero —
indeed it is surjective
(`Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed`), and its target is
not the zero space, which `Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis` records by
making `coeffMap M` surjective onto a nontrivial `k^{n+1}`. -/
theorem evalVector_ne_zero_of_isImmersive [IsAlgClosed D.k] [Smooth D.toBase] {p : ℕ}
    {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    D.evalVector x ≠ 0 := by
  obtain ⟨n, hn⟩ := D.exists_natCast_eq_topologicalKrullDimAt_of_isClosed hx
  obtain ⟨M, hMsurj, hMker⟩ := D.exists_evalMatrix_of_basis himm b hx hn
  obtain ⟨c₀, hc₀⟩ := hMsurj (fun _ => 1)
  have hne : evalCoord (fun i => D.sectionOf (b i)) D.toBase x
      (fun l => c₀ (D.basisIndexEquiv b l)) ≠ 0 := by
    intro h
    have h2 := (hMker c₀).mpr h
    rw [hc₀] at h2
    exact one_ne_zero (congrFun h2 0)
  rw [D.evalCoord_sectionOf_apply b x] at hne
  exact fun h0 => hne (by rw [h0, LinearMap.zero_apply])

/-- **The general-position assertion of [Stacks, Tag 0FH7], under hypotheses (2) and (3) of
[Stacks, Tag 0FD6].** At a closed point `x` of a smooth `X` over an algebraically closed field,
if the linear system generates `L` and the morphism `φ_{L,ψ} : X → 𝐏(V)` is an immersion, then
there is a nonempty open of the parameter space `𝔸^r_k` at every `k`-rational parameter of which
the corresponding member has germ at `x` outside `𝔪_x²ℒ_x`.

The two halves are
`Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_of_isImmersive`, the `1`-jet surjection, and
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero`,
the openness. The hypotheses here are the *sufficient* condition the surjection is available
under in this library; they are not the source's, which reads the surjection off the very
ampleness of a high power of `ℒ` for the subsystem of sections vanishing at the points being
separated — a subsystem that does not generate `L` at those very points, so hypothesis (2) fails
for it and the statement above, taking `ev_x ≠ 0` directly, is the form a consumer of the source's
argument needs. -/
theorem exists_nonempty_opens_notMem_maximalSqSmul_constCoeffSection [IsAlgClosed D.k]
    [Smooth D.toBase] {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ∀ c : Fin (Module.finrank D.k D.V) → D.k,
        (∀ q : Spec (.of D.k), D.parameterPoint c q ∈ U) →
          (D.L.presheaf.Γgerm x).hom (D.constCoeffSection c) ∉ maximalSqSmul D.L x :=
  D.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero
    (D.evalVector_ne_zero_of_isImmersive himm hx)

/-! ### A general member that is smooth and in general position -/

/-- **A nonzero member of the linear system whose divisor is smooth and whose `1`-jet at a closed
point is nonzero.** The two conditions are each satisfied on a nonempty open of `𝔸^r_k` — the
first by a `Stacks.Bertini.FamilyDivisors.ForGeneral` smoothness conclusion of
[Stacks, Tag 0FD6], the second by
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_constCoeffSection` —
and the parameter space is irreducible
(`Stacks.Bertini.FamilyDivisors.irreducibleSpace_parameterBase`), so the two opens meet;
`Stacks.Bertini.FamilyDivisors.exists_parameterPoint_mem` then produces a nonzero `k`-rational
parameter in the intersection and
`Stacks.Bertini.FamilyDivisors.smooth_divisor_of_smooth_specializedDivisor` carries the smoothness
of `H_v` back from `X_k` to `X`.

This is the conjunction the Bertini step of [Stacks, Tag 0FH7] needs: the smoothness conclusion
alone leaves the divisor smooth only away from the points where general position is being imposed.
The infinitude of the base field is where it is used, exactly as in the source. -/
theorem exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_of_evalVector_ne_zero [Infinite D.k]
    {x : D.X} (hev : D.evalVector x ≠ 0)
    (h : D.ForGeneral fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :
    ∃ w : D.V, w ≠ 0 ∧ Smooth ((D.divisor w).subschemeι ≫ D.toBase) ∧
      (D.L.presheaf.Γgerm x).hom (D.sectionOf w) ∉ maximalSqSmul D.L x := by
  have := D.irreducibleSpace_parameterBase
  obtain ⟨U, hUne, hU⟩ := h
  obtain ⟨W, hWne, hW⟩ := D.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero hev
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hev
  have hr : 0 < Module.finrank D.k D.V :=
    Module.finrank_pos_iff.mpr ⟨⟨v₀, 0, fun hw => hv₀ (by rw [hw, map_zero]; rfl)⟩⟩
  have hinter : ((U ⊓ W : D.parameterBase.Opens) : Set D.parameterBase).Nonempty := by
    obtain ⟨y, -, hy⟩ := (IrreducibleSpace.isIrreducible_univ D.parameterBase).2
      (U : Set D.parameterBase) (W : Set D.parameterBase) U.isOpen W.isOpen
      (let ⟨y, hy⟩ := hUne; ⟨y, trivial, hy⟩) (let ⟨y, hy⟩ := hWne; ⟨y, trivial, hy⟩)
    exact ⟨y, hy⟩
  obtain ⟨c, hc0, hcU⟩ := D.exists_parameterPoint_mem hr (U ⊓ W) hinter
  refine ⟨∑ i, c i • D.basis i, fun hw => hc0 ?_,
    D.smooth_divisor_of_smooth_specializedDivisor c
      (hU D.k c (fun q => (hcU q).1) c rfl), ?_⟩
  · exact funext (Fintype.linearIndependent_iff.mp D.basis.linearIndependent c hw)
  · rw [← D.constCoeffSection_eq_sectionOf c]
    exact hW c fun q => (hcU q).2

/-- **A nonzero member whose divisor is smooth and whose `1`-jet at a closed point is nonzero,
under hypotheses (2) and (3) of [Stacks, Tag 0FD6].** This is
`Stacks.Bertini.FamilyDivisors.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_of_evalVector_`
`ne_zero` with the nonvanishing of the evaluation supplied by
`Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_of_isImmersive`; the infinitude of the base
field is then no longer a binder, an algebraically closed field being infinite. -/
theorem exists_ne_zero_smooth_divisor_notMem_maximalSqSmul [IsAlgClosed D.k]
    [Smooth D.toBase] {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    (h : D.ForGeneral fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :
    ∃ w : D.V, w ≠ 0 ∧ Smooth ((D.divisor w).subschemeι ≫ D.toBase) ∧
      (D.L.presheaf.Γgerm x).hom (D.sectionOf w) ∉ maximalSqSmul D.L x :=
  D.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_of_evalVector_ne_zero
    (D.evalVector_ne_zero_of_isImmersive himm hx) h

end Stacks.Bertini.FamilyDivisors

end
