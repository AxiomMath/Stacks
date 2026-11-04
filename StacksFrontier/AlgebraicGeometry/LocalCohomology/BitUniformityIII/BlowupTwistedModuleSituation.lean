module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupCanonicalSections
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistDownVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# A `TwistedModuleSituation` on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. This file assembles `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation` — the
data and standing hypotheses of all five clauses of [Stacks, Tag 0GAA] — on that blowup, so
that clauses (3), (4) and (5) hold there and not only in the two degenerate witnesses
`topTwistedModuleSituation` and `affineTwistedModuleSituation`.

## What goes into it

Nothing new. The `ModuleSituation` underneath is
`Stacks.LocalCohomology.UniformityIII.blowupModuleSituationOf`, and the nine remaining fields
are the nine results that were proved for them one at a time:

* `Htr`, `HGtr` and the three naturality fields `HGtr_trans`, `pullbackToImage_tr`,
  `kernelToImage_tr` are `Stacks.LocalCohomology.UniformityIII.blowupHtr`,
  `…blowupHGtr`, `…blowupHGtr_comp`, `…blowupHtr_comp_δ_free` and
  `…toCycles_comp_blowupHGtr` of `BitUniformityIII/BlowupTwistDownCohomology.lean`, read on
  elements by `CategoryTheory.ConcreteCategory.congr_hom`;
* `dotted` and `kernelToImage_dotted` are
  `Stacks.LocalCohomology.UniformityIII.blowupDotted` and `…kernelToImage_blowupDotted` of
  `BitUniformityIII/BlowupTwistDownVanishing.lean`;
* `secM` and `secM_freeSections` are
  `Stacks.LocalCohomology.UniformityIII.twistedPullbackSecM` and
  `…twistedPullbackSecM_freeSections` of `BitUniformityIII/BlowupCanonicalSections.lean`.

The only field whose direction has to be turned around is `pullbackToImage_tr`: the δ-functor's
naturality square is stated with the connecting map second, and the field asks for it first.

## What this witness is not

It is not degenerate in the way the two existing witnesses are. `topTwistedModuleSituation` has
every `(A, n, c)`-module zero, and `affineTwistedModuleSituation` has `d = 0`, which makes the
case hypotheses of clauses (1), (2), (3) and (5) — `d ≥ 1`, `d ≥ 2`, `d ≥ 3`, `d ≥ 2` —
unsatisfiable, so those four clauses say nothing there. Here `d` is the field `d` of
`Stacks.LocalCohomology.UniformityIII.blowupSituationOf`, the Čech vanishing bound
`Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH` of the blowup, which
is not forced to be `0`; and the `(A, n, c)`-modules the witness is applied to need not be free
over `A ⧸ Iⁿ` (`Stacks.LocalCohomology.UniformityIII.not_free_quotPowANCModule`). Clause (4) at
this witness is a statement about the blowup's own `H⁰(X, 𝒪_X(q) ⊗ p^*M̃)` and about the
canonical map `twistedPullbackSecM` out of `(I^q/I^{q+n}) ⊗_A M`, not about zero modules.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupTwistedModuleSituationOf`: **the witness**, at any
  `q₀` with the defining property of `q(S)`, on the twisted pullbacks `𝒪_X(q) ⊗ p^*M̃`.
  `Stacks.LocalCohomology.UniformityIII.blowupTwistedModuleSituation` records the same clauses
  through `thickeningPullback` at `d = d(S)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.nonempty_twistedModuleSituation`:
  **`TwistedModuleSituation` is inhabited** for every Noetherian ring, every ideal and every
  pair of exponents `c ≤ n`.
* `Stacks.LocalCohomology.UniformityIII.blowupHtr_eq_zero`,
  `…surjective_twistedPullbackSecM` and `…range_blowupHtr_le`: **clauses (3), (4) and (5) of
  [Stacks, Tag 0GAA] on the blowup**, stated about the blowup's own cohomology.
* `Stacks.LocalCohomology.UniformityIII.nonempty_twistedModuleSituation_two`,
  `…nontrivial_quotPowANCModule_two` and `…not_free_quotPowANCModule_two`: the witness at a
  concrete `(A, I, n, c)` with `c ≥ 1`, applied to a nonzero module that is not free over
  `A ⧸ Iⁿ`.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **A `TwistedModuleSituation` on the blowup**: the data and standing hypotheses of all five
clauses of [Stacks, Tag 0GAA] hold for the blowup of `Spec(A)` in `I`, for a Noetherian ring
`A`, any ideal `I`, any `q₀` with the defining property of `q(S)` and any exponents `c ≤ n`.

Every field is a proved result about the blowup; see the module docstring for the list. -/
def blowupTwistedModuleSituationOf (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n) :
    TwistedModuleSituation A I n c where
  toModuleSituation := blowupModuleSituationOf I q₀ h n c hcn
  Htr M i q q' hq := (blowupHtr I (resModule I n M.1) i q q' hq).hom
  HGtr M i q q' hq := (blowupHGtr I i q q' hq (S := blowupPresShortComplex I n c M)).hom
  HGtr_trans M i q q' q'' hq hq' hq'' x :=
    ConcreteCategory.congr_hom
      (blowupHGtr_comp I i q q' q'' hq' hq hq'' (S := blowupPresShortComplex I n c M)) x
  pullbackToImage_tr M i q q' hq x :=
    (ConcreteCategory.congr_hom
      (blowupHtr_comp_δ_free I (blowupANCPres I n c M).shortExact_resShortComplex i q q' hq)
      x).symm
  kernelToImage_tr M i q q' hq x :=
    ConcreteCategory.congr_hom
      (toCycles_comp_blowupHGtr I i q q' hq (S := blowupPresShortComplex I n c M)) x
  dotted := blowupDotted I q₀ h n c hcn
  kernelToImage_dotted := kernelToImage_blowupDotted I q₀ h n c hcn
  secM := twistedPullbackSecM I q₀ h n c hcn
  secM_freeSections := twistedPullbackSecM_freeSections I q₀ h n c hcn

/-- **`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation` is inhabited for every
Noetherian ring, every ideal and every pair of exponents `c ≤ n`**, by the blowup:
`blowupTwistedModuleSituationOf` at the integer `qS I`.

This is the companion of `Stacks.LocalCohomology.UniformityIII.nonempty_moduleSituation` one
level up the tower; the two degenerate witnesses `topTwistedModuleSituation` and
`affineTwistedModuleSituation` give inhabitedness only for `I = A` and for the case where the
blowing up is an isomorphism. -/
theorem nonempty_twistedModuleSituation (n c : ℕ) (hcn : c ≤ n) :
    Nonempty (TwistedModuleSituation A I n c) :=
  ⟨blowupTwistedModuleSituationOf I (qS I) (isBaseThreshold_qS I) n c hcn⟩

/-! ### The three clauses of [Stacks, Tag 0GAA] that the witness discharges on the blowup -/

variable (q₀ : ℕ) (h : IsBaseThreshold I q₀) (n c : ℕ) (hcn : c ≤ n)

include h hcn in
/-- **[Stacks, Tag 0GAA], clause (3), on the blowup.** For an `(A, n, c)`-module `M` with
`c ≤ n`, in the case `d - 1 > i > 0` and `q ≥ q₀ + (d - 1 - i)c` the map
`Hⁱ(X, 𝒪_X(q) ⊗ p^*M̃) ⟶ Hⁱ(X, 𝒪_X(q - (d - 1 - i)c) ⊗ p^*M̃)` induced by `𝒪_X(q) ⟶ 𝒪_X(q')` is
zero.

This is `TwistedModuleSituation.Htr_eq_zero` at `blowupTwistedModuleSituationOf`; the point is
that it is now a statement about the blowup's own cohomology and its own twisting-down maps
rather than about an abstract witness. -/
theorem blowupHtr_eq_zero (M : ANCModule I n c) {i k : ℕ} {q r : ℤ} (hle : r ≤ q)
    (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hik : i + k + 1 = (exists_forall_subsingleton_blowupH I).choose)
    (hr : r + k * c = q) (hq : (q₀ : ℤ) + k * c ≤ q) :
    blowupHtr I (resModule I n M.1) i q r hle = 0 :=
  ModuleCat.hom_ext
    ((blowupTwistedModuleSituationOf I q₀ h n c hcn).Htr_eq_zero M hle hi hk hik hr hq)

/-- **[Stacks, Tag 0GAA], clause (4), on the blowup.** For an `(A, n, c)`-module `M` with
`c ≤ n`, in the case `i = 0`, `d ∈ {0, 1}` and `q ≥ q₀` the canonical map

`(I^q/I^{q+n}) ⊗_A M ⟶ H⁰(X, 𝒪_X(q) ⊗ p^*M̃)`

of `Stacks.LocalCohomology.UniformityIII.twistedPullbackSecM` is surjective.

As at the abstract level, the source is the tensor product and not the submodule `I^qM` of `M`,
for which the clause is false; see `Stacks.LocalCohomology.UniformityIII.powTensor`. -/
theorem surjective_twistedPullbackSecM (M : ANCModule I n c)
    {q : ℕ} (hd : (exists_forall_subsingleton_blowupH I).choose ≤ 1) (hq : q₀ ≤ q) :
    Function.Surjective (twistedPullbackSecM I q₀ h n c hcn M q) :=
  (blowupTwistedModuleSituationOf I q₀ h n c hcn).surjective_secM M hd hq

/-- **[Stacks, Tag 0GAA], clause (5), on the blowup.** For an `(A, n, c)`-module `M` with
`c ≤ n`, in the case `i = 0`, `d > 1` and `q ≥ q₀ + (d - 1)c` the image of
`H⁰(X, 𝒪_X(q) ⊗ p^*M̃) ⟶ H⁰(X, 𝒪_X(r) ⊗ p^*M̃)`, for `r = q - (d - 1)c`, lies in the image of
the canonical map of clause (4) at `r`. -/
theorem range_blowupHtr_le (M : ANCModule I n c) {k r : ℕ} {q : ℤ} (hle : (r : ℤ) ≤ q)
    (hk : 1 ≤ k) (hkd : k + 1 = (exists_forall_subsingleton_blowupH I).choose)
    (hr : (r : ℤ) + k * c = q) (hq : (q₀ : ℤ) + k * c ≤ q) :
    LinearMap.range (blowupHtr I (resModule I n M.1) 0 q (r : ℤ) hle).hom ≤
      LinearMap.range (twistedPullbackSecM I q₀ h n c hcn M r) :=
  (blowupTwistedModuleSituationOf I q₀ h n c hcn).range_Htr_le M hle hk hkd hr hq

/-! ### A concrete instance, and what it does and does not establish -/

section Concrete

/-- The image of `(2)` in `ℤ ⧸ (2)²` is a proper ideal. -/
private theorem map_mk_span_two_ne_top :
    Ideal.map (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)} ^ 2)) (Ideal.span {(2 : ℤ)} ^ 1) ≠ ⊤ := by
  rw [Ne, Ideal.map_eq_top_iff_of_ker_le _
      (by rw [Ideal.mk_ker]; exact Ideal.pow_le_pow_right (by lia))
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective),
    pow_one, Ideal.span_singleton_eq_top, Int.isUnit_iff]
  rintro (hc | hc) <;> lia

/-- **The witness elaborates at a concrete instance**: `A = ℤ`, `I = (2)`, `n = 2`, `c = 1`.

`nonempty_twistedModuleSituation` is already stated for every Noetherian ring, every ideal and
every `c ≤ n`, so this adds no generality; what it adds is a check that no hidden hypothesis
makes the family empty at a particular `(A, I, n, c)` with `c ≥ 1`. That is not idle: the
structure `Rig.PerturbedPresentation.LiftingInputs` downstream is `IsEmpty` for `0 < c`, since it
asks for a dual situation at every thickness, which is why
`Rig.PerturbedPresentation.LiftingInputsAboveExponent` asks for one only at the thicknesses
`m ≥ c`; a statement whose antecedent is an empty structure asserts nothing. -/
theorem nonempty_twistedModuleSituation_two :
    Nonempty (TwistedModuleSituation ℤ (Ideal.span {(2 : ℤ)}) 2 1) :=
  nonempty_twistedModuleSituation (Ideal.span {(2 : ℤ)}) 2 1 (by lia)

/-- At that instance the `(A, n, c)`-modules the witness is applied to include a nonzero one:
`(ℤ ⧸ 4) ⧸ (2)·(ℤ ⧸ 4) ≅ ℤ ⧸ 2`. So the clauses are not statements about zero modules there. -/
theorem nontrivial_quotPowANCModule_two :
    Nontrivial (quotPowANCModule (Ideal.span {(2 : ℤ)}) 2 1).1 :=
  nontrivial_quotPowANCModule (Ideal.span {(2 : ℤ)}) 2 1 map_mk_span_two_ne_top

/-- And that module is not free over `A ⧸ Iⁿ = ℤ ⧸ 4`, so clause (4) at this witness is not a
restatement of [Stacks, Tag 0GA7] (2), which computes the sections of `𝒪_{Yₙ}(q)` and so covers
only the free case.

What this section does **not** establish is that the invariant `d` of the witness is nonzero.
`d` is `(exists_forall_subsingleton_blowupH I).choose`, a chosen Čech vanishing bound, and
nothing here pins it down; the clauses whose case hypotheses ask for `d ≥ 1` therefore have no
concrete instance exhibited. The difference from `affineTwistedModuleSituation` is structural
rather than exhibited: there `d` is the literal `0`, so those clauses are unsatisfiable for
every `A` and `I`. -/
theorem not_free_quotPowANCModule_two :
    ¬ Module.Free (ℤ ⧸ (Ideal.span {(2 : ℤ)}) ^ 2)
      (quotPowANCModule (Ideal.span {(2 : ℤ)}) 2 1).1 :=
  not_free_quotPowANCModule (Ideal.span {(2 : ℤ)}) 2 1
    (by
      rw [Ne, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, pow_one]
      intro hc
      have h2 : (2 : ℤ) ∈ (Ideal.span {(2 : ℤ)}) ^ 2 :=
        hc (Ideal.mem_span_singleton_self 2)
      rw [show ((Ideal.span {(2 : ℤ)}) : Ideal ℤ) ^ 2 = Ideal.span {(4 : ℤ)} by
        rw [Ideal.span_singleton_pow]; norm_num, Ideal.mem_span_singleton] at h2
      lia)
    map_mk_span_two_ne_top

end Concrete

end Stacks.LocalCohomology.UniformityIII

end
