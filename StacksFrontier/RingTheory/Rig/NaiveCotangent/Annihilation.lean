module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.PresentationIndependence
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ProIsomorphism

/-!
# Annihilation of the cohomology: the equivalence (0AJW) ⇔ (0AJX) of Stacks 0AJU

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` be an object of the category
(Stacks 0AL4), and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`.  Writing
`Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, two of the equivalent conditions of Stacks 0AJU are

* (0AJW) there is a `c ≥ 0` such that `I^c` annihilates `H^i(NL^∧_{B/A})`, `i = -1, 0`;
* (0AJX) there is a `c ≥ 0` such that `I^c` annihilates `H^i(NL_{Bₙ/Aₙ})`, `i = -1, 0`, for
  every `n ≥ 1`.

This file proves that equivalence.  The source discharges it by citing the strict
pro-isomorphism of the two systems `{NL^∧_{B/A} ⊗_B Bₙ}` and `{NL_{Bₙ/Aₙ}}` (Stacks 0AJS (1),
available here as `Rig.CompletedPolynomialPresentation.smul_top_le_conormalSub` and
`Rig.CompletedPolynomialPresentation.exists_conormalSub_le_smul_top`, the two halves of the
Artin–Rees sandwich) and omitting the details.  The details are the two directions of the
annihilation transport, and they are genuinely different:

* **Forward.**  `H⁰` is a cokernel, so it is literally the same for `NL_{Bₙ/Aₙ}` as for
  `NL^∧_{B/A} ⊗_B Bₙ` and is a quotient of `H⁰(NL^∧_{B/A})`; annihilation passes to it with
  the same exponent.  `H⁻¹` is a *kernel*, and a surjective chain map gives no surjection
  there — but no shift is needed either.  If `x ∈ J / J²` has `d x ∈ IⁿB · (⨁ B dxᵢ)`, write
  `d x = ∑ aᵢ yᵢ` with `aᵢ ∈ IⁿB`; annihilation of `H⁰` by `a` makes each `a yᵢ` a
  derivative `d zᵢ`, so `a · d x = d (∑ aᵢ zᵢ)` with `∑ aᵢ zᵢ ∈ IⁿB · (J / J²)`; hence
  `a x − ∑ aᵢ zᵢ ∈ H⁻¹`, and a second factor `a'` annihilating `H⁻¹` gives
  `a' a x ∈ IⁿB · (J / J²)`.  So the exponent is *doubled* and the shift is unused:
  `NaiveCotangent.AnnihilatesCohomology.quotBySmulTop`.
* **Backward.**  Here the shift is what is used, and the surjection runs the wrong way.  An
  element `x` of `H⁻¹(NL^∧_{B/A}) = ker d` is a cohomology class of *every* `NL_{Bₙ/Aₙ}`, so
  `a x` lies in the submodule divided out at level `n`, which the Artin–Rees sandwich puts
  inside `I^{n−c₀}B · (J / J²)`.  Letting `n` grow, `a x` lies in `IᵐB · (J / J²)` for every
  `m`, and the conormal module is `I`-adically separated
  (`Rig.completedCotangent_isAdicComplete`), so `a x = 0`.  The same argument runs for `H⁰`
  using that `H⁰(NL^∧_{B/A})` is a finite module over the `I`-adically complete Noetherian
  ring `B`.  The exponent is *unchanged*.

So the `H⁻¹` half needs no interleaving of the two comparison maps: one direction is
elementary with a doubled exponent, and the other is the shift plus adic separatedness.

## Main definitions

* `NaiveCotangent.AnnihilatesCohomology`: an ideal annihilates both cohomology modules of a
  two-term complex.

## Main results

* `NaiveCotangent.AnnihilatesCohomology.quotBySmulTop`: the forward transport, generic — if
  `𝔟` annihilates the cohomology of `X` and `U` is a submodule of `X₁` containing `𝔞 X₁` and
  carried into `𝔞 X₀` by the differential, then `𝔟²` annihilates the cohomology of
  `X₁ / U ⟶ X₀ / 𝔞 X₀`.
* `NaiveCotangent.AnnihilatesCohomology.modIdeal`: the special case `U = 𝔞 X₁`, i.e.
  annihilation passes from `X` to `X ⊗_S S / 𝔞` with the exponent doubled.
* `Rig.CompletedNaiveCotangentComplex.annihilatesCohomology_reducedComplex`: **(0AJW) ⇒
  (0AJX)**.
* `Rig.CompletedNaiveCotangentComplex.annihilatesCohomology_twoTerm`: **(0AJX) ⇒ (0AJW)**.
* `Rig.CompletedNaiveCotangentComplex.exists_annihilator_twoTerm_iff_forall_reducedComplex`:
  **Stacks 0AJU, (0AJW) ⇔ (0AJX)**.
* `Rig.CompletedNaiveCotangentComplex.annihilatesCohomology_adicIdeal_pow_iff`: annihilation
  by the ideal `IᶜB = B.adicIdeal ^ c` is the source's elementwise condition "annihilated by
  `I^c`", because an annihilator is an ideal.

## Implementation notes

`NL_{Bₙ/Aₙ}` is named here, as in Stacks 0AJS (1), by
`Rig.CompletedNaiveCotangentComplex.reducedComplex` — the quotient of `NL^∧_{B/A}` by the
image of `J ∩ Iⁿ A⟨x⟩` in degree `-1` and by `IⁿB · (⨁ B dxᵢ)` in degree `0`.  That is the
object the comparison of Stacks 0AJS (1) produces.  Identifying it with the naive cotangent
complex of the genuine `Algebra.Generators Aₙ Bₙ (Fin r)` of
`Rig.CompletedPolynomialPresentation.reductionGenerators` is a separate statement (the
modular law for `J ∩ (J² + Kⁿ)` together with `Algebra.Generators.cotangentSpaceBasis`) and
is not used or needed here.

That is why the tag on the main theorem carries the sublabel *for the reduced complexes*.
Condition (4) of Stacks 0AJU can also be read through `Algebra.naiveCotangentComplex Aₙ Bₙ`,
i.e. through the *tautological* presentation of `Bₙ` over `Aₙ` and the categorical homology
of `HomologicalComplex.double`.  Deducing that reading from this one needs three further
identifications, none of them proved here: the one above; presentation independence of
`H⁻¹` and `H⁰` at level `n` (available in Mathlib as `Algebra.Generators.equivH1Cotangent`
and `Algebra.Extension.exact_cotangentComplex_toKaehler`); and the computation of the
homology of `HomologicalComplex.double` as the kernel and cokernel of its one differential.

All three are now proved, elsewhere:
`StacksFrontier/Homology/DoubleHomology.lean` for the `double`,
`StacksFrontier/RingTheory/NaiveCotangent/PresentationHomology.lean` for the presentation
independence, and `Rig/NaiveCotangent/ReductionComparison.lean` together with
`Rig/NaiveCotangent/ReductionIdentification.lean` for the identification of
`reducedComplex n` with `NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`.  The theorem below is the step they
are consumed by, and the bare `(3) iff (4)` label of the tag sits on
`Rig.isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated`; the sublabel here is kept
because it says truthfully what *this* theorem is about.

Annihilation is recorded as an inclusion of ideals into `Submodule.annihilator` and
`Module.annihilator` rather than elementwise, so that the ideal-theoretic manipulations —
`Ideal.mul_le` in the forward direction — are available with no bookkeeping;
`annihilatesCohomology_adicIdeal_pow_iff` converts to the source's elementwise form.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B)
-/

@[expose] public section

namespace NaiveCotangent

/-! ## Annihilation of the cohomology of a two-term complex -/

universe u v w

variable {S : Type u} [CommRing S]

/-- An ideal `𝔞` of `S` **annihilates the cohomology** of a two-term complex
`X : X₁ --d--> X₀` of `S`-modules if it annihilates both `H⁻¹ X = ker d` and
`H⁰ X = coker d`.  This is the shape of conditions (0AJW) and (0AJX) of Stacks 0AJU. -/
public structure AnnihilatesCohomology (𝔞 : Ideal S) (X : TwoTerm.{u, v, w} S) : Prop where
  /-- `𝔞` annihilates `H⁻¹ X = ker d`. -/
  hH₁ : 𝔞 ≤ (H₁ X).annihilator
  /-- `𝔞` annihilates `H⁰ X = coker d`. -/
  hH₀ : 𝔞 ≤ Module.annihilator S (H₀ X)

namespace AnnihilatesCohomology

variable {𝔞 𝔟 : Ideal S} {X Y : TwoTerm.{u, v, w} S}

/-- An element of an ideal annihilating the cohomology of `X` kills every cohomology class in
degree `-1`, that is, every element of the kernel of the differential. -/
public theorem smul_eq_zero_of_d_eq_zero (h : AnnihilatesCohomology 𝔞 X) {a : S} (ha : a ∈ 𝔞)
    {x : X.X₁} (hx : X.d x = 0) : a • x = 0 :=
  Submodule.mem_annihilator.mp (h.hH₁ ha) x hx

/-- An element of an ideal annihilating the cohomology of `X` carries every element of the
degree-`0` term into the image of the differential, since `H⁰ X` is the cokernel. -/
public theorem smul_mem_range (h : AnnihilatesCohomology 𝔞 X) {a : S} (ha : a ∈ 𝔞)
    (y : X.X₀) : a • y ∈ LinearMap.range X.d := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul]
  exact Module.mem_annihilator.mp (h.hH₀ ha) _

/-- Annihilation of the cohomology passes to a smaller ideal. -/
public theorem mono (h : AnnihilatesCohomology 𝔞 X) (hba : 𝔟 ≤ 𝔞) :
    AnnihilatesCohomology 𝔟 X :=
  ⟨hba.trans h.hH₁, hba.trans h.hH₀⟩

/-- Annihilation of `H⁰` transports forward along any chain map that is surjective in degree
`0`: a cokernel maps onto a cokernel. -/
public theorem hH₀_of_surjective (f : ChainMap X Y) (hf : Function.Surjective f.f₀)
    (h : 𝔞 ≤ Module.annihilator S (H₀ X)) : 𝔞 ≤ Module.annihilator S (H₀ Y) := by
  intro a ha
  refine Module.mem_annihilator.mpr fun z => ?_
  obtain ⟨w, rfl⟩ := surjective_onH₀ f hf z
  rw [← map_smul, Module.mem_annihilator.mp (h ha) w, map_zero]

end AnnihilatesCohomology

namespace TwoTerm

variable (X : TwoTerm.{u, v, w} S)

/-- The canonical surjection onto a quotient complex is surjective in degree `0`. -/
public theorem surjective_quotProj_f₀ (U : Submodule S X.X₁) (V : Submodule S X.X₀)
    (h : U ≤ V.comap X.d) : Function.Surjective (X.quotProj U V h).f₀ :=
  Submodule.mkQ_surjective V

end TwoTerm

/-- **The forward annihilation transport of Stacks 0AJU, (0AJW) ⇒ (0AJX).**  Let `X` be a
two-term complex of `S`-modules, let `𝔞` be an ideal of `S`, and let `U` be a submodule of
`X₁` containing `𝔞 X₁` and carried into `𝔞 X₀` by the differential — the situation of Stacks
0AJS (1), where `U` is the image of `J ∩ Iⁿ A⟨x⟩` in `J / J²`.  If an ideal `𝔟` annihilates
the cohomology of `X`, then `𝔟²` annihilates the cohomology of the quotient complex
`X₁ / U ⟶ X₀ / 𝔞 X₀`.

No shift is needed, and the hypothesis `U ⊆ I^{n-c} X₁` of the Artin–Rees sandwich is not
used: in degree `0` the cohomology is a quotient of `H⁰ X`, and in degree `-1` one factor of
`𝔟` corrects the class `x` by a derivative into the kernel of `d`, where the second factor
kills it.  The exponent is doubled because both factors are spent. -/
public theorem AnnihilatesCohomology.quotBySmulTop {X : TwoTerm.{u, v, w} S} {𝔞 𝔟 : Ideal S}
    {U : Submodule S X.X₁} (hU : (𝔞 • ⊤ : Submodule S X.X₁) ≤ U)
    (hd : U ≤ (𝔞 • ⊤ : Submodule S X.X₀).comap X.d) (h : AnnihilatesCohomology 𝔟 X) :
    AnnihilatesCohomology (𝔟 ^ 2) (X.quotBy U (𝔞 • ⊤) hd) := by
  refine ⟨?_, AnnihilatesCohomology.hH₀_of_surjective (X.quotProj U (𝔞 • ⊤) hd)
    (X.surjective_quotProj_f₀ _ _ hd) ((Ideal.pow_le_self two_ne_zero).trans h.hH₀)⟩
  rw [pow_two]
  refine Ideal.mul_le.mpr fun r hr s hs => Submodule.mem_annihilator.mpr ?_
  intro xbar hxbar
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U xbar
  have hdx : X.d x ∈ (𝔞 • ⊤ : Submodule S X.X₀) := (Submodule.Quotient.mk_eq_zero _).mp hxbar
  have key : ∃ w ∈ (𝔞 • ⊤ : Submodule S X.X₁), s • X.d x = X.d w := by
    refine Submodule.smul_induction_on hdx ?_ ?_
    · intro a ha y _
      obtain ⟨z, hz⟩ := h.smul_mem_range hs y
      exact ⟨a • z, Submodule.smul_mem_smul ha Submodule.mem_top, by
        rw [map_smul, hz, smul_comm]⟩
    · rintro y₁ y₂ ⟨w₁, hw₁, e₁⟩ ⟨w₂, hw₂, e₂⟩
      exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by rw [smul_add, e₁, e₂, map_add]⟩
  obtain ⟨w, hw, hwe⟩ := key
  have hrs : (r * s) • x = r • w := by
    rw [mul_smul, ← sub_eq_zero, ← smul_sub]
    refine h.smul_eq_zero_of_d_eq_zero hr ?_
    rw [map_sub, map_smul, hwe, sub_self]
  have hfin : Submodule.mkQ U ((r * s) • x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (hrs ▸ hU (Submodule.smul_mem _ r hw))
  rwa [map_smul] at hfin

/-- **Annihilation passes from `X` to its reductions `X ⊗_S S / 𝔞`, with the exponent
doubled.**  This is `AnnihilatesCohomology.quotBySmulTop` for the pair `(𝔞 X₁, 𝔞 X₀)`, i.e.
the direction of Stacks 0AJU, (0AJW) ⇒ (0AJX) that does not see the shift at all. -/
public theorem AnnihilatesCohomology.modIdeal {X : TwoTerm.{u, v, w} S} {𝔞 𝔟 : Ideal S}
    (h : AnnihilatesCohomology 𝔟 X) : AnnihilatesCohomology (𝔟 ^ 2) (X.modIdeal 𝔞) :=
  h.quotBySmulTop le_rfl (X.smul_top_le_comap_d 𝔞)

end NaiveCotangent

namespace Rig

namespace CompletedNaiveCotangentComplex

/-! ## The equivalence (0AJW) ⇔ (0AJX) of Stacks 0AJU -/

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  {P : CompletedPolynomialPresentation I B}

/-- Annihilation by the ideal `IᶜB = B.adicIdeal ^ c` of `B` is exactly the source's
elementwise condition that the cohomology be *annihilated by `I^c`*: an annihilator is an
ideal of `B`, so it contains the image of every element of `I^c` precisely when it contains
the ideal that image generates. -/
public theorem annihilatesCohomology_adicIdeal_pow_iff
    (X : NaiveCotangent.TwoTerm B.carrier) (c : ℕ) :
    NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c) X ↔
      (∀ a ∈ I ^ c, algebraMap A B.carrier a ∈ (NaiveCotangent.H₁ X).annihilator) ∧
        ∀ a ∈ I ^ c, algebraMap A B.carrier a ∈
          Module.annihilator B.carrier (NaiveCotangent.H₀ X) := by
  have hpow : B.adicIdeal ^ c = (I ^ c).map (algebraMap A B.carrier) :=
    (Ideal.map_pow (algebraMap A B.carrier) I c).symm
  refine ⟨fun h => ⟨fun a ha => h.hH₁ (hpow ▸ Ideal.mem_map_of_mem _ ha),
    fun a ha => h.hH₀ (hpow ▸ Ideal.mem_map_of_mem _ ha)⟩, fun h => ?_⟩
  rw [hpow]
  exact ⟨Ideal.map_le_iff_le_comap.mpr fun a ha => h.1 a ha,
    Ideal.map_le_iff_le_comap.mpr fun a ha => h.2 a ha⟩

/-- **Stacks 0AJU, (0AJW) ⇒ (0AJX).**  If `IᶜB` annihilates `H^i(NL^∧_{B/A})` for `i = -1, 0`
then `I^{2c}B` annihilates `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0` and *every* `n`.

The proof is the generic forward transport
`NaiveCotangent.AnnihilatesCohomology.quotBySmulTop` applied to the presentation of
`NL_{Bₙ/Aₙ}` as a quotient of `NL^∧_{B/A}`: the only input from Stacks 0AJS (1) is the easy
half `IⁿJ ⊆ J ∩ Iⁿ A⟨x⟩` of the Artin–Rees sandwich
(`Rig.CompletedPolynomialPresentation.smul_top_le_conormalSub`), which holds for every `n`
with no shift.  The exponent doubles because `H⁻¹` is a kernel: one factor of `IᶜB` corrects
a class by a derivative into `ker d` and the second kills it there. -/
public theorem annihilatesCohomology_reducedComplex (K : CompletedNaiveCotangentComplex P)
    {c : ℕ} (h : NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c) K.twoTerm) (n : ℕ) :
    NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ (2 * c)) (K.reducedComplex n) := by
  have hq := h.quotBySmulTop (P.smul_top_le_conormalSub n)
    (K.conormalSub_le_comap_differential n)
  rwa [← pow_mul, mul_comm c 2] at hq

/-- **The degree-`-1` half of Stacks 0AJU, (0AJX) ⇒ (0AJW).**  Suppose `IᶜB` annihilates the
cohomology of `NL_{Bₙ/Aₙ}` for every `n ≥ 1`.  Then every `a ∈ IᶜB` kills every class of
`H⁻¹(NL^∧_{B/A}) = ker d`, that is, every element of `J / J²` killed by the differential.

This is where the shift of Stacks 0AJS (1) enters, and the comparison map runs the wrong way:
`H⁻¹` is a kernel, so a surjective chain map gives no surjection on it.  Instead `x` with
`d x = 0` is a degree-`-1` class of *every* `NL_{Bₙ/Aₙ}`, so `a x` lies in the submodule
`conormalSub n` divided out at level `n`, and Artin–Rees
(`Rig.CompletedPolynomialPresentation.exists_conormalSub_le_smul_top`) puts that inside
`I^{n-c₀}B · (J / J²)`.  Taking `n = m + c₀` for every `m` shows that `a x` lies in
`IᵐB · (J / J²)` for all `m`, and the conormal module is `I`-adically separated by
`Rig.completedCotangent_isAdicComplete`, so `a x = 0`.  No exponent is lost. -/
public theorem smul_eq_zero_of_differential_eq_zero [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) {c : ℕ}
    (h : ∀ n ≥ 1, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
      (K.reducedComplex n))
    {a : B.carrier} (ha : a ∈ B.adicIdeal ^ c) {x : P.extension.Cotangent}
    (hx : K.differential x = 0) : a • x = 0 := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := P.exists_conormalSub_le_smul_top
  have hmem : ∀ m : ℕ,
      a • x ∈ (B.adicIdeal ^ m) • (⊤ : Submodule B.carrier P.extension.Cotangent) := by
    intro m
    have hn : m + c₀ ≥ c₀ := Nat.le_add_left c₀ m
    have hdn : (K.reducedComplex (m + c₀)).d
        (Submodule.mkQ (P.conormalSub (m + c₀)) x) = 0 := by
      change Submodule.mkQ ((B.adicIdeal ^ (m + c₀)) • (⊤ : Submodule B.carrier
        (Fin P.variableCount → B.carrier))) (K.differential x) = 0
      rw [hx, map_zero]
    have hcls : a • x ∈ P.conormalSub (m + c₀) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul]
      exact (h (m + c₀) (le_trans hc₀pos hn)).smul_eq_zero_of_d_eq_zero ha hdn
    have hle := hc₀ (m + c₀) hn hcls
    rwa [Nat.add_sub_cancel] at hle
  exact IsHausdorff.haus (completedCotangent_isAdicComplete P).toIsHausdorff (a • x)
    fun m => SModEq.zero.mpr (hmem m)

/-- **The degree-`0` half of Stacks 0AJU, (0AJX) ⇒ (0AJW).**  Suppose `IᶜB` annihilates the
cohomology of `NL_{Bₙ/Aₙ}` for every `n ≥ 1`.  Then every `a ∈ IᶜB` carries every element of
`⨁ᵢ B dxᵢ` into the image of the differential, that is, kills `H⁰(NL^∧_{B/A})`.

Here the comparison needs no shift — `H⁰(NL_{Bₙ/Aₙ}) = H⁰(NL^∧_{B/A}) / IⁿB · H⁰(NL^∧_{B/A})`
because the degree-`0` terms of the two systems agree on the nose — but the conclusion is
still about the complex rather than the system, so separatedness is again what closes the
argument: `a y` is a derivative modulo `IⁿB · (⨁ᵢ B dxᵢ)` for every `n`, and
`H⁰(NL^∧_{B/A})` is a finite module over the `I`-adically complete Noetherian ring `B`, hence
`I`-adically separated by the Krull intersection theorem. -/
public theorem smul_mem_range_differential [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) {c : ℕ}
    (h : ∀ n ≥ 1, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
      (K.reducedComplex n))
    {a : B.carrier} (ha : a ∈ B.adicIdeal ^ c) (y : Fin P.variableCount → B.carrier) :
    a • y ∈ LinearMap.range K.differential := by
  let : IsAdicComplete B.adicIdeal B.carrier := B.isAdicallyComplete
  have hmem : ∀ m : ℕ,
      Submodule.mkQ (LinearMap.range K.differential) (a • y) ∈
        (B.adicIdeal ^ m) • (⊤ : Submodule B.carrier
          ((Fin P.variableCount → B.carrier) ⧸ LinearMap.range K.differential)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨xbar, hxbar⟩ := (h m hm).smul_mem_range ha
      (Submodule.mkQ ((B.adicIdeal ^ m) •
        (⊤ : Submodule B.carrier (Fin P.variableCount → B.carrier))) y)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (P.conormalSub m) xbar
    have heq : Submodule.mkQ ((B.adicIdeal ^ m) •
        (⊤ : Submodule B.carrier (Fin P.variableCount → B.carrier))) (K.differential x)
          = a • Submodule.mkQ ((B.adicIdeal ^ m) •
            (⊤ : Submodule B.carrier (Fin P.variableCount → B.carrier))) y := hxbar
    have hsub : a • y - K.differential x ∈
        (B.adicIdeal ^ m) • (⊤ : Submodule B.carrier (Fin P.variableCount → B.carrier)) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, heq,
        sub_self]
    have himg := Submodule.mem_map_of_mem
      (f := Submodule.mkQ (LinearMap.range K.differential)) hsub
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, map_sub] at himg
    have hker : Submodule.mkQ (LinearMap.range K.differential) (K.differential x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ x)
    rwa [hker, sub_zero] at himg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
    (M := (Fin P.variableCount → B.carrier) ⧸ LinearMap.range K.differential)
    B.adicIdeal (IsAdicComplete.le_jacobson_bot B.adicIdeal)
  exact (Submodule.Quotient.mk_eq_zero _).mp
    (Submodule.mem_bot _ |>.mp (hbot.le (Submodule.mem_iInf _ |>.mpr hmem)))

/-- **Stacks 0AJU, (0AJX) ⇒ (0AJW).**  If `IᶜB` annihilates `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0`
and every `n ≥ 1`, then the same `IᶜB` annihilates `H^i(NL^∧_{B/A})`.

This is the direction in which the shift of Stacks 0AJS (1) is used, and in which the
comparison maps run the wrong way: `H⁻¹` is a kernel, so there is no surjection
`H⁻¹(NL_{Bₙ/Aₙ}) → H⁻¹(NL^∧_{B/A})` to transport along.  Instead, a class
`x ∈ H⁻¹(NL^∧_{B/A}) = ker d` is a cohomology class of *every* `NL_{Bₙ/Aₙ}`, so for `a ∈ IᶜB`
the element `a x` lies in the submodule `J ∩ Iⁿ A⟨x⟩ · (J / J²)` divided out at level `n`,
which the Artin–Rees half
`Rig.CompletedPolynomialPresentation.exists_conormalSub_le_smul_top` puts inside
`I^{n-c₀}B · (J / J²)`.  Letting `n` grow, `a x` lies in `IᵐB · (J / J²)` for every `m`, and
the conormal module is `I`-adically separated by
`Rig.completedCotangent_isAdicComplete`, so `a x = 0`.  In degree `0` the same argument runs
with `H⁰(NL^∧_{B/A})`, a finite module over the `I`-adically complete Noetherian ring `B`,
in place of the conormal module.  The exponent is unchanged. -/
public theorem annihilatesCohomology_twoTerm [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) {c : ℕ}
    (h : ∀ n ≥ 1, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
      (K.reducedComplex n)) :
    NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c) K.twoTerm := by
  refine ⟨fun a ha => Submodule.mem_annihilator.mpr fun x hx =>
      K.smul_eq_zero_of_differential_eq_zero h ha hx,
    fun a ha => Module.mem_annihilator.mpr fun z => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.twoTerm.d) z
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact K.smul_mem_range_differential h ha y

/-- **Stacks 0AJU, the equivalence of (0AJW) and (0AJX).**  For a completed polynomial
presentation `B = A⟨x₁, …, x_r⟩ / J` of an object `B` of the category (Stacks 0AL4) over a
Noetherian ring `A`, the following are equivalent:

* some power of `I` annihilates `H^i(NL^∧_{B/A})` for `i = -1, 0`;
* some power of `I` annihilates `H^i(NL_{Bₙ/Aₙ})` for `i = -1, 0` and all `n ≥ 1`.

Here `NL_{Bₙ/Aₙ}` is `Rig.CompletedNaiveCotangentComplex.reducedComplex`, the object the
strict pro-isomorphism of Stacks 0AJS (1) produces: the quotient of `NL^∧_{B/A}` by the image
of `J ∩ Iⁿ A⟨x⟩` in degree `-1` and by `IⁿB · (⨁ B dxᵢ)` in degree `0`.  The forward
implication doubles the exponent and the backward one preserves it; see
`annihilatesCohomology_reducedComplex` and `annihilatesCohomology_twoTerm`.  Annihilation by
the ideal `IᶜB` is the source's elementwise condition by
`annihilatesCohomology_adicIdeal_pow_iff`, and the left-hand side is condition (3) on the
nose: `H⁻¹` is `LinearMap.ker K.differential` and `H⁰` is
`(Fin r → B) ⧸ LinearMap.range K.differential`.

The sublabel records that `NL_{Bₙ/Aₙ}` is taken in the shape Stacks 0AJS (1) produces; see
the implementation notes for the identifications that would be needed to read condition (4)
through `Algebra.naiveCotangentComplex Aₙ Bₙ` instead. -/
@[stacks 0AJU "(3) iff (4) for the reduced complexes"]
public theorem exists_annihilator_twoTerm_iff_forall_reducedComplex [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) :
    (∃ c : ℕ, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c) K.twoTerm) ↔
      ∃ c : ℕ, ∀ n ≥ 1, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
        (K.reducedComplex n) :=
  ⟨fun ⟨c, hc⟩ => ⟨2 * c, fun n _ => K.annihilatesCohomology_reducedComplex hc n⟩,
    fun ⟨c, hc⟩ => ⟨c, K.annihilatesCohomology_twoTerm hc⟩⟩

end CompletedNaiveCotangentComplex

end Rig

end
