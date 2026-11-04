module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Cohen-ring reduction in Epp's theorem

Step 5 of the Stacks Project's proof of Epp's theorem (Tag 09F9) is a reduction *upwards*: one
starts from a complete discrete valuation ring `A` whose residue field `k` is the perfect core
`⋂_{n ≥ 1} κ_B^{p^n}` of the residue field upstairs, interposes a third discrete valuation ring
`Λ` — a Cohen ring for `κ_B` in the mixed characteristic case, `κ_B[[t]]` in the equicharacteristic
case — and arrives at a tower
$$ A \to Λ \to B $$
in which `A → Λ` is formally smooth in the adic topology and `B` is *finite* over `Λ`.  That triple
is the input shape of Lemma 09F8, which is how the proof ends.

The Stacks text splits the construction of the tower into three moves, and this file addresses
them separately.

* **(a)** There is a ring map `A → Λ` lifting `k → κ_B` and sending a uniformizer to a uniformizer,
  and it is formally smooth in the adic topology because `k ⊂ κ_B` is separable (Tag 09E7).
* **(b)** Hence, `B` being complete, the given map `A → B` factors as `A → Λ → B` (Tag 07NJ).
* **(c)** `Λ` and `B` are complete discrete valuation rings with the same residue field, so `B` is
  finite over `Λ` (Tag 031D).

What is proved here is **(a)** and **(c)**, and their combination into the reduced situation.

**(c)** is the substantial half.  `Module.Finite Λ B` is not visible in advance: `B` is only known
through its residue field, and the finite generating set has to be manufactured.  The route is the
one Tag 031D is designed for.  Writing `e` for the ramification index of `Λ → B` and `π` for a
uniformizer of `B`, surjectivity of `κ_Λ → κ_B` gives `B = Λ·1 + 𝔪_B`, and multiplying that
identity by `π^i` unwinds the `𝔪_B`-adic filtration one step at a time:
`𝔪_B^i = Λ·π^i + 𝔪_B^{i+1}`.  After `e` steps the tail is `𝔪_B^e = 𝔪_Λ B`, so `B/𝔪_Λ B` is
generated over `Λ` — hence over `κ_Λ` — by `1, π, …, π^{e-1}`.  Separatedness `⋂_n 𝔪_Λ^n B = 0`
comes from Krull's intersection theorem applied to `B`, and Tag 031D converts the two facts into
finiteness.  Only `Λ` is assumed complete: the completeness of `B` that the source also assumes is
not used, since Krull's theorem covers separatedness for any Noetherian local domain.

**(b)** is not proved *here*, and the factorisation `A → Λ → B` appears in
`isWeaklyUnramified_and_formallySmoothNAdic_and_module_finite_of_tower` as a hypothesis
(`Algebra A B` together with `IsScalarTower A Λ B`) rather than as a conclusion.  The existence of
`Λ` itself — a Cohen ring for `κ_B`, or `κ_B[[t]]` — is likewise assumed rather than constructed.

**No obstruction from the topological form of Tag 07NJ.**  Tag 07NJ is available as
`RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic`, in the topological form. It might
seem that the bridge `RingHom.formallySmoothTop_iff_formallySmoothNAdic` to the
algebraic form used by Tag 09E7 requires the source ring to carry the *discrete* topology, which
`A` does not, and that applying it would need adic topologies on `A`, `Λ` and `B` together with
`IsAdic`, `IsLinearTopology`, closedness and continuity witnesses.  Neither is the case:

* the `DiscreteTopology` hypothesis is needed only by the *forward* direction of that equivalence.
  `RingHom.formallySmoothTop_of_formallySmoothNAdic`
  (`StacksFrontier.RingTheory.FormallySmooth.Adic`) is the direction actually wanted, stated without
  it; the `iff` is now derived from it, with its own statement unchanged;
* the "not built" infrastructure is `WithIdeal`, which installs the adic topology and carries
  `IsTopologicalRing`, `IsLinearTopology` and a uniform structure with it, and makes `IsAdic` hold
  by `rfl`.

`Stacks.EppTheorem.exists_lift_of_formallySmoothNAdic`
(`StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectResidueComplete`) is step (b) in
algebraic form: from `FormallySmoothNAdic (algebraMap A Λ) (𝔪 Λ)`, completeness of `B`, and a ring
map `Λ → B ⧸ 𝔪_B` killing `𝔪_Λ` and compatible with `A → B`, it produces the factorisation.  It
calls Tag 07NJ rather than restating it.  This file is left stating the reduced situation, as its
deliverable, and the hypotheses above are unchanged; what has changed is that a caller can now
discharge the factorisation instead of assuming it.

Neither is the **final appeal to Tag 09F8 made**.  The deliverable of this file ends at the reduced
situation: `IsWeaklyUnramified A Λ`, formal smoothness of `A → Λ` in the `𝔪_Λ`-adic topology, and
`Module.Finite Λ B`.  Feeding those to Tag 09F8 is what completes Epp's theorem, and it is left to
the caller.

That appeal is made, over a **perfect** rather than algebraically closed
base residue field, by
`Stacks.EppTheorem.exists_finite_extension_isWeakSolution_of_perfectField_of_cohenTower` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectResidueComplete`, which consumes exactly
the reduced situation this file produces and concludes a weak solution for `A → B` with **no**
finiteness hypothesis on the fraction field extension.  It is conditional on the layer recursion
and not tagged.

The other reduction in the same part of the Stacks proof — the *downward* one over the base, which
replaces `A` by a Cohen ring `Λ` for `k` (or by `k[[t]]`) and transports a weak solution for
`Λ → B` to one for `A → B` along Tag 09ES — is not treated here.  It needs the same Tag 07NJ
lifting for `Λ → A` in the mixed characteristic case, and in the equicharacteristic case a form of
the Cohen structure theorem (Tag 032A) presenting `A` as a quotient of a *one*-variable power
series ring over `k` with `t ↦ π`.

*That last shape exists, and is stronger than a quotient.*
`Stacks.EppTheorem.exists_powerSeriesRingEquiv_of_irreducible`
(`EqualCharacteristicStructure.lean`) gives an **isomorphism** `κ_R⟦X⟧ ≃+* R` with `X ↦ π` and the
residue map split on constants, which is precisely the one-variable presentation needed.
The multivariate provider
`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries` is indeed the wrong
shape, but it is not the only one.  The *upward* interposition of this file uses that
isomorphism in `Stacks.EppTheorem.exists_isExtension_powerSeries_of_equalCharacteristic`.

## Main results

* `Module.Finite.of_top_le_span_sup_quotient`: if the whole module is spanned by a finite set
  together with a submodule `N`, then the quotient by `N` is a finite module.
* `IsDiscreteValuationRing.exists_sub_algebraMap_mem_maximalIdeal`: surjectivity of the residue
  field extension says exactly that `B = Λ + 𝔪_B`.
* `IsDiscreteValuationRing.pow_maximalIdeal_restrictScalars_le_span_sup` and
  `IsDiscreteValuationRing.top_le_span_pow_sup_pow_maximalIdeal`: one step, and then all `e` steps,
  of the unwinding `𝔪_B^i = Λ·π^i + 𝔪_B^{i+1}`.
* `IsDiscreteValuationRing.module_finite_of_residueField_map_surjective`: **step (c)** — an
  extension of discrete valuation rings with `Λ` complete and surjective residue field extension
  is finite.
* `IsDiscreteValuationRing.isWeaklyUnramified_of_irreducible_algebraMap`: a map of discrete
  valuation rings carrying a uniformizer to a uniformizer is weakly unramified.
* `IsDiscreteValuationRing.formallySmoothNAdic_of_irreducible_algebraMap`: **step (a)** — such a
  map is formally smooth in the adic topology as soon as its residue field extension is separable.
* `IsDiscreteValuationRing.isWeaklyUnramified_and_formallySmoothNAdic_and_module_finite_of_tower`:
  **the reduced situation**, steps (a) and (c) together, stated for a tower `A → Λ → B`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9), steps 4 and 5 of the
  proof
* [The Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
* [The Stacks Project, Tag 09E7](https://stacks.math.columbia.edu/tag/09E7)
* [The Stacks Project, Tag 07NJ](https://stacks.math.columbia.edu/tag/07NJ)
* [Epp, *Elimination of wild ramification*][epp1973]
-/

@[expose] public section

open IsLocalRing

/-- **A quotient by a submodule that covers all but a finite span is finite.**

If `⊤ ≤ span R S ⊔ N` with `S` finite, then `M ⧸ N` is generated over `R` by the images of `S`,
hence is a finite `R`-module.

This is the bookkeeping step of Tag 031D's finiteness hypothesis: the filtration argument produces
exactly a covering of this shape, with `N` the submodule `𝔪_Λ • ⊤` by which one is about to
divide. -/
theorem Module.Finite.of_top_le_span_sup_quotient {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {S : Set M} (hS : S.Finite) {N : Submodule R M}
    (h : (⊤ : Submodule R M) ≤ Submodule.span R S ⊔ N) :
    Module.Finite R (M ⧸ N) := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨N.mkQ '' S, hS.image _, ?_⟩
  rw [← Submodule.map_span, eq_top_iff]
  intro x _
  obtain ⟨b, rfl⟩ := N.mkQ_surjective x
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h (Submodule.mem_top : b ∈ ⊤))
  have hz0 : N.mkQ z = 0 := by
    have hker := Submodule.ker_mkQ N
    exact LinearMap.mem_ker.mp (by rw [hker]; exact hz)
  rw [map_add, hz0, add_zero]
  exact Submodule.mem_map_of_mem hy

namespace IsDiscreteValuationRing

variable {Λ B : Type*} [CommRing Λ] [CommRing B] [Algebra Λ B]

/-! ### Consequences of a surjective residue field extension -/

section Local

variable [IsLocalRing Λ] [IsLocalRing B] [IsLocalHom (algebraMap Λ B)]

/-- **A surjective residue field extension says `B = Λ + 𝔪_B`.**

If `κ_Λ → κ_B` is surjective then every `b : B` agrees with the image of some `c : Λ` modulo the
maximal ideal of `B`.  This is the only use made below of the hypothesis that `Λ` and `B` have
"the same residue field", and it is what lets the `𝔪_B`-adic filtration of `B` be unwound over
`Λ` rather than over `B`. -/
theorem exists_sub_algebraMap_mem_maximalIdeal
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B))) (b : B) :
    ∃ c : Λ, b - algebraMap Λ B c ∈ maximalIdeal B := by
  obtain ⟨x, hx⟩ := hres (residue B b)
  obtain ⟨c, rfl⟩ := residue_surjective x
  refine ⟨c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact hx.symm.trans (ResidueField.map_residue _ c)

end Local

/-! ### Unwinding the adic filtration over the base -/

section Filtration

variable [IsLocalRing Λ] [IsDomain B] [IsDiscreteValuationRing B]
  [IsLocalHom (algebraMap Λ B)]

/-- **One step of the filtration: `𝔪_B^i = Λ·π^i + 𝔪_B^{i+1}`.**

Let `π` be a uniformizer of `B`.  Viewing the ideals of `B` as `Λ`-submodules, the `i`-th power of
the maximal ideal is covered by the `Λ`-line through `π ^ i` together with the next power.

The proof is the identity `B = Λ + 𝔪_B` of `exists_sub_algebraMap_mem_maximalIdeal` multiplied
through by `π ^ i`: an element of `𝔪_B ^ i` is `d * π ^ i`, and writing
`d = c + (d - c)` with `c` from `Λ` and `d - c ∈ 𝔪_B` splits it as required. -/
theorem pow_maximalIdeal_restrictScalars_le_span_sup
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B)))
    {π : B} (hπ : Irreducible π) (i : ℕ) :
    ((maximalIdeal B ^ i : Ideal B)).restrictScalars Λ ≤
      Submodule.span Λ {π ^ i} ⊔ ((maximalIdeal B ^ (i + 1) : Ideal B)).restrictScalars Λ := by
  have hspan : maximalIdeal B = Ideal.span {π} := (irreducible_iff_uniformizer π).mp hπ
  intro b hb
  rw [Submodule.restrictScalars_mem, hspan, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at hb
  obtain ⟨d, rfl⟩ := hb
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal hres d
  have key : d * π ^ i = c • π ^ i + (d - algebraMap Λ B c) * π ^ i := by
    rw [Algebra.smul_def]; ring
  rw [key]
  refine Submodule.add_mem_sup (Submodule.mem_span_singleton.mpr ⟨c, rfl⟩) ?_
  rw [Submodule.restrictScalars_mem, pow_succ']
  exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ((mem_maximalIdeal _).mpr hπ.not_isUnit) i)

/-- **All `i` steps of the filtration at once.**

Iterating `pow_maximalIdeal_restrictScalars_le_span_sup`, the whole of `B` is covered, as a
`Λ`-module, by the span of `1, π, …, π ^ (i - 1)` together with `𝔪_B ^ i`.  Taking `i` to be the
ramification index of `Λ → B` makes the tail equal to `𝔪_Λ B`, which is what
`module_finite_of_residueField_map_surjective` needs. -/
theorem top_le_span_pow_sup_pow_maximalIdeal
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B)))
    {π : B} (hπ : Irreducible π) (i : ℕ) :
    (⊤ : Submodule Λ B) ≤
      Submodule.span Λ ((fun j => π ^ j) '' Set.Iio i) ⊔
        ((maximalIdeal B ^ i : Ideal B)).restrictScalars Λ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hins : Set.Iio (i + 1) = insert i (Set.Iio i) := by ext j; simp
    rw [hins, Set.image_insert_eq, Submodule.span_insert]
    refine ih.trans (sup_le (le_sup_of_le_left le_sup_right) ?_)
    exact (pow_maximalIdeal_restrictScalars_le_span_sup hres hπ i).trans
      (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)

end Filtration

/-! ### Step (c): finiteness over a complete base with the same residue field -/

section Finiteness

variable [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsDomain B] [IsDiscreteValuationRing B]

/-- **Step (c) of the Cohen-ring reduction: `B` is finite over `Λ`.**

Let `Λ → B` be an extension of discrete valuation rings with `Λ` complete, and suppose the induced
residue field extension `κ_Λ → κ_B` is surjective.  Then `B` is a finite `Λ`-module.

This is the form in which Tag 031D enters Epp's proof: in the Stacks text `Λ` and `B` are complete
discrete valuation rings with *the same* residue field, and finiteness of `B` over `Λ` is the last
missing piece of the input to Lemma 09F8.

Only `Λ` is assumed complete.  The source assumes `B` complete as well, but completeness of `B` is
used there only to know `⋂_n 𝔪_Λ^n B = 0`, which for the Noetherian local domain `B` already
follows from Krull's intersection theorem; and Tag 031D asks only for precompleteness of the base.

The generating set is `1, π, …, π ^ (e - 1)` for `π` a uniformizer of `B` and `e` the ramification
index of `Λ → B`, produced by `top_le_span_pow_sup_pow_maximalIdeal`. -/
theorem module_finite_of_residueField_map_surjective [IsExtension Λ B]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B))) :
    Module.Finite Λ B := by
  obtain ⟨π, hπ⟩ := exists_irreducible B
  set e := Stacks.DiscreteValuationRing.Ramification.ramificationIdx Λ B
  have hmap : (maximalIdeal Λ).map (algebraMap Λ B) = maximalIdeal B ^ e :=
    Stacks.DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx Λ
      B
  have hle : (maximalIdeal Λ).map (algebraMap Λ B) ≤ maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_le (algebraMap Λ B)
  have hN : maximalIdeal Λ • (⊤ : Submodule Λ B)
      = (maximalIdeal B ^ e : Ideal B).restrictScalars Λ := by
    rw [Ideal.smul_top_eq_map, hmap]
  have hsep : ⨅ n : ℕ, (maximalIdeal Λ ^ n) • (⊤ : Submodule Λ B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hx' : x ∈ (⨅ n : ℕ, maximalIdeal B ^ n : Ideal B) := by
      rw [Submodule.mem_iInf]
      intro n
      have h := hx n
      rw [Ideal.smul_top_eq_map, Ideal.map_pow, Submodule.restrictScalars_mem] at h
      exact Ideal.pow_right_mono hle n h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B)
      (maximalIdeal.isMaximal B).ne_top] at hx'
    simpa using hx'
  have hfinΛ : Module.Finite Λ (B ⧸ maximalIdeal Λ • (⊤ : Submodule Λ B)) :=
    Module.Finite.of_top_le_span_sup_quotient ((Set.finite_Iio e).image _)
      (by rw [hN]; exact top_le_span_pow_sup_pow_maximalIdeal hres hπ e)
  have hfinres : Module.Finite (Λ ⧸ maximalIdeal Λ)
      (B ⧸ maximalIdeal Λ • (⊤ : Submodule Λ B)) :=
    Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ maximalIdeal Λ)
      (B ⧸ maximalIdeal Λ • (⊤ : Submodule Λ B))
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    (maximalIdeal Λ) hsep hfinres

end Finiteness

/-! ### Step (a): a uniformizer-preserving map is formally smooth in the adic topology -/

section Unramified

universe u v

/-- **Step (a) of the Cohen-ring reduction: `A → Λ` is formally smooth in the adic topology.**

Let `A → Λ` be an extension of discrete valuation rings carrying a uniformizer of `A` to a
uniformizer of `Λ`, and suppose the residue field extension `κ_A → κ_Λ` is separable.  Then
`A → Λ` is formally smooth in the `𝔪_Λ`-adic topology.

This is the appeal to Tag 09E7 that the Stacks proof makes after choosing the Cohen ring `Λ` for
`κ_B`: the choice is made so that a uniformizer goes to a uniformizer, and separability of
`k ⊂ κ_B` is available because `k` is the perfect core of `κ_B`.  Here the separability is a
hypothesis; producing it is the business of the earlier steps of Tag 09F9. -/
@[ega "0 19.8.2" "(i), special case", sga "1 III 1.2" "more general"]
theorem formallySmoothNAdic_of_irreducible_algebraMap
    (A : Type u) (Λ : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra A Λ] [IsExtension A Λ]
    {πA : A} (_hπA : Irreducible πA) (h : Irreducible (algebraMap A Λ πA))
    (hsep : Algebra.IsSeparableExtension (ResidueField A) (ResidueField Λ)) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A Λ) (maximalIdeal Λ) :=
  (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A Λ).mpr
    ⟨isWeaklyUnramified_of_irreducible_algebraMap A Λ πA h, hsep⟩

end Unramified

/-! ### The reduced situation -/

section Reduction

universe u' v' w'

/-- **The Cohen-ring reduction of Tag 09F9, step 5: the reduced situation.**

Suppose given a tower `A → Λ → B` of discrete valuation rings, factoring the map `A → B` one
started with, in which

* `Λ` is complete — in Epp's proof `Λ` is a Cohen ring for `κ_B` in the mixed characteristic case
  and `κ_B[[t]]` in the equicharacteristic case;
* some uniformizer of `A` maps to a uniformizer of `Λ`;
* the residue field extension `κ_A → κ_Λ` is separable — in Epp's proof `κ_A` is the perfect core
  `⋂_n κ_B^{p^n}`, which is exactly what makes this hold;
* the residue field extension `κ_Λ → κ_B` is surjective — in Epp's proof `κ_Λ = κ_B` by
  construction of `Λ`.

Then `A → Λ` is weakly unramified and formally smooth in the `𝔪_Λ`-adic topology, and `B` is
finite over `Λ`.  That is precisely the situation Lemma 09F8 takes as input, and the Stacks proof
of Epp's theorem ends by invoking it.

**The final appeal to Tag 09F8 is deliberately left to the caller**, and is not a hypothesis that
this file discharges: the conclusion here *is* the reduced situation, not a weak solution.  The
09F8 provider in this tree presently carries an algebraically closed residue field hypothesis and
is being generalised separately.

Two further parts of the Stacks argument are hypotheses rather than conclusions, for the reasons
set out in the module docstring: the existence of `Λ` itself, and the factorisation of `A → B`
through it (`Algebra A B` with `IsScalarTower A Λ B`), which in the source comes from Tag 07NJ.

Both now have providers for a caller to use, so these are hypotheses of *this* lemma rather than
gaps in the development.  The factorisation is
`Stacks.EppTheorem.exists_lift_of_formallySmoothNAdic`.  For `Λ` in **equal** characteristic it is
`Stacks.EppTheorem.exists_isExtension_powerSeries_of_equalCharacteristic`, giving `Λ = κ_B⟦X⟧`;
  mixed
characteristic still needs Cohen-ring functoriality. -/
@[ega "0 19.8.2" "(i), special case", sga "1 III 1.2" "more general"]
theorem isWeaklyUnramified_and_formallySmoothNAdic_and_module_finite_of_tower
    (A : Type u') (Λ : Type v') (B : Type w')
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A Λ] [Algebra Λ B] [Algebra A B] [IsScalarTower A Λ B]
    [IsExtension A Λ] [IsExtension Λ B]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    {πA : A} (hπA : Irreducible πA) (hπΛ : Irreducible (algebraMap A Λ πA))
    (hsep : Algebra.IsSeparableExtension (ResidueField A) (ResidueField Λ))
    (hres : Function.Surjective (ResidueField.map (algebraMap Λ B))) :
    IsWeaklyUnramified A Λ ∧
      RingHom.FormallySmoothNAdic.{max u' v'} (algebraMap A Λ) (maximalIdeal Λ) ∧
        Module.Finite Λ B :=
  ⟨isWeaklyUnramified_of_irreducible_algebraMap A Λ πA hπΛ,
    formallySmoothNAdic_of_irreducible_algebraMap A Λ hπA hπΛ hsep,
    module_finite_of_residueField_map_surjective hres⟩

end Reduction

end IsDiscreteValuationRing

end
