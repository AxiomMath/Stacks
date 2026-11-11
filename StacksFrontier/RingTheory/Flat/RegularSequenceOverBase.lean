module

public import StacksFrontier.RingTheory.Flat.LocalCriterionNonNoetherian
public import StacksFrontier.RingTheory.Sequence.QuotientByMinimalGenerator
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Regular elements and regular sequences over the base, from the fibre over the closed point

Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation over
`R`, let `𝔪` be the maximal ideal of `R`, and let `M` be an `S`-module of finite presentation which
is flat over `R`. Stacks 046Z says that an `f ∈ S` which is a nonzerodivisor on the fibre `M/𝔪M`
is a nonzerodivisor on `M`, with `M/fM` again flat over `R`; Stacks 0470 says the same for a
sequence `f₁, …, f_c`, every partial quotient being flat over `R`. Both are stated in module form,
the source's case being `M = S`, which is stated separately for 0470 in the source's words.

## Main results

* `Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal`: Tag 046Z.
* `Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`: the module form
  of Tag 0470.
* `Module.Flat.isRegular_and_flat_quotient_ofList_of_isRegular_map_maximalIdeal`: Tag 0470, for the
  ring `S` itself.

## Implementation notes

046Z is the source's proof: apply 046Y to `LinearMap.lsmul S M f`. Both of 046Y's conclusions
specialise once two submodules are identified, and both identifications are equalities of
submodules rather than of quotients, so the two ways of writing a quotient of `M` never have to be
compared as types. The fibre: 046Y takes the quotient by `𝔪 • (⊤ : Submodule R M)` while 046Z and
0470 take it by `𝔪S • (⊤ : Submodule S M)`, and the second restricted to `R` is the first
(`Ideal.smul_restrictScalars`); the hypothesis is therefore transported at the level of membership.
The cokernel: 046Y produces `M ⧸ LinearMap.range (LinearMap.lsmul S M f)` and 046Z asks for
`M ⧸ Ideal.span {f} • ⊤`, the same submodule (`range_lsmul`).

0470 is induction on the length of the sequence with 046Z as its step: 046Z makes `f` regular on
`M` with `M/fM` flat over `R`, and the induction hypothesis applies to `M/fM`, whose fibre is
`(M/𝔪M)/f(M/𝔪M)` — that commutation of the two reductions is
`quotSMulTopQuotIdealSMulTopEquivComm`, Noether's third isomorphism theorem read in both orders.
The source's statement is the case `M = S`, with the hypothesis read on the images
`f̄₁, …, f̄_c` in the ring `S/𝔪S` (`isRegular_map_algebraMap_iff_self`) and `(f₁, …, f_i)S` being
the ideal `(f₁, …, f_i)` itself.

## References

* [Stacks Project, Tag 046Z](https://stacks.math.columbia.edu/tag/046Z)
* [Stacks Project, Tag 0470](https://stacks.math.columbia.edu/tag/0470)
-/

open IsLocalRing
open scoped Pointwise

/-! ### 046Z: one element -/

/-- The range of multiplication by `f` on an `S`-module `M` is the submodule `fM`. This is
`Ideal.range_mul` with the ring `A` replaced by a module. -/
private lemma range_lsmul {S M : Type*} [CommSemiring S] [AddCommMonoid M] [Module S M] (f : S) :
    LinearMap.range (LinearMap.lsmul S M f) = Ideal.span {f} • (⊤ : Submodule S M) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def, ← LinearMap.range_eq_map]
  rfl

/-- **Stacks 046Z.** Let `R → S` be a local homomorphism of local rings with `S` essentially of
finite presentation over `R`, let `𝔪` be the maximal ideal of `R`, and let `M` be an `S`-module of
finite presentation which is flat over `R`. If `f ∈ S` is a nonzerodivisor on the fibre `M/𝔪M`,
then `f` is a nonzerodivisor on `M` and `M/fM` is flat over `R`.

The source is the case `M = S`: `f` is a nonzerodivisor in `S` and `S/fS` is flat over `R`. Here
`𝔪M` is `𝔪S • ⊤` and `fM` is `Ideal.span {f} • ⊤`; see the module docstring. -/
@[stacks 046Z "Stated in module form (the source's case is `M := S`), with `𝔪M` spelled
`Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M)` and `fM` spelled
`Ideal.span {f} • ⊤`, and \"nonzerodivisor\" spelled `IsSMulRegular`. Hypothesis (1) is
`RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)), Mathlib having no such predicate.
The two conclusions are conjoined; see the module docstring.",
  ega "IV 11.3.8" "(c) ⇒ (a), special case"]
public theorem Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] [Module.Flat R M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) {f : S}
    (hf :
      IsSMulRegular (M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))) f) :
    IsSMulRegular M f ∧ Module.Flat R (M ⧸ (Ideal.span {f} • (⊤ : Submodule S M))) := by
  -- The fibre of 046Z and the fibre of 046Y are the same submodule of `M`.
  have hres :
    (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M)).restrictScalars R =
      maximalIdeal R • (⊤ : Submodule R M) := by
    rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  -- Hypothesis (3), read on elements: `f • m ∈ 𝔪M` forces `m ∈ 𝔪M`.
  have hcomap :
    Submodule.comap ((LinearMap.lsmul S M f).restrictScalars R)
        (maximalIdeal R • (⊤ : Submodule R M)) ≤
      maximalIdeal R • (⊤ : Submodule R M) := by
    intro m hm
    rw [← hres] at hm ⊢
    exact mem_of_isSMulRegular_quotient_of_smul_mem hf hm
  -- 046Y applied to `f • · : M → M`.
  obtain ⟨h1, h2⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal hS
      (LinearMap.lsmul S M f) ((Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).2 hcomap)
  exact ⟨h1, by rwa [← range_lsmul]⟩

/-! ### 0470: a sequence -/

/-- Reducing a module modulo two submodules commutes: `(M/p)/q(M/p)` and `(M/q)/p(M/q)` are both
`M/(p + q)`, so Noether's third isomorphism theorem read in the two orders identifies them. -/
private def quotientQuotientEquivComm {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (p q : Submodule S M) : ((M ⧸ p) ⧸ q.map p.mkQ) ≃ₗ[S] (M ⧸ q) ⧸ p.map q.mkQ :=
  Submodule.quotientQuotientEquivQuotientSup p q ≪≫ₗ Submodule.quotEquivOfEq _ _ (sup_comm p q) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup q p).symm

/-- Reducing a module modulo an element `f` and modulo an ideal `I` commutes: both
`(M/fM)/I(M/fM)` and `(M/IM)/f(M/IM)` are `M/(fM + IM)`. -/
private def quotSMulTopQuotIdealSMulTopEquivComm {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] (I : Ideal S) (f : S) :
    (QuotSMulTop f M ⧸ (I • ⊤ : Submodule S (QuotSMulTop f M))) ≃ₗ[S]
      QuotSMulTop f (M ⧸ (I • (⊤ : Submodule S M))) :=
  Submodule.quotEquivOfEq _ _
      (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]) ≪≫ₗ
    quotientQuotientEquivComm (f • ⊤) (I • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])

/-- The quotient of a module of finite presentation by the submodule `fM` is again of finite
presentation. -/
private lemma finitePresentation_quotSMulTop {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [Module.FinitePresentation S M] (f : S) :
    Module.FinitePresentation S (QuotSMulTop f M) :=
  Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective (f • (⊤ : Submodule S M)))
    (by
      rw [Submodule.ker_mkQ, ← Submodule.ideal_span_singleton_smul]
      exact Submodule.FG.smul (Submodule.fg_span_singleton f) Module.Finite.fg_top)

/-- A module carrying a regular sequence on one of its quotients is nonzero: the nonvanishing
clause of `RingTheory.Sequence.IsRegular` makes the quotient nonzero, and a quotient of a zero
module is zero. -/
private lemma nontrivial_of_isRegular_quotient {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] {p : Submodule S M} {fs : List S} (h : RingTheory.Sequence.IsRegular (M ⧸ p) fs) :
    Nontrivial M :=
  have := h.nontrivial
  (Submodule.mkQ_surjective p).nontrivial

/-- The flatness half of the inductive step of 0470: every partial quotient of `M` along `f :: l`
is flat over `R` as soon as `M` is and every partial quotient of `M/fM` along `l` is, since
`M/(f, l₁, …, l_i)M` is `(M/fM)/(l₁, …, l_i)(M/fM)`. -/
private lemma flat_quotient_ofList_take_cons_smul_top {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] (f : S) (l : List S)
    (h :
      ∀ i,
        Module.Flat R
          (QuotSMulTop f M ⧸ (Ideal.ofList (l.take i) • (⊤ : Submodule S (QuotSMulTop f M))))) :
    ∀ i, Module.Flat R (M ⧸ (Ideal.ofList ((f :: l).take i) • (⊤ : Submodule S M)))
  | 0 => Module.Flat.quotient_of_eq_bot (by simp)
  | i + 1 =>
    have := h i
    .of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M f (l.take i)).restrictScalars R)

/-- **Stacks 0470, module form.** Let `R → S` be a local homomorphism of local rings with `S`
essentially of finite presentation over `R`, let `𝔪` be the maximal ideal of `R`, and let `M` be an
`S`-module of finite presentation which is flat over `R`. If a sequence `f₁, …, f_c` of elements
of `S` is regular on the fibre `M/𝔪M`, then it is regular on `M` and every partial quotient
`M/(f₁, …, f_i)M` is flat over `R`.

The source is the case `M = S`, stated as
`Module.Flat.isRegular_and_flat_quotient_ofList_of_isRegular_map_maximalIdeal`. Here `𝔪M` is
`𝔪S • ⊤` and `M/(f₁, …, f_i)M` is `M ⧸ Ideal.ofList (fs.take i) • ⊤`; see the module docstring. -/
@[ega "0 15.1.16" "c)=>a), ess fin pres",
  ega "0 15.1.17" "(f_i) is M-regular",
  ega "IV 11.3.8" "c) ⇒ a)"]
public theorem Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] [Module.Flat R M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (fs : List S)
    (hfs :
      RingTheory.Sequence.IsRegular
        (M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))) fs) :
    RingTheory.Sequence.IsRegular M fs ∧
      ∀ i, Module.Flat R (M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule S M))) := by
  induction fs generalizing M with
  | nil =>
    -- The nonvanishing clause of `IsRegular` on the fibre makes the fibre, hence `M`, nonzero.
    have : Nontrivial M := nontrivial_of_isRegular_quotient hfs
    exact ⟨.nil S M, fun _ => Module.Flat.quotient_of_eq_bot (by simp)⟩
  | cons f l ih =>
    rw [RingTheory.Sequence.isRegular_cons_iff] at hfs
    obtain ⟨hreg, hflat⟩ :=
      Module.Flat.isSMulRegular_and_flat_quotient_smul_of_isSMulRegular_maximalIdeal hS hfs.1
    have : Module.FinitePresentation S (QuotSMulTop f M) := finitePresentation_quotSMulTop f
    have : Module.Flat R (QuotSMulTop f M) :=
      .of_linearEquiv
        ((Submodule.quotEquivOfEq _ _
              (Submodule.ideal_span_singleton_smul f ⊤).symm).restrictScalars
          R)
    obtain ⟨hregl, hflatl⟩ :=
      ih (M := QuotSMulTop f M)
        (((quotSMulTopQuotIdealSMulTopEquivComm _ f).isRegular_congr l).mpr hfs.2)
    exact ⟨.cons hreg hregl, flat_quotient_ofList_take_cons_smul_top f l hflatl⟩

/-- **Stacks 0470.** Let `R → S` be a local homomorphism of local rings, essentially of finite
presentation and flat, and let `𝔪` be the maximal ideal of `R`. If `f₁, …, f_c ∈ S` are such that
their images `f̄₁, …, f̄_c` form a regular sequence in `S/𝔪S`, then `f₁, …, f_c` is a regular
sequence in `S` and each quotient `S/(f₁, …, f_i)` is flat over `R`.

This is the case `M = S` of
`Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`. -/
@[stacks 0470 "The sequence is a `List S` and `(f₁, …, f_i)` is `Ideal.ofList (fs.take i)`, for
every `i` (beyond the length `c` the quotient is `S/(f₁, …, f_c)`). \"Regular sequence\" is
Mathlib's `RingTheory.Sequence.IsRegular`, which is Definition 00LF verbatim (nonvanishing clause
included), and the images `f̄_i` in `S/𝔪S` are `fs.map (Ideal.Quotient.mk _)`. Hypothesis (1) is
`RingHom.EssentiallyOfFinitePresentation`, Definition 00QM (2). The two conclusions are
conjoined."]
public theorem Module.Flat.isRegular_and_flat_quotient_ofList_of_isRegular_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (fs : List S)
    (hfs :
      RingTheory.Sequence.IsRegular (S ⧸ (maximalIdeal R).map (algebraMap R S))
        (fs.map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))))) :
    RingTheory.Sequence.IsRegular S fs ∧ ∀ i, Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) := by
  -- The hypothesis, read over `S` rather than over `S/𝔪S`.
  have hfs' :
      RingTheory.Sequence.IsRegular
        (S ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S S))) fs := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (RingTheory.Sequence.isRegular_map_algebraMap_iff_self (R := S)
      (T := S ⧸ (maximalIdeal R).map (algebraMap R S)) fs).mp
        (by rwa [Ideal.Quotient.algebraMap_eq])
  obtain ⟨hreg, hflat⟩ :=
    Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal (M := S) hS fs
      hfs'
  refine ⟨hreg, fun i => ?_⟩
  have h := hflat i
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
  exact h
