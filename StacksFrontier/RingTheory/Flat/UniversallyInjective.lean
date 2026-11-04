module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.PUnit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.EquationalCriterion
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Universally injective module maps

A map `f : M → N` of `R`-modules is *universally injective* when `f ⊗ id_Q` is injective for every
`R`-module `Q`. This file relates universal injectivity to flatness, to tensor products and
compositions, to faithfully flat ring maps and to localization, and shows that base change along
a universally injective ring map reflects injections, surjections and isomorphisms.

## Main definitions

* `UniversallyInjective`, `IsPureMono`, `UniversallyInjectivePoly`,
  `Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective`: universal injectivity
  of a module map, with the test modules in various universes.
* `Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapR`,
  `Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapRp`: the localization
  `f_q : M_q → M'_q` of a map of `S`-modules at a prime `q`, as a map of `R`-modules and of
  `R_p`-modules.
* `baseChangeUnit`: the map `M → M ⊗[R] S`, `m ↦ m ⊗ₜ 1`.

## Main results

* `Module.Flat.iff_forall_rTensor_injective_of_exact`: `M` is flat if and only if every short
  exact sequence `0 → M₁ → M₂ → M → 0` is universally exact.
* `Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top`: a map `f : M → M'` into a flat
  module is universally injective if and only if `M/IM → M'/IM'` is injective for every finitely
  generated ideal `I`.
* `universallyInjective_rTensor`: `u ⊗ id_N` is universally injective if `u` is.
* `comp_universallyInjective`: a composition of universally injective maps is universally
  injective.
* `faithfullyFlat_universallyInjective`, `faithfullyFlat_comap_map_eq`: a faithfully flat ring map
  `R → S` is universally injective, and `φ⁻¹(I S) = I` for every ideal `I ⊆ R`.
* `Stacks.UniversalInjectivity.LocalizationCriteria.universally_injective_check_stalks`: universal
  injectivity of a map of `S`-modules over `R` can be checked on localizations at primes or at
  maximal ideals of `S`, over `R` or over the localizations of `R`.
* `reflects_injections`, `reflects_surjections`, `reflects_isomorphisms`: base change along a
  universally injective ring map reflects injections, surjections and isomorphisms.
* `Stacks.Derivations.derivation_pow_char`: a derivation kills `p`-th powers in characteristic
  `p`.

## References

* [Stacks Project, Tag 058I](https://stacks.math.columbia.edu/tag/058I)
* [Stacks Project, Tag 058M](https://stacks.math.columbia.edu/tag/058M)
* [Stacks Project, Tag 0AS5](https://stacks.math.columbia.edu/tag/0AS5)
* [Stacks Project, Tag 05CH](https://stacks.math.columbia.edu/tag/05CH)
* [Stacks Project, Tag 05CI](https://stacks.math.columbia.edu/tag/05CI)
* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
* [Stacks Project, Tag 0H9I](https://stacks.math.columbia.edu/tag/0H9I)
-/

@[expose] public section

universe u v

/-! ## Flatness as complementarity with universal injectivity -/

namespace Stacks.UniversalInjectivity.FlatCriterion

/-- An `R`-module `M` is flat if and only if `f₁ ⊗ id_Q` is injective for every short exact
sequence `0 → M₁ →[f₁] M₂ →[f₂] M → 0` of `R`-modules and every `R`-module `Q`. -/
public theorem solution {R : Type u} [CommRing R]
    [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ ⦃M₁ M₂ : Type v⦄ [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
        (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M), Function.Injective f₁ →
        Function.Exact f₁ f₂ → Function.Surjective f₂ →
          ∀ (Q : Type v) [AddCommGroup Q] [Module R Q],
            Function.Injective (f₁.rTensor Q) := by
  rw [Module.Flat.iff_surjective_compRight_of_finitePresentation]
  constructor
  · intro hM M₁ M₂ _ _ _ _ f₁ f₂ h₁ h h₂
    have e := (h.universallyExact_tfae h₁ h₂).out 5 1
    exact e.mp fun P _ _ _ ↦ hM P f₂ h₂
  · intro hM P _ _ _ N _ _ φ hφ
    have h : Function.Exact (LinearMap.ker φ).subtype φ := LinearMap.exact_subtype_ker_map φ
    have h₁ : Function.Injective (LinearMap.ker φ).subtype := Subtype.val_injective
    have e := (h.universallyExact_tfae h₁ hφ).out 1 5
    exact e.mp (hM (LinearMap.ker φ).subtype φ h₁ h hφ) P

end Stacks.UniversalInjectivity.FlatCriterion

@[expose] public section

/-- An `R`-module `M` is flat if and only if every short exact sequence
`0 → M₁ →[f₁] M₂ →[f₂] M → 0` of `R`-modules is universally exact, that is, if and only if
`f₁ ⊗ id_Q : M₁ ⊗ Q → M₂ ⊗ Q` is injective for every such sequence and every `R`-module `Q`. -/
@[stacks 058M "Exactness is hypothesised; universal injectivity of `f₁` is spelled out."]
public theorem Module.Flat.iff_forall_rTensor_injective_of_exact {R : Type u} [CommRing R]
    [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ ⦃M₁ M₂ : Type v⦄ [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
        (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M), Function.Injective f₁ →
        Function.Exact f₁ f₂ → Function.Surjective f₂ →
          ∀ (Q : Type v) [AddCommGroup Q] [Module R Q],
            Function.Injective (f₁.rTensor Q) :=
  Stacks.UniversalInjectivity.FlatCriterion.solution

end

/-! ## Universal injectivity of a map into a flat module, tested on cyclic modules -/

@[expose] public section

namespace Stacks.UniversalInjectivity.FGIdealTest

open Function LinearMap TensorProduct

variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M']

/-- In a commutative diagram of `R`-modules with rows `A → B → C` and `A' → B' → C'`, if the top
row is exact at `B`, the map `A' → B'` is injective, and the outer vertical maps `A → A'` and
`C → C'` are injective, then the middle vertical map `B → B'` is injective. -/
theorem injective_middle_of_exact {R : Type*} [Semiring R] {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [Module R A] [Module R B] [Module R C] [Module R A'] [Module R B']
    [Module R C'] {α : A →ₗ[R] B} {β : B →ₗ[R] C} {α' : A' →ₗ[R] B'} {β' : B' →ₗ[R] C'}
    {a : A →ₗ[R] A'} {b : B →ₗ[R] B'} {c : C →ₗ[R] C'} (hsqα : b ∘ₗ α = α' ∘ₗ a)
    (hsqβ : c ∘ₗ β = β' ∘ₗ b) (hrow : Function.Exact α β) (hα' : Function.Injective α')
    (ha : Function.Injective a) (hc : Function.Injective c) : Function.Injective b := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hrow x).mp <| (injective_iff_map_eq_zero c).mp hc _ <| by
    rw [← LinearMap.comp_apply, hsqβ, LinearMap.comp_apply, hx, map_zero]
  have hy : a y = 0 := (injective_iff_map_eq_zero α').mp hα' _ <| by
    rw [← LinearMap.comp_apply, ← hsqα, LinearMap.comp_apply, hx]
  rw [(injective_iff_map_eq_zero a).mp ha y hy, map_zero]

/-- Naturality of `f ⊗ id` in the second variable: both composites are `TensorProduct.map f g`. -/
private theorem rTensor_comp_lTensor_comm {Q Q' : Type*} [AddCommGroup Q] [Module R Q]
    [AddCommGroup Q'] [Module R Q'] (f : M →ₗ[R] M') (g : Q →ₗ[R] Q') :
    f.rTensor Q' ∘ₗ lTensor M g = lTensor M' g ∘ₗ f.rTensor Q := by
  rw [rTensor_comp_lTensor, lTensor_comp_rTensor]

/-- Injectivity of `f ⊗ id_Q` depends on the test module `Q` only through its isomorphism
class. -/
private theorem injective_rTensor_congr {Q Q' : Type*} [AddCommGroup Q] [Module R Q]
    [AddCommGroup Q'] [Module R Q'] (f : M →ₗ[R] M') (e : Q ≃ₗ[R] Q') :
    Function.Injective (f.rTensor Q) ↔ Function.Injective (f.rTensor Q') := by
  rw [← (LinearEquiv.lTensor M' e).injective.of_comp_iff (f.rTensor Q), ← LinearEquiv.coe_coe,
    LinearEquiv.coe_lTensor, ← LinearMap.coe_comp, ← rTensor_comp_lTensor_comm, LinearMap.coe_comp,
    ← LinearEquiv.coe_lTensor, LinearEquiv.coe_coe,
    Function.Injective.of_comp_iff' _ (LinearEquiv.lTensor M e).bijective]

/-- The map `M ⧸ p → M' ⧸ q` induced by `f` is injective exactly when `q` pulls back into `p`
along `f`. -/
theorem injective_mapQ_iff {R : Type*} [Ring R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] {p : Submodule R M} {q : Submodule R M'}
    (f : M →ₗ[R] M') (h : p ≤ q.comap f) :
    Function.Injective (p.mapQ q f h) ↔ q.comap f ≤ p := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, ← le_bot_iff, Submodule.map_le_iff_le_comap,
    Submodule.comap_bot, Submodule.ker_mkQ]

/-- Membership in `I • N` is witnessed by a finitely generated subideal of `I`. -/
private theorem exists_fg_le_and_mem_smul {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {I : Ideal R} {N : Submodule R M} {x : M} (hx : x ∈ I • N) :
    ∃ J : Ideal R, J.FG ∧ J ≤ I ∧ x ∈ J • N := by
  refine Submodule.smul_induction_on hx (fun r hr n hn ↦ ?_) ?_
  · exact ⟨Ideal.span {r}, Submodule.fg_span_singleton r,
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr),
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) hn⟩
  · rintro y z ⟨J₁, hJ₁, hJ₁I, hy⟩ ⟨J₂, hJ₂, hJ₂I, hz⟩
    exact ⟨J₁ ⊔ J₂, Submodule.FG.sup hJ₁ hJ₂, sup_le hJ₁I hJ₂I,
      add_mem (Submodule.smul_mono_left le_sup_left hy)
        (Submodule.smul_mono_left le_sup_right hz)⟩

/-- If `f` induces injective maps `M/JM → M'/JM'` for the finitely generated ideals `J`, then
it induces an injective map `M/IM → M'/IM'` for every ideal `I`. -/
private theorem injective_mapQ_smul_top_of_forall_fg (f : M →ₗ[R] M')
    (hfg : ∀ ⦃J : Ideal R⦄, J.FG → Function.Injective ((J • ⊤ : Submodule R M).mapQ
      (J • ⊤ : Submodule R M') f (Submodule.smul_top_le_comap_smul_top J f))) (I : Ideal R) :
    Function.Injective ((I • ⊤ : Submodule R M).mapQ (I • ⊤ : Submodule R M') f
      (Submodule.smul_top_le_comap_smul_top I f)) := by
  rw [injective_mapQ_iff]
  intro x hx
  obtain ⟨J, hJ, hJI, hxJ⟩ := exists_fg_le_and_mem_smul hx
  exact Submodule.smul_mono_left hJI ((injective_mapQ_iff f _).mp (hfg hJ) hxJ)

/-- The identification `M ⊗_R R/I = M/IM` is natural in `M`: the square with vertical maps
`f ⊗ id_{R/I}` and the map `M/IM → M'/IM'` induced by `f` commutes. -/
private theorem tensorQuotEquivQuotSMul_comp_rTensor (f : M →ₗ[R] M') (I : Ideal R) :
    (tensorQuotEquivQuotSMul M' I : M' ⊗[R] (R ⧸ I) →ₗ[R] M' ⧸ I • ⊤) ∘ₗ f.rTensor (R ⧸ I)
      = (I • ⊤ : Submodule R M).mapQ (I • ⊤ : Submodule R M') f
          (Submodule.smul_top_le_comap_smul_top I f) ∘ₗ
        (tensorQuotEquivQuotSMul M I : M ⊗[R] (R ⧸ I) →ₗ[R] M ⧸ I • ⊤) := by
  refine TensorProduct.ext' fun x r' ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
  simp [tensorQuotEquivQuotSMul_tmul_mk, Submodule.mapQ_apply]

/-- The map `M/IM → M'/IM'` induced by `f` is injective if and only if `f ⊗ id_{R/I}` is. -/
private theorem injective_mapQ_smul_top_iff (f : M →ₗ[R] M') (I : Ideal R) :
    Function.Injective ((I • ⊤ : Submodule R M).mapQ (I • ⊤ : Submodule R M') f
        (Submodule.smul_top_le_comap_smul_top I f)) ↔
      Function.Injective (f.rTensor (R ⧸ I)) := by
  rw [← Function.Injective.of_comp_iff' _ (tensorQuotEquivQuotSMul M I).bijective,
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, ← tensorQuotEquivQuotSMul_comp_rTensor,
    LinearMap.coe_comp, LinearEquiv.coe_coe,
    (tensorQuotEquivQuotSMul M' I).injective.of_comp_iff]

/-- The four lemma for a short exact sequence `0 → A → B → C → 0` tensored with `f`: if `M'` is
flat and `f ⊗ id` is injective on `A` and on `C`, then it is injective on `B`. -/
private theorem rTensor_injective_of_shortExact [Module.Flat R M'] (f : M →ₗ[R] M') {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {g₁ : A →ₗ[R] B} {g₂ : B →ₗ[R] C} (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (hg₂ : Function.Surjective g₂) (hA : Function.Injective (f.rTensor A))
    (hC : Function.Injective (f.rTensor C)) : Function.Injective (f.rTensor B) :=
  injective_middle_of_exact (α := lTensor M g₁) (β := lTensor M g₂) (α' := lTensor M' g₁)
    (β' := lTensor M' g₂) (rTensor_comp_lTensor_comm f g₁) (rTensor_comp_lTensor_comm f g₂)
    (lTensor_exact M hg hg₂) (Module.Flat.lTensor_preserves_injective_linearMap g₁ hg₁) hA hC

/-- If `M'` is flat and `f ⊗ id_{R/I}` is injective for every ideal `I`, then `f ⊗ id_Q` is
injective for every finite `R`-module `Q`. -/
private theorem rTensor_injective_of_finite [Module.Flat R M'] (f : M →ₗ[R] M')
    (H : ∀ I : Ideal R, Function.Injective (f.rTensor (R ⧸ I))) (Q : Type*) [AddCommGroup Q]
    [Module R Q] [Module.Finite R Q] : Function.Injective (f.rTensor Q) := by
  obtain ⟨X, hhead, hlast, -⟩ := Module.Finite.exists_relSeries_isQuotientEquivQuotientCyclic R Q
  have key : ∀ i : Fin (X.length + 1), Function.Injective (f.rTensor ↥(X i)) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have : Subsingleton ↥(X 0) := by rw [show X 0 = ⊥ from hhead]; infer_instance
      exact Function.injective_of_subsingleton _
    | succ i ih =>
      obtain ⟨hle, I, ⟨e⟩⟩ := X.step i
      exact rTensor_injective_of_shortExact f
        (g₁ := Submodule.inclusion hle)
        (g₂ := ((X i.castSucc).submoduleOf (X i.succ)).mkQ)
        (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_inclusion]; rfl))
        (Submodule.inclusion_injective hle) (Submodule.mkQ_surjective _) ih
        ((injective_rTensor_congr f e).mpr (H I))
  exact (injective_rTensor_congr f
    ((LinearEquiv.ofEq _ _ hlast).trans Submodule.topEquiv).symm).mpr (key (Fin.last _))

/-- For `M'` flat, `f : M →ₗ[R] M'` is universally injective if and only if the induced map
`M/IM → M'/IM'` is injective for every finitely generated ideal `I ⊆ R`. -/
public theorem solution {R : Type u} [CommRing R]
    [Small.{v} R] {M M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module.Flat R M'] (f : M →ₗ[R] M') :
    (∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q)) ↔
      ∀ ⦃I : Ideal R⦄, I.FG →
        Function.Injective ((I • ⊤ : Submodule R M).mapQ (I • ⊤ : Submodule R M') f
          (Submodule.smul_top_le_comap_smul_top I f)) := by
  constructor
  · intro hL I _
    have : Small.{v} (R ⧸ I) := small_of_surjective Ideal.Quotient.mk_surjective
    rw [injective_mapQ_smul_top_iff,
      injective_rTensor_congr f (Shrink.linearEquiv R (R ⧸ I)).symm]
    exact hL _
  · intro hR
    have hkey : ∀ I : Ideal R, Function.Injective (f.rTensor (R ⧸ I)) := fun I ↦
      (injective_mapQ_smul_top_iff f I).mp (injective_mapQ_smul_top_of_forall_fg f hR I)
    have hinj : Function.Injective f := by
      simpa [Submodule.bot_smul, ← LinearMap.ker_eq_bot, le_bot_iff] using
        (injective_mapQ_iff f (Submodule.smul_top_le_comap_smul_top (⊥ : Ideal R) f)).mp
          (hR Submodule.fg_bot)
    have hex : Function.Exact f (LinearMap.range f).mkQ :=
      LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
    refine ((hex.universallyExact_tfae hinj (Submodule.mkQ_surjective _)).out 2 1).mp ?_
    intro Q _ _ _
    exact ⟨rTensor_injective_of_finite f hkey Q, rTensor_exact Q hex (Submodule.mkQ_surjective _),
      LinearMap.rTensor_surjective Q (Submodule.mkQ_surjective _)⟩

end Stacks.UniversalInjectivity.FGIdealTest

end

@[expose] public section

/-- Let `f : M →ₗ[R] M'` be a map of `R`-modules with `M'` flat. Then `f` is universally
injective, that is `f ⊗ id_Q` is injective for every `R`-module `Q`, if and only if the induced
map `M/IM → M'/IM'` is injective for every finitely generated ideal `I ⊆ R`. -/
@[stacks 0AS5 "`M/IM` is `M ⧸ I • ⊤` and the induced map is `Submodule.mapQ` along `f`; the
left-hand side spells out universal injectivity, which `Mathlib` has no name for."]
public theorem Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top {R : Type u} [CommRing R]
    [Small.{v} R] {M M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module.Flat R M'] (f : M →ₗ[R] M') :
    (∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q)) ↔
      ∀ ⦃I : Ideal R⦄, I.FG →
        Function.Injective ((I • ⊤ : Submodule R M).mapQ (I • ⊤ : Submodule R M') f
          (Submodule.smul_top_le_comap_smul_top I f)) :=
  Stacks.UniversalInjectivity.FGIdealTest.solution f

end

end

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

/-- **Universally injective module map.**
A homomorphism of `R`-modules `f : M →ₗ[R] N` is *universally injective* if for every
`R`-module `Q`, the induced map `f ⊗ id_Q : M ⊗_R Q → N ⊗_R Q` (i.e. `f.rTensor Q`) is
injective. -/
@[stacks 058I, ega "IV 11.9.14" "special case", ega "IV 11.9.18" "special case", sga "1 II 4.5"]
def UniversallyInjective {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q)

end

/-! ## Universal injectivity is preserved by tensoring -/

@[expose] public section

open scoped TensorProduct

/-- If `u : M →ₗ[R] M'` is universally injective, then for any `R`-module `N` the induced map
`u ⊗ id_N : M ⊗_R N → M' ⊗_R N` (i.e. `LinearMap.rTensor N u`) is again universally
injective. -/
@[stacks 05CH]
theorem universallyInjective_rTensor {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    {M' : Type} [AddCommGroup M'] [Module R M']
    (u : M →ₗ[R] M') (hu : UniversallyInjective u)
    (N : Type) [AddCommGroup N] [Module R N] :
    UniversallyInjective (LinearMap.rTensor N u) := by
  intro Q _ _
  have hnat : (TensorProduct.assoc R M' N Q).toLinearMap ∘ₗ (u.rTensor N).rTensor Q =
      u.rTensor (N ⊗[R] Q) ∘ₗ (TensorProduct.assoc R M N Q).toLinearMap := by
    ext
    simp
  refine Function.Injective.of_comp (f := TensorProduct.assoc R M' N Q) ?_
  rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp, hnat, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (hu (N ⊗[R] Q)).comp (TensorProduct.assoc R M N Q).injective

end

/-! ## Compositions of universally injective module maps -/

@[expose] public section
open TensorProduct

universe u v

/-- A map of `R`-modules `f : M → N` is *universally injective* if for every
`R`-module `Q`, the induced map `f ⊗_R id_Q : M ⊗_R Q → N ⊗_R Q` (namely
`LinearMap.rTensor Q f`) is injective. -/
@[ega "IV 11.9.14" "special case", ega "IV 11.9.18" "special case", sga "1 II 4.5"]
def IsPureMono {R : Type u} [CommRing R] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (LinearMap.rTensor Q f)

/-- A composition of universally injective `R`-module maps is universally injective. -/
@[stacks 05CI]
theorem comp_universallyInjective {R : Type u} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : IsPureMono.{u, v} f) (hg : IsPureMono.{u, v} g) :
    IsPureMono.{u, v} (g ∘ₗ f) := by
  intro Q _ _
  rw [LinearMap.rTensor_comp]
  exact (hg Q).comp (hf Q)

end

/-! ## Faithfully flat ring maps are universally injective -/

@[expose] public section
open TensorProduct

universe u w

/--
A linear map `f : M →ₗ[R] N` is *universally injective* if for every `R`-module `Q`
(in any universe), the induced map `f ⊗ id_Q : M ⊗_R Q → N ⊗_R Q` is injective.
(Stacks tag 058I.)

The module `Q` ranges over modules in an arbitrary universe `w`, captured here by
the universe-polymorphic definition (the universe variable `w` is implicit in the
`Type*` annotation on `Q`).

Note: Definitions 1 (flatness) and 2 (faithful flatness) are already present in
Mathlib as `Module.Flat`, `Module.FaithfullyFlat` and `RingHom.FaithfullyFlat`, and
are reused below. -/
@[ega "IV 11.9.14" "special case", ega "IV 11.9.18" "special case", sga "1 II 4.5"]
def UniversallyInjectivePoly {R : Type u} {M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type w) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q)

/-- For any `R`-algebra `S` and `R`-module `Q`, the map `R ⊗_R Q → S ⊗_R Q` becomes injective
after applying `S ⊗ -`. -/
theorem lTensor_rTensor_algebraMap_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {Q : Type*} [AddCommGroup Q] [Module R Q] :
    Function.Injective (LinearMap.lTensor S ((Algebra.linearMap R S).rTensor Q)) := by
  set f : R →ₗ[R] S := Algebra.linearMap R S with hf
  set g : R ⊗[R] Q →ₗ[R] S ⊗[R] Q := f.rTensor Q with hg
  set m : S ⊗[R] (S ⊗[R] Q) →ₗ[R] S ⊗[R] Q :=
    (LinearMap.rTensor Q (LinearMap.mul' R S)) ∘ₗ (TensorProduct.assoc R S S Q).symm.toLinearMap
    with hm
  set h : Q →ₗ[R] R ⊗[R] Q := (TensorProduct.lid R Q).symm.toLinearMap with hh
  set ret : S ⊗[R] (S ⊗[R] Q) →ₗ[R] S ⊗[R] (R ⊗[R] Q) :=
    (LinearMap.lTensor S h) ∘ₗ m with hret
  have hcomp : ret ∘ₗ (LinearMap.lTensor S g) = LinearMap.id := by
    apply TensorProduct.ext'
    intro s t
    induction t with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
        TensorProduct.tmul_add, map_add] at hx hy ⊢
      rw [hx, hy]
    | tmul r q =>
      simp only [hret, hm, hh, hg, hf, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
        LinearMap.id_coe, id_eq, TensorProduct.assoc_symm_tmul, LinearMap.mul'_apply,
        TensorProduct.lid_symm_apply, LinearEquiv.coe_coe]
      rw [show r ⊗ₜ[R] q = r • ((1 : R) ⊗ₜ[R] q) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
  exact Function.HasLeftInverse.injective ⟨ret, fun x ↦ by
    simpa using LinearMap.congr_fun hcomp x⟩

/-- For a faithfully flat ring map `φ : R → S`, the map `R ⊗_R Q → S ⊗_R Q` induced by
`Algebra.linearMap R S` is injective for any `R`-module `Q`. -/
theorem faithfullyFlat_rTensor_injective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.FaithfullyFlat)
    {Q : Type*} [AddCommGroup Q] [Module R Q] :
    haveI := φ.toAlgebra
    Function.Injective ((Algebra.linearMap R S).rTensor Q) := by
  let := φ.toAlgebra
  have : Module.FaithfullyFlat R S := hφ
  rw [← LinearMap.exact_zero_iff_injective PUnit.{1}]
  refine Module.FaithfullyFlat.lTensor_reflects_exact R S 0 _ ?_
  rw [LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective]
  exact lTensor_rTensor_algebraMap_injective

/--
For a faithfully flat ring map `φ : R → S`, the structure map `R → S` viewed as an
`R`-linear map (`Algebra.linearMap R S`, where `S` is given its `R`-module structure
via `φ`) is universally injective: for every `R`-module `Q`, the induced map
`R ⊗_R Q → S ⊗_R Q` is injective. -/
@[stacks 05CK,
  ega "0 6.5.1" "B faithfully flat",
  ega "IV 2.2.8" "affine case",
  ega "0 6.6.1" "(a)",
  sga "3 VIB 11.14" "necessity"]
theorem faithfullyFlat_universallyInjective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.FaithfullyFlat) :
    haveI := φ.toAlgebra
    UniversallyInjectivePoly (Algebra.linearMap R S) := by
  let := φ.toAlgebra
  exact fun Q _ _ ↦ faithfullyFlat_rTensor_injective φ hφ

/--
For a faithfully flat ring map `φ : R → S` and every `R`-module `Q`, the natural map
`Q → S ⊗_R Q`, `q ↦ 1 ⊗ q`, is injective. Under the canonical isomorphism
`R ⊗_R Q ≅ Q` this is the map `φ ⊗ id_Q` of Statement 1. -/
@[ega "0 6.5.1" "special case",
  ega "0 6.5.2" "special case",
  ega "IV 2.2.8" "Affine source and target",
  sga "1 IV 2.6" "(i) ⇒ (iii), (i) ⇒ (iv)",
  sga "3 VIB 11.14" "necessity"]
theorem faithfullyFlat_tensor_mk_injective
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.FaithfullyFlat)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    haveI := φ.toAlgebra
    Function.Injective ((TensorProduct.mk R S Q) 1) := by
  let := φ.toAlgebra
  have hfac : ((TensorProduct.mk R S Q) 1) =
      ((Algebra.linearMap R S).rTensor Q) ∘ ((TensorProduct.lid R Q).symm) := by
    funext q
    simp [LinearMap.rTensor_tmul]
  rw [hfac]
  exact (faithfullyFlat_rTensor_injective φ hφ).comp (TensorProduct.lid R Q).symm.injective

/--
For a faithfully flat ring map `φ : R → S` and every ideal `I ⊆ R`, the contraction
of the extended ideal `I S` back to `R` equals `I`, i.e. `φ⁻¹(I S) = I`.

This is Mathlib's `Ideal.comap_map_eq_self_of_faithfullyFlat`, restated for a bare ring map. -/
@[stacks 05CK "in particular",
  ega "0 6.6.3" "first part, M = A",
  ega "0 6.5.1" "B faithfully flat",
  ega "0 22.4.8" "more general",
  ega "0 6.5.2" "φ⁻¹(aB) = a",
  ega "0 6.6.1" "(a) ⇒ φ⁻¹(aB) = a in (d)", sga "1 IV 2.6" "(i)", sga "3 V 9.1" "partial"]
theorem faithfullyFlat_comap_map_eq
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.FaithfullyFlat)
    (I : Ideal R) :
    Ideal.comap φ (Ideal.map φ I) = I := by
  algebraize [φ]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

end

/-!
## Checking universal injectivity on localizations

Let `R → S` be a ring map, `f : M → M'` a map of `S`-modules, `q` a prime of `S` and
`p = q.under R`. The localized map `f_q : M_q → M'_q` is
`Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapR f q` as a map of `R`-modules and
`Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapRp f q` as a map of `R_p`-modules.
-/

@[expose] public section

namespace Stacks.UniversalInjectivity.LocalizationCriteria

open scoped TensorProduct

universe t u v w w'

/-- A homomorphism `g : X → Y` of `A`-modules is *universally injective* if for every
`A`-module `Q`, the induced map `g ⊗ id_Q : X ⊗_A Q → Y ⊗_A Q` is injective. -/
def UniversallyInjective.{uQ, uA, uX, uY} {A : Type uA} [CommRing A]
    {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [AddCommGroup Y] [Module A X] [Module A Y] (g : X →ₗ[A] Y) : Prop :=
  ∀ (Q : Type uQ) [AddCommGroup Q] [Module A Q], Function.Injective (g.rTensor Q)

section Setup

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {M M' : Type*}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']

/-- For a prime ideal `q ⊆ S`, the localization `S_q` is an algebra over `R_p`, where
`p = q.under R` is the inverse image of `q`, through the canonical map `R_p → S_q`. -/
noncomputable instance algebraRpSq (q : Ideal S) [q.IsPrime] :
    Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
  Localization.AtPrime.algebraOfLiesOver (q.under R) q

/-- The `R_p`-module structure on `M_q`, obtained by restricting the `S_q`-action along
`R_p → S_q`. -/
noncomputable instance moduleRpMq (q : Ideal S) [q.IsPrime] :
    Module (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl M) :=
  Module.compHom _ (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))

/-- The `R_p`-action on `M_q` is compatible with the `S_q`-action (scalar tower). -/
instance towerRpSqMq (q : Ideal S) [q.IsPrime] :
    IsScalarTower (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
      (LocalizedModule q.primeCompl M) :=
  ⟨fun x y z ↦ by
    change (algebraMap _ _ x * y) • z = algebraMap _ (Localization.AtPrime q) x • (y • z)
    rw [mul_smul]⟩

/-- The localized map `f_q : M_q → M'_q`, viewed as a map of `R`-modules. -/
noncomputable def localizedMapR (f : M →ₗ[S] M') (q : Ideal S) [q.IsPrime] :
    LocalizedModule q.primeCompl M →ₗ[R] LocalizedModule q.primeCompl M' :=
  (LocalizedModule.map q.primeCompl f).restrictScalars R

/-- The localized map `f_q : M_q → M'_q`, viewed as a map of `R_p`-modules
(`p = q.under R`). -/
noncomputable def localizedMapRp (f : M →ₗ[S] M') (q : Ideal S) [q.IsPrime] :
    LocalizedModule q.primeCompl M →ₗ[Localization.AtPrime (q.under R)]
      LocalizedModule q.primeCompl M' :=
  (LocalizedModule.map q.primeCompl (f : M →ₗ[S] M')).restrictScalars
    (Localization.AtPrime (q.under R))

/-- `M_q` is a scalar tower over `R → R_p`, where `p = q.under R`. -/
private instance isScalarTower_localization_under (q : Ideal S) [q.IsPrime] :
    IsScalarTower R (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl M) := by
  refine ⟨fun r x z ↦ ?_⟩
  have key : ∀ (a : Localization.AtPrime (q.under R)) (w : LocalizedModule q.primeCompl M),
      a • w = (algebraMap _ (Localization.AtPrime q) a) • w := fun _ _ ↦ rfl
  rw [key (r • x), key x, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime (q.under R)) (Localization.AtPrime q),
    mul_smul, algebraMap_smul]

end Setup

/-! ### Implications between the criteria

Universal injectivity is tested in `Type (max u t)`, where `R : Type u`. -/

section Edges

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} {M' : Type w'}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']

/-- Naturality of the localization maps `M ⊗[R] Q → M_q ⊗[R] Q` with respect to `f`. -/
private theorem rTensor_localizedMap_comp_mkLinearMap (f : M →ₗ[S] M') (q : Ideal S) [q.IsPrime]
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    TensorProduct.AlgebraTensorModule.rTensor R Q
        ((LocalizedModule.map q.primeCompl f).restrictScalars S) ∘ₗ
      TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.primeCompl M)
      = TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.mkLinearMap q.primeCompl M') ∘ₗ
        TensorProduct.AlgebraTensorModule.rTensor R Q f := by
  rw [← TensorProduct.AlgebraTensorModule.rTensor_comp,
    ← TensorProduct.AlgebraTensorModule.rTensor_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LocalizedModule.mkLinearMap_apply]
  exact LocalizedModule.map_mk q.primeCompl f x 1

/-- Over `R_p`, `p = q.under R`, `f_q ⊗ id_{R_p ⊗ Q}` is injective if and only if `f_q ⊗ id_Q`
is injective over `R`. -/
private theorem injective_rTensor_localizedMapR_iff (f : M →ₗ[S] M') (q : Ideal S) [q.IsPrime]
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((localizedMapR (R := R) f q).rTensor Q) ↔
      Function.Injective ((localizedMapRp (R := R) f q).rTensor
        (Localization.AtPrime (q.under R) ⊗[R] Q)) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime (q.under R))
    (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl M) Q
  let eM' := TensorProduct.AlgebraTensorModule.cancelBaseChange R
    (Localization.AtPrime (q.under R)) (Localization.AtPrime (q.under R))
    (LocalizedModule q.primeCompl M') Q
  have nat : (localizedMapR (R := R) f q).rTensor Q ∘ eM = eM' ∘
      (localizedMapRp (R := R) f q).rTensor (Localization.AtPrime (q.under R) ⊗[R] Q) := by
    refine funext fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Function.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]
    | tmul m w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        simp only [Function.comp_apply, TensorProduct.tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
      | tmul a n =>
        simp only [eM, eM', Function.comp_apply, LinearMap.rTensor_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        congr 1
        exact map_smul (localizedMapRp (R := R) f q) a m
  rw [← Function.Injective.of_comp_iff' _ eM.bijective, nat, eM'.injective.of_comp_iff]

/-- If `f_q ⊗ id_{R_p ⊗ Q}` is injective over `R_p`, then so is `f_q ⊗ id_Q` for any `R_p`-module
`Q`. -/
private theorem injective_rTensor_localizedMapRp_of_tensor {N N' : Type*}
    [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S N'] (f : N →ₗ[S] N')
    (q : Ideal S) [q.IsPrime] (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.under R)) Q]
    (h : Function.Injective
      ((localizedMapRp (R := R) f q).rTensor (Localization.AtPrime (q.under R) ⊗[R] Q))) :
    Function.Injective ((localizedMapRp (R := R) f q).rTensor Q) := by
  let eQ : Localization.AtPrime (q.under R) ⊗[R] Q ≃ₗ[Localization.AtPrime (q.under R)] Q :=
    IsLocalization.moduleLid (q.under R).primeCompl _ Q
  have natQ : (localizedMapRp (R := R) f q).rTensor Q ∘
        LinearEquiv.lTensor (LocalizedModule q.primeCompl N) eQ
      = LinearEquiv.lTensor (LocalizedModule q.primeCompl N') eQ ∘
        (localizedMapRp (R := R) f q).rTensor (Localization.AtPrime (q.under R) ⊗[R] Q) := by
    refine funext fun t ↦ ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Function.comp_apply, map_add] at ha hb ⊢; rw [ha, hb]
    | tmul m w => simp
  rw [← Function.Injective.of_comp_iff' _ (LinearEquiv.lTensor _ eQ).bijective, natQ]
  exact (LinearEquiv.lTensor _ eQ).injective.comp h

/-- If `f ⊗ id_Q` is injective over `R`, then so is `f_q ⊗ id_Q` for every prime `q` of `S`. -/
theorem localizedMapR_rTensor_injective
    (f : M →ₗ[S] M') (q : Ideal S) [q.IsPrime]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hf : Function.Injective
      ((LinearMap.rTensor Q (f.restrictScalars R) :
        M ⊗[R] Q →ₗ[R] M' ⊗[R] Q))) :
    Function.Injective ((LinearMap.rTensor Q (localizedMapR f q) :
      LocalizedModule q.primeCompl M ⊗[R] Q →ₗ[R]
        LocalizedModule q.primeCompl M' ⊗[R] Q)) := by
  have lM : IsLocalizedModule q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.mkLinearMap q.primeCompl M)) :=
    IsLocalizedModule.rTensor S q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl M)
  have lM' : IsLocalizedModule q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.mkLinearMap q.primeCompl M')) :=
    IsLocalizedModule.rTensor S q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl M')
  set h : M ⊗[R] Q →ₗ[S] M' ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.rTensor R Q f with hh
  have hinj : Function.Injective ⇑h := hf
  set lmap := IsLocalizedModule.map q.primeCompl
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.primeCompl M))
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.primeCompl M'))
    h with hlmap
  have hlmap_inj : Function.Injective lmap :=
    IsLocalizedModule.map_injective q.primeCompl _ _ h hinj
  set g : LocalizedModule q.primeCompl M ⊗[R] Q →ₗ[S] LocalizedModule q.primeCompl M' ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.rTensor R Q
      ((LocalizedModule.map q.primeCompl f).restrictScalars S) with hg
  have nat := rTensor_localizedMap_comp_mkLinearMap (R := R) f q Q
  have heq : lmap = g := by
    apply IsLocalizedModule.linearMap_ext q.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.primeCompl M))
      (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.primeCompl M'))
    rw [hlmap, IsLocalizedModule.map_comp, nat]
  exact (heq ▸ hlmap_inj : Function.Injective ⇑g)

/-- If for every maximal ideal `m ⊆ S` the localized map `f_m : M_m → M'_m` is universally
injective over `R`, then `f : M → M'` is universally injective as a map of `R`-modules. -/
theorem universallyInjective_of_localizedMapR_maximal
    (f : M →ₗ[S] M')
    (h3 : ∀ (m : Ideal S) [m.IsMaximal],
      UniversallyInjective.{max u t} (A := R) (localizedMapR f m)) :
    UniversallyInjective.{max u t} (f.restrictScalars R) := by
  intro Q _ _
  set h : M ⊗[R] Q →ₗ[S] M' ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.rTensor R Q f with hh
  suffices hinj : Function.Injective ⇑h by exact hinj
  apply injective_of_localized_maximal h
  intro m _
  have lM : IsLocalizedModule m.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.mkLinearMap m.primeCompl M)) :=
    IsLocalizedModule.rTensor S m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl M)
  have lM' : IsLocalizedModule m.primeCompl
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.mkLinearMap m.primeCompl M')) :=
    IsLocalizedModule.rTensor S m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl M')
  set g : LocalizedModule m.primeCompl M ⊗[R] Q →ₗ[S] LocalizedModule m.primeCompl M' ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.rTensor R Q
      ((LocalizedModule.map m.primeCompl f).restrictScalars S) with hg
  have nat := rTensor_localizedMap_comp_mkLinearMap (R := R) f m Q
  have hginj : Function.Injective ⇑g := h3 m Q
  let eM := IsLocalizedModule.iso m.primeCompl
    (TensorProduct.AlgebraTensorModule.rTensor R Q
      (LocalizedModule.mkLinearMap m.primeCompl M))
  let eM' := IsLocalizedModule.iso m.primeCompl
    (TensorProduct.AlgebraTensorModule.rTensor R Q
      (LocalizedModule.mkLinearMap m.primeCompl M'))
  have sq : g ∘ₗ (eM.toLinearMap)
      = (eM'.toLinearMap) ∘ₗ (LocalizedModule.map m.primeCompl h) := by
    apply IsLocalizedModule.linearMap_ext m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q))
      (TensorProduct.AlgebraTensorModule.rTensor R Q
        (LocalizedModule.mkLinearMap m.primeCompl M'))
    rw [LinearMap.comp_assoc]
    have heM : (eM.toLinearMap) ∘ₗ
          LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q)
        = TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap m.primeCompl M) := by
      have := IsLocalizedModule.iso_symm_comp m.primeCompl
        (TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.mkLinearMap m.primeCompl M))
      apply LinearMap.ext; intro x
      have := LinearMap.congr_fun this x
      simp only [LinearMap.comp_apply] at this ⊢
      rw [← this]
      simp [eM]
    rw [heM]
    rw [LinearMap.comp_assoc]
    have hmapcomp : ((LocalizedModule.map m.primeCompl h).restrictScalars S) ∘ₗ
        (LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q))
        = (LocalizedModule.mkLinearMap m.primeCompl (M' ⊗[R] Q)) ∘ₗ h := by
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LocalizedModule.mkLinearMap_apply]
      exact LocalizedModule.map_mk m.primeCompl h x 1
    rw [hmapcomp, ← LinearMap.comp_assoc]
    have heM' : (eM'.toLinearMap) ∘ₗ
        (LocalizedModule.mkLinearMap m.primeCompl (M' ⊗[R] Q))
        = TensorProduct.AlgebraTensorModule.rTensor R Q
            (LocalizedModule.mkLinearMap m.primeCompl M') := by
      have := IsLocalizedModule.iso_symm_comp m.primeCompl
        (TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.mkLinearMap m.primeCompl M'))
      apply LinearMap.ext; intro x
      have := LinearMap.congr_fun this x
      simp only [LinearMap.comp_apply] at this ⊢
      rw [← this]
      simp [eM']
    rw [heM']
    exact nat
  have sqf : ∀ x, eM' ((LocalizedModule.map m.primeCompl h) x) = g (eM x) := fun x ↦ by
    simpa using (LinearMap.congr_fun sq x).symm
  intro a b hab
  apply eM.injective
  apply hginj
  rw [← sqf, ← sqf, hab]

/-- If for every prime `q` of `S` the localization `f_q` is universally injective over `R_p`,
`p = q.under R`, then it is universally injective over `R`. -/
theorem universallyInjective_localizedMapR_of_localizedMapRp
    (f : M →ₗ[S] M')
    (h4 : ∀ (q : Ideal S) [q.IsPrime],
      UniversallyInjective.{max u t} (A := Localization.AtPrime (q.under R)) (localizedMapRp f q)) :
    ∀ (q : Ideal S) [q.IsPrime], UniversallyInjective.{max u t} (A := R) (localizedMapR f q) := by
  intro q _ Q _ _
  exact (injective_rTensor_localizedMapR_iff f q Q).mpr (h4 q _)

/-- If every localization `M_q → M'_q` is universally injective over `R`, then it
is universally injective over the localization `R_p`, `p = q ∩ R`. -/
theorem universallyInjective_localizedMapRp_of_localizedMapR
    (f : M →ₗ[S] M')
    (h2 : ∀ (q : Ideal S) [q.IsPrime],
      UniversallyInjective.{max u t} (A := R) (localizedMapR f q)) :
    ∀ (q : Ideal S) [q.IsPrime],
      UniversallyInjective.{max u t} (localizedMapRp (R := R) f q) := by
  intro q _ Q _ _
  let moduleRQ : Module R Q := Module.compHom Q (algebraMap R (Localization.AtPrime (q.under R)))
  have : IsScalarTower R (Localization.AtPrime (q.under R)) Q :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact injective_rTensor_localizedMapRp_of_tensor f q Q
    ((injective_rTensor_localizedMapR_iff f q Q).mp (h2 q Q))

/-- Universal injectivity over `R_p` at every maximal ideal implies universal
injectivity over `R` at every maximal ideal. -/
theorem universallyInjective_localizedMapR_of_localizedMapRp_maximal
    (f : M →ₗ[S] M')
    (h5 : ∀ (m : Ideal S) [m.IsMaximal],
      UniversallyInjective.{max u t} (A := Localization.AtPrime (m.under R)) (localizedMapRp f m)) :
    ∀ (m : Ideal S) [m.IsMaximal], UniversallyInjective.{max u t} (A := R) (localizedMapR f m) := by
  intro m _ Q _ _
  exact (injective_rTensor_localizedMapR_iff f m Q).mpr (h5 m _)

/-- Universal injectivity over `R` at every maximal ideal implies universal
injectivity over the corresponding `R_p`. -/
theorem universallyInjective_localizedMapRp_of_localizedMapR_maximal
    (f : M →ₗ[S] M')
    (h3 : ∀ (m : Ideal S) [m.IsMaximal],
      UniversallyInjective.{max u t} (A := R) (localizedMapR f m)) :
    ∀ (m : Ideal S) [m.IsMaximal],
      UniversallyInjective.{max u t} (localizedMapRp (R := R) f m) := by
  intro m _ Q _ _
  let moduleRQ : Module R Q := Module.compHom Q (algebraMap R (Localization.AtPrime (m.under R)))
  have : IsScalarTower R (Localization.AtPrime (m.under R)) Q :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact injective_rTensor_localizedMapRp_of_tensor f m Q
    ((injective_rTensor_localizedMapR_iff f m Q).mp (h3 m Q))

end Edges

/-- For a ring map `R → S` and a map `f : M → M'` of `S`-modules, universal injectivity of `f` as
a map of `R`-modules can be checked on localizations: the following are equivalent: `f` is
universally injective over `R`; `f_q` is, for every prime `q` of `S`; `f_m` is, for every maximal
ideal `m` of `S`; and the corresponding statements over the localizations `R_p`. -/
@[stacks 05CL]
theorem universally_injective_check_stalks
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} {M' : Type w'}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M') :
    [ -- (1) f is universally injective as a map of R-modules
      UniversallyInjective.{max u t} (f.restrictScalars R),
      -- (2) for every prime q of S, f_q is universally injective as a map of R-modules
      ∀ (q : Ideal S) [q.IsPrime], UniversallyInjective.{max u t} (A := R) (localizedMapR f q),
      -- (3) for every maximal m of S, f_m is universally injective as a map of R-modules
      ∀ (m : Ideal S) [m.IsMaximal], UniversallyInjective.{max u t} (A := R) (localizedMapR f m),
      -- (4) for every prime q of S, f_q is universally injective as a map of R_p-modules
      ∀ (q : Ideal S) [q.IsPrime],
        UniversallyInjective.{max u t} (A := Localization.AtPrime (q.under R)) (localizedMapRp f q),
      -- (5) for every maximal m of S, f_m is universally injective as a map of R_p-modules
      ∀ (m : Ideal S) [m.IsMaximal],
        UniversallyInjective.{max u t} (A := Localization.AtPrime (m.under R)) (localizedMapRp f m)
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro h1 q _ Q _ _
    exact localizedMapR_rTensor_injective f q Q (h1 Q)
  tfae_have 2 → 3 := by
    intro h2 m _ Q _ _
    exact h2 m Q
  tfae_have 3 → 1 := universallyInjective_of_localizedMapR_maximal f
  tfae_have 2 → 4 := universallyInjective_localizedMapRp_of_localizedMapR f
  tfae_have 4 → 2 := universallyInjective_localizedMapR_of_localizedMapRp f
  tfae_have 3 → 5 := universallyInjective_localizedMapRp_of_localizedMapR_maximal f
  tfae_have 5 → 3 := universallyInjective_localizedMapR_of_localizedMapRp_maximal f
  tfae_finish

/-- The prime-local criterion implies universal injectivity with test modules in any smaller
universe. In particular, when `M` and `M'` both live in `Type t`, the conclusion is definitionally
`_root_.UniversallyInjective (f.restrictScalars R)`. -/
theorem universallyInjective_of_localizedMapRp
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} {M' : Type w'}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']
    (f : M →ₗ[S] M')
    (hloc : ∀ (q : Ideal S) [q.IsPrime],
      UniversallyInjective.{max u t} (localizedMapRp (R := R) f q)) :
    UniversallyInjective.{t} (f.restrictScalars R) := by
  have hglobal : UniversallyInjective.{max u t} (f.restrictScalars R) :=
    ((universally_injective_check_stalks f).out 4 1).mp hloc
  intro Q _ _
  let e : Q ≃ₗ[R] ULift.{u} Q := ULift.moduleEquiv.symm
  have nat : (f.restrictScalars R).rTensor (ULift.{u} Q) ∘ₗ
        (LinearEquiv.lTensor M e).toLinearMap =
      (LinearEquiv.lTensor M' e).toLinearMap ∘ₗ (f.restrictScalars R).rTensor Q := by
    ext m q
    rfl
  intro x y hxy
  apply (LinearEquiv.lTensor M e).injective
  apply hglobal (ULift.{u} Q)
  change ((f.restrictScalars R).rTensor (ULift.{u} Q) ∘ₗ
    (LinearEquiv.lTensor M e).toLinearMap) x = _
  rw [nat]
  change _ = ((f.restrictScalars R).rTensor (ULift.{u} Q) ∘ₗ
    (LinearEquiv.lTensor M e).toLinearMap) y
  rw [nat]
  simp only [LinearMap.comp_apply, hxy]

end Stacks.UniversalInjectivity.LocalizationCriteria

end

/-!
## Base change along a universally injective ring map

If `R → S` is universally injective as a map of `R`-modules, then base change along it reflects
injections, surjections and isomorphisms.
-/

@[expose] public section

universe u

/-- The canonical `R`-linear map `M → M ⊗[R] S`, `m ↦ m ⊗ₜ 1`. -/
def baseChangeUnit (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] : M →ₗ[R] TensorProduct R M S :=
  (TensorProduct.comm R S M).toLinearMap.comp
    ((LinearMap.rTensor M (Algebra.linearMap R S)).comp
      (TensorProduct.lid R M).symm.toLinearMap)

/-- `baseChangeUnit R S M` sends `m` to `m ⊗ₜ 1`. -/
@[simp]
theorem baseChangeUnit_apply (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (m : M) :
    baseChangeUnit R S M m = m ⊗ₜ[R] (1 : S) := by
  simp [baseChangeUnit, LinearMap.rTensor_tmul, Algebra.linearMap_apply]

/-- If `R → S` is universally injective as a map of `R`-modules, then `m ↦ m ⊗ₜ 1` is
injective for every `R`-module `M`. -/
theorem baseChangeUnit_injective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : UniversallyInjective (Algebra.linearMap R S))
    (M : Type u) [AddCommGroup M] [Module R M] :
    Function.Injective (baseChangeUnit R S M) :=
  (TensorProduct.comm R S M).injective.comp ((hRS M).comp (TensorProduct.lid R M).symm.injective)

/-- **Base change along a universally injective ring map reflects injections.**
If `R → S` is universally injective as a map of `R`-modules and
`f ⊗_R id_S : M ⊗[R] S → N ⊗[R] S` is injective, then `f` is injective. -/
@[stacks 0H9I "(1)"]
theorem reflects_injections
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : UniversallyInjective (Algebra.linearMap R S))
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (LinearMap.rTensor S f)) :
    Function.Injective f := fun a b hab ↦
  baseChangeUnit_injective hRS M <| hf <| by
    simp only [baseChangeUnit_apply, LinearMap.rTensor_tmul, hab]

/-- **Base change along a universally injective ring map reflects surjections.**
If `R → S` is universally injective as a map of `R`-modules and
`f ⊗_R id_S : M ⊗[R] S → N ⊗[R] S` is surjective, then `f` is surjective. -/
@[stacks 0H9I "(2)", ega "IV 2.2.7" "partial", ega "IV 2.5.4.1" "more general"]
theorem reflects_surjections
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : UniversallyInjective (Algebra.linearMap R S))
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Surjective (LinearMap.rTensor S f)) :
    Function.Surjective f := by
  have hmk0 : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
    ext m
    simp
  have hmkComp : LinearMap.rTensor S ((LinearMap.range f).mkQ)
      ∘ₗ LinearMap.rTensor S f = 0 := by
    rw [← LinearMap.rTensor_comp, hmk0, LinearMap.rTensor_zero]
  have hmkZero : ∀ x : TensorProduct R N S,
      LinearMap.rTensor S ((LinearMap.range f).mkQ) x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    simpa using LinearMap.congr_fun hmkComp y
  have hsub : Subsingleton (TensorProduct R (N ⧸ LinearMap.range f) S) := by
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨a', rfl⟩ := LinearMap.rTensor_surjective S (Submodule.mkQ_surjective _) a
    obtain ⟨b', rfl⟩ := LinearMap.rTensor_surjective S (Submodule.mkQ_surjective _) b
    rw [hmkZero a', hmkZero b']
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact ⟨fun a b ↦ baseChangeUnit_injective hRS _ (Subsingleton.elim _ _)⟩

/-- **Base change along a universally injective ring map reflects isomorphisms.**
If `R → S` is universally injective as a map of `R`-modules and
`f ⊗_R id_S : M ⊗[R] S → N ⊗[R] S` is bijective, then `f` is bijective. -/
@[stacks 0H9I "(3)"]
theorem reflects_isomorphisms
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : UniversallyInjective (Algebra.linearMap R S))
    {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Bijective (LinearMap.rTensor S f)) :
    Function.Bijective f :=
  ⟨reflects_injections hRS f hf.left, reflects_surjections hRS f hf.right⟩

end

@[expose] public section

namespace Stacks.Derivations

/-- A derivation kills `p`-th powers in characteristic `p`: by the Leibniz rule
`d (a ^ p) = p • a ^ (p - 1) • d a`, and the factor `p` acts as zero. -/
@[ega "0 21.1.5" "(i)"]
public theorem derivation_pow_char {R A M : Type*}
    [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A]
    [Module R M] [Module A M] (p : ℕ) [CharP A p]
    (d : Derivation R A M) (a : A) : d (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow]
  simp [← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero]

end Stacks.Derivations

end
